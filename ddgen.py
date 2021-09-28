import sys
import earleyparser
import hdd
import fuzzer
import gmultiple
import gexpr
import gnegated
import gatleast
import grandom
import itertools as I

MERGE_OR_DEFINITIONS = True

def _sp(t,p):
    return fuzzer.tree_to_string(hdd.get_child(t,p))

def _st(t):
    return fuzzer.tree_to_string(t)

def remove_empty_def_keys(g):
    return {k:g[k] for k in g if g[k]}


def reachable_key(grammar, key, cnodesym, suffix, reachable):
    rules = grammar[key]
    my_rules = []
    for rule in grammar[key]:
        positions = gatleast.get_reachable_positions(rule, cnodesym, reachable)
        if not positions: continue
        # at each position, insert the cnodesym
        for pos in positions:
            new_rule = [with_suffix(t, suffix) if pos == p else t
                    for p,t in enumerate(rule)]
            my_rules.append(new_rule)
    return (with_suffix(key, suffix), my_rules)


def reachable_grammar(grammar, start, cnodesym, suffix, reachable):
    new_grammar = {}
    s_key = None
    for key in grammar:
        fk, rules = reachable_key(grammar, key, cnodesym, suffix, reachable)
        assert fk not in new_grammar
        if not rules: continue
        if key == start: s_key = fk
        new_grammar[fk] = rules
    return new_grammar, s_key
import pudb
bp = pudb.set_trace
class ReconstructRules(gexpr.ReconstructRules):
    def __init__(self, grammar, base_grammar, reachable):
        self.grammar = grammar
        self.base_grammar = base_grammar
        self.reachable = reachable

    def reconstruct_orig_bexpr(self, key_to_build, bexpr):
        # which keys can reach key_to_build that is in the gramamr given?
        reachable_keys = self.reachable[key_to_build]
        for k in reachable_keys:
            v = bexpr.with_key(k)
            if v not in self.grammar: continue
            reach_s, reach_d = reachable_key(self.base_grammar, k, k, bexpr._simple, self.reachable)
            return reach_d, reach_s
        return [], bexpr.with_key(key_to_build) #TODO

    def pattern_rules_from_key(self, f_key, bexpr):
        nbexpr = bexpr.negate()
        f_key_i = nbexpr.with_key(f_key)
        if f_key_i not in self.grammar: return [], []
        p_rules = []
        other_rules = []
        for rule in self.grammar[f_key_i]:
            has_rule = False
            for t in rule:
                if not fuzzer.is_nonterminal(t): continue
                if gatleast.is_base_key(t): continue
                if nbexpr._simple != get_suffix(t):
                    p_rules.append(rule)
                    has_rule = True
                    break
            if not has_rule: other_rules.append(rule)
        # assert len(p_rules) <= 1 # Note: This assertion assumes the original grammar is suffix free.
        return p_rules, other_rules

    def reconstruct_neg_bexpr(self, key, bexpr):
        fst = bexpr.op_fst()
        f_key = bexpr.with_key(key)

        # the idea is as follows: First check if this is at
        # the top of a pattern grammar. The way to check this
        # is to get the inner(f_key) rules, and search for
        # any other refinements in any other rules. If we
        # have such a rule, then we have a pattern grammar.
        # extract the complete pattern, negate it, then use it to
        # reconstruct. TODO:
        negated_pattern_rules = []
        prule, orules = self.pattern_rules_from_key(f_key, bexpr)
        #if prule:
        #    assert len(prule) == 1
        negated_pattern_rules = gnegated.unmatch_definition_in_pattern_grammar(prule, self.base_grammar[key])
        d, s = orules, bexpr.negate().with_key(key)
        #else:
        #    d, s = self.reconstruct_rules_from_bexpr(key, fst)
        d1 = negate_definition(negate_nonterminal(s), d, self.base_grammar)
        # at this point, we want to drop from d1 all the rules corresponding to
        # prule.

        combined_rules = gmultiple.and_definitions(d1, negated_pattern_rules)
        #combined_rules = d1 + negated_pattern_rules # TODO; should this be `and`ed?
        return combined_rules, f_key


def complete(grammar, base_grammar, start, reachable, log=False):
    rr = ReconstructRules(grammar, base_grammar, reachable)
    grammar, start = gatleast.grammar_gc(rr.reconstruct_key(start, log))
    return grammar, start

def generate_grammar_with_expr(grammar, base_grammar, start, suffix, reachable_keys):
    if not suffix: return ({**grammar, **base_grammar}, start)

    new_grammar = {**grammar, **base_grammar}
    my_key = with_suffix(start, suffix)

    return complete(new_grammar, base_grammar, my_key, reachable_keys)


def ddgen(reduced_tree, grammar, predicate):
    # The idea of ddewok is this: We start bottom up from an input that induces
    # failure. At the bottom, we get to a nonterminal just above a terminal
    # symbol, and try to abstract it. If the abstraction succeeds, we mark it as
    # abstract, and move to the next child of the same parent (peer). If on the
    # other hand, abstraction did not succeed, we try to relax the immediate
    # placement of the child node to containment of the child node. If this
    # works, we mark the containment and move to the next peer. When all peers
    # are finished, move up to the parent.
    # At the parent say P, we start with multiple possibilities. Say the peers
    # were <A'> <B fb> and <C fc>, where A is concrete, fb and fc are
    # containments. Now, the question is whether fb and fc need the same
    # sequence or can the be replaced with <P fb&fc>. So, we generate subtrees
    # with A in the immediate placement called <P fa>, and & it with <P fb> and
    # <P fc>. Then, generate and test. If that works, then our parent is an
    # abstract node with containment <P fa&fb&fc> if not, it is not abstract,
    # and we define <P fp> as <A'> <B fb> <C fc> and check if containment is now
    # sufficient. The, move to the next peer, and eventually move to the parent.
    reachable_keys = gatleast.reachable_dict(grammar)
    gs = generalize_bottomup_dd(reduced_tree, [], grammar, predicate, reachable_keys)
    ug, s, t = unwrap_ands(gs[2], gs[0], gs, predicate)
    assert t[0] == s
    assert s in ug
    return (t[0], t[1], ug)

# BEXPR_GRAMMAR = {
#     '<start>': [['<bexpr>']],
#     '<bexpr>': [
#         ['<bop>', '(', '<bexprs>', ')'],
#         ['<fault>']],
#     '<bexprs>' : [['<bexpr>', ',', '<bexprs>'], ['<bexpr>']],
#     '<bop>' : [list('and'), list('or'), list('neg')],
#     '<fault>': [['<letters>'], []],
#     '<letters>': [
#         ['<letter>'],
#         ['<letter>', '<letters>']],
#     '<letter>': [[i] for i in (
#         string.ascii_lowercase +
#         string.ascii_uppercase +
#         string.digits) + '_+*.-']
# }
def find_single_and(g):
    for k in g:
        if gatleast.is_base_key(k): continue
        stem, refinement = split(k)
        v = gexpr.BExpr(refinement)
        bexpr = v._tree
        assert bexpr[0] == '<bexpr>'
        bchild = bexpr[1][0]
        if bchild[0] == '<fault>': continue
        bexprs = bexpr[1][2]
        assert bexprs[0] == '<bexprs>'
        if len(bexprs[1]) == 1:
            return k
        else:
            continue
    return None

def shrink_and(my_and):
    v = gexpr.BExpr(my_and)
    bexpr = v._tree
    assert bexpr[0] == '<bexpr>'
    bchild = bexpr[1][0]
    assert bchild[0] != '<fault>'
    bexprs = bexpr[1][2]
    assert bexprs[0] == '<bexprs>'
    assert len(bexprs[1]) == 1
    and_bexpr = bexprs[1][0]
    #inner_bexpr = and_bexpr[1][2][1][0]
    return fuzzer.tree_to_string(and_bexpr)

def replace_suffix_expr_in_key(t, my_and, sand):
    #if not fuzzer.is_nonterminal(t): return t
    #if gatleast.is_base_key(t): return t
    return t.replace(my_and, sand)


def replace_suffix_expr_in_key_rule(rule, my_and, sand):
    return [replace_suffix_expr_in_key(t, my_and, sand) for t in rule]

def replace_suffix_expr_in_key_def(rules, my_and, sand):
    return [replace_suffix_expr_in_key_rule(rule, my_and, sand) for rule in rules]

def verify_equal_rules(rules1, rules2):
    for r1 in rules1:
        assert len([r2 for r2 in rules2 if r1 == r2]) == 1
    return True

def shrink_and_key_in_grammar(my_g, my_s, suffix_and, shrunk_and):
    return replace_suffix_expr_in_key_grammar(my_g, my_s, suffix_and, shrunk_and)


def replace_suffix_in_tree(tree, suffix_expr, new_expr):
    name, children, *_ = tree
    if not fuzzer.is_nonterminal(name): return (name, children)
    return (replace_suffix_expr_in_key(name, suffix_expr, new_expr),
            [replace_suffix_in_tree(c, suffix_expr, new_expr) for c in children])

def replace_suffix_expr_in_key_grammar(my_g, my_s, suffix_expr, new_expr):
    new_s = replace_suffix_expr_in_key(my_s, suffix_expr, new_expr)
    new_g = {}
    for k in my_g:
        if gatleast.is_base_key(k):
            new_g[k] = my_g[k]
            continue
        # replace my_and with new_expr
        new_k = replace_suffix_expr_in_key(k, suffix_expr, new_expr)
        new_rules = replace_suffix_expr_in_key_def(my_g[k], suffix_expr, new_expr)
        if new_k in new_g:
            verify_equal_rules(new_g[new_k], new_rules)
        else:
            new_g[new_k] = new_rules
    return new_g, new_s

def replace_and(new_g, new_s, suffix_expr, new_expr):
    return replace_suffix_expr_in_key_grammar(new_g, new_s, suffix_expr, new_expr)

def unwrap_ands(g, s, t, predicate):
    #at this point, there are many and(X) wraps which only wrap one single
    # argument X. It could be that this represents X or it could be that
    # the particular rule expansion (e.g '(' X ')' is required for X. If it is
    # the first case, unwrap it to X. If it is the second case, rename and(X)
    # to a new nonterminal Y, and replace all instances in the grammar
    new_g, new_s = g, s
    new_tree = t
    while True:
        my_and = find_single_and(new_g)
        if my_and is None: break

        suffix_and = get_suffix(my_and)
        shrunk_and = shrink_and(suffix_and)
        new_g_, new_s_ = shrink_and_key_in_grammar(new_g, new_s, suffix_and, shrunk_and)
        if validate_grammar(new_g_, new_s_, (), [], predicate):
            new_g, new_s = new_g_, new_s_
            new_tree = replace_suffix_in_tree(new_tree, suffix_and, shrunk_and)
        else:
            fault_val = new_fault_val()
            new_g, new_s = replace_and(new_g, new_s, suffix_and, fault_val)
            new_tree = replace_suffix_in_tree(new_tree, suffix_and, fault_val)
    return new_g, new_s, new_tree

def remove_grammar(cs):
    return [(n, cs) for (n,cs,g) in cs]

def generalize_bottomup_dd(tree, path, base_grammar, predicate, reachable_keys):
    o_key, o_children = hdd.get_child(tree, path)
    if not fuzzer.is_nonterminal(o_key): return (o_key, o_children, {})
    gchildren = process_children(o_children, tree, path, base_grammar, predicate, reachable_keys) # abstract children first

    grammar_from_children = dict(i for c in gchildren for i in c[2].items())

    new_grammar, new_key = can_and_conditions(o_key, tree, path,
            grammar_from_children, base_grammar, predicate, gchildren, reachable_keys)
    if new_grammar:
        # TODO: it may be that only some of the expressions can be anded
        # together In which case, we need to attempt to remove one at a time
        # from the `and` and leave the rest concrete.
        return (new_key, remove_grammar(gchildren), new_grammar)

    # At this point, we know that it was not just the refinements of child nodes
    # that was required, but possibly something from this current rule.
    # So, the question is, is the current rule only necessary somewhere in the
    # derivation tree?
    new_grammar, new_key = is_reach_sufficient(o_key, tree, path,
            grammar_from_children, base_grammar, predicate, reachable_keys, gchildren)
    if new_key is not None:
        return (new_key, remove_grammar(gchildren), new_grammar)


    # For make_match grammar, the constraint is that the grammar that we
    # make with g[k] should strictly reproduce the bug when expanded in
    # the particular position.
    new_grammar, new_key = make_match_grammar(o_key, base_grammar, reachable_keys, gchildren)
    return (new_key, remove_grammar(gchildren), {**grammar_from_children, **new_grammar})

def with_suffix(key, suffix):
    assert key[0], key[-1] == ('<', '>')
    if not suffix: return key
    val = key[1:-1]
    assert ' ' not in val
    return '<%s %s>' % (val, suffix)

def split(nonterminal):
    assert nonterminal[0], nonterminal[-1] == ('<', '>')
    return nonterminal[1:-1].split(' ')

def get_suffix(nonterminal):
    assert nonterminal[0], nonterminal[-1] == ('<', '>')
    name, suffix = nonterminal[1:-1].split(' ')
    return suffix

FAULT_COUNTER = 0
FAULT_NAME = 'E'
def new_fault_val():
    global FAULT_COUNTER
    c = FAULT_COUNTER
    FAULT_COUNTER += 1
    return FAULT_NAME + str(FAULT_COUNTER)

CONCRETE_COUNTER = 0
TMP_SUFFIX = '_tmp_'
def new_pattern_val():
    global CONCRETE_COUNTER
    c = CONCRETE_COUNTER
    CONCRETE_COUNTER += 1
    return TMP_SUFFIX + str(CONCRETE_COUNTER)

def is_base_node(node):
    name, children, *rest = node
    if ' ' not in name: return True
    return False

def unique_cnode_to_grammar(tree, grammar=None):
    if grammar is None: grammar = {}
    if is_base_node(tree): return grammar, gmultiple.normalize(tree[0])
    name, children, *rest = tree
    tokens = []
    if name not in grammar: grammar[name] = []
    for c in children:
        n, cs, *rest = c
        tokens.append(n)
        if fuzzer.is_nonterminal(n):
            unique_cnode_to_grammar(c, grammar)
    grammar[name].append(tokens)
    return grammar, tree[0]

def basic_grammar(g):
    return {k:g[k] for k in g if ' ' not in k}

def process_tmp_names(tree, fault_name, start=0, renames=None):
    if renames is None: renames = {}
    kname, children, grammar = tree
    if ' ' not in kname: return tree, renames
    name, suffix = kname[1:-1].split(' ')
    if suffix.startswith(TMP_SUFFIX):
        new_name = '<%s %s_%s>' % (name, FAULT_NAME, suffix[len(TMP_SUFFIX):])
        renames[kname] = new_name
        start += 1
        return (new_name, [process_tmp_names(c, fault_name, start, renames)[0] for c in children]), renames
    else:
        # not part of this pattern.
        return tree, renames

# Note that at the point where is_reach_sufficient is checked,
# the grammar already contains the definitions for each gchildren
# so, we now only need to produce a rule for the node name, and attach
# a rule to it for the nodes of gchildren.
def is_reach_sufficient(start, tree, path, cgrammar, base_grammar, predicate, reachable_keys, gchildren):
    tmp_fname = new_pattern_val()
    my_key = with_suffix(start, tmp_fname)
    rule = [c[0] for c in gchildren]
    reach_g, reach_s = reachable_grammar(base_grammar, start, start,
            tmp_fname, reachable_keys)
    if reach_s is None:
        # unable to reach start from start
        reach_g[my_key] = [rule]
    else:
        assert my_key == reach_s
        if MERGE_OR_DEFINITIONS:
            reach_g[reach_s] = gmultiple.or_definitions(reach_g[reach_s], [rule], merge_with_or=False)
        else:
            reach_g[reach_s] = reach_g[reach_s] + [rule]

    new_grammar = {**reach_g, **base_grammar, **cgrammar}
    new_grammar, reach_s = complete(new_grammar, base_grammar, my_key, reachable_keys)
    if validate_grammar(new_grammar, my_key, tree, path, predicate):
        return new_grammar, my_key
    return {}, None

# check if and(x,y) works
# Essentially, collect the children as pattern grammars, then generate
# an `and_grammar` of the corresponding expressions, and check if
# satisfies. If it satisfies, return the node name with anded
# expressions of child suffixes.
def can_and_conditions(start, tree, path, cgrammar, base_grammar, predicate, gchildren, reachable_keys):
    suffix, lst = and_exprs(gchildren)
    # we should always make sure that n_start is new. That is, make sure that
    # if there is at least one suffix, it is wrapped in and()
    n_grammar, n_start = generate_grammar_with_expr(cgrammar, base_grammar, start, suffix, reachable_keys)
    if validate_grammar(n_grammar, n_start, tree, path, predicate):
        return n_grammar, n_start
    return {}, None

MAX_TRIES_FOR_ABSTRACTION = 1000
def validate_grammar(grammar, start, tree, path, predicate):
    i = 0
    cache = None
    while (i < MAX_TRIES_FOR_ABSTRACTION):
        cache, gnode = generate_random_value(grammar, start, cache)
        t = replace_path(tree, path, gnode)
        with open('/tmp/ddgen.log', 'w+') as f:
            s = fuzzer.iter_tree_to_str(t)
            if predicate(s) == hdd.PRes.failed:
                print('X>', s, file=f)
                return False
            elif predicate(s) == hdd.PRes.invalid:
                print('*>', s, file=f)
                continue
            else:
                print(' >', s, file=f)
                i += 1
                continue
    return True


def and_exprs(nodes):
    lst = [split(node[0]) for node in nodes if not is_base_node(node)]
    if len(lst) == 1: return 'and(%s)' % lst[0][1], lst
    s = ','.join([l[1] for l in lst])
    if not s: return '', []
    return 'and(%s)' % s, lst

def process_children(children, tree, path, grammar, predicate, reachable_keys):
    gchildren = []
    for i, child in enumerate(children):
        gs = generalize_bottomup_dd(tree, path + [i], grammar, predicate, reachable_keys)
        gchildren.append(gs)
    return gchildren

def make_match_grammar(start, base_grammar, reachable_keys, gchildren):
    tmp_fname = new_pattern_val()
    my_key = with_suffix(start, tmp_fname)
    rule = [c[0] for c in gchildren]
    return {my_key: [rule]}, my_key

import copy
def replace_path(tree, path, new_node=None):
    if new_node is None: new_node = []
    if not path: return copy.deepcopy(new_node)
    cur, *path = path
    name, children, *rest = tree
    new_children = []
    for i,c in enumerate(children):
        if i == cur:
            nc = replace_path(c, path, new_node)
        else:
            nc = c
        if nc:
            new_children.append(nc)
    return (name, new_children, *rest)

# Given a key, generate a random value for that key using the grammar. 

def generate_random_value(grammar, key, my_fuzzer=None):
    if my_fuzzer is None:
        my_fuzzer = fuzzer.LimitFuzzer(grammar)
    t = my_fuzzer.iter_gen_key(key, max_depth=10)
    return (my_fuzzer, t)

import random
def generate_random_value(grammar, start, rscfg=None):
    max_len = 10
    if rscfg is None:
        rscfg = grandom.RandomSampleCFG(grammar)
        rscfg.produce_shared_forest(start, max_len)
    v, tree = rscfg.random_sample(start, max_len)
    return (rscfg, tree)

def abstract_tree_to_string(t):
    name, children, grammar = t
    if not fuzzer.is_nonterminal(name): return name
    if ' ' not in name: return name
    return ''.join([abstract_tree_to_string(c) for c in children])

import re
def check_doubled_paren(val):
    while '((' in val and '))' in val:
        val = re.sub(r'[^()]+','X', val)
        if '((X))' in val:
            return hdd.PRes.success
        val = val.replace(r'(X)', '')
    return hdd.PRes.failed

if __name__ == '__main__x':
    my_input = '1+((2*3/4))'
    expr_parser = earleyparser.EarleyParser(hdd.EXPR_GRAMMAR)
    parsed_expr = list(expr_parser.parse_on(my_input, '<start>'))[0]
    reduced_expr_tree = hdd.perses_reduction(parsed_expr, hdd.EXPR_GRAMMAR, check_doubled_paren)

    pattern = ddgen(reduced_expr_tree, hdd.EXPR_GRAMMAR, check_doubled_paren)
    print(abstract_tree_to_string(pattern))

def check_zero(v):
    if '/0)' in v: return hdd.PRes.success
    return hdd.PRes.failed

if __name__ == '__main__x':
    my_input = '1+((2*3/0))'
    expr_parser = earleyparser.EarleyParser(hdd.EXPR_GRAMMAR)
    parsed_expr = list(expr_parser.parse_on(my_input, '<start>'))[0]
    reduced_expr_tree = hdd.perses_reduction(parsed_expr, hdd.EXPR_GRAMMAR, check_zero)

    pattern = ddgen(reduced_expr_tree, hdd.EXPR_GRAMMAR, check_zero)
    print(abstract_tree_to_string(pattern))

def check_zero_doubled_paren(val):
    has_zero = False
    while True:
        lst = re.findall(r'[(][(][^()]*[)][)]', val)
        for s in lst:
            if '/0' in  s:
                has_zero = True
                return hdd.PRes.success

        val_ = re.sub(r'[(][^()]+[)]','X', val)
        if val == val_: break
        val = val_
    return hdd.PRes.failed

if __name__ == '__main__x':
    my_input = '1+((2*3/0))' # True
    #my_input = '1+((2*3/0)+(1))' # False
    #my_input = '1+(((2*3/5))+(1/0))' # Fales
    #my_input = '1+(((2*3/5))+((1/0)))' # True
    #my_input = '1+(((2*(3/5)/0))+(1/2))' # True
    expr_parser = earleyparser.EarleyParser(hdd.EXPR_GRAMMAR)
    parsed_expr = list(expr_parser.parse_on(my_input, '<start>'))[0]
    reduced_expr_tree = hdd.perses_reduction(parsed_expr, hdd.EXPR_GRAMMAR, check_zero_doubled_paren)

    pattern = ddgen(reduced_expr_tree, hdd.EXPR_GRAMMAR, check_zero_doubled_paren)
    print(abstract_tree_to_string(pattern))
    gatleast.display_grammar(pattern[2], pattern[0])


# ## Negation of full evocative expressions
#
# Negation of a single pattern is useful, but we may also want
# to negate larger expressions such as say `neg(or(and(f1,f2),f3))`
#
# ## Nonterminals
# Let us start with negating nonterminals.

def negate_refinement(ref):
    return 'neg(%s)' % ref

def negate_nonterminal(key):
    stem, refinement = gatleast.tsplit(key)
    v = gexpr.BExpr(refinement)
    m = v.negate().with_key(key)
    return m
    #assert refinement
    #return '<%s %s>' % (stem, negate_refinement(refinement))

# ### Negating a rule
# 
# Negating a rule produces as many rules as there are specialized
# nonterminals in that rule.

def specialized_positions(rule):
    positions = []
    for i,t in enumerate(rule):
        if not fuzzer.is_nonterminal(t):
            continue
        if gatleast.is_base_key(t):
            continue
        positions.append(i)
    return positions

def negate_rule(rule):
    positions = specialized_positions(rule)
    new_rules = []
    for p in positions:
        new_rule = [negate_nonterminal(t)
                        if i == p else t for i,t in enumerate(rule)]
        new_rules.append(new_rule)
    return new_rules

# ### Negation of a ruleset
# 
# negation of a ruleset is based on boolean algebra.
# say a definition is `S = R1 | R2 | R3` then,
# `neg(S)` is `neg(R1) & neg(R2) & neg(R3)`. Since each
# `neg(R)` results in multiple `r` we apply distributive
# law. That is,
#
# `(r1|r2|r3) & (r4|r5|r6) & (r7|r8|r9)`
#
# This gives r1&r4&r7 | r1&r4&r8 | etc.

def and_all_rules_to_one(rules):
    new_rule, *rules = rules
    while rules:
        r,*rules = rules
        new_rule = gmultiple.and_rules(new_rule, r)
    return new_rule

def negate_ruleset(rules):
    negated_rules_set = [negate_rule(ruleR) for ruleR in rules]
    negated_rules = []
    for rules in I.product(*negated_rules_set):
        r = and_all_rules_to_one(rules)
        negated_rules.append(r)
    return negated_rules

# ### Negation of a definition.
#
# Negating a defintion adds any rules in the base that is not
# part of the specialized definition. Then, we negate each
# ruleset. Further, each nonterminal in rule is conjuncted
# ith the specialization.

def and_suffix(k1, suffix):
    if gatleast.is_base_key(k1):
        return '<%s %s>' % (gatleast.stem(k1), suffix)
    refinement = 'and(%s,%s)' % (gatleast.refinement(k1), suffix)
    v = gexpr.BExpr(refinement)
    return  v.with_key(k1)
    #return '<%s and(%s,%s)>' % (gatleast.stem(k1), gatleast.refinement(k1), suffix)

def negate_definition(specialized_key, refined_rules, grammar):
    refined_rulesets = gmultiple.get_rulesets(refined_rules)
    base_key = gmultiple.normalize(specialized_key)
    base_rules = grammar[base_key]
    refinement = gatleast.refinement(specialized_key)

    # todo -- check if refined_rulesets key is in the right format.
    negated_rules = [r for r in base_rules if tuple(r) not in refined_rulesets]

    for rule_rep in refined_rulesets:
        new_nrules = negate_ruleset(refined_rulesets[rule_rep])
        negated_rules.extend(new_nrules)

    conj_negated_rules = []
    for rule in negated_rules:
        conj_rule = [and_suffix(t, refinement)
                        if fuzzer.is_nonterminal(t) else t for t in rule]
        conj_negated_rules.append(conj_rule)

    return conj_negated_rules

# ### Construction of a grammar negation.
#
# At this point, we are ready to construct a negated grammar.
# For negated grammars, we can simply return the grammar and negated start
# and let the reconstruction happen in `complete()`

def negate_grammar_(grammar, start):
    nstart = negate_nonterminal(start)
    #defs = negate_definition(nstart, grammar[start], grammar)
    #grammar[nstart] = defs
    return grammar, nstart

#  We extend ReconstructRules with negation


E_GRAMMAR = {
 '<start>': [['<expr>']],
 '<expr>': [['<factor>', '+', '<expr>'],
            ['<factor>']],
 '<factor>': [['(', '<expr>', ')'],
              ['<integer>']],
 '<integer>': [['1']]}

E_START = '<start>'

if __name__ == '__main__':
    my_input = '1+((1))'
    expr_parser = earleyparser.EarleyParser(E_GRAMMAR)
    parsed_expr = list(expr_parser.parse_on(my_input, E_START))[0]
    reduced_expr_tree = hdd.perses_reduction(parsed_expr, E_GRAMMAR, check_doubled_paren)

    pattern = ddgen(reduced_expr_tree, E_GRAMMAR, check_doubled_paren)
    gatleast.display_grammar(pattern[2], pattern[0])


    # The idea for negating these grammars is this: We extract the
    # pattern grammars out of these, and negate them
    new_grammar, new_start = negate_grammar_(pattern[2], pattern[0])
    base_grammar = E_GRAMMAR
    reachable_keys = gatleast.reachable_dict(E_GRAMMAR)
    g,s = complete(new_grammar, base_grammar, new_start, reachable_keys)
    gatleast.display_grammar(g, s)

    my_fuzzer = fuzzer.LimitFuzzer(g)
    for i in range(10):
        t = my_fuzzer.iter_gen_key(s, max_depth=10)
        v = fuzzer.tree_to_string(t)
        print(v)
        assert check_doubled_paren(v) == hdd.PRes.failed


