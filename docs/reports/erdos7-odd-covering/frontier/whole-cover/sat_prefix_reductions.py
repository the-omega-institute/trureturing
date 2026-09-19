#!/usr/bin/env python3
"""Exact finite diagnostics for the AP/multivalued-CNF interface.

No SAT result is assumed: all original private points, DP existential semantics,
and derived scope collisions are checked over the entire finite CRT product.
"""
import argparse
from fractions import Fraction
from hashlib import sha256
from itertools import product
from math import gcd, lcm
from pathlib import Path
import importlib.util
import json
import sys
sys.dont_write_bytecode = True


def require(test, message):
    if not test:
        raise ValueError(message)


def crt(pairs):
    a, d = 0, 1
    for b, m in pairs:
        require(gcd(d, m) == 1, 'Coprime CRT factors')
        a += d * (((b-a) * pow(d, -1, m)) % m)
        d *= m
    return a, d


def factors(n):
    out = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0)+1
            n //= p
        p += 1
    if n > 1:
        out[n] = out.get(n, 0)+1
    return out


def clause(a, d):
    return {(p, k): (a // p**(k-1)) % p
            for p, h in factors(d).items() for k in range(1, h+1)}


def falsifies(c, x):
    return all(x[v] == value for v, value in c.items())


def canonical(c):
    return tuple(sorted((p, k, value) for (p, k), value in c.items()))


def prefix(c):
    return all(all((p, j) in c for j in range(1, k+1)) for p, k in c)


def as_ap(c):
    require(prefix(c), 'Only prefix scopes represent one AP')
    primes = sorted({p for p, _ in c})
    pairs = []
    for p in primes:
        h = max(k for q, k in c if q == p)
        pairs.append((sum(c[(p,k)]*p**(k-1) for k in range(1,h+1)), p**h))
    return crt(pairs) if pairs else (0, 1)


def dp(clauses, variable):
    domain = range(variable[0])
    parents = [[i for i,c in enumerate(clauses) if c.get(variable) == a] for a in domain]
    result = []
    for indices in product(*parents):
        c, compatible = {}, True
        for i in indices:
            for v, value in clauses[i].items():
                if v == variable:
                    continue
                if v in c and c[v] != value:
                    compatible = False
                c[v] = value
        if compatible:
            result.append((indices, c))
    return parents, result


def verify_example(name, originals, variable, expected_unique, expected_prefix):
    require(len(originals) == len({d for a,d in originals}), 'Distinct original moduli')
    require(all(d > 1 and d % 2 for a,d in originals), 'Odd nontrivial original moduli')
    clauses = [clause(a,d) for a,d in originals]
    require(all(as_ap(c) == ad for c,ad in zip(clauses,originals)), 'Exact AP/clauses roundtrip')
    period = lcm(*(d for a,d in originals))
    private = [None]*len(originals)
    covered_count = 0
    uncovered = None
    for n in range(period):
        membership = [i for i,(a,d) in enumerate(originals) if n % d == a]
        if membership:
            covered_count += 1
        elif uncovered is None:
            uncovered = n
        if len(membership) == 1 and private[membership[0]] is None:
            private[membership[0]] = n
    require(all(v is not None for v in private), 'Every original label has actual private point')
    for i, witness in enumerate(private):
        require([j for j,(a,d) in enumerate(originals) if witness % d == a] == [i],
                'Private witness independently checked against every original label')
    require(uncovered is not None, 'Diagnostics are explicit noncovers')
    parents, derivations = dp(clauses, variable)
    unique = {canonical(c):c for indices,c in derivations}
    require(len(unique) == expected_unique, 'Expected number of distinct DP clauses')
    require(all(prefix(c) == expected_prefix for c in unique.values()), 'Expected prefix status')
    other_variables = sorted(set().union(*(set(c) for c in clauses)) - {variable})
    untouched = [c for c in clauses if variable not in c]
    checks, fully_covered_fibres, satisfying_extensions = 0, 0, 0
    extension_histogram, extension_examples = {}, {}
    for values in product(*(range(p) for p,k in other_variables)):
        state = dict(zip(other_variables,values))
        extension_count = 0
        for a in range(variable[0]):
            state[variable] = a
            extension_count += not any(falsifies(c,state) for c in clauses)
        state.pop(variable)
        reduced_sat = not any(falsifies(c,state) for c in [*untouched,*unique.values()])
        require((extension_count > 0) == reduced_sat, 'DP is exact existential quantification')
        checks += 1
        fully_covered_fibres += extension_count == 0
        satisfying_extensions += extension_count
        extension_histogram[extension_count] = extension_histogram.get(extension_count,0)+1
        extension_examples.setdefault(extension_count,canonical(state))
    result = dict(name=name,period=period,original_classes=[dict(residue=a,modulus=d,private=private[i]) for i,(a,d) in enumerate(originals)],
                  uncovered=uncovered,original_union_mass=str(Fraction(covered_count,period)),
                  original_reciprocal_sum=str(sum((Fraction(1,d) for a,d in originals),Fraction())),
                  eliminated_variable=list(variable),literal_occurrences=[len(v) for v in parents],
                  generated_count=len(derivations),unique_count=len(unique),
                  generated=[dict(parents=list(ids),literals=canonical(c),ap=list(as_ap(c)) if prefix(c) else None) for ids,c in derivations],
                  finite_dp_checks=checks,fully_covered_fibre_fraction=str(Fraction(fully_covered_fibres,checks)),
                  projected_support_size=checks-fully_covered_fibres,satisfying_extension_total=satisfying_extensions,
                  extension_histogram=extension_histogram,extension_examples=extension_examples,
                  private_modular_checks=len(originals)**2)
    if not expected_prefix:
        require(len(unique)==1, 'One cylinder in interior example')
        c = next(iter(unique.values()))
        lifted = [n for n in range(period) if falsifies(c,clause(n,period))]
        require(lifted == [0,875,1000], 'Interior hole lifts to three equal-modulus APs')
        require(len({(lifted[(i+1)%3]-lifted[i])%period for i in range(3)})>1,
                'The pullback is not a single AP in the full cyclic group')
        result['lifted_residues'] = lifted
        result['lifted_modulus'] = period
    return result


def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None, 'Readable source')
    value=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def actual_autarky(base):
    producer=load_module('sat_actual_hn_source',base/'frontier/whole-cover/hn_majorant_reduction.py')
    value=producer.calculate(base)
    io=load_module('sat_prefix_certificate_io',base/'certificate_io.py')
    artifact=io.read_artifact_bytes(base/'certificates/source_norms/hn_majorant_reduction.json')
    stored=json.loads(artifact,object_pairs_hook=io._unique)
    require(json.loads(json.dumps(value))==stored,'Actual 226-class canonical certificate replay')
    originals=value['original_classes']
    assignment={(13,1):12}
    touched,retained=[],[]
    for i,entry in enumerate(originals):
        c=clause(entry['residue'],entry['modulus'])
        if set(c).intersection(assignment):
            require(any(assignment[v]!=c[v] for v in assignment if v in c),
                    'Autarky satisfies every touched original clause')
            touched.append(i)
        else:
            retained.append(i)
    require(touched==list(range(205,226)),'Autarky deletes exactly 21 original future labels')
    require(retained==list(range(205)),'The 204 original head labels and current remain literal')
    heights={}
    for entry in originals:
        for p,h in factors(entry['modulus']).items():
            heights[p]=max(heights.get(p,0),h)
    global_bound=1+sum(h*(p-1) for p,h in heights.items())
    require(global_bound==293>226,'Existing Simpson whole-lcm condition excludes whole minimality')
    return dict(source_certificate_sha256=sha256(artifact).hexdigest(),
                original_count=226,retained_original_indices=retained,deleted_original_indices=touched,
                autarky={'prime':13,'digit':1,'value':12},global_lcm_heights=heights,
                simpson_minimal_whole_cover_required_count=global_bound,
                conclusion='Label-preserving equisatisfiable reduction on an already-certified actual noncover; no new family exclusion or source-mass identity.')


def calculate(base):
    old=[1,3,5,15,9,25,27,125]
    branch=[0,1,1,2,3,4,5,6]
    a=[crt([(b,7),(0,g)]) if g>1 else (b,7) for b,g in zip(branch,old)]
    one=verify_example('same derived clause despite original irredundancy',a,(7,1),1,True)
    old=[3,5,15,9,27,81,243,729]
    branch=[0,1,1,2,3,4,5,6]
    residues=[0,0,6,0,0,0,0,0] # 6 mod15 means 0 mod3, 1 mod5.
    b=[crt([(u,7),(r,g)]) for u,r,g in zip(branch,residues,old)]
    two=verify_example('nondegenerate singular DP repeats derived modulus',b,(7,1),2,True)
    require([row['ap'] for row in two['generated']]==[[0,3645],[2916,3645]],'Two residues of one derived modulus')
    require(two['generated_count']==two['unique_count']==2,'Singular step is nondegenerate')
    require(two['original_union_mass']==two['original_reciprocal_sum'],'Original APs are pairwise disjoint')
    require(len([k for k in two['extension_histogram'] if k>0])>1,
            'Projection has nonconstant positive witness multiplicities')
    paired={}
    for y in (1,3):
        witnesses=[crt([(y,3645),(a,7)])[0] for a in range(7)]
        paired[y]=sum(all(n%d != r for r,d in b) for n in witnesses)
    require(paired=={1:7,3:6},'Same projected legality has unequal original witness multiplicity')
    two['paired_projection_witnesses']=paired
    three=verify_example('interior digit elimination leaves nonprefix support',
                         [crt([(a,9),(0,5**(a+1))]) for a in range(3)],(3,1),1,False)
    return dict(schema='sat-ap-reduction-diagnostics-v1',examples=[one,two,three],actual226_autarky=actual_autarky(base))


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    value=calculate(args.base.resolve())
    print('PASS',sum(e['finite_dp_checks'] for e in value['examples']),'complete DP fibre checks;',
          sum(e['private_modular_checks'] for e in value['examples']),'private modular checks; exact actual226 replay and 21-label autarky')

if __name__=='__main__':
    main()
