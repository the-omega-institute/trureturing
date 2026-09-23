#!/usr/bin/env python3
"""Exact pair-kernel and source-anchor bounds for arbitrary two old centers.

Computes finite upper envelopes covering every prime-adic separation depth.
Source mass, stochastic domination and original-family transfer are ordinary
proof inputs in report477. No Lean or unrestricted Erdős7 claim is made.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as F
from functools import reduce
from hashlib import sha256
from math import lcm, gcd
from pathlib import Path
import json

INPUTS = {
    "common_law_mass_tail.json": "3781704377f2ca6234ed55f3eff1a37d2f8665a3810b02c694aebdc2fc063cb4",
    "query_stoploss_completion.json": "44f871684942eb7dceb37c55880c9f9a49244d8bdd60134670ad80d10a3c587d",
    "two_center_kernel_domination.json": "2e35557ccf3f70ee31b8ca1d16255fce001e9a8ad9d47ba4528fa282d4357aa5",
}

def need(b, msg):
    if not b:
        raise ValueError(msg)


def capacity(a,b):
    return max(22-a,0)*max(28-b,0)-a

STATES=tuple((a,b) for a in range(1,22) for b in range(1,28) if capacity(a,b)>0)
STATE_SET=set(STATES)
SPLITS=tuple(range(19))+('infinity',)
CAPS=((7,F(3,2)),(11,F(5,3)),(13,F(3,2)),(17,F(2)),(19,F(9,5)))


def coordinate_good_weights(p,h,cap,pure5=False):
    # Each row is a literal joint valuation type of two paths in a p-ary tree.
    # Haar mass of a depth-k shell is (p-1)/p^(k+1).
    rows={}
    def put(u,v,w):
        key=(u+1,v+1)
        if key in STATE_SET:
            rows[key]=rows.get(key,F())+w
    if h=='infinity':
        for k in range(19):
            put(k,k,F(p-1,p**(k+1)))
    else:
        for k in range(h):
            put(k,k,F(p-1,p**(k+1)))
        put(h,h,F(p-2,p**(h+1)))
        for k in range(h+1,27):
            put(k,h,F(p-1,p**(k+1)))
            put(h,k,F(p-1,p**(k+1)))
    haar_baseline=rows[(1,1)]
    rows={key:cap*w for key,w in rows.items()}
    rows[(1,1)]=1-cap*(1-haar_baseline)
    if pure5:
        need(p==5 and cap==1,'pure5 scope')
        rows[(1,1)]-=F(1,4)
    mass=F(3,4) if pure5 else F(1)
    need(all(w>=0 for w in rows.values()) and sum(rows.values())<=mass,'positive comparison measure')
    return tuple((a,b,w) for (a,b),w in sorted(rows.items()) if w)


def monotone(table,den,mass):
    top=mass*den
    need(top.denominator==1,'mass denominator')
    top=top.numerator
    need(all(0<=v<=top for v in table.values()),'table probability range')
    for a,b in STATES:
        for nxt in ((a+1,b),(a,b+1)):
            need(table[(a,b)]<=table.get(nxt,top),'table not increasing')


def advance(table,den,p,cap,pure5=False):
    # Prior table has remaining mass one. Missing states already lost.
    distributions=[coordinate_good_weights(p,h,cap,pure5) for h in SPLITS]
    d=lcm(*(w.denominator for rows in distributions for _,_,w in rows))
    if pure5:d=lcm(d,4)
    introws=[tuple((a,b,(w*d).numerator) for a,b,w in rows) for rows in distributions]
    need(all((w*d).denominator==1 for rows in distributions for _,_,w in rows),'weight integrality')
    mass=F(3,4) if pure5 else F(1)
    newden=den*d;baseline=mass*newden
    need(baseline.denominator==1,'new mass integrality')
    baseline=baseline.numerator
    out={};choices={}
    for a,b in STATES:
        values=[]
        for rows in introws:
            deficit=sum(w*(den-table.get((a*x,b*y),den)) for x,y,w in rows)
            values.append(baseline-deficit)
        best=max(range(len(values)),key=values.__getitem__)
        out[(a,b)]=values[best];choices[(a,b)]=SPLITS[best]
        need(all(out[(a,b)]>=x for x in values),'majorant inequality')
    common=reduce(gcd,out.values(),newden)
    if common>1:
        newden//=common;out={k:v//common for k,v in out.items()}
    monotone(out,newden,mass)
    return out,newden,choices


def valuation(n,p):
    need(n!=0,'finite valuation called at zero')
    d=0
    while n%p==0:n//=p;d+=1
    return d

BAD=(22,28)
DEPTH=28

def local_distributions(p,E,forbidden):
    """Exact Haar valuation weights per root, denominator p**DEPTH.

    Prefixes determine membership in the anchor.  Every discarded depth is
    already BAD for every other coordinate, hence goes to one absorbing atom.
    Identical prefixes enumerate h=E,...,27; larger h has the same GOOD part.
    """
    den=p**DEPTH
    signatures={}
    raw=0
    for a in range(p**E):
      for b in range(p**E):
       for h in (range(E,DEPTH) if a==b else [valuation(a-b,p)]):
        raw+=1
        roots=[defaultdict(int) for _ in range(p)]
        for x in range(p**E):
          if any(x%m==r for m,r in forbidden):continue
          row=roots[x%p]
          def put(i,j,w):
            key=(i+1,j+1)
            if capacity(*key)<=0:key=BAD
            row[key]+=w
          if x!=a and x!=b:
            put(valuation(x-a,p),valuation(x-b,p),p**(DEPTH-E))
            continue
          before=sum(row.values())
          if a!=b:
            for j in range(E,DEPTH):
              w=(p-1)*p**(DEPTH-j-1)
              if x==a:put(j,h,w)
              else:put(h,j,w)
          else:
            for j in range(E,h):put(j,j,(p-1)*p**(DEPTH-j-1))
            put(h,h,(p-2)*p**(DEPTH-h-1))
            for j in range(h+1,DEPTH):
              w=(p-1)*p**(DEPTH-j-1)
              put(j,h,w);put(h,j,w)
          residual=p**(DEPTH-E)-(sum(row.values())-before)
          need(residual>=0,'negative tail residual')
          row[BAD]+=residual
        key=tuple(tuple(sorted((s,w) for s,w in r.items() if w)) for r in roots)
        for r,row in enumerate(roots):
          cells=sum(1 for x in range(p**E) if x%p==r and not any(x%m==s for m,s in forbidden))
          need(sum(row.values())==cells*p**(DEPTH-E),'root mass changed')
        signatures.setdefault(key,{'centres':(a,b,h),'roots':key})
    return tuple(signatures.values()),den,raw

def merge_roots(row,roots):
    out=defaultdict(int)
    for r in roots:
        for s,w in row['roots'][r]:out[s]+=w
    return tuple(sorted(out.items()))

def anchor_bound(table, den):
    p3,d3,raw3=local_distributions(3,3,((3,0),(9,1),(27,4)))
    p5,d5,raw5=local_distributions(5,2,((5,0),(25,1)))
    u3=[(merge_roots(row,(1,)),merge_roots(row,(2,))) for row in p3]
    u5=[(merge_roots(row,(1,2,3,4)),merge_roots(row,(1,3,4))) for row in p5]
    need(all(sum(w for _,w in r1)*27==5*d3 and sum(w for _,w in r2)*3==d3 for r1,r2 in u3),'ternary region masses')
    need(all(sum(w for _,w in v)*25==19*d5 and sum(w for _,w in v2)*25==14*d5 for v,v2 in u5),'quinary region masses')
    coords5=tuple(sorted({s for pair in u5 for row in pair for s,_ in row}))
    coords3=tuple(sorted({s for pair in u3 for row in pair for s,_ in row}))
    pairvalues={(s,t):table.get((s[0]*t[0],s[1]*t[1]),den) for s in coords3 for t in coords5}
    bound=F(61,4000)
    bigden=d3*d5*den
    best=-1;witness=None
    checks=0
    for i,(r1,r2) in enumerate(u3):
        e1={t:sum(w*pairvalues[(s,t)] for s,w in r1) for t in coords5}
        e2={t:sum(w*pairvalues[(s,t)] for s,w in r2) for t in coords5}
        for j,(v,v2) in enumerate(u5):
            numerator=sum(w*e1[t] for t,w in v)+sum(w*e2[t] for t,w in v2)
            need(numerator*bound.denominator<bound.numerator*bigden,'six-cylinder upper bound failed')
            checks+=1
            if numerator>best:best=numerator;witness=(i,j)
    exact=F(best,bigden)
    m7=F(7235955529,450000000000)
    need(m7-bound>F(1,1250),'source margin below target')
    i,j=witness
    result={'scope':'Six-cylinder completed anchor with coarse (a15,b27,c25)=(2,4,1); arbitrary pair centres at every old prime, with category fixed. Upper bounds the actual anchor survivor law by dropping all additional pure powers,45,75 and later mixed exclusions.',
      'raw_ternary_cases':raw3,'raw_quinary_cases':raw5,
      'distinct_ternary_distributions':len(p3),'distinct_quinary_distributions':len(p5),
      'checked_distribution_pairs':checks,'good_load_states':len(STATES),
      'upper_bound':str(bound),'exact_max':str(exact),'exact_max_float':float(exact),
      'max_representative':{'ternary':p3[i]['centres'],'quinary':p5[j]['centres']},
      'source_mass_lower':str(m7),'certified_margin':str(m7-bound),
      'margin_floor':'1/1250','head_haar_floor':'1/10395000',
      'tail_merging':'Every omitted shell has a valuation at least28 and is already BAD. All h>=27 give the same GOOD transitions; all actual larger or infinite depths are represented.',
      'integration':'Nonnegative R1 x V5 plus R2 x (V5 minus column2), with masses5/27,1/3,19/25,14/25.',
      'arithmetic':'Integer weights, exact signature deduplication, exact nonnegative integration, strict rational comparison in every case.'}
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def global_bound(table, den):
    table5, den5, _ = advance(table, den, 5, F(1), True)
    payoff = lambda a, b: F(table5[(a, b)], den5) if (a, b) in table5 else F(3, 4)
    results = []
    for h in SPLITS:
        rows = list(coordinate_good_weights(3, h, F(1)))
        baseline_remove = F(1, 3) if h == 0 else F(1, 2)
        rows = [(a, b, w - baseline_remove if (a, b) == (1, 1) else w)
                for a, b, w in rows]
        need(all(w >= 0 for _, _, w in rows), "positive full-pure3 comparison")
        mass = F(2, 3) if h == 0 else F(1, 2)
        bound = mass * F(3, 4) - sum((w * (F(3, 4) - payoff(a, b))
                                      for a, b, w in rows), F())
        if h == 0:
            weights = {(a, b): w for a, b, w in rows}
            need(weights[(2, 1)] >= F(1, 6) and weights[(1, 2)] >= F(1, 6),
                 "either extra pure3 deletion leaves a positive comparator")
            bound -= min(payoff(2, 1), payoff(1, 2)) / 6
        results.append({"ternary_split": h, "bad_upper": bound})
    worst = max(r["bad_upper"] for r in results)
    need(worst < F(17, 1000), "global arbitrary-pair bad bound")
    return {"all_ternary_splits": results, "exact_upper": worst,
            "exact_upper_decimal": float(worst), "simple_strict_upper": F(17, 1000)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", type=Path, default=Path(__file__).parent)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    data = {}
    for name, digest in INPUTS.items():
        raw = (args.input_dir / name).read_bytes()
        need(sha256(raw).hexdigest() == digest, "retained input identity: " + name)
        data[name] = json.loads(raw)
    source = data["common_law_mass_tail.json"]["common_seven_core_law"]
    need(tuple(F(c) for c in source["conditional_caps"]) == tuple(c for _, c in CAPS),
         "same-source conditional caps")
    density = F(source["unnormalized_joint_density_cap"])
    need(density == F(27, 2), "same-source joint density")
    table = {s: 0 for s in STATES}
    den = 1
    stages = []
    for p, cap in reversed(CAPS):
        table, den, choices = advance(table, den, p, cap)
        stages.append({"prime": p, "at_unit_loads": F(table[(1, 1)], den),
                       "chosen_separations": sorted(set(choices.values()),
                           key=lambda h: 99 if h == "infinity" else h)})
    universal = global_bound(table, den)
    anchor = anchor_bound(table, den)
    need(anchor["checked_distribution_pairs"] == 9504, "complete anchor signature pairs")

    prefix = data["query_stoploss_completion.json"]
    expected = {(a, b, c, j) for a in (1, 2) for b in (2, 4)
                for c in (1, 2) for j in range(1, 5)}
    seen = set()
    coarse = {}
    for row in prefix["rows"]:
        node = row["node"]
        key = (node[0], node[1], node[2], node[4])
        need(key in expected and key not in seen, "source vertex inventory")
        seen.add(key)
        mass = F(row["cores"]["7"]["live_mass_lower_cell_units"]) / 135
        group = key[:3]
        coarse[group] = min(coarse.get(group, mass), mass)
    need(seen == expected and prefix["basic_vertices"] == 32, "complete 32-vertex source data")
    m7 = F(source["unnormalized_mass_lower"])
    need(min(coarse.values()) == coarse[(2, 4, 1)] == m7, "source worst coarse geometry")
    margins = []
    for group, mass in sorted(coarse.items()):
        upper = F(anchor["upper_bound"]) if group == (2, 4, 1) else universal["simple_strict_upper"]
        margin = mass - upper
        need(margin > F(1, 1250), "positive good mass for every source coarse geometry")
        margins.append({"coarse": group, "source_mass_lower": mass,
                        "bad_mass_strict_upper": upper, "good_mass_strict_lower": margin})
    gap = min(row["good_mass_strict_lower"] for row in margins)
    need(gap == F(373455529, 450000000000), "uniform simple good mass")
    fibre = F(1, 616)
    need(min(capacity(a, b) for a, b in STATES) == 1, "universal positive integer fibre capacity")
    haar = gap * fibre / density
    need(haar > F(1, 10395000), "uniform arbitrary-two-center Haar reserve")
    prior = data["two_center_kernel_domination.json"]
    tail = prior["large_prime_tail"]
    need(F(prior["simple_strict_full_survivor_haar_lower"]) == F(1, 10395000)
         == F(tail["seed_mass_strict_lower"]), "same retained tail seed threshold")
    need(tail["head_primes"] == [3, 5, 7, 11, 13, 17, 19, 23, 29]
         and tail["cutoff"] == 500000000, "retained tail scope")
    tail_gap = F(1, 10395000) - F(tail["tail_loss_upper"])
    need(tail_gap == F(tail["remaining_mass_strict_lower"]) > F(1, 75000000),
         "retained unrestricted-large-prime continuation")
    result = {
        "scope": "Exact all-height pair-kernel and anchor comparison for category-fixed arbitrary two centers. Source continuous-anchor interpolation and original-family transfer are ordinary proof inputs, not Lean certification or unrestricted Erdos7 settlement.",
        "inputs": INPUTS, "source_producers_rerun": False,
        "good_load_states": len(STATES), "later_separations": SPLITS,
        "later_stages": stages, "global_full_pure_bound": universal,
        "six_cylinder_anchor": anchor, "source_coarse_margins": margins,
        "uniform_good_mass_strict_lower": gap,
        "simple_good_mass_strict_lower": F(1, 1250),
        "good_fibre_haar_lower": fibre,
        "uniform_head_haar_strict_lower": haar,
        "simple_head_haar_strict_lower": F(1, 10395000),
        "tail": {"cutoff": tail["cutoff"], "remaining_distorted_mass_strict_lower": tail_gap,
                 "simple_strict_lower": F(1, 75000000),
                 "scope": "Reuse report476's retained Chapter33 tail inequality with the same Haar seed threshold; arbitrary original tail phases, heights and shared prime supports."},
        "noncoverage_scope": {
            "head_primes": tail["head_primes"],
            "centers": "arbitrary fixed a,b; equality allowed; no coordinate agreement or separation required",
            "category_rule": "23-only and23/29-cross old residues at a;29-only at b",
            "old_only_residues_and_all_finite_heights": "arbitrary",
            "new_coordinate_residues": "arbitrary",
            "tail_primes": "any finite set above500000000",
            "tail_touching_original_classes": "unrestricted phases and joint supports",
            "unrestricted_erdos7_resolved": False}}
    output = json.dumps(encode(result), indent=2) + "\n"
    if args.output:
        args.output.write_text(output)
        print("PASS: adaptive pair kernels,9504 anchor pairs,32 source vertices,and arbitrary-two-center noncoverage constants.")
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
