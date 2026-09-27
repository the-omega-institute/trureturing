"""Exact finite checks for the actual 5/7 anchor and q=11 cap obstruction.

This checks the explicitly fixed CRT residue family, not arbitrary query
factorization. Output records finite verification only; the infinite limit is
proved by the formulas in the accompanying note.
"""
from collections import Counter
from fractions import Fraction as F
from pathlib import Path
import argparse
import json

checks = 0

def check(a, b, name):
    global checks
    checks += 1
    if a != b:
        raise AssertionError((name, a, b))

def crt(parts):
    residue, modulus = 0, 1
    for r, m in parts:
        residue += modulus * (((r-residue) * pow(modulus, -1, m)) % m)
        modulus *= m
        residue %= modulus
    return residue, modulus

def comb(p, color, height):
    return [(color*p**(i-1), p**i) for i in range(1, height+1)]

def contains(word, x):
    r, m = word
    return x % m == r

def qwords(channel, height):
    # P: roots 0,1, continuation root 2; X: 3,4,5; Y: 6,7,8.
    base = {"P": 0, "X": 3, "Y": 6}[channel]
    return [((base+j-1) if e == 1 else base+2+j*11**(e-1), 11**e)
            for e in range(1, height+1) for j in (1, 2)]

results = []
for K in (1, 2, 3):
    p5 = comb(5, 1, K) + comb(5, 2, K)
    p7 = comb(7, 1, K) + comb(7, 2, K)
    mixed_anchor = [crt([u, v]) for u in comb(5, 4, K)
                    for color in (4, 5) for v in comb(7, color, K)]
    originals = p5 + p7 + mixed_anchor
    # These old cofactors are fixed, and apply identically to every q slot.
    inventory = [(w, "X") for w in comb(5, 3, K)]
    inventory += [(w, "Y") for w in comb(7, 3, K)]
    inventory += [(crt([u, v]), "X") for u in comb(5, 4, K)
                  for v in comb(7, 6, K)]
    period = 5**K * 7**K
    hist = Counter()
    witnesses = {}
    channel_hist = Counter()
    for x in range(period):
        if any(contains(w, x) for w in originals):
            continue
        channels = tuple(sorted(ch for w, ch in inventory if contains(w, x)))
        n = len(channels)
        check(len(set(channels)), n, "active channels never repeat")
        hist[n] += 1
        channel_hist[channels] += 1
        witnesses.setdefault(n, x)
    l5, l7 = F(1- F(1,5**K),4), F(1-F(1,7**K),6)
    z5, z7 = F(1,5**K), F(1,7**K)
    L = 1-2*l5-2*l7+2*l5*l7
    Z = z5*(1-3*l7)+l5*z7
    P2 = l5*l7
    P1 = L-Z-P2
    check(set(hist), {0,1,2}, "all count categories present")
    for n, target in ((0,Z),(1,P1),(2,P2)):
        check(F(hist[n],period), target, "actual anchor category mass")
    check(sum(hist.values(),0)*F(1,period),L,"actual anchor mass")
    check(Z, z5/F(2)+z7/F(4)+z5*z7/F(4), "expanded zero count")
    check(L,(3+5*z5+3*z7+z5*z7)/12,"expanded anchor mass")
    check(Counter(m for _,m in originals),
          Counter({m:2 for _,m in originals}),"two copies each anchor label")

    for H in (1,2,3):
        eps = F(1,11**H)
        channels = {c:qwords(c,H) for c in ("P","X","Y")}
        allq = sum(channels.values(),[])
        for i, (r,m) in enumerate(allq):
            for s,n in allq[i+1:]:
                check(r % min(m,n) == s % min(m,n), False, "q prefix disjoint")
        family = originals + channels["P"] + [crt([w,qw])
                  for w,ch in inventory for qw in channels[ch]]
        counts = Counter(m for _,m in family)
        check(set(counts.values()),{2},"exactly two copies per full numerical label")
        check(len(family),len(set(family)),"no duplicate complete residue")
        # Check literal CRT events at a witness of each old count category.
        integrals = {"v":F(0),"cap_deficit":F(0),"G":F(0),"loss":F(0)}
        for n,x in witnesses.items():
            occupied = []
            for qx in range(11**H):
                fullx, _ = crt([(x,period),(qx,11**H)])
                occupied.append(any(contains(w,fullx) for w in family[len(originals):]))
            g = 1-F(sum(occupied),11**H)
            check(g,F(4-n,5)+F(n+1,5)*eps,"literal CRT q survivor")
            r = F(sum(any(contains(w,qx) for w in channels["P"])
                      for qx in range(11**H)),11**H)
            delta = 1-5*r
            check(delta,eps,"actual pure current deficit")
            beta_total = sum((F(10,2*11**e) for e in range(1,H+1)
                              for j in (1,2)),F(0))
            b = beta_total * min(n,1)
            G = beta_total * max(n-1,0)
            v = delta+1-b
            cap = min(F(5,3),1/g)
            loss = max(F(0),1-F(5,3)*g)
            check(F(5,3)*g,1+F(1,3)*(v-G),"retained PU2 is equality")
            mass = F(hist[n],period)
            for key,val in (("v",v),("cap_deficit",F(5,3)-cap),("G",G),("loss",loss)):
                integrals[key] += mass*val
        check(integrals["v"],Z+eps*(2*L-Z),"integrated effective deficit")
        check(integrals["cap_deficit"],Z*5*(1+eps)/(3*(4+eps))
              +P1*10*eps/(3*(3+2*eps)),"integrated cap deficit")
        check(integrals["G"],(1-eps)*P2,"actual integrated hinge")
        check(integrals["loss"],(F(1,3)-eps)*P2,"actual integrated loss")
        slack = F(1,3)*integrals["G"]-integrals["loss"]
        check(slack,F(2,3)*eps*P2,"count bound slack")
        results.append({"K":K,"H":H,"old_period":period,
                        "original_labels":len(counts),
                        "mass":str(L),"zero_count_mass":str(Z),
                        **{k:str(v) for k,v in integrals.items()},
                        "count_slack":str(slack)})
check(F(97,840)-F(1,24),F(31,420),"surviving comparison slack")
target=F(257,51)
kreq=F(6168733163201163811,1650097635185615616000)
saving=F(31,1260)
query=target-(target-2)*(saving-kreq)
check(query,F(100057015925264522393,20108716701186713600),"full-query consumer")
check(saving>kreq,True,"saving exceeds required mass")
result={"checks":checks,"cases":results,"uniform_mass_saving":str(saving),
        "full_query_bound":str(query),"full_query_bound_decimal":float(query),
        "scope":"Fixed actual 5/7 and first11 family; arbitrary later13/17/19 two-copy rows. No unrestricted noncoverage or Lean verification."}
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output",type=Path,default=Path(__file__).with_suffix(".json"))
args=parser.parse_args()
args.output.write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps({"checks":checks,"full_query_bound_decimal":float(query)},indent=2))
