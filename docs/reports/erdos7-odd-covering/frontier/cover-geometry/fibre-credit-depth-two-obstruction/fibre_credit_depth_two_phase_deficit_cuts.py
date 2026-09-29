#!/usr/bin/env python3
"""Exact short phase-deficit cuts and failure of all one-row summaries.

Uses only literal old core classes and actual per-label phase dictionaries.
Every claimed one-row projection is witnessed by one actual dictionary;
there is no convex-mixture or solver premise.
"""
from fractions import Fraction as F
from pathlib import Path
import json

def need(ok, message):
    if not ok:
        raise RuntimeError(message)

D=(3,5,7,9,15,21,35,45,63,105,315)
CORE=((3,0),(5,0),(7,0),(9,4),(15,11),(21,8),
      (35,9),(45,1),(63,1),(105,59),(315,179))
X=tuple(x for x in range(315) if all(x%d!=a for d,a in CORE))
need(len(X)==75,'actual core rows')
N={d:[sum(x%d==a for x in X) for a in range(d)] for d in D}
M={d:max(N[d]) for d in D}
MAXTOTAL=sum(M.values())
need(MAXTOTAL==146,'maximum achievable total load')

def load(phases):
    need(len(phases)==len(D) and all(type(a) is int and 0<=a<d for d,a in zip(D,phases)),
         'one legal fixed phase per original label')
    return {x:sum(x%d==a for d,a in zip(D,phases)) for x in X}

def cut(weights):
    """Smallest multiplier retaining the max-total face support intercept."""
    theta=F(0)
    face_total=0
    evidence=[]
    for d in D:
        rewards=[sum(weights.get(x,0) for x in X if x%d==a) for a in range(d)]
        face=max(rewards[a] for a in range(d) if N[d][a]==M[d])
        face_total+=face
        local=F(0)
        for a in range(d):
            delta=M[d]-N[d][a]
            if delta:
                local=max(local,F(max(0,rewards[a]-face),delta))
        theta=max(theta,local)
        evidence.append(dict(d=d,maximum_size=M[d],face_reward=face,
                             minimal_multiplier=str(local),
                             options=sorted({(M[d]-N[d][a],rewards[a]) for a in range(d)})))
    # Independent direct support evaluation over all numerical phases.
    direct=sum(max(theta*N[d][a]+sum(weights.get(x,0) for x in X if x%d==a)
                   for a in range(d)) for d in D)
    need(direct==theta*MAXTOTAL+face_total,'support equals lifted face intercept')
    scale=theta.denominator
    return dict(weights=sorted(weights.items()),theta=str(theta),face_bound=face_total,
                integer_total_coefficient=int(theta*scale),
                integer_row_coefficients=[[x,v*scale] for x,v in sorted(weights.items())],
                integer_rhs=int(direct*scale),label_evidence=evidence)

def exact_deficit_support(weights):
    """Exact (deficit, best reward) DP, choosing each label once."""
    states={0:0}
    for d in D:
        options={(M[d]-N[d][a],sum(weights.get(x,0) for x in X if x%d==a))
                 for a in range(d)}
        new={}
        for deficit,reward in states.items():
            for delta,gain in options:
                key=deficit+delta
                new[key]=max(new.get(key,-10**9),reward+gain)
        states=new
    return states

single=cut({16:-1})
pair=cut({16:1,61:-1})
need((single['integer_total_coefficient'],single['integer_row_coefficients'],single['integer_rhs'])
     ==(1,[[16,-9]],137),'sharp single-row deficit cut')
need((pair['integer_total_coefficient'],pair['integer_row_coefficients'],pair['integer_rhs'])
     ==(1,[[16,1],[61,-1]],147),'short joint-row deficit cut')

baseline=(2,2,6,7,2,5,2,16,25,2,2)
witness16=baseline[:-1]+(16,)
witness61=tuple(7 if d==45 else a for d,a in zip(D,baseline))
dictionaries={'baseline':baseline,'row16':witness16,'row61':witness61}
loads={name:load(phases) for name,phases in dictionaries.items()}
h=loads['baseline'].copy()
need(sum(h.values())==146 and max(h.values())==6 and (h[16],h[61])==(2,2),
     'actual baseline properties')
h[16]+=1
h[61]-=1
need(sum(h.values())==146 and max(h.values())==6 and min(h.values())>=0,
     'perturbed integer load retains total and all high-level bounds')

# This is stronger than checking finitely many scalar linear inequalities:
# for each row, the ENTIRE (H,h_x) pair is realized by one explicit dictionary.
projections=[]
for x in X:
    name='row16' if x==16 else 'row61' if x==61 else 'baseline'
    witness=loads[name]
    need(sum(witness.values())==sum(h.values()) and witness[x]==h[x],
         'actual full one-row projection witness')
    projections.append(dict(row=x,claimed_total=146,claimed_load=h[x],dictionary=name))
pair_lhs=sum(h.values())+h[16]-h[61]
need(pair_lhs==148 and pair_lhs>147,'joint cut separates all-single-row relaxation')

# Report the exact conditional capacities near the exposed face.  The
# universal cuts above are directly proved; these finite DPs are additional
# exact scalar projections and need no phase-vector enumeration.
single_dp=exact_deficit_support({16:-1})
pair_dp=exact_deficit_support({16:1,61:-1})
need(single_dp[0]==-1 and single_dp[8]==-1 and single_dp[9]==0,
     'first feasible deficit for zero row16 load is nine')
need(pair_dp[0]==1 and pair_dp[1]==2,'first two conditional pair bounds')

forced=[]
for x in X:
    c=cut({x:-1})
    if c['face_bound']<0:
        forced.append([x,c['theta'],c['face_bound']])
need(len(forced)==61,'complete max-total forced-row inventory')
need(sum(x%9==7 for x,_,_ in forced)==23,'mod9 forced rows')
need(sum(x%3==2 for x,_,_ in forced)==38,'mod3 forced rows')

out=dict(scope="Actual phase-deficit cuts and exact one-row witnesses which fail a joint cut; no row-envelope obstruction is claimed for this load",core_originals=CORE,original_labels=D,core_rows=X,
         maximum_total=MAXTOTAL,single_row_cut=single,pair_cut=pair,
         actual_dictionaries=dictionaries,relaxed_load_pairs=sorted(h.items()),
         projection_witnesses=projections,relaxed_pair_lhs=pair_lhs,
         exact_deficit_support=[dict(deficit=d,row16_negative_max=single_dp[d],
                                     row16_minus_row61_max=pair_dp[d]) for d in range(13)],
         max_total_forced_rows=forced,
         all_single_row_linear_cuts_satisfied=True,
         actual_joint_realization=False,lean_verification=False)
result = json.loads(json.dumps(out))


if __name__ == "__main__":
    expected = json.loads(Path(__file__).with_suffix(".json").read_text())
    need(result == expected, "retained result agrees with exact recomputation")
    print(json.dumps(result, indent=2))
