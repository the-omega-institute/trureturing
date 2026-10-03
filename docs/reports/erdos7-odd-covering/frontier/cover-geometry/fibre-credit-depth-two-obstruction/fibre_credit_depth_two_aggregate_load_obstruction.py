"""Exact obstruction to an aggregate-load relaxation and its unrealizability.

Literal loads and a rational dual are checked directly. This is not an
actual phase-family or covering counterexample. Report760 gives the proof.
"""
from pathlib import Path
from fractions import Fraction as F
from math import prod
from hashlib import sha256
import json


INPUT_SHA256 = "39a01e92aa18f8ab1ee37256c8773950f271a4c9824c728e30eb1b2ba203b01e"


def need(condition, message):
    if not condition:
        raise ValueError(message)


def calculate():
    source = Path(__file__).with_name("fibre_credit_depth_two_aggregate_load_obstruction_input.json")
    raw = source.read_bytes()
    need(sha256(raw).hexdigest() == INPUT_SHA256, "pinned literal input")
    c=json.loads(raw);D=c['dual_denominator'];need(type(D)is int and D>0,'positive integer denominator')
    P=c['minimal_outside_primes'];need(P==[11,13,17,19,23],'minimum ordered outside primes')
    div=[d for d in range(1,316) if 315%d==0];core=c['core_originals'];need(sorted(m for m,r in core)==div[1:],'11actual core numerical slots')
    need(all(0<=r<m for m,r in core),'core phase ranges')
    X=[x for x in range(315) if all(x%m!=r for m,r in core)]
    need([x for x,h in c['row_load_pairs']]==X,'unique ordered full old rows');load=dict(c['row_load_pairs']);need(sorted(load)==X and len(X)==75,'literal full75 core rows')
    need(all(len(h)==5 and all(type(t)is int and 0<=t<=6 for t in h) for h in load.values()),'loads are integers between0and6')
    totals=[sum(load[x][j] for x in X) for j in range(5)];need(totals==[146]*5,'every-axis exact aggregate budget146')
    ell={x:[p-1-h for p,h in zip(P,load[x])] for x in X};need(all(min(v)>0 for v in ell.values()),'strictly positive denominator rows')
    budget={}
    for d in div:
        sat=[(p,t) for p,t in ((3,9),(5,5),(7,7)) if d%t==0]
        k=prod((F(p,p-1) for p,t in sat),start=F(1))-1
        for J in range(32):
            b=(k+(J.bit_count()>=2))*48*D
            if b:need(b.denominator==1,'integer slot budget');budget[d,J]=int(b)
    need(len(budget)==372,'372 nonzero robust slots')
    spent={slot:0 for slot in budget};dual={}
    for d,J,r,v in c['dual_entries']:
        need(all(type(z) is int for z in (d,J,r)) and (d,J) in budget and 0<=r<d,'valid old query phase')
        need(type(v)is int and v>0 and (d,J,r) not in dual,'distinct positive rational dual term')
        dual[d,J,r]=v;spent[d,J]+=v
    need(spent==budget,'every one of372 slot budgets exactly equals kappa+multi indicator')
    scores={}
    for x in X:
        score=F(0)
        for (d,J,r),v in dual.items():
            if x%d==r:score+=F(v,48*D*prod(ell[x][j] for j in range(5) if J>>j&1))
        scores[x]=score
    minimum=min(scores.values());need(minimum>1,'strict rowwise dual obstruction')


    # At aggregate equality146 every actual old cylinder would have to be maximal.
    maxima={};maxphases={}
    for d in div[1:]:
        sizes=[sum(x%d==r for x in X) for r in range(d)]
        maxima[d]=max(sizes);maxphases[d]=[r for r,n in enumerate(sizes) if n==max(sizes)]
    need(sum(maxima.values())==146,'actual independent old-label cardinality upper budget')
    need(maxphases[9]==[7] and maxima[9]==23,'unique maximal mod9phase')
    need(16 in X and 16%9==7 and load[16][0]==0,'literal axis0 row16 violates forced mod9hit')
    cut_bound=sum(max(sum(x!=16 and x%d==r for x in X) for r in range(d)) for d in div[1:])
    cut_value=sum(load[x][0] for x in X if x!=16)
    need(cut_bound==145 and cut_value==146,'explicit integer phase-mask support cut')
    result={'passed':True,'scope':'Aggregate-load relaxation counterexample only; literal loads provably not realizable by actual11old labels','core_rows':75,'load_totals':totals,'maximum_load':6,'high_layer_counts':{str(t):[sum(load[x][j]>=t for x in X) for j in range(5)] for t in (7,8,9,10)},'slot_budgets_checked':372,'nonzero_dual_terms':len(dual),'minimum_row_score':str(minimum),'strict_cost_lower':str(minimum),'row_scores':[[x,str(scores[x])] for x in X],'nonrealizability':{'axis':0,'old_row':16,'declared_load':0,'sum_independent_old_maxima':146,'forced_label':9,'unique_maximizing_phase':7,'maximum_cylinder_size':23,'forced_load_lower':1,'support_cut':'sum_(x in X except16) h_0(x) <=145','actual_cut_bound':cut_bound,'literal_cut_value':cut_value},'lean_verification':False}
    result["input_sha256"] = INPUT_SHA256
    return result


if __name__ == "__main__":
    result = calculate()
    expected = json.loads(Path(__file__).with_suffix(".json").read_text())
    need(result == expected, "retained result agrees with exact recomputation")
    print(json.dumps(result, indent=2))
