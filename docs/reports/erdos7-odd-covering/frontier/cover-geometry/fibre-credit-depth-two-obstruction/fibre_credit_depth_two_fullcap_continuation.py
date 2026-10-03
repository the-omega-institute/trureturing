#!/usr/bin/env python3
"""Literal CRT pair: all current caps agree, but one legal continuation splits J.

The common prior is explicitly weighted and supported, not full Haar.
Only standard-library exact arithmetic is used. No Lean or all-source
obstruction is asserted.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import product,combinations
from math import prod,lcm
from pathlib import Path
import argparse,json

def need(ok,msg):
    if not ok:raise RuntimeError(msg)
OLD=((3,0),(9,4),(5,0),(15,1),(45,37),(7,0),(21,0),(35,0),(63,0),(105,0),(315,0))
P=(11,13,17);CARRIER=315*prod(P);W=791
X=tuple(x for x in range(315) if all(x%m!=a for m,a in OLD))
D=tuple(d for d in range(1,316) if 315%d==0)
SCOPES=tuple(J for k in range(4) for J in combinations(range(3),k))
K={d:(F(3,2) if d%9==0 else 1)*(F(5,4) if d%5==0 else 1)*(F(7,6) if d%7==0 else 1)-1 for d in D}
EXT=F(437,396)

def crt(pairs):
    modulus=prod(m for m,a in pairs)
    need(all(lcm(m,n)==m*n for i,(m,a) in enumerate(pairs) for n,b in pairs[i+1:]),'pairwise coprime CRT factors')
    value=sum(a*(modulus//m)*pow(modulus//m,-1,m) for m,a in pairs)%modulus
    need(all(value%m==a%m for m,a in pairs),'literal CRT reconstruction')
    return modulus,value

def raw_prior():
    cells={}
    for x in X:
        for y in product(range(3,11),range(3,13),range(3,17)):
            m,z=crt(((315,x),)+tuple(zip(P,y)));need(m==CARRIER and z not in cells,'unique background cell')
            cells[z]=1
    for x in (2,11):
        for y in product((1,2),repeat=3):
            m,z=crt(((315,x),)+tuple(zip(P,y)));need(z not in cells,'corner separate from background');cells[z]=W
    return cells

def originals(name):
    labels=((5,7,15,21),(35,45,63,105));rows=[]
    for ix,x in enumerate((2,11)):
        deleted_parity=1 if name=='A' else 0
        holes=[y for y in product((1,2),repeat=3) if sum(t-1 for t in y)%2==deleted_parity]
        need(len(holes)==4,'four parity holes')
        for d,y in zip(labels[ix],holes):
            need(x%d!=(11 if x==2 else 2)%d,'old label separates corner rows')
            rows.append(crt(((d,x%d),)+tuple(zip(P,y))))
    allrows=OLD+tuple((p,0) for p in (11,13,17,19,23))+tuple(rows)
    need(len(allrows)==len({m for m,a in allrows})==24,'24 distinct numerical originals')
    need(all(m>1 and m%2==1 for m,a in allrows),'odd nonunit originals')
    return tuple(rows),allrows

def hist(cells,m):
    out=Counter()
    for z,w in cells.items():out[z%m]+=w
    return out

def conditional_marginals(cells):
    table={}
    for J in SCOPES:
        if len(J)>2:continue
        h=Counter()
        for z,w in cells.items():h[(z%315,tuple(z%P[i] for i in J))]+=w
        table[J]=h
    return table

def profile(cells,prior_hists=None):
    rows=[];cost=F(0);credit=F(0)
    for d in D:
        if K[d]==0:continue
        for J in SCOPES:
            m=d*prod(P[i] for i in J);h=hist(cells,m);cap=max(h.values(),default=0);cost+=K[d]*cap
            record=dict(d=d,scope=list(J),modulus=m,cap=cap)
            if prior_hists is not None:
                h0=prior_hists[(d,J)];cap0=max(h0.values(),default=0)
                deleted={a:v-h[a] for a,v in h0.items()};need(all(v>=0 for v in deleted.values()),'submeasure cylinder differences')
                cr=min([cap0]+[cap0-v+deleted[a] for a,v in h0.items()])
                need(cr==cap0-cap,'all-phase slack-plus-intersection credit')
                credit+=K[d]*cr;record['credit']=cr
            rows.append(record)
    return rows,EXT*cost,EXT*credit

def calculate():
    need(len(X)==102 and 2 in X and 11 in X,'old actual support')
    prior=raw_prior();mass0=sum(prior.values());need(mass0==126896,'common weighted prior mass')
    need(all(all(z%m!=a for m,a in OLD) and all(z%p!=0 for p in P) for z in prior),'common supported prior')
    h0={(d,J):hist(prior,d*prod(P[i] for i in J)) for d in D if K[d]>0 for J in SCOPES}
    p0,R0,_=profile(prior)
    sources={};results={};tables={}
    for name in ('A','B'):
        mixed,allrows=originals(name)
        cells={z:w for z,w in prior.items() if all(z%m!=a for m,a in mixed)};sources[name]=cells
        mass=sum(cells.values());need(mass==120568 and mass0-mass==6328,'equal actual retention')
        need(all(all(z%m!=a for m,a in mixed) for z in cells),'literal actual mixed survivors')
        rows,R,credit=profile(cells,h0);margin=mass-R
        need(margin==(mass0-R0)-(mass0-mass)+credit,'joint deletion credit telescope')
        results[name]=dict(actual_originals=[list(t) for t in allrows],mixed_originals=[list(t) for t in mixed],
             actual_surviving_cells=len(cells),survivor_mass=mass,higher_core_debit=str(R),margin=str(margin),
             lost_mass=mass0-mass,total_deletion_credit=str(credit),normalized_margin=str(margin/mass0),profile=rows)
        tables[name]=conditional_marginals(cells)
    need(tables['A']==tables['B'],'complete old and all conditional singleton/pair marginal tables agree')
    differences=[]
    for a,b in zip(results['A']['profile'],results['B']['profile']):
        need((a['d'],a['scope'])==(b['d'],b['scope']),'query matching')
        if a['cap']!=b['cap']:differences.append(dict(d=a['d'],scope=a['scope'],cap_A=a['cap'],cap_B=b['cap']))
    need(differences==[],'all80 base query caps and hence all320 five-axis caps agree')
    need(F(results['A']['margin'])==F(results['B']['margin'])==F(459757,9504)>0,'same positive current certificate')
    background={z:w for z,w in prior.items() if w==1};bgrows,bgR,_=profile(background);bgmargin=sum(background.values())-bgR
    need(bgmargin==F(2912955,64)>0,'same actual common background has a positive certificate')
    need(all(z in sources[name] for name in ('A','B') for z in background),'positive background survives either family')
    # One actual next original also separates the sources despite the equal pairwise boundary.
    next_original=crt(((315,11),)+tuple(zip(P,(1,1,1))))
    need(next_original[0] not in {m for m,a in results['A']['actual_originals']},'new continuation has unused distinct numerical label')
    next_loss={name:sum(w for z,w in cells.items() if z%next_original[0]==next_original[1]) for name,cells in sources.items()}
    need(next_loss=={'A':791,'B':0},'same actual continuation differs')
    continuation={}
    for name,cells in sources.items():
        m,a=next_original;after={z:w for z,w in cells.items() if z%m!=a}
        old_hist={(d,J):hist(cells,d*prod(P[i] for i in J)) for d in D if K[d]>0 for J in SCOPES}
        rows,R,credit=profile(after,old_hist);margin=sum(after.values())-R
        need(margin==F(results[name]['margin'])-next_loss[name]+credit,'actual continuation credit identity')
        changed=[dict(d=p['d'],scope=p['scope'],before=p['cap'],after=q['cap']) for p,q in zip(results[name]['profile'],rows) if p['cap']!=q['cap']]
        continuation[name]=dict(lost_mass=next_loss[name],remaining_mass=sum(after.values()),higher_core_debit=str(R),margin=str(margin),total_credit=str(credit),changed_base_caps=changed)
    need(continuation['A']['changed_base_caps']==[dict(d=9,scope=[],before=33208,after=32417)],'only shared saturated9 cap changes')
    need(continuation['B']['changed_base_caps']==[],'other source is unchanged')
    need(F(continuation['A']['margin'])==F(-2909903,9504)<0<F(continuation['B']['margin'])==F(459757,9504),'opposite signs after the same actual continuation')
    out=dict(scope=__doc__,old_carrier=315,three_axis_carrier=CARRIER,full_five_axis_carrier=CARRIER*19*23,
             prior_mass=mass0,corner_weight=W,background_cells=114240,corner_cells_before_deletions=16,
             free_outside_query_multiplier=str(EXT),results=results,equal_conditional_scopes=[list(J) for J in tables['A']],
             conditional_marginal_cells=sum(len(v) for v in tables['A'].values()),distinguishing_query_slots=differences,
             next_original=list(next_original),next_actual_losses=next_loss,continuation=continuation,current_nonzero_five_axis_query_caps=320,common_background_margin=str(bgmargin),
             common_background_normalized_margin=str(bgmargin/mass0),lean_verification=False,
             not_an_all_source_obstruction=True)
    need(all(z%next_original[0]!=next_original[1] for z in background),
         'common positive background survives the new original')
    return out

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args();result=calculate()
    rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output is None:
        need(json.loads(Path(__file__).resolve().with_suffix('.json').read_text())==result,
             'retained result agrees with the full-cap continuation pair')
        print(rendered,end='')
    else:args.output.write_text(rendered)

if __name__=='__main__':main()
