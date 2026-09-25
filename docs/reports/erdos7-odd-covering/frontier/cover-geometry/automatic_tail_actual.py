#!/usr/bin/env python3
"""Independent exact replay of an actual family failing an automatic tail gate.

The finite family has 149 distinct numerical moduli, one globally fixed CRT
residue each. Its actual selected PA source is reconstructed independently.
No candidate producer is imported. No unrestricted covering or Lean claim.
"""
from argparse import ArgumentParser
from collections import defaultdict
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import prod
from pathlib import Path
import json

Q=(5,7,11,13,17,19)
LABELS=(5, 7, 11, 13, 35, 25, 17, 19, 55, 65, 49, 85, 77, 95, 91, 175, 125, 119, 133, 245, 143, 121, 385, 275, 455, 187, 325, 169, 209, 221, 595, 247, 425, 665, 475, 343, 715, 605, 323, 289, 539, 875, 625, 361, 935)
PINS={
'pa_complete_suffix_debits.json':'b1b204f8728c64ed9265e91d78d3072a2e77f64f6efca57512f3e58f0bdf3ccc',
'height_three_clipping_envelope.json':'276d7e266a86ed8e5a1c9da2982b219725c2738bc4ad19da1243bf8575543685'}

def ex(x):return {'exact':str(x),'decimal':float(x)}

def exponents(d):
    out=[]
    for q in Q:
        k=0
        while d%q==0:d//=q;k+=1
        out.append(k)
    if d!=1:raise ValueError('non-Q cofactor')
    return tuple(out)

def main():
    ap=ArgumentParser(description=__doc__)
    ap.add_argument('--source-dir',type=Path,default=Path(__file__).resolve().parent)
    ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=ap.parse_args();checks=[]
    def need(name,condition):
        if not condition:raise ValueError('FAILED: '+name)
        checks.append(name)
    sources={}
    for name,pin in PINS.items():
        b=(args.source_dir/name).read_bytes();need('source pin '+name,sha256(b).hexdigest()==pin)
        sources[name]=json.loads(b)
    B=F(sources['pa_complete_suffix_debits.json']['joint_bound'])
    K2=B-2
    alpha=min(F(c['alpha']) for c in sources['pa_complete_suffix_debits.json']['corners'])
    K3=max(F(c['K_integer'][3]) for c in sources['height_three_clipping_envelope.json']['corners'])
    tau_star=(39581-7693*B-490*K3)/1110
    need('same clipped gate',tau_star==F(21218460281840396929028797,380636632468201812726474000))
    labels=LABELS;need('45 distinct nonunit Q labels',len(labels)==len(set(labels))==45 and all(d>1 for d in labels))
    vectors=[exponents(d) for d in labels]
    ts=[t for t in range(81) if t%3!=1 and t%9!=3]
    pure_masks={};survival={};source_rows=[];selected={}
    originals=[]
    def original(e,d,t,r,label):
        a=r%d if e==0 else (t%(3**e) if d==1 else
             r+d*(((t-r)*pow(d,-1,3**e))%(3**e)))
        m=3**e*d
        if not(0<=a<m and a%d==r%d and a%(3**e)==t%(3**e)):
            raise ValueError('CRT failure '+label)
        row={'e':e,'d':d,'t':t,'r':r,'modulus':m,'phase':a,'label':label}
        originals.append(row);return row
    original(1,1,1,0,'pure3');original(2,1,3,0,'pure9')
    for q in Q:
        pairs={1:(0,1)}
        blocks=[{a for a in range(q**3) if a%(q**h)==r}
                for h,pair in pairs.items() for r in pair]
        need('q='+str(q)+' selected cylinders pairwise disjoint',
             all(blocks[i].isdisjoint(blocks[j]) for i in range(len(blocks)) for j in range(i)))
        forbidden=set().union(*blocks);pure_masks[q]=forbidden
        g=F(q**3-len(forbidden),q**3);survival[q]=g
        need('q='+str(q)+' actual pure survival',g==F(q-2,q))
        need('q='+str(q)+' entire root2 retained',all(a not in forbidden for a in range(2,q**3,q)))
        for h,pair in pairs.items():
            selected[q**h]=list(pair)
            original(0,q**h,0,pair[0],'selected-first-'+str(q)+'-'+str(h))
            original(1,q**h,2,pair[1],'selected-second-'+str(q)+'-'+str(h))
        cap={11:F(5,3),13:F(3,2),17:F(2),19:F(9,5)}.get(q)
        if cap:need('q='+str(q)+' actual later cap inactive',1/g<cap)
        source_rows.append({'q':q,'survival':ex(g),'density':ex(1/g),'later_cap':ex(cap) if cap else None})
    deep=[]
    for i,d in enumerate(labels):
        for e,t in ((4,ts[i]),(5,ts[(i+1)%45]),(6,ts[(i+2)%45]+81)):
            row=original(e,d,t,2,'deep-'+str(e)+'-'+str(i));deep.append(row)
    need('149 distinct odd numerical original moduli',len(originals)==149
         and len({r['modulus'] for r in originals})==149
         and all(r['modulus']>1 and r['modulus']%2 for r in originals))
    need('selected shallow phases exactly the12 originals',len(selected)==6
         and all(r['e']>=4 or r['d']==1 or r['r'] in selected[r['d']] for r in originals))
    need('fixed original deep phases',len(deep)==135 and all(r['r']==2 for r in deep))
    # The selected PA law has no mixed Q constraints. The5/7 prefix remains
    # raw pure-survivor product; every later row normalizes its own pure set.
    # One final normalization gives the full product stated here.
    source_density=prod((1/survival[q] for q in Q),start=F(1))
    actual_RQ=prod((1+1/(survival[q]*(q-1)) for q in Q),start=F(1))-1
    need('actual complete source query norm below supplier',actual_RQ==F(214267985,147806208)<B)
    gate=F(566,49)
    Rcrit=(gate-1-(3*K2-3+(gate-3)*K3)/27)/2
    haar_source=F(49,5544)*alpha*(Rcrit-actual_RQ)
    need('exact source-only threshold',Rcrit==F(1461204049288174906748586781,302451810663922521463738800))
    need('actual source passes source-only criterion',actual_RQ<Rcrit and haar_source>0)
    need('full source-only normalization is positive', K3 < 27)
    for rr in (actual_RQ, F(24,5), Rcrit):
        for tt in (F(0), K3/2, K3):
            retained = 1-tt/27
            raw_bound = 1+2*rr+(3*K2-3-3*tt)/27
            need('source-only joint margin R='+str(rr)+' tau='+str(tt),
                 gate*retained-raw_bound == 2*(Rcrit-rr)+(gate-3)*(K3-tt)/27)
    need('source-only nine-prime Haar coefficient',
         F(27*49*2,299376) == F(49,5544))
    pure_source_cap = prod((F(q-2,q-3) for q in Q),start=F(1))-1
    need('pure selected sources lie below source-only gate',
         pure_source_cap == F(47063,28672) and pure_source_cap < Rcrit)
    need('pure selected later caps remain inactive',
         all(F(q-1,q-3) < cap for q,cap in ((11,F(5,3)),(13,F(3,2)),(17,F(2)),(19,F(9,5)))))
    maxp=tuple(max(v[j] for v in vectors) for j in range(6))
    need('1620 actual incidence patterns',prod(e+1 for e in maxp)==1620)
    laws=[]
    for q,h in zip(Q,maxp):
        g=survival[q]
        law=[1-F(1,q)/g]+[(F(1,q**v)-F(1,q**(v+1)))/g for v in range(1,h)]+[F(1,q**h)/g]
        need('q='+str(q)+' incidence partition normalized',sum(law,F())==1 and min(law)>=0)
        laws.append(law)
    # Independent ordinary sets on the full modulus729, rather than the
    # discovery program's bit masks or its shortcut excluding small hit sets.
    A={a for a in range(729) if a%9 in (0,6)}
    C={a for a in range(729) if a%3==2}
    need('actual two-root carrier sizes',len(A)==162 and len(C)==243 and A.isdisjoint(C))
    blocks=[]
    for i in range(45):
        rows=[r for r in deep if r['d']==labels[i]]
        blocks.append(set().union(*({a for a in range(729) if a%(3**r['e'])==r['t']} for r in rows)))
    need('all deep ternary classes stay within pure survivors',all(b<=A|C for b in blocks))
    tau=F();total=F();meanW=F();hist=defaultdict(F);control_count=0
    zeroA=F();zeroC=F();zeroBoth=F()
    for state in product(*(range(h+1) for h in maxp)):
        probability=prod((law[v] for law,v in zip(laws,state)),start=F(1))
        active=[i for i,v in enumerate(vectors) if all(a<=b for a,b in zip(v,state))]
        removed=set().union(*(blocks[i] for i in active)) if active else set()
        ca=F(len(A-removed),162);cb=F(len(C-removed),243)
        W=12*(1-ca)+18*(1-cb)
        if W!=F(2,27)*len(removed):raise ValueError('actual reserve identity')
        T=max(W-F(16,3),F())
        tau+=probability*T;meanW+=probability*W;total+=probability
        hist[len(removed)]+=probability
        if not ca:zeroA+=probability
        if not cb:zeroC+=probability
        if not ca and not cb:zeroBoth+=probability
        control_count+=1
    need('all1620 full-mask reserve controls',control_count==1620 and total==1)
    need('exact actual clipping tail',tau==F(428853838918,5843456994375))
    need('automatic strict tail gate fails on actual PA source',tau>tau_star)
    need('actual damage mean respects query bound',meanW<=actual_RQ)
    need('histogram reconstructs tail',sum((p*max(F(2*n,27)-F(16,3),F()) for n,p in hist.items()),F())==tau)
    out={'schema':'automatic-tail-actual-v1',
         'statement':'One finite actual family satisfying the fixed pure3 and shallow two-phase hypotheses has E_nu(W-16/3)+>tau_star under its actual569 PA source. Thus the clipped tail condition is not automatic for this prescribed selector/source.',
         'scope':'Does not refute clipped transport, eventwise CJ6, existence of another good source or selector, or odd-covering nonexistence. Source full query norm is computed exactly and is far below conservative B. Ordinary finite arithmetic, no Lean.',
         'cofactor_table':labels,'deep_ternary_phase_rule':'At cofactor index i=0..44, e4:t_i; e5:t_((i+1) mod45); e6:t_((i+2) mod45)+81. t is the increasing pure-survivor residue list modulo81.',
         'sources':[{'path':name,'sha256':pin} for name,pin in PINS.items()],
         'original_count':149,'originals':originals,
         'source_rows':source_rows,'selected_phases':{str(d):v for d,v in selected.items()},
         'source_density':ex(source_density),'actual_complete_RQ':ex(actual_RQ),'B':ex(B),
         'full_query_proof':'The root2 cylinder survives all pure deletions. For every q^e, its mass1/(g_q q^e) attains the density upper bound; product factorization gives the complete norm product_q(1+1/(g_q(q-1)))-1, with the unit removed once.',
         'max_cofactor_exponents':maxp,'actual_incidence_patterns':control_count,
         'ternary_resolution':729,'tau':ex(tau),'tau_star':ex(tau_star),'tail_excess':ex(tau-tau_star),
         'pure_selected_source_query_upper':ex(pure_source_cap),'source_only_Rcrit':ex(Rcrit),'source_only_query_margin':ex(Rcrit-actual_RQ),'source_only_Haar_lower':ex(haar_source),
         'mean_W':ex(meanW),'zero_A_mass':ex(zeroA),'zero_B_mass':ex(zeroC),'joint_zero_mass':ex(zeroBoth),
         'deleted_ternary_cell_histogram':{str(n):str(p) for n,p in sorted(hist.items())},
         'check_count':len(checks),'checks':checks}
    args.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'checks':len(checks),'originals':len(originals),'patterns':control_count,
                      'tau':str(tau),'actual_RQ':str(actual_RQ)}))

if __name__=='__main__':main()
