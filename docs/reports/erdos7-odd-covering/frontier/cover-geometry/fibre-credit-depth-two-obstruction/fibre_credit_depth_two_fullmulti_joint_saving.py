#!/usr/bin/env python3
"""Literal-only joint certificate for a fixed full shallow distinct-modulus family.

Input contains numerical [modulus, phase] classes, fixed forest edges,
and optional explicit nonnegative weights on the actual core rows.
No final survivor count, final query maximum, tensor, optimization output,
or random seed is read. Source construction and all intersections are
recomputed from those literal originals using exact integer arithmetic.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations
from math import prod,gcd
from pathlib import Path
from hashlib import sha256
import argparse,json

def need(ok,msg):
    if not ok:raise RuntimeError(msg)
D=(1,3,5,7,9,15,21,35,45,63,105,315)
K48=(0,0,12,8,24,12,8,22,42,36,22,57)

def evaluate(raw):
    P=tuple(raw['outside_primes']);Q=raw['carrier']
    need(P==(11,13,17,19,23) and Q==315*prod(P),'declared shallow carrier')
    literals=raw['originals'];need(len(literals)==len({m for m,a in literals})==383,'383 distinct numerical originals')
    expected={d*prod(P[j] for j in range(5) if J>>j&1) for d in D for J in range(32)}-{1}
    need({m for m,a in literals}==expected,'every nonunit shallow slot present exactly once')
    rules=[]
    for m,a in literals:
        need(type(m) is int and type(a) is int and m>1 and m%2==1 and 0<=a<m and Q%m==0,'literal legal original')
        d=gcd(m,315);J=sum(1<<j for j,p in enumerate(P) if m%p==0)
        need(m==d*prod(P[j] for j in range(5) if J>>j&1),'exact numerical slot decoding')
        rules.append(dict(m=m,a=a,d=d,J=J,old=a%d,roots=[a%p if J>>j&1 else None for j,p in enumerate(P)]))
    core=[q for q in rules if q['J']==0];single=[q for q in rules if q['J'].bit_count()==1];multi=[q for q in rules if q['J'].bit_count()>=2]
    need((len(core),len(single),len(multi))==(11,60,312),'exact numerical source/deletion partition')
    X=[x for x in range(315) if all(x%q['m']!=q['a'] for q in core)]
    need(bool(X),'nonempty actual old315 source')
    if "row_weights" in raw:
        entries=raw["row_weights"]
        need(len(entries)==len({x for x,w in entries})==len(X),"one literal weight for every actual core row")
        weightmap=dict(entries);need(set(weightmap)==set(X),"exact actual core row weight domain")
        rowweights=[weightmap[x] for x in X]
        need(all(type(w) is int and 0<=w<=1000000000 for w in rowweights) and max(rowweights)>0,"bounded nonnegative integer weights")
    else:rowweights=[1]*len(X)
    A=[]
    for x in X:
        row=[set(range(p)) for p in P]
        for q in single:
            if x%q['d']==q['old']:
                j=q['J'].bit_length()-1;row[j].discard(q['roots'][j])
        A.append(row)
    r=[[len(s) for s in row] for row in A];rowmass=[rowweights[i]*prod(v) for i,v in enumerate(r)];mass=sum(rowmass)
    need(mass>0,'nonempty actual singleton product source')
    common=[sorted(set.intersection(*(row[j] for row in A))) for j in range(5)]
    need(all(common[j] for j in range(1,5)),'global untouched13/17/19/23 query roots')
    caps=[];capdict={};debit48=0
    for d,k in zip(D,K48):
        if not k:continue
        groups=defaultdict(list)
        for i,x in enumerate(X):groups[x%d].append(i)
        for J in range(32):
            cap=0;witness=None
            for a,indices in groups.items():
                for t in range(P[0]) if J&1 else (None,):
                    v=sum(rowweights[i]*prod(r[i][j] for j in range(5) if not (J>>j&1)) for i in indices if t is None or t in A[i][0])
                    if witness is None or v>cap:cap=v;witness=[a,t]
            need(witness is not None,'complete exact initial query maximum')
            capdict[d,J]=cap;caps.append([d,J,k,cap,witness]);debit48+=k*cap
    need(len(caps)==320,'all initial nonzero-coefficient query slots')
    n=len(X)
    def intersect(qs):
        for q,s in combinations(qs,2):
            if (q['a']-s['a'])%gcd(q['m'],s['m']):return [0]*n
        J=0;roots=[None]*5
        for q in qs:
            J|=q['J']
            for j in range(5):
                if q['J']>>j&1:
                    need(roots[j] is None or roots[j]==q['roots'][j],'CRT compatibility agrees with coordinate phases')
                    roots[j]=q['roots'][j]
        out=[]
        for i,x in enumerate(X):
            if any(x%q['d']!=q['old'] for q in qs) or any(roots[j] not in A[i][j] for j in range(5) if J>>j&1):out.append(0)
            else:out.append(rowweights[i]*prod(r[i][j] for j in range(5) if not (J>>j&1)))
        return out
    single_vectors=[intersect([q]) for q in multi];S1=[sum(v[i] for v in single_vectors) for i in range(n)]
    S2=[0]*n;pairvalues={};pairmass={}
    for i,j in combinations(range(len(multi)),2):
        v=intersect([multi[i],multi[j]])
        for x,h in enumerate(v):S2[x]+=h
        key=tuple(sorted((multi[i]['m'],multi[j]['m'])));pairmass[key]=sum(v)
        if any(v):pairvalues[key]=v
    parent={q['m']:q['m'] for q in multi}
    def find(a):
        while parent[a]!=a:parent[a]=parent[parent[a]];a=parent[a]
        return a
    forest=[];seen=set();savedrow=[0]*n
    for m,k in raw['forest_edges']:
        need(m in parent and k in parent and m!=k,'forest uses actual multioutside labels')
        key=tuple(sorted((m,k)));need(key not in seen,'no duplicated forest edge');seen.add(key)
        a,b=find(m),find(k);need(a!=b,'fixed forest is acyclic');parent[a]=b
        v=pairvalues.get(key,[0]*n)
        for i,h in enumerate(v):savedrow[i]+=h
        forest.append([m,k,pairmass[key]])
    saving=sum(savedrow);upperrow=[a-b for a,b in zip(S1,savedrow)];upper=sum(upperrow)
    lowerrow=[max(0,a-b) for a,b in zip(S1,S2)]
    need(all(0<=lo<=rm and up>=lo for lo,up,rm in zip(lowerrow,upperrow,rowmass)),'consistent per-row Bonferroni/forest mass bounds')
    credit48=0;creditrows=[]
    for d,k in zip(D,K48):
        if not k:continue
        groups=defaultdict(lambda:[0,0])
        for i,x in enumerate(X):groups[x%d][0]+=rowmass[i];groups[x%d][1]+=lowerrow[i]
        phases=[[a,old,loss,old-loss] for a,(old,loss) in sorted(groups.items())]
        oldcap=max((p[1] for p in phases),default=0);newupper=max((p[3] for p in phases),default=0)
        need(oldcap==capdict[d,0] and 0<=newupper<=oldcap,'all old phases considered for credit')
        eta=oldcap-newupper;credit48+=k*eta
        creditrows.append(dict(d=d,kappa48=k,old_cap=oldcap,post_cap_upper=newupper,certified_credit=eta,phase_evidence=phases))
    initial48=48*mass-debit48;naive48=initial48-48*sum(S1);forest48=initial48-48*upper
    lower48=forest48+credit48;masslower=mass-upper;debitupper48=debit48-credit48
    need(lower48==48*masslower-debitupper48,'same-source joint balance')
    need(lower48>0,'strict compact certificate')
    haar=F(lower48,48*Q*max(rowweights))
    return dict(scope=__doc__,carrier=Q,original_count=383,core_rows=X,row_weights=rowweights,maximum_weight=max(rowweights),initial_row_data=[dict(x=x,allowed_roots=[sorted(a) for a in A[i]],mass=rowmass[i],event_sum=S1[i],pair_sum=S2[i],forest_saved=savedrow[i],removed_mass_lower=lowerrow[i],removed_mass_upper=upperrow[i]) for i,x in enumerate(X)],
          singleton_mass=mass,common_query_roots=common,initial_caps=caps,singleton_debit48=debit48,singleton_margin48=initial48,
          multi_event_count=312,event_mass_sum=sum(S1),pair_intersection_count=len(pairmass),positive_pair_count=sum(v>0 for v in pairmass.values()),pair_intersection_sum=sum(S2),
          fixed_forest=forest,forest_saving=saving,removed_mass_upper=upper,old_query_credit=creditrows,certified_credit48=credit48,
          naive_margin_lower48=naive48,forest_only_margin_lower48=forest48,compact_margin_lower48=lower48,
          final_mass_lower=masslower,final_debit_upper48=debitupper48,Haar_survivor_lower=str(haar),
          uses_final_tensor_or_oracle=False,uniform_over_all_shallow_phases=False,lean_verification=False)

DEPENDENCIES = {'fibre_credit_depth_two_fullmulti_joint_input.json': '9d1e21705c4e618c70db324b143cf732371ceaf79e3470d4c66b8260bb6ae4e9'}

def calculate():
    directory=Path(__file__).resolve().parent
    need(len(DEPENDENCIES)==1,'complete joint-saving literal interface')
    for name,digest in DEPENDENCIES.items():
        need(sha256((directory/name).read_bytes()).hexdigest()==digest,'pinned joint-saving input: '+name)
    raw=json.loads((directory/'fibre_credit_depth_two_fullmulti_joint_input.json').read_text())
    result=evaluate(raw)
    need(result['compact_margin_lower48']==92922359 and F(result['Haar_survivor_lower'])>F(1,173),
         'declared literal family compact density')
    result['dependency_hashes']=DEPENDENCIES
    return result

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args();result=calculate()
    rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output is None:
        need(json.loads(Path(__file__).resolve().with_suffix('.json').read_text())==result,
             'retained result agrees with literal-only joint certificate')
        print(rendered,end='')
    else:args.output.write_text(rendered)

if __name__=='__main__':main()
