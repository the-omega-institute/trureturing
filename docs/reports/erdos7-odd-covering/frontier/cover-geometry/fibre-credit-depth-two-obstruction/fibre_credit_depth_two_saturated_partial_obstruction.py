#!/usr/bin/env python3
"""Exact saturated partial comparisons and a common-event relaxation obstruction."""
from fractions import Fraction as F
from itertools import product, combinations
from pathlib import Path
from math import prod
from hashlib import sha256
import argparse,json

def need(ok,message):
    if not ok:raise RuntimeError(message)

def partial_profiles():
    MODS=(3,5,9,15,45)
    points=[x for x in range(45) if all(x%m!=a for m,a in ((3,0),(9,4),(5,0),(15,1),(45,37)))]
    n=len(points)
    groups={m:sorted({tuple(i for i,x in enumerate(points) if x%m==a) for a in range(m)}-{()}) for m in MODS}
    need(n==17,'first shape')
    nmin=6*n-sum(max(map(len,groups[m])) for m in MODS)
    need(nmin==77,'315 minimum mass')
    subsets=[tuple(s) for r in range(1,4) for s in combinations((3,5,7),r)]
    mean_expected={ (3,):F(35,83),(5,):F(7,9),(7,):F(6,11),(3,5):F(1,11),
     (3,7):F(5,77),(5,7):F(9,77),(3,5,7):F(1,77)}

    def quantile_cost(ha,hb,t):
        aa=list(ha);bb=list(hb);i=j=0;value=0
        while i<len(aa) and j<len(bb):
            if aa[i]==0:i+=1;continue
            if bb[j]==0:j+=1;continue
            mass=min(aa[i],bb[j]);aa[i]-=mass;bb[j]-=mass
            value+=mass*max(i+j-t,0)
        need(sum(aa)==sum(bb)==0,'equal quantile mass')
        return value

    profiles=[]
    for S in subsets:
        selected=[d for d in (1,3,5,9,15,45) if (3 not in S or d%9==0) and (5 not in S or d%5==0)]
        constant=int(1 in selected); qmods=[m for m in selected if m>1]
        maxB=len(selected)
        loads=[];histograms=set()
        for choice in product(*(groups[m] for m in qmods)):
            load=[constant]*n
            for cylinder in choice:
                for i in cylinder:load[i]+=1
            hist=tuple(load.count(v) for v in range(maxB+1))
            loads.append((tuple(load),hist));histograms.add(hist)
        K=maxB if 7 in S else 2*maxB
        caps=[];iterations=[];minimum_slacks=[]
        for t in range(K):
            if 7 in S:
                numerator=max(sum(max(v-t,0) for v in load) for load,hist in loads)
                g=F(numerator,nmin)
                steps=0;slack=F(0)
            else:
                coupling={ha:max(quantile_cost(ha,hb,t) for hb in histograms) for ha in histograms}
                data=[]
                for load,hist in loads:
                    vals=tuple(max(v-t,0) for v in load)
                    data.append((vals,5*sum(vals)+coupling[hist]))
                g=F(0)
                for steps in range(100):
                    nextg=g
                    for vals,base in data:
                        active_sum=0;active_count=0
                        for m in MODS:
                            chosen=max(groups[m],key=lambda C:sum(max(g-vals[i],0) for i in C))
                            for i in chosen:
                                if vals[i]<g:
                                    active_sum+=vals[i];active_count+=1
                        ratio=F(base-active_sum,6*n-active_count)
                        nextg=max(nextg,ratio)
                    if nextg==g:break
                    g=nextg
                else:raise RuntimeError('D2 exact branch iteration did not stabilize')
                slacks=[]
                for vals,base in data:
                    credit=sum(max(sum(max(g-vals[i],0) for i in C) for C in groups[m]) for m in MODS)
                    slacks.append(6*n*g-base-credit)
                slack=min(slacks)
                need(slack>=0,'full exact D2 inequality at every partial layout')
            caps.append(g);iterations.append(steps);minimum_slacks.append(str(slack))
        need(caps[0]==mean_expected[S],'independent earlier partial mean')
        ext=[1+caps[0]]+caps+[F(0),F(0)]
        probs=[ext[y]-2*ext[y+1]+ext[y+2] for y in range(K+1)]
        need(all(p>=0 for p in probs) and sum(probs)==1,'genuine zero-inclusive comparison probability')
        for t in range(K):
            need(sum((p*max(y-t,0) for y,p in enumerate(probs)),F(0))==caps[t],'exact stoploss recovery')
        profiles.append({'S':list(S),'K':K,'query45_slots':selected,'old45_layouts':len(loads),'histograms':len(histograms),
                         'stoploss_caps':list(map(str,caps)),'probabilities':list(map(str,probs)),'D2_iterations':iterations,'minimum_slacks':minimum_slacks})

    P=(11,13,17,19,23)
    c=F(185,86)

    def ntail(p,n):
        if n==0:return F(1)
        if n==1:return F(1,p-1)
        return F(1,(p-2)*p**(n-1))
    def pmass(p,n):return ntail(p,n)-ntail(p,n+1)
    def tailmean(p,m):
        if m==0:return 1+F(1,p-2)
        if m==1:return F(2*p-3,(p-2)*(p-1))
        return ntail(p,m)*(m+1+F(1,p-1))
    def lowmean(p,m):return 1+F(1,p-2)-tailmean(p,m)

    # Exact below-cutoff probability and first moment; all tails handled analytically.
    def product_low(base,cutoff,full):
        if base==0:return F(1),F(0)
        if not full:
            return (F(1),F(base)) if base<=cutoff else (F(0),F(0))
        if len(full)==1:
            p=full[0];m=cutoff//base
            return 1-ntail(p,m),base*lowmean(p,m)
        p,q=full; prob=F(0);first=F(0)
        for a in range(cutoff//base):
            scale=base*(a+1);m=cutoff//scale;pa=pmass(p,a)
            prob+=pa*(1-ntail(q,m));first+=pa*scale*lowmean(q,m)
        return prob,first

    cases=[]
    for full in ((),(23,),(19,23)):
        theta=[F(1,p-2 if p in full else p-1) for p in P]
        mult=prod((1+t for t in theta),start=F(1))
        delta=c+2+sum(theta)-(c+1)*mult
        bern=[F(1)]
        for p in P:
            if p in full:continue
            new=[F(0)]*(len(bern)+1)
            for j,pj in enumerate(bern):
                new[j]+=pj*F(p-2,p-1);new[j+1]+=pj*F(1,p-1)
            bern=new
        results=[]
        for profile in profiles:
            probs=list(map(F,profile['probabilities']))
            rawmean=F(profile['stoploss_caps'][0])*mult
            def low(cutoff):
                probability=F(0);first=F(0)
                for y,py in enumerate(probs):
                    for j,pj in enumerate(bern):
                        if not py or not pj:continue
                        ppart,mpart=product_low(y*2**j,cutoff,full)
                        probability+=py*pj*ppart;first+=py*pj*mpart
                return probability,first
            for threshold in range(0,1000):
                mass_le,first_le=low(threshold)
                if 1-mass_le<=delta:break
            else:raise RuntimeError('no quantile found within fixed diagnostic bound1000')
            mass_lt=low(threshold-1)[0] if threshold else F(0)
            need(1-mass_le<=delta<=1-mass_lt,'one-event upper tail quantile')
            beta=threshold+(rawmean-first_le-threshold*(1-mass_le))/delta
            results.append({'S':profile['S'],'quantile':threshold,'P_gt_quantile':str(1-mass_le),'P_ge_quantile':str(1-mass_lt),
                            'conditional_mean_upper':str(beta),'conditional_mean_decimal':float(beta),
                            'weighted_debit':str(beta*prod((F(1,p-1) for p in profile['S']),start=F(1)))})
        lam=sum((F(r['weighted_debit']) for r in results),F(0))
        cases.append({'full_outside_axes':list(full),'retention_lower':str(delta),'partial_bounds':results,
                      'height_deletion_upper':str(lam),'height_deletion_upper_decimal':float(lam),'retention_test_passes':lam<1})

    out={'scope':'First canonical old315 shape. Seven genuine partial-query comparison laws, zero included; all exact D2. Outside product transport then one common actual-event restriction. Upper bounds, not actual CRT extremizers; not Lean.',
         'profiles':profiles,'cases':cases}
    return out

def joint_witness(partial,head):
    p=partial
    profiles=p['profiles']; shallow=p['cases'][0];delta=F(shallow['retention_lower'])
    full=head
    fullcaps=list(map(F,full['hinge_bounds']))
    weights=[prod((F(1,q-1) for q in r['S']),start=F(1)) for r in profiles]
    Ds=[prod(3 if q==3 else 2 for q in r['S']) for r in profiles]
    probabilities=[list(map(F,r['probabilities'])) for r in profiles]
    # Base ancestor-completion interface also remains valid in this relaxation.
    for ps,D in zip(probabilities,Ds):
        for t in range(12):
            lhs=sum((w*max(max(1,D*y)-t,0) for y,w in enumerate(ps)),F(0))
            need(lhs<=fullcaps[t],'all full-query hinges dominate ancestor-completed partial comparator')

    cdf=[];cuts={F(0),F(1)}
    for ps in probabilities:
        run=F(0);row=[]
        for q in ps:
            run+=q;row.append(run);cuts.add(run)
        cdf.append(row)
    cuts=sorted(cuts)
    core=[]
    for lo,hi in zip(cuts,cuts[1:]):
        if lo==hi:continue
        u=(lo+hi)/2
        values=tuple(next(y for y,c in enumerate(row) if u<c) for row in cdf)
        core.append((hi-lo,values))
    need(sum(w for w,v in core)==1,'one common core source')
    for i,ps in enumerate(probabilities):
        for y,py in enumerate(ps):
            need(sum((w for w,v in core if v[i]==y),F(0))==py,'exact core marginal')

    bern=[F(1)]
    for q in (11,13,17,19,23):
        new=[F(0)]*(len(bern)+1)
        for j,w in enumerate(bern):
            new[j]+=w*F(q-2,q-1);new[j+1]+=w*F(1,q-1)
        bern=new
    raw=[]
    for w,values in core:
        for j,pj in enumerate(bern):
            vv=tuple(y*2**j for y in values)
            score=sum((a*b for a,b in zip(weights,vv)),F(0))
            raw.append({'mass':w*pj,'values':vv,'score':score,'multiplier':2**j})
    need(sum(r['mass'] for r in raw)==1,'joint product-source normalization')
    # Restrict ONCE by the upper delta tail of the aggregate marked score.
    raw.sort(key=lambda r:r['score'],reverse=True)
    remaining=delta
    retained=[]
    for r in raw:
        take=min(remaining,r['mass'])
        if take:
            retained.append({**r,'retained_mass':take})
            remaining-=take
    need(remaining==0,'one common retained event has prescribed mass')
    means=[sum((r['retained_mass']*r['values'][i] for r in retained),F(0))/delta for i in range(7)]
    score=sum((a*b for a,b in zip(weights,means)),F(0))
    need(score>1,'strict failure of the height union-debit criterion on a common-source relaxation')
    # Individual optimal CVaR bounds remain valid for this single common event.
    for x,r in zip(means,shallow['partial_bounds']):
        need(x<=F(r['conditional_mean_upper']),'individual uniform bound consistent with common event')
    # Explicit upper-tail ordering, including the possible fractional final atom.
    cut=retained[-1]['score']
    above=sum((r['mass'] for r in raw if r['score']>cut),F(0))
    atorabove=sum((r['mass'] for r in raw if r['score']>=cut),F(0))
    need(above<=delta<=atorabove,'aggregate quantile certificate')
    output={'scope':'Finite common-source relaxation witness. NOT actual CRT residues or actual congruence-generated mixed event. All seven partial ICX marginals and their full-query ancestor-completion ICX inequalities are preserved.',
            'core_atoms':len(core),'raw_atoms':len(raw),'retained_atoms':len(retained),'retained_mass':str(delta),
            'aggregate_quantile':str(cut),'P_score_gt_quantile':str(above),'P_score_ge_quantile':str(atorabove),
            'conditional_partial_means':list(map(str,means)),'conditional_partial_means_decimal':list(map(float,means)),
            'joint_height_debit':str(score),'joint_height_debit_decimal':float(score),
            'raw_atoms_data':[{'mass':str(r['mass']),'values':list(r['values']),'score':str(r['score']),'multiplier':r['multiplier']} for r in raw],
            'retained_atoms_data':[{'retained_mass':str(r['retained_mass']),'values':list(r['values']),'score':str(r['score'])} for r in retained]}
    return output

DEPENDENCIES={'fibre_credit_depth_two_old23_full_height.json': 'ca998ef3ce5e1043cbd1a78a4f9cd4306b12cfb781b219729aa916f0ba016ede', 'fibre_credit_depth_two_core_height_joint_bridge.json': '385db85e5f01bb21534c4e31ed9f089d0871360193236dab1f1fbc42bb08a491'}

def calculate():
    directory=Path(__file__).resolve().parent
    for name,digest in DEPENDENCIES.items():
        need(sha256((directory/name).read_bytes()).hexdigest()==digest,'pinned partial source: '+name)
    head=json.loads((directory/'fibre_credit_depth_two_old23_full_height.json').read_text())['rows'][0]
    core=json.loads((directory/'fibre_credit_depth_two_core_height_joint_bridge.json').read_text())['partial_bounds'][0]
    partial=partial_profiles()
    for row in partial['profiles']:
        key=','.join(map(str,row['S']))
        need(row['stoploss_caps'][0]==core['partial_query_caps'][key]['cap'],'partial means match the inherited core interface')
    joint=joint_witness(partial,head)
    need(joint['joint_height_debit']=='491126096519693/111577640854680','one shared retained event obstruction')
    return {'scope':'Ordinary exact partial D2 comparisons and one finite joint relaxation; not actual CRT extrema, not Lean.',
            'dependency_hashes':DEPENDENCIES,'partial':partial,'joint_relaxation':joint}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args(); result=calculate()
    rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output is None:
        need(json.loads(Path(__file__).resolve().with_suffix('.json').read_text())==result,
             'retained result agrees with saturated partial comparison')
        print(rendered,end='')
    else:args.output.write_text(rendered)

if __name__=='__main__':main()
