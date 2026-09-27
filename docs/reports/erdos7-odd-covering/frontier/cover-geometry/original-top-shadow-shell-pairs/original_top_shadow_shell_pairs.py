#!/usr/bin/env python3
"""Exact original-label top-shadow/shell-pair controls under one uniform source.

Includes the distinct-odd18-label NONCOVER and repeated-modulus whole-cover
controls. No finite control establishes unrestricted odd noncoverage.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations
from math import gcd,lcm,prod
from pathlib import Path
import argparse
import json


def require(ok,message):
    if not ok:raise ValueError(message)


def factor(n):
    out={};p=2
    while p*p<=n:
        while n%p==0:out[p]=out.get(p,0)+1;n//=p
        p+=1
    if n>1:out[n]=out.get(n,0)+1
    return out


def bits(mask):
    while mask:
        low=mask&-mask
        yield low.bit_length()-1
        mask-=low


def pi_pairs(r,M):
    require(M>=1,'positive support-bin count')
    q,b=divmod(r,M)
    return b*q*(q+1)//2+(M-b)*q*(q-1)//2


def inputs():
    ms=(3,5,7,9,15,21,25,35,45,49,63,75,105,175,225,315,525,1575)
    aa=(2,2,3,1,10,12,16,29,9,0,27,18,63,124,30,111,195,735)
    ww=(5,7,3,1,25,33,16,169,9,0,90,18,63,124,30,111,195,2310)
    out=[dict(name='distinct_odd18_noncover',classes=list(zip(ms,aa)),witnesses=ww,
              expected_whole=False,expected_distinct=True,expected_odd=True)]
    out.append(dict(name='distinct_even_L60_whole_cover',
        classes=[(2,1),(4,2),(3,1),(6,2),(5,1),(10,2),(20,8),(15,0),(30,24)],
        original_names=['D1','D2','P1','P2','Q1','Q2','Q3','T1','T2'],
        witnesses=(3,18,4,20,36,12,48,0,24),
        expected_whole=True,expected_distinct=True,expected_odd=False))
    for m in(3,25,225):
        out.append(dict(name='repeated_modulus_partition_'+str(m),classes=[(m,a) for a in range(m)],
                        witnesses=tuple(range(m)),expected_whole=True,expected_distinct=False,expected_odd=True))
    return out


def analyze(inp):
    classes=inp['classes'];L=lcm(*(m for m,a in classes));fac=factor(L);primes=tuple(fac)
    R=prod(primes);N=L//R;allmask=(1<<L)-1
    require(all(m>1 for m,a in classes),'all original moduli nonunit')
    odd=all(m%2 for m,a in classes)
    require(odd==inp['expected_odd'],'declared oddness scope')
    distinct=len({m for m,a in classes})==len(classes)
    require(distinct==inp['expected_distinct'],'declared numerical-distinctness scope')
    owners=[[] for x in range(L)];classmasks=[];info=[]
    for s,(m,a) in enumerate(classes):
        require(L%m==0,'all original moduli divideperiod')
        cm=0
        for x in range(a%m,L,m):owners[x].append(s);cm|=1<<x
        classmasks.append(cm)
        fs=factor(m);A=tuple(p for p in primes if fs.get(p,0)==fac[p]);P=prod(A)
        bar=m//P;require(N%bar==0,'lower index divides oneglobalN')
        theta=tuple((a%(p**fac[p]))//(p**(fac[p]-1)) for p in A)
        shadow=sum(1<<z for z in range(a%bar,N,bar))
        info.append(dict(s=s,m=m,a=a,A=A,P=P,bar=bar,theta=theta,shadow=shadow))
    private=[0]*len(classes);overlap=0;uncovered=0
    for x,oo in enumerate(owners):
        if len(oo)==1:private[oo[0]]|=1<<x
        elif len(oo)>1:overlap|=1<<x
        else:uncovered|=1<<x
    whole=uncovered==0
    require(whole==inp['expected_whole'],'declared whole-cover boundary')
    require(all(private),'every original class has actual privatepoints')
    for s,w in enumerate(inp['witnesses']):require(owners[w%L]==[s],'listed private witness')
    # Full class slicing is checked literally on the SAME residue source.
    slice_checks=0
    for d in info:
        for x in range(L):
            pred=(x%d['bar']==d['a']%d['bar'] and all(
                (x%(p**fac[p]))//(p**(fac[p]-1))==th for p,th in zip(d['A'],d['theta'])))
            require(pred==bool(classmasks[d['s']]>>x&1),'exact lower-shadow/top-phase classslice')
            slice_checks+=1
    if distinct:
        for s,t in combinations(range(len(info)),2):
            if info[s]['A']==info[t]['A']:require(info[s]['bar']!=info[t]['bar'],'same-top distinct original labels implydistinctlowerindices')
    lifted={}
    def lift(shadow):
        if shadow not in lifted:lifted[shadow]=sum(1<<x for x in range(L) if shadow>>(x%N)&1)
        return lifted[shadow]
    pairs=[];collision=0;crt_checks=0
    for s,t in combinations(range(len(info)),2):
        ds,dt=info[s],info[t]
        if not ds['A'] or ds['A']!=dt['A'] or ds['theta']==dt['theta']:continue
        sh=ds['shadow']&dt['shadow'];count=sh.bit_count();g=gcd(ds['bar'],dt['bar'])
        expected=Q(1,lcm(ds['bar'],dt['bar'])) if (ds['a']-dt['a'])%g==0 else Q(0)
        require(Q(count,N)==expected,'exact original-pair lower-shadow CRT capacity')
        pre=lift(sh);require(pre.bit_count()==count*R,'sameuniformsource lower-shadow lift')
        collision|=pre;crt_checks+=1
        pairs.append((s,t,expected,pre))
    top_labels=[d['s'] for d in info if d['A']]
    selections=[tuple(top_labels)]+[(s,) for s in top_labels]
    selections=list(dict.fromkeys(selections));saving_checks=0;selected_summaries=[]
    for selected in selections:
        selected_set=set(selected);U=0
        for s in selected:U|=private[s]
        rhs=Q(0)
        for s,t,c,pre in pairs:
            saving=1-Q(2-int(s in selected_set)-int(t in selected_set),info[s]['P'])
            actual=Q((U&pre).bit_count(),L)
            require(actual<=saving*c,'privacy savingunderoneuniformsource')
            rhs+=saving*c;saving_checks+=1
        missing=U&~collision
        if whole and odd:
            require(missing==0,'proper top-shadow collisioncover atallselectedprivatepoints')
            require(Q(U.bit_count(),L)<=rhs,'integrated private-saving necessarycondition')
        # Weighted phase-excess is only asserted with the whole-cover premise.
        excess_checks=0;excess_failures=0
        for z in {x%N for x in bits(U)}:
            active=[d for d in info if d['shadow']>>z&1]
            require(not any(not d['A'] for d in active),'private top-touching source hasnoactivewholebox')
            phases=defaultdict(set)
            for d in active:phases[d['A']].add(d['theta'])
            excess=sum(Q(max(0,len(v)-1),prod(A)) for A,v in phases.items())
            excess_checks+=1
            if excess<Q(1,R):excess_failures+=1
        if whole and odd:require(excess_failures==0,'weighted phase-excess lowerbound')
        if len(selected_summaries)<4 or not whole or not odd:
            selected_summaries.append(dict(selected_original_labels=list(selected),private_mass=str(Q(U.bit_count(),L)),
                collision_uncovered_private_points=missing.bit_count(),private_saving_rhs=str(rhs),
                rhs_over_private_mass=str(rhs/Q(U.bit_count(),L)),strict_rejection=odd and rhs<Q(U.bit_count(),L),
                numerical_inequality_holds=Q(U.bit_count(),L)<=rhs,odd_top_shadow_scope=odd,
                whole_cover_inequality_applicable=whole,phase_excess_sources=excess_checks,
                phase_excess_failures=excess_failures))
    shells={}
    for d in info:
        for p in d['A']:
            s=d['s'];m=d['m'];a=d['a'];mask=sum(1<<x for x in range(a%(m//p),L,m//p))&~classmasks[s]
            require(Q(mask.bit_count(),L)==Q(p-1,m),'weight-one top shellcapacity')
            shells[s,p]=mask
    visible=defaultdict(list);pair_shell_checks=0
    for s,t,c,pre in pairs:
        A=info[s]['A'];theta_s=dict(zip(A,info[s]['theta']));theta_t=dict(zip(A,info[t]['theta']))
        differing=[p for p in A if theta_s[p]!=theta_t[p]]
        if len(differing)!=1:continue
        p=differing[0];inter=shells[s,p]&shells[t,p];expected=Q(p-2,info[s]['P'])*c
        require(Q(inter.bit_count(),L)==expected,'exact(p-2)/P_A common-source shellintersection')
        visible[p].append((s,t,expected));pair_shell_checks+=1
    supplier_checks=0;missing_neighbors=defaultdict(int);first_missing={};top0_neighbors={}
    idempotent={p:(L//(p**fac[p]))*pow(L//(p**fac[p]),-1,p**fac[p]) for p in primes}
    for t,pmask in enumerate(private):
        for x in bits(pmask):
            for p in info[t]['A']:
                yp=(x%(p**fac[p]))//(p**(fac[p]-1));suppliers=[];alts=[]
                for a in range(p):
                    if a==yp:continue
                    xx=(x+idempotent[p]*(a-yp)*p**(fac[p]-1))%L
                    require(xx%N==x%N and not(classmasks[t]>>xx&1),'topchange keepslowerandescapes privatetarget')
                    oo=owners[xx];alts.append(dict(phase=a,residue=xx,covering_original_labels=oo))
                    if not oo:
                        missing_neighbors[t,p]+=1;first_missing.setdefault((t,p),(x,a,xx));continue
                    s=oo[0];suppliers.append(s);ds=info[s]
                    require(p in ds['A'] and ds['theta'][ds['A'].index(p)]==a,'actual changedphase supplierreaches globaltop')
                    require(shells[s,p]>>x&1,'originalprivatepoint inactual supplier topshell')
                    require(all((x%(q**fac[q]))//(q**(fac[q]-1))==th for q,th in zip(ds['A'],ds['theta']) if q!=p),'supplierotherphases agreeatsamepoint')
                    supplier_checks+=1
                require(len(suppliers)==len(set(suppliers)),'differentchangedphases require differentlabels')
                if whole:require(len(suppliers)==p-1,'wholecover suppliesp-1 actual labels')
                if len(suppliers)==p-1:
                    sig=len({d['A'] for d in info if p in d['A']});bins=defaultdict(int)
                    for s in suppliers:bins[info[s]['A']]+=1
                    count=sum(v*(v-1)//2 for v in bins.values())
                    require(count>=pi_pairs(p-1,sig),'balanced-bin lowerbound onactual supplierpairs')
                if x==0:top0_neighbors[str(p)]=alts
    inequalities=[]
    for p in primes:
        target=[s for s in top_labels if p in info[s]['A']]
        sig=len({info[s]['A'] for s in target});coef=pi_pairs(p-1,sig)
        rhs=sum((v for s,t,v in visible[p]),Q(0))
        for selected in dict.fromkeys((tuple(target),*((s,) for s in target))):
            u=sum((Q(private[s].bit_count(),L) for s in selected),Q(0));lhs=coef*u
            if whole:require(lhs<=rhs,'same-source positive-row shell-pair inequality')
            if len(selected)==len(target) or not whole or not odd:
                inequalities.append(dict(prime=p,selected_original_labels=list(selected),sigma=sig,
                    pair_coefficient=coef,private_mass=str(u),lhs=str(lhs),rhs=str(rhs),holds=lhs<=rhs,
                    rhs_over_private_mass=str(rhs/u),strict_rejection=lhs>rhs,
                    whole_cover_premise=whole))
    result=dict(name=inp['name'],period=L,lower_modulus=N,top_box_size=R,whole_cover=whole,
        numerically_distinct=distinct,all_moduli_odd=odd,classes=[dict(label=s,modulus=m,residue=a,private_witness=inp['witnesses'][s],
              private_count=private[s].bit_count(),top_support=info[s]['A'],top_phase=info[s]['theta'],lower_index=info[s]['bar']) for s,(m,a) in enumerate(classes)],
        uncovered_count=uncovered.bit_count(),first_uncovered=next(bits(uncovered),None),
        source_slice_checks=slice_checks,original_pair_crt_checks=crt_checks,private_saving_checks=saving_checks,
        top_shell_pair_checks=pair_shell_checks,actual_supplier_checks=supplier_checks,
        uncovered_top_neighbors=sum(missing_neighbors.values()),selected_family_checks=selected_summaries,
        shell_pair_inequalities=inequalities,top_neighbors_of_private_zero=top0_neighbors)
    if not odd:
        require(L==60 and whole and distinct,'literal originalevenwholecover')
        result.update(original_names=inp['original_names'],
            odd_hypothesis_boundary='Whole coverage and numerical distinctness hold; oddness is false. TS1/TS4/TS5 are not asserted as general necessary conditions here. Displayed numerical conclusions are measured individually. TS7/TS8 and actual supplier checks remain applicable.')
    if not whole:
        require(L==11025 and N==105 and uncovered.bit_count()==2415 and bool(uncovered>>4&1),'countercoverage exactboundary')
        mods={m for m,a in classes};expected={d for d in range(2,1576) if 1575%d==0}|{49}
        require(mods==expected,'exact claimeddivisor-closed inventory')
        require(all(d in mods for m in mods for d in range(2,m+1) if m%d==0),'every nonunit divisor represented')
        active0=[d for d in info if d['shadow']&1]
        require([d['m'] for d in active0]==[49,225,1575],'exactlower-sourcezero active labels')
        require(owners[0]==[9],'zero private tooriginal49label')
        activepairs=[(s,t) for s,t,c,pre in pairs if pre&1]
        require(activepairs==[(14,17)],'unique activeparallelcollision atzero')
        endpoint=[]
        for s in(14,17):
            m,a=classes[s];defect=m//gcd(m,a);memberships=[]
            for p,e in factor(m).items():
                d=m//(p**e)
                for r in range(e):
                    if a%(d*p**r)==0 and a%(d*p**(r+1))!=0:memberships.append((p,r))
            require(defect==15 and not memberships,'mixeddefect endpoint hasnoone-primeshell atzero')
            endpoint.append(dict(label=s,modulus=m,residue=a,defect=defect,shell_memberships=memberships))
        require([z['residue'] for z in top0_neighbors['7']]==[1575,3150,4725,6300,7875,9450] and
                all(not z['covering_original_labels'] for z in top0_neighbors['7']),'all sixchangedtop7neighbors uncovered')
        result.update(uncovered_residues=list(bits(uncovered)),divisor_closed_above_one=True,
                      active_zero_original_labels=[d['s'] for d in active0],
                      unique_active_parallel_pair=[14,17],mixed_defect_endpoints=endpoint,
                      pair_225_1575_lower_capacity=str(Q(1,105)),
                      upper_bound_scope='Thewholecover collision/supplier conclusions are NOT asserted for thisnoncover. Pair CRT, privacy saving and exact shell-intersection identities remain valid.')
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();results=[]
    for inp in inputs():
        res=analyze(inp);results.append(res)
        print(json.dumps({k:res[k] for k in('name','period','whole_cover','numerically_distinct','uncovered_count','original_pair_crt_checks','top_shell_pair_checks','actual_supplier_checks')}))
    out=dict(scope='Oneuniformoriginalsourcepercontrol. Distinctodd18-label noncover verifies exactmixedcollision/nonvisibility boundary; literalevenL60wholecover verifies odd-hypothesisboundary; repeated-modulus wholecover controls verify conditional same-source identities withoutclaiming distinctoddcover. Ordinary exact arithmetic, notLean verification.',controls=results)
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')


if __name__=='__main__':main()
