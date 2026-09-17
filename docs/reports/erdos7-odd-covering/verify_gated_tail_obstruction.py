#!/usr/bin/env python3
"""Refute a uniform CHT7 tail-price premise using literal distinct odd moduli.

Standard-library rational arithmetic. Reconstructs the actual AP13 unit source,
physical17/killed17 rows, the full191-class family, both complete inherited tests,
and the prices from the same original labels. This is not Lean verification.
"""
from fractions import Fraction as F
from math import gcd
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json

def require(ok, message):
    if not ok:
        raise ArithmeticError(message)

def crt(a,m,b,n):
    require(gcd(m,n)==1, "noncoprime CRT input")
    c=(a+m*((b-a)*pow(m,-1,n)%n))%(m*n)
    require(c%m==a%m and c%n==b%n, "CRT reconstruction")
    return c

def charge(p, count):
    return max(F(count,p-1)-F(7,p-2),0)/(1-F(7,p-2))

def gate(p, headcount, tailcount):
    b=charge(p,headcount)
    return min(1-b,charge(p,headcount+tailcount)-b)

def exact(v):
    return str(v)

def compute():
    head=[d for d in range(1,316) if 315%d==0]
    oldQ=315*11*13
    olddiv=sorted(d*11**a*13**b for d in head for a in (0,1) for b in (0,1))
    unithead=[x for x in range(315) if gcd(x,315)==1]
    period=oldQ*17*19
    headroots={d:i for i,d in enumerate(head[1:],1)}
    family=[(d,0) for d in olddiv if d>1]
    family += [(17,0),(19,0)]
    masks17=[]
    for d in olddiv:
        if d==1: continue
        current=headroots[d] if 315%d==0 else 12
        residue=crt(1,d,current,17)
        family.append((d*17,residue))
        masks17.append((d,residue,current,315%d!=0))
    masks19=[]
    for has17 in (0,1):
        for d in olddiv:
            if d==1 and not has17: continue
            tail=has17 or 315%d!=0
            cofactor=d*17**has17
            oldres=crt(1,d,16,17) if has17 else 1%d
            current=12 if tail else headroots[d]
            residue=crt(oldres,cofactor,current,19)
            family.append((cofactor*19,residue))
            masks19.append((cofactor,residue,current,bool(tail)))
    family.sort()
    complete=sorted(d*17**e*19**f for d in olddiv for e in (0,1) for f in (0,1))
    require(len(family)==191 and len(set(m for m,a in family))==191, "distinct original moduli")
    require(all(m>1 and m%2 and period%m==0 and 0<=a<m for m,a in family),
            "literal odd congruence validity")
    require(len(complete)==192 and len(set(complete))==192, "full original test inventory")
    require([m for m,a in family]==complete[1:], "every nonunit divisor retained once")
    require(sum(z[3] for z in masks17)==36 and sum(z[3] for z in masks19)==84,
            "full cofactor-tail label counts")

    # Enumerate all actual source points. Group only mask/test-indistinguishable
    # values: literal head x, and categories1/2/other in11 and13.
    groups=Counter()
    for x in unithead:
        for y in range(1,11):
            for z in range(1,13):
                old=crt(crt(x,315,y,11),315*11,z,13)
                require(gcd(old,oldQ)==1, "source is an old unit")
                require(all(old%d!=0 for d in olddiv if d>1), "old exclusions avoided")
                cy=y if y in (1,2) else 3
                cz=z if z in (1,2) else 3
                rep=crt(crt(x,315,cy,11),315*11,cz,13)
                for d in olddiv:
                    require((old%d==1%d)==(rep%d==1%d), "group changed mask incidence")
                    require((old%d==2%d)==(rep%d==2%d), "group changed complete centered test")
                groups[x,cy,cz]+=1
    require(sum(groups.values())==17280 and len(groups)==1296, "actual source grouping")

    fields=["mass","T17","T19","P17","P19","survival","head_baseline"]
    totals={name:{field:F(0) for field in fields} for name in ("whole","center1","center2")}
    event_heads={name:{x:F(0) for x in range(315)} for name in totals}
    charge17=charge19=F(0)
    countdist=Counter()
    support_le_center2=True
    for (x,y,z),count in sorted(groups.items()):
        nu=F(count,17280)
        old=crt(crt(x,315,y,11),315*11,z,13)
        C=sum(x%d==1%d for d in head)
        A1=sum(old%d==1%d for d in olddiv)
        A2=sum(old%d==2%d for d in olddiv)
        require(A1==C*(1+(y==1))*(1+(z==1)), "complete inherited load")
        countdist[A1]+=count
        active17=[m for m in masks17 if old%m[0]==m[1]%m[0]]
        bad17={m[2] for m in active17}
        h17={m[2] for m in active17 if not m[3]}
        tail17=sum(m[3] for m in active17)
        require(len(h17)==C-1 and tail17==A1-C and 16 not in bad17,
                "literal17 head/tail and globally clean root")
        bh17=charge(17,len(h17));bh19=charge(19,C-1)
        be17=charge(17,len(bad17))
        r17=be17-bh17;s17=gate(17,len(h17),tail17)
        require(0<=r17<=s17, "actual17 residual bound")
        gain=1/(1-min(F(len(bad17),16),F(7,15)))
        physical={t:(be17/len(bad17) if t in bad17 else gain/16) for t in range(1,17)}
        require(sum(physical.values())==1, "actual physical17 normalization")
        require(sum(v for t,v in physical.items() if t not in bad17)==1-be17,
                "actual killed17 mass")
        oneT=(1-bh19)*s17;oneP=(1-bh19)*r17
        twoT=twoP=survival=be19physical=F(0)
        for t,weight in physical.items():
            old17=crt(old,oldQ,t,17)
            active19=[m for m in masks19 if old17%m[0]==m[1]%m[0]]
            bad19={m[2] for m in active19}
            h19={m[2] for m in active19 if not m[3]}
            tail19=sum(m[3] for m in active19)
            require(len(h19)==C-1 and tail19==A1-C+A1*(t==16),
                    "literal19 full cofactor-tail count")
            be19=charge(19,len(bad19));r19=be19-bh19;s19=gate(19,len(h19),tail19)
            require(0<=r19<=s19, "actual19 residual bound")
            be19physical+=weight*be19
            if t not in bad17:
                twoT+=weight*s19;twoP+=weight*r19;survival+=weight*(1-be19)
        baseline=(1-bh17)*(1-bh19)
        require(survival==baseline-oneP-twoP, "same-law CHT4 identity")
        if oneT+twoT:
            support_le_center2 &= A2<=10
        for name,inside in [("whole",True),("center1",A1<=10),("center2",A2<=10)]:
            if inside:
                row=dict(mass=1,T17=oneT,T19=twoT,P17=oneP,P19=twoP,
                         survival=survival,head_baseline=baseline)
                for key,val in row.items():totals[name][key]+=nu*val
                event_heads[name][x]+=nu
        charge17+=nu*be17;charge19+=nu*be19physical
    require(support_le_center2, "priced support not contained in center2 low-load event")
    threshold=F(704627631753217,45514648675654535)
    for values in totals.values():
        values["T"]=values["T17"]+values["T19"]
        values["P"]=values["P17"]+values["P19"]
        require(values["survival"]==values["head_baseline"]-values["P"], "integrated same-event identity")
    for name,values in totals.items():
        w1,w2=sorted(event_heads[name].values(),reverse=True)[:2]
        headprice=max(F(7,10)*w1,F(1,2)*w1+F(2,5)*w2)
        intercept=values["mass"]-headprice
        surplus=intercept-values["T"]
        require(values["survival"]>=surplus,"CHT6 exact-head bound")
        values.update(w1=w1,w2=w2,CHT6_head_price=headprice,CHT6_intercept=intercept,
                      CHT6_surplus=surplus,CT121_loss_lower=21*surplus)
    require(totals["whole"]["T"]==F(889799,43545600)>threshold,
            "whole-space universal premise not refuted")
    require(totals["center1"]["T"]==F(300761,70761600)<threshold,
            "center1 event certificate")
    require(totals["center2"]["T"]==totals["whole"]["T"]>threshold,
            "uniform event-price premise not refuted")
    require(totals["center1"]["mass"]==totals["center2"]["mass"]==F(4229,4320),
            "same event-mass comparison")
    require(sorted(event_heads["center1"].values())==sorted(event_heads["center2"].values()),
            "same sorted complete head-profile comparison")
    require(totals["center1"]["CHT6_intercept"]==totals["center2"]["CHT6_intercept"]==F(2101,2160),
            "same exact intercept")
    require(charge17>0 and charge19>0, "both actual stages charged")
    # A genuinely uniform statement over all independent inherited test labels.
    def phi(d):
        return sum(gcd(x,d)==1 for x in range(d))
    meanbound=sum((F(1,phi(d)) for d in olddiv),F(0))
    require(meanbound==F(5005,1728),"all-original-label mean bound")
    event_lower=(11-meanbound)/10
    head_upper=F(1,160)
    uniform_surplus=event_lower-head_upper-totals["whole"]["T"]
    require(uniform_surplus>0,"all-original-test CHT6 surplus")
    return {
        "schema":"gated-tail-obstruction-v1", "period":period,"old_period":oldQ,
        "source_unit_count":17280,"source_incidence_groups":1296,
        "forbidden_original_moduli":191,"complete_final_test_labels":192,
        "complete_inherited_test_labels":48,"tail_labels17":36,"tail_labels19":84,
        "family_sha256":hashlib.sha256(json.dumps(family,separators=(",",":")).encode()).hexdigest(),
        "mstar":exact(threshold),"charge17":exact(charge17),"charge19_physical":exact(charge19),
        "source_center1_load_counts":{str(a):n for a,n in sorted(countdist.items())},
        "events":{name:{key:exact(value) for key,value in row.items()} for name,row in totals.items()},
        "center2_contains_all_priced_support":support_le_center2,
        "same_sorted_head_profiles":True,
        "all_original_test_CHT6":{
            "actual_source_mean_upper":exact(meanbound),"event_mass_lower":exact(event_lower),
            "head_price_upper":exact(head_upper),"survival_lower":exact(uniform_surplus),
            "CT121_loss_lower":exact(21*uniform_surplus)},
        "scope":"ordinary exact arithmetic; refutes uniform CHT7 tail-price premises, not Erdős7",
    }

if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate",type=Path,
                        default=Path(__file__).with_name("gated_tail_obstruction_certificate.json"))
    parser.add_argument("--write",action="store_true")
    args=parser.parse_args()
    result=compute()
    if args.write:
        args.certificate.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    else:
        def unique(pairs):
            out={}
            for k,v in pairs:
                require(k not in out,"duplicate certificate key")
                out[k]=v
            return out
        require(json.loads(args.certificate.read_text(),object_pairs_hook=unique)==result,
                "certificate differs from exact reconstruction")
    print("PASS literal191-class same-law counterexample to uniform whole/event tail threshold")
