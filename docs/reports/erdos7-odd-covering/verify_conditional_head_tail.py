#!/usr/bin/env python3
"""Check the actual conditional head/tail deletion certificate.

Reconstructs original congruences and the same physical/killed probability.
The arbitrary-cofactor theorem is in marked_head_profile.md. Standard-library
exact arithmetic; no Lean verification or unrestricted covering conclusion.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from math import gcd, prod
import json

def require(c,msg):
    if not c: raise ArithmeticError(msg)

def rec(x): return {'exact':str(x),'decimal':float(x)}

def crt(a,m,b,n):
    require(gcd(m,n)==1,'coprime literal coordinates')
    c=(a+m*((b-a)*pow(m,-1,n)%n))%(m*n)
    require(c%m==a%m and c%n==b%n,'literal original CRT residue')
    return c

def beta(p,bad):
    alpha=F(len(bad),p-1); delta=F(7,p-2)
    return max(alpha-delta,0)/(1-delta)

def row(p,bad):
    b=beta(p,bad); g=1/(1-min(F(len(bad),p-1),F(7,p-2)))
    out={y:(b/len(bad) if y in bad else g/(p-1)) for y in range(1,p)}
    require(sum(out.values())==1,'physical normalization')
    return out
head=[d for d in range(1,316) if 315%d==0]
xs=[x for x in range(315) if gcd(x,315)==1]
# Exact AP13 law from all d|315*11*13, d>1 forbidding0: uniform units.
# Group only coordinates indistinguishable by masks and the ONE inherited test.
cats11=[(1,1),(2,1),(3,8)]
cats13=[(1,1),(2,1),(3,10)]
source=[(x,y,z,F(ny*nz,len(xs)*10*12)) for x in xs for y,ny in cats11 for z,nz in cats13]
require(sum(v for x,y,z,v in source)==1,'actual source mass')
# Old coordinate residues are1 throughout forbidden current masks.
# Future full test is centered at2 on every original divisor.
head17=[(d,i+1) for i,d in enumerate(head[1:])]
head19=[(d,i+1) for i,d in enumerate(head[1:])]
tail17_11=[(d,13+i%4) for i,d in enumerate(head)]
tail17_13=[(d,12) for d in head]
tail19_17=[(d,12+i%7) for i,d in enumerate(head)]
oldQ=315*11*13
actual_classes=[(d,0) for d in range(2,oldQ+1) if oldQ%d==0]
actual_classes += [(17,0)]+[(d*17,crt(1,d,j,17)) for d,j in head17]
actual_classes +=[(d*11*17,crt(1,d*11,j,17)) for d,j in tail17_11]
actual_classes +=[(d*13*17,crt(1,d*13,j,17)) for d,j in tail17_13]
actual_classes +=[(19,0)]+[(d*19,crt(1,d,j,19)) for d,j in head19]
actual_classes +=[(d*17*19,crt(crt(1,d,16,17),d*17,j,19)) for d,j in tail19_17]
actual_moduli=[m for m,a in actual_classes]
require(len(set(actual_moduli))==len(actual_moduli),'original moduli distinct')
require(all(m>1 and m%2 for m in actual_moduli),'odd original moduli')
period=oldQ*17*19
require(all(period%m==0 for m in actual_moduli),'full period')
complete_tests=[d*11**a*13**b*17**e*19**f for d in head for a in [0,1] for b in [0,1] for e in [0,1] for f in [0,1]]
require(len(set(complete_tests))==192 and all(period%d==0 for d in complete_tests),'complete test count')
bh17={x:beta(17,{j for d,j in head17 if x%d==1%d}) for x in range(315)}
bh19={x:beta(19,{j for d,j in head19 if x%d==1%d}) for x in range(315)}
require(sum(bh17.values())<=F(1,2),'HBD17 counting budget')
require(sum(bh19.values())<=F(2,5),'HBD19 counting budget')
rows=[]
for cutoff in [1,2,4,8,10,16,48]:
    w={x:F(0) for x in range(315)}
    baseline=surv=price17=price19=physical19=linear17=linear19=gated17=gated19=F(0)
    zero_slack_points=positive_tail_points=0
    for x,y,z,mass in source:
        A=sum(x%d==2%d for d in head)*(1+(y==2))*(1+(z==2))
        if A>cutoff: continue
        w[x]+=mass
        b17=bh17[x]; b19=bh19[x]
        bad17={j for d,j in head17 if x%d==1%d}
        headalpha17=F(len(bad17),16)
        originaltail17=[j for d,j in tail17_11 if y==1 and x%d==1%d]
        originaltail17 +=[j for d,j in tail17_13 if z==1 and x%d==1%d]
        bad17.update(originaltail17)
        r17=beta(17,bad17)-b17
        lam17=F(16,17); delta17=F(7,15)
        ell17=F(len(originaltail17),17)/lam17
        clipped17=min(1-b17,(max(headalpha17+ell17-delta17,0)-max(headalpha17-delta17,0))/(1-delta17))
        require(0<=r17<=clipped17<=ell17/(1-delta17),'slack gated17')
        if originaltail17:
            positive_tail_points+=1
            zero_slack_points+=(clipped17==0)
        price17+=mass*(1-b19)*r17
        gated17+=mass*(1-b19)*clipped17
        linear17+=mass*(1-b19)*ell17/(1-delta17)
        baseline+=mass*(1-b17)*(1-b19)
        k17=row(17,bad17)
        for t,kmass in k17.items():
            bad19={j for d,j in head19 if x%d==1%d}
            headalpha19=F(len(bad19),18)
            originaltail19=[j for d,j in tail19_17 if t==16 and x%d==1%d]
            bad19.update(originaltail19)
            r19=beta(19,bad19)-b19
            ell19=F(len(originaltail19),18)
            delta19=F(7,17)
            clipped19=min(1-b19,(max(headalpha19+ell19-delta19,0)-max(headalpha19-delta19,0))/(1-delta19))
            require(0<=r19<=clipped19<=ell19/(1-delta19),'slack gated19')
            physical19+=mass*kmass*r19
            if t in bad17: continue
            price19+=mass*kmass*r19
            gated19+=mass*kmass*clipped19
            linear19+=mass*kmass*F(len(originaltail19),18)/F(10,17)
            surv+=mass*kmass*(1-beta(19,bad19))
    require(surv==baseline-price17-price19,'exact same-law head/tail identity')
    require(price19<=physical19,'actual killed19 saving')
    require(price17+price19<=gated17+gated19<=linear17+linear19,'full labelled gated union price')
    w1,w2=sorted(w.values(),reverse=True)[:2]
    outer=sum(w.values())-max(F(7,10)*w1,F(1,2)*w1+F(2,5)*w2)-price17-price19
    require(surv>=outer,'two-cell bound with actual tail correction')
    rows.append(dict(cutoff=cutoff,mass=rec(sum(w.values())),actual_survival=rec(surv),head_baseline=rec(baseline),price17=rec(price17),price19_killed=rec(price19),price19_physical=rec(physical19),linear_union_price=rec(linear17+linear19),gated_union_price=rec(gated17+gated19),two_cell_lower=rec(outer),positive_tail_source_cells=positive_tail_points,zero_slack_charge_source_cells=zero_slack_points))
D=F(1039695426000000,18925009844347)
M=F(2621130891614589,246025127976511)
r=F(18925009844347,38266567762500)
m=(11-M)/10;c=1/(74*r)
threshold=min(m-F(7,10)*c,F(3,5)*m-F(1,10)*c)
require(threshold==F(704627631753217,45514648675654535),'exact wide-band threshold')
S=prod(F(p,p-1) for p in [3,5,7,11,13])
crude17=D*(S-F(208,105))/8
crude19=2*D*(S*F(17,16)-F(208,105))/10
require(crude17>1 and crude19>1,'uniform-density tail bound is vacuous')
gated_whole=F(rows[-1]['gated_union_price']['exact'])
require(gated_whole<threshold,'tail certificate passes uniformly for every event')
uniform_gain=21*(threshold-gated_whole)
require(uniform_gain>0,'all-test CT121 gain')
result=dict(actual_forbidden_labels=len(actual_moduli),complete_test_labels=192,period=period,tail_threshold=rec(threshold),all_test_fixture_CT121_gain=rec(uniform_gain),CT121_gain_intercept=rec(21*threshold),crude_unrestricted_tail17=rec(crude17),crude_unrestricted_tail19=rec(crude19),rows=rows)

if __name__ == '__main__':
    import argparse
    from pathlib import Path
    def unique(pairs):
        out = {}
        for key, value in pairs:
            require(key not in out, 'duplicate JSON key: ' + key)
            out[key] = value
        return out
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path,
                        default=(Path(__file__).resolve().parent / 'certificates/conditional_head_tail_certificate.json'))
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    if args.write:
        write_certificate_text(args.certificate, json.dumps(result, indent=2) + '\n')
    else:
        require(json.loads(read_artifact_text(args.certificate), object_pairs_hook=unique) == result,
                'certificate differs from exact recomputation')
    print('PASS actual107-class chain, all original tails, gated price and same-event identity')
