"""Verify an actual-carrier, fibre-uniform saturated-envelope obstruction.

Python standard library only. The original family, five actual test-layout
cuts, geometric coefficients and rational dual inequality are reconstructed
from semantic inputs. No LP solver, NumPy, float, or enumeration cache is used.
The lower bound concerns an upper-bound formula, not actual test moments.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from itertools import product
from math import lcm
from pathlib import Path
import argparse
import json


def require(ok,message):
    if not ok:
        raise ArithmeticError(message)


def verify(path):
    data=json.loads(read_artifact_text(Path(path)))
    old=data['old_classes']
    points=[x for x in range(45) if all(x%d!=a for d,a in old)]
    require(points==data['points'] and len(points)==16,'actual old45 survivor set')
    family=old+[data['pure_seven_class']]+data['mixed_seven_classes']
    ds=[3**a*5**b*7**c for a,b,c in product(range(3),range(2),range(2))]
    require(sorted(d for d,a in family)==sorted(ds[1:]),'all distinct nonunit315 divisor labels')
    require(all(d>1 and d%2==1 and 0<=a<d for d,a in family),'original odd covering problem domain')
    require(data['pure_seven_class']==[7,0],'normalized pure seven class')
    survivor=[z for z in range(315) if all(z%d!=a for d,a in family)]
    fibres=[[z%7 for z in survivor if z%45==x] for x in points]
    r=[len(fibre) for fibre in fibres]
    b=[6-v for v in r]
    require(b==data['deletion_vector'],'exact original-class deletion vector')
    require(len(survivor)==sum(r)==data['N']==77,'actual77-point carrier')
    require(all(6 in fibre for fibre in fibres),'one globally unused seven digit')

    exps=list(product(range(3),range(2),range(2)))
    gamma=[]
    eta=[F(0) for d in ds]
    for a in exps:
        z=F(1)
        for prime,height,e in zip((3,5,7),(2,1,1),a):
            if e==height:
                z*=F(prime,prime-1)
        gamma.append(z-1)
    for a,d in zip(exps,ds):
        for b0,e in zip(exps,ds):
            z=F(1)
            for prime,height,j,k in zip((3,5,7),(2,1,1),a,b0):
                if j==height and k==height:
                    z*=F(prime*(prime+1),(prime-1)**2)
                elif j==height or k==height:
                    z*=F(prime,prime-1)
            eta[ds.index(lcm(d,e))]+=z-1
    require(ds==data['divisors'],'twelve divisor labels')
    uniform_caps=[]
    for d in ds:
        co=d//7 if d%7==0 else d
        counts=[sum(1 if d%7==0 else rr for x,rr in zip(points,r) if x%co==a)
                for a in range(co)]
        uniform_caps.append(F(max(counts),77))
    uniform_R=sum(a*b0 for a,b0 in zip(gamma,uniform_caps))
    require(uniform_R==F(1825,3696)<1,'nonempty R<1 domain witnessed by uniform law')

    # x=(v_0,...,v_15,t,zG,z_1,z_7,...,z_315).
    # E*x=(0,1,0), A*x<=0, x>=0; minimize 1+c*x.
    n=len(points)
    nv=n+14
    E=[[F(v) for v in r]+[F(-1),F(0)]+[F(0)]*12,
       [F(0)]*n+[F(1),F(0)]+[-v for v in gamma],
       [F(0)]*n+[F(-1),F(0),F(1)]+[F(0)]*11]
    rhs=[F(0),F(1),F(0)]
    c=[F(0)]*n+[F(-1),F(1)]+eta
    combined=[F(0)]*nv
    square_count=0
    for cut in data['constraints']:
        y=F(cut['multiplier'])
        require(y<=0,'dual inequality multiplier sign')
        row=[F(0)]*nv
        kind=cut['kind']
        if kind=='cylinder':
            d=cut['d']
            require(d in ds,'cylinder divisor')
            co=d//7 if d%7==0 else d
            a=cut['residue']
            require(isinstance(a,int) and 0<=a<co,'cylinder residue')
            row[:n]=[F(int(x%co==a)*(1 if d%7==0 else rr)) for x,rr in zip(points,r)]
            row[n+2+ds.index(d)]=F(-1)
        elif kind=='square':
            mods=data['old_test_moduli']
            require(mods==[3,5,9,15,45],'complete old test labels')
            ar,br=cut['A_residues'],cut['B_residues']
            require(len(ar)==len(br)==5,'complete square layout assignments')
            require(all(isinstance(a,int) and 0<=a<d for aa in (ar,br) for d,a in zip(mods,aa)),
                    'actual square layout residues')
            A=[1+sum(x%d==a for d,a in zip(mods,ar)) for x in points]
            B=[1+sum(x%d==a for d,a in zip(mods,br)) for x in points]
            row[:n]=[F(rr*a*a+2*a*b0+b0*b0) for rr,a,b0 in zip(r,A,B)]
            row[n+1]=F(-1)
            square_count+=1
        elif kind=='unit_square':
            row[n],row[n+1]=F(1),F(-1)
        else:
            raise ArithmeticError('unknown dual constraint kind')
        combined=[a+y*b0 for a,b0 in zip(combined,row)]
    z=list(map(F,data['equality_multipliers']))
    require(len(z)==3,'three equality multipliers')
    combined=[a+sum(zz*row[j] for zz,row in zip(z,E)) for j,a in enumerate(combined)]
    require(all(a<=b0 for a,b0 in zip(combined,c)),'every dual objective coordinate')
    lower=1+sum(a*b0 for a,b0 in zip(z,rhs))
    require(lower==F(data['envelope_lower_bound']),'exact dual lower bound')
    baseline=F(data['comparison_bound'])
    require(baseline==F(3849,106),'fixed comparison bound')
    require(lower-baseline==F(data['strict_excess'])>0,'strict obstruction above comparison')
    return {'status':'verified exact dual lower bound for the stated fibre-uniform envelope',
            'carrier_size':len(survivor),'constraints':len(data['constraints']),
            'actual_square_layout_pairs':square_count,'envelope_lower_bound':str(lower),
            'uniform_domain_witness_R':str(uniform_R),
            'comparison_bound':str(baseline),'strict_excess':str(lower-baseline),
            'scope':'This is not a lower bound for actual Gamma, or for arbitrary77-point laws.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate',nargs='?',default=str((Path(__file__).resolve().parent / 'certificates/fiber_uniform_saturated_envelope_obstruction_certificate.json')))
    args=parser.parse_args()
    print(json.dumps(verify(args.certificate),indent=2))


if __name__=='__main__':
    main()
