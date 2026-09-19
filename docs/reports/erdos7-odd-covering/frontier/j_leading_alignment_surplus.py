#!/usr/bin/env python3
"""Exact arithmetic and actual finite examples for imperfect J anti-alignment."""
from fractions import Fraction as F
from hashlib import sha256
import argparse
import importlib.util
from itertools import combinations, product
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
CERTIFICATE='certificates/source_norms/j_leading_alignment_surplus.json'
PINS={'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'profile-notes/48-actual-source-compatibility-excludes-a-relaxed-mass-endpoint.md': 'f1919e46166ff701af789dafe498e7fe39bc620939937d0494ccf111f75076b4', 'profile-notes/50-sharp-source-survival-endpoints.md': '5b829ebe7ff4bd8c2f61d0d99add9cb4446be1b974a75e7eea7255aced5f15a0', 'profile-notes/71-global-j-k-control-faces-and-exact-escape-gaps.md': '1ba67485969c424f5523b77dd03a0dc0823f82f9d06f4c3dc719e9cfb66024c1', 'profile-notes/130-the-whole-j-face-forces-source-anti-alignment.md': 'a57717f7d0432a2d0365d85b4fa471729e52630fff2be75aafe6b3c4e4db7db7', 'profile-notes/136-a-whole-j-source-neighborhood-has-a-complete-labelwise-bound.md': '137aacdd1de6890568edc6d0490fe00c7df41e2c1ff35f95c7732d79829e3806', 'profile-notes/301-three-missing-source-pairs-clear-the-complete-core-comparisons.md': 'f53341ba3738291a8bdc063faebae5baae5b7c601f7a28e09ae5b2cf26b6ab61', 'profile-notes/305-ineffective-leading-pairs-retain-the-complete-core-bounds.md': '6d3e60c74ed6467d5e304275278e8a3490e39e7d268ef1f4b85e8eee6bf48b77', 'certificates/source_norms/global_control_faces.json': 'd99736841c20977095c5c397c5949dec20960a4ee1afd72a3f926f2e773b8817'}
CELLS=(0,3,1,4,7)
def require(ok,msg):
    if not ok:raise ValueError(msg)
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'Loadable module')
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value
def enc(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {str(k):enc(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [enc(v) for v in x]
    return x
def overlap(a,b):
    # Product cylinder (ternary depth, residue, five depth, residue).
    return (a[1]-b[1])%3**min(a[0],b[0])==0 and (a[3]-b[3])%5**min(a[2],b[2])==0
def mass(c):return F(1,3**c[0]*5**c[2])
def intersection(x,y):
    return F(1,3**max(x[0],y[0])*5**max(x[2],y[2])) if overlap(x,y) else F(0)
def source_label(a,b):
    if b==0:return (a,2 if a==1 else 6 if a==2 else 3**(a-1),0,0)
    if a==0:return (0,0,b,5**(b-1))
    if a==1:return (1,1,b,2*5**(b-1))
    if a==2:return (2,1 if b==1 else 4,b,3*5**(b-1))
    if (a,b)==(3,1):return (3,10,1,4)
    return (a,7+3**(a-1),b,3*5**(b-1))
def mixed_label(a,b):
    if (a,b)==(1,0):return (1,0,0,0),1
    if (a,b)==(2,0):return (2,3,0,0),2
    if b==0:return (a,2*3**(a-1),0,0),2
    if a==0:return (0,0,b,4*5**(b-1)),3
    if a==1:return (1,1,b,4*5**(b-1)),1
    if a==2:return (2,3,b,4*5**(b-1)),5
    return (a,7+2*3**(a-1),b,4*5**(b-1)),5
def crt(a,ra,b,rb,e,re):
    mods=(3**a,5**b,7**e);res=(ra,rb,re);m=mods[0]*mods[1]*mods[2]
    return m,sum(r*(m//p)*pow(m//p,-1,p) for r,p in zip(res,mods) if p>1)%m
def example(N):
    labels={(a,b):source_label(a,b) for a,b in product(range(N+1),repeat=2) if a+b}
    pure3=[c for (a,b),c in labels.items() if not b]
    pure5=[c for (a,b),c in labels.items() if not a]
    alpha=[c for (a,b),c in labels.items() if a==1 and b]
    beta=[c for (a,b),c in labels.items() if a==2 and b]
    late=[c for (a,b),c in labels.items() if a>=3 and b]
    for group in (pure3,pure5,alpha,beta,late):
        require(all(not overlap(x,y) for x,y in combinations(group,2)),'Each source stage has disjoint original cylinders')
    require(all(not overlap(x,y) for x in alpha for y in pure3+pure5),'Full additional alpha')
    require(all(not overlap(x,y) for x in beta for y in pure3+pure5+alpha),'Full additional beta')
    require(all(not overlap(x,y) for x in late for y in pure3+pure5+alpha+beta),'Every late label spends its full raw cap')
    t=sum((F(1,3**a) for a in range(3,N+1)),F(0))
    q=sum((F(1,5**b) for b in range(1,N+1)),F(0))
    require(t==(1-F(1,3**(N-2)))/18 and q==(1-F(1,5**N))/4,'All finite geometric terms and omitted tails')
    eta=[F(1,9)-t]+[F(1,9)]*4
    betavec=[F(0),F(0),F(1,5),q-F(1,5),F(0)]
    latevec=[sum((mass(c) for c in late if c[1]%9==cell),F(0)) for cell in CELLS]
    require(latevec==[F(0),F(0),F(1,135),F(0),t*q-F(1,135)],'Two genuine nonzero late cells')
    avail=[1-q,1-q]+[1-2*q-betavec[i] for i in range(2,5)]
    n=[eta[i]*avail[i]-latevec[i] for i in range(5)]
    s=sum(n);require(s==F(5,9)-t-q and min(n)>0,'Actual raw source mass from disjoint stages')
    def source_mass(c):
        c3=(c[0],c[1],0,0);c5=(0,0,c[2],c[3])
        v3=mass(c3)-sum((intersection(c3,z) for z in pure3),F(0))
        v5=mass(c5)-sum((intersection(c5,z) for z in pure5),F(0))
        value=v3*v5-sum((intersection(c,z) for z in alpha+beta+late),F(0))
        require(value>=0,'Actual cylinder mass after the disjoint source stages')
        return value
    require([source_mass((2,c,0,0)) for c in CELLS]==n,'Independent actual rectangle integration recovers all five source cells')
    oldmass=n[0]+2*n[1]
    u7=(5+F(1,7**N))/6;kappa=(1-F(1,7**N))/(5+F(1,7**N))
    seventerms=[(e,j*7**(e-1)) for e in range(1,N+1) for j in (1,2,3,5,6)]
    require(all((r-sr)%7**min(e,se)!=0 for (e,r),(se,sr) in combinations(seventerms,2)),'Every mixed-seven class and pure7 has disjoint seven cylinders')
    original=[]
    groups={j:[] for j in (1,2,3,5)}
    category_masses=[F(0)]*5
    for (a,b),c in labels.items():
        original.append(crt(*c,0,0))
        old,j=mixed_label(a,b)
        require(all(not overlap(old,other) for other in groups[j]),'Within each seven class all original old-coordinate carriers are disjoint')
        groups[j].append(old)
        category=0 if b==0 else 1 if a==0 else 2 if a==1 else 3 if a==2 else 4
        category_masses[category]+=source_mass(old)
        for e in range(1,N+1):original.append(crt(*old,e,j*7**(e-1)))
    original.extend(crt(0,0,0,0,e,6*7**(e-1)) for e in range(1,N+1))
    require(len(original)==len({m for m,r in original})==(N+1)**3-1,'Exactly one residue per original modulus')
    require(category_masses==[(1-q)/3,(F(5,9)-t)*q-F(1,135),q/3-F(1,135),q/9,t*q],
            'All five complete finite cofactor-category mass formulas')
    H=sum(category_masses)
    require(H==F(1,3)+2*q/3-F(2,135),'Sharp mixed7 completion retains every other cofactor cap')
    S=s-kappa*H
    crt_survivors=None
    if N==3:
        period=105**N;removed=bytearray(period)
        for mod,residue in original:
            count=(period-1-residue)//mod+1
            removed[residue::mod]=b'\x01'*count
        crt_survivors=period-sum(removed)
        require(F(crt_survivors,period)==u7*S,'Independent complete CRT union agrees with normalized actual survivor')
    h=sum(eta);h1=sum(eta[2:]);rawrest=(max(avail)/18+(h+max(sum(eta[:2]),h1)+max(eta))/4+F(1,72))/5
    D=s-rawrest-(max(sum(n[:2]),sum(n[2:]))+max(n))/5
    piA=1-F(1,7**N)
    S0=s-rawrest-piA*oldmass/5
    rho=S-S0
    qJ=(18*t)*(4*q)**3*(72*t*q)*piA
    require(qJ==(1-F(1,3**(N-2)))**2*(1-F(1,5**N))**4*piA,'Actual product weight of whole J zero faces')
    delta=1-qJ;lam=F(1,72)-sum(latevec[2:])
    require(rho>=0 and S0>=D and delta>=0,'Actual shared mass and concentration parameters')
    actual135=labels[3,1];actual45=labels[2,1]
    require(actual135[1]%9==actual45[1]%9==1,'Leading135 and45 occupy the same surviving cell')
    require(all(not overlap(actual135,c) for c in pure3+pure5+alpha+beta),'Actual leading135 remains effective')
    old50=[];old48=[]
    for i in range(2,5):
        source_delta=(1-q-F(3,4))+(F(1,4)-q)+(F(1,4)-betavec[i])
        epsilon=F(1,72)-latevec[i]
        old50.append(max(F(0),2*h1/125-2*source_delta/3-12*epsilon))
        old48.append(max(F(0),2*latevec[i]-F(7,300)-source_delta/9))
    require(old48==old50==[F(0)]*3,'All earlier same-cell scalar corrections vanish on the dispersed witness')
    if N>=10:
        require(delta<=F(1,1000),'Witness belongs to preregistered concentration domain')
        require(lam<=delta/72 and S0-D<=17*delta/90,'Independent witness checks of source and carrier slacks')
        bound=F(2,675)-7*delta/36
        require(bound>0 and rho>=bound and S-D>=F(2,5)*(F(1,135)-lam),'The imperfect-source alignment bound holds with positive content')
    else:bound=None
    return {'height':N,'original_label_count':len(original),'source_beta':betavec,'source_late':latevec,
        'raw_source_mass':s,'actual_survivor_mass':S,'D':D,'S0':S0,'rho':rho,'qJ':qJ,'delta':delta,'lambda':lam,
        'mixed7_old_carrier_category_masses':category_masses,'mixed7_old_carrier_total':H,
        'rho_lower_from_leading_alignment':bound,'old48_corrections':old48,'old50_corrections':old50,
        'leading_residues':{str(m):r for m,r in original if m in (3,5,9,15,27,45,135)},
        'original_family_sha256':sha256(json.dumps(original,separators=(',',':')).encode()).hexdigest(),
        'independent_full_CRT_period':105**N if N==3 else None,'independent_full_CRT_survivors':crt_survivors}


def calculate(base):
    io=load('j_leading_alignment_calculate_io',base/'certificate_io.py')
    read=lambda path:io.read_artifact_bytes(path)
    get=lambda path:json.loads(read(path),object_pairs_hook=io._unique)
    for path,pin in PINS.items():
        require(sha256(read(base/path)).hexdigest()==pin,'Pinned complete source input '+path)
    dmax=F(1,1000)
    require(dmax/4<F(1,25) and (1-dmax)/4>F(21,100),'P,A,B,Q forcing uses source budgets only')
    require(dmax/72<F(1,675),'135 cannot use Q after its original25 loss')
    other_slot_losses=[F(1,10),F(1,50),(F(1,3)-dmax/18)/5,(F(1,3)-dmax/18)/25,
                      (F(1,9)-dmax/18)/5,(F(1,6)-dmax/9)/5]
    require(min(other_slot_losses)>=F(1,90),'Every competing5 or15 carrier loses at least the complete b=1 raw budget')
    require(F(2,5)*F(1,72)+F(17,90)==F(7,36),'Complete leading alignment delta coefficient')
    require(F(1,18)*F(1,20)==F(1,360) and F(1,18)*F(1,5)==F(1,90),'Full b>=2 and b=1 late tails')
    require(F(2,675)-7*dmax/36==F(299,108000),'Uniform positive lower floor across stated concentration interval')
    examples=[example(N) for N in (3,4,10,12)]
    limitn=[F(1,24),F(1,12),F(7,270),F(1,20),F(53,1080)]
    limitC=max(sum(limitn[:2]),sum(limitn[2:]))+max(limitn)+F(3,4)/18+(F(1,2)+F(1,3)+F(1,9))/4+F(1,72)
    require(sum(limitn)==F(1,4) and limitC==F(1,2) and sum(limitn)-limitC/5==F(3,20),
            'The actual limiting source has D=S0=3/20 for its concentrated carrier')
    limitS=F(1,4)-F(1,5)*(F(1,3)+F(2,3)*F(1,4)-F(2,135))
    require(limitS==F(3,20)+F(2,675),'Actual dispersed-beta completion attains the aligned-sector limit')
    src=get(base/'certificates/source_norms/global_control_faces.json')
    target=F(src['targets']['J']['target']);a_old=F(src['targets']['J']['mass_coefficient'])
    a403=a_old-F(23,42)*(target-403)
    require(a403<0,'A larger actual mass lower bound alone cannot improve the old53 target403 proof')
    out={'schema':'erdos7-imperfect-j-leading-alignment-v1','source_sha256':PINS,'helper_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
        'delta_max':dmax,'uniform_alignment_rho_floor':F(299,108000),'other_slot_loss_minimum':min(other_slot_losses),
        'aligned_sector_limiting_raw_cell_masses':limitn,
        'aligned_sector_limiting_survivor_mass':limitS,'aligned_sector_limiting_rho':F(2,675),
        'old53_J403_signed_mass_coefficient':a403,'examples':examples,
        'scope':'Exact local arithmetic and actual finite original-label constructions. The universal all-height inequality is proved in the companion note. No old scan, LP, price inventory or Lean theorem is produced; no J<403, Gamma19<403 or unrestricted result is asserted.'}
    return enc(out)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[1])
    modes=parser.add_mutually_exclusive_group()
    modes.add_argument('--write',action='store_true')
    modes.add_argument('--check',action='store_true')
    parser.add_argument('--output',type=Path,help='Optional certificate path for scratch generation or verification')
    args=parser.parse_args()
    result=calculate(args.base)
    io=load('j_leading_alignment_writer_io',args.base/'certificate_io.py')
    path=args.output if args.output is not None else args.base/CERTIFICATE
    if args.write:
        path.parent.mkdir(parents=True,exist_ok=True)
        io.write_certificate_text(path,json.dumps(result,indent=2)+'\n')
    else:
        stored=json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique)
        require(stored==result,'Exact complete alignment coefficients, four actual finite families and original signed-mass obstruction')
    print('PASS complete capacity coefficients, all four dispersed-beta original families, and height3 full CRT union')
    print('PASS aligned-sector sharp limiting surplus '+result['aligned_sector_limiting_rho'])
    print('Old53 J403 signed mass coefficient '+result['old53_J403_signed_mass_coefficient'])

if __name__=='__main__':
    try:
        main()
    except (ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError) as error:
        print('FAIL: '+str(error),file=sys.stderr)
        raise SystemExit(1)
