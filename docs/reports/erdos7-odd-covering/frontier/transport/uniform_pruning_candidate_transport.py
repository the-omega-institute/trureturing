#!/usr/bin/env python3
"""Explicit complete errors for every two/four/six pruning candidate.

Uses original225/226 scan certificates without rerunning their head scans.
The ordinary proof preserves the complete whole-hinge credit and tails.
This is not a full52-cost or global comparison.
"""
import argparse
from fractions import Fraction as F
from pathlib import Path
from hashlib import sha256
from itertools import product
import importlib.util
import json
import sys

sys.dont_write_bytecode=True
CERTIFICATE='certificates/source_norms/retained-transport/uniform_pruning_candidate_transport.json'
PINS={'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/k_face_common_seven_hinges.py': '8cc4600c9b3f2f65a11820fcb2d0d6663c765c20765bbaf1ae0de6e883cefc97', 'frontier/transport/second_depth_seven_comparison.py': 'e04a9cfb22cdb4c3f3ffda097b7975facc253c21840873ef527e5a601f028bfe', 'frontier/transport/expanded_seven_pair_comparison.py': 'a651711988f8adf20dfc27cba9665f25d0d5863cb310c26e2f4b7fc16bab1c29', 'frontier/transport/retained135125_heavy_comparison.py': '5e7a8bdd7ee1e93afd3115c80a8792d0afbf035ac50be715cf69631b75c70ff5', 'frontier/transport/retained135125_survival_comparison.py': '600cc560ea2d8c7d5698aca79539e0c1b1de8fc4440bda7f323fef605ab7cdff', 'certificates/source_norms/retained-transport/retained135125_heavy_comparison.json': '98195f65f9d5acc4a27b8275952488b928e5204c56871e9a41cf4f32cf0e4ff6', 'certificates/source_norms/retained-transport/retained135125_survival_comparison.json': '67d7003462bde8fa391245e76f226694cea286ab005d0404a7cfe4046453b797', 'profile-notes/125-the-complete-off-face-omitted-tails-recover-every-face-constant.md': 'cbe1fc88855354bd58e7a11ff22574bd8f9f9f94dceb57612c3ac8b1d943df17', 'profile-notes/transport/195-the-complete-source-comparison-extends-beyond-the-old-radius-domain.md': '4ce83eb8dce7127273b13d431f23d608eed3e152218a6eaf57406c60e339b991', 'profile-notes/transport/208-the-expanded-seven-survival-bound-covers-both-wide-source-domains.md': '9beb7e1c7eb5b006d896927b536d4a85a2b11b39ad16025941907762a31ad5e2', 'profile-notes/transport/218-the-retained-deletions-control-sixteen-complete-tests.md': '2fa3135eb73df6334b84586d81f45d0ca7bd1333a1e0a859595c9a34b07fe9b7', 'profile-notes/transport/227-the-actual-deletion-mask-rows-have-one-off-face-error-budget.md': '5f755984495bf3a0229f60c597b6454beed932fe6113a93884e7f74e4c0ef29b', 'profile-notes/transport/228-the-complete-pure-three-projection-shares-the-deletion-row-budget.md': 'f0866c11b52aba685e52d4f718a4fe9dfed506d86e5d3b262bd3f4eef44aa4d0', 'frontier/transport/joint_deletion_row_transport.py': '22eea33556056edb038580598002e32c74d4cfa9297a6c07c4bfc2ae34469d3d', 'frontier/transport/selected_deletion_mask_row_transport.py': '5a1ac7bfc00bf04edc27ec4b87e2fd232eaa989cc6e50edad1536f10ae7b1ae9', 'profile-notes/156-exposing-each-loss-gives-exact-rational-joint-price-bounds.md': '97e06983dc0c964fb935a34e6561f1cbcfaaad3adef845c6ab24dd9d56f5c3a1', 'profile-notes/158-the-seven-containing-pair-tails-have-one-exposed-source-price.md': '782a5b48fb152002ec55b2753bcf976799f5c8a8cabaa37481fe9f399c932127'}
Z=F(0)


def require(ok,message):
    if not ok:
        raise ValueError(message)


def module(n,p):
    spec=importlib.util.spec_from_file_location(n,p)
    require(spec is not None and spec.loader is not None,'Loadable original provider')
    result=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(v):
    if isinstance(v,F):return str(v)
    if isinstance(v,dict):return{str(k):encode(x)for k,x in v.items()}
    if isinstance(v,(list,tuple)):return[encode(x)for x in v]
    return v


PFACE=(F(1,50),F(1,36),F(1,75),F(1,108))
CRT=(Z,F(1,675),F(1,675),F(2,2025))
FAMILIES=((3,3),(5,2),(5,2),(5,2))

def omitted(t,family):
    k=min(t-1,4)
    if family==0:return({3}if k>=2 else set())|({4}if k>=4 else set())
    if family==1:return{2}if k>=1 else set()
    if family==2:return{2}if k>=3 else set()
    return set()

def finite_coefficients(a,j,bridge,depth):
    require(j in(2,4,6)and a and all(1<=t<=8 and x>=0 for t,x in a.items()),'Original nonnegative finite hinge combination')
    choices=list(product(range(5),range(3)))if j==6 else[(m,0)for m in range(j+1)]
    def g(t,v,m,e):return depth.seven_increment(t,v,m,e)if j==6 else bridge.seven_increment(t,v,m)
    # The complete unit-seven infinite series occurs inside both exact providers.
    ghead=max(sum(at*g(t,v,m,e)for t,at in a.items())for v in range(1,7)for m,e in choices)
    A=[sum(at for t,at in a.items()if min(t-1,4)>=i)for i in range(1,5)]
    dg=[]
    for i in range(1,5):
        values=[sum(at*(g(t,v+k+1,m,e)-g(t,v+k,m,e))for t,at in a.items()if min(t-1,4)>=i)
                for v in range(1,7)for k in range(i)for m,e in choices]
        require(min(values)>=0,'Every selected raw seven increment remains increasing')
        dg.append(max(values))
    H6=sum(at*max(6-t,0)for t,at in a.items())
    MH=sum(at*max(6+min(t-1,4)-t,0)for t,at in a.items())
    return ghead,A,dg,H6,MH

def deletion_tail_data(a,j,d,R,N=None):
    """Full D_H and full assigned tail, before spending the shared defect budget.

    In shifted_primitive_prices, E5 and E15 denote E5-G*q5 and E15-G*q15.
    Add G times tail_wrong_slot_coefficients dotted with(q5,q15).
    The old-hinge W price MH is included once; raw-head/profile transport is not.
    """
    a={int(t):F(v)for t,v in a.items()if F(v)}
    d,R=F(d),F(R)
    require(j in(2,4,6)and a and all(1<=t<=8 and v>0 for t,v in a.items()),'Original positive hinge vector')
    require(0<=d<=F(1,12)and R>=0,'Valid source endpoint for the full deletion/tail formulas')
    At=sum(a.values());H=sum(at*max(6-t,0)for t,at in a.items())
    MH=sum(at*max(6+min(t-1,4)-t,0)for t,at in a.items())
    if N is None:
        N=4
        if d+R:
            while F(1,3**N)>d+R:N+=1
    require(isinstance(N,int)and N>=4,'One finite support cut fixed for the whole rectangle')
    kap=(6-d)/(3-2*d);tb=2*(1+d)/(1-4*d);Cb=(F(3,4)+d/4)/(F(1,5)-3*d/8)
    require(Cb>=1+tb,'Uniform full E3 projection price domination')
    source_deletion=H*(d/(120*(3-2*d))+19*d/3600)
    dc=(d/4,13*d/90,d/15,d/45)
    Hb=(F(1,20)+21*d/20-d*d/5,F(1,10)+(19*d+2*d*d)/90,
        F(1,15)+d/9,F(1,45)+d/30-d*d/360)
    require(min(Hb)>=0,'Full raw-minus-reference envelopes')
    P=[];geom=[]
    for f,(p,start)in enumerate(FAMILIES):
        count=Z;geometric=Z
        for t,at in a.items():
            O=omitted(t,f)
            require(all(start<=n<=N for n in O),'All assigned omissions inside the fixed support')
            count+=at*(N-start+1-len(O))
            geometric+=at*(F(1,p**(start-1)*(p-1))-sum(F(1,p**n)for n in O))
        P.append(count);geom.append(geometric)
    P3,P5,P15,P45=P
    source_tail=sum(x*y for x,y in zip(dc,geom))+At*sum(Hb[f]*F(1,p**N*(p-1))for f,(p,start)in enumerate(FAMILIES))+d*P5/240
    zeta={2:F(3,280),4:F(1,168),6:F(23,5880)}[j]
    source_tail+=At*zeta*d
    if d==R==0:
        source_tail=Z  # Every actual family excess vanishes exactly at the face.
    names=('E5','E15','E27','Ege4','E5d','E15d','omega')
    prices=(P3+H/9,kap*P3,P5+H*Cb,P5+H*(1+tb),P3+H,kap*(P3+H),P3+P5+P15+P45+MH)
    return{'cut':N,'source_whole_hinge_deletion':source_deletion,'source_complete_tails':source_tail,
           'combined_source_upper':source_deletion+source_tail,
           'shifted_primitive_prices':dict(zip(names,prices)),
           'tail_wrong_slot_coefficients':[P3,kap*P3],
           'H6':H,'maximum_selected_old_hinge':MH,
           'all_complete_tail_counts':P,'all_complete_tail_geometric_coefficients':geom}


def evaluate_with_finite(a,j,finite,d,R,G,N=None):
    ghead,A,dg,H,MH=finite
    require(0<=d<=F(1,12)and R>=0 and G>0,'Nonnegative endpoint and positive proven wrong-slot gap')
    require((d<=F(1,20)and R<=F(1,1000)and G<=F(1,60))
            or(d<=F(1,12)and R<=F(1,3000)and G<=F(53,2700)), 'Subset of an established195/208 domain with a valid gap')
    if d==R==0:return{'error_upper':Z,'scope':'Exact face, zero additive error.'}
    tail=deletion_tail_data(a,j,d,R,N)
    require(H==tail['H6']and MH==tail['maximum_selected_old_hinge'],'The same full hinge in finite and deletion/tail terms')
    U=d/(1-d);v0=min(F(1,20),U/4+10*R);v1=min(F(1,10),U/4+5*R/(F(1,3)-d/18))
    delta_caps=2*d/45+v0/6+v1/3
    delta_budgets=(9+d)*U/72+d/36
    wmax=1+d/5+R/G
    source_head=(delta_caps+delta_budgets)*(wmax*H+ghead)+41*d*H/900
    dp=(d/450,max(v0,v1)/27,d/450,max(v0,v1)/81)
    selected_q=sum(Ai*(p+c)for Ai,p,c in zip(A,PFACE,CRT))
    source_selected=sum(dp_i*(wmax*Ai+gg)for dp_i,Ai,gg in zip(dp,A,dg))+d*selected_q/5
    q5price=H/10+selected_q;q15price=H/15+selected_q
    # Pass the nonnegative shifted deletion prices to full defects, then
    # add the finite objective's q prices before using the one unshifted budget.
    prices=dict(tail['shifted_primitive_prices'])
    prices['E5']+=q5price/G;prices['E15']+=q15price/G
    source=source_head+source_selected+tail['combined_source_upper']
    residual=R*max(prices.values());result=source+residual
    require(result>=0 and min(prices.values())>=0,'Valid nonnegative all-layout error')
    return{'cut':tail['cut'],'source_head':source_head,'source_selected':source_selected,
           'source_whole_hinge_deletion':tail['source_whole_hinge_deletion'],
           'source_complete_tails':tail['source_complete_tails'],'one_residual_prices':prices,
           'one_residual_upper':residual,'error_upper':result,'H6':H,'maximum_selected_old_hinge':MH,
           'finite_raw_increment_maximum':ghead,'finite_selected_increment_maxima':dg,
           'all_complete_tail_counts':tail['all_complete_tail_counts'],
           'all_complete_tail_geometric_coefficients':tail['all_complete_tail_geometric_coefficients']}


def evaluate(a,j,d,R,G,N=None):
    """Public complete-candidate error API; all arithmetic uses exact rationals."""
    a={int(t):F(v)for t,v in a.items()if F(v)}
    base=Path(__file__).resolve().parents[2]
    bridge=module('pruning_api_bridge',base/'frontier/k_face_common_seven_hinges.py')
    depth=module('pruning_api_depth',base/'frontier/transport/second_depth_seven_comparison.py')
    return evaluate_with_finite(a,j,finite_coefficients(a,j,bridge,depth),F(d),F(R),F(G),N)

def check_algebra(bridge):
    pre,raw,_,descendant=bridge.source_tables(2)
    require(sum(sum(row)for row in raw)==F(97,360)and sum(sum(row)for row in raw[1:])==F(41,180)
            and sum(row[4]for row in raw)==F(1,10)and sum(row[4]for row in raw[2:])==F(1,15),'All exact face raw coefficient sums')
    probs=(F(1,50),F(1,36),F(1,75),F(1,108))
    actual=(max(sum(descendant[c][s]/25 for c in range(5))for s in range(5)),
            max(sum(pre[c][s]/27 for s in range(5))for c in range(5)),
            max(sum(descendant[c][s]/25 for c in range(5)if bridge.ROOT[c]==r)for r in range(2)for s in range(5)),
            max(sum(pre[c][s]/81 for s in range(5))for c in range(5)))
    require(actual==probs==PFACE,'Every exact selected operator norm')
    face_c=(F(7,10),F(2,5),F(4,15),F(4,45));remainders=[]
    for t in range(1,6):
        value=F(1,72)
        for f,(p,start)in enumerate(FAMILIES):
            value+=face_c[f]*(F(1,p**(start-1)*(p-1))-sum(F(1,p**n)for n in omitted(t,f)))
        remainders.append(value)
    require(remainders[0]==F(163,1800)and remainders[-1]==F(19,648),'Unpunctured and fully punctured face tails exactly recovered')
    return{'face_zero_seven_remainders':remainders,'face_raw_mass_cap_sum':F(97,360),'selected_operator_norms':PFACE}



def positive_tail_checks():
    face=(F(5,36),F(1,12),F(3,4),F(1,2),F(1,3),F(1,9),F(1))
    source=((F(1,12),F(1,12),F(1,36),F(1,72),Z,Z),
            (Z,F(1,36),Z,Z,Z,Z),(Z,F(1,4),Z,Z,Z,Z),
            (Z,Z,Z,F(1,18),Z,Z))+((Z,)*6,)*3
    coefficients={2:(F(1,35),F(1,5),F(1,90),F(11,700),F(1,20),F(1,20),F(1,360)),
                  4:(F(1,35),F(1,35),F(1,90),F(11,700),F(11,700),F(1,20),F(1,360)),
                  6:(F(1,245),F(1,35),F(1,90),F(53,4900),F(11,700),F(1,20),F(1,360))}
    constants={2:F(779,12600),4:F(13,360),6:F(2669,88200)}
    zeta={2:F(3,280),4:F(1,168),6:F(23,5880)}
    records={}
    require(coefficients[4][1]==coefficients[2][1]-F(6,35)
            and coefficients[4][4]==coefficients[2][4]-F(6,175)
            and coefficients[6][0]==coefficients[4][0]-F(6,245)
            and coefficients[6][3]==coefficients[4][3]-F(6,1225),
            'Remove precisely the assigned63/105 and147/245 series terms')
    for j,c in coefficients.items():
        prices=[sum(a*b[i]for a,b in zip(c,source))for i in range(6)]
        require(min(c)>0 and sum(a*b for a,b in zip(c,face))==constants[j]
                and max(prices)==zeta[j] and sorted(prices)[-2]<=F(11,12)*zeta[j],
                'Complete positive-seven series and exposed source price through d=1/12')
        records[j]={'scalar_coefficients':c,'six_loss_prices':prices,
                    'face_constant':constants[j],'source_price':zeta[j]}
    return records


def original_scans(heavy,survival):
    require(heavy['r']==heavy['rho']==survival['r']==survival['rho']=='0'
            and heavy['faces']==survival['faces']
            and F(heavy['mass'])==F(survival['mass'])==F(53,360),
            'The same two actual saturated face domains')
    require([r['index']for r in heavy['heavy_results']]==[0,16]
            and survival['AP11_block_results'][0]['block']==0,'All four original independent test identities')
    rows=[('heavy0',heavy['heavy_results'][0]['scan']),('heavy16',heavy['heavy_results'][1]['scan']),
          ('AP13',survival['AP13_result']['scan']),('AP11-B0',survival['AP11_block_results'][0]['scan'])]
    out=[]
    for label,scan in rows:
        require(scan['pruning_credit']=='whole-hinge-deletion','Original full D_H pruning semantics')
        M=F(scan['complete_hinge_upper']);counts=scan['counts'];classes={}
        require(counts['prefix_bounded']==0 and F(scan['maximum_pruned_uppers']['prefix'])==-1,
                'No untransported prefix-pruned branch')
        require(counts['two']==125000 and counts['four']==50*(counts['two']-counts['two_bounded'])
                and counts['six']==10*(counts['four']-counts['four_bounded'])
                and counts['joint']-1==counts['six']-counts['six_bounded'], 'Complete original scan partition')
        for kind,mult in (('two',500),('four',10),('six',1)):
            number=counts[kind+'_bounded'];upper=F(scan['maximum_pruned_uppers'][kind])
            require(number>0 and 0<=upper<=M,'Nonempty original class and its exact complete face bound')
            classes[kind]={'pruned_nodes':number,'original_leaves':number*mult,
                           'face_upper':upper,'face_margin':M-upper}
        require(sum(v['original_leaves']for v in classes.values())+counts['joint']-1
                ==scan['covered_containing_choices']==62500000,'All original choices retained exactly once')
        coefficients={int(t):F(a)for t,a in scan['coefficients'].items()if F(a)}
        require(coefficients and all(1<=t<=8 and a>0 for t,a in coefficients.items()),'Original positive hinge vector')
        out.append({'objective':label,'coefficients':coefficients,'face_maximum':M,'classes':classes,
                    'joint_original_leaves':counts['joint']-1,'branch_decisions_sha256':scan['branch_decisions_sha256']})
    return out


def calculate(base):
    io=module('pruning_rows_io',base/'certificate_io.py')
    read=lambda name:json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')))
    heavy,survival=[read('retained-transport/retained135125_heavy_comparison'), read('retained-transport/retained135125_survival_comparison')]
    pins=dict(PINS)
    for parent in(heavy,survival):
        for path,pin in parent['source_sha256'].items():
            require(path not in pins or pins[path]==pin,'Consistent original source '+path)
            pins[path]=pin
    for path,pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Pinned logical original source '+path)
    bridge=module('pruning_rows_bridge',base/'frontier/k_face_common_seven_hinges.py')
    depth=module('pruning_rows_depth',base/'frontier/transport/second_depth_seven_comparison.py')
    scans=original_scans(heavy,survival)
    finite={(r['objective'],j):finite_coefficients(r['coefficients'],j,bridge,depth)for r in scans for j in(2,4,6)}
    checks=check_algebra(bridge)
    checks['complete_positive_seven_tails']=positive_tail_checks()
    parameters=[('wide',F(1,20),F(1,1000),F(1,60)),('extended',F(1,12),F(1,3000),F(53,2700)),
         ('small_1e3',F(1,1000),F(1,10**6),F(1,60)),('small_1e4',F(1,10**4),F(1,10**7),F(1,60)),
         ('small_1e6',F(1,10**6),F(1,10**9),F(1,60)),('small_1e8',F(1,10**8),F(1,10**11),F(1,60))]
    rows=[]
    for label,d,R,G in parameters:
        objects={}
        for scan in scans:
            name=scan['objective'];a=scan['coefficients']
            bounds={str(j):evaluate_with_finite(a,j,finite[name,j],d,R,G)for j in(2,4,6)}
            errors=[bounds[str(j)]['error_upper']for j in(2,4,6)]
            comparisons={}
            for kind,error in zip(('two','four','six'),(errors[0],max(errors[:2]),max(errors))):
                upper=scan['classes'][kind]['face_upper']+error
                comparisons[kind]={'complete_upper':upper,'error_upper':error,
                   'face_margin_after_transport':scan['face_maximum']-upper,
                   'within_face_ceiling':upper<=scan['face_maximum']}
                if label=='small_1e8':
                    require(upper<scan['face_maximum'],'All twelve complete pruning classes preserve their face ceilings')
            objects[name]={'candidate_errors':bounds,'complete_pruning_comparisons':comparisons}
        rows.append({'domain':label,'delta':d,'rho':R,'gap':G,'objectives':objects})
    for scan in scans:
        for j in(2,4,6):
            require(evaluate_with_finite(scan['coefficients'],j,finite[scan['objective'],j],Z,Z,F(1,60))['error_upper']==0,
                    'Exact face specialization with zero transport error')
    return encode({'schema':'erdos7-uniform-pruning-candidate-transport-v1','source_sha256':pins,
        'original_scans':scans,'algebra_checks':checks,'domains':rows,
        'scope':'Explicit uniform all-layout errors for the complete two/four/six candidates, full D_H, independent labels and full assigned infinite tails. The same seven actual defects are priced once. All twelve pruning classes preserve their original face ceilings on delta<=10^-8,rho<=10^-11 with gap1/60. Expanded joint-dual values, remaining52-cost and signed-mass consumer, global complement and unrestricted Erdos7 remain separate. No Lean verification.'})


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    modes=parser.add_mutually_exclusive_group()
    modes.add_argument('--write',action='store_true');modes.add_argument('--check',action='store_true')
    args=parser.parse_args();result=calculate(args.base)
    io=module('pruning_rows_output',args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE,json.dumps(result,indent=2)+'\n')
    else:
        require(result==json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)),'Exact complete pruning-transport certificate')
    small=result['domains'][-1]
    for name,row in small['objectives'].items():
        errors=[float(F(row['candidate_errors'][str(j)]['error_upper']))for j in(2,4,6)]
        print(name+': complete candidate errors '+str(errors))
    print('PASS: all12 complete pruning classes remain below their face ceilings on the stated positive rectangle.')


if __name__=='__main__':
    try:
        main()
    except(ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError)as error:
        print('FAIL: '+str(error),file=sys.stderr)
        raise SystemExit(1)
