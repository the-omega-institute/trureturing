"""Two declared xi7 pilots; exact positive-difference transport of the fixed-node domain."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
import argparse,hashlib,json,runpy
ROOT=Path(__file__).resolve().parent
BOUNDS_SHA256='24eb182b3d3d3a20e95921a66f875dced7c3a659968bda9cd42503a379144944'
PRIOR_VERIFY_SHA256='1c3d7bb2839c59ef3b538fe16c958e7dfaa6b4791f405cc5a739a72b292ab863'
BASE_VERIFY_SHA256='a519fef29bb1fb76370ea1ca4d252365205093448d53b4442fd445d80e30018f'
OLD=(1,4,7,14);PILOTS=((2,4,7,4),(2,4,2,14));K7=(11,11,9,6,3)
def demand(test,message):
    if not test:raise ValueError(message)
def verify(prior,late,base,first,rest):
    raw=(ROOT/'bounds.json').read_bytes();demand(hashlib.sha256(raw).hexdigest()==BOUNDS_SHA256,'pinned transport bounds');data=json.loads(raw)
    demand(data['scope']==dict(node=[2,4,1,8,1,2,1,0,13],old_xi7=list(OLD),pilot_xi7=list(map(list,PILOTS)),source_thresholds=[2,4,4,8,8,16],query=16),'two-pilot scope')
    path=prior/'verify.py';demand(hashlib.sha256(path.read_bytes()).hexdigest()==PRIOR_VERIFY_SHA256,'pinned complete-domain consumer')
    lib=runpy.run_path(str(path));old=lib['verify'](late,base,first,rest)
    path=base/'verify.py';demand(hashlib.sha256(path.read_bytes()).hexdigest()==BASE_VERIFY_SHA256,'pinned base consumer');v=runpy.run_path(str(path))
    h0=F(old['H16']);rbar=F(old['combined_fixed_node']['worst_query_upper']);demand(h0>0 and rbar>15,'positive common query data')
    # Every prior row satisfies15+H16/D<=rbar. This is a common lower bound,
    # not an assertion that rounded query sorting identifies an exact minimum.
    dstar=h0/(rbar-15);old7=F(v['DATA']['current7']);ceil=v['ceil_fraction'];cells=v['CELLS']
    domain=tuple(product((1,2),range(1,5),(2,4,5,7,8),(1,4,7,8,11,13,14)))
    def field(xi):return tuple(K7[sum(x%m==a for m,a in zip((3,5,9,15),xi))] for x in cells)
    oldfield=field(OLD);dominated=[list(xi) for xi in domain if all(a<=b for a,b in zip(field(xi),oldfield))]
    demand(dominated==[list(OLD)],'only old projection is pointwise dominated without a charge')
    demand(len(data['pilots'])==2 and {tuple(r['xi7']) for r in data['pilots']}==set(PILOTS),'exact two distinct pilot inputs')
    rows=[]
    for row in data['pilots']:
        xi=tuple(row['xi7']);delta=tuple(max(a-b,0) for a,b in zip(field(xi),oldfield))
        demand(row['positive_difference_numerators']=={str(x):z for x,z in zip(cells,delta) if z},'actual positive difference on the same cells')
        e=row['delta_envelope'];env=(F(e['mass']),F(e['whole']),{F(t):F(a) for t,a in e['values'].items()})
        demand(set(env[2])==set(map(F,range(1,29))) and env[0]>0 and env[1]>0 and all(a>=0 for a in env[2].values()),'complete nonnegative difference envelope')
        dist=v['UNIT'];increments=[]
        for q,t in ((11,4),(13,4),(17,8),(19,8),(29,16)):
            increments.append(v['hinge'](t,dist,env)/F(14*(q-1-t)))
            dist=v['mul'](dist,v['full'](q,t))
        hinc=v['hinge'](16,dist,env)/14;l7=F(row['current7']);gain=old7-l7
        newd=dstar+gain-sum(increments,F(0));newh=h0+hinc;slack=14*newd-newh;success=newd>0 and slack>0
        # Rounded certificate floors available live mass and ceils every charge.
        dmicro=dstar.numerator*10**6//dstar.denominator
        gainmicro=gain.numerator*10**6//gain.denominator
        lossesmicro=[int(ceil(a,10**6)*10**6) for a in increments]
        dnewmicro=dmicro+gainmicro-sum(lossesmicro);hnewmicro=int(ceil(newh,10**6)*10**6);smicro=14*dnewmicro-hnewmicro
        demand(success==(xi==PILOTS[0]),'the declared positive-comparison outcome')
        if success:demand(dnewmicro>0 and smicro>0,'millionth strict transport certificate')
        rows.append(dict(xi7=list(xi),current7=str(l7),current7_saving=str(gain),positive_difference_mass=str(env[0]/14),loss_increases=list(map(str,increments)),query_increase=str(hinc),new_live_lower=str(newd),new_query_upper_numerator=str(newh),slack_lower=str(slack),live_lower_micro=dnewmicro,slack_lower_micro=smicro,passes_positive_transport=success,query_upper=str(ceil(15+newh/newd)) if newd>0 else None,conclusion='All280^5 future physical choices satisfy the query16 certificate.' if success else 'This positive-only transport bound fails; no assertion of actual impossibility.'))
    demand(old['combined_fixed_node']['total_parameter_tuples']==280**5,'unchanged complete future-label domain')
    return dict(scope='Same fixed A1 node, source weights, labels, padding, thresholds and query16. Only two declared new xi7 are tested. The first passes positive-difference transport; the second does not.',source_thresholds=[2,4,4,8,8,16],query=16,old_xi7=list(OLD),old_common_H16=str(h0),old_common_query_upper=str(rbar),old_common_live_lower_from_query=str(dstar),pointwise_dominated_projection_count=len(dominated),pilots=rows,newly_certified_xi7=[list(PILOTS[0])],future_parameter_tuples_per_certified_xi7=280**5,bounds_sha256=BOUNDS_SHA256,verification='Exact rational transport from the pinned complete old-domain certificate and two explicit current7/difference-envelope inputs. No future280-squared geometry enumeration; integer geometry is separately replayed.')
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--prior',type=Path,default=ROOT.parent/'missing23-eta13-rest');p.add_argument('--late',type=Path,default=ROOT.parent/'missing23-late280');p.add_argument('--base',type=Path,default=ROOT.parent/'missing23-eta14');p.add_argument('--first',type=Path,default=ROOT.parent/'missing23-eta11-1-4');p.add_argument('--rest',type=Path,default=ROOT.parent/'missing23-eta11-rest');p.add_argument('--output',type=Path);args=p.parse_args()
    result=verify(args.prior,args.late,args.base,args.first,args.rest)
    if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
