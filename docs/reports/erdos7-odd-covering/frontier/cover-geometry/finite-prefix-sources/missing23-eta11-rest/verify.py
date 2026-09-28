"""Four remaining eta11 slices, with actual current11 costs and two refinements."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from collections import Counter
import argparse,hashlib,json,runpy
ROOT=Path(__file__).resolve().parent
BOUNDS_SHA256='b929bbe055ea9a9208d1879b2ee8151bcf3cdc1044d1180bb36c04bfd7726a97'
LATE_VERIFY_SHA256='05048c5691b6201e4d6d402cf8acaf3782312687a64db5829d632bf830a5c118'
ETAS=(1,4,7,8,11,13,14);NEW_ETAS=(7,8,11,13)
D=(2,3,2,8);E=(2,3,5,8)
def demand(test,message):
    if not test:raise ValueError(message)
def verify(late,base):
    raw=(ROOT/'bounds.json').read_bytes();demand(hashlib.sha256(raw).hexdigest()==BOUNDS_SHA256,'pinned actual-prefix inputs')
    data=json.loads(raw);demand(data['scope']==dict(node=[2,4,1,8,1,2,1,0,13],xi7=[1,4,7,14],eta11=list(NEW_ETAS),eta13=14,late_etas=list(ETAS),thresholds=[2,4,4,8,8,16],query=16),'declared extension scope')
    prior_path=late/'verify.py';demand(hashlib.sha256(prior_path.read_bytes()).hexdigest()==LATE_VERIFY_SHA256,'pinned late280 consumer')
    ext=runpy.run_path(str(prior_path));prior=ext['verify'](base);_,v=ext['read_inputs'](base);old=v['DATA'];A=v['A'];B=v['B'];C=v['C'];swap=v['swap'];ceil=v['ceil_fraction'];carrier=v['CELLS']
    domain11=tuple(product((1,2),range(1,5),(2,4,5,7,8),NEW_ETAS));domain13=v['DOMAIN']
    l11={tuple(r['xi11']):F(r['cost']) for r in data['current11']}
    demand(len(data['current11'])==160 and set(l11)==set(domain11),'complete160 actual current11 labels')
    representatives={tuple(r['representative']) for r in data['current11']}
    demand(representatives==set(product((1,2),range(1,5),(2,4,7,8),NEW_ETAS)),'exact128 source representatives')
    crt={(x%27,x%5):x for x in range(135)}
    def perm(x):
        y=x%27;y+=3 if y%9==2 else -3 if y%9==5 else 0
        return crt[y,x%5]
    demand({perm(x) for x in carrier}==set(carrier),'same live carrier')
    for row in data['current11']:
        x=tuple(row['xi11']);rep=tuple(row['representative']);transport=row['transport']
        demand((transport=='identity' and rep==x) or (transport=='prefix2_to5_mod9' and rep==swap(x) and x[2]==5),'explicit physical-label transport')
        demand(l11[x]==l11[rep],'transported numerical equality')
        demand(all((z%m==a)==(perm(z)%m==b) for z in carrier for m,a,b in zip((3,5,9,15),x,swap(x))),'all160 label cylinders transported')
    c13={tuple(r['xi13']):F(r['cost']) for r in data['current13_D']}
    demand(len(data['current13_D'])==3 and set(c13)=={(2,3,2,14),(2,3,5,14),C},'three actual-D current13 refinements')
    demand(set(data['released_DC'])=={'17','19','29'},'three direct continuation stages')
    dc=[]
    for q in (17,19,29):
        values=data['released_DC'][str(q)];demand(set(values)==set(map(str,ETAS)),'all seven actual late phases')
        dc.append(max(map(F,values.values())))
    ref=list(map(F,prior['reference_late_bounds']));fa=list(map(F,prior['direct_late_bounds']['FA']))
    ordinary=v['continuation'](True)[0];lift11=v['perturbation'](13,11);lift13=v['perturbation'](11,13)
    h16=F(prior['H16']);l7=F(old['current7']);flat13=v['load_table'](old['current13']['flat'])
    cap=F(5,3)
    demand(all(0<=min(F(1),cap*F(10-s,11))-cap/11<=F(28,33) for s in range(5)),'common flat11 majorant')
    rows=[];counts=Counter();slices={}
    for x11,x13 in product(domain11,domain13):
        l13=flat13[x13]
        if x11 in (D,E):
            key=swap(x13) if x11==E else x13
            if key in c13:l13=min(l13,c13[key])
        options=[('ordinary',ordinary)]
        for b13 in (A,B):
            loss=[min(ref[i]+lift11[i]+(lift13[i] if x13!=b13 and i>0 else 0),ordinary[i]) for i in range(3)]
            options.append(('transfer',loss))
        if x13 in (A,B):options.append(('flat11-A',fa))
        if x11 in (D,E) and x13==C:options.append(('DC-direct',dc))
        route,late_loss=min(options,key=lambda r:sum(r[1],F(0)))
        losses=[l7,l11[x11],l13,*late_loss];live=F(135,4)-sum(losses,F(0));slack=14*live-h16
        demand(live>0 and slack>0,'actual-prefix common query16 inequality')
        micro=[int(ceil(x,10**6)*10**6) for x in losses];dmicro=33750000-sum(micro);smicro=14*dmicro-int(ceil(h16,10**6)*10**6)
        demand(smicro>0,'millionth actual-prefix certificate')
        upper=ceil(15+h16/live);counts[route]+=1
        rows.append(dict(xi11=list(x11),xi13=list(x13),route=route,losses=list(map(str,losses)),loss_micro=micro,live_lower=str(live),slack_lower=str(slack),live_lower_micro=dmicro,slack_lower_micro=smicro,query_upper=str(upper),query_upper_decimal=float(upper)))
    demand(len(rows)==6400,'complete four-slice prefix domain')
    for eta in NEW_ETAS:
        erows=[r for r in rows if r['xi11'][-1]==eta];demand(len(erows)==1600,'complete each phase slice')
        slices[str(eta)]=dict(prefix_pairs=1600,worst=max(erows,key=lambda r:F(r['query_upper'])),minimum_micro_slack=min(r['slack_lower_micro'] for r in erows))
    demand(dict(counts)=={'transfer':6078,'flat11-A':320,'DC-direct':2},'complete disjoint routes')
    return dict(scope='Fixed A1/xi7A; eta11 in7,8,11,13; eta13=14; each slice40x40 prefix labels; later17/19/29 each280. No other eta13, node or xi7.',source_thresholds=[2,4,4,8,8,16],query=16,covered_prefix_pairs=6400,later_choices_per_pair=280**3,total_parameter_tuples=6400*280**3,route_counts=dict(counts),current11_maxima={str(e):str(max(value for x,value in l11.items() if x[-1]==e)) for e in NEW_ETAS},DC_late_bounds=list(map(str,dc)),H16=str(h16),slices=slices,worst=max(rows,key=lambda r:F(r['query_upper'])),minimum_micro_slack=min(r['slack_lower_micro'] for r in rows),bounds_sha256=BOUNDS_SHA256,late_verify_sha256=LATE_VERIFY_SHA256,verification='Exact rational arithmetic and complete6400 routing from pinned current upper bounds. Geometry maxima remain a separate replay obligation.',routes=rows)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--late',type=Path,default=ROOT.parent/'missing23-late280');p.add_argument('--base',type=Path,default=ROOT.parent/'missing23-eta14');p.add_argument('--output',type=Path);args=p.parse_args()
    result=verify(args.late,args.base)
    if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='routes'},indent=2))
