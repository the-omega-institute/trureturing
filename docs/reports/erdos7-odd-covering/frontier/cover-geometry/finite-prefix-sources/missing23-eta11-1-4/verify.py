"""Two additional eta11 slices by monotone reuse; no geometry is run here."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from collections import Counter
import argparse,hashlib,json,runpy
ROOT=Path(__file__).resolve().parent
SOURCE_CURRENT11_SHA256='0912b101439bbe9d0e11e3f4b0b9668cc7b8dd4a514eeef0df058e84edece7aa'
LATE_VERIFY_SHA256='05048c5691b6201e4d6d402cf8acaf3782312687a64db5829d632bf830a5c118'
ETAS=(1,4,7,8,11,13,14)
def demand(test,message):
    if not test:raise ValueError(message)
def verify(late,base):
    raw=(ROOT/'source_current11.json').read_bytes()
    demand(hashlib.sha256(raw).hexdigest()==SOURCE_CURRENT11_SHA256,'pinned source current11 inputs')
    source=json.loads(raw)
    demand(source['state']=='A1' and source['node']==[2,4,1,8,1,2,1,0,13] and source['xi7']==[1,4,7,14],'exact attributed source row')
    current11={r['eta']:F(r['cost']) for r in source['rows']}
    demand(len(source['rows'])==7 and set(current11)==set(ETAS),'all seven source phase bounds')
    source_path=late/'verify.py'
    demand(hashlib.sha256(source_path.read_bytes()).hexdigest()==LATE_VERIFY_SHA256,'pinned late280 consumer')
    ext=runpy.run_path(str(source_path));prior=ext['verify'](base)
    new,v=ext['read_inputs'](base);old=v['DATA'];A=v['A'];B=v['B'];C=v['C']
    domain13=v['DOMAIN'];ref=list(map(F,prior['reference_late_bounds']));fa=list(map(F,prior['direct_late_bounds']['FA']))
    ordinary=v['continuation'](True)[0];lift11=v['perturbation'](13,11);lift13=v['perturbation'](11,13)
    h16=F(prior['H16']);l7=F(old['current7']);flat13=v['load_table'](old['current13']['flat']);ceil=v['ceil_fraction'];carrier=v['CELLS']
    cap=F(5,3)
    for s in range(5):
        zero=min(F(1),cap*F(10-s,11))-cap/11
        demand(F(0)<=zero<=F(28,33),'pointwise flat11 dominance')
    rows=[];counts=Counter();byeta={}
    for eta in (1,4):
        starts=tuple(product((1,2),range(1,5),(2,4,5,7,8),(eta,)))
        erows=[]
        for x11,x13 in product(starts,domain13):
            # Labels remain explicit; only the outgoing zero11 field is enlarged.
            field=tuple(x for x in carrier if all(x%m==a for m,a in zip((3,5,9,15),x11)))
            l11=current11[eta];l13=flat13[x13]
            options=[('ordinary',ordinary)]
            for b11,b13 in ((A,B),(B,A)):
                late_loss=[min(ref[i]+lift11[i]+(lift13[i] if x13!=b13 and i>0 else 0),ordinary[i]) for i in range(3)]
                options.append(('transfer',late_loss))
            if x13 in (A,B):options.append(('flat11-A',fa))
            route,late_loss=min(options,key=lambda r:sum(r[1],F(0)))
            losses=[l7,l11,l13,*late_loss];live=F(135,4)-sum(losses,F(0));slack=14*live-h16
            demand(live>0 and slack>0,'new eta11 slice strict query16 inequality')
            micro=[int(ceil(x,10**6)*10**6) for x in losses];dmicro=33750000-sum(micro);smicro=14*dmicro-int(ceil(h16,10**6)*10**6)
            demand(smicro>0,'millionth certificate for new eta11 slice')
            upper=ceil(15+h16/live);row=dict(xi11=list(x11),xi13=list(x13),actual_zero11_support=list(field),route=route,losses=list(map(str,losses)),live_lower=str(live),slack_lower=str(slack),loss_micro=micro,live_lower_micro=dmicro,slack_lower_micro=smicro,query_upper=str(upper),query_upper_decimal=float(upper))
            rows.append(row);erows.append(row);counts[route]+=1
        demand(len(erows)==1600,'complete phase-slice domain')
        byeta[str(eta)]=dict(prefix_pairs=1600,worst=max(erows,key=lambda r:F(r['query_upper'])),minimum_micro_slack=min(r['slack_lower_micro'] for r in erows))
    demand(len(rows)==3200,'complete two-slice disjoint domain')
    return dict(scope='Fixed A1 and xi7=(1,4,7,14); eta11 in{1,4}, eta13=14; each prefix slice has40x40 physical labels; later17/19/29 each280 projections. No other slice or node is concluded.',source_thresholds=[2,4,4,8,8,16],query=16,covered_prefix_pairs=3200,later_choices_per_pair=280**3,total_parameter_tuples=3200*280**3,route_counts=dict(counts),slices=byeta,worst=max(rows,key=lambda r:F(r['query_upper'])),minimum_micro_slack=min(r['slack_lower_micro'] for r in rows),H16=str(h16),source_current11_sha256=SOURCE_CURRENT11_SHA256,late_verify_sha256=LATE_VERIFY_SHA256,verification='Exact rational reuse and complete3200 route checks. New current11 inputs are attributed source closing bounds, not a new geometry enumeration. Prior geometry verification remains separate.',routes=rows)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--late',type=Path,default=ROOT.parent/'missing23-late280');p.add_argument('--base',type=Path,default=ROOT.parent/'missing23-eta14');p.add_argument('--output',type=Path);args=p.parse_args()
    result=verify(args.late,args.base)
    if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='routes'},indent=2))
