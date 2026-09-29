"""Remaining six eta13 slices at one fixed missing23 node; stdout-only by default."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from collections import Counter
import argparse,hashlib,json,runpy
ROOT=Path(__file__).resolve().parent
BOUNDS_SHA256='9744ea02c4bd46d3d6696e967f0476f9bc40e634c5c1d5ecc7440eea7ad20db8'
LATE_VERIFY_SHA256='05048c5691b6201e4d6d402cf8acaf3782312687a64db5829d632bf830a5c118'
FIRST_VERIFY_SHA256='28cfb7ae7162462ebbdd9c27c2829ad89480a5c701294dc9d1b1df6c52d863dd'
REST_VERIFY_SHA256='0222ca05f70dbfe19a5f11c7f48cf217e4cc91a8daf91b743f9369a4efdf917b'
ETAS=(1,4,7,8,11,13,14);NEW_ETAS=(1,4,7,8,11,13)
def demand(test,message):
    if not test:raise ValueError(message)
def pinned_module(folder,pin):
    path=folder/'verify.py';demand(hashlib.sha256(path.read_bytes()).hexdigest()==pin,'pinned prior consumer: '+folder.name)
    return runpy.run_path(str(path))
def verify(late,base,first,rest):
    raw=(ROOT/'bounds.json').read_bytes();demand(hashlib.sha256(raw).hexdigest()==BOUNDS_SHA256,'pinned eta13 inputs');data=json.loads(raw)
    demand(data['scope']==dict(node=[2,4,1,8,1,2,1,0,13],xi7=[1,4,7,14],eta11=list(ETAS),eta13=list(NEW_ETAS),late_etas=list(ETAS),thresholds=[2,4,4,8,8,16],query=16),'fixed extension scope')
    ext=pinned_module(late,LATE_VERIFY_SHA256);prior=ext['verify'](base);_,v=ext['read_inputs'](base)
    first_module=pinned_module(first,FIRST_VERIFY_SHA256);first_result=first_module['verify'](late,base)
    rest_module=pinned_module(rest,REST_VERIFY_SHA256);rest_result=rest_module['verify'](late,base)
    # The prior consumers validate their complete pinned numerical inputs.
    earlier=json.loads((rest/'bounds.json').read_text());source=json.loads((first/'source_current11.json').read_text())
    old=v['DATA'];swap=v['swap'];ceil=v['ceil_fraction'];A=v['A'];B=v['B'];carrier=v['CELLS']
    domain11=tuple(product((1,2),range(1,5),(2,4,5,7,8),ETAS));domain13=tuple(product((1,2),range(1,5),(2,4,5,7,8),NEW_ETAS))
    l11=v['load_table'](old['current11']);l11.update({tuple(r['xi11']):F(r['cost']) for r in earlier['current11']})
    source11={r['eta']:F(r['cost']) for r in source['rows']}
    for x in domain11:
        if x[-1] in (1,4):l11[x]=source11[x[-1]]
    demand(set(l11)==set(domain11) and len(l11)==280,'complete actual current11 source domain')
    l13={tuple(r['xi13']):F(r['cost']) for r in data['current13_flat11']}
    demand(len(data['current13_flat11'])==240 and set(l13)==set(domain13),'complete240 flat11-current13 labels')
    reps={tuple(r['representative']) for r in data['current13_flat11']}
    demand(reps==set(product((1,2),range(1,5),(2,4,7,8),NEW_ETAS)),'exact192 geometry representatives')
    crt={(x%27,x%5):x for x in range(135)}
    def perm(x):
        y=x%27;y+=3 if y%9==2 else -3 if y%9==5 else 0
        return crt[y,x%5]
    demand({perm(x) for x in carrier}==set(carrier),'same live carrier')
    for row in data['current13_flat11']:
        x=tuple(row['xi13']);rep=tuple(row['representative']);transport=row['transport']
        demand((transport=='identity' and rep==x) or (transport=='prefix2_to5_mod9' and x[2]==5 and rep==swap(x)),'explicit physical-label transport')
        demand(l13[x]==l13[rep],'transported cost equality')
        demand(all((z%m==a)==(perm(z)%m==b) for z in carrier for m,a,b in zip((3,5,9,15),x,swap(x))),'all240 label cylinders transported')
    for q,t,flat in ((11,4,F(28,33)),(13,4,F(23,26))):
        cap=F(q-1,q-1-t)
        demand(all(0<=min(F(1),cap*F(q-1-s,q))-cap/q<=flat for s in range(5)),'nonnegative pointwise zero-factor majorant')
    demand(set(data['released_FF'])=={'17','19','29'},'three FF stages')
    ff=[]
    for q in (17,19,29):
        table=data['released_FF'][str(q)];demand(set(table)==set(map(str,ETAS)),'all seven late phases')
        demand(all(F(x)>=0 for x in table.values()),'nonnegative direct FF costs');ff.append(max(map(F,table.values())))
    ref17=F(prior['reference_late_bounds'][0]);demand(ref17<ff[0],'A/B full13 reference17 improvement')
    h16=F(prior['H16']);l7=F(old['current7']);groups={};counts=Counter();worst=None;minimum_micro=None;minimum_live=None;total=0
    for x11,x13 in product(domain11,domain13):
        use_ref=x11 in (A,B);route='AB-reference17_FF19_29' if use_ref else 'FF17_19_29'
        losses=[l7,l11[x11],l13[x13],ref17 if use_ref else ff[0],ff[1],ff[2]]
        live=F(135,4)-sum(losses,F(0));slack=14*live-h16
        demand(live>0 and slack>0,'same-source six-loss strict query16 inequality')
        micro=[int(ceil(x,10**6)*10**6) for x in losses];dmicro=33750000-sum(micro);smicro=14*dmicro-int(ceil(h16,10**6)*10**6)
        demand(smicro>0,'millionth certificate')
        row=dict(xi11=list(x11),xi13=list(x13),route=route,losses=list(map(str,losses)),loss_micro=micro,live_lower=str(live),slack_lower=str(slack),live_lower_micro=dmicro,slack_lower_micro=smicro,query_upper=str(ceil(15+h16/live)))
        key=f'{x11[-1]},{x13[-1]}'
        if key not in groups:groups[key]=dict(prefix_pairs=0,worst=row,minimum_micro_slack=smicro)
        group=groups[key];group['prefix_pairs']+=1;group['minimum_micro_slack']=min(group['minimum_micro_slack'],smicro)
        if F(row['slack_lower'])<F(group['worst']['slack_lower']):group['worst']=row
        if worst is None or slack<F(worst['slack_lower']):worst=row
        minimum_micro=smicro if minimum_micro is None else min(minimum_micro,smicro)
        minimum_live=live if minimum_live is None else min(minimum_live,live)
        counts[route]+=1;total+=1
    demand(total==67200 and len(groups)==42 and all(g['prefix_pairs']==1600 for g in groups.values()),'complete six eta13 slices, forty physical labels per phase')
    demand(dict(counts)=={'FF17_19_29':66720,'AB-reference17_FF19_29':480},'complete two-route partition')
    prior_pairs=prior['covered_prefix_pairs']+first_result['covered_prefix_pairs']+rest_result['covered_prefix_pairs']
    demand(prior_pairs==11200,'earlier disjoint eta13=14 slices')
    combined_worst=max((prior['worst'],first_result['worst'],rest_result['worst'],worst),key=lambda r:F(r['query_upper']))
    return dict(scope='Fixed A1 node and xi7=(1,4,7,14); xi11 all280, xi13 the240 labels with eta in1,4,7,8,11,13, later17/19/29 each280. The three prior packages cover the disjoint eta13=14 slice. No other node or xi7.',source_thresholds=[2,4,4,8,8,16],query=16,covered_prefix_pairs=total,later_choices_per_pair=280**3,total_parameter_tuples=total*280**3,route_counts=dict(counts),FF_late_bounds=list(map(str,ff)),AB_full13_reference17=str(ref17),current13_maxima={str(e):str(max(a for x,a in l13.items() if x[-1]==e)) for e in NEW_ETAS},H16=str(h16),worst=worst,minimum_live_lower=str(minimum_live),minimum_micro_slack=minimum_micro,phase_pair_certificates=groups,combined_fixed_node=dict(prefix_pairs=prior_pairs+total,total_parameter_tuples=280**5,worst_query_upper=combined_worst['query_upper']),bounds_sha256=BOUNDS_SHA256,verification='Exact rational arithmetic checks every67200 ordered prefix pair. Retained output groups certificates into42 disjoint1600-pair phase blocks. Geometry reconstruction remains a separate explicit obligation.')
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--late',type=Path,default=ROOT.parent/'missing23-late280');p.add_argument('--base',type=Path,default=ROOT.parent/'missing23-eta14');p.add_argument('--first',type=Path,default=ROOT.parent/'missing23-eta11-1-4');p.add_argument('--rest',type=Path,default=ROOT.parent/'missing23-eta11-rest');p.add_argument('--output',type=Path);args=p.parse_args()
    result=verify(args.late,args.base,args.first,args.rest)
    if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='phase_pair_certificates'},indent=2))
