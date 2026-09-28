"""All280 later projections at a fixed missing23 node and first two eta14 labels.

Exact arithmetic/routing conditional on pinned numerical upper bounds. The
separate geometry replay rebuilds those bounds. Default is stdout-only.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from collections import Counter
import argparse,hashlib,json,runpy
ROOT=Path(__file__).resolve().parent
BOUNDS_SHA256='7563de00779df733750cce6a2a075d3efe6211cfb2c9526f60456d5496090723'
BASE_VERIFY_SHA256='a519fef29bb1fb76370ea1ca4d252365205093448d53b4442fd445d80e30018f'
ETAS=(1,4,7,8,11,13,14)
A=(2,4,2,14);B=(2,4,5,14);C=(2,4,8,14)
def demand(condition,message):
    if not condition:raise ValueError(message)
def read_inputs(base):
    raw=(ROOT/'bounds.json').read_bytes()
    demand(hashlib.sha256(raw).hexdigest()==BOUNDS_SHA256,'pinned late280 bounds mismatch')
    source=base/'verify.py'
    demand(hashlib.sha256(source.read_bytes()).hexdigest()==BASE_VERIFY_SHA256,'pinned prior consumer mismatch')
    return json.loads(raw),runpy.run_path(str(source))
def verify(base):
    data,v=read_inputs(base);old=v['DATA'];domain=v['DOMAIN'];ceil=v['ceil_fraction']
    demand(data['scope']==dict(base_node=[2,4,1,8,1,2,1,0,13],xi7=[1,4,7,14],eta11=14,eta13=14,later_etas=list(ETAS),source_thresholds=[2,4,4,8,8,16],query=16),'fixed extension scope')
    demand(set(data['released'])=={'AB','AA','CA','CC','FA'},'all declared source-field pairs')
    maxima={}
    for name,table in data['released'].items():
        demand(set(table)=={'17','19','29'},'three later stages')
        maxima[name]=[]
        for q in (17,19,29):
            values=table[str(q)]
            demand(set(values)==set(map(str,ETAS)),'every allowed later eta')
            demand(all(F(x)>=0 for x in values.values()),'nonnegative loss bound')
            maxima[name].append(max(map(F,values.values())))
    ref17={int(e):F(x) for e,x in data['reference17_full13_released'].items()}
    demand(set(ref17)==set(ETAS),'full13 reference covers all late eta')
    demand(set(data['reference17_four'])=={'8','11'},'two exact residual eta refinements')
    for es,rows in data['reference17_four'].items():
        e=int(es);expected=set(product((1,2),range(1,5),(2,4,5,7,8),(e,)))
        demand(len(rows)==40 and {tuple(r['xi']) for r in rows}==expected,'refined complete four-head domain')
        ref17[e]=min(ref17[e],max(F(r['cost']) for r in rows))
    prior_max={int(q):max(v['load_table'](rows).values()) for q,rows in old['uniform_currents'].items()}
    ref17[14]=min(ref17[14],prior_max[17])
    # Ref17 uses full13. Ref19/29 retain both same-cell zero fields.
    ref=[max(ref17.values())]
    for q in (19,29):
        values={int(e):F(x) for e,x in data['released']['AB'][str(q)].items()}
        values[14]=min(values[14],prior_max[q]);ref.append(max(values.values()))
    l7=F(old['current7']);l11=v['load_table'](old['current11']);l13={k:v['load_table'](rows) for k,rows in old['current13'].items()}
    c13={tuple(r['xi']):F(r['cost']) for r in data['current13_C']}
    demand(len(data['current13_C'])==2 and set(c13)=={A,(2,3,2,14)},'exact two current13 refinements')
    ordinary,query=v['continuation'](True);charged,_=v['continuation'](False);h16=query[16]
    lift11=v['perturbation'](13,11);lift13=v['perturbation'](11,13)
    routes=[];counts=Counter()
    for x11,x13 in product(domain,repeat=2):
        mapped=v['swap'](x13) if x11==B else x13
        cost13=l13['B2'][mapped] if x11 in (A,B) else l13['flat'][x13]
        if x11==C:
            if x13 in (A,B):cost13=min(cost13,c13[A])
            elif x13 in ((2,3,2,14),(2,3,5,14)):cost13=min(cost13,c13[(2,3,2,14)])
        fixed=[l7,l11[x11],cost13]
        options=[('ordinary',fixed+(charged if x11 in (A,B) else ordinary))]
        for b11,b13 in ((A,B),(B,A)):
            change11=v['field'](x11)!=b11;change13=v['field'](x13)!=b13
            late=[min(ref[i]+(lift11[i] if change11 else 0)+(lift13[i] if change13 and i>0 else 0),ordinary[i]) for i in range(3)]
            options.append(('transfer',fixed+late))
        if x11==C and x13 in (A,B):options.append(('CA-direct',fixed+maxima['CA']))
        if (x11,x13) in ((A,A),(B,B)):options.append(('AA-direct',fixed+maxima['AA']))
        if v['field'](x11) is None and x13 in (A,B):options.append(('FA-direct',fixed+maxima['FA']))
        if x11==C and x13==C:options.append(('CC',list(map(F,old['CC']['losses'][:3]))+maxima['CC']))
        route,losses=min(options,key=lambda row:sum(row[1],F(0)))
        live=F(135,4)-sum(losses,F(0));slack=14*live-h16
        demand(live>0 and slack>0,'expanded-domain strict query16 inequality')
        micro=[int(ceil(x,10**6)*10**6) for x in losses]
        dmicro=33750000-sum(micro);smicro=14*dmicro-int(ceil(h16,10**6)*10**6)
        demand(smicro>0,'millionth-rounded expanded-domain inequality')
        upper=ceil(15+h16/live);counts[route]+=1
        routes.append(dict(xi11=list(x11),xi13=list(x13),route=route,losses=list(map(str,losses)),loss_micro=micro,live_lower=str(live),slack_lower=str(slack),live_lower_micro=dmicro,slack_lower_micro=smicro,query_upper=str(upper),query_upper_decimal=float(upper)))
    demand(len(routes)==1600,'complete ordered prefix-label domain')
    demand(dict(counts)=={'transfer':1521,'FA-direct':74,'AA-direct':2,'CA-direct':2,'CC':1},'complete disjoint route counts')
    worst=max(routes,key=lambda r:F(r['query_upper']))
    return dict(scope='Fixed A1 node and xi7=(1,4,7,14); xi11,xi13 each40 eta14 projections; xi17,xi19,xi29 each280 allowed projections. No other first-two eta, anchor, xi7 or full missing23 result.',source_thresholds=[2,4,4,8,8,16],query=16,covered_prefix_pairs=1600,later_choices_per_pair=280**3,total_parameter_tuples=1600*280**3,route_counts=dict(counts),reference_late_bounds=list(map(str,ref)),direct_late_bounds={k:list(map(str,z)) for k,z in maxima.items()},H16=str(h16),worst=worst,minimum_micro_slack=min(r['slack_lower_micro'] for r in routes),minimum_live_lower_micro=min(r['live_lower_micro'] for r in routes),bounds_sha256=BOUNDS_SHA256,base_verify_sha256=BASE_VERIFY_SHA256,verification='Exact rational arithmetic and exhaustive1600 route checks from pinned upper-bound inputs; integer maxima require the separate explicit geometry replay.',routes=routes)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--base',type=Path,default=ROOT.parent/'missing23-eta14');p.add_argument('--output',type=Path);args=p.parse_args()
    answer=verify(args.base)
    if args.output:args.output.write_text(json.dumps(answer,indent=2)+'\n')
    print(json.dumps({k:v for k,v in answer.items() if k!='routes'},indent=2))
