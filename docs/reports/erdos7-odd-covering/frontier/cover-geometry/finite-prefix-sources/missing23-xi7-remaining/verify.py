"""Exact arithmetic for 22 declared first labels at the fixed missing23 A1 node."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
import argparse,hashlib,json,runpy
ROOT=Path(__file__).resolve().parent
BOUNDS_SHA256='a5209491bd8146f5630a1ad8e70f6120497c19ed479d44a0a372ec24782c023a'
BASE_VERIFY_SHA256='a519fef29bb1fb76370ea1ca4d252365205093448d53b4442fd445d80e30018f'
ETAS=(1,4,7,8,11,13,14);DOMAIN=tuple(product((1,2),range(1,5),(2,4,5,7,8),ETAS));K7=(11,11,9,6,3)
def demand(test,message):
    if not test:raise ValueError(message)
def load_data():
    raw=(ROOT/'bounds.json').read_bytes();demand(hashlib.sha256(raw).hexdigest()==BOUNDS_SHA256,'pinned remaining-source inputs');return json.loads(raw)
def envelope(r):
    e=F(r['mass']),F(r['whole']),{F(t):F(x) for t,x in r['values'].items()}
    demand(set(e[2])==set(map(F,range(1,29))) and e[0]>0 and all(a>=0 for a in e[2].values()),'complete nonnegative envelope');return e
def table(rows,eta):
    t={tuple(r['xi']):F(r['cost']) for r in rows};demand(len(rows)==40 and set(t)=={x for x in DOMAIN if x[-1]==eta} and all(v>=0 for v in t.values()),'all40 actual labels');return t
def swap(a):return a[:2]+({2:5,5:2}.get(a[2],a[2]),)+a[3:]
def verify(base):
    data=load_data();demand(data['model']==dict(node=[2,4,1,8,1,2,1,0,13],core=[3,5,7,11,13,17,19,29],thresholds=[2,4,4,8,8,16],query=16,source_count=22,comparison_groups=16),'declared fixed A1 scope')
    p=base/'verify.py';demand(hashlib.sha256(p.read_bytes()).hexdigest()==BASE_VERIFY_SHA256,'pinned base arithmetic');v=runpy.run_path(str(p));ceil=v['ceil_fraction'];cells=v['CELLS'];crt={(x%27,x%5):x for x in range(135)}
    def perm(x):
        z=x%27;z+=3 if z%9==2 else -3 if z%9==5 else 0
        return crt[z,x%5]
    def field(a):return {x:K7[sum(x%m==r for m,r in zip((3,5,9,15),a))] for x in cells}
    demand(sorted(perm(x) for x in range(135))==list(range(135)) and {perm(x) for x in cells}==set(cells),'carrier transport')
    for m in (3,9,27,5,15,45,135):
        images=[{perm(x)%m for x in range(135) if x%m==r} for r in range(m)];demand(all(len(s)==1 for s in images) and len({next(iter(s)) for s in images})==m,'named partition transport')
    for r in product((False,True),repeat=2):
        ws={x:(1 if r[0] else 4-3*(x%27==13))*(1 if r[1] else 16-5*(x%5==1)-4*(x%3==2 and x%5==1)) for x in cells};demand(all(ws[x]==ws[perm(x)] for x in cells),'source region weight transport')
    for a in DOMAIN:demand(swap(a) in DOMAIN and all((x%m==r)==(perm(x)%m==s) for x in range(135) for m,r,s in zip((3,5,9,15),a,swap(a))),'all future labels transported jointly')
    full=v['UNIT']
    for q,t in ((11,4),(13,4),(17,8),(19,8),(29,16)):full=v['mul'](full,v['full'](q,t))
    positive_h=v['hinge'](16,v['mul'](v['POS7'],full),v['ENVS'][(0,0,0)])
    pos13=({m:F(18,13**m) for m in range(2,20)},F(25,104),F(3,26));parts={k:v['mul'](v['mul'](v['UNIT'] if k[0] else v['POS7'],v['UNIT'] if k[1] else v['POS11']),v['UNIT'] if k[2] else pos13) for k in product((0,1),repeat=3)}
    for q,t in ((17,8),(19,8),(29,16)):parts={k:v['mul'](dist,v['full'](q,t)) for k,dist in parts.items()}
    def query_joint(record):
        es={tuple(map(int,k.split(','))):envelope(e) for k,e in record['ordinary_envelopes'].items()};demand(set(es)==set(parts),'eight actual7/11/13 envelopes')
        return sum((v['hinge'](16,dist,es[k])/F(14**k[0]*33**k[1]*26**k[2]) for k,dist in parts.items()),F(0))
    members_seen=set();group_ids=set();summaries=[];total_pairs=0
    for group in data['groups']:
        gid=group['index'];rep=tuple(group['representative']);demand(gid not in group_ids and rep in DOMAIN,'distinct declared comparison group');group_ids.add(gid);rf=field(rep)
        for member in group['members']:
            a=tuple(member['xi7']);demand(a in DOMAIN and a not in members_seen and F(member['current7'])>=0,'distinct physical source with its own prefix bound');members_seen.add(a);f=field(a)
            if member['field_transport']=='identity':demand(f==rf,'identical K7 comparison input, not source identity')
            else:demand(member['field_transport']=='swap2_5' and all(f[perm(x)]==rf[x] for x in cells),'whole-coordinate comparison transport')
        h=positive_h+v['hinge'](16,full,envelope(group['zero_envelope']))/14
        released={(r['prime'],r['eta']):F(r['cost']) for r in group['released']};demand(len(group['released'])==35 and set(released)==set(product((11,13,17,19,29),ETAS)) and all(z>=0 for z in released.values()),'35 released currents')
        tab={q:{a:released[q,a[-1]] for a in DOMAIN} for q in (11,13)};seen=set()
        for record in group['four']:
            q,eta=record['prime'],record['eta'];demand(q in tab and eta in ETAS and (q,eta) not in seen,'unique refined current phase');seen.add((q,eta))
            for a,c in table(record['rows'],eta).items():tab[q][a]=min(tab[q][a],c)
        late=[max(released[q,eta] for eta in ETAS) for q in (17,19,29)];actual={};joint={}
        if group['actual13'] or group['joint']:demand(all(rf[x]==rf[perm(x)] for x in cells),'comparison source invariant for anchor mirror transport')
        for record in group['actual13']:
            a,b=tuple(record['xi11']),tuple(record['xi13']);cost=F(record['cost']);demand(a in DOMAIN and b in DOMAIN and cost>=0,'actual current13 anchor')
            for key in ((a,b),(swap(a),swap(b))):demand(key not in actual or actual[key]==cost,'consistent current13 mirror');actual[key]=cost
        for record in group['joint']:
            a,b=tuple(record['xi11']),tuple(record['xi13']);demand(a in DOMAIN and b in DOMAIN,'actual7/11/13 anchor')
            phase={(r['prime'],r['eta']):F(r['cost']) for r in record['rows']};demand(len(record['rows'])==21 and set(phase)==set(product((17,19,29),ETAS)) and all(z>=0 for z in phase.values()),'all21 actual joint later currents')
            seen_joint=set()
            for t in record['four']:
                q,eta=t['prime'],t['eta'];demand((q,eta) in phase and (q,eta) not in seen_joint,'unique joint full40 phase');seen_joint.add((q,eta));phase[q,eta]=min(phase[q,eta],max(table(t['rows'],eta).values()))
            jloss=[F(record['current13']),*[max(phase[q,eta] for eta in ETAS) for q in (17,19,29)]];jh=query_joint(record)
            for key in ((a,b),(swap(a),swap(b))):demand(key not in joint or joint[key]==(jloss,jh),'consistent joint mirror');joint[key]=jloss,jh
        rows=[]
        for member in group['members']:
            l7=F(member['current7']);uniform=[l7,max(tab[11].values()),max(tab[13].values()),*late];d0=F(135,4)-sum(uniform,F(0));s0=14*d0-h;routes={};worst=None;minimum_micro=None;minimum_live_micro=None
            cases=((None,None),) if s0>0 else product(DOMAIN,repeat=2)
            for a,b in cases:
                losses=uniform if a is None else [l7,tab[11][a],tab[13][b],*late];hh=h;route='uniform' if a is None else 'ordinary'
                live=F(135,4)-sum(losses,F(0));slack=14*live-hh
                if slack<=0 and (a,b) in actual:
                    losses=[l7,tab[11][a],min(tab[13][b],actual[a,b]),*late];route='actual13';live=F(135,4)-sum(losses,F(0));slack=14*live-hh
                if slack<=0 and (a,b) in joint:
                    jloss,hh=joint[a,b];losses=[l7,tab[11][a],*jloss];route='joint';live=F(135,4)-sum(losses,F(0));slack=14*live-hh
                demand(live>0 and slack>0,'unclosed source/pair '+str((member['xi7'],a,b)))
                upper=15+hh/live
                if worst is None or upper>worst[0]:worst=upper,a,b,live,slack,route
                dmicro=33750000-sum(int(ceil(z,10**6)*10**6) for z in losses);smicro=14*dmicro-int(ceil(hh,10**6)*10**6);demand(dmicro>0 and smicro>0,'millionth strict rounding')
                minimum_micro=smicro if minimum_micro is None else min(minimum_micro,smicro);minimum_live_micro=dmicro if minimum_live_micro is None else min(minimum_live_micro,dmicro);routes[route]=routes.get(route,0)+(280**2 if a is None else 1)
            demand(sum(routes.values())==280**2,'complete prefix pair routing');total_pairs+=280**2
            rows.append(dict(xi7=member['xi7'],current7=member['current7'],field_transport=member['field_transport'],routes=routes,worst_pair=None if worst[1] is None else [list(worst[1]),list(worst[2])],worst_query_upper=str(ceil(worst[0])),worst_query_decimal=float(ceil(worst[0])),worst_route=worst[5],minimum_live_lower_micro=minimum_live_micro,minimum_slack_lower_micro=minimum_micro,future_parameter_tuples=280**5))
        summaries.append(dict(index=gid,representative=list(rep),common_unconditioned_H16=str(h),full40_tables=len(group['four']),actual13_anchors=len(group['actual13']),joint_anchors=len(group['joint']),joint_full40_tables=sum(len(r['four']) for r in group['joint']),members=rows))
    demand(group_ids==set(range(16)) and len(members_seen)==22 and total_pairs==22*280**2,'exact declared source domain')
    allrows=[r for g in summaries for r in g['members']]
    return dict(scope='22 specified xi7 at one fixed missing23 A1 node; comparison-input reuse or proved coordinate transport, with each prefix loss kept separately. Every source covers all280^5 future labels. No Lean verification.',source_count=22,comparison_groups=16,future_parameter_tuples_per_source=280**5,total_future_parameter_tuples=22*280**5,prefix_pairs_covered=total_pairs,worst_query_upper=str(max(F(r['worst_query_upper']) for r in allrows)),minimum_slack_lower_micro=min(r['minimum_slack_lower_micro'] for r in allrows),groups=summaries,bounds_sha256=BOUNDS_SHA256,verification='Exact rational routing and full source/label transport checks. Declared numeric geometry inputs are separately replayable; their hashes are not substituted for geometric reconstruction.')
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--base',type=Path,default=ROOT.parent/'missing23-eta14');p.add_argument('--output',type=Path);args=p.parse_args();result=verify(args.base);text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')
