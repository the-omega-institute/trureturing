"""Exact fixed-Q arithmetic, one pointwise analytic credit, and whole-source transport."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
import argparse,hashlib,json,runpy
ROOT=Path(__file__).resolve().parent
BOUNDS_SHA256='0a910c1d2dfbf16ad6a5a65ca5d4b7640a835e432dfffce21648fcaed4645593'
BASE_VERIFY_SHA256='a519fef29bb1fb76370ea1ca4d252365205093448d53b4442fd445d80e30018f'
ETAS=(1,4,7,8,11,13,14);Q=(2,4,2,14);QP=(2,4,5,14);X=(1,4,7,4)
FOUR={11:(4,7,8,13),13:(4,7,8,13,14)}
def demand(test,message):
    if not test:raise ValueError(message)
def weights(cells,region):
    # Pinned source_model.weights specialized to the stated A1 node.
    return tuple((1 if region[0] else 4-3*(x%27==13))*(1 if region[1] else 16-4*(x%5==1)-(x%5==1)-4*(x%3==2 and x%5==1)) for x in cells)
def verify(base):
    raw=(ROOT/'bounds.json').read_bytes();demand(hashlib.sha256(raw).hexdigest()==BOUNDS_SHA256,'pinned Q inputs');data=json.loads(raw)
    demand(data['model']==dict(core=[3,5,7,11,13,17,19,29],node=[2,4,1,8,1,2,1,0,13],xi7=list(Q),transported_xi7=list(QP),thresholds=[2,4,4,8,8,16],query=16),'one fixed Q source')
    path=base/'verify.py';demand(hashlib.sha256(path.read_bytes()).hexdigest()==BASE_VERIFY_SHA256,'pinned base arithmetic');v=runpy.run_path(str(path));ceil=v['ceil_fraction'];cells=v['CELLS']
    e=data['zero_envelope'];env=F(e['mass']),F(e['whole']),{F(t):F(a) for t,a in e['values'].items()}
    demand(set(env[2])==set(map(F,range(1,29))) and env[0]>0 and env[1]>0 and all(a>=0 for a in env[2].values()),'complete Q zero7 envelope')
    dist=v['UNIT']
    for p,t in ((11,4),(13,4),(17,8),(19,8),(29,16)):dist=v['mul'](dist,v['full'](p,t))
    h=v['hinge'](16,v['mul'](v['POS7'],dist),v['ENVS'][(0,0,0)])+v['hinge'](16,dist,env)/14
    l7=F(data['current7']);domain=tuple(product((1,2),range(1,5),(2,4,5,7,8),ETAS))
    released={(r['prime'],r['eta']):F(r['cost']) for r in data['released']}
    demand(len(data['released'])==35 and set(released)==set(product((11,13,17,19,29),ETAS)) and all(a>=0 for a in released.values()),'all35 released stage-phase inputs')
    four={}
    for record in data['four']:
        p,eta=record['prime'],record['eta'];key=p,eta
        demand(key not in four and p in FOUR and eta in FOUR[p],'one declared full40 table')
        rows={tuple(r['xi']):F(r['cost']) for r in record['rows']}
        demand(len(record['rows'])==40 and set(rows)=={x for x in domain if x[-1]==eta} and all(a>=0 for a in rows.values()),'all40 distinct physical labels')
        four[key]=rows
    demand(set(four)=={(p,eta) for p,etas in FOUR.items() for eta in etas},'exact nine refined phase tables')
    tables={p:{x:four[p,x[-1]][x] if (p,x[-1]) in four else released[p,x[-1]] for x in domain} for p in (11,13)}
    peaks={}
    for p in (11,13):
        ranking=sorted(four[p,4].items(),key=lambda z:z[1],reverse=True)
        demand(ranking[0][0]==X and ranking[0][1]>ranking[1][1],'unique eta4 peak at X')
        peaks[str(p)]=dict(maximum=str(ranking[0][1]),runner_up=list(ranking[1][0]),runner_up_value=str(ranking[1][1]),strict_gap=str(ranking[0][1]-ranking[1][1]))
    # Exact parameters of the analytic inequality proved in README.md.
    intersection=tuple(x for x in cells if all(x%m==a for m,a in zip((3,5,9,15),X)))
    demand(intersection==(34,79,124),'the actual X four-way support')
    for x in intersection:
        integrated=sum((F(weights(cells,r)[cells.index(x)],(1 if r[0] else 6)*(1 if r[1] else 20))*F(1,3 if r[0] else 1)*F(1,5 if r[1] else 1) for r in product((False,True),repeat=2)),F(0))
        demand(integrated==1 and sum(x%m==a for m,a in zip((3,5,9,15),Q))==1,'unit source cell mass and Q overlap one')
    zero11_gap=F(28-25,33);charged7_mass=F(11,14)+v['POS7'][2];hinge_lower=1+F(12*4,13)-4
    credit=len(intersection)*zero11_gap*charged7_mass*hinge_lower/8
    demand(credit==F(27,1144),'uniform per-layout current13 credit')
    late=[max(released[p,eta] for eta in ETAS) for p in (17,19,29)]
    before=[];worst=None;minmicro=None;minlive=None;count=0
    for a,b in product(domain,repeat=2):
        losses=[l7,tables[11][a],tables[13][b],*late]
        if 14*(F(135,4)-sum(losses,F(0)))<=h:before.append((a,b))
        if a==b==X:losses[2]-=credit
        live=F(135,4)-sum(losses,F(0));slack=14*live-h
        demand(live>0 and slack>0,'all-prefix strict query16 certificate')
        upper=15+h/live
        if worst is None or upper>worst[0]:worst=(upper,a,b,live,slack)
        rounded=[int(ceil(z,10**6)*10**6) for z in losses];dmicro=33750000-sum(rounded);smicro=14*dmicro-int(ceil(h,10**6)*10**6)
        demand(dmicro>0 and smicro>0,'millionth rounding preserves positivity')
        minmicro=smicro if minmicro is None else min(minmicro,smicro);minlive=dmicro if minlive is None else min(minlive,dmicro);count+=1
    demand(before==[(X,X)] and count==280**2,'exactly one pair needs the analytic credit')
    # A whole-source transport, never an identification of labels inside Q.
    crt={(x%27,x%5):x for x in range(135)}
    def perm(x):
        z=x%27;z+=3 if z%9==2 else -3 if z%9==5 else 0
        return crt[z,x%5]
    def swap(x):return x[:2]+({2:5,5:2}.get(x[2],x[2]),)+x[3:]
    demand(sorted(perm(x) for x in range(135))==list(range(135)) and {perm(x) for x in cells}==set(cells),'whole-carrier permutation')
    for m in (3,9,27,5,15,45,135):
        images=[{perm(x)%m for x in range(135) if x%m==r} for r in range(m)]
        demand(all(len(s)==1 for s in images) and len({next(iter(s)) for s in images})==m,'named source partition transport')
    for reg in product((False,True),repeat=2):
        ws=dict(zip(cells,weights(cells,reg)));demand(all(ws[x]==ws[perm(x)] for x in cells),'all four source weight fields preserved')
    for xi in domain:
        demand(swap(xi) in domain and all((x%m==a)==(perm(x)%m==b) for x in range(135) for m,a,b in zip((3,5,9,15),xi,swap(xi))),'all future labels transported together')
    demand(swap(Q)==QP and Q!=QP,'transport connects two distinct sources')
    return dict(scope='Fixed A1 node. Actual Q K7 field, complete 280^5 future domain, plus a whole-source transport to Q-prime; no within-Q symmetry and no Lean verification.',xi7=list(Q),transported_xi7=list(QP),current7=str(l7),H16=str(h),prefix_pairs=count,late_choices_per_prefix=280**3,future_parameter_tuples_per_source=280**5,certified_sources=2,refined_phases={str(p):list(etas) for p,etas in FOUR.items()},released_inputs=35,full40_tables=9,eta4_peaks=peaks,analytic_credit=str(credit),pairs_requiring_credit=1,late_loss_upper=list(map(str,late)),worst_pair=[list(worst[1]),list(worst[2])],worst_query_upper=str(ceil(worst[0])),worst_query_decimal=float(ceil(worst[0])),minimum_live_lower=str(worst[3]),minimum_slack_lower=str(worst[4]),minimum_live_lower_micro=minlive,minimum_slack_lower_micro=minmicro,bounds_sha256=BOUNDS_SHA256,verification='Exact rational combination of pinned bounds, arithmetic checks of the pointwise credit parameters, and finite source/label transport. Integer geometry has a separate replay; the uniform credit proof is in README.md.')
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--base',type=Path,default=ROOT.parent/'missing23-eta14');p.add_argument('--output',type=Path);args=p.parse_args();result=verify(args.base);text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')
