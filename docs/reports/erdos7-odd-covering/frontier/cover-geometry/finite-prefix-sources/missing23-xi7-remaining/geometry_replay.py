"""Explicit replay of the declared remaining-source comparison inputs."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
import argparse,hashlib,json,runpy,subprocess
ROOT=Path(__file__).resolve().parent
BOUNDS_SHA256='a5209491bd8146f5630a1ad8e70f6120497c19ed479d44a0a372ec24782c023a'
BASE_REPLAY_SHA256='d0c5dbf54089cf05da07e562b34b639890fb722fbf9efb96bc8a5068c729ed9a'
def demand(test,message):
    if not test:raise ValueError(message)
def pack(e):return dict(mass=str(e[0]),whole=str(e[1]),values={str(t):str(v) for t,v in e[2].items()})
def main():
    p=argparse.ArgumentParser();p.add_argument('--base',type=Path,default=ROOT.parent/'missing23-eta14');p.add_argument('--group',type=int,required=True);p.add_argument('--kind',choices=('current7','query','released','four','actual13','joint','joint-four'),required=True);p.add_argument('--source');p.add_argument('--prime',type=int,choices=(11,13,17,19,29));p.add_argument('--eta',type=int,choices=(1,4,7,8,11,13,14));p.add_argument('--a',type=int,choices=(2,5,8));p.add_argument('--b',type=int,choices=(2,5,8));p.add_argument('--cache',type=Path,action='append',default=[]);p.add_argument('--fresh',action='store_true');p.add_argument('--regenerate',action='store_true');p.add_argument('--binary',type=Path);p.add_argument('--output',type=Path);args=p.parse_args()
    raw=(ROOT/'bounds.json').read_bytes();demand(hashlib.sha256(raw).hexdigest()==BOUNDS_SHA256,'pinned remaining-source inputs');data=json.loads(raw);group=next((g for g in data['groups'] if g['index']==args.group),None);demand(group is not None,'declared comparison group')
    source=args.base/'geometry_replay.py';demand(hashlib.sha256(source.read_bytes()).hexdigest()==BASE_REPLAY_SHA256,'pinned base producer');d=runpy.run_path(str(source));g=d['current'].__globals__;g['xi7']=tuple(group['representative']);root=ROOT/'geometry-cache'
    g['root']=root;g['cachefolders']=tuple(args.cache)+(root,args.base/'geometry-cache');g['ALLOW_GENERATE']=args.fresh or args.regenerate;g['REGENERATE']=args.regenerate;g['ENUMERATOR']=args.binary or ROOT/'geometry-enumerator'
    if g['ALLOW_GENERATE'] and not g['ENUMERATOR'].exists():subprocess.run(['c++','-O2','-std=c++17',str(args.base/'geometry.cpp'),'-o',str(g['ENUMERATOR'])],check=True)
    if args.kind=='current7':
        demand(args.source is not None,'explicit first label');xi=tuple(map(int,args.source.split(',')));record=next((r for r in group['members'] if tuple(r['xi7'])==xi),None);demand(record is not None,'declared member source')
        env=d['envelope']((0,0,0),None,None,1,7,1,xi,'prefix7');value=str(d['v']['up'](env[2][F(1)]/4));demand(value==record['current7'],'member current7 matches')
    elif args.kind=='query':
        value=pack(d['envelope']((1,0,0),None,None));demand(value==group['zero_envelope'],'complete representative zero7 envelope matches')
    elif args.kind in ('released','four'):
        parts={(a,0,0):d['unit'] if a else d['pos7'] for a in (0,1)};rows=[]
        if args.kind=='four':
            record=next((r for r in group['four'] if (r['prime'],r['eta'])==(args.prime,args.eta)),None);demand(record is not None,'declared full40 table')
        for q,t in ((11,4),(13,4),(17,8),(19,8),(29,16)):
            if args.kind=='released':
                for eta in (1,4,7,8,11,13,14):
                    for i,m in ((0,3),(1,5),(2,9)):demand({x[i] for x in d['v']['PROJECTIONS'] if x[-1]==eta}=={x%m for x in d['cs']},'released domain')
                    cost,_=d['current'](parts,None,None,(1,4,7,eta),q,t,'released');rows.append(dict(prime=q,eta=eta,cost=str(cost)))
            elif q==args.prime:
                for xi in d['v']['PROJECTIONS']:
                    if xi[-1]==args.eta:
                        cost,_=d['current'](parts,None,None,xi,q,t,'four');rows.append(dict(xi=list(xi),cost=str(cost)))
                break
            parts={k:d['mul'](dist,d['full'](q,t)) for k,dist in parts.items()}
        value=rows;demand(value==(group['released'] if args.kind=='released' else record['rows']),'all declared current bounds match')
    else:
        demand(args.a is not None and args.b is not None,'actual11/13 anchors required');a=(2,4,args.a,14);b=(2,4,args.b,14)
        records=group['actual13'] if args.kind=='actual13' else group['joint'];record=next((r for r in records if tuple(r['xi11'])==a and tuple(r['xi13'])==b),None);demand(record is not None,'declared actual11/13 anchor')
        if args.kind=='actual13':
            parts={(i,j,0):d['mul'](d['unit'] if i else d['pos7'],d['unit'] if j else d['pos11']) for i,j in product((0,1),repeat=2)};cost,_=d['current'](parts,a,None,b,13,4,'four');value=str(cost);demand(value==record['cost'],'actual13 matches')
        elif args.kind=='joint-four':
            table=next((r for r in record['four'] if (r['prime'],r['eta'])==(args.prime,args.eta)),None);demand(table is not None,'declared joint full40 table');parts=d['initial_parts']()
            for q,t in ((17,8),(19,8)):
                if q<args.prime:parts={k:d['mul'](dist,d['full'](q,t)) for k,dist in parts.items()}
            rows=[];t={17:8,19:8,29:16}[args.prime]
            for xi in d['v']['PROJECTIONS']:
                if xi[-1]==args.eta:
                    cost,_=d['current'](parts,a,b,xi,args.prime,t,'four');rows.append(dict(xi=list(xi),cost=str(cost)))
            value=rows;demand(len(value)==40 and value==table['rows'],'all40 actual joint current bounds match')
        else:
            parts=d['initial_parts']();rows=[]
            for q,t in ((17,8),(19,8),(29,16)):
                for eta in (1,4,7,8,11,13,14):
                    cost,_=d['current'](parts,a,b,(1,4,7,eta),q,t,'released');rows.append(dict(prime=q,eta=eta,cost=str(cost)))
                parts={k:d['mul'](dist,d['full'](q,t)) for k,dist in parts.items()}
            envs={','.join(map(str,k)):pack(d['envelope'](k,a,b)) for k in parts};prior={(i,j,0):d['mul'](d['unit'] if i else d['pos7'],d['unit'] if j else d['pos11']) for i,j in product((0,1),repeat=2)};cost,_=d['current'](prior,a,None,b,13,4,'four');value=dict(rows=rows,ordinary_envelopes=envs,current13=str(cost));demand(all(value[k]==record[k] for k in value),'all21 joint currents, eight envelopes and actual13 match')
    result=dict(group=args.group,kind=args.kind,prime=args.prime,eta=args.eta,a=args.a,b=args.b,input_matched=True,value=value,new_batches=len(g['NEW']),new_queries=sum(r['queries'] for r in g['NEW'].values()),used_batches=len(g['USED']),used_queries=sum(g['USED'].values()));text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
