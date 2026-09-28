"""Scoped replay of the fixed-Q envelope and the 35+9 declared current tables."""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,json,runpy,subprocess
ROOT=Path(__file__).resolve().parent
BOUNDS_SHA256='0a910c1d2dfbf16ad6a5a65ca5d4b7640a835e432dfffce21648fcaed4645593'
BASE_REPLAY_SHA256='d0c5dbf54089cf05da07e562b34b639890fb722fbf9efb96bc8a5068c729ed9a'
def demand(test,message):
    if not test:raise ValueError(message)
def main():
    p=argparse.ArgumentParser();p.add_argument('--base',type=Path,default=ROOT.parent/'missing23-eta14');p.add_argument('--kind',choices=('current7','query','released','four'),required=True);p.add_argument('--prime',type=int,choices=(11,13,17,19,29));p.add_argument('--eta',type=int,choices=(1,4,7,8,11,13,14));p.add_argument('--cache',type=Path,action='append',default=[]);p.add_argument('--fresh',action='store_true');p.add_argument('--regenerate',action='store_true');p.add_argument('--binary',type=Path);p.add_argument('--output',type=Path);args=p.parse_args()
    raw=(ROOT/'bounds.json').read_bytes();demand(hashlib.sha256(raw).hexdigest()==BOUNDS_SHA256,'pinned Q inputs');data=json.loads(raw)
    if args.kind in ('released','four'):demand(args.prime is not None and args.eta is not None,'current stage and phase required')
    else:demand(args.prime is None and args.eta is None,'no unused stage or phase arguments')
    source=args.base/'geometry_replay.py';demand(hashlib.sha256(source.read_bytes()).hexdigest()==BASE_REPLAY_SHA256,'pinned base producer')
    d=runpy.run_path(str(source));g=d['current'].__globals__;g['xi7']=(2,4,2,14)
    root=ROOT/'geometry-cache';g['root']=root;g['cachefolders']=tuple(args.cache)+(root,args.base/'geometry-cache');g['ALLOW_GENERATE']=args.fresh or args.regenerate;g['REGENERATE']=args.regenerate;g['ENUMERATOR']=args.binary or ROOT/'geometry-enumerator'
    if g['ALLOW_GENERATE'] and not g['ENUMERATOR'].exists():subprocess.run(['c++','-O2','-std=c++17',str(args.base/'geometry.cpp'),'-o',str(g['ENUMERATOR'])],check=True)
    if args.kind=='current7':
        env=d['envelope']((0,0,0),None,None,1,7,1,g['xi7'],'prefix7');value=str(d['v']['up'](env[2][F(1)]/4));demand(value==data['current7'],'current7 bound matches')
    elif args.kind=='query':
        env=d['envelope']((1,0,0),None,None);value=dict(mass=str(env[0]),whole=str(env[1]),values={str(t):str(a) for t,a in env[2].items()});demand(value==data['zero_envelope'],'entire Q zero7 envelope matches')
    else:
        parts={(a,0,0):d['unit'] if a else d['pos7'] for a in (0,1)}
        for q,t in ((11,4),(13,4),(17,8),(19,8)):
            if q<args.prime:parts={k:d['mul'](dist,d['full'](q,t)) for k,dist in parts.items()}
        threshold={11:4,13:4,17:8,19:8,29:16}[args.prime]
        if args.kind=='released':
            expected=next(r['cost'] for r in data['released'] if (r['prime'],r['eta'])==(args.prime,args.eta))
            for i,m in ((0,3),(1,5),(2,9)):demand({x[i] for x in d['v']['PROJECTIONS'] if x[-1]==args.eta}=={x%m for x in d['cs']},'released category domain')
            cost,_=d['current'](parts,None,None,(1,4,7,args.eta),args.prime,threshold,'released');value=str(cost);demand(value==expected,'released current bound matches')
        else:
            record=next((r for r in data['four'] if (r['prime'],r['eta'])==(args.prime,args.eta)),None);demand(record is not None,'one of the nine declared tables')
            value=[]
            for xi in d['v']['PROJECTIONS']:
                if xi[-1]==args.eta:
                    cost,_=d['current'](parts,None,None,xi,args.prime,threshold,'four');value.append(dict(xi=list(xi),cost=str(cost)))
            demand(len(value)==40 and value==record['rows'],'all40 actual-label bounds match')
    result=dict(kind=args.kind,prime=args.prime,eta=args.eta,input_matched=True,value=value,new_batches=len(g['NEW']),new_queries=sum(r['queries'] for r in g['NEW'].values()),used_batches=len(g['USED']),used_queries=sum(g['USED'].values()));text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
