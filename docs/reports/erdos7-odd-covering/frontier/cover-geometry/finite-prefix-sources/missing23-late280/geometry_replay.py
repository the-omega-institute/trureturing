"""Explicit targeted geometry rebuild for the fixed-node late280 extension.

Imports the byte-pinned prior producer. Default only looks up full-input keys.
--fresh enables missing geometry generation; --regenerate reruns existing keys.
"""
from pathlib import Path
from itertools import product
import argparse,hashlib,json,runpy,subprocess
ROOT=Path(__file__).resolve().parent
BASE_REPLAY_SHA256='d0c5dbf54089cf05da07e562b34b639890fb722fbf9efb96bc8a5068c729ed9a'
ETAS=(1,4,7,8,11,13,14)
A=(2,4,2,14);B=(2,4,5,14);C=(2,4,8,14)
PAIRS={'AB':(A,B),'CC':(C,C),'CA':(C,A),'AA':(A,A),'FA':((2,3,2,14),A)}
def demand(test,message):
    if not test:raise ValueError(message)
def main():
    p=argparse.ArgumentParser()
    p.add_argument('--base',type=Path,default=ROOT.parent/'missing23-eta14')
    p.add_argument('--task',choices=('released','full13-released','full13-four','current13-C'),required=True)
    p.add_argument('--pair',choices=tuple(PAIRS),default='AB')
    p.add_argument('--stage',type=int,choices=(17,19,29),default=17)
    p.add_argument('--eta',type=int,choices=ETAS,default=14)
    p.add_argument('--projection',choices=('2,4,2,14','2,3,2,14'),default='2,4,2,14')
    p.add_argument('--cache',type=Path,action='append',default=[])
    p.add_argument('--fresh',action='store_true');p.add_argument('--regenerate',action='store_true')
    p.add_argument('--binary',type=Path);p.add_argument('--output',type=Path)
    args=p.parse_args();source=args.base/'geometry_replay.py'
    demand(hashlib.sha256(source.read_bytes()).hexdigest()==BASE_REPLAY_SHA256,'pinned prior geometry producer mismatch')
    d=runpy.run_path(str(source));g=d['current'].__globals__
    cache=ROOT/'geometry-cache';g['root']=cache
    g['cachefolders']=tuple(args.cache)+(cache,args.base/'geometry-cache')
    g['ALLOW_GENERATE']=args.fresh or args.regenerate;g['REGENERATE']=args.regenerate
    g['ENUMERATOR']=args.binary or ROOT/'geometry-enumerator'
    if g['ALLOW_GENERATE'] and not g['ENUMERATOR'].exists():
        subprocess.run(['c++','-O2','-std=c++17',str(args.base/'geometry.cpp'),'-o',str(g['ENUMERATOR'])],check=True)
    x11,x13=PAIRS[args.pair];stage=args.stage;threshold={17:8,19:8,29:16}[stage];mode='released'
    if args.task=='current13-C':
        demand(args.pair=='AB' and args.stage==17,'current13-C ignores no nondefault pair/stage')
        x11=C;x13=tuple(map(int,args.projection.split(',')));stage=13;threshold=4;mode='four'
        parts={(a,b,0):d['mul'](d['unit'] if a else d['pos7'],d['unit'] if b else d['pos11']) for a,b in product((0,1),repeat=2)}
        projections=(x13,)
    elif args.task.startswith('full13-'):
        demand(args.pair=='AB' and stage==17,'full13 reference is only AB current17')
        parts={(a,b,0):d['mul'](d['mul'](d['unit'] if a else d['pos7'],d['unit'] if b else d['pos11']),d['full'](13,4)) for a,b in product((0,1),repeat=2)}
        if args.task=='full13-four':
            demand(args.eta in (8,11),'only the two retained four-head refinements')
            mode='four';projections=tuple(x for x in d['v']['PROJECTIONS'] if x[-1]==args.eta)
        else:projections=((1,4,7,args.eta),)
    else:
        parts=d['initial_parts']()
        for q,t in ((17,8),(19,8)):
            if q<stage:parts={k:d['mul'](dist,d['full'](q,t)) for k,dist in parts.items()}
        projections=((1,4,7,args.eta),)
    if mode=='released':
        for i,m in ((0,3),(1,5),(2,9)):
            demand({x[i] for x in d['v']['PROJECTIONS'] if x[-1]==args.eta}=={x%m for x in d['cs']},'full contributing residue domain')
    rows=[]
    for projection in projections:
        cost,_=d['current'](parts,x11,x13,projection,stage,threshold,mode)
        rows.append(dict(xi=list(projection),cost=str(cost)))
    result=dict(task=args.task,pair=args.pair,stage=stage,eta=args.eta,xi11=list(x11),xi13=list(x13),rows=rows,new_batches=len(g['NEW']),new_queries=sum(x['queries'] for x in g['NEW'].values()),used_batches=len(g['USED']),used_queries=sum(g['USED'].values()))
    text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
