"""Replay all280 current7 inputs or the37 declared actual-zero7 envelopes.

Cache-only by default. This producer pins the complete original geometry
implementation and source. It does not enumerate future-label grids.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse, hashlib, json, runpy, subprocess

ROOT = Path(__file__).resolve().parent
BOUNDS_SHA256 = '5f506cd32264ae3c247c3055b2dd84004625d6fb7fa7aebec22fac2f365b7065'
BASE_REPLAY_SHA256 = 'd0c5dbf54089cf05da07e562b34b639890fb722fbf9efb96bc8a5068c729ed9a'

def demand(condition,message):
    if not condition:
        raise ValueError(message)

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--base',type=Path,default=ROOT.parent/'missing23-eta14')
    p.add_argument('--kind',choices=('current280','zero37'),required=True)
    p.add_argument('--projection',help='Optional single declared xi7 as four comma-separated integers')
    p.add_argument('--cache',type=Path,action='append',default=[])
    p.add_argument('--fresh',action='store_true')
    p.add_argument('--regenerate',action='store_true')
    p.add_argument('--binary',type=Path)
    p.add_argument('--output',type=Path)
    args=p.parse_args()
    raw=(ROOT/'bounds.json').read_bytes()
    demand(hashlib.sha256(raw).hexdigest()==BOUNDS_SHA256,'pinned ordinary inputs')
    data=json.loads(raw)
    source=args.base/'geometry_replay.py'
    demand(hashlib.sha256(source.read_bytes()).hexdigest()==BASE_REPLAY_SHA256,'pinned base producer')
    d=runpy.run_path(str(source));g=d['current'].__globals__
    root=ROOT/'geometry-cache'
    g['root']=root;g['cachefolders']=tuple(args.cache)+(root,args.base/'geometry-cache')
    g['ALLOW_GENERATE']=args.fresh or args.regenerate;g['REGENERATE']=args.regenerate
    g['ENUMERATOR']=args.binary or ROOT/'geometry-enumerator'
    if g['ALLOW_GENERATE'] and not g['ENUMERATOR'].exists():
        subprocess.run(['c++','-O2','-std=c++17',str(args.base/'geometry.cpp'),'-o',str(g['ENUMERATOR'])],check=True)
    rows=data['current7'] if args.kind=='current280' else data['actual_zero7']
    demand(len(rows)==(280 if args.kind=='current280' else 37),'declared complete replay target count')
    if args.projection:
        xi=tuple(map(int,args.projection.split(',')))
        rows=[r for r in rows if tuple(r['xi7'])==xi]
        demand(len(rows)==1,'one declared replay projection')
    for record in rows:
        xi=tuple(record['xi7'])
        g['xi7']=xi
        d['envelope'].cache_clear()
        if args.kind=='current280':
            env=d['envelope']((0,0,0),None,None,1,7,1,xi,'prefix7')
            value=str(d['v']['up'](env[2][F(1)]/4))
            demand(value==record['current7'],'actual current7 bound matches: '+str(xi))
        else:
            env=d['envelope']((1,0,0),None,None)
            value=dict(mass=str(env[0]),whole=str(env[1]),values={str(t):str(a) for t,a in env[2].items()})
            demand(value==record['zero_envelope'],'actual zero7 envelope matches: '+str(xi))
    result=dict(kind=args.kind,matched_targets=len(rows),new_batches=len(g['NEW']),new_queries=sum(r['queries'] for r in g['NEW'].values()),used_batches=len(g['USED']),used_queries=sum(g['USED'].values()),bounds_sha256=BOUNDS_SHA256)
    text=json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text,end='')

if __name__=='__main__':
    main()
