"""Explicit current7 or positive-difference envelope reconstruction for two xi7 pilots."""
from pathlib import Path
import argparse,hashlib,json,runpy,subprocess
ROOT=Path(__file__).resolve().parent
BASE_REPLAY_SHA256='d0c5dbf54089cf05da07e562b34b639890fb722fbf9efb96bc8a5068c729ed9a'
BOUNDS_SHA256='24eb182b3d3d3a20e95921a66f875dced7c3a659968bda9cd42503a379144944'
def demand(test,message):
    if not test:raise ValueError(message)
def main():
    p=argparse.ArgumentParser();p.add_argument('--base',type=Path,default=ROOT.parent/'missing23-eta14');p.add_argument('--projection',required=True);p.add_argument('--kind',choices=('current7','difference'),required=True)
    p.add_argument('--cache',type=Path,action='append',default=[]);p.add_argument('--fresh',action='store_true');p.add_argument('--regenerate',action='store_true');p.add_argument('--binary',type=Path);p.add_argument('--output',type=Path);args=p.parse_args()
    raw=(ROOT/'bounds.json').read_bytes();demand(hashlib.sha256(raw).hexdigest()==BOUNDS_SHA256,'fixed transport inputs');data=json.loads(raw);xi=tuple(map(int,args.projection.split(',')))
    records={tuple(r['xi7']):r for r in data['pilots']};demand(xi in records,'one of the two declared pilot projections');record=records[xi]
    source=args.base/'geometry_replay.py';demand(hashlib.sha256(source.read_bytes()).hexdigest()==BASE_REPLAY_SHA256,'prior geometry producer pin')
    d=runpy.run_path(str(source));g=d['current'].__globals__;root=ROOT/'geometry-cache'
    g['root']=root;g['cachefolders']=tuple(args.cache)+(root,args.base/'geometry-cache');g['ALLOW_GENERATE']=args.fresh or args.regenerate;g['REGENERATE']=args.regenerate;g['ENUMERATOR']=args.binary or ROOT/'geometry-enumerator'
    if g['ALLOW_GENERATE'] and not g['ENUMERATOR'].exists():subprocess.run(['c++','-O2','-std=c++17',str(args.base/'geometry.cpp'),'-o',str(g['ENUMERATOR'])],check=True)
    if args.kind=='current7':
        env=d['envelope']((0,0,0),None,None,1,7,1,xi,'prefix7');value=str(d['v']['up'](env[2][d['F'](1)]/4));demand(value==record['current7'],'current7 reconstruction mismatch')
    else:
        cs=d['cs'];K=(11,11,9,6,3);old=tuple(K[s] for s in d['v']['counts'](cs,(1,4,7,14)));new=tuple(K[s] for s in d['v']['counts'](cs,xi));delta=tuple(max(a-b,0) for a,b in zip(new,old))
        demand(record['positive_difference_numerators']=={str(x):z for x,z in zip(cs,delta) if z},'same-cell positive difference')
        old_cell=g['cell_weights']
        def delta_cell_weights(reg,part,x11,x13):
            demand(part==(0,0,0),'difference envelope has no extra source factors')
            return tuple(a*b for a,b in zip(old_cell(reg,part,x11,x13),delta))
        g['cell_weights']=delta_cell_weights;d['envelope'].cache_clear();env=d['envelope']((0,0,0),None,None)
        value=dict(mass=str(env[0]),whole=str(env[1]),values={str(t):str(a) for t,a in env[2].items()});demand(value==record['delta_envelope'],'difference-envelope reconstruction mismatch')
    result=dict(xi7=xi,kind=args.kind,input_matched=True,value=value,new_batches=len(g['NEW']),new_queries=sum(r['queries'] for r in g['NEW'].values()),used_batches=len(g['USED']),used_queries=sum(g['USED'].values()))
    text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
