"""Targeted reconstruction:192 flat11-current13 representatives and21 FF bounds."""
from pathlib import Path
from itertools import product
import argparse,hashlib,json,runpy,subprocess
ROOT=Path(__file__).resolve().parent
BASE_REPLAY_SHA256='d0c5dbf54089cf05da07e562b34b639890fb722fbf9efb96bc8a5068c729ed9a'
BOUNDS_SHA256='9744ea02c4bd46d3d6696e967f0476f9bc40e634c5c1d5ecc7440eea7ad20db8'
ETAS=(1,4,7,8,11,13,14)
def demand(test,message):
    if not test:raise ValueError(message)
def main():
    p=argparse.ArgumentParser();p.add_argument('--base',type=Path,default=ROOT.parent/'missing23-eta14');p.add_argument('--stage',type=int,choices=(13,17,19,29),required=True);p.add_argument('--projection',default='2,3,2,8');p.add_argument('--eta',type=int,choices=ETAS,default=14)
    p.add_argument('--cache',type=Path,action='append',default=[]);p.add_argument('--fresh',action='store_true');p.add_argument('--regenerate',action='store_true');p.add_argument('--binary',type=Path);p.add_argument('--output',type=Path);args=p.parse_args()
    raw=(ROOT/'bounds.json').read_bytes();demand(hashlib.sha256(raw).hexdigest()==BOUNDS_SHA256,'fixed numerical input pin');data=json.loads(raw)
    source=args.base/'geometry_replay.py';demand(hashlib.sha256(source.read_bytes()).hexdigest()==BASE_REPLAY_SHA256,'prior geometry producer pin')
    d=runpy.run_path(str(source));g=d['current'].__globals__;root=ROOT/'geometry-cache'
    g['root']=root;g['cachefolders']=tuple(args.cache)+(root,args.base/'geometry-cache');g['ALLOW_GENERATE']=args.fresh or args.regenerate;g['REGENERATE']=args.regenerate;g['ENUMERATOR']=args.binary or ROOT/'geometry-enumerator'
    if g['ALLOW_GENERATE'] and not g['ENUMERATOR'].exists():subprocess.run(['c++','-O2','-std=c++17',str(args.base/'geometry.cpp'),'-o',str(g['ENUMERATOR'])],check=True)
    q=args.stage;t={13:4,17:8,19:8,29:16}[q]
    if q==13:
        projection=tuple(map(int,args.projection.split(',')));rows={tuple(r['xi13']):r for r in data['current13_flat11']}
        demand(projection in rows,'declared current13 label');demand(projection==tuple(rows[projection]['representative']),'rebuild192 representatives; use explicit transport for other48 labels')
        expected=rows[projection]['cost'];parts={(a,b,0):d['mul'](d['unit'] if a else d['pos7'],d['unit'] if b else d['pos11']) for a,b in product((0,1),repeat=2)};mode='four'
    else:
        expected=data['released_FF'][str(q)][str(args.eta)];parts=d['initial_parts']();projection=(1,4,7,args.eta);mode='released'
        # All eight source components, including zero13, are retained at17.
        for oldq,oldt in ((17,8),(19,8)):
            if oldq<q:parts={k:d['mul'](dist,d['full'](oldq,oldt)) for k,dist in parts.items()}
        for i,m in ((0,3),(1,5),(2,9)):
            demand({x[i] for x in d['v']['PROJECTIONS'] if x[-1]==args.eta}=={x%m for x in d['cs']},'complete released category domain')
    cost,_=d['current'](parts,None,None,projection,q,t,mode);demand(str(cost)==expected,'numerical reconstruction mismatch')
    result=dict(stage=q,xi11=None,xi13=None,projection=projection,mode=mode,cost=str(cost),input_matched=True,new_batches=len(g['NEW']),new_queries=sum(x['queries'] for x in g['NEW'].values()),used_batches=len(g['USED']),used_queries=sum(g['USED'].values()))
    text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
