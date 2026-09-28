"""Explicit targeted reconstruction of the four additional eta11 slices."""
from pathlib import Path
from itertools import product
import argparse,hashlib,json,runpy,subprocess
ROOT=Path(__file__).resolve().parent
BASE_REPLAY_SHA256='d0c5dbf54089cf05da07e562b34b639890fb722fbf9efb96bc8a5068c729ed9a'
BOUNDS_SHA256='b929bbe055ea9a9208d1879b2ee8151bcf3cdc1044d1180bb36c04bfd7726a97'
ETAS=(1,4,7,8,11,13,14);D=(2,3,2,8);C=(2,4,8,14)
def demand(test,message):
    if not test:raise ValueError(message)
def main():
    p=argparse.ArgumentParser();p.add_argument('--base',type=Path,default=ROOT.parent/'missing23-eta14')
    p.add_argument('--stage',type=int,choices=(11,13,17,19,29),required=True);p.add_argument('--projection',default='2,3,2,8');p.add_argument('--eta',type=int,choices=ETAS,default=14)
    p.add_argument('--cache',type=Path,action='append',default=[]);p.add_argument('--fresh',action='store_true');p.add_argument('--regenerate',action='store_true');p.add_argument('--binary',type=Path);p.add_argument('--output',type=Path);args=p.parse_args()
    raw=(ROOT/'bounds.json').read_bytes();demand(hashlib.sha256(raw).hexdigest()==BOUNDS_SHA256,'fixed numerical input pin');data=json.loads(raw)
    source=args.base/'geometry_replay.py';demand(hashlib.sha256(source.read_bytes()).hexdigest()==BASE_REPLAY_SHA256,'prior geometry producer pin')
    d=runpy.run_path(str(source));g=d['current'].__globals__;root=ROOT/'geometry-cache'
    g['root']=root;g['cachefolders']=tuple(args.cache)+(root,args.base/'geometry-cache');g['ALLOW_GENERATE']=args.fresh or args.regenerate;g['REGENERATE']=args.regenerate;g['ENUMERATOR']=args.binary or ROOT/'geometry-enumerator'
    if g['ALLOW_GENERATE'] and not g['ENUMERATOR'].exists():subprocess.run(['c++','-O2','-std=c++17',str(args.base/'geometry.cpp'),'-o',str(g['ENUMERATOR'])],check=True)
    q=args.stage;t={11:4,13:4,17:8,19:8,29:16}[q];mode='four';projection=tuple(map(int,args.projection.split(',')))
    if q==11:
        rows={tuple(r['xi11']):r for r in data['current11']};demand(projection in rows,'declared current11 label')
        demand(projection==tuple(rows[projection]['representative']),'rebuild only128 representatives; use the explicit transport for other labels')
        expected=rows[projection]['cost'];parts={(a,0,0):d['unit'] if a else d['pos7'] for a in (0,1)};x11=projection;x13=C
    elif q==13:
        rows={tuple(r['xi13']):r['cost'] for r in data['current13_D']};demand(projection in rows,'one of three actual-D current13 labels')
        expected=rows[projection];parts={(a,b,0):d['mul'](d['unit'] if a else d['pos7'],d['unit'] if b else d['pos11']) for a,b in product((0,1),repeat=2)};x11=D;x13=projection
    else:
        expected=data['released_DC'][str(q)][str(args.eta)];parts=d['initial_parts']();x11=D;x13=C;projection=(1,4,7,args.eta);mode='released'
        for oldq,oldt in ((17,8),(19,8)):
            if oldq<q:parts={k:d['mul'](dist,d['full'](oldq,oldt)) for k,dist in parts.items()}
        for i,m in ((0,3),(1,5),(2,9)):
            demand({x[i] for x in d['v']['PROJECTIONS'] if x[-1]==args.eta}=={x%m for x in d['cs']},'complete released category domain')
    cost,_=d['current'](parts,x11,x13,projection,q,t,mode);demand(str(cost)==expected,'numerical bound reconstruction mismatch')
    result=dict(stage=q,xi11=x11,xi13=x13,projection=projection,mode=mode,cost=str(cost),input_matched=True,new_batches=len(g['NEW']),new_queries=sum(x['queries'] for x in g['NEW'].values()),used_batches=len(g['USED']),used_queries=sum(g['USED'].values()))
    text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
