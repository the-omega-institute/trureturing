"""Explicit source current11 reconstruction; uses the pinned prior producer."""
from pathlib import Path
import argparse,hashlib,json,runpy,subprocess
ROOT=Path(__file__).resolve().parent
BASE_REPLAY_SHA256='d0c5dbf54089cf05da07e562b34b639890fb722fbf9efb96bc8a5068c729ed9a'
SOURCE_CURRENT11_SHA256='0912b101439bbe9d0e11e3f4b0b9668cc7b8dd4a514eeef0df058e84edece7aa'
def demand(test,message):
    if not test:raise ValueError(message)
def main():
    p=argparse.ArgumentParser();p.add_argument('--base',type=Path,default=ROOT.parent/'missing23-eta14');p.add_argument('--eta',type=int,choices=(1,4,7,8,11,13,14),required=True)
    p.add_argument('--cache',type=Path,action='append',default=[]);p.add_argument('--fresh',action='store_true');p.add_argument('--regenerate',action='store_true');p.add_argument('--binary',type=Path);p.add_argument('--output',type=Path);args=p.parse_args()
    raw=(ROOT/'source_current11.json').read_bytes();demand(hashlib.sha256(raw).hexdigest()==SOURCE_CURRENT11_SHA256,'source input pin')
    expected=next(r['cost'] for r in json.loads(raw)['rows'] if r['eta']==args.eta)
    source=args.base/'geometry_replay.py';demand(hashlib.sha256(source.read_bytes()).hexdigest()==BASE_REPLAY_SHA256,'prior producer pin')
    d=runpy.run_path(str(source));g=d['current'].__globals__;root=ROOT/'geometry-cache'
    g['root']=root;g['cachefolders']=tuple(args.cache)+(root,args.base/'geometry-cache');g['ALLOW_GENERATE']=args.fresh or args.regenerate;g['REGENERATE']=args.regenerate;g['ENUMERATOR']=args.binary or ROOT/'geometry-enumerator'
    if g['ALLOW_GENERATE'] and not g['ENUMERATOR'].exists():subprocess.run(['c++','-O2','-std=c++17',str(args.base/'geometry.cpp'),'-o',str(g['ENUMERATOR'])],check=True)
    for i,m in ((0,3),(1,5),(2,9)):
        demand({x[i] for x in d['v']['PROJECTIONS'] if x[-1]==args.eta}=={x%m for x in d['cs']},'full released domain')
    parts={(a,0,0):d['unit'] if a else d['pos7'] for a in (0,1)}
    cost,_=d['current'](parts,(2,4,2,14),(2,4,5,14),(1,4,7,args.eta),11,4,'released')
    demand(str(cost)==expected,'reconstructed source current11 differs')
    result=dict(eta=args.eta,cost=str(cost),source_value_matched=True,new_batches=len(g['NEW']),new_queries=sum(x['queries'] for x in g['NEW'].values()),used_batches=len(g['USED']),used_queries=sum(g['USED'].values()))
    text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
