#!/usr/bin/env python3
"""Complete raw prime-path moments and tails of the actual aligned J source.

Standard-library replay of every independent original six-label head,
with fixed H masses, one source parameter, and complete geometric tails.
"""
from fractions import Fraction as F
from pathlib import Path
from hashlib import sha256
import argparse,importlib.util,json,sys
sys.dont_write_bytecode=True
CERTIFICATE='certificates/source_norms/j_aligned_raw_prime_path_moments.json'
def module(n,p):
 s=importlib.util.spec_from_file_location(n,p)
 if s is None or s.loader is None:raise ValueError('Loadable mathematical source')
 m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m

def calculate(B):
 provider=module('aligned_raw313',B/'frontier/j_aligned_joint_selected_heads.py')
 d=provider.strengthen(provider.build_source(B,'aligned_raw_moments'))
 j,io=d['j'],d['io']
 source313=json.loads(io.read_artifact_bytes(B/'certificates/source_norms/j_aligned_joint_selected_heads.json'),object_pairs_hook=io._unique)
 for path,pin in source313['source_sha256'].items():
  provider.require(sha256(io.read_artifact_bytes(B/path)).hexdigest()==pin,'Current313 mathematical source '+path)
 pins={**source313['source_sha256']}
 for path in ('frontier/j_aligned_joint_selected_heads.py','certificates/source_norms/j_aligned_joint_selected_heads.json','frontier/j_face_shared_square_factorial.py','frontier/j_face_raw_prime_path_pairs.py','frontier/j_face_coherent_positive7_pairs.py','frontier/j_face_joint_retained_square.py','frontier/complete_off_face_factorial_tail.py'):
  pins[path]=sha256(io.read_artifact_bytes(B/path)).hexdigest()
 mom=module('aligned_raw_mom241',B/'frontier/j_face_shared_square_factorial.py')
 paths=module('aligned_raw_paths265',B/'frontier/j_face_raw_prime_path_pairs.py')
 tails=module('aligned_raw_tails128',B/'frontier/complete_off_face_factorial_tail.py')
 previous=module('aligned_raw_pairs258',B/'frontier/j_face_coherent_positive7_pairs.py')
 headmod=module('aligned_raw_head245',B/'frontier/j_face_joint_retained_square.py')
 tail=mom.complete_tail(tails);omitted=previous.complete_raw_omitted_tail(tails,tail)
 partition=previous.complete_positive7_partition(tail)
 p,raw,e,w=j.source_tables(j.LO)
 c3=tuple(sum(row)for row in p);c5=tuple(sum(row[s]for row in e)for s in range(5))
 problem=mom.JMomentHead(j)
 best={k:F(-1)for k in ('pair','square')};witness={k:[]for k in best}
 digest=sha256();count=0
 for il,layout in enumerate(j.layouts()):
  H=headmod.head_load(j,layout);cross=problem.old_tail(H)
  a3=tuple(sum(p[c][s]*H[5*c+s]for s in range(5))for c in range(5))
  a5=tuple(sum(e[c][s]*H[5*c+s]for c in range(5))for s in range(5))
  blocks={name:[paths.path_bound(3,3,a3,c3,name=='square'),paths.path_bound(5,2,a5,c5,name=='square')]for name in best}
  changes={name:sum(row['block_change']for row in values)for name,values in blocks.items()}
  for theta in (j.LO,j.HI):
   values={
    'pair':problem.lp(tuple(F(v*(v-1),2)for v in H),theta)+cross+omitted['raw_omitted_distinct_pairs']+changes['pair'],
    'square':problem.lp(tuple(F(v*v)for v in H),theta)+2*cross+2*omitted['raw_omitted_distinct_pairs']+omitted['raw_omitted_diagonal']+changes['square']}
   row={'layout':layout,'theta':theta,'complete_raw_old_cross':cross,'block_changes':changes,'complete_bounds':values}
   digest.update(json.dumps(provider.encode(row),sort_keys=True,separators=(',',':')).encode())
   for name in best:
    if values[name]>best[name]:best[name]=values[name];witness[name]=[]
    if values[name]==best[name]:witness[name].append({**row,'complete_prime_blocks':blocks[name]})
   count+=1
  if (il+1)%2500==0:print('Aligned raw prime paths',il+1,'/12500',flush=True)
 provider.require(count==25000,'All original raw layouts and both common theta endpoints')
 pzz=partition['complete_same_depth_weight']*best['pair']+partition['complete_cross_depth_weight']*best['square']
 fullpairs=tail['old_old_distinct']+tail['old_positive7']+pzz
 zdiag=F(3,20)-F(2,675)
 ordered=2*fullpairs+tail['old_diagonal']+zdiag
 result={'schema':'erdos7-aligned-raw-prime-path-moments-v1',
  'domain':'Actual aligned312 endpoint, own independent old tests, complete source paths and pair tails.',
  'source_sha256':pins,
  'actual_raw_mass':F(1,4),'actual_survivor_mass':F(413,2700),'theta_interval':[j.LO,j.HI],
  'original_head_count':12500,'endpoint_records':count,'all_endpoint_bounds_sha256':digest.hexdigest(),
  'complete_raw_pair_upper':best['pair'],'complete_raw_square_upper':best['square'],
  'maximizing_relaxation_witnesses':witness,'complete_raw_omitted_tail':omitted,
  'complete_positive7_partition':partition,'complete_PZZ_upper':pzz,
  'complete_POO_upper':tail['old_old_distinct'],'complete_POZ_upper':tail['old_positive7'],
  'complete_survivor_tail_distinct_pairs':fullpairs,'complete_survivor_tail_square':ordered,
  'scope':'Fresh actual aligned source bounds. Numerical saturated raw moment maxima are not reused. All finite heights pass through complete positive geometric tails. No source realization of LP maxima, full403 consumer, explicit neighborhood or unrestricted resolution.'}
 provider.require((best['pair'],best['square'],pzz,fullpairs,ordered)==(F(1093,864),F(2321,720),F(3893,10800),F(14413,21600),F(3391,2160)),'Complete actual aligned rational maxima and tail partition')
 return provider.encode(result)


def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[1])
 parser.add_argument('--certificate',type=Path)
 mode=parser.add_mutually_exclusive_group();mode.add_argument('--write',action='store_true');mode.add_argument('--check',action='store_true')
 args=parser.parse_args();base=args.base.resolve();path=args.certificate or base/CERTIFICATE
 result=calculate(base);io=module('aligned_raw_writer',base/'certificate_io.py')
 if args.write:io.write_certificate_text(path,json.dumps(result,indent=2)+'\n')
 elif result!=json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique):raise ValueError('Every complete raw-moment field must reconstruct')
 print('PASS aligned raw pair='+result['complete_raw_pair_upper']+', square='+result['complete_raw_square_upper']+', PZZ='+result['complete_PZZ_upper']+';25000 complete endpoint records',flush=True)
if __name__=='__main__':main()
