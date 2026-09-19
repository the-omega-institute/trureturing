#!/usr/bin/env python3
"""Five further complete hinges on313's actual aligned source.

The same876-variable source includes every independently labelled target.
All new duals and original containing choices are checked with exact
rational arithmetic. The checker needs only the Python standard library.
"""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
import argparse,importlib.util,json,sys
sys.dont_write_bytecode=True
CERTIFICATE='certificates/source_norms/j-source/j_aligned_remaining_hinges.json'
PROVIDER='frontier/j-source/j_aligned_joint_selected_heads.py'
BASE_CERTIFICATE='certificates/source_norms/j-source/j_aligned_joint_selected_heads.json'
TARGETS=('hinge2','hinge3','hinge5','hinge6','hinge8')
def require(p,m):
 if not p:raise ValueError(m)
def module(n,p):
 s=importlib.util.spec_from_file_location(n,p);require(s is not None and s.loader is not None,'Readable established source provider')
 m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m

def calculate(base,given):
 provider=module('additional_actual_aligned313',base/PROVIDER)
 data=provider.strengthen(provider.build_source(base,'additional_aligned_source'))
 new=provider.build_joint(base,data);problem=new['problem'];io=data['io']
 read=lambda path:json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique)
 original=read(base/provider.ORIGINAL);bases={r['name']:r for r in original['basis']};prior=read(base/BASE_CERTIFICATE)
 require(new['specification']['rows_sha256']==prior['model']['rows_sha256'],'The identical actual876-column source from313')
 require(set(given['seeds'])==set(TARGETS),'Exactly five original complete hinge targets')
 problem.bank=given['rational_duals'];rows=[]
 for name in TARGETS:
  threshold=int(name[5:]);a=provider.original_coefficients(bases[name])
  require(a=={threshold:F(1)},'Original numbered hinge at every positive integer load')
  seed=given['seeds'][name];layout=tuple(seed['layout']);projection=tuple(seed['projection21_35_63_105'])
  require(len(layout)==7 and all(0<=v<limit for v,limit in zip(layout,(2,5,5,2,5,5,5)))and len(projection)==5 and all(0<=v<limit for v,limit in zip(projection,(2,5,5,2,5))),'Independent containing choices used only to schedule pruning')
  request={'index':name,'scan':{'coefficients':a,'maximizing_witness':{'layout':layout,**dict(zip(('seven21_root','seven35_slot','seven63_cell','seven105_root','seven105_slot'),projection))}}}
  scan=problem.scan(request);upper=scan['complete_hinge_upper']
  rows.append({'name':name,'complete_upper':upper,'original_low_load_values':bases[name]['low_load_values'],
   'original_tail_polynomial':bases[name]['tail_polynomial'],'scan':scan})
  print('Complete additional aligned '+name+' <= '+str(upper)+' = '+str(float(upper)),flush=True)
 require(problem.used==set(problem.bank),'All new rational duals consumed')
 # Reuse only313's already exact original-consumer coefficient arithmetic.
 account=provider.consumer_account(original,rows);prices={r['name']:r for r in account['proved_source_costs']}
 contributions=[]
 for r in rows:
  name=r['name'];reference=F(bases[name]['upper']);gap=r['complete_upper']-reference;price=prices[name]['signed403_price']
  contributions.append({'name':name,'original299_reference':reference,'signed_gap':gap,'signed403_price':price,
   'signed403_gap_cost':price*gap,'nonnegative403_gap_cost':price*max(gap,F(0))})
 inherited={r['name']for r in prior['results']};remaining=sorted(set(prior['fixed299_consumer_account']['remaining_observations'])-set(TARGETS))
 require(inherited.isdisjoint(TARGETS)and len(inherited)==5 and len(remaining)==6,'Five inherited plus five new observations leave six original source bounds')
 sources=tuple(provider.SOURCES)+(PROVIDER,BASE_CERTIFICATE)
 return provider.encode({'schema':'erdos7-aligned-remaining-hinges-v1',
  'source_sha256':{p:sha256(io.read_artifact_bytes(base/p)).hexdigest()for p in sources},
  'domain':prior['domain'],'actual_source_mass':F(1,4),'actual_survivor_mass':F(413,2700),
  'model_sha256':new['specification']['rows_sha256'],'seeds':given['seeds'],'results':rows,
  'rational_duals':{k:problem.bank[k]for k in sorted(problem.used)},'distinct_dual_count':len(problem.used),
  'rational_dual_columns_checked':876*len(problem.used),'total_containing_choices':6250000*len(rows),
  'fixed299_observation_costs':contributions,
  'sum_signed403_gap_cost':sum(r['signed403_gap_cost']for r in contributions),
  'sum_nonnegative403_gap_cost':sum(r['nonnegative403_gap_cost']for r in contributions),
  'remaining_original_source_observations':remaining,
  'scope':'Five complete independent original hinges on the same actual aligned312/313 endpoint. Each target retains its own residues,all selected labels and full exponent/cofactor tails.313 supplies the model embedding and uniform finite-sequence limsup via complete summable tails. No common optimizer,explicit finite radius,positive403 comparison,unrestricted Erdos7 resolution or Lean verification.'})

def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2]);parser.add_argument('--certificate',type=Path)
 mode=parser.add_mutually_exclusive_group();mode.add_argument('--write',action='store_true');mode.add_argument('--check',action='store_true')
 args=parser.parse_args();base=args.base.resolve();path=args.certificate or base/CERTIFICATE
 io=module('additional_aligned_hinge_io',base/'certificate_io.py');given=json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique)
 result=calculate(base,given)
 if args.write:io.write_certificate_text(path,json.dumps(result,indent=2)+'\n');print('WROTE '+str(path),flush=True)
 else:require(result==given,'Complete exact additional-hinge certificate reconstructed');print('PASS five additional complete aligned hinges',flush=True)
if __name__=='__main__':main()
