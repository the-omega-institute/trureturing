#!/usr/bin/env python3
"""Run the frozen ell0 independent engine on numerical branches of one witness.
No producer implementation or temporary Python source is read or imported.
"""
from argparse import ArgumentParser
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import json,subprocess,sys
p=ArgumentParser(description=__doc__)
p.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
p.add_argument('--witness',type=Path,default=Path(__file__).with_name('regular_leaf_remaining_roles_certificate.json'))
p.add_argument('--engine',type=Path,default=Path(__file__).with_name('square7_ell0_product_full_layout_independent_driver.py'))
p.add_argument('--cpp',type=Path,default=Path(__file__).with_name('square7_ell0_product_full_layout_independent.cpp'))
p.add_argument('--branch',help='Optional row,column; default verifies all three remaining representative roles.')
p.add_argument('--mode',choices=('prepare','full'),default='full')
p.add_argument('--threads',type=int,default=2,help='Threads per selected branch, run concurrently.')
p.add_argument('--cxx',default='clang++')
p.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
a=p.parse_args();checks={}
def ck(k,b):
 checks[k]=checks.get(k,0)+1
 if not b:raise RuntimeError(k)
raw=a.witness.read_bytes();w=json.loads(raw);wh=sha256(raw).hexdigest()
engine_raw=a.engine.read_bytes();cpp_raw=a.cpp.read_bytes()
ck('frozen_independent_engine',sha256(engine_raw).hexdigest()=='e13f6dac582e1e5a4608e27d522d4278caacdcd4a3ded7ab624129fb20b10ce3')
ck('frozen_independent_cpp',sha256(cpp_raw).hexdigest()=='8d847167da6a51db132b7c478dd2cc4799d18f508578320b7e6bcb0ef773bcf3')
expected=[(0,1,0),(1,1,0),(1,2,0)]
ck('complete_witness_role_inventory',len(w['branches'])==3 and sorted(tuple(b['square7_roles']) for b in w['branches'])==expected)
branches={tuple(b['square7_roles']):b for b in w['branches']}
roles=expected
if a.branch:
 parts=a.branch.split(',');ck('branch_syntax',len(parts)==2)
 role=(int(parts[0]),int(parts[1]),0);ck('branch_in_domain',role in branches);roles=[role]
ck('thread_count',1<=a.threads<=64)
pins={'remaining33_global_root_exclusion_certificate.json':'dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4','joint_square_pair_225_star_certificate.json':'cbdc3903174d5640ea6518160abaaa9ac567424f9f8afc717128e1202f378be5'}
for name,h in pins.items():ck('container_source_pin',w['source_sha256'][name]==h)
payloads=[]
for role in roles:
 branch=branches[role]
 for name,h in pins.items():ck('branch_source_pin',branch['source_sha256'][name]==h)
 # These are precisely the numerical fields consumed by the frozen engine.
 payload=dict(square7_roles=list(role),source_sha256=dict(pins),families=branch['families'])
 data=(json.dumps(payload,sort_keys=True,separators=(',',':'))+'\n').encode()
 payloads.append((role,data))
def run(item,root):
 role,data=item;tag='row'+str(role[0])+'_column'+str(role[1]);sub=root/tag;sub.mkdir()
 numerical=sub/(tag+'_derived_numeric.json');result_path=sub/'result.json';numerical.write_bytes(data)
 command=[sys.executable,'-I','-S','-B','-O',str(a.engine.resolve()),'--directory',str(a.directory.resolve()),'--cpp',str(a.cpp.resolve()),'--witness',str(numerical),'--mode',a.mode,'--threads',str(a.threads),'--cxx',a.cxx,'--output',str(result_path)]
 completed=subprocess.run(command,stdout=subprocess.PIPE,text=True,check=True)
 result_raw=result_path.read_bytes();result=json.loads(result_raw)
 return role,dict(square7_roles=list(role),derived_numerical_sha256=sha256(data).hexdigest(),engine_result_sha256=sha256(result_raw).hexdigest(),result=result)
with TemporaryDirectory(prefix='remaining-regular-independent-',dir='/tmp') as tmp:
 root=Path(tmp)
 with ThreadPoolExecutor(max_workers=len(roles)) as pool:
  futures=[pool.submit(run,item,root) for item in payloads]
  verified=[f.result() for f in futures]
verified.sort(key=lambda x:x[0]);outbranches=[x[1] for x in verified]
for role,branch in verified:
 r=branch['result'];ck('branch_result_roles',tuple(r['square7_roles'])==role)
 ck('branch_result_status',r['status']==('PASS' if a.mode=='full' else 'PREPARED'))
 ck('branch_numerical_pin',list(r['field_witness_sha256'].values())==[branch['derived_numerical_sha256']])
 ck('branch_engine_pin',r['driver_sha256']==sha256(engine_raw).hexdigest() and r['cpp_sha256']==sha256(cpp_raw).hexdigest())
 if a.mode=='full':
  e=r['enumeration'];ck('branch_complete_domain',e['canonical_layout_count']==2470931 and e['actual_layout_count']==9765625)
  ck('branch_complete_corner_queries',e['accepted_complete_corner_gates']==49418620 and e['accepted_complete_screen_maxima']==25302333440)
  ck('branch_complete_orbit_census',r['layout_orbit_counts']==[1,59048,2411882])
ck('engine_unchanged',a.engine.read_bytes()==engine_raw);ck('cpp_unchanged',a.cpp.read_bytes()==cpp_raw);ck('witness_unchanged',a.witness.read_bytes()==raw)
result=dict(schema='remaining-regular-roles-independent-v1',status=('PASS' if a.mode=='full' else 'PREPARED'),mode=a.mode,new_lean_verification=False,read_same_round_producer=False,field_witness_sha256={a.witness.name:wh},source_sha256=pins,driver_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),engine_sha256=sha256(engine_raw).hexdigest(),cpp_sha256=sha256(cpp_raw).hexdigest(),selected_roles=[list(r) for r in roles],branches=outbranches,checks=checks,wrapper_check_count=sum(checks.values()),engine_check_count=sum(b['result']['check_count'] for b in outbranches),scope=('Preparation only; no layout gates checked. ' if a.mode=='prepare' else 'Independent full labelled-layout checks completed. ')+'Exactly the selected fixed ell0 roles; one whole field per canonical layout, with joint field/source transport. Inherited fixed low-pure/null/central15, globally fixed original phases, incidences and complete-tail hypotheses remain. No unrestricted odd-covering or new Lean conclusion.')
a.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status=result['status'],selected_roles=result['selected_roles'],wrapper_check_count=result['wrapper_check_count'],engine_check_count=result['engine_check_count'])))
