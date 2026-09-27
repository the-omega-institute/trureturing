"""Small synthetic process/checkout/orchestration regressions; no workflow assertions."""
import contextlib, hashlib, importlib.util, io, json, os, pathlib, signal, subprocess, sys, tempfile, time, unittest
from unittest import mock
ROOT=pathlib.Path(__file__).resolve().parents[3]
HELP=ROOT/'tools/lean-inspector/M3TemporaryProbe'
sys.path.insert(0,str(HELP))
sys.dont_write_bytecode=True

def load(name):
 spec=importlib.util.spec_from_file_location(name,HELP/(name+'.py')); m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
measure=load('measure'); probe=load('probe')
class Measurement(unittest.TestCase):
 def setUp(self):
  probe.WORK_DEADLINE=None
  self.temp=tempfile.TemporaryDirectory(); self.p=pathlib.Path(self.temp.name); self.addCleanup(self.temp.cleanup)
  self.bin=self.p/'bin'; self.bin.mkdir()
 def trial(self, name, script, ps='printf "1 0 0.0 init\\n"', seconds=1800, cap=16777216):
  fake=self.bin/'ps'; fake.write_text('#!/bin/sh\n'+ps+'\n'); fake.chmod(0o755)
  argv=['measure','--output',str(self.p),'--sample',name,'--cwd',str(self.p),'--',sys.executable,'-c',script]
  with mock.patch.object(sys,'argv',argv), mock.patch.dict(os.environ,{'PATH':str(self.bin)+os.pathsep+os.environ['PATH']}), mock.patch.object(measure,'MAX_SECONDS',seconds), mock.patch.object(measure,'MAX_OUTPUT_BYTES',cap), contextlib.redirect_stdout(io.StringIO()):
   code=measure.main()
  data=json.loads((self.p/(name+'.result.json')).read_text()); data['review_return']=code
  return code,data
 def test_success_and_boundaries(self):
  code,r=self.trial('clean',"print('ok')")
  self.assertEqual(code,0); self.assertTrue(r['accepted']); self.assertEqual(r['load_samples'],3); self.assertEqual(r['output_bytes'],3)
 def test_nonzero_child_rejected(self):
  code,r=self.trial('nonzero','raise SystemExit(7)'); self.assertEqual(code,1); self.assertEqual(r['exit'],7)
 def test_external_process_rejected(self):
  code,r=self.trial('external',"print('ok')",ps='printf "999999 1 0.0 lean\\n"')
  self.assertEqual(code,1); self.assertEqual(r['external_lean_min'],1)
 def test_failed_census_rejected(self):
  code,r=self.trial('failed_census',"print('ok')",ps='exit 9')
  self.assertFalse(r['accepted'],'failed ps must not certify an empty host census')
 def test_malformed_census_rejected(self):
  code,r=self.trial('malformed_census',"print('ok')",ps='printf "garbage\\n"')
  self.assertFalse(r['accepted'],'unparseable ps must not certify an empty host census')
 def test_output_overflow_rejected_and_storage_bounded(self):
  code,r=self.trial('overflow',"print('x'*2048)",cap=1024)
  self.assertEqual(code,1); self.assertTrue(r['output_truncated']); self.assertEqual((self.p/'overflow.stdout.log').stat().st_size,1024)
 def test_running_timeout_rejected(self):
  code,r=self.trial('timeout','import time; time.sleep(3)',seconds=.1)
  self.assertEqual(code,1); self.assertTrue(r['timed_out']); self.assertLess(r['wall_seconds'],2)
 def test_completion_over_deadline_rejected(self):
  code,r=self.trial('late_completion','import time; time.sleep(.35)',seconds=.1)
  self.assertFalse(r['accepted'],'completion after the budget but before the next poll must reject')
 def test_descendant_pipe_cannot_escape_deadline(self):
  script="import subprocess,sys; subprocess.Popen([sys.executable,'-c','import time; time.sleep(1.4)'])"
  code,r=self.trial('orphan_pipe',script,seconds=.1)
  self.assertFalse(r['accepted'],'an inherited stdout child must remain in the deadline domain')
 def test_ownership_classification(self):
  rows=[(10,1,0.,'time'),(11,10,0.,'lean'),(12,11,0.,'reportInspector'),(14,1,0.,'lean')]
  with mock.patch.object(measure,'ps_rows',return_value=rows): r=measure.observation(10)
  self.assertEqual(r['own_lean_count'],2); self.assertEqual(r['external_lean_count'],1)
class Helpers(unittest.TestCase):
 def setUp(self):
  probe.WORK_DEADLINE=None
  self.temp=tempfile.TemporaryDirectory(); self.p=pathlib.Path(self.temp.name); self.addCleanup(self.temp.cleanup)
 def test_run_nonzero_and_timeout(self):
  r=probe.run([sys.executable,'-c','raise SystemExit(9)'],self.p,os.environ.copy(),self.p,'nonzero',timeout=1)
  self.assertEqual(r['exit'],9)
  r=probe.run([sys.executable,'-c','import time; time.sleep(3)'],self.p,os.environ.copy(),self.p,'timeout',timeout=.1)
  self.assertIsNotNone(r['error']); self.assertLess(r['wall_seconds'],2)
 def test_run_orphan_remains_bounded(self):
  r=probe.run([sys.executable,'-c',"import subprocess,sys; subprocess.Popen([sys.executable,'-c','import time; time.sleep(1.4)'])"],self.p,os.environ.copy(),self.p,'orphan',timeout=.1)
  self.assertIsNotNone(r['error'],'run() must reject descendant output retained past its deadline')
 def test_identity_hash_and_axioms(self):
  rows=[{'name':'T','levelParams':[],'type_dag':{'root':0,'nodes':[['sort','0']]},'value_dag':None,'axioms':['propext']}]
  path=self.p/'test.raw.json'; path.write_text(json.dumps(rows))
  r=subprocess.run([sys.executable,'-B',str(HELP/'hash-identities.py'),str(path)],capture_output=True,text=True,timeout=5)
  self.assertEqual(r.returncode,0); out=path.with_name('test.json'); data=json.loads(out.read_text())
  expected=hashlib.sha256(b'{"nodes":[["sort","0"]],"root":0}').hexdigest()
  self.assertEqual(data[0]['type_dag_sha256'],expected); self.assertIsNone(data[0]['value_dag_sha256'])
  self.assertEqual(probe.identity_summary(out)['unexpected_axioms'],[])
  data[0]['axioms'].append('customAx'); out.write_text(json.dumps(data))
  self.assertEqual(probe.identity_summary(out)['unexpected_axioms'],['customAx'])
 def test_normalizer_malformed_rejected(self):
  path=self.p/'bad.raw.json'; path.write_text('[{"type_dag":null}]')
  r=subprocess.run([sys.executable,'-B',str(HELP/'hash-identities.py'),str(path)],capture_output=True,text=True,timeout=5)
  self.assertNotEqual(r.returncode,0)

class StrictCensus(unittest.TestCase):
 setUp=Measurement.setUp
 trial=Measurement.trial
 def test_empty_census(self):
  self.assertFalse(self.trial('empty',"print('ok')",ps='exit 0')[1]['accepted'])
 def test_timeout_census(self):
  with mock.patch.object(measure,'CENSUS_SECONDS',.08):
   code,r=self.trial('ps_timeout',"print('ok')",ps='sleep 2',seconds=.3)
  self.assertFalse(r['accepted']); self.assertLess(r['wall_seconds'],.6)
 def test_invalid_numeric_census(self):
  for value in ('nan','inf','-1'):
   with self.subTest(value=value):
    self.assertFalse(self.trial('badcpu',"print('ok')",ps=f'printf "1 0 {value} init\\n"')[1]['accepted'])
 def test_invalid_after_or_scheduled(self):
  good={'utc':'synthetic','valid':True,'external_lean_count':0}
  bad={'utc':'synthetic','valid':False,'external_lean_count':None}
  for fail_at in (1,2,3):
   with self.subTest(fail_at=fail_at):
    rows=[dict(good) for _ in range(4)]; rows[fail_at]=dict(bad)
    with mock.patch.object(measure,'SAMPLE_SECONDS',.05), mock.patch.object(measure,'observation',side_effect=rows+[dict(good)]*10):
     self.assertFalse(self.trial('missing',"import time; time.sleep(.12)",seconds=1)[1]['accepted'])
 def test_after_boundary_failure(self):
  good={'utc':'synthetic','valid':True,'external_lean_count':0}
  bad={'utc':'synthetic','valid':False,'external_lean_count':None}
  calls=[]
  def census(owner,deadline=None):
   calls.append(owner)
   return dict(bad if owner is None and len(calls)>1 else good)
  with mock.patch.object(measure,'observation',side_effect=census):
   _,result=self.trial('invalid_after',"print('ok')")
  self.assertFalse(result['accepted']); self.assertFalse(result['boundary_after']['valid'])
 def test_unrelated_process_survives_cleanup(self):
  other=subprocess.Popen([sys.executable,'-c','import time; time.sleep(5)'],start_new_session=True)
  try:
   _,r=self.trial('own_only','import time; time.sleep(3)',seconds=.1)
   self.assertFalse(r['accepted']); self.assertIsNone(other.poll())
  finally:
   other.kill(); other.wait(timeout=1)
 def test_descendant_is_killed(self):
  pidfile=self.p/'child.pid'
  code="import subprocess,sys,pathlib; p=subprocess.Popen([sys.executable,'-c','import time; time.sleep(4)']); pathlib.Path(sys.argv[1]).write_text(str(p.pid))"
  # A direct run exercises the same primitive as every auxiliary command.
  result=probe.run([sys.executable,'-c',code,str(pidfile)],self.p,os.environ.copy(),self.p,'child',timeout=.3)
  self.assertFalse(measure.process_ok(result))
  child=int(pidfile.read_text())
  census=subprocess.run(['ps','-p',str(child),'-o','stat='],capture_output=True,text=True,timeout=1)
  self.assertTrue(census.returncode!=0 or census.stdout.strip().startswith('Z'))

class Imports(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.source=subprocess.check_output(['git','show',probe.BASELINE_SHA+':'+probe.IMPORT_PATH],cwd=ROOT)
 def result(self,exit=0):
  return dict(exit=exit,error=None,process_error=None,timed_out=False,output_truncated=False,
              within_deadline=True,wall_seconds=.01,max_seconds=120,output_bytes=0,output_limit_bytes=16777216)
 def test_exact_baseline_and_final(self):
  a=probe.import_result(self.result(1),'file.lean:50:4: error: ImportCost: M3 closure changed: modules=144 interface=6','baseline',self.source)
  b=probe.import_result(self.result(),'DTR_M3_IMPORTS modules=143 limit=143 interface=6\n','final',self.source)
  self.assertTrue(a['accepted']); self.assertTrue(b['accepted']); self.assertEqual(a['limit'],143)
 def test_unrelated_errors_and_changed_threshold(self):
  exact='file.lean:50:4: error: ImportCost: M3 closure changed: modules=144 interface=6'
  for text in ('error: unrelated',exact+'\nerror: unrelated',exact.replace('144','145'),'DTR_M3_IMPORTS modules=144 limit=143 interface=6',exact+'\n'+exact):
   with self.subTest(text=text): self.assertFalse(probe.import_result(self.result(1),text,'baseline',self.source)['accepted'])
  self.assertFalse(probe.import_result(self.result(1),exact,'baseline',self.source.replace(b'> 143',b'> 144'))['accepted'])
  self.assertFalse(probe.import_result(self.result(),'error: unrelated\nDTR_M3_IMPORTS modules=143 limit=143 interface=6','final',self.source)['accepted'])
 def test_breaches_cannot_hide_behind_exit(self):
  for flag,value in (('error','timeout'),('output_truncated',True),('timed_out',True),('within_deadline',False),('wall_seconds',121),('output_bytes',16777217)):
   with self.subTest(flag=flag):
    r=self.result(1); r[flag]=value
    self.assertFalse(probe.import_result(r,'error: ImportCost: M3 closure changed: modules=144 interface=6','baseline',self.source)['accepted'])

class Checkout(unittest.TestCase):
 def test_fetch_then_actual_checkout_strips_remote(self):
  import shutil
  with tempfile.TemporaryDirectory() as t:
   folder=pathlib.Path(t); origin=folder/'origin'; origin.mkdir(); repo=folder/'checkout'
   def git(root,*args): return subprocess.run(['git',*args],cwd=root,check=True,capture_output=True,text=True,timeout=5).stdout.strip()
   git(origin,'init','-q'); git(origin,'config','user.name','Synthetic'); git(origin,'config','user.email','test@example.invalid')
   revisions=[]
   for i in range(4):
    git(origin,'commit','-qm',str(i),'--allow-empty'); revisions.append(git(origin,'rev-parse','HEAD'))
   git(folder,'clone','-q','--depth=1','file://'+str(origin),str(repo))
   missing=subprocess.run(['git','cat-file','-e',revisions[0]+'^{commit}'],cwd=repo,capture_output=True,timeout=5)
   self.assertNotEqual(missing.returncode,0)
   helper=repo/'tools/scripts/workflow'; helper.mkdir(parents=True)
   for name in ('ci.py','ci_plan.py'): shutil.copy2(ROOT/'tools/scripts/workflow'/name,helper/name)
   clean={k:v for k,v in os.environ.items() if not k.startswith(('GITHUB_','CI_PUSH_','M3_READ_TOKEN'))}
   with mock.patch.dict(os.environ,clean,clear=True):
    r=probe.bootstrap(repo,revisions[-1],folder/'result',revisions)
   self.assertTrue(measure.process_ok(r['checkout']))
   self.assertEqual(git(repo,'remote'),''); self.assertEqual(git(repo,'for-each-ref','refs/remotes/'),'')
   for revision in revisions: git(repo,'cat-file','-e',revision+'^{commit}')
   after=subprocess.run(['git','fetch','origin',revisions[0]],cwd=repo,capture_output=True,timeout=5)
   self.assertNotEqual(after.returncode,0)

class Orchestration(unittest.TestCase):
 def trial(self,breach=None,bad_export=False,exhausted=False):
  with tempfile.TemporaryDirectory() as t:
   folder=pathlib.Path(t); output=folder/'out'; calls=[]
   fixture={'synthetic_export':True}; normalized=json.dumps(fixture,sort_keys=True,separators=(',',':')).encode()
   source=subprocess.check_output(['git','show',probe.BASELINE_SHA+':'+probe.IMPORT_PATH],cwd=ROOT).decode()
   rows=[{'name':'synthetic'+str(i),'levelParams':[],'type_dag':{'root':0,'nodes':[['sort','0']]},'value_dag':None,'axioms':probe.EXPECTED_AXIOMS} for i in range(282)]
   identity_rows=[{'name':r['name'],'levelParams':[],'type_dag_sha256':hashlib.sha256(b'{"nodes":[["sort","0"]],"root":0}').hexdigest(),'value_dag_sha256':None,'axioms':probe.EXPECTED_AXIOMS} for r in rows]
   ids=hashlib.sha256(json.dumps(identity_rows,sort_keys=True,separators=(',',':')).encode()).hexdigest()
   def fakegit(root,*args,**kwargs):
    if args[:2]==('worktree','add'): pathlib.Path(args[3]).mkdir()
    if args[:2]==('worktree','remove'): pathlib.Path(args[3]).rmdir()
    text=source if args[0]=='show' and args[1].endswith(probe.IMPORT_PATH) else (ROOT/'lean-toolchain').read_text()
    return subprocess.CompletedProcess(args,0,text,'')
   def fakerun(argv,cwd,env,output,name,timeout=300):
    output.mkdir(parents=True,exist_ok=True); stdout=output/(name+'.stdout.log'); stdout.write_text('')
    phase=output.name; calls.append((phase,name,timeout)); r=Imports().result(); r.update(stdout=str(stdout),max_seconds=timeout)
    if phase=='module': stdout.write_text('M3_MODULE_ID LeanInformationAudit.Tests.Seal.M3')
    if phase=='imports':
     stdout.write_text('error: ImportCost: M3 closure changed: modules=144 interface=6' if name=='baseline' else 'DTR_M3_IMPORTS modules=143 limit=143 interface=6')
     r['exit']=1 if name=='baseline' else 0
    if 'M3_ANALYSIS_PATH' in env: pathlib.Path(env['M3_ANALYSIS_PATH']).write_text(json.dumps({'bad':True} if bad_export else fixture))
    if 'M3_IDENTITIES_PATH' in env: pathlib.Path(env['M3_IDENTITIES_PATH']).write_text(json.dumps(rows))
    if name.endswith('-normalize'):
     completed=subprocess.run(argv,cwd=cwd,capture_output=True,timeout=5); r['exit']=completed.returncode
    if breach and (phase==breach[0] or name.endswith('-'+breach[0])): r[breach[1]]=breach[2]
    return r
   sample_calls=[]
   def fake_measure(argv,cwd,env,output,name,deadline=None):
    sample_calls.append(name); r=Imports().result(); r['accepted']=True; return r
   args=['probe','--repository',str(ROOT),'--output',str(output),'--producer-dll',str(folder/'synthetic.dll')]
   env={'M3_JOB_STARTED_MONOTONIC':str(time.monotonic()-20000 if exhausted else time.monotonic())}
   with mock.patch.object(sys,'argv',args), mock.patch.dict(os.environ,env), mock.patch.object(probe,'git',fakegit), mock.patch.object(probe,'source_hash',return_value=probe.M3_SHA256), mock.patch.object(probe,'run',fakerun), mock.patch.object(probe,'measure',fake_measure), mock.patch.object(probe,'EXPORT_BYTES',len(normalized)), mock.patch.object(probe,'EXPORT_SHA256',hashlib.sha256(normalized).hexdigest()), mock.patch.object(probe,'IDENTITY_SHA256',ids), contextlib.redirect_stdout(io.StringIO()): code=probe.main()
   return code,json.loads((output/'summary.json').read_text()),sample_calls,calls
 def test_positive_fixed_four_sample_plan(self):
  code,r,samples,calls=self.trial(); self.assertEqual(code,0); self.assertTrue(r['accepted'])
  self.assertEqual(samples,['A1','B1','B2','A2']); self.assertEqual(len(calls),12)
 def test_every_auxiliary_phase_propagates_error_overflow_and_deadline(self):
  for phase in ('warm','module','imports','export','identities','normalize'):
   for flag,value in (('error','timeout'),('output_truncated',True),('within_deadline',False),('wall_seconds',1801)):
    with self.subTest(phase=phase,flag=flag):
     code,r,_,_=self.trial(breach=(phase,flag,value)); self.assertEqual(code,1); self.assertFalse(r['accepted'])
 def test_bad_export_rejected(self):
  code,r,_,_=self.trial(bad_export=True); self.assertEqual(code,1); self.assertFalse(r['correspondence_accepted'])
 def test_exhausted_global_budget_returns_useful_incomplete_without_partial_run(self):
  code,r,samples,calls=self.trial(exhausted=True); self.assertEqual(code,1)
  self.assertTrue(r['incomplete']); self.assertFalse(r['accepted']); self.assertEqual(samples,[]); self.assertEqual(calls,[])

class LeanModuleIdentity(unittest.TestCase):
 def test_pinned_tiny_module_uses_production_direct_argv(self):
  pin=(ROOT/'lean-toolchain').read_text().strip()
  with tempfile.TemporaryDirectory() as t:
   root=pathlib.Path(t); impl=root/'tools/lean-inspector'
   source=impl/'LeanInformationAudit/Tests/Seal/M3.lean'; source.parent.mkdir(parents=True)
   (root/'lean-toolchain').write_text(pin+'\n')
   (impl/'lakefile.toml').write_text('name = "identityProbe"\n')
   source.write_text('import Lean\nopen Lean Elab Command\nrun_cmd do\n'
                    '  let actual := (← getEnv).mainModule\n'
                    '  unless actual == `LeanInformationAudit.Tests.Seal.M3 do\n'
                    '    throwError "wrong module: {actual}"\n'
                    '  logInfo m!"M3_MODULE_ID {actual}"\n')
   # The cache wrapper's cwd contract is repository root. The tiny package
   # has no project dependencies and only uses the installed pinned toolchain.
   direct=probe.direct_lean(root,probe.M3_PATH)
   with_root=['elan','run',pin,*direct[1:]]
   good=subprocess.run(with_root,cwd=root,capture_output=True,text=True,timeout=30)
   self.assertEqual(good.returncode,0); self.assertIn('M3_MODULE_ID LeanInformationAudit.Tests.Seal.M3',good.stdout)
   without_root=[arg for arg in with_root if not arg.startswith('--root=')]
   bad=subprocess.run(without_root,cwd=root,capture_output=True,text=True,timeout=30)
   self.assertEqual(bad.returncode,1); self.assertIn('wrong module: tools.«lean-inspector».LeanInformationAudit.Tests.Seal.M3',bad.stdout)

class SetupCLI(unittest.TestCase):
 def test_auxiliary_clean_and_overdue_job(self):
  with tempfile.TemporaryDirectory() as t:
   root=pathlib.Path(t)
   argv=[sys.executable,'-B',str(HELP/'measure.py'),'--aux','--seconds','1','--sample','setup',
         '--cwd',str(root),'--output',str(root),'--',sys.executable,'-c',"print('ok')"]
   for age,accepted in ((0,True),(2000,False)):
    with self.subTest(age=age):
     r=subprocess.run(argv,env=dict(os.environ,M3_JOB_STARTED_MONOTONIC=str(time.monotonic()-age)),capture_output=True,timeout=3)
     data=json.loads((root/'setup.result.json').read_text())
     self.assertEqual(data['accepted'],accepted); self.assertEqual(r.returncode,0 if accepted else 1)

if __name__=='__main__': unittest.main(verbosity=2)
