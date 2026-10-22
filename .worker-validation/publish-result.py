import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import xml.etree.ElementTree as ET

root=Path.cwd()
logs=root/'.worker-validation'
evidence=Path('/Users/macstudio/omega/research/open-problem-search-20261016/scoped-report-cache-refresh-fix-20261023')
acceptance_path=evidence/'darwin435-scoped-acceptance.json'
acceptance=json.loads(acceptance_path.read_text())
identity=json.loads((logs/'final-source-identity.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert acceptance['status']=='passed'
assert [x['exit'] for x in acceptance['commands']]==[0,0]
assert all(sha(root/x['path'])==x['sha256'] for x in identity['files'])
assert hashlib.sha256(subprocess.check_output(['git','diff','--',*[x['path'] for x in identity['files']]])).hexdigest()==identity['sha256']

def tests(label,directory,exit_code):
    files=list((logs/directory).glob('*.trx'))
    assert len(files)==1
    p=files[0]
    document=ET.parse(p).getroot()
    counters=document.find('{*}ResultSummary/{*}Counters').attrib
    return dict(name=label,exit=exit_code,total=int(counters['total']),passed=int(counters['passed']),failed=int(counters['failed']),
                trx=str(p),trx_sha256=sha(p),failed_cases=[r.attrib['testName'] for r in document.findall('{*}Results/{*}UnitTestResult') if r.attrib['outcome']!='Passed'])

results=[tests('cache-guard','guard-trx',0),tests('initial-scoped','scoped-trx',2),
         tests('final-scoped-contracts','final-scoped-trx',0),tests('final-native-regressions','final-native-trx',0)]
assert [(r['total'],r['failed']) for r in (results[0],results[2],results[3])]==[(24,0),(8,0),(2,0)]
commands=[
 dict(environment={'LEAN_NUM_THREADS':'1','TEST_RESULTS_DIRECTORY':str(logs/'guard-trx')},argv=['make','-C','tools','test','SELECTED_TEST_PROJECT='+str(root/'tools/tests/StrataLint.Tests/StrataLint.Tests.csproj'),'TEST_FILTER=FullyQualifiedName~WrappedWarmBuildReusesMatchingCacheWithoutReleaseRefresh|FullyQualifiedName~WrappedColdBuildStillFetchesProjectArchive|FullyQualifiedName~WrappedBuildStillRefreshesWhenMathlibIsCold|FullyQualifiedName~ProjectColdWithoutConsent|FullyQualifiedName~OleanEnumerationFailures|FullyQualifiedName~EitherProbeFailureRefuses|FullyQualifiedName~BusyTargetWriterFailsClosedBeforeEnsuring|FullyQualifiedName~WarmCacheRefreshUsesSourceAge|FullyQualifiedName~StampForPreviousMathlibPartition|FullyQualifiedName~RequiredMainDonorCloneFailure'],exit=0),
 dict(environment={'LEAN_NUM_THREADS':'1','TEST_RESULTS_DIRECTORY':str(logs/'final-scoped-trx')},argv=['make','-C','tools','test','SELECTED_TEST_PROJECT='+str(root/'tools/tests/StrataLint.Lean.Tests/StrataLint.Lean.Tests.csproj'),'TEST_FILTER=FullyQualifiedName~LeanReportScopedTests.ScopedProducerContract|DisplayName~test_native_scope_includes_external_consumer_and_checks_its_closure|DisplayName~test_native_aged_warm_scope_reuses_cache_without_archive_refresh'],exit=0,selected_cases=8),
 dict(environment={'LEAN_NUM_THREADS':'1','TEST_RESULTS_DIRECTORY':str(logs/'final-native-trx')},argv=['make','-C','tools','test','SELECTED_TEST_PROJECT='+str(root/'tools/tests/StrataLint.Lean.Tests/StrataLint.Lean.Tests.csproj'),'TEST_FILTER=DisplayName~test_native_scope_includes_external_consumer|DisplayName~test_native_aged_warm_scope'],exit=0,selected_cases=2),
 dict(argv=['git','diff','--check'],exit=0),
 *acceptance['commands']]
failures=[
 dict(boundary='First guarded cache seed replaced the prematurely-created default log directory',diagnostic=json.loads((evidence/'darwin435-scoped-attempt1.json').read_text())['failure_diagnostic'],exit=2,resolution='Discovery keeps startup logs outside .lake until cache admission completes; regression reproduces baseline FileNotFoundError and passes final source.',evidence=str(evidence/'darwin435-scoped-attempt1.json')),
 dict(boundary='Initial external-consumer native fixture',diagnostic='NATIVE_COMMAND_TIMEOUT timeout_seconds=120; owned native processes survived the fixture cleanup grace; ConsumerSupport Lean later exited 143.',exit=2,resolution='Owned processes exited; retained inactive fixture was removed after preserving diagnostics. Unmodified scenario passed its single focused rerun with original budgets.',evidence=str(logs/'initial-native-timeout')),
 dict(boundary='Acceptance observer after successful produce/verify',diagnostic=acceptance['observation_corrections'][0]['error'],exit=1,resolution='Strip newline before ISO timestamp parsing; final acceptance uses preserved exit-0 command evidence and unchanged report bytes, without rerunning or rebinding the report.')]
summary=dict(worktree=str(root),base=acceptance['base'],common_git=acceptance['common_git'],source_identity=identity,
             tests=results,commands=commands,real_acceptance=str(acceptance_path),real_acceptance_sha256=sha(acceptance_path),
             resolved_failures=failures,remaining_implementation_issues=[],
             cleanup=dict(removed_inactive_owned_timeout_fixture=True,shared_donor_preserved=True,worktree_retained_for_caller=True),
             lifecycle=dict(committed=False,pushed=False,pr_created=False,main_modified=False),
             limitations=['Validation covers the selected Darwin 4.35 scoped path and focused tests; no whole-project report/cache claim or CI claim.',
                          'The real run used the canonical linked worktree; isolated native fixtures exercise main-style age-based standalone refresh semantics.',
                          'Independent CLI reviews and publication/worktree lifecycle remain with the caller.'])
p=evidence/'verification-summary.json';tmp=p.with_suffix('.json.tmp');tmp.write_text(json.dumps(summary,indent=2)+'\n');tmp.replace(p)
diagnostics=dict(summary,logs={name:str(logs/name) for name in ('guard-tests.log','scoped-tests.log','final-scoped-tests.log','final-native-tests.log','real-produce.log','real-verify.log','log-replacement-test.log','log-replacement-negative-control.log')})
diagnostic_path=logs/'diagnostics.json';diagnostic_path.write_text(json.dumps(diagnostics,indent=2)+'\n')
conclusion=dict(status='implemented_and_scoped_validated',worktree=str(root),base=acceptance['base'],
 changed_paths=[x['path'] for x in identity['files']],diff=dict(files=3,insertions=60,deletions=6,sha256=identity['sha256']),
 behavior='Removed redundant standalone ensure from scoped produce/verify. Guarded discovery provisions/admit caches before creating persistent logs; standalone refresh semantics, cache guards and report/source/axiom checks remain intact.',
 focused_tests=dict(passed=34,failed=0,cache_guard=24,scoped_contracts=8,native_regressions=2,command_evidence=str(p)),
 real_acceptance=dict(produce_command='LEAN_NUM_THREADS=1 make lean-report-scoped LEAN_TARGETS=D5.S0.Automata.DFAOStateLowerBound',produce_exit=0,
 verify_command='/bin/bash tools/scripts/report/lean-report-input.sh verify-scoped --repository '+str(root)+' --report '+str(root/'.lake/build/stratalint/scoped-lean-report.json')+' --targets D5.S0.Automata.DFAOStateLowerBound',verify_exit=0,
 platform='Darwin arm64; Lean 4.35.0; native inspector Mach-O arm64',modules=1,declarations=45,report_sha256=acceptance['report_sha256'],
 archive_status='not_attempted',archive_age_hours=round(acceptance['archive_age_hours'],3),refresh_marker_unchanged=True,
 accepted_axioms=acceptance['accepted_axioms'],evidence=str(acceptance_path)),
 iteration_answer='No additional cache-admission or source-evidence obligation was found: existing guarded discovery supplies admission. Real first-seed validation exposed the default-log-directory replacement obligation, which is fixed and regression-tested.',
 resolved_failures=['Initial cache-seeding log-directory loss; initial 120-second native consumer-fixture timeout (focused rerun passed); observer timestamp parsing after successful real commands. Exact evidence is in verification-summary.json.'],
 remaining_implementation_issues=[],limitations=summary['limitations'],lifecycle=summary['lifecycle'],cleanup=summary['cleanup'])
envelope={'conclusion':conclusion,'log_ref':str(diagnostic_path)}
attempt=Path('/Users/macstudio/.sshx/6ada53b5b4af5544ba3ebeba/attempt-1')
result_tmp=attempt/'result.json.tmp'
with result_tmp.open('w') as f:
 json.dump(envelope,f,ensure_ascii=False,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
result_tmp.replace(attempt/'result.json')
sentinel_tmp=attempt/'completion.sentinel.tmp'
with sentinel_tmp.open('w') as f:
 f.write('completed\n');f.flush();os.fsync(f.fileno())
sentinel_tmp.replace(attempt/'completion.sentinel')
print(json.dumps(envelope,ensure_ascii=False))
