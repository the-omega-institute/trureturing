import collections
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import time

root = Path.cwd()
logs = root / '.worker-validation'
evidence = Path('/Users/macstudio/omega/research/open-problem-search-20261016/scoped-report-cache-refresh-fix-20261023')
evidence.mkdir(parents=True, exist_ok=True)
report = root / '.lake/build/stratalint/scoped-lean-report.json'
marker = root / '.lake/build/.release-refreshed-at'
donor_marker = Path('/Users/macstudio/omega/trureturing/.lake/build/.release-refreshed-at')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
now = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat()
result = dict(started_at=now(), worktree=str(root), base=subprocess.check_output(['git','rev-parse','HEAD'], text=True).strip(),
    common_git=subprocess.check_output(['git','rev-parse','--git-common-dir'],text=True).strip(),
    platform=dict(system=platform.system(), machine=platform.machine()), toolchain=(root/'lean-toolchain').read_text().strip(),
    roots=['D5.S0.Automata.DFAOStateLowerBound'], environment_overrides={'LEAN_NUM_THREADS':'1'}, commands=[],
    disk_before=shutil.disk_usage(root)._asdict(), donor_marker_before=donor_marker.read_text() if donor_marker.is_file() else None,
    worktree_marker_before=marker.read_text() if marker.is_file() else None)
env = dict(os.environ, LEAN_NUM_THREADS='1')

def run(name, args, observations=False):
    local = dict(env)
    if observations:
        local.update(STRATALINT_INSPECTOR_PHASES=str(logs / (name+'-phases.jsonl')),
                     STRATALINT_INSPECTOR_CHILD_STDOUT=str(logs / (name+'-child-stdout')),
                     STRATALINT_INSPECTOR_CHILD_STDERR=str(logs / (name+'-child-stderr')))
    path = logs / (name+'.log')
    started = time.monotonic()
    print('START '+name, flush=True)
    with path.open('wb') as out:
        status = subprocess.run(args, cwd=root, env=local, stdout=out, stderr=subprocess.STDOUT).returncode
    result['commands'].append(dict(command=args, exit=status, seconds=time.monotonic()-started, log=str(path), log_sha256=sha(path)))
    print('EXIT '+name+' '+str(status), flush=True)
    if status:
        raise RuntimeError(name+' exit '+str(status))

try:
    run('real-produce', ['make','lean-report-scoped','LEAN_TARGETS=D5.S0.Automata.DFAOStateLowerBound'], True)
    result['worktree_marker_after_produce'] = marker.read_text() if marker.is_file() else None
    run('real-verify', ['/bin/bash','tools/scripts/report/lean-report-input.sh','verify-scoped', '--repository',str(root),
                      '--report',str(report),'--targets','D5.S0.Automata.DFAOStateLowerBound'], True)
    value = json.loads(report.read_text())
    assert value['schema'] == 'stratalint-scoped-lean-report-v1'
    rows = value['modules']
    assert any(row['module']==result['roots'][0] for row in rows)
    axioms = sorted({a for row in rows for d in row['declarations'] for a in d['axioms']})
    assert set(axioms) <= {'propext','Classical.choice','Quot.sound'}, axioms
    for row in rows:
        assert row['source_sha256'] == 'sha256:'+sha(root/row['source_path'])
    result.update(modules=[row['module'] for row in rows], declarations=sum(len(row['declarations']) for row in rows), accepted_axioms=axioms)
    receipts=[]
    for name in ('scope.stdout.log','report.stdout.log'):
        for line in (Path(str(report)+'.logs')/name).read_text().splitlines():
            if line.startswith('LEAN_CACHE '): receipts.append(dict(phase=name, **json.loads(line[len('LEAN_CACHE '):])))
    verify_receipts=[json.loads(line[len('LEAN_CACHE '):]) for line in (logs/'real-verify-child-stdout.cache').read_text().splitlines() if line.startswith('LEAN_CACHE ')]
    assert receipts and verify_receipts
    assert all(row['archive_status']=='not_attempted' for row in [*receipts,*verify_receipts])
    assert all(row['project_olean_state']=='warm' and row['mathlib_olean_state']=='warm' for row in [*receipts,*verify_receipts])
    result.update(cache_receipts=receipts, verify_cache_receipts=verify_receipts,
        work=json.loads((Path(str(report)+'.logs')/'work.json').read_text()),
        worktree_marker_after=marker.read_text() if marker.is_file() else None,
        donor_marker_after=donor_marker.read_text() if donor_marker.is_file() else None)
    assert result['donor_marker_before']==result['donor_marker_after']
    assert result['worktree_marker_after_produce']==result['worktree_marker_after']
    age=datetime.datetime.now(datetime.timezone.utc)-datetime.datetime.fromisoformat(result['worktree_marker_after'].strip())
    result['archive_age_hours']=age.total_seconds()/3600
    assert result['archive_age_hours']>6
    products=[]
    for suffix in ('','.sha256','.input.attestation','.provenance.json','.materials.zip'):
        source=Path(str(report)+suffix)
        target=evidence/source.name
        shutil.copyfile(source,target)
        products.append(dict(path=str(target), bytes=target.stat().st_size, sha256=sha(target)))
    result.update(products=products, status='passed')
except Exception as error:
    result.update(status='failed',error=repr(error))
finally:
    result.update(finished_at=now(), disk_after=shutil.disk_usage(root)._asdict())
    target=evidence/'darwin435-scoped-acceptance.json'
    temporary=target.with_suffix('.json.tmp')
    temporary.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    temporary.replace(target)
    print(json.dumps(dict(status=result['status'],evidence=str(target),error=result.get('error'))),flush=True)
sys.exit(0 if result['status']=='passed' else 1)
