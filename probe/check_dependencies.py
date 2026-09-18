"""Inspect the successful theorem's elaborated proof and its reduced proof term."""
import json
from pathlib import Path
import subprocess

source = Path('probe/SyyProbe.lean').read_text()
audit = r'''
run_cmd Lean.Elab.Command.liftTermElabM do
  let info ← Lean.getConstInfo ``result
  let some value := info.value? (allowOpaque := true)
    | throwError "No theorem proof value"
  let raw := value.getUsedConstants.contains ``potential_weak
  let reduced ← Lean.Meta.withTransparency .reducible
    (Lean.Meta.reduce value false false false)
  let live := reduced.getUsedConstants.contains ``potential_weak
  unless raw && live do
    throwError "Potential dependency disappeared: raw={raw}, reduced={live}"
  Lean.logInfo m!"POTENTIAL_DEPENDENCY raw={raw} reduced={live}"

'''
assert source.count('end SyyProbe') == 1
text = 'import Lean.Meta.Reduce\n' + source.replace('end SyyProbe', audit + 'end SyyProbe')
path = Path('probe/.SyyDependencyAudit.lean')
log = Path('/var/folders/rm/8w0nylc12d909d_tl053wqkw0000gn/T/consensus-rnd/sshx/s6c2e-probe-syy-cycles-probe/attempt-1/scratch/dependency-audit.log')
try:
    path.write_text(text)
    run = subprocess.run(['lake', 'env', 'lean', str(path)], text=True, capture_output=True)
    log.write_text(run.stdout + run.stderr)
    print(run.stdout + run.stderr)
    assert run.returncode == 0
    assert 'POTENTIAL_DEPENDENCY raw=true reduced=true' in run.stdout
    assert 'sorryAx' not in run.stdout
    result = dict(exit=0, direct_potential_dependency=True,
                  retained_after_reduction=True,
                  reduction='Lean.Meta.reduce with reducible transparency, explicitOnly=false, skipTypes=false, skipProofs=false',
                  log=str(log))
    Path('probe/dependency_result.json').write_text(json.dumps(result, indent=2)+'\n')
finally:
    path.unlink(missing_ok=True)
