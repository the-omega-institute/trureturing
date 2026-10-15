"""Emit and independently bind the complete original Lean DAG input."""
import json
import pathlib
import shutil
import subprocess
import time

s=pathlib.Path(__file__).resolve().parent
cp=pathlib.Path('/Users/macstudio/omega/.formalization-goal-01a12631/checkpoints/ejm-mdd-global/existing-cover-original-suffix-alignment-20261014')
out=cp/'original-source-identity-stream'
started=time.time()
for name in ['emit-original-global-dag.py','check-original-global-dag-source.py',pathlib.Path(__file__).name]:
    shutil.copy2(s/name,cp/name)
subprocess.check_call(['python3',str(s/'emit-original-global-dag.py')])
subprocess.check_call(['python3',str(s/'check-original-global-dag-source.py')])
record=dict(status='complete_original_Lean_DAG_source_bound_not_kernel',
    binding=json.loads((out/'original-global-dag-source-binding.json').read_text()),elapsed_seconds=time.time()-started)
(out/'data40-result.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(dict(status=record['status'],elapsed_seconds=record['elapsed_seconds'])),flush=True)
