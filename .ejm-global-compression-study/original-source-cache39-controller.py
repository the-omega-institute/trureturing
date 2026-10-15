"""Reproduce the actual existing incremental cache over the complete DAG."""
import json
import pathlib
import shutil
import subprocess
import time

s=pathlib.Path(__file__).resolve().parent
cp=pathlib.Path('/Users/macstudio/omega/.formalization-goal-01a12631/checkpoints/ejm-mdd-global/existing-cover-original-suffix-alignment-20261014')
out=cp/'original-source-identity-stream'
started=time.time()
for name in ['prepare-incremental-cache-inputs.py','check-original-incremental-cache.cpp',pathlib.Path(__file__).name]:
    shutil.copy2(s/name,cp/name)
subprocess.check_call(['python3',str(s/'prepare-incremental-cache-inputs.py')])
subprocess.check_call(['/usr/bin/clang++','-isysroot','/Library/Developer/CommandLineTools/SDKs/MacOSX26.5.sdk',
    '-std=c++17','-O3',str(s/'check-original-incremental-cache.cpp'),'-o',str(s/'check-original-incremental-cache')])
subprocess.check_call([str(s/'check-original-incremental-cache'),str(out)])
result=json.loads((out/'actual-incremental-cache-check.json').read_text())
record=dict(status='actual_incremental_cache_complete_DAG_native_not_kernel',result=result,elapsed_seconds=time.time()-started)
(out/'cache39-result.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record),flush=True)
