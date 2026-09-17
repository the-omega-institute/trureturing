#!/usr/bin/env python3
"""Exact-context tests, not tests on the complete 998827-byte original volume."""
import difflib
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('apply_st', HERE/'apply_ST0_ST26.py')
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
chunks = mod.load_chunks(HERE)
# Exact six-line context was read from the original; preceding lines are blank padding.
context = '[4]: https://arxiv.org/abs/1205.0710?utm_source=chatgpt.com "Heavy fields, reduced speeds of sound and decoupling during inflation"\n[5]: https://arxiv.org/abs/hep-th/9807099?utm_source=chatgpt.com "Towards a Relativistic KMS Condition"\n[6]: https://arxiv.org/abs/1403.7377?utm_source=chatgpt.com "The Confrontation between General Relativity and Experiment"\n# 钟记录、径向俘获与视界红移\n\n## ——量子观察者—关系时空理论第三十一至第四十节增订\n'
base = b'\n'*3414 + context.encode('utf-8')
sha = mod.blob_sha(base)
combined = b''.join(chunks)
expected = base.replace(mod.ANCHOR, combined+mod.ANCHOR, 1)
checks = []
with tempfile.TemporaryDirectory() as tmp:
    directory = Path(tmp)
    for i, row in enumerate(mod.CHUNKS):
        (directory/row[0]).write_bytes(chunks[i][:-1] if i == 0 else chunks[i])
    assert mod.load_chunks(directory) == chunks
    checks.append('known_remote_blank_line_normalization')
    (directory/mod.CHUNKS[2][0]).write_bytes(chunks[2]+b'changed')
    try:
        mod.load_chunks(directory)
    except ValueError:
        checks.append('chunk_integrity_rejection')
    else:
        raise AssertionError('edited chunk admitted')
for n in range(4):
    current = base.replace(mod.ANCHOR, b''.join(chunks[:n])+mod.ANCHOR, 1)
    result, count = mod.plan(current, chunks, sha)
    assert result == expected and count == n
    assert result.replace(combined, b'', 1) == base
    checks.append(f'prefix_{n}_preservation')
bad = {
    'source-drift': b'changed\n'+base,
    'wrong-order': base.replace(mod.ANCHOR, chunks[1]+chunks[0]+mod.ANCHOR, 1),
    'missing-first': base.replace(mod.ANCHOR, chunks[2]+mod.ANCHOR, 1),
    'duplicate': base.replace(mod.ANCHOR, chunks[0]*2+mod.ANCHOR, 1),
    'edited': base.replace(mod.ANCHOR, chunks[0].replace(b'ST0',b'edited',1)+mod.ANCHOR, 1),
    'wrong-location': chunks[0]+base,
    'intervening-text': base.replace(mod.ANCHOR, chunks[0]+b'change\n'+mod.ANCHOR,1),
    'lost-anchor': base.replace(mod.ANCHOR,b''),
}
for name, current in bad.items():
    try:
        mod.plan(current, chunks, sha)
    except ValueError:
        checks.append('rejected_'+name)
    else:
        raise AssertionError(name)
# A test fixture must fail under the actual reviewed blob guard.
try:
    mod.plan(base, chunks)
except ValueError:
    checks.append('real_guard_rejects_fixture')
else:
    raise AssertionError('fixture wrongly admitted as complete original')
(HERE/'QUANTUM-REALITY.ST0-ST26.combined.insert.md').write_bytes(combined)
base_name = 'docs/develop/theory/QUANTUM-REALITY.md'
for label, prior in [('ST0-ST26',b''),('ST19-ST26',b''.join(chunks[:2]))]:
    before = base.replace(mod.ANCHOR,prior+mod.ANCHOR,1)
    patch = ''.join(difflib.unified_diff(before.decode().splitlines(True),
                    expected.decode().splitlines(True), fromfile='a/'+base_name,
                    tofile='b/'+base_name,n=5)).encode()
    path = HERE/f'QUANTUM-REALITY.{label}.patch'
    path.write_bytes(patch)
    with tempfile.TemporaryDirectory() as tmp:
        root=Path(tmp)
        target=root/base_name
        target.parent.mkdir(parents=True)
        target.write_bytes(before)
        subprocess.run(['git','init','-q',str(root)],check=True)
        subprocess.run(['git','-C',str(root),'apply','--check',str(path)],check=True)
        subprocess.run(['git','-C',str(root),'apply',str(path)],check=True)
        assert target.read_bytes()==expected
        checks.append('fixture_patch_applied_'+label)
result={'status':'passed','checks':checks,'count':len(checks),
        'scope':'Exact insertion-context fixture only. Complete original was unavailable.',
        'reviewed_original_blob':mod.BASE_BLOB,'fixture_blob':sha,
        'combined_bytes':len(combined),'combined_sha256':hashlib.sha256(combined).hexdigest()}
(HERE/'insertion_checks_ST26.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(result,ensure_ascii=False,indent=2))
