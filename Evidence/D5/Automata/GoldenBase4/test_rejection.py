"""Negative tests for the two certificate checkers. No solver is required."""
from __future__ import annotations
import json
from pathlib import Path
import subprocess
import tempfile
from check_gap3_proof import replay

root=Path(__file__).resolve().parent
reports=[]
with tempfile.TemporaryDirectory() as tmp:
    tmp=Path(tmp)
    source=(root/'machine21.tsv').read_text()
    # A legal but incorrect destination in row 1 must violate interval transport.
    rows=source.splitlines(); fields=rows[1].split(); fields[3]='0'; rows[1]=' '.join(fields)
    bad=tmp/'wrong_transition.tsv'; bad.write_text('\n'.join(rows)+'\n')
    p=subprocess.run([str(root/'check21'),str(bad)],capture_output=True,text=True)
    assert p.returncode!=0, 'C++ checker accepted a wrong transition'
    reports.append({'test':'wrong_21_state_transition','rejected':True,'diagnostic':p.stderr.strip()})
    cases=[]
    proof=(root/'gap3_refutation.txt').read_text()
    cases.append(('incomplete_branch_domain', (root/'gap3_core_rows.tsv').read_text(), proof.replace('B 0 7','B 0 3',1)))
    cases.append(('false_contradiction_leaf',(root/'gap3_core_rows.tsv').read_text(),proof.replace('B 0 7','L',1)))
    cases.append(('truncated_refutation',(root/'gap3_core_rows.tsv').read_text(),proof.rsplit('P 7',1)[0]))
    badrows=(root/'gap3_core_rows.tsv').read_text().replace('0 2 0\n','0 1 0\n',1)
    cases.append(('wrong_exact_digit',badrows,proof))
    for name,rr,pp in cases:
        rp=tmp/'rows.tsv';pf=tmp/'proof.txt';rp.write_text(rr);pf.write_text(pp)
        try:
            replay(rp,pf)
        except (ValueError,StopIteration) as e:
            reports.append({'test':name,'rejected':True,'diagnostic':str(e) or type(e).__name__})
        else:
            raise AssertionError(f'Checker accepted mutation: {name}')
result={'status':'PASS','negative_tests':reports,'independent_reviewer':False,'lean_kernel_checked':False}
(root/'rejection_tests.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
