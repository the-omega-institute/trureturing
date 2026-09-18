"""Delete the live potential lemma and attempt to finish from finite-orbit facts.

The generated mutant is deliberately expected to fail. Keep the transformation,
not a duplicate snapshot of the proof. Run only after make lean-cache-ensure.
"""
import json
from pathlib import Path
import subprocess

source = Path('probe/SyyProbe.lean').read_text()
start = source.index('private theorem potential_weak')
end = source.index('/-- Shieh–Yang–Yu Conjecture 6.2', start)
mutant = source[:start] + source[end:]
old = '  have hwk := potential_weak u ndu'
assert mutant.count(old) == 1
mutant = mutant.replace(old, '  have hwk : Phi u ≤ Phi (M u) := by\n    aesop')
assert 'potential_weak' not in mutant
path = Path('probe/.SyyMutant.lean')
log = Path('/var/folders/rm/8w0nylc12d909d_tl053wqkw0000gn/T/consensus-rnd/sshx/s6c2e-probe-syy-cycles-probe/attempt-1/scratch/mutant.log')
try:
    path.write_text(mutant)
    run = subprocess.run(['lake', 'env', 'lean', str(path)], text=True, capture_output=True)
    log.write_text(run.stdout + run.stderr)
    errors = '\n'.join(line for line in run.stdout.splitlines() if 'error' in line or '⊢' in line)
    results = dict(compiled=run.returncode == 0, exit=run.returncode,
                   mutation='Delete potential_weak; replace its use by aesop on remaining finite-orbit context.',
                   retained='All source definitions, operational lemmas, permutation invariance, orbit finiteness, maximal reachable potential.',
                   removed='The strong induction proving Phi u <= Phi (M u).',
                   diagnostics=errors, log=str(log))
    Path('probe/mutant_result.json').write_text(json.dumps(results, indent=2)+'\n')
    print(json.dumps(results, indent=2))
    # An elaboration failure from a missing tactic would not test the witness.
    assert run.returncode != 0, 'Mutant compiled: witness fails this test.'
    assert 'aesop' in run.stdout and ('failed' in run.stdout or 'unsolved goals' in run.stdout)
    assert 'Unknown' not in run.stdout
finally:
    path.unlink(missing_ok=True)
