# A397902 implementation attempt

Origin: Codex implementation worker, using the local `lean4` skill. Single worker;
no independent review or multi-model consensus is claimed. User supplied the
literature adjudication and probe expectations; measurements below were run here.
Base: `0011b3f0dfdd9eb32b753d122219f0749927922a`, branch `lane/math/a397902`.
Tier: 第一档. Target: all n > 2, for the zero-constant integer formal series in
the OEIS NAME. Rational construction does not discharge integer existence.

## Numerical probe (not a theorem or mathematical progress)

The exact recurrence from the task was run in Python arbitrary-precision integers,
N=90. Both divisions were asserted before taking each quotient. Results:
4095 successful j-divisions; 90 successful e-divisions; first 16 coefficients
match the live OEIS DATA individually; 0 conjecture mismatches for n=3..90;
70 even coefficients. Actual odd indices:
`3,4,5,6,7,8,13,14,15,16,29,30,31,32,61,62,63,64`.
Negative control: explicitly use the wrong predicate `False`; 18 mismatches.
The user's wrong predicate was unspecified, so equality is of mismatch counts,
not a claim that the two negative-control predicates were identical.
Measured recurrence runtime: 0.034471667 s on this worktree host.

OEIS request: https://oeis.org/search?q=id:A397902&fmt=text
HTTP 200, 2734 bytes, SHA-256
`eac596ae2bcf450245d98d5bb3ef4106b4ce2945b721165bee45dfab40bdc9c5`.
Read NAME, Conjecture, DATA, formulas, author and cross-references directly.
The fetched text labels the parity assertion Conjecture and links only the b-file.
Asymptotics do not assert parity. No conclusion is transferred from A397591,
A397596, A397594 or A397592.
Raw response and probe output are in the runner attempt directory.

## Search and proof status

D5 exact text search for A397902, A397594, A397592, A397591, A397596: no matches
(`rg`, exit 1). Pinned mathlib: v4.33.0,
`db584cd6d46c92f209a44c0f1c829460d327499d`.
Further library searches and Lean proof work are pending.

## Not claimed

No all-n theorem, integer existence proof, counterexample, freeze, coverage,
build success or PR is claimed at this checkpoint. The numerical probe is only
an instrument check. User-reported arXiv evidence has not yet been re-fetched;
its origin remains user input, not a worker measurement.
