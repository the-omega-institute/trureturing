# Harmonic–log signed tail: implementation record

Origin: no skill; Codex main loop implements and self-checks. No independent review seats.
Worktree: `/Users/auricstudio/trureturing-robin7smooth-0909`.
Branch: `lane/math/harmonic-gamma-tail-0910`.
Initial HEAD and origin/dev: `248a800843acf89ed184074d66a8d577fc028f99`.
Scope: implementation only; no deposit, cover, or PR.

## Preregistration v1 (before Lean probes)

Question answered: for every natural N ≥ 1, prove
`1/(2*N) - 1/(12*N^2) < (harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant`.
The named companion specializes at N = 128 to prove `γ < 5772156650/10^10`.
The full two-sided fourth-order remainder estimate is outside this attempt.

Proposed `escape_witness`: a uniform signed harmonic–log tail estimate obtained from the
strict decrease of `q_N = H_N - log N - 1/(2*N) + 1/(12*N^2)` and its limit γ.
The live intermediate fact is positivity of the one-step corrected gap on all positive
real inputs, followed by strict sequence monotonicity and a limit comparison retaining
the first strict gap (equivalently, a telescoping infinite tail).
Pure numeric arithmetic and derivative algebra are explicitly not the witness.

Predicted `proof_shape`: main theorem content; companion inherits the main theorem's live
analytic derivation and is not a separate numerical delivery.
Proposed `admission_basis`: escape-witness, conditional on observing the stated live path.
Companion obligation: the explicit ten-digit upper bound in the task brief.
Directed edge (consumer → prerequisite): companion γ upper bound → uniform tail theorem.
Proposed `utility`: general analytic estimate with a named numeric companion; no standalone
checker, bounded enumeration, or certified finite instance module.

First attempt only Mathlib instantiation, frozen projections, and normalization (including
`sq_nonneg` and `linarith only`). If an existing high precision γ bound or fourth-order
tail estimate is found, stop as bind-only without a module. A changed witness requires
a new preregistration before testing it.

Provenance: classical Euler–Maclaurin mathematics; no novelty claim. Investigate an L-plane
note and `FromLiterature`; if no supported note mechanism is available, use the explicitly
authorized `FromRepo()` fallback and disclose its scope in the Scribe prose.

Downstream limitation: `RobinRationalBasis.robinPositiveJudge_sound` already accepts a coarse
`hgamma` witness and does not explicitly require ten-digit precision. This is an allowed
tightening, not a documented missing prerequisite of that consumer. Its frozen module
statement_id is `sha256:6dcafd483a23c78180a3518807013e46c0dccfcb211d2d5f442207eb1ee621c2`
(to be read from the existing state record).

Completion criteria: both target theorems, Lean build/report, Scribe and emitted mirror,
governance-word self-scan with positive control, local gate, and stepwise commit/push.
Stop honestly if the minimum slice cannot be completed; never deliver only derivative
identities or an isolated positive numerical instance.
