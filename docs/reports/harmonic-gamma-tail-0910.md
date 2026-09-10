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


## Library and bind-only receipts

Read `CLAUDE.md` completely in chunks and `agents/CONTEXT.md`. The tree is already a
registered task worktree; the initial branch and base were equal. Preregistration commit:
`68ca382e1a`, pushed before Lean probes.

Search order: D5, pinned Mathlib, GitHub Lean ecosystem, then local analytic proof.
`rg -n '\b(eulerMascheroni\w*|\w*eulerMascheroni\w*)\b' D5` returned 139 matching
lines. The narrower `\beulerMascheroni\w*\b` has 35 / 8 / 6 matching lines in
`RobinRationalBasis` / `Robin/PaddingRatio` / `Robin/SevenSmooth`, confirming the brief.
Positive controls with the same `\b` feature found the existing remainder and decimal
theorems. Read the full RobinRationalBasis module: its uniform bracket is
`1/(2*(N+1)) < H_N-log N-γ < 1/(2*N)` and its decimal upper endpoint is 0.5772161.
Other matches include coarse first-Li-coefficient positivity and harmonic residual limits;
none of the examined statements supplies the requested correction.

Mathlib pin: `db584cd6d46c92f209a44c0f1c829460d327499d` (v4.33.0).
A whole-Mathlib regex including both sides of eulerMascheroni names and the positive control
`log_two_(gt|lt)_d9` returned 76 lines. Direct γ numeric bounds are exactly
`Real.one_half_lt_eulerMascheroniConstant` and
`Real.eulerMascheroniConstant_lt_two_thirds`; the two log-2 controls were found.
Also read EulerMascheroni.lean and inspected Harmonic/Bounds and Gamma-related candidates.
The upper-sequence lemma's actual name ends in a prime:
`Real.eulerMascheroniConstant_lt_eulerMascheroniSeq'`.
No pre-existing high precision γ bound or fourth-order harmonic tail was found in this scope.

GitHub code search capability: `gh api -X GET search/code -f q=... -f per_page=100`
now succeeds (exit 0). Queries and counts (`incomplete_results=false` for each):
`eulerMascheroniConstant language:Lean` → 72;
`"harmonic" "120" language:Lean` → 5;
`"harmonic" "12" "log" language:Lean` → 45;
`57721566 language:Lean` → 5.
Inspected bencinn/all-math's EulerMascheroniMathlib.lean at
`4bd71f262ec4395ceeb17cf1a437b0607e3a6a15`: an uncorrected series identity only.
DLorell/stoch_to_det Constants.lean at `299c75264b07db05eab8e6d232ef88e0988f4790`
uses the original lower approximants at 255 and 2499; no target upper bound.
The other decimal hits define Float literals, not bounds for the Mathlib real constant.
The former authorization failure is not present here. These are bounded indexed queries,
not a claim of exhaustive coverage of all third-party Lean code.

The first Lean probe imported only RobinRationalBasis (and its Mathlib closure), specialized
its two brackets and Mathlib's two approximants, unfolded the sequence definitions, then used
`linarith only` with `sq_nonneg`. Both targets failed with `linarith failed to find a contradiction`;
exit 1. This is a concrete failed bind-only attempt, not a formal impossibility proof.
`make lean-cache-ensure` returned `status=present`, both olean layers warm and no stamp miss;
only thereafter were hot-tree `lake env lean` incremental probes used. No naked lake build.

## Independent derivative derivation

Differentiating each term gives
`f' = -1/(x*(x+1)) + 1/(2*x^2) + 1/(2*(x+1)^2)
      - 1/(6*x^3) + 1/(6*(x+1)^3)`.
For `f-w`, add `1/(30*x^5) - 1/(30*(x+1)^5)`.
With x > 0, Lean `field_simp` followed by `ring` verifies respectively
`-1/(6*x^3*(x+1)^3)` and `(5*x^2+5*x+1)/(30*x^5*(x+1)^5)`.
Derivative algebra probe exit 0. No discrepancy with the brief. The second identity is an
auxiliary verification record only; the full upper-tail inequality remains out of scope.

## Provenance inspection

DLMF §5.11 equation (5.11.2) gives the digamma asymptotic expansion. Section (ii) states
that for positive real inputs its truncated remainder has the same sign as the first
omitted term and is bounded by its magnitude. Retrieved https://dlmf.nist.gov/5.11 on
2026-09-10. The repository already has supported LibraryNoteRef and FromLiterature calls,
so no fallback obstacle was observed. A citation-only L-plane note will record this source.
