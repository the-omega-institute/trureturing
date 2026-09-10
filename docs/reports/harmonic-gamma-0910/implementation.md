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
Derivative algebra probe exit 0. A separate strengthened audit also proves both actual
`HasDerivAt` statements for the original `log(1+x⁻¹)` expression, by independently applying
the chain rule before `field_simp` and `ring`; exit 0, standard three axioms only.
Receipts: `HarmonicDerivativeAudit.lean` and `harmonic-gamma-derivative-audit.log` in the
attempt directory. No discrepancy with the brief. The second identity is an auxiliary
verification record only; the full upper-tail inequality remains out of scope.

## Provenance inspection

DLMF §5.11 equation (5.11.2) gives the digamma asymptotic expansion. Section (ii) states
that for positive real inputs its truncated remainder has the same sign as the first
omitted term and is bounded by its magnitude. Retrieved https://dlmf.nist.gov/5.11 on
2026-09-10. The repository already has supported LibraryNoteRef and FromLiterature calls,
so no fallback obstacle was observed. The citation-only L-plane note records this source.


## Implemented result and witness comparison

The two public statements are now kernel checked in
`D5/S3/Arith/GoldenResource/HarmonicGammaTail.lean`.

| Public theorem | proof_shape | Direct frozen dependencies | escape_witness | admission_basis |
| --- | --- | --- | --- | --- |
| harmonic_log_tail_lower | content | none (GID/statement_id: not applicable) | step_gap_pos → corrected_seq_strictAnti with corrected_seq_tendsto | escape-witness |
| eulerMascheroni_upper_128 | content after inlining its new main theorem; local specialization is arithmetic | none (GID/statement_id: not applicable) | the same live analytic path through harmonic_log_tail_lower at 128 | escape-witness (named companion) |

The observed witness agrees with preregistration v1. The implementation uses the equivalent
monotone-limit form of the telescoping argument: the consecutive corrected difference is
positive and `γ ≤ q_(N+1) < q_N`. Thus the first strict gap is retained, with no separate
infinite-sum definition. Neither derivative identity is exposed as a public deliverable.
The main theorem handles every N ≥ 1. The numerical companion has no γ premise: its
12-term lower logarithm sum and the 128-term harmonic sum are evaluated in Lean.

Directed obligation edge (consumer → prerequisite):
`D5/S3/Arith/GoldenResource/HarmonicGammaTail.eulerMascheroni_upper_128`
→ `D5/S3/Arith/GoldenResource/HarmonicGammaTail.harmonic_log_tail_lower`.
This is the task brief's named numerical companion, not a separate finite-instance module.
The corrected sequence is stored at index n as q_(n+1) to keep all denominators positive.

`utility: none`: the primary new mathematical content of both public declarations, after
inlining, is the uniform analytic estimate. The second is its expressly requested named
corollary. There is no new checker, numerical-reduction infrastructure, bounded-enumeration
result, or independently delivered certified finite instance. The rational computations
supply no independent escape claim. The numeric companion exception is explicitly scoped
by the user brief; this record does not propose a general positive-instance exception.

No frozen module is imported: the proved statement uses Mathlib's existing harmonic limit
directly, so the new dependency list is empty. The existing Robin module state was read and
matches the brief's statement_id. Its identity is a downstream contextual anchor, not a
claimed proof dependency. The earlier honest limitation about its coarse hgamma remains.

Provenance implementation: `Library/Analytic/nist2026asymptotic.md` supplies the supported
L-plane note `D5/L/Analytic/nist2026asymptotic`. The uniform classical result uses
`FromLiterature`; the newly calculated named corollary uses `FromRepo(Source)` to attribute
its derivation to that same literature basis without pretending the source printed N=128.
No unsupported-note obstacle and no unreferenced fallback occurred; no suspected-novel label.

Validation so far: the complete probe and the formal module both report only
`[propext, Classical.choice, Quot.sound]` for both public theorems. `make lean` completed
successfully (12912 jobs; cache present and warm). During packaging an initial module-doc
comment before imports and mistaken FormulaDsl constructor names were corrected. The first
`make emit` refused a stale report, correctly requiring `make lean-report` first; no bypass.
The formal module currently contains 2 public theorems and 8 private helpers/definitions.
`make lean-report` then completed with exit 0; the canonical inspector found both target
declarations with only the standard three axioms. The full report hash is
`sha256:6c196d0d6a1e17e8ffa108fa85459d81b2257ed7b98a5f81daaaca268ed81137`.
The target module extract is saved as `lean-report-module.json` in the attempt directory.
The public declaration statement identities are:

- `harmonic_log_tail_lower`: `sha256:c5dd4b35decb8df3d6bb8483fb3b20d1e6c99516fa109dc118d08fce16329c3f`.
- `eulerMascheroni_upper_128`: `sha256:08aacf51441e127037d707f4f29261fa35b9cdf2dfaadbbab9d91924783912e1`.

`make emit` completed with exit 0 and generated the required
`Blueprint/D5/S3/Arith/GoldenResource/HarmonicGammaTail.md`. Both formulae, the `✓ std3`
markers, the literature citation, and the corollary's repository derivation were checked.
Only this new Blueprint mirror is a tracked emission change. Local gate receipts follow below.


## Gate capacity correction

The first full `make gate BASE=248a800843acf89ed184074d66a8d577fc028f99` completed
its engineering build, full tests (760 s), selftest, and Lean report phases successfully,
but rejected the two new files at their initial locations: `Library/Arith` and
`docs/reports` each contained 49 files, exceeding the admission limit of 48 (SL-003).
The inner gate exited 1; make returned 2. SL-032 passed. The Scribe source also has the
ordinary SL-022 protected-surface classification.

Moved only this attempt's new literature note to the existing `Library/Analytic` bucket
and this report to `docs/reports/harmonic-gamma-0910/implementation.md`; updated the
LibraryNoteRef accordingly. No mathematical declaration or proof changed. The original
full-gate log is retained as `harmonic-gamma-gate-initial.log`. The subsequent gate rerun
uses the supported `GATE_ARGS=--skip-engineering`, preserving the already successful full
engineering receipt while rerunning report validation, Scribe, and admission for the
corrected paths. No harness or policy changes were made.


## Final validation and delivery

The corrected `make emit` exited 0; the rendered Blueprint bytes did not change because
only the citation note's bucket changed. Final `make gate
BASE=248a800843acf89ed184074d66a8d577fc028f99 GATE_ARGS=--skip-engineering` ran at commit
`675eddc7a1`, exited 0 in 121 s, and passed all content checks, including SL-003 and SL-032.
The supported rerun reused the successful full engineering run described above. Its
protected-surface classification is SL-022 for the Scribe source; local gate explicitly
reports `protected-surface change (SL-022); content checks passed` and returns success.
This is a local validation receipt, not a claim of PR or CI approval.

Nonblocking observations remain honest: SL-031 reports `utility: none` with
`semantics=unverified-by-machine`, so the per-theorem content classification above is the
main loop's mathematical assessment. SL-034 observes the absent frozen state; this is
expected for the requested implementation-only delivery without deposit. No module was
frozen, no coverage was written, and no PR was opened. The full two-sided fourth-order
remainder bound was not implemented. No independent review seats were used.

The final Scribe self-scan used `rg -n -i -P` with this regex:

```
\b(?:issue\s*#?\s*\d{3,}|PR\s+#\d+|pull\s+request|panel\s+brief|dispatch\s+brief|orchestrator|six-route|proof_shape|admission_basis|escape[ _-]witness|bind-only|postmortem|git-history|accepted-event\s+receipts?|search(?:es)?|duplicate)\b
```

It returned exit 1 with empty output (zero forbidden matches). The positive control
`rg -n -P '\bMathlib\b'` on the same file returned exit 0 and matched line 26.
The full receipt, including the final Scribe source SHA-256, is `scribe-scan.json` in the
attempt directory. `git diff --check` also passed.

Stepwise commits were pushed: `68ca382e1a` preregistration, `743d11d0b4` library/derivative
receipts, `ac6f1f3acd` the completed Lean module/Scribe/L-note, `93eebec807` emitted mirror,
and `675eddc7a1` the directory-capacity correction. The final report-only receipt commit
is recorded, with the remote HEAD and a clean-tree check, in the runner result envelope.
The final receipt commit does not alter Lean, Scribe, the Blueprint mirror, or the L-note.

Worker-owned artifacts are published under:
`/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/harmonic-gamma-0910/attempt-1`.
They include the full and corrected gate logs, build/report/emission logs, indexed-query
receipts, both derivative audits, the restricted binding probe, the canonical target-module
report extract, this report, and the final Scribe scan. The populated `result.json` is
published via `.tmp` and atomic rename before `completion.sentinel` is published the same
way. Its top level has exactly `conclusion` (object) and `log_ref` (nonempty string).
