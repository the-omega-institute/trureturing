# All-theta coherent-history Schmidt attempt (2026-09-09)

Provenance: no skill invoked by this worker; Codex implementation worker,
one source of judgment, no independent review or consensus claimed. The caller
uses the consensus-rnd/sshx attempt contract. LANE #6160. User-authorized scope:
attempt bind-only first, stop on success or a false source clause, publish a
report and PR without auto-merge. No deposit, cover, or freeze.

## Final Outcome

**Bind-only for the all-theta Schmidt target; stop rule 1 triggered.**
Run 05 of `make lean` exited 0. The checked probe is retained verbatim as
`docs/reports/schmidt-theta-0909-snippets.lean`, outside the D5 build glob.
There is no production module, deposit, cover, or freeze. This is a report
delivery, not a claim that the entire atom has been Lean-certified:
cross-theta orthogonality remains explicitly open in Lean.

| Source obligation | Checked result |
| --- | --- |
| (27), every real theta, source B(a,b), both phased sector families orthonormal | Proved in probe: `cross_area_count_formula`, `area_append`, `phased_factorization`, `phased_cut_sector_gram` |
| Every chronological prefix cut, every real theta, same Schmidt coefficients; (29) rank 12 at 4\|4 | Proved using actual `LinearMap.singularValues`: `all_theta_cut_singular_values`, `all_theta_cut_rank`, `all_theta_5040_rank` |
| Psi_0 orthogonal to Psi_(pi/4) | **Lean-open**; exact integer diagnostic gives overlap 0/840 = 0; not an assumed premise of any spectral result |
| Psi_0 and Psi_(pi/4) have the same entanglement spectrum and entropy | Proved for all pairs of real phases by `all_theta_cut_singular_values` and `all_theta_cut_entropy` |

The source scope is a finite ordered alphabet with one fixed occupation and
`a.card = t+s`; for 5040 it is (4,2,1,1), `k=0,...,8`, `t=k`, `s=8-k`.
No theta=0 restriction or extra unproved mathematical hypothesis was added.
The generic matrix identity also holds for unnormalized matrices; its use as
a normalized source state is guarded by the cardinality premise, checked in
`phased_state_normalized` and `normalization_positive`. All three multiplicities
are positive, as are the nonzero Schmidt coefficients. Entropy sums only over
the singular-value support; `entropy_log_argument_pos` checks each log argument
is positive. Mathlib defines singular values through a positive adjoint Gram
operator. There is no infimum in this probe.

The local phase factors are explicit: the left entry is
exp(i theta (A(u)+B(occ(u),a-occ(u)))); the right entry is exp(i theta A(v)).
They factor the actual phased coefficient matrix on its legal support.
`Matrix.charpoly_mul_comm` cancels the right unitary after the left unitary has
cancelled in the Gram matrix. The two Mathlib eigenvalue/charpoly iff theorems
and the existing singular-value formulas then identify the sorted sequences,
including multiplicities and trailing zero values. A global diagonal unitary
alone is insufficient; the fixed-occupation factorization is essential.

Proof shape is **bind-only**, `escape_witness: null`,
`admission_basis: not-applicable(user-stop-rule-1; report-only)`.
No independent new-content or novelty claim is made.

## Verified Artifact And Reproduction

Run 05 built the temporary path
`D5/S3/Quantum/Entanglement/SchmidtThetaProbe0909.lean` using `make lean`.
The file was then moved without changing its bytes to the report directory.
SHA-256: `69c39fe441633bb77ec6727b6faa7a108a16906eb3a24fee95a040263f2db061`.
The probe build's own job took 26 seconds according to Lean's build output;
this is not total wall time or a cold-build benchmark. Every one of the 19
printed theorem axiom closures is exactly
`[propext, Classical.choice, Quot.sound]`. The two remaining helper theorems
(`phase_add`, `phase_preserves_gram`) occur in those live dependency closures.
There is no `sorry`, `admit`, private axiom, or budget override in the checked file.
Unused-instance/hypothesis/simp-argument warnings remain in the probe; the build
exit code is 0, not a warning-free claim.

To reproduce, place the unchanged snippet bytes at the temporary D5 path above,
run `make lean`, and remove that temporary file afterwards. Do not register,
deposit, or freeze it. The normal build does not import the archived snippet.
Run `node docs/reports/schmidt-theta-0909-witnesses.mjs` for the separately
labelled finite diagnostic. Build and diagnostic logs are in the runner's
`schmidt-theta-0909/attempt-1` artifact directory.

## Per-Declaration Accounting

These are archived probe declarations, not public D5 additions. In every row:
`proof_shape=bind-only`, `escape_witness=null`, and the admission basis is the
report-only stop above. Utility kind is `none`: these are general identities,
normalization, or direct specialization of an existing rank theorem, with no
new checker, numeric reduction, bounded enumeration, or certified instance.

Direct frozen dependencies use these full pins:

- CHS: `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt`,
  `sha256:12fe938e662c8edbaeefb12298e5fc281e7f17595aafd457281a98bd63db1ca1`.
- OWS: `D5/S3/Quantum/Entanglement/OccupancyWordSectors`,
  `sha256:4c2e6fd9d41a26d9ddd554f91b64b4ed76e6b80ed308ee656970febafbbe55e1`.
  Scope: finite alphabet and fixed-length word sectors; normalization requires
  the occupation cardinality to equal the word length.

| Declaration | Direct frozen theorem use | Utility / live consumer |
| --- | --- | --- |
| `phase_star_mul` | none | Unit modulus for `phaseUnitary` and `phase_preserves_gram` |
| `unitary_gram_eigenvalues` | none | Sorted Gram eigenvalues for `all_theta_cut_eigenvalues` |
| `unitary_rank` | none | Rank for both all-theta rank consumers |
| `gram_toEuclideanLin` | none | Actual adjoint operator in `singular_values_of_gram_eigenvalues` |
| `singular_values_of_gram_eigenvalues` | none | Mathlib singular values in `all_theta_cut_singular_values` |
| `entropy_log_argument_pos` | none | Defined log domain for the entropy obligation |
| `cross_area_count_formula` | none | Source B formula in clause 1; a fidelity check |
| `area_append` | none | Definition/sum normalization for both phased factorizations |
| `phase_add` | none | Exponential normalization for both phased factorizations |
| `phased_matrix_local_factors` | OWS `occupation_append` | Local unitary matrices for all-theta spectral/rank consumers |
| `phased_factorization` | CHS `normalized_coefficient_factorization` | Equation (27) |
| `phase_preserves_gram` | none | Both phased orthogonality and whole-state normalization |
| `phased_cut_sector_gram` | CHS `cut_sector_gram` | Orthogonality in clause 1 |
| `phased_state_normalized` | OWS `multiplicity_pos`, `sector_gram` | Positive normalization and unit whole-state norm |
| `phased_matrix_is_state` | CHS `coefficient_eq_uniform_word` | Source's actual state-to-matrix connection |
| `all_theta_cut_eigenvalues` | none | Spectrum with multiplicity for all-theta singular values |
| `all_theta_cut_singular_values` | none | Clause 2 and entropy consumer |
| `all_theta_cut_entropy` | none | Entropy part of clause 3 |
| `all_theta_cut_rank` | CHS `coefficient_rank` | Every cut's rank |
| `all_theta_5040_rank` | CHS `history_5040_max_schmidt_rank` | Equation (29), all theta |
| `normalization_positive` | CHS `schmidt_coefficient_pos`; OWS `multiplicity_pos`, `boundary_spec`, `complement_card` | Denominator/root/log-domain audit |

The seven auxiliary definitions only spell out the source phase, phased vectors,
the matrix, and the entropy functional, or package a diagonal matrix as a
unitary. They supply notation to the consumers above, not separate content.
`area_append` uses OWS's word/occupation definitions, but no direct frozen
theorem; definitions are distinguished from theorem dependencies in this table.

## Accepted Mathlib Bindings

| Declaration | Path under pinned Mathlib/ | Actually used |
| --- | --- | --- |
| `Complex.norm_exp_ofReal_mul_I` | `Analysis/Complex/Trigonometric.lean` | yes, phase cancellation |
| `Matrix.mem_unitaryGroup_iff'` | `LinearAlgebra/UnitaryGroup.lean` | yes, diagonal unitary packaging |
| `Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff` | `Analysis/Matrix/Spectrum.lean` | yes |
| `Matrix.charpoly_mul_comm` | `LinearAlgebra/Matrix/Charpoly/Basic.lean` | yes |
| `Matrix.rank_mul_eq_left_of_isUnit_det`, `Matrix.rank_mul_eq_right_of_isUnit_det` | `LinearAlgebra/Matrix/Rank.lean` | yes |
| `Matrix.UnitaryGroup.det_isUnit` | `LinearAlgebra/UnitaryGroup.lean` | yes |
| `Matrix.toEuclideanLin_conjTranspose_eq_adjoint` | `Analysis/InnerProductSpace/Adjoint.lean` | yes |
| `Matrix.toEuclideanLin_eq_toLin_orthonormal` | `Analysis/InnerProductSpace/PiL2.lean` | yes |
| `Matrix.toLin_mul` | `LinearAlgebra/Matrix/ToLin.lean` | yes |
| `Matrix.charpoly_toLin` | `LinearAlgebra/Charpoly/ToMatrix.lean` | yes |
| `LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff` | `Analysis/InnerProductSpace/Spectrum.lean` | yes |
| `LinearMap.singularValues_of_lt`, `LinearMap.singularValues_of_finrank_le`, `LinearMap.singularValues_pos_iff_ne_zero` | `Analysis/InnerProductSpace/SingularValues.lean` | yes |
| `Fin.sum_univ_add` | `Algebra/BigOperators/Fin.lean` | yes |
| `Finset.sum_multiset_map_count` | `Algebra/BigOperators/Group/Finset/Basic.lean` | yes |
| `Matrix.charpoly_units_conj`, `Matrix.charpoly_units_conj'` | `LinearAlgebra/Matrix/Charpoly/Basic.lean` | no, attempted inverse-coercion route superseded |
| `Unitary.spectrum_star_right_conjugate` | `Algebra/Star/Unitary.lean` | no, set spectrum loses multiplicities |

## Required Numerical Witnesses

Positive: the two-word occupation (1,1), cut 1|1, has normalized Gram matrix
diag(1/2,1/2) at both theta 0 and pi: norm squared 1, Schmidt squares (1/2,1/2),
rank 2, entropy log(2) approximately 0.6931471805599453.

Negative for the fixed-occupation premise: use all four words with amplitude
1/2. At theta 0 the coefficient matrix is [[1,1],[1,1]]/2; at theta pi it is
[[1,1],[-1,1]]/2. Both norms squared equal 1, but the Gram matrices are
[[1/2,1/2],[1/2,1/2]] and diag(1/2,1/2); Schmidt squares change from (1,0) to
(1/2,1/2), rank changes from 1 to 2, and entropy from 0 to log(2). This state
uses occupations (2,0), (1,1), and (0,2), violating fixed occupation. It refutes
the proposed unrestricted-global-diagonal-unitary justification, not the source.

Negative for normalization: occupation (1,0), cut 1|1, violates 1=1+1. There
are zero legal words. The totalized coefficient matrix is zero: rank 0 while
the boundary count is 1. This falsifies the unguarded rank/normalization
conclusion; it does not falsify the purely algebraic Gram invariance identity.

The source-specific pi/4 overlap has equal inversion-residue counts
[105,105,105,105,105,105,105,105]. Reduction modulo q^4+1 gives [0,0,0,0], hence
overlap 0/840=0. Exact small-integer enumeration is independently executable
in Node, but has not been proved correct by Lean. Entropy decimals are
approximations, not certified intervals. The diagnostic exited 0 after adding
the fixed-occupation counterexample. The eigenvalues in both small examples
are computed from the actual Gram matrices; positivity/nonnegativity is
checked before division, log, or square root. `make lean` on the final tree
after archiving the probe also exited 0 (`lean-final-tree.log`).

Final search-count audit on the unchanged source tree: using `rg -c -i -P`
with the two repository regexes printed below returned 76 and 37 matching
lines respectively (both exit 0). The same-option matrix-directory search
for `\b(?:\w*singularValues\w*|\w*singular_values\w*|\w*svd\w*)\b`
returned 0 (exit 1); its same-feature control
`\b(?:\w*conjTranspose\w*|\w*unitary\w*)\b` returned 398 (exit 0).
The directories were `.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix`
and `.lake/packages/mathlib/Mathlib/Analysis/Matrix`. The count is matching
lines, not declarations. The actual singular-value API was read under
`Analysis/InnerProductSpace`, as recorded below.

## Explicit Nonclaims

No complete Lean proof or coverage of the full atom is claimed. In particular,
cross-theta orthogonality is not inferred from equal entanglement spectra and
is not smuggled into any hypothesis. No arbitrary real-valued cut positions,
nonchronological bipartitions, mixed occupations, or infinite alphabets are
covered by the source-state claim. No exhaustive literature/library search,
general provability claim, independent review, admission, or implication for
RH is claimed. Unopened external pages and unseen reviews remain
ASSUMED-UNVERIFIED. No third-party search was needed after pinned Mathlib
bindings closed the main target and activated the immediate stop rule.

The sections below preserve the earlier search and failed-build history.

## Registered Question And Stop Rules

Question: does atom
`0a350824194cd6312628fc5708116dfece7d0e63fec2a1e2f8c201549d63c707`
follow using only pinned Mathlib instantiation, frozen projections, and
normalization (including `sq_nonneg` and `linarith only`)?

The three obligations are tracked separately:

1. Equation (27), for every real theta, including orthogonality of both
   families of phased occupation-sector states.
2. Theta-independent Schmidt coefficients at every chronological prefix cut;
   equation (29) asserts rank 12 specifically at the 4|4 cut.
3. Orthogonality of the states at theta = 0 and theta = pi/4, separately from
   equality of their cut spectra and entropies.

Stop immediately if bind-only succeeds, a source clause is false, or making
the proof compile would require silently weakening the statement. A local
unitary theorem alone does not prove orthogonality of two different states.

## Baseline And First Readings

- HEAD: `a8809894ea0f1dac06913ed56e09db6223d7ddfa`.
- Branch: `lane/math/schmidt-theta-0909`, initially clean, tracking origin/dev.
- Read `tools/scripts/agent/probe-brief-note.txt`, all of `CLAUDE.md` in
  untruncated segments, and `agents/CONTEXT.md` before acting on the repo.
- Pinned Lean: `leanprover/lean4:v4.33.0`.
- Pinned Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.
- Read the CAS atom bytes. The source defines a cut after beat k into the
  first k and last 8-k registers; it does not quantify over arbitrary real
  cut positions or arbitrary noncontiguous partitions.
- `make show-atom ATOM_ID=<full id>`: exit 2, CLI executable missing in the
  fresh worktree. `make lean-cache-ensure` started through the canonical
  entry point. The show-atom command must be retried after CLI preparation.
- Initial file discovery mentioning `.lake` returned exit 2 because `.lake`
  was absent. This is not a negative Mathlib search result.

## Frozen Interface

GID: `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt`.
State: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.lean.json`.
statement_id:
`sha256:12fe938e662c8edbaeefb12298e5fc281e7f17595aafd457281a98bd63db1ca1`.

Read the complete Lean source. Its scope is a finite alphabet, an occupation
multiset with `a.card = t + s`, and an unphased uniform word state.
`normalized_coefficient_factorization` and `cut_sector_gram` require that
cardinality equation. `schmidt_coefficient_sq` alone has no such hypothesis;
using it alone would not establish nonzero normalization or positive weights.
`schmidt_coefficient_pos` supplies positivity under the cardinality hypothesis.
`occupation5040` has counts (4,2,1,1) and cardinality 8.
`history_5040_max_schmidt_rank` supplies the maximum and the 4|4 rank, both
for the unphased matrix. No theta quantifier is present in that matrix.

## Repository Search Receipt

Both commands below ran successfully. These are textual candidate searches,
not semantic dependency counts. Both use the same word-boundary, alternation,
noncapturing-group, and wildcard features. The positive control finds the
known coefficient declarations in the frozen source.

```sh
rg -n -i -P '\b(?:\w*schmidt\w*|\w*coherenthistory\w*|\w*singularvalues\w*)\b' D5/S3/Quantum
rg -n -i -P '\b(?:\w*coefficientMatrix\w*|\w*schmidt_coefficient_sq\w*)\b' D5/S3/Quantum
```

The source of `CoherentHistorySchmidt` is an exact unphased hit. Other textual
hits include `SequentialOccupationHistory` and `OccupationPhysicalPreparation`;
their relevance to theta is not yet verified. The full Mathlib search and
bind-only elaboration remain pending at this checkpoint.

## Pinned Mathlib Search Checkpoint

The retry of `make show-atom ATOM_ID=<full id>` exited 0. It printed the
registered raw and normalized SHA-256, identical to the target ID, and
`coverage_gids=[]`. The cache preparation exited 0 with `status=seeded`,
`method=clonefile`, one clone attempt, and both project and Mathlib warm.

Read the source context around equations (20)--(26). The actual phase is
the inversion statistic A of a chronological word, with
`B(u,v) = sum_{i>j} u_i v_j`. The state is normalized by sqrt(840), not
sqrt(5040); 5040 labels the integer with prime exponents (4,2,1,1).

The initial matrix-directory search for
`\b(?:\w*singularValues\w*|\w*singular_values\w*|\w*svd\w*)\b`
returned no matches (exit 1). Discovery located and full reading confirmed
`Mathlib/Analysis/InnerProductSpace/SingularValues.lean`: the interface is
`LinearMap.singularValues`. It defines singular values through the eigenvalues
of the adjoint Gram operator, with nonnegativity and support/rank theorems;
it contains no direct unitary-composition invariance declaration.

Exact usable candidates, read at the pinned version:

| Declaration | Mathlib path | Use at this checkpoint |
| --- | --- | --- |
| `Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff` | `Analysis/Matrix/Spectrum.lean` | Planned: preserve eigenvalues with multiplicity by charpoly equality |
| `Matrix.charpoly_units_conj` | `LinearAlgebra/Matrix/Charpoly/Basic.lean` | Planned: direct similarity invariance |
| `Unitary.spectrum_star_right_conjugate` | `Algebra/Star/Unitary.lean` | Read; set-valued spectrum alone does not preserve multiplicity |
| `Matrix.rank_mul_eq_left_of_isUnit_det` | `LinearAlgebra/Matrix/Rank.lean` | Planned: preserve rank under a right phase factor |
| `Matrix.rank_mul_eq_right_of_isUnit_det` | `LinearAlgebra/Matrix/Rank.lean` | Planned: preserve rank under a left phase factor |
| `Complex.norm_exp_ofReal_mul_I` | `Analysis/Complex/Trigonometric.lean` | Planned: modulus one for real theta |
| `LinearMap.singularValues` | `Analysis/InnerProductSpace/SingularValues.lean` | Read; no direct use yet |

Positive-control search with the same `-n -i -P`, word boundaries,
noncapturing group, alternation and wildcards found 398 matching lines for
`\b(?:\w*conjTranspose\w*|\w*unitary\w*)\b` in the same two matrix
directories. The narrow singular-value search is not an exhaustive library
search. A first lookup at `LinearAlgebra/Matrix/Spectrum.lean` exited 2;
the discovered and read correct path is `Analysis/Matrix/Spectrum.lean`.
Two early repository searches named nonexistent `D5/S2`, `D5/S3/Ledger`, or
`D5/S3/Algebra`; their exit 2 is recorded and is not evidence of absence.
Subsequent whole-D5 filename and identifier searches found no inversion-word
or q-multinomial interface under the searched names. No absence proof is claimed.

The required actual-history connection is still outstanding: a globally
diagonal unitary need not preserve bipartite Schmidt coefficients. Here the
fixed occupation permits the cross term to be absorbed into a left factor,
but the equality with the source's inversion statistic must itself be checked.

## Probe Run 01 And Numerical Cross-Check

`make lean` exited 2. Log: `lean-bind-01.log` in the runner attempt directory.
The temporary probe used the existing D5 glob solely for elaboration, with no
production header or registration. `phase_star_mul` passed with only
`propext`, `Classical.choice`, and `Quot.sound`. The other statements failed
on matrix notation scope, applying an iff before its parameters, namespace
resolution for `det_isUnit`, and finite-sum normalization. Error-recovery
`sorryAx` in those failed elaborations is not accepted proof evidence.
The statements are retained at their original strength while fixing the script.

An independent Node integer enumeration of the 840 legal words computed the
inversion polynomial coefficients as
`[1,3,7,13,22,33,46,59,71,80,85,85,80,71,59,46,33,22,13,7,3,1]`.
Counts modulo 8 are `[105,105,105,105,105,105,105,105]`.
The remainder modulo `q^4+1` is `[0,0,0,0]`, so evaluation at
`q=exp(i*pi/4)` is exactly zero. This is an integer-computation cross-check,
not a Lean proof of clause 3. No false source clause has been detected.

At k=4, the 12 positive probability numerators over denominator 840 are
`[12,96,48,48,72,144,144,72,48,48,96,12]`; their sum is 840.
The boundary-count sequence is `[1,4,8,11,12,11,8,4,1]`.

## Run 02 Claims And Limits (Historical)

Run 02 (`make lean`) exited 2. `unitary_rank` now passes with the standard
three axioms. Remaining script errors concern the diagonal entry's
`starRingEnd` spelling, a missing matrix coercion, and normalization of
`Fin.castAdd` order comparisons. The first standalone Node script run exited 1
because a closing `});` was omitted; this syntax error does not supersede the
successful one-shot enumeration above and is being repaired before acceptance.

No target clause has yet been proved or refuted. No new D5 module or public
declaration exists, so `proof_shape`, `escape_witness`, `admission_basis`, and
per-declaration utility are not yet applicable. No hypotheses have been added.
Numerical witnesses and axiom checks remain pending. No completeness of the
search, provability of the target, or implication concerning RH is claimed.
Unopened external pages and unseen reviews are ASSUMED-UNVERIFIED.

## Probe Run 03

`make lean` exited 2 (`lean-bind-03.log`). With the original all-real-theta
statements retained, equation (27), both phased sector Gram identities,
inversion concatenation, and normalization positivity passed with exactly
`propext`, `Classical.choice`, and `Quot.sound`. The matrix factorization and
spectral/rank consumers still failed: overly broad simplification hit recursion
depth; matrix inverse coercion hit the unchanged heartbeat limit; a negative
support branch needed `occupation_append`; the concrete Option alphabet needs
the source order `none < some 0 < some 1 < some 2`. No budgets were changed.

The repaired Node diagnostic exited 0 (`numerical-witnesses.json`). The positive
two-letter witness has occupation (1,1), cut 1|1, two legal words, spectrum
(1/2,1/2), rank 2, and entropy log(2) = 0.6931471805599453 at theta 0 and pi.
The negative witness has occupation (1,0), cut 1|1, no legal words, and
cardinality 1 != 2: totalized matrix rank 0 differs from boundary count 1.
No division or logarithm is evaluated at invalid normalization in the diagnostic.

Additional API readings: `Matrix.charpoly_units_conj'` uses the matrix inverse
of the unit's value, so direct elaboration is not definitional at the adjoint.
The next attempt uses `Matrix.charpoly_mul_comm` and the existing unitary
cancellation instead. `Matrix.toEuclideanLin_eq_toLin_orthonormal`,
`Matrix.toLin_mul`, and `Matrix.toEuclideanLin_conjTranspose_eq_adjoint` give
the matrix-to-operator route to actual `LinearMap.singularValues`.
Two incidental searches exited 2 (a malformed Makefile regexp and a quoted
WithBot wildcard); corrected searches returned the actual definitions above.
Neither error is treated as a negative search result.

## Probe Run 04

`make lean` exited 2 (`lean-bind-04.log`). The all-theta Gram eigenvalue
identity, local diagonal phase factorization, normalized whole state, all-cut
rank, and rank 12 at 4|4 now pass with the standard three axioms. No source
claim has been weakened. The remaining errors are in the explicit bridge to
Mathlib singular values (an unspecified intermediate basis and omitted explicit
linear-map arguments), the entropy definition's decidable index instance, and
a natural-number zero cast in the count formula. These failed declarations
are not accepted despite error-recovery axiom output.
