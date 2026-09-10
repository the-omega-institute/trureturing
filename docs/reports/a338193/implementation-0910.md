# A338193 implementation, 2026-09-10

Current mathematical result: the full all-index target and unique formal
solution are proved and frozen. Earlier checkpoint sections below record
their status at the time, not the final mathematical status.

## Provenance and scope

Skill: `lean4`; implementation by the single Codex worker in the runner's
`a338193-impl-0910/attempt-1`. No independent review is claimed. The user's
EGF coefficient and quadratic-bridge observations are supplied evidence, not
worker-recomputed evidence. This report is updated during implementation.

Base: `82938786158c163b50350c14c948e63df61107a8` (`origin/dev` at start).
Branch: `lane/math/a338193`. Initial tree was clean. `CLAUDE.md` was read in full.

Question answered: for the independently defined integral-differential EGF A
and Kurkov's natural-valued two-index recurrence f, prove
`n! * coeff n A = f 0 (n-1)` for every `n >= 1`.
Tier: first tier, as assigned. The user's main-entry and six-neighbor reading
found no proof of this equality; worker literature checks are recorded below.

## Preregistered proof route

Use the user's proposed witness: degree-first, row-index-second induction
establishing `F_j = F_0 R^j` for the independently constructed recurrence,
where `R = 1 + x*R + x*R^2`. Then derive the boundary differential equation,
set `B = F_0*(1-x*R)`, and prove `B' = F_0`. The quadratic equation for the
logarithmic derivative must imply the original equation. Prove coefficient
uniqueness before identifying B with A. None of these bridges is a hypothesis
of the target or a definition of either side.

Stop as a note if the formal equation equivalence, infinite-row factorization,
or unit/uniqueness bridge cannot be completed. A blocked report must contain a
real Lean attempt and the remaining goal. No finite positive test is a result.
No theory volume or atom will be created for this task.

## Search receipts

1. D5, `rg -n -i 'schr[oö]der|schroeder|A338193|Kurkov' D5`:
   no Schroeder/Schröder or A338193 match. Kurkov matches occur only in
   `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.lean`; its public interface
   still needs reading before ruling out reusable general lemmas.
2. D5 filename and `PowerSeries` searches found recurrence modules including
   `IntegralEGFComposition`, `QuarticEGFFixedPoint`, and
   `PiecewiseConvolutionPowersOfFour`; their general interfaces will be read.
3. The initial worktree has no `.lake`. `make lean-cache-ensure` was launched
   before any Lake invocation. Receipt is in the runner attempt directory,
   `lean-cache.log`.

## Declaration accounting

No new public theorem yet. For each eventual theorem, record `proof_shape`,
direct frozen prerequisites (GID and statement_id), `escape_witness`, and
`admission_basis`. The proposed module classification is `utility: none`:
the intended theorem is quantified over all natural indices, with an algebraic
and inductive proof, and is not a finite computation or a certified instance.

## Unclaimed

No proof, counterexample, integrality theorem, freeze, coverage, successful
build, or PR is claimed at this checkpoint. Pages not opened by this worker
are `ASSUMED-UNVERIFIED` as worker observations. The full target remains open.

## Search checkpoint: exact reusable interfaces

- Cache ensure EXIT=0: `status=seeded`, donor `/Users/chronoai/trureturing`,
  `method=clonefile`, `clonefile_attempts=1`, `stamp_miss=null`,
  `mathlib_olean_state=warm`, `project_olean_state=warm`.
- Pinned Mathlib search for `schr[oö]der|schroeder|A338193` found
  `Mathlib/RingTheory/PowerSeries/Schroder.lean` and
  `Mathlib/Combinatorics/Enumerative/Schroder.lean`. Both files were read fully.
  Exact reuse:
  `PowerSeries.largeSchroderSeries` and
  `PowerSeries.largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq`,
  transported from naturals to rationals by the existing series map.
  The header advertises a small series, but that file's body has no such
  definition. `Nat.smallSchroder` exists with a shifted indexing convention;
  the proof will use the exact large-series interface.
- Read the full public surfaces of `IntegralEGFComposition`,
  `QuarticEGFFixedPoint`, `PiecewiseConvolutionPowersOfFour`, and
  `DyadicPowerRowClosedForm`. General reusable results are `eCoeff_derivative`,
  `eCoeff_mul`, `eCoeff_X_mul`, `encode`, `eCoeff_encode`, `eCoeff_ext`.
  The latter two modules have no applicable public general result for this
  characteristic-zero differential/row problem; their private helper lemmas
  were inspected too.
- Third-party Lean ecosystem, authenticated GitHub code search:
  `gh search code A338193 --language Lean --limit 25` returned `[]`.
  `Schroder` returned Mathlib and copies plus unrelated Schroeder-Bernstein
  uses. No independent A338193 formalization was found in this search scope.
- Fetched and read `https://oeis.org/A338193/internal`. The entry states the
  original integral equation and all three Kurkov recurrences exactly as in
  the brief, and still labels the equality `Conjecture`, dated Oct 26 2024.
  The Kotesovec one-dimensional recurrence is a separate formula.
  Raw response: runner artifact `oeis-internal.html`.
- Capacity: `find D5/S1/Recurrence/Residue -type f | wc -l` returned 11.
  Spec A5.1 confirms the literal header syntax `utility: none`.

## Lean checkpoint: the infinite-row bridge is proved

Warm-tree `lake env lean /tmp/A338193.lean` exited 0. The exact successful
source is saved as `docs/reports/a338193-0910-snippets.lean` at this checkpoint.
This is a symbolic proof for every degree and every row, not finite checking.
It constructs `f` by well-founded recursion on `(m,j)` using exactly the
three OEIS recurrences, encodes each row using the frozen EGF interface,
proves the row series equation, and proves `row_factor` by degree-first and
row-second induction. It then proves `B_derivative : derivative B = F 0`.
No factorization assumption, target-based definition, sorry, or axiom is used.
The original equation equivalence and uniqueness remain to be proved.

Initial Lean attempts exposed two concrete interface errors: scalar
multiplication had to be distributed without expanding the inner `X * (...)`,
and the rational mapped constant coefficient needed `coeff_map` at degree 0.
Both were repaired; the resulting compiler output is empty and exit is 0.

Additional search: arXiv API `search_query=all:A338193` returned totalResults 0.
GitHub's non-Mathlib `rwst/lean-code/unsorted/gf.lean` hit concerns OGFs of
combinatorial classes, not this EGF or the row recurrence. Its full body was
not read: no statement from that file is used (`ASSUMED-UNVERIFIED` beyond the
read interface). D5's two linear ODE uniqueness hits are private, so cannot
be imported as public API. Their public results concern distinct implicit
exponential equations and congruences.

Route command diagnostics were input errors, not mathematical blockers:
absolute manifest paths are rejected, every field must be a string, and
`artifact=lean` is required on plane F. The manifest is now corrected.

## Lean checkpoint: original integral equation and unit bridge

`lake env lean /tmp/A338193.lean` EXIT=0 for the expanded source. Four linter
warnings (redundant change/simp arguments) will be removed before the final
build. The following are now kernel-checked:

- `Original` states the literal formal integral equation using the primitive
  with zero constant term and the two inverse series from the source.
- `original_iff_cleared` proves the integral/differential equivalence, including
  the nonzero constant coefficient of its denominator derivative.
- `original_iff_algebraic` proves equivalence to
  `(1+X)*S*S' - 2*X*(S')^2 - S^2 = 0`, clearing denominators using proved
  `S*S⁻¹=1` and cancellation by the nonzero series `S^3`.
- `B_algebraic` proves B satisfies that polynomial equation.
- `algebraic_iff_linear` identifies the constant-one branch with `D*S'=S`,
  where `D=1-X*R`. The other factor has constant coefficient -1, so cannot
  vanish. This is the unit/branch argument, not a branch assumption.

The all-degree coefficient uniqueness proof and the final choice of A by
`Original` alone are next. Route output is
`D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.lean`; its directory currently
contains one file, below capacity. No canonical D5 file has been created yet.

## Lean checkpoint: the complete target is proved

Warm-tree `lake env lean /tmp/A338193.lean` EXIT=0, no warnings. Both
`egf_coeff_eq_f` and `original_exists_unique` report exactly
`[propext, Classical.choice, Quot.sound]`. The proof quantifies over every
positive n. Uniqueness is proved by strong induction on the ordinary
coefficient index, using the linear equation obtained from the original
integral equation; the factor `(n+1 : ℚ)` is proved nonzero before cancellation.

A is `Classical.choose original_exists_unique`, with selection predicate
`Original` alone. This predicate contains the original integral equation and
constant coefficient 1; it contains no f, F, R, B, or coefficient equality.
The existence proof constructs B, and the final comparison uses the proved
uniqueness theorem. The target is not installed in either definition.

One intermediate uniqueness attempt rewrote S inside its own derivative,
leaving the explicit goal `derivative (D * derivative S) = derivative S`.
Restricting that rewrite to the right-hand side resolved it. The failed
compiler run was not a proof; only the subsequent clean run is claimed.

Repository build/report/emission/freeze and Scribe checks have not yet run.
The successful proof will now move from the reviewable snippet to the routed
canonical module; no second mathematical source will remain in the final tree.

## Canonical module and first repository build

The successful source has moved to
`D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.lean`; the snippet is removed
from the current tree and remains available in Git history. A source note
and six Scribe descriptions accompany it. Source metadata was checked against
%A: the original entry author is Vaclav Kotesovec (Oct 15 2020), and Kurkov's
conjecture is the 2024 contribution. No author is inferred from neighboring
examples.

`make lean` EXIT=0, elapsed 66.759 seconds on this macOS ARM worktree.
The log explicitly reports `Built D5.S1.Recurrence.Algebraic.SchroderIntegralEGF
(5.1s)` and standard three-axiom closures for both target and uniqueness.
`LEAN_CACHE`: `status=present`, `method=none`, `stamp_miss=null`, both layers
warm. Two new-module long-line warnings remain to be shortened; existing
unrelated-module warnings are outside this change. Canonical report production
is in progress. Logs are in the runner attempt directory.

## Public theorem accounting

All three declarations below have `utility: none`: these are symbolic
existence, uniqueness, and all-index coefficient theorems, not finite
instances, enumerations, checkers, or numerical reductions.

| Declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| original_exists_unique | content | row_factor, on the existence proof's path through B_derivative and B_original | escape-witness |
| A_original | bind-only | null | escape-witness at module level; companion to original_exists_unique and egf_coeff_eq_f |
| egf_coeff_eq_f | content | row_factor, used by B_derivative and the original-equation comparison | escape-witness |

The companion edges point consumer to prerequisite:
`egf_coeff_eq_f -> A_original -> original_exists_unique`.
No separate deposit is requested for the companion.

For each content theorem, the named `row_factor` meets CLAUDE 3.2:
1. Dependency closure: the proof reaches `B_derivative`, which uses
   `row_factor 1`; existence reaches the same fact through `B_algebraic` and
   `B_original`. Elaboration evidence will be saved below.
2. Not a frozen projection: existing libraries provide the EGF calculus and
   the Schroeder quadratic, but not this row identity. The new nested
   induction uses the independently constructed Kurkov recurrence.
3. Not definitionally equivalent: it identifies all row EGFs with powers of
   the independent Schroeder series, rather than restating either existence
   of the source solution or the boundary coefficient theorem.
4. Live path: the equality for row 1 is required to turn the original
   recurrence's boundary `F(0)-X*F(1)` into `B=F(0)*(1-X*R)`; no unused
   conjunction or discarded proof component supplies it.

Direct frozen source modules (current state pins, read rather than recomputed):
- `D5/S1/Recurrence/Residue/IntegralEGFComposition`:
  `sha256:7659badce7f3a2bb9681521c575cf07726e51bb3ba90baa36231036c4405e667`.
- `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint`:
  `sha256:05c8ee2d2a8eb1624df659d6581634873aafdcda010603c06e252caa930a7454`.

Exact outgoing declaration GIDs and statement identities will be extracted
from the new canonical Lean report and the elaborated proofs, before freeze.

## Final elaboration and report receipts

The final `make lean` EXIT=0 in 22.647 seconds; the final `make lean-report`
EXIT=0. Only the changed module was rechecked (`changed=1, recheck=1`).
The final raw report SHA-256 is
`51522b89d1b94cc06ea2a83bd11e1a3d4a6f97a6f39c52afe3ccd17369a1f4c6`.
The helper script `/tmp/A338193Dependencies.lean` read Lean `ConstantInfo` proof
bodies and walked module-local constants, stopping at frozen-module constants.
It exited 0 and confirmed `row_factor` in both content theorem closures.
This is closure evidence; the live-path argument is the explicit derivation
in the preceding section, not a claim that reachability alone proves liveness.

`docs/reports/a338193/declarations-0910.json` contains every public theorem's
statement identity, standard axioms, shape, witness, and exact direct frozen
GIDs plus their statement identities. These identities were read from the
canonical report, not recomputed from frozen source. The direct set has eight
constants (including definitions) from the two frozen EGF interface modules.

Before PR, `git grep -P 'A338193|SchroderIntegralEGF|row_factor.*Schroder'
origin/dev -- D5` returned no match.

## Emission and local Scribe checkpoint

`make emit` EXIT=0; the canonical Blueprint was generated from Scribe.
The required script `scribe-content-checks.sh` ran with the exact base SHA
and canonical report, EXIT=0 in 23.460 seconds. Its changed-path logic ran
`describe-report --check` and `markdown-check` (one document, zero authored
formulas, zero red results). `projections --check` was not triggered because
this change does not touch its producer or fixture inputs. Two observations
flag formula-like prose; they are observations, not hidden failing checks.
A subsequent Scribe update will render the main equation as a formula.

`A_original` remains a bind-only companion with `escape_witness=null`;
its `admission_basis=escape-witness` is explicitly module-level, not a claim
that the projection theorem supplies its own content witness.

## Freeze checkpoint

`make deposit-uncovered` EXIT=0 in 90.415 seconds. The required workflow
reused the final canonical report, passed `deposit-header-check`, ran `emit`,
and called `ledger-align --add`: added=1, changed=0, conflicts=0.
It reported `PLAYBOOK_DEPOSIT_FROZEN_UNCOVERED ... reason=NO_ATOM`.
The generated module state is
`sha256:6abcaba5514ab9f30ec08304d3379cb1e039f81c44a0a445b5271ea65e051b15`;
the new accepted event is
`3c38008523c0b3d79676a68cbcfd1557f8d4e25e99e96ba68a12c2872f01adde.json`.
No theory volume, atom, coverage edge, or hand-authored freeze state was made.

## Resolution registration

`Problems/oeis-a338193-egf-coefficients.md` records exactly Kurkov's positive-index
coefficient conjecture. The main theorem's Scribe node has the typed
`OpenProblemResolutionClaim` with `ResolutionKind.Proved`; its displayed
formula is authored in the typed Formula DSL. The generated Markdown is
produced by `make emit`, not edited directly.

Capacity was checked before adding the dossier: `find Problems -type f | wc -l`
returned 104. Canonical `Problems/*.md` are explicitly excluded from directory
occupancy by `RepositoryRules.Structure.cs:IsDirectoryCapacityExcluded`,
while their individual file length remains bounded. The D5 and Library
folders have respectively 2 and 41 files after this change, below 48.

## Final unclaimed scope

This worker does not claim historical priority, an exhaustive absence of
prior proofs, an analytic convergence theorem, asymptotics, or a new proof
of Kotesovec's separate one-dimensional recurrence. The six one-hop source
pages were not reopened by this worker; they are `ASSUMED-UNVERIFIED` as
worker observations, with the user's reading explicitly supplied evidence.
No independent adversarial review or merge is claimed. No new axiom, theory
volume, atom, or positive finite-instance deposit is part of this change.
The formal infinite-row factorization and coefficient uniqueness have been
proved; neither is an unproved premise of a public theorem.

## Final local content checks

After resolution registration, `make emit` EXIT=0 in 65.541 seconds.
The required `scribe-content-checks.sh` ran again against the exact base and
canonical report, EXIT=0 in 24.655 seconds. `describe-report --check` reported
`red=0` and emitted the A338193 `OPEN_PROBLEM_RESOLUTION` record for the exact
main theorem. The actual KaTeX check reported
`markdown: judged=1 formula(s)=1 red=0`. Its conditional projections test was
not triggered. These are the final Scribe bytes submitted for review.

Final local sequence: `make lean` (22.647s, 0), `make lean-report` (56.186s, 0),
`make emit` (0), local Scribe checks (23.460s, 0),
`make deposit-uncovered` (90.415s, 0), resolution registration,
`make emit` (65.541s, 0), local Scribe checks (24.655s, 0).
Lean source was unchanged after its final successful build and freeze.

The final report also records `OPEN projection ... reason=missing:` for the
main theorem. Inspection of `StatementProjectionFixtureLoader.LoadStatements`
shows this concerns membership in the two pinned presentation fixture files,
not a missing Lean declaration or proof. The typed `FromAuthor` formula is
permitted when this projection is unavailable; the gap is explicit. The
formula passes KaTeX, but no automatic Lean-to-formula equivalence is claimed.

## CI capacity failure and correction

PR #6751 was opened at commit `5cabf6a06f207787bf0e51995c8cfcb18d02519e`.
Run 34427683788 passed both Canonical Lean report production and Candidate
harness engineering checks. Its admission gate failed with `SL-003`:
`docs/reports` had 50 direct files against the admission limit of 48.
The two new reports were mistakenly added at that already-full directory;
the earlier capacity checks covered D5, Library and Problems but missed
reports. This was an implementation packaging error, not a proof failure.

Both reports now live under `docs/reports/a338193/`, leaving 48 files directly
under `docs/reports` and two under the new subdirectory. No pre-existing
report, frozen Lean module, or governance rule was changed. The report's
internal link and the PR links follow the new paths. The separate `SL-022`
Scribe surface diagnostic was also visible; the CI wrapper permits exit 3
for that diagnostic alone, whereas the capacity rejection produced exit 1.

The correction passed `make gate BASE=82938786158c163b50350c14c948e63df61107a8
GATE_ARGS=--skip-engineering`, EXIT=0 in 112.278 seconds. This ran the cached
Lean report producer and the actual admission/Scribe/filemap checks. It
explicitly did not rerun engineering tests, which had passed in CI and whose
inputs were unchanged by relocating reports. `SL-003` is now absent; only
the permitted `SL-022` protected Scribe surface result remains. This command
is the repository's local admission route, not `make preflight`.
