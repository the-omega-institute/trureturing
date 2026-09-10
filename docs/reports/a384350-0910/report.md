# A384350 / A384318 implementation

Provenance: `lean4` skill; one Codex implementation worker, no delegated or
independent review seats. The user supplied the triage decision and independent
finite checks. Worker measurements below are distinguished from those inputs.

## Preregistration

- Tier: first tier, as assigned. Base:
  `5d6a244a852db7cf66e3d9a78f4ec885b9f0a55c`; branch `lane/math/a384350`.
- Question: for every finite set S of positive natural numbers, is a nontrivial
  family of pairwise disjoint strict partitions of the members of S equivalent
  to some member being a sum of distinct positive numbers outside S?
- Semantic contract: a function assigns exactly one finite set T_s to each
  s in S; every part is positive, its sum is s, distinct indexed blocks are
  disjoint, and at least one block differs from the singleton {s}. The index
  names its required sum; no independent product of block counts is used.
- Proposed escape witness (before proof): in any nontrivial family, the block
  of the least changed member is disjoint from S. Every part in that block is
  strictly smaller than its sum; a part in S would therefore have its own
  unchanged singleton block, contradicting pairwise disjointness.
- Reverse construction: replace the selected singleton by the outside block,
  retaining the singleton for every other member.
- Empty S is included; nontriviality supplies a member when needed.
- Stop for a published proof of this uniqueness criterion or a counterexample
  to the least-changed argument. Success for this implementation assignment:
  kernel proof, requested local gates, and an open PR. No merge is claimed.
- No new theory volume, ingestion, atom, or coverage edge. Use the existing
  no-atom freeze entry point (`make deposit-uncovered`, backed by ledger-align).

## Search receipts

Initial repository search at the base above:
`rg -n 'A384350|A384318|A384322|A384317|DisjointRefinement|disjoint.{0,40}partition|partition.{0,40}disjoint|严格分拆|不交.*分拆' D5 Blueprint Library docs/reports`.
No target theorem was found. The triage note
`Library/Words/oeis2026triage0910.md` contains the assigned statement and route.
Other hits are unrelated finite partitions/cosets; their public APIs and broader
sum/refinement candidates remain to be inspected before local proof work.

Triage decision (verbatim from the task, not a new literature claim):

> A384322 的 NAME 与 A384317 的 formula **复述了同一对应但未给证明**——
> **不能因为「有人写过」就降级**(本仓判例 A392698:因此错误降级,重派后落地 #6596)。
> 它另取得 arXiv:2111.11084、2112.15096、2301.06347、2107.04666、2602.01281 完整 PDF 定位检索,
> 未找到本族唯一性证明;**但明写「未逐页审完,open 只限此检索范围」**。

## Verification log

The initial preregistration checkpoint claimed no Lean proof or gate success.
The chronological records below now establish the general equivalence and all
requested local gates, including no-atom freezing. PR delivery is recorded last.

## Unclaimed

- No exhaustive literature review or global novelty claim. Papers not opened
  by this worker are `ASSUMED-UNVERIFIED`; the triage PDF work is attributed above.
- The user's 2036-subset enumeration is a supplied observation, not worker
  verification. Finite examples will be private semantic checks only.
- No counting formula, sequence coefficient computation, or labeled set
  partition count is claimed.
- Independent review and remote CI success are not yet claimed.

### Worker library and online pass

- Repository broadening: searched D5 for `strict.partition`, `unrefinable`,
  `disjoint.*refinement`, `distinct.part.*sum`, and `sum id`; reviewed the
  public theorem signatures in CommonPriorPosteriorAgreement,
  IcosahedralAxisDecomposition, FiniteCosetPartitionMaximalIndexMultiplicity,
  ImmutableExtension, LayeredCapture, ObservationEscapeTopology,
  ResidualPermutationSign, PaddingRatio, TauSigmaPowerBounds, and
  SamePrimeScaleRedundancy. General APIs concern probability averages, prefix
  codes, observation kernels, permutation sums, or prime-factor bounds; none
  supplies the needed positive distinct-sum/least-changed-block lemma.
- Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d` verified from
  `.lake/packages/mathlib`. Text searches for unrefinable/strict partition/
  disjoint refinement found no target declaration. Reusable primitives read:
  `Finset.min'_mem`, `Finset.min'_le`, `Finset.single_le_sum`,
  `Finset.sum_erase_add`, `Finset.sum_lt_sum_of_subset`.
- Online HTTP capability measured: all seven requests returned HTTP 200.
  All fields of A384350, A384318, A384322, A384317 were read at their `/internal`
  URLs. The first two still explicitly label the family characterization
  Conjecture; the latter two state the correspondence without a proof.
  Their retrieved revision dates are respectively 2025-10-20, 2025-06-11,
  2025-07-27, 2025-05-28. No bibliography/proof field occurs in these responses.
- GitHub repository API search `unrefinable lean`: total_count 0,
  incomplete_results false. This is a scoped repository search, not a complete
  code search. Loogle bare `unrefinable` was rejected as an unknown identifier;
  that is a query error, not an absence result. A quoted query follows.
- arXiv API `all:unrefinable`, max_results=15: read returned abstracts.
  Seven partition papers include the five triage papers plus 2206.04261 and
  2601.10227. Abstracts discuss classification, generation, normalizer chains,
  numerical semigroups and Young diagrams; none states this family criterion.
  Full text follow-up of the additional relevant papers remains pending.
- Raw responses and `web-receipts.json` are in the runner attempt directory.

Cache receipt: `status=seeded`, `method=clonefile`, donor
`/Users/chronoai/trureturing`, `clonefile_attempts=1`,
`project_olean_state=warm`, `mathlib_olean_state=warm`,
`mathlib_missing_olean_files=0`; `make lean-cache-ensure` EXIT 0.

### Follow-up before local proof

Quoted Loogle query `"unrefinable"` returned count 0; positive control
`"Finset.min'_mem"` returned count 1 with the expected type. This repairs the
bare-query error above. The online API is therefore available and responsive.

Retrieved 2601.10227 (15 pages) and 2206.04261 (28 pages), extracted every page
with pypdf, and searched `disjoint`, `unique`, `family`, `families`, `decompos`,
`least`, and `refinement`, reading the returned contexts. No disjoint-family
uniqueness result occurred in those contexts. A relevant distinction:
2601.10227, p.3, Proposition 1 proves that the smallest *refinable part* has a
refinement into two missing parts; 2206.04261, p.2, attributes that reduction
to ACCL23 Proposition 4. These start with an outside-sum refinement, not an
arbitrary simultaneously chosen disjoint block family. They do not establish
the forward implication sought here. We do not reproach or reprove that
binary-refinement reduction. Full page-by-page reading is not claimed.

`dominating_theorem_search: not-found-in-searched-scope`. The stopping condition
has not been triggered by these searches. Proceed with the preregistered proof.

Routing measurements: Arith direct Lean files 33, Arith Blueprint direct files
56, Library/Arith total files 48. Use the already registered ArithSums domain
(S3; finite sums over integer indices) for this new actual module. Its Lean
and Blueprint directories do not yet exist (initial files 0). No Library note
is required for the repository-derived proof; the report retains the OEIS
statement locators and bounded literature assessment. First route invocation
with an absolute manifest path was rejected (`manifest path must be
repository-relative`); the manifest is moved to a relative run-local path.

### First kernel-checked proof unit

The private lemma `part_lt_of_nontrivial` is accepted by Lean (hot-cache
`lake env lean /tmp/a384350-part.lean`, EXIT 0). For any positive finite
partition whose sum is s and which differs from {s}, every part is < s.
It reuses `single_le_sum`, `sum_erase_add`, and
`eq_singleton_iff_unique_mem`. This is an unbounded structural lemma, not a
finite certificate. The final equivalence is not yet claimed.

Failure history: the initial `simpa [hsum]` did not rewrite an eta-expanded
sum; the second version still left `hsum : T.sum id = s` opaque to omega's
atom comparison. An actual goal trace isolated the mismatch with
`sum (fun x => x)`; `change (∑ x ∈ T, x) = s at hsum` fixed it. No assumption
or mathematical statement was weakened. The supplied scratch proof is now
incorporated into the canonically routed D5 module with its semantic definitions.

Routing succeeded for D5/S3/ArithSums/DisjointStrictRefinement, generality G.
The route parser also required string-valued empty fields and artifact=lean;
those manifest-input errors were fixed before creating the module.

### Full equivalence accepted

Hot-cache `lake env lean D5/S3/ArithSums/DisjointStrictRefinement.lean` returned
EXIT 0. `nontrivial_disjoint_refinement_iff` has exactly the axioms
`[propext, Classical.choice, Quot.sound]`. No sorry or private axiom is used.
The main file still awaits the mandatory project/report/emission/deposit gates.

The total function `blocks : ℕ → Finset ℕ` is constrained only on S; nontriviality
is also witnessed *inside S*. Changing an off-S value cannot witness it. Thus
this existential represents exactly one block per member and does not pretend
that total functions off S have a unique extension. All disjointness obligations
explicitly quantify distinct members of S. The least changed set is nonempty
by the supplied nontriviality witness, including when considering S = ∅.

## Declaration accounting

The only public theorem is
`D5/S3/ArithSums/DisjointStrictRefinement.nontrivial_disjoint_refinement_iff`.

- `proof_shape: content`.
- `direct_frozen_dependencies: []` (there are no D5 imports, hence no frozen
  GID/statement_id pairs; Mathlib is accounted separately above).
- `escape_witness: least_changed_block_disjoint`, the private theorem saying
  the least changed member's block avoids S.
- `admission_basis: escape-witness`.
- Section 3.2(i): the public proof explicitly calls this private theorem;
  it is in the elaborated transitive constant dependency closure.
- Section 3.2(ii): selection by min' alone does not establish disjointness;
  positive-sum strict descent and contradiction with the smaller singleton
  block supply the new combination. No searched frozen or upstream theorem
  supplies this conclusion by projection or normalization.
- Section 3.2(iii): the witness concerns an already selected block with a
  leastness hypothesis, while the public conclusion is an existence iff.
  It is neither definitionally equivalent to nor an alias of that conclusion.
- Section 3.2(iv): its disjointness proof is the actual second conjunct of the
  constructed right-hand witness. It survives reduction; removing it leaves
  that required conjunct unproved, not a discarded or unrelated proof term.
- The reverse implication constructs the function that replaces exactly the
  selected singleton. Original positivity hS is used for every unchanged block.
- `utility: none`: the public mathematical result is a general finite-set
  theorem with no bound on member size or number of blocks; it is not an
  enumeration, checker, numeric reduction, or certified finite instance.
  Utility-specific fields: `not-applicable(kind=none)`.

Definitions `IsDisjointStrictRefinement` and `NontrivialDisjointRefinement`
only encode the semantic contract; they are not claimed as independent results.

### Semantic controls and narrative

The complete module, including private controls, passed hot-cache Lean, EXIT 0.
All five assigned positives ({3}, {4}, {5}, {6}, {1,5}), all five assigned
negatives ({1}, {2}, {1,2}, {1,3}, {1,4}), and the empty case are kernel checked.
The positives give explicit outside blocks. For the negatives, the private
helper derives a bound on every possible part from its sum before finite
`decide`; it proves absence of the unbounded witness, not just failure within
an assumed search limit. No native_decide is used. These controls are private
and provide no new independently frozen public finite-instance result.
They are semantic checks, not additional research progress.

Added a single Scribe theorem narrative and a citation-only Library note
`D5/L/ArithSums/wiseman2025disjoint` acknowledging the OEIS conjectures.
The proof provenance is repo-derived. This supersedes the earlier optional
choice to omit a note: the note gives durable exact source locators, not a
new theory volume or an atom. Its Verified locator section includes the
literal frontmatter doi/url lines. Capacity correction from measured base
`git ls-tree`: Library/ArithSums already had 6 files and now has 7; the prior
unmeasured "starts with one file" assertion was incorrect. Lean/Blueprint
ArithSums have 1/1 before markdown emission, respectively.

Before-PR repository recheck: fetched origin/dev
`fa5ec493a0729f691cd5e453bb4129117ee9bace`; PCRE search for A384350, A384318,
nontrivial_disjoint_refinement and least_changed_block in that revision's D5
returned no matches (EXIT 1). `git merge-tree --write-tree HEAD origin/dev`
returned EXIT 0, tree `100418aa468c235ec37d2eeb6c945eb6d7acb488`, with no
conflicts. This is a data-only integration preview; the original local gate
base remains the immutable SHA recorded in preregistration.

### Mandatory project build

`make lean`: EXIT 0, 60.71 seconds on this macOS ARM worktree.
Build completed successfully (12830 jobs); the target module built in 8.7s.
Unrelated base modules emitted style warnings; the target emitted no warning.
Log: runner attempt `make-lean.log`; structured timing in `make-lean-result.json`.

```text
LEAN_CACHE {"status":"present","worktree":"/Users/chronoai/trureturing-a384350","donor":null,"method":"none","reason":null,"stamp_miss":null,"pin_sha256":"sha256:6c4c682ffba051b5744fe7a75ccc99d7f3b20227b3b026f392f3315be0adaa4e","clonefile_errno":null,"clonefile_errnos":[],"clonefile_attempts":0,"clonefile_cleanup_error":null,"mathlib_missing_olean_files":0,"mathlib_missing_olean_samples":[],"archive_status":"not_attempted","archive_mode":null,"archive_skip_reason":"project olean state is warm","archive_reason":null,"archive_producer_commit_sha":null,"archive_workflow_run_id":null,"mathlib_olean_state":"warm","mathlib_olean_probe_error":null,"project_olean_state":"warm","project_olean_probe_error":null}
```

`make lean-report`: EXIT 0, 68.02 seconds; delta plan recheck=1.
Canonical report `.lake/build/stratalint/raw-lean-report.json`, SHA-256
`148186255b81597d45b30c56c5b73803a6aeb43c7dbae7dd8ca144fb70663f0a`.
Log and timing: runner `make-lean-report.log` / `make-lean-report-result.json`.

`make emit`: EXIT 0, 56.23 seconds; exactly one changed Blueprint emitted.
The generated theorem states the required positive-set quantified iff.
A supplemental compiler dependency diagnostic initially used the reserved
word `prefix` as a local identifier and failed to parse; renamed the local
identifier. This diagnostic does not alter the proved module.

### Scribe and elaborated dependency checks

`bash tools/scripts/workflow/scribe-content-checks.sh
.lake/build/stratalint/raw-lean-report.json ""
5d6a244a852db7cf66e3d9a78f4ec885b9f0a55c`: EXIT 0, 23.94 seconds.
Describe and real-KaTeX markdown checks passed; markdown reported
`judged=1 formula(s)=1 red=0`. Existing offline DOI observations were not RED.
The wrapper conditionally skips projections for this delta; a separate explicit
projection check is recorded below. Log/timing: runner
`scribe-content-checks.log` / `scribe-content-checks-result.json`.

The repaired hot-cache compiler diagnostic passed (EXIT 0). Its inspection of
elaborated theorem values with `getUsedConstants` reports the actual edges
`nontrivial_disjoint_refinement_iff → least_changed_block_disjoint →
part_lt_of_nontrivial`. Private controls depend on the main theorem; the main
theorem does not depend on those controls. Log: runner
`elaborated-dependencies.log`. This directly supports the dependency-closure
and live-path accounting above.

Canonical declaration identities from the Lean report:

- Public theorem: `sha256:0c87ce641e5dbb2ea1460f9718efe00f24908e519e8dd215cd64b90b6a323736`.
- Private escape witness: `sha256:ebf9271d79b19ab3e5471802cb117ec8096f5d39f684c79bff02695c491fb9c7`.
- `IsDisjointStrictRefinement`: `sha256:45cb643497a80430d7c39f92f368f3f8a095b7d5ae9593ae1c9ddb434640f136`.
- `NontrivialDisjointRefinement`: `sha256:d0eedc4448afe0f6ec075f5dfae34431cb01f2f0af059892991ea18325713832`.

Explicit `projections --check --report` via the canonical
`StrataLint.Scribe.Documents` project: EXIT 0, 13.06 seconds. No diagnostics.
The same canonical report was supplied both as the environment variable and
the report argument. Log/timing: runner `projections-check.log` /
`projections-check-result.json`. All three requested Scribe checks have now run.

### No-atom freeze

`make deposit-uncovered
BASE=5d6a244a852db7cf66e3d9a78f4ec885b9f0a55c
GID=D5/S3/ArithSums/DisjointStrictRefinement.nontrivial_disjoint_refinement_iff`:
EXIT 0, 84.28 seconds. The canonical wrapper reused the successful report,
passed SL-012 header checks, emitted zero changed Blueprints, then ran
`ledger-align --add D5/S3/ArithSums/DisjointStrictRefinement.lean`.
Receipt: `changed=0 added=1 unchanged=3942 conflicts=0`, `reason=NO_ATOM`.
No theory source, atom, or coverage edge was created.

- Module `statement_id`: `sha256:e1f6c3c7bd0cbeafa2c44d8ac014afcdbfd970ed288134d24d08b5546bff2bab`.
- Freeze event: `sha256:4d06f5002ee0ac0a811870332594091ef0f6f078cde7f1de334111ff9aa88883`.
- Frozen prerequisite node IDs: `[]`.
- New canonical files: the module's `Golden/Frozen/state` pin and its single
  `Golden/Frozen/accepted` event. The module snapshot includes private semantic
  controls; none is exposed or claimed as a separate public finite-instance result.
- Logs: runner `make-deposit-uncovered.log` / `make-deposit-uncovered-result.json`.

These final local gate results supersede earlier pending checkpoint descriptions.

### PR delivery

Opened https://github.com/the-omega-institute/trureturing/pull/6730 through
`make pr-open HEAD=lane/math/a384350 MESSAGE=<runner>/pr-message.md`.
The creation step returned EXIT 0; the same canonical process is waiting for
the three required CI checks. Auto-merge was not enabled.

Implementation outcome under the user-assigned stopping rule: **成**. The
general theorem is kernel checked, has no sorry or private axiom, is frozen
without an atom, and has an open PR. This is not a claim that the PR is merged.
At this checkpoint remote CI is pending; its terminal receipt is stored in the
runner's `make-pr-open-result.json` and final `implementation-report.md`.

Final source delta contains seven added files: Lean, Scribe source and emitted
markdown, the Library locator note, two canonical freeze files, and this report.
`git diff --check` passed. No protected base file or preexisting module changed.
