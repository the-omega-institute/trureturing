# Zhao vincular stack probe

## Preregistered falsifiable predictions

Recorded before inspection, downloads, or computation.

1. An independently implemented right-greedy stack map, with the stack read top to bottom, reproduces the source's four outputs for input 514362: 463215, 263415, 426315, 632415.
2. Over S_9, the maximum fibre size of SC_{1_23_} exceeds 128.
3. At n = 5, the fibre-size multiset has two distinct values strictly greater than 4.

These are predictions, not verified conclusions. The source and issue #8634 still require clause-by-clause fidelity checking. All work is confined to this worktree and probe/. Third-party downloads will remain in runner scratch.

## Statement fidelity

Source: arXiv:2410.17057v1, fetched as the source archive into runner scratch; no third-party files enter this worktree. The macros in main.tex (lines 54, 59, 60) define SC, underline, and the symmetric group. Introduction paragraph 2 defines adjacency by underlining; paragraph 3 and pictures/ex*.tikz give exactly the four specified figure outputs.

- 4.14: dynamics.tex, label 1un23preimages: n >= 2; both maximum fibre sizes equal 2^(n-2). An attained-maximum predicate for each map expresses the same chain equality.
- 4.19: dynamics.tex, label 1un23uniquemaximum: the two specified words uniquely achieve the respective maxima. The source omits an n range. Issue #8634 explicitly supplies n >= 2 as an interpretation; the requested n = 8 refutation is unaffected by the small-n boundary. Strict inequality for every other permutation expresses unique attainment.
- 5.2: futuredirections.tex, second conjecture: n >= 3; second-largest distinct fibre value is 2^(n-3); exactly 2*n-2 permutations attain that value. The refutation must negate this entire conjunction via its first clause only.
- The source describes right-greedy sorting but has no formal transition rule. The adopted left-to-right input scan, stack word top-to-bottom, push iff the whole proposed stack avoids the pattern, otherwise pop and retry, agrees with the stated interpretation in #8634. The source does not explicitly specify this convention; agreement of the four anchors is its operational check.

No clause mismatch requiring a revised preregistration was found. The formal-answer skill is subordinate here to the explicit probe-only scope, exact JSON response, prohibition on delegation, and externally named open-problem-resolution exception; no generalized wrapper or D5 mutation will be manufactured.

## Independent Python result

Whole-word containment enumerates all triples and imposes the indicated adjacency; it never uses a new-top-only rule. Both increasing and decreasing maps were exhaustively evaluated on S_2 through S_9.

| n | inputs per map | max 1_23 | max 3_21 | designated increasing maximizer fibre |
|---|---:|---:|---:|---:|
| 2 | 2 | 1 | 1 | 1 |
| 3 | 6 | 2 | 2 | 2 |
| 4 | 24 | 4 | 4 | 4 |
| 5 | 120 | 8 | 8 | 8 |
| 6 | 720 | 16 | 16 | 16 |
| 7 | 5040 | 32 | 32 | 32 |
| 8 | 40320 | 64 | 64 | 64 |
| 9 | 362880 | 144 | 144 | 128 |

All three predictions passed. The four anchors reproduce exactly. F(765432819) = 144. At n = 5 the histogram over **all** outputs in S_5 is {'0': 65, '1': 19, '2': 24, '3': 1, '4': 8, '5': 2, '8': 1} (including 65 zero fibres); the first-clause witnesses have fibres 5 and 8.

The complete independent results, maximizers, histograms, and explicit witnesses are in enumeration.json. At n = 8 the three maxima are 65432718, 65432817, 76543218, each with 64 preimages. The preregistered n >= 2 uniqueness statement additionally fails at n = 2 (both permutations have fibre 1); the requested formal probe will still use n = 8.

Python measured wall duration: 9.790535 s. These are executable enumeration results, not yet kernel proofs.

## Reuse and literature checks

Expected proof_shape is bind-only for each result: instantiate the closed conjecture at a finite n, check the requisite finite facts, and normalize cardinal inequalities. Admission is open-problem-resolution under issue #8634, not escape-witness.

Queries and exact counts are in dedupe.json; search_reuse.py is the reproducible program. git grep -P is used with explicit path arguments and no unquoted globs.

| scope | query | line hits | files | exit |
|---|---|---:|---:|---:|
| . | topic | 0 | 0 | 1 |
| . | patterns | 99 | 25 | 0 |
| . | reuse | 623 | 222 | 0 |
| . | positive_control | 164 | 111 | 0 |
| .lake/packages/mathlib | topic | 0 | 0 | 1 |
| .lake/packages/mathlib | patterns | 1 | 1 | 0 |
| .lake/packages/mathlib | reuse | 933 | 263 | 0 |
| .lake/packages/mathlib | positive_control | 92 | 54 | 0 |

Topic search: stack.?sort, vincular, and 2410.17057. Positive control: Nat.add_comm. Pinned Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d (v4.33.0). Relevant repository pattern containment in DerangementRatioNonconvergence and ArcherBourneDecomposition is classical, with no adjacency or stack transition, so it does not close these conjectures. No project declaration is imported. Available upstream machinery: List.mem_permutations, List.nodup_permutations, List.toFinset_card_of_nodup, Finset.card_le_card, and membership/filter rules. The final proofs directly use List.mem_permutations', Finset.card_le_card, and membership/filter rules; other listed theorems justify the carrier or are available alternatives, not direct proof dependencies.

Authenticated GitHub code search `vincular language:Lean` returned total_count=0, incomplete_results=false (unauthenticated API was 401). No new third-party dependency is required. OEIS query of 1,2,4,8,16,32,64,144 returned only A274859 (set partitions, not these stack maps). Crossref DOI 10.1016/j.disc.2025.114834 confirms the title, March 2026 publication, zero indexed citations, and no update-to field. This is not proof of absence of a settlement. General web search was inaccessible: Google returned a JavaScript challenge, DuckDuckGo a CAPTCHA; the journal full-text API returned HTTP 400. The preregistration reports additional searches, which remain inherited evidence, ASSUMED-UNVERIFIED by this seat. Journal-version content and comprehensive literature openness remain ASSUMED-UNVERIFIED. No known settlement was found in the successfully searched scope.

## Lean cache capability

The initial worktree had no .lake/packages/mathlib; the first repository build door was make lean-cache-ensure with the exact requested PATH. Its exit was 0. Receipt:

```text
LEAN_CACHE {"status":"seeded","worktree":"/Users/auric/trureturing-op-zhao-vinc-probe","donor":"/Users/auric/trureturing","method":"clonefile","reason":null,"stamp_miss":null,"pin_sha256":"sha256:1499ba00eb44d4b760a213127fc10c82158b7595723ae155179378723cf14db3","clonefile_errno":null,"clonefile_errnos":[],"clonefile_attempts":1,"clonefile_cleanup_error":null,"mathlib_missing_olean_files":0,"mathlib_missing_olean_samples":[],"archive_status":"not_attempted","archive_mode":null,"archive_skip_reason":"project olean state is warm","archive_reason":null,"archive_producer_commit_sha":null,"archive_workflow_run_id":null,"mathlib_olean_state":"warm","mathlib_olean_probe_error":null,"project_olean_state":"warm","project_olean_probe_error":null}
```

No bare lake command ran before this stamp. All subsequent Lean invocations use the requested PATH and lake env lean.

## Compiled refutations: 4.14 and 5.2

`ZhaoProbe.lean` compiles with exit 0 using the stamped cache and:

```text
/usr/bin/time -l lake env lean -Dprofiler=true probe/ZhaoProbe.lean
```

Measured whole file: wall 14.22 s, cumulative kernel type checking 6.66 s, peak RSS 2,177,564,672 bytes (2.177564672 GB; 2.028 GiB). Lean 4.33 labels the checked-time profiler bucket `type checking`; that is the checked_s measurement, not wall time or elaboration time. This is a local macOS ARM build on the supplied host and warm cloned dependency cache, not a CI measurement.

```text
'ZhaoProbe.C414.result' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZhaoProbe.C52.result' depends on axioms: [propext, Classical.choice, Quot.sound]
```

4.14 checks 129 explicit input permutations independently, checks their finite-set cardinality is 129, applies Mathlib's `Finset.card_le_card`, and contradicts the universal bound 128 at n = 9. No exact n = 9 upper bound is claimed by Lean. 5.2 checks F(32415) = 5 and F(43215) = 8 over all 120 inputs, then contradicts uniqueness of the distinct value above 4 in the definition of second largest. Its second clause is stated faithfully but never used in the refutation.

Encoding: IsPerm is List.Perm with [1,...,n]; Sn uses Mathlib's structurally recursive `List.permutations'`. Membership is exactly IsPerm by `List.mem_permutations'`; absence of repeats follows from `List.permutations_perm_permutations'` and `List.nodup_permutations` applied to the distinct range. Fibre filters these inputs and converts to a Finset before taking its cardinality. Multiplicity counts output permutations in the same repetition-free enumeration. MaximumIs means attainment plus a bound on every permutation; the two attained maxima equal the same power in 4.14. SecondLargestIs means the value is attained and exactly one distinct larger value is attained, with every larger fibre equal to it. Thus zero fibres are included in the range, without multiplicity affecting the order statistic.

Implementation constraint discovered by compilation: Mathlib's well-founded `List.permutations` did not kernel-reduce in this environment (stuck on Acc.rec), so the final implementation directly uses its existing structural `permutations'` variant and existing membership theorem. This changes enumeration order only. The 129 conjunctions are split before `decide +kernel`; there is no new helper theorem, sorry, native_decide, new axiom, or raised resource budget.

The optional 4.19 upper-bound cost experiment is separate; its final scope decision is below. No D5 publication or required harness check is claimed.

Additional read-only checks: authenticated GitHub issue search for "2410.17057" found only #8634. arXiv API returns the v1 identifier and 2024-10-19 published/updated dates. OpenAlex returned HTTP 429. Bing RSS returned unrelated CSC portal entries, so it supplies no relevant search evidence. The author/source and repository deduplication checks were successful; comprehensive current literature coverage remains ASSUMED-UNVERIFIED.

## Exact closed claims

All names below are inside namespace ZhaoProbe; each claim has no parameters or free universe variables. Definitions are in ZhaoProbe.lean.

C414.claim

```lean
def claim : Prop :=
  ∀ n : Nat, 2 ≤ n →
    MaximumIs false n (2 ^ (n - 2)) ∧ MaximumIs true n (2 ^ (n - 2))
```

C52.claim

```lean
def claim : Prop :=
  ∀ n : Nat, 3 ≤ n →
    SecondLargestIs n (2 ^ (n - 3)) ∧ Multiplicity n (2 ^ (n - 3)) = 2 * n - 2
```

C419.claim

```lean
def claim : Prop :=
  ∀ n : Nat, 2 ≤ n →
    (∀ pi, IsPerm n pi → pi ≠ (List.range' 1 (n - 1)).reverse ++ [n] →
      F false n pi < F false n ((List.range' 1 (n - 1)).reverse ++ [n])) ∧
    (∀ pi, IsPerm n pi → pi ≠ List.range' 2 (n - 1) ++ [1] →
      F true n pi < F true n (List.range' 2 (n - 1) ++ [1]))
```

## Declaration judgement and proposed placement

For each of `ZhaoProbe.C414.result` and `ZhaoProbe.C52.result`:

- `proof_shape: bind-only` (instantiation, finite checking, existing cardinal monotonicity, and normalization).
- `direct_frozen_dependencies: none` (no D5 imports; Mathlib is not a frozen project dependency).
- `escape_witness: null`. Test (i): no proposed new intermediate declaration in the elaborated dependency closure. Test (ii): no fact is claimed to escape the allowed finite computation/normalization steps. Test (iii): no distinct non-equivalent intermediate witness is asserted. Test (iv): no escape witness is claimed on a live proof path. Both results rely on the preregistered external-open-problem exception, not an escape witness.
- `admission_basis: open-problem-resolution`, preregistered in issue #8634 before the probe.
- `utility: kind=certified-instance; basis=refutes`. Independent question answered: the respective explicitly numbered arXiv v1 conjecture. Each closed `result : ¬ claim` is the only public theorem for its conjecture; no companion theorem is proposed.
- Dominating-theorem search: repository mathematical/evidence surfaces and pinned Mathlib, queries and counts in dedupe.json, plus authenticated GitHub Lean search; `not-found-in-searched-scope`. Literature openness has the explicit limits above.

Proposed module GID: `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations`.
Proposed path: `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.lean`.
Existing permutation-pattern modules in this Words subdomain supply the closest subject placement; no new domain is needed. `git ls-files -- 'D5/S1/Words/Patterns/*'` reports 5 tracked files, all direct Lean files, so this module would bring the direct count to 6. For comparison, the ConceptDynamics/PatternAvoidance directory has 2 direct tracked Lean files; D5/S3/Combinatorics currently has none. `tools/StrataLint.Engine/Rules/RepositoryRules.Structure.cs:65` sets DirectoryFileLimit = 96. Counts were taken at eed1763b5c223b8979b0be656ca8d6887b308614; no D5 files changed in this probe.

The proposed shared definitions are Contains, Push, Process, SC, IsPerm, Sn, Fibre, F, MaximumIs, SecondLargestIs, and Multiplicity, with the two computational Decidable instances. The delivered public theorem pairs are C414.claim/C414.result and C52.claim/C52.result. C419.claim is stated in the probe for fidelity and scope accounting; an implementation must include it in the admitted public surface only if a corresponding result is delivered.

Reasoning discipline: predictions were fixed before computation; source conditions and chosen conventions were made explicit; finite enumeration and kernel results are reported at their actual strengths; no retrospective claim of an escape witness or full literature search is made. The ordinal and multiplicity definitions include all output permutations, including zero fibres. The n = 2 uniqueness observation does not replace the requested n = 8 target. This seat has read no other seat output or orchestrator script; issue #8634 itself contains inherited orchestrator evidence, distinguished from independent checks here.

Kernel measurement metadata is in verification.json, bound to ZhaoProbe.lean by SHA-256. No CI timing, full-project build, lint, freeze, admission, PR, merge, or KPI increment is claimed. The repository-push operations are probe persistence only.

## 4.19 cost boundary and final disposition

**Do not deliver 4.19.** The retained item-by-item cost trial `Zhao419Cost.lean` compiles with exit 0, but **32 of 120 insertion blocks alone** (10,752 of 40,320 inputs) consume **177 s kernel type checking**, **292.55 s wall**, and **2,227,175,424 bytes peak RSS (2.227175424 GB)**. These are measured partial-trial costs, not an extrapolation or a completed S_8 upper bound. The partial checked cost already exceeds the 120 s guide. The full upper-bound proof and Lemma 4.15 are not delivered or claimed.

Reproduce the retained cost experiment with:

```text
python3 probe/generate_cost_probe.py --blocks 32
/usr/bin/time -l lake env lean -Dprofiler=true probe/Zhao419Cost.lean
```

Use the exact PATH recorded above and the stamped cache. This experiment partitions S_8 by deleting entries 1, 2, and 3; each permutation of [4,5,6,7,8] generates 336 words by insertion. The checked 32 blocks cover only a subset. Each block's explicit list, split into chunks of 48, is kernel-checked against the enumerator. Every word's fibre-membership equivalence is a separate decide goal. This avoids full-list simplifier recursion/step limits; a failed simplifier run supplies no kernel-cost evidence. No resource setting was raised. The retained source and measurements in verification.json suffice to reproduce the cost result; failed source drafts are not retained.

Measured host: Apple M5, 10 logical CPUs, 34,359,738,368 bytes RAM. The cache was warm. Other Lean work was observed on this shared host during the cost trial; these local elapsed-time measurements do not establish CI performance.

Final verdict: **propose**, delivered conjectures **4.14 and 5.2 only**, as exact closed negations with the standard three axioms. The n = 9 exact maximum 144, exact fibre 144, all n = 2..9 tables, four anchors, and n = 8 ties are Python evidence; Lean proves only the 129-witness bound needed for 4.14 and the two exact n = 5 fibres needed for 5.2. The second clause of 5.2 is included in its claim but its failure is not formalized. 4.19 remains a scope wall in this seat.

All retained artifacts under probe/ are this seat's own source, generated finite data, or reports. Third-party source/archive downloads stay in runner scratch. No agents, reviews, sshx, PR, deposit, emit, lean-report, preflight, or full-project build were run. The result envelope and completion sentinel are published by this worker in the runner-owned attempt directory after the final push. This is a probe proposal, not an admitted result or merged open-problem settlement.
