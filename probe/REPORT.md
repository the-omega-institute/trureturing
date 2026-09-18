# Shieh–Yang–Yu Conjecture 6.2 isolated probe

## Falsifiable predictions (registered before checks)

1. An independent Python implementation of West's stack map composed with reversal of each valley run reproduces Theorem 4.4 fixed-point counts for n = 1,...,8: 1,1,2,4,9,23,65,199, and Theorem 4.2 sortable counts 2^(n-1).
2. There is no cycle of length at least two among permutations of 1,...,n for 1 <= n <= 8.
3. At every non-fixed permutation in that range, the reversed output word is strictly larger in lexicographic order than the reversed input word.

These are predictions, not measured results. The source fidelity check precedes execution of the Python experiment. The preregistration defines the dotted-pattern stack map by the proved right-hand side of Proposition 3.5; that boundary is retained explicitly.

## Result

Verdict: **propose**. The exact preregistered S_n statement compiles without warnings, sorry, native_decide, or new axioms. The required potential-deletion mutant fails at the missing forward inequality. This is an isolated probe result; no integration or publication is claimed.

## Source fidelity

Checked arXiv:2411.11914v2 directly (PDF downloaded only to runner scratch), against issue #8639. The clauses agree:

- The machine is the dotted-pattern stack map followed by West's map, composition `s ∘ s_{21-dot}` (printed p. 2).
- A valley is strictly smaller than every earlier entry; the first entry is a valley vacuously. Runs are maximal consecutive blocks beginning at valleys (printed p. 3). The example is `243 | 15`.
- Proposition 3.5 states reversal of each valley run. Using that proved expression as the definition retains the preregistered source-level identification; this probe does not formalize the dotted-pattern operational map or Proposition 3.5's identification with it.
- West's stack is increasing from top to bottom, operating right greedily. On distinct entries, popping while top < input, then pushing, has exactly that behavior.
- Conjecture 6.2 quantifies over all permutations in S_n and every n >= 1 and asserts eventual arrival at a fixed point. The requested consecutive-iterate equality is exactly that assertion; it does not assert sorting to the identity.
- The numerical anchors are Theorem 4.2 (one-pass sortable count 2^(n-1)) and Theorem 4.4 (fixed points, A007476).

Locator correction only: in the fetched v2, Proposition 3.5 is on printed p. 6, not p. 5. Conjecture 6.2 is on printed p. 11 after its introduction on p. 10. This changes no mathematical clause and does not require a statement revision.

## Independent exhaustive Python result

`python3 probe/check_syy.py > probe/python_results.json` exited 0. All 46,233 permutations in S_1 through S_8 were inspected. Fixed-point counts were `1,1,2,4,9,23,65,199`; one-pass sortable counts were `1,2,4,8,16,32,64,128`. Both preregistered anchors match. Functional-graph traversal found 0 nontrivial cycles; direct comparison found 0 reversed-lex potential violations. Every image preserves its input multiset. The source examples `243 | 15` and West's `3124 -> 1234` also match. This is finite experimental evidence, not a proof of Conjecture 6.2.

## Reuse search and capability

Repository snapshot for the search: `c5f4b69647f63d7b30daa77803017f3db080d3a0`. Pinned Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d` (v4.33.0).

- `git grep -l -i -P 'stack.?sort|2411[.]11914|dotted.pattern|West.{0,20}stack' -- 'D5/**/*.lean' 'Blueprint/**' 'Problems/**' 'Library/**'`: 0 files, exit 1. Positive control with the same scope and flags, `Riordan`: 7 files, exit 0.
- `git -C .lake/packages/mathlib grep -l -i -P 'stack.?sort|dotted.pattern|valley.?run|West.{0,20}stack' -- 'Mathlib/**/*.lean'`: 0 files, exit 1. Positive control `List[.]Perm` in `'Mathlib/Data/List/*.lean'`, same flags: 13 files, exit 0.
- Statement-shape searches for fixed iterates, eventual fixed points, and finite permutation sets located `Function.iterate_fixed`, `List.mem_permutations`, `Nat.stabilises_of_monotone`, and the repository's `finite_orbit_and_readout_eventually_periodic`. The latter was read: it gives an arbitrary positive period, not period one. `iterate_fixed` requires the fixed-point equality as a premise. `Nat.stabilises_of_monotone` requires monotonicity and boundedness. None discharges the machine-specific monotonicity premise by instantiation, projection, or normalization. Direct reuse has not closed the target; no exhaustive nonexistence claim is made.
- Third-party search capability was tested: `gh search code '"stack sorting" language:Lean' --limit 30 --json repository,path,url` succeeded with 0 hits. This is a scoped search, not an exhaustive Lean-ecosystem claim.
- Independent arXiv API query `all:"stack-sorting" AND all:dotted` succeeded, returning this paper and *Permutree sorting* (2007.07802v2). No settlement found in this searched scope. Google Scholar and a complete citation sweep remain unverified.

The initial Mathlib search could not run because `.lake` did not exist. It was rerun after the required cache door succeeded; no bare Lake command preceded that door. This dependency required warming the cache before completing step 2.

## Cache receipt

The exact requested PATH was exported. `make lean-cache-ensure` exited 0. Receipt:

```text
LEAN_CACHE {"status":"seeded","worktree":"/Users/auric/trureturing-op-syy-cycles-probe","donor":"/Users/auric/trureturing","method":"clonefile","reason":null,"stamp_miss":null,"pin_sha256":"sha256:1499ba00eb44d4b760a213127fc10c82158b7595723ae155179378723cf14db3","clonefile_errno":null,"clonefile_errnos":[],"clonefile_attempts":1,"clonefile_cleanup_error":null,"mathlib_missing_olean_files":0,"mathlib_missing_olean_samples":[],"archive_status":"not_attempted","archive_mode":null,"archive_skip_reason":"project olean state is warm","archive_reason":null,"archive_producer_commit_sha":null,"archive_workflow_run_id":null,"mathlib_olean_state":"warm","mathlib_olean_probe_error":null,"project_olean_state":"warm","project_olean_probe_error":null}
```

## Placement proposal

Proposed GID `D5/S1/Words/Patterns/ShiehYangYuMachineConvergence`, path `D5/S1/Words/Patterns/ShiehYangYuMachineConvergence.lean`, adjacent to existing permutation-pattern modules. `git ls-files 'D5/**'` counted 5 tracked files directly in that directory; adding this module gives 6. `DirectoryFileLimit = 96` at `tools/StrataLint.Engine/Rules/RepositoryRules.Structure.cs:65`. No D5 file is created by this probe.

## Formal result and source surface

Public definitions: `IsValley`, `valleyRuns`, `r`, `s`, `M`. The single public theorem is:

```lean
theorem result (n : ℕ) (_hn : 1 ≤ n) (w : List ℕ)
    (hw : w.Perm (List.range' 1 n)) :
    ∃ t : ℕ, (M^[t + 1]) w = (M^[t]) w
```

`valleyRuns` scans from the current valley until the next strictly smaller entry. The current valley is the minimum of the already scanned prefix, so each cut is precisely at an entry strictly smaller than every earlier entry. `s` uses the pop/push/flush algorithm; its stack top is the head. The potential and all proof helpers are private. No maximum decomposition is built into the definition of `s`.

The operational proofs establish permutation preservation, persistence of a maximum at the bottom of the stack, and the derived identity `s (X ++ m :: Y) = s X ++ s Y ++ [m]` for X < m and Y <= m. Splitting the valley runs at their last valley gives the preregistered machine decomposition. Strong induction on word length proves `Phi w <= Phi (M w)` on distinct words. A maximal-potential reachable element of the finite permutation set is fixed, since its successor has equal potential and reversal is injective.

The final command was `/usr/bin/time -l lake env lean probe/SyyProbe.lean`, with the exact required PATH. Exit 0, no warnings. On this macOS ARM64 worktree with the warmed cloned cache:

- Wall time: 7.59 seconds.
- Peak RSS: 1647378432 bytes = 1.647378432 decimal GB.

Exact kernel axiom output:

```text
'SyyProbe.result' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Judgement form

- Public theorem: `SyyProbe.result`.
- `proof_shape: content`.
- Direct frozen project dependencies: **none** (no D5 imports; therefore no dependency GID or statement_id).
- `admission_basis: escape-witness`.
- Escape witness: private `potential_weak`, asserting `Phi w <= Phi (M w)` for every Nodup word, proved by genuine strong induction and the operational stack/run lemmas.
- Test i: **passed**. Lean's elaborated `result` proof directly contains `potential_weak`. `probe/check_dependencies.py` also checks the reduced proof term.
- Test ii: **passed in the searched scope, semantic judgement**. The searched frozen library and pinned Mathlib supply finite maximization, permutations and iterate facts, but no stack/run algorithm or its potential inequality. Expanding this delivery's helpers leaves the stack recursion and length induction, not just instantiation, projections or normalization of existing theorems.
- Test iii: **passed**. The witness is a local one-step comparison on arbitrary distinct words; the public conclusion is eventual equality of iterates on S_n. They are not definitionally equal, aliases or restatements.
- Test iv: **mutant did not compile**. Removing the entire `potential_weak` declaration and replacing its use by `aesop` leaves `Phi (M^[t] w) <= Phi (M (M^[t] w))` unsolved. Lean exits 1; the check script exits 0 for this expected semantic failure. The finite orbit and its maximality survive; maximality gives the opposite inequality. This checks the specified bypass, not the impossibility of every conceivable alternative proof.

The direct dependency survives `Lean.Meta.reduce` with reducible transparency, explicitOnly=false, skipTypes=false, skipProofs=false. Exact audit output: `POTENTIAL_DEPENDENCY raw=true reduced=true`. In the live proof, the inequality is consumed by antisymmetry, then reversal injectivity yields fixedness; it is not a dead let or discarded conjunction component. The failed mutant's error-recovery `sorryAx` is absent from the successful main theorem.

## Witness versus preregistration

The length induction and reversed lexicographic potential are retained. The auxiliary lemma is strengthened to `w <= reverse (s w)` for every word, without a minimum hypothesis. Instantiating at `reverse A ++ [v]` supplies the necessary weak inequality. The proof does not need the preregistered equality-iff-increasing classification. It uses weak monotonicity plus reversal injectivity and finite maximization directly; at a non-fixed point those same facts imply strict increase. This is a disclosed proof restructuring, with no change to the preregistered statement or source definitions.

## Limits and persistence

No mathematical goals remain in this probe. Global literature absence remains unverified: the direct arXiv and GitHub searches have the bounded scopes recorded above; Google Scholar and a complete citation sweep were not run. The source-level Proposition 3.5 identification is deliberately not formalized. Orchestrator replay and independent review remain outside this isolated seat's result.

No claim is made for Conjecture 6.1, repository-wide gates, D5 admission, freezing, a PR, or a merged settlement. All authored sources, experiment data, and this report are committed and pushed on `lane/math/op-syy-cycles-probe`; the paper and all downloads remain only in runner scratch. The result envelope records the exact pushed commits.
