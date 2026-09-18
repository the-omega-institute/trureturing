# Shieh–Yang–Yu Conjecture 6.2 isolated probe

## Falsifiable predictions (registered before checks)

1. An independent Python implementation of West's stack map composed with reversal of each valley run reproduces Theorem 4.4 fixed-point counts for n = 1,...,8: 1,1,2,4,9,23,65,199, and Theorem 4.2 sortable counts 2^(n-1).
2. There is no cycle of length at least two among permutations of 1,...,n for 1 <= n <= 8.
3. At every non-fixed permutation in that range, the reversed output word is strictly larger in lexicographic order than the reversed input word.

These are predictions, not measured results. The source fidelity check precedes execution of the Python experiment. The preregistration defines the barred-pattern stack map by the proved right-hand side of Proposition 3.5; that boundary is retained explicitly.

## Status

Unverified: source fidelity, numerical predictions, library reuse, and Lean proof. No mathematical conclusion is claimed yet.

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

## Lean definitions

`probe/SyyProbe.lean` compiles with the source-form definitions: `IsValley`, recursive maximal valley runs, `r`, West's explicit pop/push/flush stack algorithm `s`, composition `M`, and reversed-word potential `Phi`. The stack helper is private; the maximum-split identity is not used as a definition. The run-based definition scans until the first strictly smaller value, then starts the next run. On distinct words this is exactly the source's valley partition.

Compiled private lemma `westRun_perm`: the operational stack algorithm preserves the combined stack/input multiset, by induction over the actual pop/push recursion.

Compiled private lemma `westRun_sentinel`: a bottom-of-stack element at least as large as all remaining input survives to the final flush. This is proved from the operational recursion, not assumed as a recursive definition of `s`.

Compiled private lemma `westRun_split`: when a new maximum arrives, the earlier input and smaller pending stack are completely emitted before processing the suffix with that maximum on the stack.

Compiled private lemma `s_split_max`: `s (X ++ m :: Y) = s X ++ s Y ++ [m]` when X < m and Y <= m. The source-route maximum identity is now derived from the stack algorithm.

Compiled private lemma `r_perm`: reversing each valley run preserves the whole word multiset.

Compiled private lemma `s_ends_max`: on every nonempty word, including words with duplicates, the operational West map ends in a largest input entry.
