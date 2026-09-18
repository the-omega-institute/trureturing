# Brietzke Conjecture 15 probe

## Preregistered falsifiable predictions

Before executing commands, searches, downloads, or experiments, this probe predicts:

1. An independently written Python implementation of `d(n,k) = (k+1) * choose(2*(n+1), n-k) / (n+1)`, with `d(n,k)=0` when `k>n`, has exact integer division, reproduces the six printed rows, and satisfies the paper's proved identities (21) `sum_j (d(n,5*j+1)-d(n,5*j+2)) = F(2*n)` and (22) `sum_j (d(n,5*j)-d(n,5*j+3)) = F(2*n+1)` for `0 <= n < 300`.
2. `b(n) = sum_j (d(n,4*j)-d(n,4*j+2))` equals `2^n` for every `0 <= n < 300`.
3. The preregistered claim is faithful to the published source. A clause mismatch requires verdict `revise`; a counterexample requires verdict `reject`.
4. The expected proof shape is `bind-only` (Pascal identities, finite telescoping, and normalization). Admission, if the claim closes, is `open-problem-resolution`; no escape witness is claimed. Only a kernel-checked theorem without sorry or new axioms warrants `propose`.

The public definition will explicitly guard `k <= n` and preserve the source expression. Finite sums must cover all nonzero terms. The intended recurrence and its lower boundary will be checked rather than assumed.

## Current result

Source verification: issue #8645 was read through `gh issue view`; the source PDF was downloaded only into the runner scratch directory. Printed pages 16, 17, and 18 were extracted and visually inspected. The definition, six rows, both Proposition 13 identities, and Conjecture 15 match the preregistration clause by clause. The quantified natural row index and zero extension beyond the row follow the lower-triangular Riordan-array interpretation. Conjecture 14 is excluded.

Independent experiment: `python3 probe/check.py` exited 0. All six rows match; both identities (21)/(22) and Conjecture 15 pass for every `0 <= n < 300`. Integer division was checked at every in-range evaluation. The three-term recurrence also passes for `0 <= n < 300, 0 <= k < n+3`, interpreting negative column indices as zero. The subtraction-trap input `d(1,3)` returns zero.

The user-specific probe instructions take precedence over the formal-answer skill's ordinary rendering, extra specialization, D5 writing, and delegated audit defaults: this seat retains only its own work under `probe/`, publishes JSON, and performs no dispatch, reviews, deposits, or PRs. The exact claim is the single formalizable assertion; Python tests are finite evidence only.

## Lean cache capability

Initial pinned-Mathlib reads failed because this isolated worktree had no `.lake` directory. The prescribed PATH was exported verbatim and `make lean-cache-ensure` exited 0 before any Lake command. The missing-package search was then repeated against the seeded pinned package. Receipt:

```text
LEAN_CACHE {"status":"seeded","worktree":"/Users/auric/trureturing-op-brietzke-probe","donor":"/Users/auric/trureturing","method":"clonefile","reason":null,"stamp_miss":null,"pin_sha256":"sha256:1499ba00eb44d4b760a213127fc10c82158b7595723ae155179378723cf14db3","clonefile_errno":null,"clonefile_errnos":[],"clonefile_attempts":1,"clonefile_cleanup_error":null,"mathlib_missing_olean_files":0,"mathlib_missing_olean_samples":[],"archive_status":"not_attempted","archive_mode":null,"archive_skip_reason":"project olean state is warm","archive_reason":null,"archive_producer_commit_sha":null,"archive_workflow_run_id":null,"mathlib_olean_state":"warm","mathlib_olean_probe_error":null,"project_olean_state":"warm","project_olean_probe_error":null}
```
