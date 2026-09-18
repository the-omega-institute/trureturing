# Brietzke Conjecture 15 probe

## Preregistered falsifiable predictions

Before executing commands, searches, downloads, or experiments, this probe predicts:

1. An independently written Python implementation of `d(n,k) = (k+1) * choose(2*(n+1), n-k) / (n+1)`, with `d(n,k)=0` when `k>n`, has exact integer division, reproduces the six printed rows, and satisfies the paper's proved identities (21) `sum_j (d(n,5*j+1)-d(n,5*j+2)) = F(2*n)` and (22) `sum_j (d(n,5*j)-d(n,5*j+3)) = F(2*n+1)` for `0 <= n < 300`.
2. `b(n) = sum_j (d(n,4*j)-d(n,4*j+2))` equals `2^n` for every `0 <= n < 300`.
3. The preregistered claim is faithful to the published source. A clause mismatch requires verdict `revise`; a counterexample requires verdict `reject`.
4. The expected proof shape is `bind-only` (Pascal identities, finite telescoping, and normalization). Admission, if the claim closes, is `open-problem-resolution`; no escape witness is claimed. Only a kernel-checked theorem without sorry or new axioms warrants `propose`.

The public definition will explicitly guard `k <= n` and preserve the source expression. Finite sums must cover all nonzero terms. The intended recurrence and its lower boundary will be checked rather than assumed.

## Current result

**Verdict: reject as an open-problem target, because a published general identity directly specializes to the claimed formula. This is not a numerical refutation.** The preregistration's openness clearance missed the polynomial/diagonal-ratio identity below. No new open-problem resolution is claimed.

Source verification: issue #8645 was read through `gh issue view`; the source PDF was downloaded only into the runner scratch directory. Printed pages 16, 17, and 18 were extracted and visually inspected. The definition, six rows, both Proposition 13 identities, and Conjecture 15 match the preregistration clause by clause. The quantified natural row index and zero extension beyond the row follow the lower-triangular Riordan-array interpretation. Conjecture 14 is excluded.

Independent experiment: `python3 probe/check.py` exited 0. All six rows match; both identities (21)/(22) and Conjecture 15 pass for every `0 <= n < 300`. Integer division was checked at every in-range evaluation. The three-term recurrence also passes for `0 <= n < 300, 0 <= k < n+3`, interpreting negative column indices as zero. The subtraction-trap input `d(1,3)` returns zero.

The user-specific probe instructions take precedence over the formal-answer skill's ordinary rendering, extra specialization, D5 writing, and delegated audit defaults: this seat retains only its own work under `probe/`, publishes JSON, and performs no dispatch, reviews, deposits, or PRs. The exact claim is the single formalizable assertion; Python tests are finite evidence only.

## Lean cache capability

Initial pinned-Mathlib reads failed because this isolated worktree had no `.lake` directory. The prescribed PATH was exported verbatim and `make lean-cache-ensure` exited 0 before any Lake command. The missing-package search was then repeated against the seeded pinned package. Receipt:

```text
LEAN_CACHE {"status":"seeded","worktree":"/Users/auric/trureturing-op-brietzke-probe","donor":"/Users/auric/trureturing","method":"clonefile","reason":null,"stamp_miss":null,"pin_sha256":"sha256:1499ba00eb44d4b760a213127fc10c82158b7595723ae155179378723cf14db3","clonefile_errno":null,"clonefile_errnos":[],"clonefile_attempts":1,"clonefile_cleanup_error":null,"mathlib_missing_olean_files":0,"mathlib_missing_olean_samples":[],"archive_status":"not_attempted","archive_mode":null,"archive_skip_reason":"project olean state is warm","archive_reason":null,"archive_producer_commit_sha":null,"archive_workflow_run_id":null,"mathlib_olean_state":"warm","mathlib_olean_probe_error":null,"project_olean_state":"warm","project_olean_probe_error":null}
```

## Decisive literature locator and exact specialization

1. [OEIS A039598](https://oeis.org/search?q=id%3AA039598&fmt=text), Wolfdieter Lang, **September 20, 2013**, `%C` comment: for the same triangle `T(n,k)`, `rho(N)^(2*n+1) = sum_{k=0..n} T(n,k)*R(N,2*(k+1))`, where `rho(N)=2*cos(pi/N)` and `R(N,2*(k+1))=S(2*k+1,rho(N))`. The comment explicitly holds identically in `N` and points to the proof in A053121. This is a general identity predating the 2024 conjecture.
2. [OEIS A053121](https://oeis.org/search?q=id%3AA053121&fmt=text), L. Edson Jeffery, **September 6, 2012**, `%C` comment: `x^m = sum_{r=0..m} T(m,r)*S(r,x)`. Lang's **September 21, 2013** comment gives the proof source: the triangle is the inverse coefficient matrix of the Chebyshev `S` polynomials. Its `%F` defines the triangle by `(r+1)*choose(m+1,(m-r)/2)/(m+1)` when `m-r` is even and `r<=m`, zero otherwise. Thus its odd-row, odd-column restriction is exactly the source's `d(n,k)`, with no shift or scaling ambiguity.
3. W. Lang, [*On Polynomials Related to Powers of the Generating Function of Catalan's Numbers*](https://www.fq.math.ca/Scanned/38-5/lang.pdf), **Fibonacci Quarterly 38(5) (2000), 408–419**, **Note 4, printed pp. 414–415**, explicitly records the inverse-matrix identity and identifies the inverse as A053121. The downloaded PDF's pages 7–8 were visually inspected. The polynomial convention is `S_m(x)=U_m(x/2)` (equation (15), printed p. 410).

Here is the complete specialization, not a name-only overlap. Put `s=sqrt(2)` in the existing polynomial identity:

```
s^(2*n+1) = sum_{k=0..n} d(n,k) * S_(2*k+1)(s).
```

The defining recurrence `S_(m+2)(s)=s*S_(m+1)(s)-S_m(s)` and `s^2=2` give

```
S_0,...,S_9 = 1, s, 1, 0, -1, -s, -1, 0, 1, s.
```

The consecutive starting pair repeats at indices 8–9, so the recurrence implies period 8 for all indices. Consequently `S_(2*k+1)(s)/s` is `1,0,-1,0` according as `k mod 4` is `0,1,2,3`. Divide the published identity by nonzero `s`: the left side becomes `2^n`; the right side becomes precisely `sum_j (d(n,4*j)-d(n,4*j+2))`. The sum over `j < n+1` includes every nonzero term since `j>=n+1` implies `4*j>n` and `4*j+2>n`. This establishes exact domination without an extra assumption or a new mathematical lemma about the triangle.

`python3 probe/check_literature.py` exited 0: it verified the full polynomial identity coefficient by coefficient for `0 <= n <= 60`, and the displayed period's state repetition in exact integer-pair arithmetic modulo `s^2=2`. These checks verify indexing and normalization on the stated finite ranges; the unbounded dominance argument uses the cited general identity and recurrence uniqueness.

The rejection follows the brief's “already settled (locator)” rule and `tools/scripts/agent/openproblem/TARGET-GATES.md` gate 1, which explicitly treats a prior formula implying the closed form as settlement. No later publication naming “Conjecture 15” was located or is claimed. The 2012/2013 identity and its 2000 published basis suffice for this duplicate decision.

## Repository and pinned-Mathlib deduplication

Repository queries used `git grep -n -P QUERY -- 'D5/*.lean' 'Problems/*' 'Blueprint/*.scribe.cs' 'Library/*' 'docs/develop/theory/*' 'Evidence/*' 'Chronicle/*' 'Meta/Digestion/*'` at content baseline `269e79d20e9ec91b35c4ebf82f9aca288accb790` (subsequent changes are confined to `probe/`). Counts are matching lines and distinct files, not theorem counts.

| Query | Lines | Files | Interpretation |
| --- | ---: | ---: | --- |
| `Brietzke\|A039598` | 0 | 0 | No name hit in the scoped tracked surfaces |
| `[Cc]atalan.{0,20}[Tt]riangle` | 3 | 3 | Unrelated q-Catalan square-sum parity |
| `[Bb]allot` | 16 | 9 | Ballot surnames, voting models, or unrelated Stieltjes refutation |
| `Nat\.choose` | 455 | 106 | Positive control |
| `choose.*n\s*-\s*k\|choose.*4\s*\*\|choose.*4\*\|sum.*catalan\|catalan.*sum` | 71 | 27 | No displayed statement equal to this target |

Pinned Mathlib commit: `db584cd6d46c92f209a44c0f1c829460d327499d`. Full-root searches used `rg -n -i QUERY .lake/packages/mathlib/Mathlib --glob '*.lean'`.

| Query | Lines | Files |
| --- | ---: | ---: |
| `ballot\|catalan.?triangle\|A039598\|Brietzke` | 0 | 0 |
| `Nat\.choose` | 251 | 95 |
| `Nat\.centralBinom` | 13 | 2 |
| `catalan` | 88 | 8 |
| `DyckWord` | 58 | 1 |
| `sum.*[Cc]atalan\|[Cc]atalan.*sum` | 6 | 2 |
| `[Cc]hebyshev.*choose\|choose.*[Cc]hebyshev` | 0 | 0 |

Inspected `Data/Nat/Choose/Basic.lean` (Pascal and multiplicative binomial identities), `Data/Nat/Choose/Central.lean`, `Combinatorics/Enumerative/Catalan/Basic.lean`, Dyck-word declarations, and the Chebyshev module's relevant search hits. No exact Lean theorem was found in this searched scope; this is not an exhaustive equivalence decision. External search capability was available through direct HTTPS retrieval.

## Lean and admission disposition

The duplicate rejection occurs at step 2 before mathematical implementation. No `probe/BrietzkeProbe.lean` or theorem `result` was created, and no `lake env lean` or mutant compile was run. Thus there are no theorem axiom readings, compile seconds, or peak RSS to report. The cache receipt above is a cache-capability result, not proof evidence.

Expected proof shape remains `bind-only` as preregistered. Direct frozen dependencies: none. Escape witness: none. Tests (i) dependency closure, (ii) non-binding novelty, (iii) non-restatement, and (iv) live-path mutant are **not performed**, because no elaborated proof exists and duplicate clearance already failed. The literature specialization also avoids the proposed three-term triangle recurrence, but **was not Lean-compiled**. The planned `open-problem-resolution` admission basis is unavailable after this prior-result finding; this rejection is not caused by bind-only proof shape.

A hypothetical faithful integer implementation would choose `d : Nat -> Nat -> Int` with `if k <= n then ((k+1 : Nat) * Nat.choose (2*(n+1)) (n-k) : Int) / (n+1 : Int) else 0`, proving exactness of integer division explicitly before using it. The result would be `forall n, (sum j in Finset.range (n+1), d n (4*j) - d n (4*j+2)) = (2 : Int)^n`. These are unimplemented statement sketches, not verified Lean text or an admission proposal.

If placement were needed, the subject-domain address would be `D5/S3/ArithSums/BrietzkeCatalanTriangleModFour.lean`, GID `D5/S3/ArithSums/BrietzkeCatalanTriangleModFour`, with public `d` and `result` only. `git ls-files 'D5/S3/ArithSums/*'` counted **13 direct files, 14 recursive files**; one module would make 14 direct files, below `DirectoryFileLimit = 96` at `tools/StrataLint.Engine/Rules/RepositoryRules.Structure.cs:65`. No module is proposed for admission after rejection.

## Boundaries and reasoning discipline

The numeric predictions stand; they do not confer novelty. The unverified-openness premise of the proposed resolution is withdrawn because of the explicit dominating identity. Source fidelity is preserved and no counterexample is claimed. The change of disposition is based on the original rejection criterion, not a changed target or a lowered proof standard. No repository-wide green status, kernel proof, mutant success, independent review, freeze, deposit, PR, merge, or KPI increment is claimed. Current arXiv papers, MathSciNet/zbMATH, and citation-index searches were not needed to establish this earlier published domination and were not independently completed by this seat.

Visible inputs: this brief + GoalArtifact + issue #8645 + source; inherited prior: repo-prior-exposed. Additional independently retrieved literature is identified above. No other probe seat's output was accessed.
