---
slug: kagey-2021-inversion-first-letter-conjecture-5-1
bibkey: kagey2021firstletter
doi: 10.48550/arXiv.2112.05281
url: https://arxiv.org/abs/2112.05281v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Permutation/KageyInversionFirstLetter.result
---

# First letters of permutations with a fixed inversion number

## Problem

Peter Kagey, “Expected value of letters of permutations with a given number of k-cycles”, arXiv:2112.05281v1, Section 5.2, page 20, Conjecture 5.1 states:

> For fixed k and n > k, the expected value of the first letter of a permutation with a given number of inversions satisfies a rational function in n given by E[π(1) | π ∈ S_n, inv(π) = k] = M(n + 1, k)/M(n, k), where M(n, k), as above, is the number of permutations w ∈ S_n such that inv(w) = k.

### Statement echo

| Source clause | Formal counterpart | Fidelity |
| --- | --- | --- |
| Fixed $k$ and $n>k$ | `claim` universally quantifies both natural parameters and assumes $k<n$. | Exact. |
| Permutations in $S_n$ | `Equiv.Perm (Fin n)` and its finite universal set. | Each permutation occurs once. |
| One-based first letter | `PSW.word`, defined by the existing owner as the list of values plus one; `List.headD 0` selects its first entry. | $k<n$ excludes the empty permutation. |
| Inversion number $k$ | `ListInversions.inv` applied to `PSW.word`. | Strict inverted pairs. |
| $M(n,k)$ | `M`, cardinality of the inversion fiber. | Literal source cardinality. |
| Conditional expectation | `E`, rational first-letter sum divided by rational cardinality. | Literal sum-over-cardinality convention. |
| Ratio $M(n+1,k)/M(n,k)$ | The conclusion of `claim` and `result`. | Both casts and the strict guard are retained. |

Rational division is total in Lean. The theorem proves the ratio identity directly; its statement does not include a separate positivity assertion for $M(n,k)$.

## Motivation

Preregistration [#19726](https://github.com/the-omega-institute/trureturing/issues/19726) identifies the external tier-1 conjecture and its literal conventions. The settling GID is `D5/S3/Combinatorics/Permutation/KageyInversionFirstLetter.result`, with admission basis `open-problem-resolution (#19726; Proved)`. Its Scribe carries one `OpenProblemResolutionClaim` with resolution `Proved`.

## Gap

The source and the inspected dissertation state this assertion as a conjecture. Finite enumeration alone cannot settle its universal quantifiers. The inspected later sources and repository search supplied no settlement in their searched scope; literature completeness is `ASSUMED-UNVERIFIED`.

## Route

The order-preserving first-letter decomposition removes exactly the rank of the first letter from the inversion count. Applying this decomposition twice gives two bounded inversion digits. Under $k<n$, a diagonal with total contribution $t$ has $t+1$ admissible digit pairs. Finite sum interchange therefore identifies the natural first-letter weighted numerator with $M(n+1,k)$. Casting this numerator identity to the rationals proves the equality without cancelling a denominator.

## Falsifier

A pair of natural numbers $k<n$ whose exact rational conditional first-letter mean differs from $M(n+1,k)/M(n,k)$ would refute the source claim. A failed inversion-insertion equation or guarded diagonal count would refute the corresponding proof route.

## Evidence

The module is `D5/S3/Combinatorics/Permutation/KageyInversionFirstLetter.lean`. Its sole public theorem `D5.S3.Combinatorics.Permutation.KageyInversionFirstLetter.result` proves `claim` for all natural $k<n$. The public definitions are `M`, `E`, and `claim`. The module reuses `ListInversions.inv`, `PSW.word`, and `Finset.expect_eq_sum_div_card` on the proof path.

The four-slot escape audit for `result` is unfinished: [#20067](https://github.com/the-omega-institute/trureturing/issues/20067). There is no compiled registration establishing the required source-family reconstruction, readout correspondence, observational dependence and independent interventions; no `declared_validated` status is asserted.

### Experiment

[Exact finite enumeration](https://github.com/the-omega-institute/trureturing-experiments/tree/4afa5568d3abc96ac08493e9df11977258a4ec08/docs/reports/kagey-2021-first-letter-expectation-conjectures-5-1-5-2) is stored in the experiments repository. Command: `python3 docs/reports/kagey-2021-first-letter-expectation-conjectures-5-1-5-2/check.py`, run from that repository, exit 0, `RESULT PASS`. The script SHA-256 is `d9a4f92ebf3ce0c7391a2632fd166c4f11b3c8890368268df7665e7708b58beb`. Its Conjecture 5.1 checks cover exactly $0\le k<n\le8$, enumerating permutations through size nine to obtain the next Mahonian counts. These finite readings support the universal theorem and do not replace its proof.

## Triage

- **Proved, kernel-checked:** the exact binding claim for every natural $k<n$, by `KageyInversionFirstLetter.result`.
- **Source identification, literature reading:** Kagey Conjecture 5.1, arXiv:2112.05281v1, Section 5.2, page 20; external tier 1, preregistration #19726.
- **Mechanism, kernel-checked:** the private `inv_decompose` gives the first-letter inversion contribution; `weighted_identity` gives the universal natural numerator identity used by `result`.
- **Computed:** the pinned experiment checks the ratio for exactly $0\le k<n\le8$; its command, exit code and script identity are given above.
- **Boundary, proved in prose:** for $n=k=3$, the only permutation with three inversions is $321$, so the first-letter mean is $3$. The six permutations of size four with three inversions are $1432$, $2341$, $2413$, $3142$, $3214$, and $4123$. Thus $M(4,3)/M(3,3)=6$, and the ratio identity fails without the strict guard. This finite boundary is not a separate Lean theorem.
- **Sibling, source identification:** Conjecture 5.2 concerns the major index and has separate preregistration [#19720](https://github.com/the-omega-institute/trureturing/issues/19720); this inversion theorem does not settle it.
- **Open:** a separately stated denominator-positivity theorem, extensions beyond $k<n$, and exhaustive literature screening. The required integration consists of the frozen settling module, its Scribe and this dossier; the literature boundary remains explicit.

### What the settlement shows

The decisive identity is the weighted numerator, established by the private `weighted_identity` and used in the public `result`. It covers all $k<n$, including the length-one case, with the original conventions. Two successive insertions count the same objects as the first-letter weight because their inversion digits have an untruncated diagonal under the strict guard. The boundary above shows that removing the guard does not preserve the identity. The source's major-index question is a separate statement; no consequence for its settlement is claimed here.

### Declaration classification

The sole public theorem `result` has `proof_shape: content`; its surviving intermediate witness is the private `weighted_identity`, whose derivation uses `inv_decompose`. The module's admission basis is `open-problem-resolution (#19726; Proved)`; `generality: I`, `utility: none`. Its internal length-one decision is an induction base, not a standalone computational certificate.

| Declaration | `proof_shape` | `escape_witness` | Direct consumers |
| --- | --- | --- | --- |
| `result` | content | `weighted_identity` | settling conclusion |
| `E_eq_expect` | bind-only | none | `result` |
| `M_decompose` | content | `inv_decompose` | `double_decompose` |
| `count_ofFn` | bind-only | none | `inv_decompose`, `inv_ofFn_congr` |
| `double_decompose` | content | `inv_decompose` | `weighted_identity` |
| `inv_decompose` | content | `inv_ofFn_congr` | `weighted_decompose`, `double_decompose`, `M_decompose` |
| `inv_ofFn_congr` | content | `inv_ofFn_congr` | `inv_decompose` |
| `rectangle_count` | bind-only | none | `weighted_identity` |
| `sum_digit` | bind-only | none | `rectangle_count` |
| `sum_unit_digit` | bind-only | none | `rectangle_count` |
| `weighted_decompose` | content | `inv_decompose` | `weighted_identity` |
| `weighted_identity` | content | `inv_decompose` | `result` |

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The supplied source screen covers arXiv v1, the author's dissertation, arXiv:2210.17021v2, arXiv:2602.11061v1, Conger's descent paper arXiv:math/0508112, and the OpenishProblems catalog. Unavailable screens include Semantic Scholar (HTTP 429), a thesis source (HTTP 403), and challenged general search engines. Absence of a settlement in this scope establishes neither exhaustive priority nor that no other proof exists.
