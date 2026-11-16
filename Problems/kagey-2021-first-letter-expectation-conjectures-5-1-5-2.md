---
slug: kagey-2021-first-letter-expectation-conjectures-5-1-5-2
bibkey: kagey2021firstletter
doi: 10.48550/arXiv.2112.05281
url: https://arxiv.org/abs/2112.05281v1
triage: theorem
motivation_gids:
  - D5/S1/Words/Permutations/KageyMajorIndexFirstLetter.result
---

# First letters at fixed major index

## Problem

Peter Kagey, *Expected value of letters of permutations with a given number of k-cycles*, arXiv:2112.05281v1, Section 5.2, page 20, Conjecture 5.2 states:

> For fixed k > 0 and n ≥ k, E[π(1) | π ∈ S_n, maj(π) = k] satisfies a rational function in n that is 1/(k + 1) times the quotient of a monic degree-(k + 1) polynomial by a monic degree-k polynomial.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Permutations of $n$ letters | `Equiv.Perm (Fin n)` | Values are shifted by one for one-based letters. |
| Major index | `maj`, sum of one-based descent positions, using `CutFactorization.descentAt` | The final descent indicator is zero. |
| Conditional first-letter mean | `E`, rational weighted sum divided by `count` | The first-letter expression is literal and inlined. |
| Fixed $k>0$ | Universal natural $k$ and its positivity hypothesis in `claim` | No fixed upper bound on $k$. |
| Monic degrees $k+1$ and $k$ | Existential `Polynomial ℚ` pair, both `Monic`, with exact `natDegree` equalities | The quotient need not be reduced. |
| All $n\ge k$ | Universal natural $n$ and `k ≤ n` in `claim` | Includes $n=k$ whenever `count n k ≠ 0`. |
| Conditional expectation is defined | `count n k ≠ 0` | Expresses nonempty conditioning, not an additional restriction on a defined mean. |
| Factor $1/(k+1)$ | `P.eval n / ((k+1) * Q.eval n)` | Rational casts and the denominator factor agree. |

The public definitions `maj`, `count`, `E` and `claim` retain the preregistered bodies. The first-letter expression equals the head of the existing one-line word but is inlined because that owner lies in S3. The proof uses the published `KotesovecA022629.partitions` for positive finite descent sets summing to $k$; no duplicate family definition is introduced.

## Motivation

Preregistration [#19720](https://github.com/the-omega-institute/trureturing/issues/19720) identifies the external tier-1 conjecture. The settling GID is `D5/S1/Words/Permutations/KageyMajorIndexFirstLetter.result`, with `admission_basis: open-problem-resolution (#19720; Proved)`, `generality: I` and `utility: none`. The supporting module `OrderedBlockAllocations` has `generality: G`, `utility: none` and `admission_basis: escape-witness`.

## Gap

Finite enumeration establishes only finitely many instances. The universal claim requires count and first-letter weighted-sum polynomials, together with their exact leading coefficients. The source screen is partial; literature completeness remains `ASSUMED-UNVERIFIED`.

## Route

Increasing permutations on prescribed blocks correspond to allocations with prescribed fiber sizes. Factoring every permutation into its allocation and internal block permutations gives the factorial count. The average minimum in a selected block supplies the first-letter weighted identity. Exact-descent inclusion–exclusion produces polynomials $A_k$ and $B_k$ evaluating to the cardinality and weighted sum of the major-index fiber.

Only $S=U=\{k\}$ reaches the highest degrees. Its coefficients are $1/k!$ for $A_k$ and $1/(k+1)!$ for $B_k$. Hence $Q_k=k!A_k$ and $P_k=(k+1)!B_k$ are monic of degrees $k$ and $k+1$, and their quotient gives the conditional mean.

## Falsifier

A positive natural $k$ and $n\ge k$ with nonempty conditioning whose exact rational mean differs from the asserted quotient would refute the claim. A failed allocation factorization, selected-block weighting, exact-descent inversion or highest-coefficient isolation would invalidate the corresponding proof route.

## Evidence

`D5.S1.Words.Permutations.KageyMajorIndexFirstLetter.result` proves the whole `claim`. Its private `A_eval`, `B_eval`, `A_top`, `B_top`, `Q_monic_degree` and `P_monic_degree` supply the polynomial evaluations and exact degrees. `OrderedBlockAllocations.allocation_card_factorial`, `weighted_increasing_blocks` and `card_increasingOnBlocks` are the consumed public supporting theorems. The publicized owner definition is `KotesovecA022629.partitions`.

The four-slot escape audit is unfinished: [#21383](https://github.com/the-omega-institute/trureturing/issues/21383). No compiled registration supplies the actual dependent allocation/permutation families, source reconstruction, lawful enrolled readout and variation/sensitivity evidence. No `declared_validated` status is asserted.

### Experiment

[Exact enumeration and polynomial comparison](https://github.com/the-omega-institute/trureturing-experiments/tree/4afa5568d3abc96ac08493e9df11977258a4ec08/docs/reports/kagey-2021-first-letter-expectation-conjectures-5-1-5-2) is in the experiments repository. Command: `git -C /Users/auric/trureturing-experiments show 4afa5568d3abc96ac08493e9df11977258a4ec08:docs/reports/kagey-2021-first-letter-expectation-conjectures-5-1-5-2/check.py | python3`, with pipeline failure propagation enabled, exit 0. The script SHA-256 is `d9a4f92ebf3ce0c7391a2632fd166c4f11b3c8890368268df7665e7708b58beb`. The major-index checks cover exactly $1\le k\le8$ and $k\le n\le9$ with nonempty conditioning. They compare $A_k(n)$ and $B_k(n)$ with brute-force counts and sums, verify monicity, integral coefficients and exact degrees of the scaled polynomials, and reproduce source displays (5.3)–(5.6).

## Triage

- **Proved, kernel-checked:** Conjecture 5.2 for all positive $k$ and all $n\ge k$ with nonempty conditioning, by `KageyMajorIndexFirstLetter.result`.
- **Mechanism, kernel-checked:** `Blocks.increasingOnBlocks_iff_descents`, `countPoly_eval_descent`, `weightedPoly_eval_descent`, `A_eval` and `B_eval` identify the finite descent-set polynomial counts and weights; `top_pair_unique`, `A_top` and `B_top` isolate the highest coefficients. These private declarations lie in the settling module.
- **Computed:** the pinned experiment verifies the stated finite major-index range and source displays. Integral coefficients are computed for $1\le k\le8$; a universal integral-coefficient theorem is open and is not asserted by `result`.
- **Endpoint, proved in prose:** at $n=k=1$ or $n=k=2$ no permutation has major index $k$, so conditioning is empty. The theorem retains $n=k$ whenever conditioning is nonempty. A classification of every nonempty conditioning set is open in this delivery.
- **Sibling, kernel-checked existing result:** Conjecture 5.1 concerns inversions and is settled independently by `D5.S3.Combinatorics.Permutation.KageyInversionFirstLetter.result`, associated with [#19726](https://github.com/the-omega-institute/trureturing/issues/19726). It is not on this module's dependency path.
- **Source and literature, literature reading:** arXiv:2112.05281v1 and the dissertation state the conjecture. The checked later works arXiv:2210.17021v2 and arXiv:2602.11061v1, Conger's descent-number paper arXiv:math/0508112, and the OpenishProblems catalog supplied no major-index settlement in the inspected scope. Exhaustive literature completeness is open (`ASSUMED-UNVERIFIED`).
- **Delivery boundary:** `repo-prior-exposed`; the evidence is the kernel-checked symbolic proof, its mirrors and frozen state. No new axiom, `sorry` or `native_decide` occurs in the delivered modules.

### What the settlement shows

The decisive mechanism is finite descent-set inversion with a unique maximal cut pair. It yields exact polynomial counts and weighted sums for every admissible size, not merely an asymptotic expansion. Factorial scaling fixes both leading coefficients and degrees, giving the rational form claimed in the source. The proof covers arbitrary positive major index with no enumeration bound. It does not prove universal integrality of the coefficients, classify all vanishing denominators, or extend the size range below $n=k$. Conjecture 5.1 remains a separate inversion identity with its own existing settlement. No further source theorem is claimed to follow from the major-index settlement.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`: Henry Friedman's 2023 thesis, *Long Increasing Subsequences*, was not retrieved (HTTP 403), and the citation screen is not exhaustive. The four-slot registration remains unfinished under #21383. These boundaries do not alter the proposition proved by `result`.
