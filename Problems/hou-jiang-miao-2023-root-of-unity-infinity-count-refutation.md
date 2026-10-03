---
slug: hou-jiang-miao-2023-root-of-unity-infinity-count-refutation
bibkey: hou2024rationalqsystems
doi: 10.21468/SciPostPhys.16.5.129
url: https://arxiv.org/abs/2310.14966
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Combinatorics/RationalQSystemInfinityCountRefutation.result
---

# Refutation of the rational Q-system infinite-root primitive count

## Problem

J. Hou, Y. Jiang and Y. Miao, *Rational Q-systems at Root of Unity I. Closed Chains*, arXiv:2310.14966v3, SciPost Phys. 16, 129 (2024), Appendix C, conjecture (C.2), page 35:

> Before introducing the algorithm, we make the following conjecture for the number of primitive states with infinite Bethe root(s) by observing the numerical results:
> N^{pri}_{±∞}(L, M, n_±) = binom(L, M − n_±) − sum_{x=0}^{M−n_±−1} binom(L,x), (C.2),
> when n_± = n_+ = n_− is a solution to (3.15). When there is no solution to (3.15), N^{pri}_{±∞}(L, M, n_±) = 0.

Appendix C specializes to no twist κ = 1, η = iπ/3, even L and M ≤ L/2. Equations (3.15)–(3.17) imply L ≡ 2(M − n) (mod 6) and 0 ≤ n ≤ 2: η = iπ/3 gives ℓ₁ = 1 and ℓ₂ = 3. For states with infinite roots, n ≥ 1; n ≤ M records that these roots are among the M Bethe roots.

## Motivation

The conjecture supplies the infinite-root primitive counts used by the recursive counting algorithm in Appendix C. The settling declaration is `D5/S0/Certificates/Combinatorics/RationalQSystemInfinityCountRefutation.result`.

## Gap

This is a tier-1 externally published conjecture preregistered in #12305. The issue records a literature check of arXiv v3, the SciPost publication, the checked citing works and MathDB; no settlement is found within that searched scope. The citing-work check is search-seat reported, and the thesis was screened only at abstract level. This is not a claim of exhaustive publication priority.

## Route

Let formula(L,M,n) be the integer-valued right-hand side of (C.2). Let Admissible require even L, 1 ≤ M, 2M ≤ L, 1 ≤ n ≤ 2, n ≤ M and L ≡ 2(M − n) (mod 6). The Lean claim asserts the existence of a natural-valued function N satisfying (N(L,M,n) : ℤ) = formula(L,M,n) at every admissible triple. The true number of primitive states, if (C.2) were correct, would provide such a function. Thus refuting this necessary consequence refutes (C.2) without modelling Bethe states.

At (26,11,1), all admissibility conditions hold. Exact binomial normalization gives binom(26,10) = 5,311,735 and sum_{x=0}^{9} binom(26,x) = 5,658,537. Their difference is −346,802. Natural-number casts into ℤ are nonnegative, which contradicts the claimed equality.

## Falsifier

The witness must satisfy the source's even-length, magnon, infinite-root and congruence restrictions. The computation must use integer subtraction, not truncated natural subtraction. Both obligations are checked inside result by norm_num; no native_decide or new axiom is used. The result would not refute (C.2) if its parameters lay outside the stated scope, or if its negative value came from a different expression.

## Evidence

The sole authored theorem is `result : ¬ claim`. Its local admissibility proof, exact formula evaluation and `Int.natCast_nonneg` application establish the contradiction.

The following independent exact-integer command enumerates all admissible triples through L = 26:

```sh
python3 - <<'PY'
from math import comb
rows = [(L,M,n,comb(L,M-n)-sum(comb(L,x) for x in range(M-n)))
        for L in range(0,27,2) for M in range(1,L//2+1)
        for n in (1,2) if n <= M and (L-2*(M-n)) % 6 == 0]
small = [r for r in rows if r[0] <= 24]
print(len(small), min(r[3] for r in small), len(rows))
print([r for r in rows if r[3] < 0])
print(comb(26,10), sum(comb(26,x) for x in range(10)))
PY
```

Output: `44 1 52`; `[(26,11,1,-346802), (26,12,2,-346802)]`; `5311735 5658537`.

## Triage

Refuted under `admission_basis: open-problem-resolution`, preregistration #12305. There is no digestion atom or cover claim.

### What the settlement shows

- **Proved in this module:** the binomial prefix overtakes the single binomial coefficient at the admissible witness (26,11,1), making the proposed count negative. The source's parity, size and congruence restrictions do not prevent this failure.
- **Computed by the Evidence command:** (C.2) is at least 1 at all 44 admissible triples with L ≤ 24. Through L = 26, its first negative values occur at (26,11,1) and (26,12,2), both −346,802. Positivity in the smaller range does not establish agreement with the true counts.
- **Computed by the Evidence command:** the Appendix C algorithm's use of (C.2) produces impossible infinite-root counts from L = 26 at these two triples. Its resulting count decomposition cannot be justified by (C.2) throughout the stated range.
- **Open:** the first L at which (C.2) disagrees with the true number of primitive states. The true counts are not computed here, including for L ≤ 24.
- **Open:** a corrected expression, a restricted range on which (C.2) equals the true count, and an independent justification of the algorithm's outputs. Nonnegativity is only a necessary condition.
- **Open in this module:** the paper's constrained Q-system construction, descendant-tower results and the identities (C.3)–(C.4) viewed as count decompositions. The refutation targets (C.2); any numerical conclusions that substitute it into these decompositions require independent justification.

## ASSUMED-UNVERIFIED

The source-to-Lean implication uses the meaning of a number of states as a natural number; the module does not construct or count Bethe states. The source specialization and literature screening are external evidence, not kernel theorems. The literature search is scoped, and the abstract-only thesis screening leaves its full text unchecked.
