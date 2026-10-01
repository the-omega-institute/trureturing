---
slug: van-herstraeten-2024-photon-addition-coefficients
bibkey: vanherstraeten2024majorization
doi: 10.1103/PhysRevA.110.042430
url: https://arxiv.org/abs/2312.02066v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/PhotonAddedMajorizationCoefficients.result
---

# Non-negativity of the photon-addition coefficients

## Problem

Z. Van Herstraeten, N. J. Cerf, S. Guha and C. N. Gagatsos (arXiv:2312.02066,
quant-ph; Phys. Rev. A 110 (2024) 042430) compare a two-mode squeezed vacuum
with `k` photons added to each mode against the single-photon-added state. The
Schmidt coefficients are `q_n^{(kk)} = λⁿ C(n+k,k)² / N_kk`, and the paper
writes `q^{(kk)} = D q^{(11)}` with a lower-triangular Toeplitz matrix `D`
whose entries are `λN_11/N_kk · c_m^{(kk)} λ^m`, where

> \binom{n+k+1}{k}^2 = \sum_{i=0}^{n+1} c_{n-i}^{(kk)} (i+1)^2

and `c_{-1}^{(kk)} = 1`. The columns of `D` sum to `1`. The appendix ends:

> At this point, we conjecture the non-negativity of Eq.
> \eqref{eqapp:Coeffcients}, \textit{i.e.}, we conjecture that the matrix
> $\mathbf{D}$ of Eq. \eqref{eqapp:Dvector} is column stochastic for all
> $k\geq 2$, implying the majorization relation $\hat{\sigma}^{k,k} \prec
> \hat{\sigma}^{1,1}$.

Issue #11700 fixes the reading: `c_n^{(kk)}` (`n ≥ 0`) are the numbers with
`c_{-1}^{(kk)} = 1` that satisfy the expansion for every `n ≥ 0`, and the
conjecture is `c_n^{(kk)} ≥ 0` for all `k ≥ 2` and `n ≥ 0`. The formal `claim`
states that a solution exists and that every solution is non-negative; the
result proves it.

## Motivation

Non-negative `c_n^{(kk)}` make `D` column stochastic, so `q^{(kk)}` is
majorized by `q^{(11)}` and `σ^{k,k}` is at least as entangled as `σ^{1,1}`
for every entanglement monotone. The paper proves the cases `k = 2, …, 8`,
prints closed forms for `k = 2, 3, 4`, and writes that "it seems difficult to
show analytically" the general case. The frozen declaration
`D5/S3/Quantum/Entanglement/PhotonAddedMajorizationCoefficients.result`
proves it for every `k ≥ 2`.

## Gap

Issue #11700 preregisters the reading, the route and the literature check.
OpenAlex lists no citing work of the Phys. Rev. A version, and arXiv searches
for photon addition together with majorization or column stochasticity return
the paper itself and works that do not state these coefficients. The proof is
a power-series factorization; the generating function
`Σ C(n+k,k)² xⁿ = P_k(x)(1−x)^{−(2k+1)}` with `P_k = Σ_j C(k,j)² x^j` is
classical (Euler's transformation of `₂F₁(k+1, k+1; 1; x)`), and this
corollary was not found in the searched sources.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent answer.

## Route

1. The expansion for all `n` is `(1 + Σ_n c_n x^{n+1}) N_1 = N_k` for the
   series `N_k = Σ C(n+k,k)² xⁿ`.
2. `N_1 = (1+x)(1−x)^{−3}`, since `C(n+2,2) + C(n+1,2) = (n+1)²`.
3. Vandermonde, `C(n+k,k) = Σ_j C(k,j) C(n,j)`, and
   `C(n+k,k) C(n,j) = C(k+j,j) C(n+k,k+j)` give
   `N_k = Σ_{j=0}^{k} a_j x^j (1−x)^{−(k+j+1)}` with `a_j = C(k,j) C(k+j,j)`.
4. With `E = (1−x²)^{−1}`, the series
   `B = (1 + (k²+k−1)x)(1−x)^{−(k−2)} E + Σ_{j=2}^{k} a_j x^j (1−x)^{−(k+j−3)} E`
   satisfies `B N_1 = N_k`, because `E(1+x) = (1−x)^{−1}`,
   `(1−x)(1−x)^{−(k+2)} = (1−x)^{−(k+1)}`, `a_0 = 1` and `a_1 = k(k+1)`.
5. For `k ≥ 2` every factor of `B` has non-negative coefficients. `N_1` is not
   a zero divisor, so `1 + Σ c_n x^{n+1} = B` for every solution, and
   `c_n = [x^{n+1}] B ≥ 0`.

## Falsifier

The statement would change if the term `j = 0` were taken alone: for `k = 2`
it is `(1−x)/(1−x²) = 1/(1+x)`, whose coefficients alternate in sign, so the
grouping of `j = 0` with `j = 1` in step 4 is needed. For `k = 1` the
coefficients vanish (`D` is the identity).

## Evidence

Exact integer recomputation (issue #11700): no negative `c_n^{(kk)}` for
`k = 2, …, 15`, `n < 80`; the series `B` reproduces `c_n^{(kk)}` exactly for
`k = 2, …, 15`, `n < 69`; the paper's closed forms for `k = 2, 3, 4` are
reproduced for `n < 40`.

The canonical source is
`D5/S3/Quantum/Entanglement/PhotonAddedMajorizationCoefficients.lean`. Its
public declarations are `Expansion`, `claim` and `result`. The frozen module
state has statement identity
`sha256:86332c30659eb10150722e9c823b6448680ebbf83bafc9d8cfc7430b61b4d864`.
The result declaration has statement identity
`sha256:cf3cc06cea29196dcdb1b273aef9270918fd1d16c2b04059e919ea0dc1e54d78`.
The Freeze event is
`sha256:eff31acbbabd74e425f789f48565073c8401aaa4c494424081706e9ea3da9245`
and has no project-level frozen prerequisites. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 conjecture from a 2023 quant-ph paper, preregistered in issue #11700
before any Lean. `theorem`; resolution `proved`. The public theorem has `proof_shape: bind-only`: Vandermonde's identity, `Nat.choose_mul` and the `invOneSubPow` identities of pinned Mathlib are instantiated and normalized coefficientwise, and the series `B` with the cancellation of `N_1` are local steps of `result`. There is no escape witness. The
admission basis is `open-problem-resolution`. Utility `none`.

### What the settlement shows

**Proved (Lean):** for every `k ≥ 2` a sequence satisfying the expansion
exists, and every such sequence is non-negative for all `n ≥ 0`. That the
expansion determines the sequence is a step inside `result`, not a conjunct of
`claim`.

**Source consequences (paper's derivation, not formalized):** the matrix `D`
is column stochastic for every `k ≥ 2` and every `0 < λ < 1`, so
`σ^{k,k} ≺ σ^{1,1}`; the paper's restriction to `k ≤ 8` is removed.

**Mechanism (proved, inside `result`):** `N_k / N_1` is a sum of products of
`(1−x)^{−d}`, `(1−x²)^{−1}`, monomials and the factor `1 + (k²+k−1)x`, all
with non-negative coefficients. Not formalized (classical identity):
`N_k / N_1 = P_k(x) / ((1−x²)(1−x)^{2k−3})`.

**Not formalized (argument, with computed check):** in
`N_k/N_1 = P_k(x)/((1−x)^{2k−2}(1+x))` the pole at `x = 1` has order `2k−2`.
At `x = −1` there is a simple pole for even `k` and none for odd `k`: the value
`P_k(−1) = Σ_j (−1)^j C(k,j)²` is `0` for odd `k`, where the terms `j` and
`k − j` cancel, and `(−1)^{k/2} C(k,k/2)` for even `k` (computed for
`k ≤ 11`). So `c_n^{(kk)}` is a polynomial of degree `2k−3` in `n`, plus a
multiple of `(−1)ⁿ` for even `k` only, with leading term
`C(2k,k) n^{2k−3} / (2 (2k−3)!)`. This matches the paper's closed forms: the
leading terms `3n`, `5n³/3`, `7n⁵/24`, and an alternating term for `k = 2, 4`
but not for `k = 3`. At `n = 598` the ratio of `c_n^{(kk)}` to the leading
term is `1.003, 1.010, 1.021, 1.036` for `k = 2, 3, 4, 5`.

**Computed, not formalized:** the same column-stochastic route does not
compare `σ^{k,k}` with `σ^{l,l}` for `l ≥ 2`. The quotient `N_k/N_l` has a
negative coefficient for every pair `2 ≤ l < k ≤ 12` checked (`N_3/N_2` starts
`1, 7, 1, 39, −87`). The reason is that `P_l` has a root in `(−1, 0)` for
`l ≥ 2` (for example `−2 + √3` for `l = 2`), which gives `N_k/N_l` a pole
inside the unit disk. Whether `σ^{k,k} ≺ σ^{l,l}` holds is not decided here;
the paper notes that failure of its method would not refute the majorization.

**Computed, not formalized:** for the paper's numerical observation
`σ^{0,l} ≻ σ^{k,l}`, the analogous quotient
`Σ C(n+k,k) C(n+l,l) xⁿ / Σ C(n+l,l) xⁿ` has non-negative coefficients for all
`k, l < 10` checked, consistent with the identity
`C(n+k,k) C(n+l,l) = Σ_j C(k,j) C(l,j) C(n−j+k+l, k+l)` (checked for
`k, l < 9`, `n < 40`), which would give the quotient
`Σ_j C(k,j) C(l,j) x^j (1−x)^{−k}`. This is a candidate for a separate
preregistration and is not part of this settlement.

## ASSUMED-UNVERIFIED

The published Phys. Rev. A text was not read, so it is unverified whether the
conjecture was edited there. The bounded literature check does not establish
exhaustive worldwide novelty, priority, or the absence of an independent
answer. The Lean kernel does not authenticate the external source or its
version history.
