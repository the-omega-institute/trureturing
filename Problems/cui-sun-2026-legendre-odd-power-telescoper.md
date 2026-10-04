---
slug: cui-sun-2026-legendre-odd-power-telescoper
bibkey: cuisun2026legendre
doi: 10.48550/arXiv.2607.12330
url: https://arxiv.org/abs/2607.12330v1
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Sun/LegendreOddPowerTelescoper.result
---

# Cui–Sun Conjecture 2.1: integral Legendre telescopers

## Problem

Li-Li Cui and Zhi-Hong Sun, *Curious identities involving Legendre polynomials and Apéry-like numbers*, arXiv:2607.12330v1, page 10, state:

> Suppose that m, p ∈ Z^+. Then there are integral polynomials f_i(t) with degree i (i = 0, 1, …, m − 1) such that (1 − x)^{m+1} Σ_{n=0}^{p−1} (2n + 1)^{2m+1} P_n(x) = pL_m(p, 1 − x)P_{p−1}(x) − pL_m(−p, 1 − x)P_p(x), where L_m(p, t) = (2p + 1)^{2m} t^m + f_{m−1}((2p + 1)^2) t^{m−1} + · · · + f_1((2p + 1)^2) t + f_0.

Equation (1.1), page 1, specifies:

> The famous Legendre polynomials {P_n(x)} are given by P_0(x) = 1, P_1(x) = x and (n + 1)P_{n+1}(x) = (2n + 1)xP_n(x) − nP_{n−1}(x) (n ≥ 1).

The coefficient family is chosen once for each positive m and works for every positive p. The model is an identity in ℚ[X], with integral coefficient polynomials in ℤ[s]; the endpoint parameter of L is an integer.

## Motivation

The frozen declaration `D5/S1/Recurrence/Sun/LegendreOddPowerTelescoper.result` proves the strong, p-independent reading of Conjecture 2.1. Equality as polynomials also includes x = 1 and entails every rational specialization without division by 1 − x.

## Gap

Issue [#12574](https://github.com/the-omega-institute/trureturing/issues/12574) preregisters the Tier 1 numbered conjecture, its verbatim source, the full quantifiers, literature check and proof route. The bounded literature search recorded no settlement in the searched scope. The paper supplies lower cases, rather than the general all-m assertion; its known cases are comparisons, not new results.

## Route

For a monomial in ℤ[s], define

$$
A(s^d)=\sum_{j=1}^{d}\left(4^j\binom{2d}{2j}+2^{2j-1}\binom{2d}{2j-1}\right)s^{d-j},
$$

and extend linearly. Its symmetric-difference identity is

$$
2r(Af)(r^2)=(r+1)f((r+2)^2)+(r-1)f((r-2)^2)-2rf(r^2).
$$

The operator lowers positive degree by one and annihilates constants. Thus its iterates on s^m terminate, and

$$
\ell_m(s,t)=\sum_{j=0}^{m}(-1)^j t^{m-j}A^j(s^m)
$$

satisfies $(t+A)\ell_m=t^{m+1}s^m$. Set $f_i=(-1)^{m-i}A^{m-i}(s^m)$ and evaluate s at $(2p+1)^2$ to obtain the source-shaped L. The Legendre recurrence turns the inverse identity into a boundary difference; summing it over n < p gives the claimed formula.

## Falsifier

A counterexample would be a positive m for which no p-independent integral family of the specified exact degrees satisfies the polynomial identity for every positive p. The route would fail if the operator identity, exact degree lowering, termination or Legendre boundary difference failed.

## Evidence

The public declarations are `P`, `L`, `claim` and `result`. The four private content lemmas are `op_identity_monomial`, `A_iter_degree`, `c_telescoping` and `g_sum`; structural rewrites and source bridges are local proof terms. Only pinned Mathlib modules are imported. The Library note `Library/Analytic/cuisun2026legendre.md` records the source, verbatim statement and DOI locator.

## Triage

Tier 1 external named open problem. Resolution: Proved. Admission basis: `open-problem-resolution (#12574; Proved)`. Utility: `none`; the theorem constructs a family uniformly for unbounded m and p, rather than certifying a finite instance or enumerating bounded cases.

| theorem | proof_shape | decisive content |
| --- | --- | --- |
| `op_identity_monomial` (private) | content | Binomial pairing gives the symmetric operator identity. |
| `A_iter_degree` (private) | content | Leading coefficients establish nonzero iterates of exact successive degrees. |
| `c_telescoping` (private) | content | The terminating inverse cancels all interior coefficients. |
| `g_sum` (private) | content | The recurrence converts that inverse into the Legendre boundary sum. |
| `result` | content | Constructs the common integral family and discharges the entire source-shaped claim. |

Information-escape registration is paused under CLAUDE.md §3.9.

### What the settlement shows

**Proved in this module.** The degree-lowering operator identity and the finite Neumann inverse supply the decisive mechanism. Degree lowering and annihilation of constants make A nilpotent on degree at most m; the proof uses this for the iterates of s^m. The local operator extension and bracket identity in `g_sum` identify the boundary difference with $(2n+1)^{2m+1}(1-X)^{m+1}P_n$. The coefficient family is p-independent, integral, nonzero and of exact degree i for every i < m; these properties occur in `claim` and are discharged by `result`.

**Proved by the coefficient argument.** The local equality `A_coeff_top` gives the top coefficient multiplier

$$
4\binom{2d}{2}+2\binom{2d}{1}=8d^2.
$$

Iterating this equality gives

$$
\operatorname{lc}(f_i)=(-1)^{m-i}\prod_{d=i+1}^{m}8d^2
=(-1)^{m-i}8^{m-i}\left(\frac{m!}{i!}\right)^2.
$$

This closed form is an algebraic consequence of the coefficient argument, not a separately exported or separately compiled Lean theorem. The kernel-checked public conclusion asserts exact degree and nonvanishing. Reflection $L_m(-p-1,t)=L_m(p,t)$ follows directly from the even power and the common square in the definition of `L`; it does not need an extra public declaration.

**Computed, m ≤ 3.** The integer operator reproduces

$$
\ell_1=st-8,
$$
$$
\ell_2=s^2t^2-(32s+48)t+256,
$$
$$
\ell_3=s^3t^3-(72s^2+400s+256)t^2+(2304s+6656)t-18432.
$$

With s = (2p+1)^2 these agree term by term with Corollary 2.1 (equation (2.4)), Corollary 2.5 and Theorem 2.4 of the source. The following exact symbolic command checks the coefficient comparison:

```sh
python3 - <<'PY'
import sympy as S
s, t = S.symbols('s t')
def A(f):
    return S.expand(sum(c * sum((4**j * S.binomial(2*d, 2*j) +
        2**(2*j-1) * S.binomial(2*d, 2*j-1)) * s**(d-j)
        for j in range(1, d+1)) for (d,), c in S.Poly(f, s).terms()))
expected = [s*t-8, s**2*t**2-(32*s+48)*t+256,
    s**3*t**3-(72*s**2+400*s+256)*t**2+(2304*s+6656)*t-18432]
for m in range(1, 4):
    q, value = s**m, 0
    for j in range(m+1):
        value += (-1)**j * t**(m-j) * q
        q = A(q)
    assert q == 0 and S.expand(value-expected[m-1]) == 0
print('COEFFICIENT_COMPARISON_OK m=1..3')
PY
```

**Open.** Uniqueness of the family is not proved in this module. Nor is a corresponding telescoper for other orthogonal-polynomial families, including v_n, proved here; their recurrences require their own operator correspondence.

**Proved / open consequence boundary.** The source-shaped identity is available for every m, so the identity input previously provided by the paper's cases m ≤ 4 has no m cutoff. No all-m mod-p or higher-power congruence is a formal conclusion of this module. Such consequences still require the source's specialization formulas, denominator controls and congruence estimates; their all-m analogues remain open here. The paper's bilinear identities, squared-polynomial sums and Apéry-like-number results are separate statements and receive no automatic all-m extension from this result.

## ASSUMED-UNVERIFIED

The preregistration's citing-work and literature readings are orchestrator-reported; the bounded search does not establish worldwide novelty or priority. Semantic Scholar returned HTTP 429 in that search. No analytic extension, uniqueness theorem, other-family result or all-m supercongruence is claimed as kernel-checked by this module.
