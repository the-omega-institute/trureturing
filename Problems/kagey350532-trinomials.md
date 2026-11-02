---
slug: kagey350532-trinomials
bibkey: kagey2022a350532
doi: null
url: https://oeis.org/A350532
triage: theorem
motivation_gids:
  - D5/S3/Factorization/Combinatorics/KageyA350532Trinomials.result
---

# Trinomial perfect-power counts over GF(2)

## Problem

P. Kagey's OEIS A350532 COMMENT states verbatim:

> Conjecture: T(2*n,3) = (n^2 - n)/2 for n >= 1.

The settled statement is $T(2n,3)=(n^2-n)/2$ for every $n\in\mathbb N$ with $1\leq n$.

The source's NAME defines the count verbatim:

> Triangle read by rows: T(n,k) is the number of degree-n polynomials over Z/2Z of the form f(x)^m for some m > 1 with exactly k nonzero terms; 1 <= k <= n + 1.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Degree-n polynomials over Z/2Z, exactly k nonzero terms, some exponent m > 1 | `KageyA350532Binomials.T` | The literal cardinality subtype; distinct nonzero polynomials, with witnesses for base and exponent. |
| Conjecture: T(2*n,3) = (n^2 - n)/2 for n >= 1. | `KageyA350532Trinomials.claim` and `KageyA350532Trinomials.result` | Literal universal assertion under the preregistered conventions. |
| No restriction to positive degree in the definition | `p ≠ 0` together with `p.natDegree` | The preregistered nonzero convention prevents zero from entering the degree-zero count. |
| Natural-number variables | The natural-number binders and arithmetic | Subtraction and division in the trinomial assertion are natural-number operations. |

## Motivation

Squaring in characteristic two doubles exponents and preserves support size. If every proper power with two or three terms is a square, contraction reduces its count in degree $2n$ to the count of degree-$n$ polynomials with the same number of terms. Their lower exponents are subsets of $\{0,\ldots,n-1\}$.

## Gap

The named OEIS assertions are the targets of preregistrations [#18613](https://github.com/the-omega-institute/trureturing/issues/18613) and [#18614](https://github.com/the-omega-institute/trureturing/issues/18614). The source and literature screen recorded there found no settlement in the checked sources. Completeness of that screen is ASSUMED-UNVERIFIED.

## Route

The private helper `D5.S3.Factorization.Combinatorics.KageyA350532Binomials.normalized_odd_sparse_power` proves that a polynomial with constant coefficient one whose odd proper power has at most three terms must be one. The proof uses the sparse forms of that power: divisibility of its derivative forces the derivative to vanish. A zero derivative in characteristic two permits exponent contraction, so strong induction on degree closes the argument.

Removing the maximal factor of $X$ reduces a general base to this normalized case. The private helper `sparse_power_even_exponent` then forces every exponent $m>1$ in a representation with two or three terms to be even. Thus the represented polynomial is a square. The private equivalence `squareEquiv` pairs these powers with their contracted roots, and `supportEquiv` pairs degree-$n$ roots with $k$ lower exponents. The public theorem `card_sparse_powers` states $T(2n,k+1)=\binom nk$ for $1\leq k\leq2$.

## Falsifier

A counterexample to the corresponding universal count, a failure of the source cardinality convention, or an unaccepted axiom in the settling declaration would invalidate the settlement. Different representations of the same polynomial contribute only one object to the count.

## Evidence

The mathematical evidence is the corresponding frozen `result` declaration and its imported proof dependencies. The only pre-existing D5 owner used here is `D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity.binary`, used to identify each nonzero coefficient with one. The other polynomial identities and finite-cardinality facts come from pinned Mathlib.

Escape audit unfinished: [#21875](https://github.com/the-omega-institute/trureturing/issues/21875) names the three public theorem targets: the binomial module's `card_sparse_powers` and `result`, and the trinomial module's `result`. No Reg mirror or completed four-slot registration is asserted. The missing evidence is the whole-family reconstruction/equivalence bridge, actual-positive law, intervention/sensitivity and observational dependence.

### Experiment

The independent experiment is [oeis-a350532-gf2-perfect-power-terms](https://github.com/the-omega-institute/trureturing-experiments/tree/9691967bdad8e9339e7fb9b1f5bea04dbead8c74/docs/reports/oeis-a350532-gf2-perfect-power-terms). The pinned `check.py` has SHA-256 `215183113f0d761af9b176c11fa95653a1ec36d94d82268aab1520190a34167d`; its bytes were verified against that revision. Running `python3 /Users/auric/.sshx/63ac023f770a5d350942b283/attempt-1/check.py`, an exact copy of that pinned script, exits 0 with `RESULT PASS`.

The tested scope is all polynomials through degree 10; binomials in degree $2n$ for $1\leq n\leq40$; trinomials in degree $2n$ for $1\leq n\leq20$; and odd-degree trinomials below 40. The same experiment computes the full-support cases through degree 70 and the degree-15 counterexample to the separate first conjecture. None of these finite computations alone proves a uniform formula.

## Triage

### What the settlement shows

1. **Kernel-checked.** Both requested even-degree counts hold for every requested $n$: `KageyA350532Binomials.result` includes $n=0$, while `KageyA350532Trinomials.result` has $1\leq n$.
2. **Kernel-checked, with an elementary consequence in prose.** `KageyA350532Binomials.sparse_power_even_exponent` proves that every representation $f^m$ with $m>1$ and $2\leq |\operatorname{support}(f^m)|\leq3$ has even $m$. Writing $m=2r$ gives $f^m=(f^r)^2$; this last identity is the elementary explanation that these powers are squares.
3. **Kernel-checked.** `KageyA350532Binomials.card_sparse_powers` gives $T(2n,k+1)=\binom nk$ for $1\leq k\leq2$, including $n=0$. At $k=2,n=0$, it gives $T(0,3)=\binom02=0$; this specialization is a consequence of the shared theorem, without a separate public declaration.
4. **Computed.** The experiment entry reproduces the rows through degree 10, the binomial formula for $1\leq n\leq40$, the trinomial formula for $1\leq n\leq20$, and zero trinomial counts at odd degrees below 40. It also verifies the separate first-conjecture failure at 15. That conjecture is outside this settlement.
5. **Proved in prose.** Four terms admit odd proper powers: over $\mathbf F_2$, $(X+X^2)^3=X^3(1+X)^3=X^3+X^4+X^5+X^6$, since both intermediate binomial coefficients are $3\equiv1\pmod2$. This exact algebraic derivation supplies the evidence for this boundary example; it is not a kernel-checked declaration or a result of the pinned counting script.
6. **Open boundary.** No general counting formula for four or more terms is asserted. There is no separately compiled general odd-degree-zero theorem in this delivery. The experiment establishes only the finite odd-degree range stated above. The sparse-power square mechanism explains the odd-degree obstruction, but the public settling declarations are the even-degree formulas.

The decisive mechanism is the derivative obstruction followed by contraction and degree descent. The common count also settles the zero boundary. The four-term example is the sharp obstruction to extending the even-exponent assertion merely by increasing the support bound. The source's independent first conjecture is not an implication of either proved count; its degree-15 failure is a separate computed fact, so the two settlements do not rehabilitate it.

## ASSUMED-UNVERIFIED

Literature completeness and originality beyond the sources screened in the preregistrations are ASSUMED-UNVERIFIED. No claim that every published proof has been excluded is made. The unfinished four-slot escape audit is disclosed in #21875 and is distinct from the kernel proof and the frozen state records.
