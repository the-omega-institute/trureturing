---
slug: b164660-chebfloor
bibkey: browne2016a164660
doi: null
url: https://oeis.org/search?q=id:A164660&fmt=text
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/BrowneA164660ChebyshevFloorProduct.result
---

# Browne's Chebyshev numerator and floor product

## Problem

Anthony Browne's final FORMULA in OEIS A164660, revision 19, reads:

> a(n+1) = Product_{k=1..n} ( 1-2*(floor(k^n/n)-floor((k^n -1)/n)) ) = (-1)^(A003557(n)) for n>0 (conjecture). - _Anthony Browne_, May 29 2016

The sequence, introduced by Wolfdieter Lang, defines:

> a(n) = numerator(Sum_{m=1..n+1} IT(n,m)), n>=0, with IT(n,m):= A164658(n,m)/A164659(n,m) (coefficient triangle from the indefinite integral Integral_{x} T(n,x), n>=0, in lowest terms).

Let $T_m$ be the first-kind Chebyshev polynomial over $\mathbb Q$ and put
$S_m=\sum_{j=1}^{m+1}[X^{j-1}]T_m/j$ and $a(m)=\operatorname{num}(S_m)$,
where the numerator is reduced and signed with positive denominator.
Let $R(n)=\operatorname{rad}(n)$, including $R(1)=1$.
For every positive natural $n$, the theorem proves

$$
a(n+1)=\prod_{k=1}^{n}\left(1-2\left(\left\lfloor\frac{k^n}{n}\right\rfloor-\left\lfloor\frac{k^n-1}{n}\right\rfloor\right)\right)=(-1)^{n/R(n)}.
$$

The division and subtraction inside each floor are rational; $n/R(n)$ is natural integer division.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Integrated coefficient triangle and row sum | `rowSum` | The coefficient of degree $j-1$ is divided by $j$ and summed over the inclusive interval $1\le j\le m+1$. The integrated coefficient is inlined. |
| Reduced signed numerator | `a` | `Rat.num` retains the positive-denominator convention. |
| Literal floor product | `floorProduct` | Rational subtraction precedes integer floor; the inclusive range is $1\le k\le n$. |
| $n>0$, both equalities | `claim`, `result` | All positive naturals, including one; no extra hypothesis. |
| A003557 exponent | Existing natural radical | $n/\operatorname{rad}(n)$, including the value at one. |

## Motivation

The result settles the entire named final FORMULA preregistered in
[#21736](https://github.com/the-omega-institute/trureturing/issues/21736).
The source note is [browne2016a164660](../Library/Factorization/browne2016a164660.md).
The admission basis is `open-problem-resolution (#21736; Proved)`.
The proof is bind-only after expanding its consumed helpers; no nonbinding escape witness or originality claim is asserted.

## Gap

The source's conjectural status is literature-attested within the screen recorded in #21736.
That screen covers the OEIS dependencies, exact-ID and shape searches, eleven Lang arXiv texts screened by keywords and relevant passages, Finch's nilpotent-count paper, and the Chebyshev identities in DLMF and pinned Mathlib.
No complete settlement was located in those readings. Completeness is `ASSUMED-UNVERIFIED`: OpenAlex and Semantic Scholar returned HTTP 429, later non-arXiv author works and journal versions were not comprehensively enumerated, and the Nyx request returned `model_unavailable`.
The count of nilpotents and the Chebyshev primitive identities are classical ingredients, not new discoveries.

## Route

For positive $n$, the module uses `UniqueFactorizationMonoid.exists_dvd_pow_iff_radical_dvd` and `Nat.dvd_radical_pow_self` to identify the divisibility test, and `Nat.Ioc_filter_dvd_card_eq_div` to count positive multiples.
Its private primitive is
$F_n=T_{n+2}/(2(n+2))-T_n/(2n)$.
The used Mathlib identities `Polynomial.Chebyshev.T_derivative_eq_U` and `Polynomial.Chebyshev.two_mul_T_eq_U_sub_U` give $F'_n=T_{n+1}$.
Polynomial coefficients and endpoint evaluations give the exact rational row sum, and `Rat.num_div_eq_of_coprime` supplies its reduced numerator.
Squarefreeness of the radical and modular arithmetic identify the common sign.

## Falsifier

A positive $n$ violating either equality of `claim`, under these literal definitions, would contradict `result`.
A source-encoding mismatch would invalidate the interpretation as Browne's assertion.
Finite computations alone do not establish the unbounded theorem.

## Evidence

The settling declaration is `D5.S3.ArithSums.BrowneA164660ChebyshevFloorProduct.result` in
[the Lean module](../D5/S3/ArithSums/BrowneA164660ChebyshevFloorProduct.lean).
Its Scribe displays the complete quantified conjunction and carries one Proved resolution claim.
The allowed axiom closure is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

Escape audit unfinished: [#21792](https://github.com/the-omega-institute/trureturing/issues/21792).
The target is the public `result`. No Reg source is retained: the delivery lacks a faithful dependent-family reconstruction, source selection, whole-family sensitivity and observational-dependence evidence. No `declared_validated` status is claimed.

### Independent finite computation

The experiment is [docs/reports/browne-a164660-floor](https://github.com/the-omega-institute/trureturing-experiments/tree/667f2c5d533b57e20191ef70185617523b77d570/docs/reports/browne-a164660-floor), pinned to commit `667f2c5d533b57e20191ef70185617523b77d570`.
Command from that experiment checkout: `python3 docs/reports/browne-a164660-floor/check.py`; exit 0.
The script SHA-256 is `5785e5aa8e60cb1342ec78195a844315ed4fd8b084163f147f73eec1096bf58f`.
It reproduces A164660's rational examples at $m=0..10$ and the first five rational triangle rows; recurrence and binomial coefficients agree at $m=0..301$.
Both target equalities and the integral/parity bridges agree at $n=1..300$, including 45,150 individual floor/divisibility pairs.
These are finite computed results; the uniform statement is supplied by `result`.

## Triage

### What the settlement shows

1. **Proved in prose, with kernel-checked consumed helpers `floor_indicator`, `power_dvd_iff`, `floor_product_eq`.** For an integer $t$ and positive $n$, $\lfloor t/n\rfloor-\lfloor(t-1)/n\rfloor$ is one precisely when $n\mid t$, and zero otherwise. Taking $t=k^n$, radical divisibility is equivalent to $n\mid k^n$. Therefore the factors equal $-1$ precisely at the positive multiples of $R(n)$. Since $R(n)\mid n$, these are $R(n),2R(n),\ldots,(n/R(n))R(n)$, exactly $n/R(n)$ terms.
2. **Kernel-checked consumed helpers `primitive_derivative`, `row_sum_primitive`, `row_sum_evaluation`, `numerator_eq`, `quotient_even_iff`.** The primitive $F_n$ evaluates the literal row sum. For $n\equiv0\pmod4$ it is $1/(n+2)$; for $n\equiv2\pmod4$ it is $-1/n$; otherwise it is $-1/(n(n+2))$. Each denominator is positive, so the reduced numerator is $+1$ precisely when $4\mid n$, and $-1$ otherwise. Also $n/R(n)$ is even precisely when $4\mid n$.
3. **Kernel-checked `result` and consumed helper `row_sum_evaluation`.** The two source equalities hold for every positive $n$, without a squarefree restriction or analytic convergence hypothesis. The displayed exact rational row sums are included in the consumed proof. The read source states no downstream theorem depending on this conjecture; no claim is made about unread dependent literature.
4. **Computed.** The independently implemented recurrence/binomial checker agrees through polynomial index 301 and target index 300, with the command, exit code, immutable experiment revision and SHA-256 in Evidence. It does not assert an unbounded computational search.
5. **Open.** Replacing the exponent $n$ by a general exponent $e$ is outside this settlement. No sharp threshold in $e$ is claimed; the prime-power divisibility conditions require a separate analysis.

## ASSUMED-UNVERIFIED

Literature completeness remains unverified for the explicit access and coverage gaps in Gap.
No claim of world-first discovery follows from the bounded search.
The four-slot escape audit remains unfinished under #21792.
