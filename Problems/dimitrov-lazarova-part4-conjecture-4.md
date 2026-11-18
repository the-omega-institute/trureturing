---
slug: dimitrov-lazarova-part4-conjecture-4
bibkey: dimitrovlazarova2026part4c2
doi: 10.3390/math14213935
url: https://mdpi-res.com/d_attachment/mathematics/mathematics-14-03935/article_deploy/mathematics-14-03935.pdf
triage: theorem
motivation_gids:
  - D5/S3/Arith/Divisors/DimitrovPartFourC4.result
---

# Dimitrov and Lazarova Part 4, Conjecture 4

## Problem

For every natural $n\geq2$ and $k\geq1$,

$$
\frac{\varphi(n)^{3k}(\psi(n)+\sigma(n))^{3k}
+\psi(n)^{3k}(\varphi(n)+\sigma(n))^{3k}
+\sigma(n)^{3k}(\varphi(n)+\psi(n))^{3k}}
{\varphi(n)^k\psi(n)^k\sigma(n)^k
(\varphi(n)+\psi(n))^k(\psi(n)+\sigma(n))^k(\varphi(n)+\sigma(n))^k}
\geq\frac{2n^{3k}+(n-1)^{3k}}{n^{2k}(n-1)^k}.
$$

Euler's totient, Dedekind psi and the sum of positive divisors are the actual
arithmetic functions. Powers are ordinary powers, and each parenthesized pair
sum is powered as a whole. Quotients, products and $n-1$ are real. There are no
prime-only, squarefree, finite-range or additional parameter restrictions.
`Nat.totient` is Euler's totient; `OeisA344695GcdSigmaPsiPrimes.psi_prod`
identifies `psi n` with the product of $p^{e-1}(p+1)$ over exact prime-power
factors $p^e$ of nonzero $n$. `ArithmeticFunction.sigma_one_apply` identifies
`ArithmeticFunction.sigma 1 n` with the sum of positive divisors.

The source is Dimitrov and Lazarova, *Mathematics* **14**(21) (2026), 3935,
DOI `10.3390/math14213935`, Section 4, page 13, Conjecture 4,
MathML mm202–204. Definitions are in Section 1, pages 1–2. The source license
is CC BY 4.0. The single whole-paper bibliographic record is
[the existing source note](../Library/ArithUnits/dimitrovlazarova2026part4c2.md).

## Motivation

This is the full external power family. Source Theorem 4 proves only $k=1$.
Numerator estimates alone do not establish this quotient.

## Gap

This is a tier-1 named conjecture in the published source. The finite source
and literature qualification belongs to
[issue 30640](https://github.com/the-omega-institute/trureturing/issues/30640)
and its [original preregistration](https://github.com/the-omega-institute/trureturing/issues/30640#issuecomment-6887262526).
No explicit full prior public settlement was identified within that inspected
scope. ArXiv and Crossref access returned 429; blocked, unindexed and worldwide
priority surfaces remain unverified. The source's exponent-one theorem does
not settle the full event. No worldwide priority claim is made.

## Route

Put $a=\varphi(n)$, $b=\psi(n)$, $c=\sigma(n)$,
$A=a(b+c)$, $B=b(a+c)$, $C=c(a+b)$ and $r=n/(n-1)$.
The existing arithmetic bounds give $0<a\leq n-1$ and $n+1\leq b\leq c$.
Applying the frozen `mixed_bound` at $m=1$, with $q=(n+1)/(n-1)$,
gives $0<A$, $1\leq r\leq B/A\leq C/A$.
Set $x=(B/A)^k$, $y=(C/A)^k$, $R=r^k$. The cleared cubic difference is

$$
R^2(1+x^3+y^3)-(1+2R^3)xy
=R(R^3-1)((x-R)+(y-R))+3R^3((x-R)-(y-R))^2
+(4R^3-1)(x-R)(y-R)+R^2((x-R)^3+(y-R)^3)\geq0.
$$

Thus $(1+x^3+y^3)/(xy)\geq(1+2R^3)/R^2$.
Exact field normalization identifies these two sides with the original source
quotients. The imported arithmetic development retains its supplier attribution
and [license account](../Library/ArithUnits/dimitrov2026c4c5.md); no supplier
code is copied. The elementary factorization has no analytic-novelty claim.

## Falsifier

A natural pair $n\geq2$, $k\geq1$ violating the exact formula would refute it.
A modified arithmetic-function family or a failed method does not refute the
source assertion. Finite successful tests do not establish its universal law.

## Evidence

`D5/S3/Arith/Divisors/DimitrovPartFourC4.result` proves the complete `claim`.
The approved source at `65937383c5491847e346685ec2fe88262e0179f3` has 6396
bytes and SHA-256 `516724f7b146b64f6593170ea3d9102de923d993d397f176b53b89166cf31f01`.
The result statement identity is
`sha256:cb7cb279860399b0cc46239ff31ae85cb1881549d28b8ec0ed9d425be5cd60fa`.
The [independent mathematical evidence](https://github.com/the-omega-institute/trureturing/issues/30640#issuecomment-6887726380)
and [unique mathematical terminal](https://github.com/the-omega-institute/trureturing/issues/30640#issuecomment-6887735234)
identify the unchanged original event, mathematically settled at
`2026-11-15T02:06:30Z`. This mathematical settlement does not certify delivery.

| Declaration | proof_shape | escape_witness | Admission or consumer |
| --- | --- | --- | --- |
| claim | bind-only definition | none | Exact original proposition, consumed by result |
| cubic_ratio_bound (private) | bind-only | none | Consumed by result |
| result | bind-only | none | open-problem-resolution, original preregistration |

Utility is `none`: this is an unbounded symbolic inequality, without a finite
certified positive instance, bounded enumeration, checker or numeric reduction.
The standard axiom boundary is `Classical.choice`, `Quot.sound`, `propext`.
Direct frozen arithmetic prerequisites are `DimitrovLowerBoundsC4C5.psi_ge`,
`sigma_ge_psi` and `mixed_bound`. No corresponding theory volume or digestion
atom was found; the canonical first-freeze route is `deposit-uncovered`.

The source mirror `Reg/D5/S3/Arith/Divisors/DimitrovPartFourC4.lean` expresses
the whole universal law, with the Euler-totient family selected on every
natural input. A constant-3 replacement fails that law at $n=2,k=1$: the
altered left side is $3$, while the unchanged right side is $17/4$.
This witnesses whole-family intervention and sensitivity, not failure of the
original conjecture. Actual totient observations differ at $2$ and $3$.
The continuation is unknown and asserts neither undecidability nor
inexhaustibility. Only the public `result` is a theorem audit target; the
consumed private helper is not a fabricated public target.
The Scribe attaches `OpenProblemResolutionClaim` with `ResolutionKind.Proved`
to the exact result and this dossier.

## Triage

The complete C4 statement is proved using imported arithmetic order bounds,
a mixed-ratio cubic normalization and ordinary real powers. Equality
classification, further consumers and generalizations are not established.
No consequence for another source conjecture is asserted.

## ASSUMED-UNVERIFIED

Worldwide literature coverage and priority, blocked or unindexed sources,
and actual model-family diversity remain unverified. Repository priors were
exposed. Original priors .70/.70, execution `2026-11-15T01:39:18Z`, reporting
deadline `2026-11-15T05:00:00Z`, preregistration and unique mathematical
settlement remain fixed. Publication approval, the first independent triplet,
required CI, normal merge, FirstDEV, full preservation and delivery credit
belong to the caller. Local full content checking is outside this delivery's
scope under [issue 29739](https://github.com/the-omega-institute/trureturing/issues/29739).
