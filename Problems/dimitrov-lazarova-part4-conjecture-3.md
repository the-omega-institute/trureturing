---
slug: dimitrov-lazarova-part4-conjecture-3
bibkey: dimitrovlazarova2026part4c2
doi: 10.3390/math14213935
url: https://mdpi-res.com/d_attachment/mathematics/mathematics-14-03935/article_deploy/mathematics-14-03935.pdf
triage: theorem
motivation_gids:
  - D5/S3/Arith/Divisors/DimitrovPartIVC3.result
---

# Dimitrov and Lazarova Part 4, Conjecture 3

## Problem

For every natural $n\geq2$ and $k\geq1$,

$$
\frac{(\varphi(n)+\psi(n))^{3k}+(\psi(n)+\sigma(n))^{3k}+(\varphi(n)+\sigma(n))^{3k}}
{(\varphi(n)+\psi(n))^k(\psi(n)+\sigma(n))^k(\varphi(n)+\sigma(n))^k}
\geq\frac{2n^{3k}+(n+1)^{3k}}{n^{2k}(n+1)^k}.
$$

Euler's totient, Dedekind psi and the sum of positive divisors are the actual
arithmetic functions. Each pair sum is powered as a whole; powers have natural
exponents and quotients are real. There are no prime-only, squarefree,
finite-range or extra parameter restrictions.

The exact source is Section 4, Conjecture 3, page 13; definitions are in
Section 1, pages 1–2. The publisher PDF has 14 pages, 3219707 bytes and SHA-256
`21c972599612cd12ac9354219cc73daa316fcdaff7548ed9be3ee381632a0d3a`.
The XML has 422720 bytes and SHA-256
`2a449be47b8bdecfcccf66158a6bf48b31637512d938e29bc4f5ff880e2507f9`;
MathML mm199–201 contains the formula. The source license is CC BY 4.0.
These identities and source agreement are attributed to the independent
mathematical evidence linked below. The immutable original preregistration is
[comment 6886661956](https://github.com/the-omega-institute/trureturing/issues/30625#issuecomment-6886661956).

## Motivation

This is the complete external power family. The source's Theorem 3 establishes
only $k=1$. Bounds on numerator terms alone do not establish the quotient.

## Gap

This tier-1 named conjecture is stated in a 2026 paper. The bounded source and
ownership qualification is recorded in
[issue 30625](https://github.com/the-omega-institute/trureturing/issues/30625)
and the [source note](../Library/ArithUnits/dimitrovlazarova2026part4c2.md).
The C3 qualification reported current VOR metadata with no notices, all-state
C3 ownership readings 3/3 and DOI readings 8/8, covering eight relevant bodies
and seventeen comments. No full prior solution was found within that inspected
scope. The public Part III C3 supplier `pro20541/dimitrov-conjectures-lean`
addresses a different assertion. C3-specific arXiv access returned 429;
global priority and inaccessible or unindexed sources remain unverified.

## Route

Put $a=\varphi(n)$, $b=\psi(n)$, $c=\sigma(n)$ and $q=(n+1)/n$.
The existing arithmetic bounds give $0<a\leq n-1$, $n+1\leq b\leq c$ and
$q(a+b)\leq2b$. The pair-gap inequality gives
$q^2(a+b)(a+c)\leq(b+c)^2$. Raising this to $k$ gives
$Q^2xy\leq z^2$ for $x=(a+b)^k$, $y=(a+c)^k$, $z=(b+c)^k$ and $Q=q^k\geq1$.
With $u=\sqrt{xy}$, the cubic envelope uses $x^3+y^3\geq2u^3$ and
$z/u\geq Q$ to give
$(x^3+y^3+z^3)/(xyz)\geq Q^2+2/Q$. Exact field normalization recovers the
original quotient, including all three whole pair-sum powers.

## Falsifier

A natural pair $n\geq2$, $k\geq1$ violating the exact formula would refute it.
A relaxed-family counterexample or a failed method does not refute the source
assertion; finite successful tests do not prove its unbounded quantifiers.

## Evidence

`D5/S3/Arith/Divisors/DimitrovPartIVC3.result` proves the complete `claim`.
The approved source at `f07a45e0ee6d370916934bfe609b282838326ef0` has 5734 bytes
and SHA-256 `af221d61daee137ce7fdd6add2538aeb2aa6e43195babce69ee8ca0d16143ca4`.
The [independent mathematical evidence](https://github.com/the-omega-institute/trureturing/issues/30625#issuecomment-6887043322)
and [unique terminal](https://github.com/the-omega-institute/trureturing/issues/30625#issuecomment-6887049344)
identify the unchanged original event, mathematically settled at
`2026-11-15T01:04:17Z`.

| Declaration | proof_shape | escape_witness | Admission or consumer |
| --- | --- | --- | --- |
| claim | bind-only definition | none | Exact original source proposition, consumed by result |
| cubic_envelope (private) | bind-only | none | Consumed by result |
| pair_gap (private) | bind-only | none | Consumed by result |
| result | bind-only | none | open-problem-resolution, original preregistration |

The utility is `none`: the declarations give unbounded symbolic inequalities,
not bounded enumeration, a finite certified positive instance, a checker or a
numerical reduction. No new analytic-content or escape-witness claim is made.
The standard axiom boundary is `Classical.choice`, `Quot.sound`, `propext`.
The directly reused frozen arithmetic bounds are `DimitrovLowerBoundsC4C5.psi_ge`
and `sigma_ge_psi`; function correspondence uses `OeisA344695GcdSigmaPsiPrimes.psi_prod`.
There is no corresponding theory volume or digestion atom; the canonical route
is `deposit-uncovered` for the exact result.

The source mirror in `Reg/D5/S3/Arith/Divisors/DimitrovPartIVC3.lean` expresses
the entire universal law, selecting the totient family on all natural inputs.
A constant-3 replacement family fails the full law at $n=2,k=1$, witnessing
whole-family intervention and sensitivity. Actual totient observations differ
at $n=2$ and $n=3$. The continuation is unknown; it asserts neither
undecidability nor inexhaustibility.
The Scribe attaches `OpenProblemResolutionClaim` with `ResolutionKind.Proved`
to this exact result and this dossier.

## Triage

Proved mechanism: a geometric-mean cubic envelope on powered pair sums,
with its gap supplied by the existing arithmetic order bounds. This extends
the source's Theorem 3 from $k=1$ to every $k\geq1$ and preserves every
$n\geq2$. Sharpness, equality classification, extra consumers and generalizations
are unmeasured. Part IV Conjecture 4 is a documentary successor candidate in
the original evidence, not an additional result or preregistered task here.
No consequence for another source conjecture is asserted.

## ASSUMED-UNVERIFIED

Worldwide literature coverage and priority, blocked or unindexed channels,
and actual model-family diversity remain unverified. Repository priors were
exposed. Original priors .83/.90, execution `2026-11-15T00:38:39Z`, reporting
deadline `2026-11-15T04:00:00Z`, immutable preregistration and unique mathematical
settlement remain fixed. Mathematical approval does not approve publication,
Reg evidence, independent triplet, required CI, merge or delivery credit.
