---
bibkey: parisse2024hypersequences
authors: Daniele Parisse
year: 2024
title: "On Hypersequences of an Arbitrary Sequence and Their Weighted Sums"
doi: 10.5281/zenodo.13331499
url: https://math.colgate.edu/~integers/y70/y70.pdf
claim: "Section 4 states two conjectures: the alternating factorial-Stirling weighted sum of the even-index Fibonacci numbers equals the signed plain weighted sum of the preceding Stirling row, and the same identity with the Lucas numbers in place of the Fibonacci numbers."
strata_touched:
  - D5/S3/Combinatorics/ParisseStirlingFibonacciAlternatingSum
  - D5/S3/Combinatorics/BinomialBases/SecondOrderStirlingTransform
  - D5/S3/Combinatorics/BinomialBases/MonicAnnihilatorStirlingTransform
license: citation-only
triage: anchor
---

# Parisse, hypersequences of an arbitrary sequence and their weighted sums

## Verified locator

DOI: 10.5281/zenodo.13331499

URL: https://math.colgate.edu/~integers/y70/y70.pdf

*Integers* **24** (2024), Article A70, received 8/28/23, revised 9/28/23, accepted
7/22/24, published 8/16/24. The author is Daniele Parisse, Airbus Defence and
Space GmbH, Manching, Germany. The volume index at
https://math.colgate.edu/~integers/vol24.html carries the same author, title and
article number, and the DOI printed on page 2 of the article resolves to the same
record.

## Definitions

For a sequence `(a_n)` the article writes `a_n^{(r)}` for the hypersequence of the
`r`-th generation, defined by `a_n^{(r)} = ∑_{k=0}^{n} a_k^{(r-1)}` with
`a_n^{(0)} = a_n`, and studies the weighted sums
`t_ℓ^{(r)}(n) = ∑_{k=0}^{n} k^ℓ a_k^{(r)}`. Theorem 9 expresses these through the
coefficients

    c_{ℓ,m}(n) = ∑_{k=0}^{m} (-1)^k C(m, k) (k + n + 1)^ℓ ,

which do not depend on `r`. Section 3 writes `S(j, m)` for the Stirling numbers of
the second kind, defined there as the number of partitions of a set of `j`
elements into exactly `m` nonempty blocks, and Equation (3.14) evaluates the
constant term

    c_{ℓ,m}(0) = (-1)^m m! S(ℓ + 1, m + 1) .

`F` denotes the Fibonacci numbers with `F_1 = F_2 = 1` and `L` the Lucas numbers
with `L_0 = 2`, `L_1 = 1`.

## The statements in question

Section 4 applies Theorem 9 to the Fibonacci sequence, obtaining Equation (4.7),
and then states:

> Conjecture 1. For all ℓ ∈ N_0, we have
>
>     ∑_{m=0}^{ℓ} (-1)^m m! S(ℓ+1, m+1) F_{2(m+1)} = (-1)^ℓ ∑_{m=0}^{ℓ} m! S(ℓ, m) F_{m+2} .

The remark immediately after reads: "Note that the unsigned sum on the
right-hand side (the sequence A000557 in [21]) is exactly the sequence `M_{2,j}`."
That remark fixes the reading of the stacked bracket symbols as Stirling numbers
of the second kind rather than binomial coefficients, because A000557 is recorded
as `a(n) = ∑_{k=0..n} k! Stirling2(n, k) Fibonacci(k+2)`.

The Lucas analogue follows the same pattern. After Equation (4.9) the article
states:

> Conjecture 2. For all ℓ ∈ N_0, we have
>
>     ∑_{m=0}^{ℓ} (-1)^m m! S(ℓ+1, m+1) L_{2(m+1)} = (-1)^ℓ ∑_{m=0}^{ℓ} m! S(ℓ, m) L_{m+2} .

with the remark that multiplying the right-hand side by `-1` gives A263968, whose
recorded formula is `a(n) = (-1)^{n+1} ∑_{k=0..n} k! Lucas(k+2) Stirling2(n, k)`.

## Scope of the recorded answer

Both identities hold, and they hold for the same reason: neither depends on the
initial values of the sequence, only on the recurrence `u_{n+2} = u_n + u_{n+1}`.
The recorded result establishes the common generalisation for an arbitrary
integer sequence satisfying that recurrence and reads off the two conjectures as
the Fibonacci and Lucas instances.

## Verified geometric-polynomial locator

URL: https://cs.uwaterloo.ca/journals/JIS/VOL20/Kargin/kargin3.pdf

Levent Kargın, “Some Formulae for Products of Geometric Polynomials with Applications,”
*Journal of Integer Sequences* **20** (2017), Article 17.4.4, pp. 1–15.
The official index is https://cs.uwaterloo.ca/journals/JIS/vol20.html#P17.4.4.
The PDF SHA256 is `a8322d91e173af7449507d27458e445f5114b3c5e602719d0f28c89e3c8a4af0`.
The relevant locators are p. 1 (1), p. 3 (11), (12), p. 4 (13)–(15), and p. 6 (21), (22).

## Normalization and scope

Equation (1) defines `w_n(y)=Σ_k S(n,k) k! y^k`, the ordinary row `Q_n(y)`.
Equations (11)–(13) define the two-variable family, beginning at `n=0`, by
`Σ_n w_n(x;y)t^n/n! = exp(xt)/(1-y(exp(t)-1))`.
The normalization `w_n(1;X)=H_n(X)=Σ_m m!S(n+1,m+1)X^m` follows from
that generating function and the Stirling recurrence.
Equation (21) states `w_n(x;y-1)=(-1)^n w_n(1-x;-y)`.
Setting `x=1` and `y=-X` gives `H_n(-1-X)=(-1)^n Q_n(X)` for every `n≥0`.
Its complex polynomial interpretation is an algebraic consequence; the paper does not print
the complete complex recurrence telescope.

Equation (15), `y w_n(1;y)=(1+y)w_n(y)`, explicitly requires `n>0`.
Equation (22) also requires `n>0` and its rational form has a pole at `y=-1`.
Neither is used as a degree-zero bridge. Coefficient extraction from (21) supports
the ordinary factorial-Stirling coefficient identity without relying on an unverified Qi locator.

## Classical recurrence antecedent

David Zeitlin, “On Summation Formulas and Identities for Fibonacci Numbers,”
*The Fibonacci Quarterly* **5**(1) (February 1967), pp. 1–43:
https://www.fq.math.ca/Scanned/5-1/zeitlin.pdf.
PDF SHA256: `a3d4f3a597fb66ab4c88343ca4a8d253defcc941048a5be1003a051c6c531198`.
Theorem 9, pp. 28–29, (4.21), (4.23), uses the recurrence in p. 22 (4.3),
arbitrary real initial values, and the integer-shift/negative-index convention on p. 23 (4.5).
Its first recurrence coefficient is 1; its second coefficient is the corrected nonzero `b`.
The arbitrary first coefficient in the complete transform is a derived extension,
not a hypothesis of the printed Theorem 9.
No distinct-root hypothesis is stated. Its positive-degree Stirling consequence has ordinary
row coefficients; the shifted row additionally uses the positive-degree bridge.

“Corrections,” *The Fibonacci Quarterly* **5**(2) (April 1967), p. 182:
https://www.fq.math.ca/Scanned/5-2/corrections3.pdf.
PDF SHA256: `a9d4a98bb9e6c068247a6651a54486533bbce0da07288a7f089a603635c95e18`.
The first correction changes `b=0` in (4.3) to `b≠0`. The correction has no verified
author byline; the separate notice signed by Hoggatt does not establish its authorship.
Complex parameters and zero parameters are algebraic extensions of this antecedent,
not hypotheses of the printed theorem. No mathematical priority claim is made for those extensions.

## Positive-degree symmetry

Bernd C. Kellner, “Identities Between Polynomials Related to Stirling and Harmonic Numbers,”
*Integers* **14** (2014), Article A54, pp. 1–22:
https://math.colgate.edu/~integers/o54/o54.pdf.
PDF SHA256: `177ac5644ebaf64078da865e567a2fc4647f044f1e76da0f00585c088576aa17`.
The exact locators are p. 1 (1.1), p. 2 (1.6), and p. 6 Corollary 3.3 and its proof.
For `n≥1`, `F_n=Q_n` and the symmetry of `F_n/X` yields
`X Q_n(-1-X)=(-1)^n(1+X)Q_n(X)`.
The printed real-variable symmetry extends by polynomial identity to complex evaluation.
The restriction `n≥1` is essential: `Q_0=1` and `Q_0/X` is not a polynomial.

## Generalized Newton connections

Robert S. Maier, “Triangular recurrences, generalized Eulerian numbers, and related
number triangles,” *Advances in Applied Mathematics* **146** (2023), 102485.
DOI: 10.1016/j.aam.2023.102485.
URL: https://arxiv.org/abs/2207.10224v2.
The original PDF SHA256 is `25ce9559eb27caa6c6e3eb7a7faf808e67f2bffb18925578102119531b6b3433`.
Definition 4.4 defines S(n,k;a,b;r). Theorem 4.5(ii), equation (4.8), gives
the connection from falling step-a factorials to falling step-b factorials
based at r. Its parameters (a,b;r) correspond to (alpha,b;a) in
`MonicAnnihilatorStirlingTransform`. Equation (4.4) gives the factorial-weighted
row exponential generating function when alpha and b are nonzero. The monic
polynomial convention retains coincident nodes and the all-zero triple.
The full actual-sequence monic-annihilator transform is a polynomial application
of this connection and its row reflection; no priority claim is made for it.

Toufik Mansour, Matthias Schork and Mark Shattuck, “The Generalized Stirling and
Bell Numbers Revisited,” *Journal of Integer Sequences* **15** (2012), Article 12.8.3.
Primary TeX: https://cs.uwaterloo.ca/journals/JIS/VOL15/Schork/schork2.tex.
Its SHA256 is `f3006b7ef496c012bfca9644eaec996857fb2b465fcb0f7de1a9807e3eb1d659`.
Section 2, equations labelled `hsushuie1`, `hsushuie2`, `hsuort` and `hsurec`,
defines S(n,k;alpha,beta,r) by generalized falling-factorial connections and gives
the inverse pair. The recurrence is
`S(n+1,k)=S(n,k-1)+(k beta-n alpha+r)S(n,k)`, with
`S(n,0)=(r|alpha)_n`. Their convention excludes (alpha,beta,r)=(0,0,0).
The monic Newton polynomial convention includes that triple without division by
a step size. These public antecedents establish the coefficient conventions;
they are not citations for the full sequence-annihilator theorem.
