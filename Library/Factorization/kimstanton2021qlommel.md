---
bibkey: kimstanton2021qlommel
authors: Jang Soo Kim and Dennis Stanton
year: 2021
title: Three families of q-Lommel polynomials
doi: 10.48550/arXiv.2105.10096
url: https://arxiv.org/abs/2105.10096v3
claim: Conjectures 8.3 and 8.4 prescribe integer polynomial numerators for contiguous basic hypergeometric ratios with the stated floor exponent denominator.
strata_touched:
  - D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore
  - D5/S3/Combinatorics/MotzkinHankel/KimStantonSingleDenominator
  - D5/S3/Combinatorics/MotzkinHankel/KimStantonSimultaneousDenominator
license: citation-only
triage: anchor
---

# Three families of q-Lommel polynomials

## Verified locator

DOI: 10.48550/arXiv.2105.10096

Source: https://arxiv.org/abs/2105.10096v3

## Conjecture 8.3

Printed page 22:

```tex
\begin{conj}
  Let
  \[
     \sum_{n\ge0} \gamma_n(a,b,c) z^n =  \frac{\qhyper21{aq,bq}{cq}{q,z}}{\qhyper21{a,b}{c}{q,z}}.
    \]
Then
  \[
    \frac{\gamma_{n}(a,b,c)}{1-c} = \frac{P_n(a,b,c)}{\prod_{k=0}^n(1-cq^k)^{\flr{\frac{n+1}{k+1}}}},
  \]
  for some polynomial $P_n(a,b,c)$ in $a,b,c,q$ with integer coefficients.
\end{conj}
```


The variables a, b, c, q are algebraically independent. The series is interpreted
as the standard Gasper–Rahman basic hypergeometric series, including the factor
(q;q) in its coefficient denominator. Natural-number division is floor division.
The coefficient index includes zero; its numerator is P₀ = 1.

## Conjecture 8.4

Printed pages 22–23:

```tex
\begin{conj}
  Let
  \[
     \sum_{n\ge0} \gamma'_n(a,b,c) z^n =  \frac{\qhyper21{aq,b}{cq}{q,z}}{\qhyper21{a,b}{c}{q,z}}.
    \]
Then
  \[
    \frac{\gamma'_{n}(a,b,c)}{1-c} = \frac{P'_n(a,b,c)}{\prod_{k=0}^n(1-cq^k)^{\flr{\frac{n+1}{k+1}}}},
  \]
  for some polynomial $P'_n(a,b,c)$ in $a,b,c,q$ with integer coefficients.
\end{conj}
```

## Scope

The reference is arXiv v3. Journal-version equivalence and exhaustive literature
completeness remain ASSUMED-UNVERIFIED. The formal polynomial membership assertions
do not assert numerator positivity, denominator minimality, or values at singular
parameter specializations.
