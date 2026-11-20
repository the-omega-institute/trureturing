---
bibkey: coonsspiegelhofer2017hyper
authors: Michael Coons; Lukas Spiegelhofer
year: 2017
title: "The maximal order of hyper-(b-ary)-expansions"
doi: 10.37236/5441
url: https://www.combinatorics.org/ojs/index.php/eljc/article/view/v24i1p15
claim: "Theorem 1 (Defant): limsup s_b(m)/m^{log_b φ} = φ^{log_b(b^2-1)}/√5, where s_b(n) counts hyper-(b-ary)-expansions of n-1; hence the logarithmic limsup exponent of the digit cap b at radix b is log_b φ."
strata_touched:
  - D5/S1/Digit/DigitCapHyperGolden
license: citation-only
triage: anchor
---

# Maximal order of hyper-(b-ary)-expansions

## Verified locator

DOI: 10.37236/5441. Electronic Journal of Combinatorics 24(1) (2017), #P1.15, published
2017-02-03. Source PDF:
https://www.combinatorics.org/ojs/index.php/eljc/article/download/v24i1p15/pdf
(text extracted locally, about 20,400 characters). Definitions and Theorem 1 are on p. 2;
Lemma 2 is in Section 2.

## Source statement

> a hyper-(b-ary)-expansion of n is an expansion n = Σ_{i⩾0} a_i b^i, where
> a_i ∈ {0, 1, . . . , b} and a_i = 0 for all but finitely many indices i.

> For n ⩾ 1, we denote by s_b(n) the number of hyper-(b-ary)-expansions of n − 1;
> moreover, we define s_b(0) = 0.

> Theorem 1 (Defant). If b ⩾ 2 is an integer, then
> lim sup_{m→∞} s_b(m)/m^{log_b ϕ} = ϕ^{log_b(b²−1)}/√5,
> where ϕ = (√5 + 1)/2 is the golden ratio.

> Lemma 2 (Defant). Let k ⩾ 2 and n be positive integers. Then
> max_{b^{k−2} ⩽ n < b^{k−1}} s_b(n) = F_k.

## Mathematical scope

With digit cap b at radix b, s_b(n) is the representation count at n − 1. Theorem 1 gives a
finite positive limsup of s_b(m)/m^{log_b φ}, so the logarithmic limsup of
log s_b(m)/log m is log_b φ, and the same holds for the count at n itself.
