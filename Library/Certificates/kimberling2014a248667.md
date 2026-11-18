---
bibkey: kimberling2014a248667
authors: Clark Kimberling; Mikhail Kurkov
year: 2014
title: "OEIS A248667: primitive numerator polynomials and Kurkov's composite-term conjecture"
doi: null
url: https://oeis.org/A248667
claim: "Conjecture: any composite term can be represented as a product a(i)*a(j) (i > 1, j > 1) in at least one way."
strata_touched:
  - D5/S3/Arith/PolynomialValues/KurkovA248667CompositeFactorization
license: citation-only
triage: anchor
---

# Primitive numerators and internal factorization

## Verified locator

Source: https://oeis.org/A248667

The source is OEIS A248667, revision 53. The entry is authored by Clark
Kimberling; the conjecture in COMMENTS paragraph 3 is attributed to Mikhail
Kurkov. The electronic entry has no page number, DOI or arXiv identifier.

## Source quotations

NAME:

> Numbers k for which coefficients of the polynomial p(k,x) defined in Comments are relatively prime.

COMMENTS paragraph 1:

> The polynomial p(n,x) is defined as the numerator when the sum 1 + 1/(n*x + 1) + 1/((n*x + 1)(n*x + 2)) + ... + 1/((n*x + 1)(n*x + 2)...(n*x + n - 1)) is written as a fraction with denominator (n*x + 1)(n*x + 2)...(n*x + n - 1). For more, see A248664.

COMMENTS paragraph 3:

> Conjecture: any composite term can be represented as a product a(i)*a(j) (i > 1, j > 1) in at least one way. - _Mikhail Kurkov_, Apr 09 2022

The offset is `1,2`; the entry states:

> so that a(1) = 1 and a(2) = 3.

## Interpretation and scope

The unreduced numerator is the integer polynomial
$P_n(X)=\sum_{j=0}^{n-1}\prod_{i=j+1}^{n-1}(nX+i)$ for positive $n$.
Empty products are one. The exact increasing enumeration contains precisely
the positive $n$ for which $P_n$ is primitive. A dummy value at index zero is
zero. Composite means greater than one and not prime; equal factors and equal
indices are permitted. The theorem includes existence of the enumeration.

The top coefficient is $n^{n-1}$, as follows from the defining polynomial.
Taylor's preceding comment prints $n^n$; this exponent is not used. Its
coefficient-coprimality criterion and the known scalar factorial recurrence
are background, not new claims. The polynomial prime-support argument proves
positive-divisor closure, and powers of three establish infinitude.

The related factorial-recurrence source is Sondow and Schalm,
https://arxiv.org/abs/0709.0671v3, Proposition A.5. It is not the source of
Kurkov's conjecture.

## Computational evidence and limits

The recorded experiment is the-omega-institute/trureturing-experiments,
commit 1ee9383937689b0a4434e5fb1159ef0d933f2f5e,
`docs/reports/kurkov-a248667/check.py`, SHA-256
882bedc7e63061ff596581cc8a1a26bbcccbc320201b138f68b5d7d8137168f0.
The recorded command `python3 docs/reports/kurkov-a248667/check.py` exits 0.
It checks all 649 composite members through 3000; independent polynomial
content calculations extend only through 100. These finite checks do not
prove the universal theorem.

Literature completeness is ASSUMED-UNVERIFIED, with the screened scope and
unread sources stated in issue #23541. Finitude of the excluded-prime set
and density or counting asymptotics are outside the theorem.
