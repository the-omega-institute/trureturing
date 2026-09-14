---
bibkey: laboselemer2013a046528
authors: Labos Elemer; Jaroslav Krizek
year: 2013
title: "OEIS A046528, Numbers that are a product of distinct Mersenne primes"
doi: null
url: https://oeis.org/A046528
claim: "A046528 %N: Numbers that are a product of distinct Mersenne primes (elements of A000668). A046528 %C: n is a product of distinct Mersenne primes iff sigma(n) is a power of 2: see exercise in Sivaramakrishnan, or Shallit. A046528 %C: Supersequence of A051281 (numbers n such that sigma(n) is a power of tau(n)). Conjecture: numbers n such that sigma(n) = tau(n)^(a/b), where a, b are integers >= 1. Example: sigma(93) = 128 = tau(93)^(7/2) = 4^(7/2). - _Jaroslav Krizek_, May 04 2013"
strata_touched:
  - D5/S3/Arith/Mersenne/KrizekSigmaTauRationalPowerMersenne
license: citation-only
triage: anchor
---

# OEIS A046528

The NAME of A046528 states:

> Numbers that are a product of distinct Mersenne primes (elements of A000668).

The known COMMENT states:

> n is a product of distinct Mersenne primes iff sigma(n) is a power of 2: see exercise in Sivaramakrishnan, or Shallit.

Jaroslav Krizek's COMMENT of May 4, 2013 states:

> Supersequence of A051281 (numbers n such that sigma(n) is a power of tau(n)). Conjecture: numbers n such that sigma(n) = tau(n)^(a/b), where a, b are integers >= 1. Example: sigma(93) = 128 = tau(93)^(7/2) = 4^(7/2). - _Jaroslav Krizek_, May 04 2013

The AUTHOR line is:

> _Labos Elemer_

The AUTHOR line carries no date. The metadata year 2013 is the date of
Krizek's conjecture, while Labos Elemer remains first as the sequence author.

## Verified locator

- URL: https://oeis.org/A046528
- NAME (verbatim): Numbers that are a product of distinct Mersenne primes (elements of A000668).
- Known COMMENT (verbatim): n is a product of distinct Mersenne primes iff sigma(n) is a power of 2: see exercise in Sivaramakrishnan, or Shallit.
- Krizek COMMENT (verbatim): Supersequence of A051281 (numbers n such that sigma(n) is a power of tau(n)). Conjecture: numbers n such that sigma(n) = tau(n)^(a/b), where a, b are integers >= 1. Example: sigma(93) = 128 = tau(93)^(7/2) = 4^(7/2). - _Jaroslav Krizek_, May 04 2013

The known classification of the integers with sigma equal to a power of two
is an attributed prerequisite. The OEIS `%D` and `%H` lines point to R.
Sivaramakrishnan, *Classical Theory of Arithmetic Functions*, Dekker, 1989;
Jeffrey Shallit, Problem 1319, *Mathematics Magazine* 63 (1990), 129; and
C. D. H. Cooper, Problem E 2493, *American Mathematical Monthly* 81 (1974),
902, with W. J. Dodge's solution in volume 82 (1975).

Only Krizek's rational-power equivalence is resolved here. It is stated in
the integer-power form `sigma(n)^b = tau(n)^a`, equivalent for these positive
integer bases to `sigma(n) = tau(n)^(a/b)`.
