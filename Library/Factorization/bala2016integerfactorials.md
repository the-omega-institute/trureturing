---
bibkey: bala2016integerfactorials
authors: Peter Bala
year: 2016
title: Some integer ratios of factorials
doi: null
url: https://oeis.org/A276098/a276098.pdf
claim: "The third-index and fifth-index samplings of (30n)!n!/((15n)!(10n)!(6n)!) are integral for every natural n."
strata_touched:
  - D5/S3/Arith/FactorialRatio/OeisA276101BalaThirdIndexIntegral
  - D5/S3/Arith/FactorialRatio/OeisA276102BalaFifthIndexIntegral
license: citation-only
triage: anchor
---

# Third-index and fifth-index fractional factorial ratios

## Verified locator

Source: https://oeis.org/A276098/a276098.pdf

Peter Bala, *Some integer ratios of factorials*, August 2016, page 5, the
unnumbered assertion following equation (11). The note has no located arXiv
identifier or journal edition. The OEIS entries are unpaginated:
https://oeis.org/A276101/internal and https://oeis.org/A276102/internal.

## Source statements

Page 1 defines the notation:

> throughout these notes x! is shorthand for Γ(x + 1)

Page 5 introduces the samplings with “Calculation suggests that the three
sequences” and concludes:

> are also integral for n ≥ 0.

OEIS A276101, NAME:

> a(n) = (10*n)!*(n/3)!/((5*n)!*(10*n/3)!*(2*n)!).

OEIS A276101, COMMENTS:

> Fractional factorials are defined in terms of the gamma function, for example, (n/3)! := gamma(n/3 + 1).

> This is only conjecturally an integer sequence.

OEIS A276102, NAME:

> a(n) = (6*n)!*(n/5)!/((3*n)!*(2*n)!*(6*n/5)!).

OEIS A276102, COMMENTS:

> Fractional factorials are defined in terms of the gamma function, for example, (n/5)! := Gamma(n/5 + 1).

> This is only conjecturally an integer sequence.

The two statements quantify over every natural index, including zero. Their
Lean expressions use Nat.factorial for the integer arguments and Real.Gamma
for the fractional arguments. Integrality is equality to the real cast of an
integer. The statement does not include algebraicity of a generating function
or integrality at arbitrary sampling denominators.

## Literature boundary

The source-specific literature screen is recorded in issues #21665 and #21666.
Its completeness and priority are ASSUMED-UNVERIFIED. No arXiv identifier is
assigned to this OEIS-only source.
