---
bibkey: bala2021fractionalfactorial
authors: Peter Bala
year: 2021
title: "OEIS A347854–A347858: fractional factorial ratios"
doi: null
url: https://oeis.org/A347854
claim: "The sequence is conjectured to be integral."
strata_touched:
  - D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral
  - D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral
  - D5/S3/Arith/FactorialRatio/OeisA347855BalaAuxBIntegral
  - D5/S3/Arith/FactorialRatio/OeisA347855BalaAuxCIntegral
  - D5/S3/Arith/FactorialRatio/OeisA347856BalaHalfIndexIntegral
  - D5/S3/Arith/FactorialRatio/OeisA347857BalaHalfIndexIntegral
  - D5/S3/Arith/FactorialRatio/OeisA347858BalaHalfIndexIntegral
license: citation-only
triage: anchor
---

# Fractional factorial ratios

## Verified locator

Source: https://oeis.org/A347854

Related source entries: https://oeis.org/A347855, https://oeis.org/A347856,
https://oeis.org/A347857, https://oeis.org/A347858.
Peter Bala, Some integer ratios of factorials, pp. 5–6:
https://oeis.org/A276098/a276098.pdf.
J. W. Bober, Factorial ratios, hypergeometric series, and a family of step functions,
Table 2, https://arxiv.org/abs/0709.1977v2, DOI 10.1112/jlms/jdn078.
The floor functions used here are associated with its first eight sporadic ratios.

## Source statements

### A347854 (unpaginated)

> a(n) = (6*n)!/((3*n)!*(2*n)!) * (n/2)!/(3*n/2)!.

> Fractional factorials are defined using the Gamma function; for example, (n/2)! := Gamma(1 + n/2).

> Here we are essentially considering the sequence ( u(n/2) )n>=0. The sequence is conjectured to be integral.

### A347855 (unpaginated)

> a(n) = (4*n)!/((2*n)!*(n)!) * (n/3)!/(4*n/3)!.

> Fractional factorials are defined using the Gamma function; for example, (n/3)! := Gamma(1 + n/3). The sequence defined by u(n) = (12*n)!*n! / ((6*n)!*(4*n)!*(3*n)!) is one of the 52 sporadic integral factorial ratio sequences of height 1 found by V. I. Vasyunin (see Bober, Table 2, Entry 1). See A295431. Here we are essentially considering the sequence (u(n/3))n>=0. The sequence is conjectured to be integral.

> a(3*n+1) = 3^(3*n+1) * b(n), where b(n) = (12*n+4)!/( (6*n+2)!*(3*n+1)!*Product_{k = 0..3*n} (3*n+3*k+4) ) appears to be integral.

> a(3*n+2) = 3^(3*n+2) * c(n), where c(n) = (12*n+8)!/( (6*n+4)!*(3*n+1)!*Product_{k = 0..3*n+2} (3*n+3*k+2) ) appears to be integral. (End)

### A347856 (unpaginated)

> a(n) = (6*n)!/((4*n)!*n!) * (n/2)!/(3*n/2)!.

> Fractional factorials are defined using the Gamma function; for example, (n/2)! := Gamma(1 + n/2).

> The sequence defined by u(n) = (12*n)!/((8*n)!*(2*n)!) * n!/(3*n)! is one of the 52 sporadic integral factorial ratio sequences of height 1 found by V. I. Vasyunin (see Bober, Table 2, Entry 3). See A295433. Here we are essentially considering the sequence (u(n/2))n>=0. The sequence is conjectured to be integral.

### A347857 (unpaginated)

> a(n) = (6*n)!/((3*n)!*(2*n)!) * (3*n/2)!/(5*n/2)!.

> Fractional factorials are defined using the Gamma function; for example, (3*n/2)! := Gamma(1 + 3*n/2). The sequence defined by u(n) = (12*n)!*(3*n)!/((6*n)!*(4*n)!*(5*n)!) is one of the 52 sporadic integral factorial ratio sequences of height 1 found by V. I. Vasyunin (see Bober, Table 2, Entry 5). See A295435. Here we are essentially considering the sequence (u(n/2))n>=0. The sequence is conjectured to be integral.

### A347858 (unpaginated)

> a(n) = (9*n)!/((3*n)!*(2*n)!) * (n/2)!/(9*n/2)!.

> Fractional factorials are defined using the Gamma function; for example, (9*n/2)! := Gamma(1 + 9*n/2).

> The sequence defined by u(n) = (18*n)!*(n)!/((4*n)!*(6*n)!*(9*n)!) is one of the 52 sporadic integral factorial ratio sequences of height 1 found by V. I. Vasyunin (see Bober, Table 2, Entry 7). See A295437. Here we are essentially considering the sequence (u(n/2))n>=0. The sequence is conjectured to be integral.
