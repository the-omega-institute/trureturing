---
bibkey: mazhang2026quartic
authors: "Haobo Ma; Wenlin Zhang"
year: 2026
title: "A class-number criterion for the quartic equality after Theorem 5.5"
doi: null
url: "https://oeis.org/A392984"
claim: "The normalized quartic character, its coset coordinates, the actual relative-class-number equality criterion, and the conditional sign congruence described in the supplied historical note."
strata_touched:
  - D5/S3/ArithUnits/MercaQuarticCharacter
  - D5/S3/ArithUnits/MercaQuarticMoments
  - D5/S3/ArithUnits/MercaClassNumberCriterion
  - D5/S3/ArithUnits/MercaKernelBins
  - D5/S3/Arith/CyclotomicFields/MercaQuarticField
  - D5/S3/Arith/CyclotomicFields/MercaQuadraticSubfield
  - D5/S3/Arith/CyclotomicFields/MercaQuarticDiscriminant
  - D5/S3/Arith/CyclotomicFields/MercaQuarticEulerFactors
  - D5/S3/Arith/CyclotomicFields/MercaRealEulerFactors
  - D5/S3/Arith/QuadraticFields/MercaImaginaryQuadratic
  - D5/S3/Arith/QuadraticFields/MercaImaginaryEulerFactors
  - D5/S3/Arith/CharacterSums/MercaPositiveGauss
  - D5/S3/Arith/CharacterSums/MercaImaginaryGauss
  - D5/S3/Arith/CharacterSums/MercaQuadraticQuarter
  - D5/S3/Analytic/Zeta/MercaRelativeClassNumber
  - D5/S3/Analytic/Zeta/MercaImaginaryCharacter
  - D5/S3/Analytic/Zeta/MercaImaginaryClassNumber
  - D5/S3/Analytic/Zeta/MercaSufficientCondition
  - D5/S3/ArithUnits/MercaSquareClassNumberRefutation
license: "CC-BY-4.0 for the Ma–Zhang note; external references retain their own terms."
triage: anchor
---
<!-- GID: D5/L/ArithUnits/mazhang2026quartic -->
# The historical quartic equality criterion

## Verified locator

The proof source is the supplied three-page note by **Haobo Ma and Wenlin
Zhang**, dated 4 November 2026, titled *A class-number criterion for the
quartic equality after Theorem 5.5*. Its PDF has SHA256
`5647e4190409aa4a395e1652109d190791bd3810a18ca98696010ca95a5d9bfb`.
The note is licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
The URL in the metadata locates the OEIS context, not a public release of
the supplied manuscript.

The note explicitly attributes the class-number criterion and conditional
sign rule to **Joseph S. Farland**. His canonical real-coordinate sequence is
[OEIS A392984](https://oeis.org/A392984), whose supplied text revision 39 has
SHA256 `c9aacd853518881a15d0927e639be36d5e655d30e461a68ac2dc7731d31d4bc5`.
OEIS terms apply to that material. The OEIS record alone is not a source
for the note's Delta congruence.

The application is Theorem 5.5, pp. 9–10, of **Haobo Ma, Mircea Merca and
Wenlin Zhang**, *Residue Sums Modulo Products of Two Distinct Odd Primes*,
[arXiv:2610.29608v1](https://arxiv.org/abs/2610.29608v1). Its supplied PDF
has SHA256 `049c9580c9eae46c3ee29f4ff4b9ffde8650e3e626d96b3f449f09d475cfe973`.
The centered predicate concerns the sum of the representatives of H itself.
Its domain includes every admissible odd prime q, including q=3, both below
and above r. The preprint's separate analytic density theorems are outside
this formalization target.

The actual relative class-number formula and its unit and torsion constants
are classical inputs identified in S. R. Louboutin, *A class number problem
for imaginary cyclic number fields of 2-power degrees*, p. 2, equations
(1)–(3), [arXiv:2508.10563v1](https://arxiv.org/abs/2508.10563v1). Its PDF
has SHA256 `265995646873959d0039bc8c850f37ff665ce83c69b7f9600cb5f868a1a14e50`.
The quartic coordinate formulas, square sufficient condition and the
square-but-unequal conductor 181 occur in R. H. Hudson, *Class numbers of
imaginary cyclic quartic fields and related quaternary systems*, Pacific
Journal of Mathematics 115 (1984), 129–142,
[DOI 10.2140/pjm.1984.115.129](https://doi.org/10.2140/pjm.1984.115.129).
The supplied Hudson PDF has SHA256
`724bf32da848550f8bea4ca20e862ffe1b6c99286253f6b962c8be56d3d543cc`.
Its coset labels require an orientation comparison with chi(2)=i.
These citations identify mathematical obligations; they are not assumed
Lean axioms or evidence that the actual-field bridges have been proved.

The complete five-member scientific ZIP has SHA256
`eb1370c82943336475573c0d0ff953ebe64f776b9bb8ab0e99f870c29a2ec3f9`.
Its TeX has SHA256 `f273f4afa05199ad53a17bc5e835aee70a1f524fdcbe232b14175b9410bc1987`,
and its checker has SHA256
`7b215f2530a3a1f245300f23d488a5873a27f19faeb3996fc0c8911182c59e59`.
The original archive is retained in the task's scientific custody.
The 313-prime census through 10000 reports 24 equal-coordinate cases and
49 square relative-class-number cases. Those checker class numbers are
norm-derived finite evidence, not independent ideal-class-group verification
or a universal theorem. No density or all-conductor classification follows.

The native finite character construction covers all primes r congruent to
5 modulo 8, including r=5. Its auxiliary generator is not assumed to be two.
The complete historical class-number theorem retains r>5, which removes
the exceptional quartic cyclotomic conductor. Representative sums in the
ordered cosets K, 2K, -K and -2K give the actual Bernoulli coordinates.
Divisibility by r uses a nonidentity element of K and retains r>5.
Oddness of (r-1)/4 makes both coordinates odd and nonzero. The analytic
value L(0,chi) is identified through the existing Yao Xu supplier with its
retained notices. These finite and special-value results do not establish
the actual-field class-number theorem. No novelty, priority, publication or
author-consent claim is made. Existing mathlib author notices and the
Yao Xu/catalan-lean4 license and attribution chain remain with their suppliers.

The actual-field modules establish the maximal orders, discriminants, CM
unit and torsion constants, local Euler factors and analytic residue bridges.
They prove the relative norm and the signed imaginary class-number quarter
sum in genuine ideal-class semantics. The sign criterion composes these
bridges with the literal subgroup moment, and the sufficient-condition proof
includes the unit square. The conductor-181 refutation uses finite residue
sums together with those universal bridges; it does not claim an independent
class-group computation. The full original first-ten table, interval checks,
r=13 reduced forms and census remain finite scientific custody, with no new
positive-instance theorem library or density claim.
