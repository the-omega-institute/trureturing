# Agoh's alternating-numerator characterization is false

## Abstract

A repeated real root is compatible with every alternating numerator factor.

**Definition 1.1 (The literal rational sum).**

$$\operatorname{Q}\left(f, n\right) = \sum_{i = 0}^{n}\frac{(0 - 1)^{i} \cdot \operatorname{choose}\left(n, i\right)}{\operatorname{f}\left(X^{i}\right)}$$

*Formalization.* `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.Q` (`✓ std3`).

*Citation.* Takashi Agoh (2026). *An Intrinsic Factor of an Alternating Sum Involving Certain Rational Functions*. DOI: [10.5281/zenodo.18154119](https://doi.org/10.5281/zenodo.18154119). URL: <https://math.colgate.edu/~integers/aa9/aa9.pdf>.

*Commentary.*

For a real polynomial f and a natural n, Q(f,n) is the alternating sum from i=0 through n of (-1)^i choose(n,i)/f(X^i), in the field of real rational functions. This is Equation (3.1). Polynomial composition supplies f(X^i). Every denominator polynomial is nonzero for the counterexample below.

**Definition 1.2 (An all-order reduced-numerator property).**

$$(\operatorname{NumeratorProperty}\left(f\right)) \Leftrightarrow (\forall n \in Nat,\; (X - 1)^{n} \mid \operatorname{num}\left(\operatorname{Q}\left(f, n\right)\right))$$

*Formalization.* `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.NumeratorProperty` (`✓ std3`).

*Citation.* Takashi Agoh (2026). *An Intrinsic Factor of an Alternating Sum Involving Certain Rational Functions*. DOI: [10.5281/zenodo.18154119](https://doi.org/10.5281/zenodo.18154119). URL: <https://math.colgate.edu/~integers/aa9/aa9.pdf>.

*Commentary.*

The quantifier includes every natural n, including zero. The num operation is the reduced rational-function numerator, not the numerator produced by an arbitrary common denominator.

**Definition 1.3 (The monomial alternative).**

$$(\operatorname{IsMonomial}\left(f\right)) \Leftrightarrow (\exists d \in Nat,\; \exists a \in Real,\; (a \ne 0) \land (f = \operatorname{monomial}\left(d, a\right)))$$

*Formalization.* `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.IsMonomial` (`✓ std3`).

*Citation.* Takashi Agoh (2026). *An Intrinsic Factor of an Alternating Sum Involving Certain Rational Functions*. DOI: [10.5281/zenodo.18154119](https://doi.org/10.5281/zenodo.18154119). URL: <https://math.colgate.edu/~integers/aa9/aa9.pdf>.

*Commentary.*

A monomial has one nonzero real coefficient a at a natural degree d. Constants are included by d=0.

**Definition 1.4 (The simple-root alternative).**

$$(\operatorname{SimpleRootsAwayFromOne}\left(f\right)) \Leftrightarrow (\forall a \in Real,\; (\operatorname{IsRoot}\left(f, a\right)) \Rightarrow ((\operatorname{rootMultiplicity}\left(f, a\right) = 1) \land (a \ne 1)))$$

*Formalization.* `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.SimpleRootsAwayFromOne` (`✓ std3`).

*Citation.* Takashi Agoh (2026). *An Intrinsic Factor of an Alternating Sum Involving Certain Rational Functions*. DOI: [10.5281/zenodo.18154119](https://doi.org/10.5281/zenodo.18154119). URL: <https://math.colgate.edu/~integers/aa9/aa9.pdf>.

*Commentary.*

Every real root must have multiplicity exactly one and be different from one. This predicate is used only on nonzero splitting polynomials.

**Definition 1.5 (The full conjectured equivalence).**

$$(fullClaim) \Leftrightarrow (\forall f \in RealPolynomial,\; ((f \ne 0) \land (\operatorname{Splits}\left(f\right))) \Rightarrow ((\operatorname{NumeratorProperty}\left(f\right)) \Leftrightarrow (\operatorname{IsMonomial}\left(f\right) \lor \operatorname{SimpleRootsAwayFromOne}\left(f\right))))$$

*Formalization.* `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.fullClaim` (`✓ std3`).

*Citation.* Takashi Agoh (2026). *An Intrinsic Factor of an Alternating Sum Involving Certain Rational Functions*. DOI: [10.5281/zenodo.18154119](https://doi.org/10.5281/zenodo.18154119). URL: <https://math.colgate.edu/~integers/aa9/aa9.pdf>.

*Commentary.*

RealPolynomial denotes polynomials over the real numbers. Splits means real-rooted. The all-order numerator property is kept inside the equivalence for each nonzero real-rooted f. The source's Section 3 also assumes f nonconstant and f(1) nonzero; the counterexample satisfies both conditions.

**Definition 1.6 (Base-nine coefficient decoding).**

Lean statement: `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.coefficientDigit`

*Formalization.* `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.coefficientDigit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Takashi Agoh (2026). *An Intrinsic Factor of an Alternating Sum Involving Certain Rational Functions*. DOI: [10.5281/zenodo.18154119](https://doi.org/10.5281/zenodo.18154119). URL: <https://math.colgate.edu/~integers/aa9/aa9.pdf>.

*Commentary.*

A number below 729 contains three base-nine digits. The digit at index i is the quotient by 9^i reduced modulo 9.

**Definition 1.7 (The actual coefficient code).**

Lean statement: `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.actualCode`

*Formalization.* `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.actualCode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Takashi Agoh (2026). *An Intrinsic Factor of an Alternating Sum Involving Certain Rational Functions*. DOI: [10.5281/zenodo.18154119](https://doi.org/10.5281/zenodo.18154119). URL: <https://math.colgate.edu/~integers/aa9/aa9.pdf>.

*Commentary.*

The code 413 has base-nine digits [8,0,5], from least to most significant.

**Definition 1.8 (The actual coefficient word).**

Lean statement: `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.actualWord`

*Formalization.* `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.actualWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Takashi Agoh (2026). *An Intrinsic Factor of an Alternating Sum Involving Certain Rational Functions*. DOI: [10.5281/zenodo.18154119](https://doi.org/10.5281/zenodo.18154119). URL: <https://math.colgate.edu/~integers/aa9/aa9.pdf>.

*Commentary.*

Reading the three digits of 413 gives [8,0,5]. Subtracting four from each digit gives coefficients [4,-4,1].

**Definition 1.9 (The three coefficient readings).**

Lean statement: `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.actualCoefficientReadout`

*Formalization.* `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.actualCoefficientReadout` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Takashi Agoh (2026). *An Intrinsic Factor of an Alternating Sum Involving Certain Rational Functions*. DOI: [10.5281/zenodo.18154119](https://doi.org/10.5281/zenodo.18154119). URL: <https://math.colgate.edu/~integers/aa9/aa9.pdf>.

*Commentary.*

The readings at indices zero, one and two are respectively 8, 0 and 5, exactly the three base-nine digits of 413.

**Definition 1.10 (Signed coefficient decoding).**

Lean statement: `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.decodeCode`

*Formalization.* `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.decodeCode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Takashi Agoh (2026). *An Intrinsic Factor of an Alternating Sum Involving Certain Rational Functions*. DOI: [10.5281/zenodo.18154119](https://doi.org/10.5281/zenodo.18154119). URL: <https://math.colgate.edu/~integers/aa9/aa9.pdf>.

*Commentary.*

Decode a code c by the real number val(c)-4.

**Definition 1.11 (Reconstructing the polynomial).**

Lean statement: `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.polynomialOfWord`

*Formalization.* `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.polynomialOfWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Takashi Agoh (2026). *An Intrinsic Factor of an Alternating Sum Involving Certain Rational Functions*. DOI: [10.5281/zenodo.18154119](https://doi.org/10.5281/zenodo.18154119). URL: <https://math.colgate.edu/~integers/aa9/aa9.pdf>.

*Commentary.*

Sum C(decode(word(i))) times X^i over the three indices. The actual word reconstructs 4-4X+X^2=(X-2)^2.

**Definition 1.12 (The complete algebraic certificate).**

Lean statement: `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.CounterexampleCertificate`

*Formalization.* `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.CounterexampleCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Takashi Agoh (2026). *An Intrinsic Factor of an Alternating Sum Involving Certain Rational Functions*. DOI: [10.5281/zenodo.18154119](https://doi.org/10.5281/zenodo.18154119). URL: <https://math.colgate.edu/~integers/aa9/aa9.pdf>.

*Commentary.*

The certificate requires nonzero, splitting, nonconstant, value one at X=1, the reduced-numerator property for every natural n, not monomial, and failure of the simple-root alternative.

**Definition 1.13 (Reading the counterexample coefficients).**

Lean statement: `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.coefficientArena`

*Formalization.* `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.coefficientArena` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Takashi Agoh (2026). *An Intrinsic Factor of an Alternating Sum Involving Certain Rational Functions*. DOI: [10.5281/zenodo.18154119](https://doi.org/10.5281/zenodo.18154119). URL: <https://math.colgate.edu/~integers/aa9/aa9.pdf>.

*Commentary.*

A state is one code below 729, representing exactly three base-nine digits. The law requires that reading code 413 returns its three digits, together with the complete algebraic certificate for the decoded coefficient word.

**Definition 1.14 (Three coefficient readings).**

Lean statement: `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.actualRealization`

*Formalization.* `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.actualRealization` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Takashi Agoh (2026). *An Intrinsic Factor of an Alternating Sum Involving Certain Rational Functions*. DOI: [10.5281/zenodo.18154119](https://doi.org/10.5281/zenodo.18154119). URL: <https://math.colgate.edu/~integers/aa9/aa9.pdf>.

*Commentary.*

At each index the readout returns the corresponding digit of code 413. Each of the three readings can change independently.

**Theorem 1.15 (The full characterization is false).**

$$\neg fullClaim$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Takashi Agoh (2026). *An Intrinsic Factor of an Alternating Sum Involving Certain Rational Functions*. DOI: [10.5281/zenodo.18154119](https://doi.org/10.5281/zenodo.18154119). URL: <https://math.colgate.edu/~integers/aa9/aa9.pdf>.

*Commentary.*

Take f=(X-2)^2. It is nonzero, real-rooted and nonconstant, with f(1)=1. For each n let t_i=f(X^i), D be their indexed product, and N the weighted sum of products deleting index i. In an auxiliary variable Y, the coefficient of degree k+1 in product_j(Y+t_j) is the elementary symmetric polynomial of degree n-k. Coefficient telescoping therefore gives the indexed deletion identity of Equation (2.3). It preserves repeated values by deleting indices rather than polynomial values. Expanding f^k by its coefficients and applying the binomial theorem changes each inner alternating sum into a sum of coeff(f^k,r)(1-X^r)^n. The remainder theorem shows X-1 divides each 1-X^r, so (X-1)^n divides N. This includes n=0. All t_i evaluate to one at X=1, so D is nonzero and D(1)=1. The literal rational sum equals N/D, and the reduced fraction identity yields num(Q)D=N denom(Q). An explicit Bezout identity makes (X-1)^n coprime to D and cancels D, proving the property for the actual reduced numerator. The nonzero coefficients 4 and -4 rule out a monomial, while root 2 has multiplicity 2. Hence this nonconstant polynomial satisfies the all-order property but neither alternative in the conjectured characterization, so the full equivalence is false.

## References

- Truth anchor: `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.CounterexampleCertificate`
- Truth anchor: `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.IsMonomial`
- Truth anchor: `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.NumeratorProperty`
- Truth anchor: `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.Q`
- Truth anchor: `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.SimpleRootsAwayFromOne`
- Truth anchor: `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.actualCode`
- Truth anchor: `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.actualCoefficientReadout`
- Truth anchor: `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.actualRealization`
- Truth anchor: `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.actualWord`
- Truth anchor: `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.coefficientArena`
- Truth anchor: `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.coefficientDigit`
- Truth anchor: `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.decodeCode`
- Truth anchor: `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.fullClaim`
- Truth anchor: `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.polynomialOfWord`
- Truth anchor: `D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.result`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/AgohCoefficientReadoutTemplate](../ConceptDynamics/InformationEscape/AgohCoefficientReadoutTemplate.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/EscapeRecord](../ConceptDynamics/InformationEscape/EscapeRecord.md)
