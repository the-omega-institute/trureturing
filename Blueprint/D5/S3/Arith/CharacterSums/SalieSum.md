# Salié sums and quadratic root fibers

## Abstract

Salié reciprocal phases collapse to a quadratic root fiber, giving exact nonsquare cancellation and the uniform square-root bound over every odd finite field.

Let F be any finite field with a decidable equality, psi a complex additive character, and chi the integer-valued quadratic character transported to Complex. The notation chi(F,x), G(F,psi), R(F,psi,a,b), and S(F,psi,a,b) below denotes quadraticCharacterComplex x, quadraticGaussSum psi, quadraticRootPhase psi a b, and salieSum psi a b, respectively. The exact evaluation assumes odd characteristic, psi nontrivial, and b nonzero; a is unrestricted, including zero. The norm theorem also includes b zero.

The mechanism connects two actions. Multiplication by a unit t acts on additive phases by mulShift; the Gauss sum transforms with inverse multiplicative eigencharacter chi(t). Counting the square-map fibers identifies a quadratic exponential sum with that Gauss eigenspace. Completion of the square then converts a linear perturbation into a reciprocal phase. Additive Fourier orthogonality selects the single equation y squared equals 4ab. Thus the reciprocal phase sum collapses to a quadratic root fiber of size at most two. Nonsquares have no roots and cancel exactly.

The stationary interpretation requires a*b nonzero: y=2*a*x identifies y squared equals 4ab with a*x squared equals b on the units, the derivative-zero equation for a*x+b/x. At the singular boundary a=0,b nonzero, the quadratic root fiber contains just zero, while the phase has no stationary point on the units. The exact formula still applies and gives S(F,psi,0,b)=chi(F,b)*G(F,psi).

Kowalski, Exponential sums over finite fields: elementary methods, version of September 14, 2021, Definition 2.18 and Theorem 2.19, equations (2.12)-(2.13), printed page 26 (PDF page 28), give the classical Salié evaluation and bound for two nontrivial additive characters over every odd finite field. Definition 2.1 and Remark 2.2, printed page 17 (PDF page 19), use the same unnormalised Gauss sum. Remark 2.20, printed page 27 (PDF page 29), attributes the elementary additive Fourier method to Sarnak and cites Iwaniec-Kowalski, Analytic Number Theory, Lemma 12.4. The present normalization and the elementary a=0 and b=0 extensions are explained in the cited Library note. No mathematical novelty is claimed.

The Lean proof reuses Mathlib's quadraticChar_card_sqrts, gaussSum_mulShift_eq, additive orthogonality sum_mulShift, gaussSum_sq, and nonvanishing of primitive Gauss sums. The Fourier-to-reciprocal reindexing uses a linear unit bijection and normalization. These steps do not establish a non-binding escape witness under the repository's admission rule. No prime-field restriction, choice of a standard additive character, or extra nonzero assumption on a is imposed.

**Definition 1.1 (The complex quadratic character).**

Lean statement: `D5/S3/Arith/CharacterSums/SalieSum.quadraticCharacterComplex`

*Formalization.* `D5/S3/Arith/CharacterSums/SalieSum.quadraticCharacterComplex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite field F, compose quadraticChar F with Int.castRingHom Complex as a multiplicative character. Its value at zero is zero and its values away from zero are one or minus one. The finite-field and decidable-equality parameters are the same throughout this document.

**Definition 1.2 (The reciprocal phase sum).**

Lean statement: `D5/S3/Arith/CharacterSums/SalieSum.salieSum`

*Formalization.* `D5/S3/Arith/CharacterSums/SalieSum.salieSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every complex additive character psi and a,b in F, S(F,psi,a,b) is the sum over all x in F of chi(F,x) times psi(a*x+b*x inverse). The zero summand vanishes because chi(F,0)=0; Lean's total inverse therefore introduces no additional boundary term.

**Definition 1.3 (The quadratic Gauss sum).**

Lean statement: `D5/S3/Arith/CharacterSums/SalieSum.quadraticGaussSum`

*Formalization.* `D5/S3/Arith/CharacterSums/SalieSum.quadraticGaussSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every complex additive character psi, G(F,psi) is gaussSum quadraticCharacterComplex psi, the sum of chi(F,x)*psi(x) over x in F. In odd characteristic with psi nontrivial its square is chi(F,-1) times the field cardinality and its norm is the square root of that cardinality.

**Definition 1.4 (The quadratic root phase).**

Lean statement: `D5/S3/Arith/CharacterSums/SalieSum.quadraticRootPhase`

*Formalization.* `D5/S3/Arith/CharacterSums/SalieSum.quadraticRootPhase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every psi and a,b in F, R(F,psi,a,b) is the finite sum of psi(y) over exactly those y in F satisfying y squared equals 4*a*b. Roots are counted once each, so the singular zero fiber contains just zero.

**Theorem 1.5 (Character transport is the integer cast).**

Lean statement: `D5/S3/Arith/CharacterSums/SalieSum.quadraticCharacterComplex_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/SalieSum.quadraticCharacterComplex_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every x in F, quadraticCharacterComplex x equals the complex cast of quadraticChar F x. This definitional, bind-only helper is consumed by the quadratic-phase calculation and the character coefficient in the reciprocal reindexing.

**Theorem 1.6 (Counting quadratic roots).**

Lean statement: `D5/S3/Arith/CharacterSums/SalieSum.quadraticRootFiber_card`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/SalieSum.quadraticRootFiber_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If ringChar F differs from two, then for every a,b in F the integer cast of the cardinality of the root set equals quadraticChar F (4*a*b)+1. This is a bind-only application of Mathlib's square-root count. The private root-phase norm estimate consumes it to obtain the cardinality bound two, and the final Salié norm theorem consumes that estimate.

**Theorem 1.7 (An empty quadratic root fiber contributes zero).**

Lean statement: `D5/S3/Arith/CharacterSums/SalieSum.quadraticRootPhase_eq_zero_of_not_isSquare`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/SalieSum.quadraticRootPhase_eq_zero_of_not_isSquare` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every psi,a,b, if 4*a*b is not a square, R(F,psi,a,b)=0. No odd-characteristic or nontrivial-character assumption is needed for this empty-sum statement. This bind-only helper is consumed by salieSum_eq_zero_of_not_isSquare.

**Theorem 1.8 (A quadratic phase lies in the Gauss eigenspace).**

Lean statement: `D5/S3/Arith/CharacterSums/SalieSum.quadraticPhase_sum_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/SalieSum.quadraticPhase_sum_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every odd finite field F, nontrivial complex additive character psi, and unit t of F, the sum of psi(t*x squared) over x equals chi(F,t) inverse times G(F,psi). Sum over fibers of x maps to x squared, replace each fiber cardinality by chi(F,z)+1, and eliminate the additive-character sum. Mathlib's Gauss shift law evaluates the remaining term. This bind-only combination of existing fiber and character identities is consumed by the private completed-square theorem, then by salieSum_fourier and the exact evaluation.

**Theorem 1.9 (The boundary with zero reciprocal coefficient).**

Lean statement: `D5/S3/Arith/CharacterSums/SalieSum.salieSum_zero_right`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/SalieSum.salieSum_zero_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emmanuel Kowalski (2021). *Exponential sums over finite fields: elementary methods*. URL: <https://people.math.ethz.ch/~kowalski/exponential-sums-elementary.pdf>.

*Commentary.*

For every odd finite field, every complex additive character psi, and every a, S(F,psi,a,0) is zero when a=0 and is chi(F,a)*G(F,psi) otherwise. This elementary extension of the cited formula does not require psi nontrivial. Nontriviality of the quadratic character handles a=0; the Gauss shift law handles a nonzero, and the character is its own inverse. This bind-only boundary calculation is consumed by salieSum_norm_le.

**Theorem 1.10 (Exact evaluation over every odd finite field).**

$$\forall F:Type, [\operatorname{Field}\left(F\right)] [\operatorname{Fintype}\left(F\right)] [\operatorname{DecidableEq}\left(F\right)] \forall psi:\operatorname{AddChar}\left(F, Complex\right), \forall a:F, \forall b:F, \operatorname{ringChar}\left(F\right)\neq 2 \land psi\neq 1 \land b\neq 0 \implies \operatorname{S}\left(F, psi, a, b\right)=\operatorname{chi}\left(F, b\right)\cdot \operatorname{G}\left(F, psi\right)\cdot \operatorname{R}\left(F, psi, a, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/SalieSum.salieSum_eq` (`✓ std3`). ∎

*Citation.* Emmanuel Kowalski (2021). *Exponential sums over finite fields: elementary methods*. URL: <https://people.math.ethz.ch/~kowalski/exponential-sums-elementary.pdf>.

*Commentary.*

Additive orthogonality gives q*R as the sum over t of psi(-4abt) times Q(t), where Q(t) is the sum over y of psi(t*y squared+y). For t nonzero, translate y by the inverse of 2t and use quadraticPhase_sum_eq: Q(t)=chi(F,t) inverse times G times psi(-(4t) inverse). The t=0 term is explicitly zero because psi is nontrivial.

The unit bijection t maps to -4bt converts this Fourier sum into chi(F,-b)*G*S. The character coefficient follows from chi(F,4)=1 and chi(F,-b) squared equal to one. Combine this relation with G squared equal to chi(F,-1)*q and cancel the nonzero coefficient to obtain the displayed evaluation. This chain combines existing identities, linear reindexing and normalization; it supplies no independently established escape witness. Its consumers are the nonsquare theorem and the square branch of the norm theorem.

**Theorem 1.11 (Nonsquare products cancel exactly).**

$$\forall F:Type, [\operatorname{Field}\left(F\right)] [\operatorname{Fintype}\left(F\right)] [\operatorname{DecidableEq}\left(F\right)] \forall psi:\operatorname{AddChar}\left(F, Complex\right), \forall a:F, \forall b:F, \operatorname{ringChar}\left(F\right)\neq 2 \land psi\neq 1 \land b\neq 0 \land \neg \operatorname{IsSquare}\left(a\cdot b\right) \implies \operatorname{S}\left(F, psi, a, b\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/SalieSum.salieSum_eq_zero_of_not_isSquare` (`✓ std3`). ∎

*Citation.* Emmanuel Kowalski (2021). *Exponential sums over finite fields: elementary methods*. URL: <https://people.math.ethz.ch/~kowalski/exponential-sums-elementary.pdf>.

*Commentary.*

If a*b is not a square and b is nonzero, the exact evaluation vanishes. A putative root of 4ab would yield a square root of ab after division by two. This bind-only consequence of the exact evaluation is consumed on the nonsquare branch of salieSum_norm_le.

**Theorem 1.12 (Uniform square-root cancellation).**

$$\forall F:Type, [\operatorname{Field}\left(F\right)] [\operatorname{Fintype}\left(F\right)] [\operatorname{DecidableEq}\left(F\right)] \forall psi:\operatorname{AddChar}\left(F, Complex\right), \forall a:F, \forall b:F, \operatorname{ringChar}\left(F\right)\neq 2 \land psi\neq 1 \implies \Vert \operatorname{S}\left(F, psi, a, b\right)\Vert \leq 2\cdot \sqrt{\operatorname{card}\left(F\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/SalieSum.salieSum_norm_le` (`✓ std3`). ∎

*Citation.* Emmanuel Kowalski (2021). *Exponential sums over finite fields: elementary methods*. URL: <https://people.math.ethz.ch/~kowalski/exponential-sums-elementary.pdf>.

*Commentary.*

For all a,b in every odd finite field and every nontrivial complex additive character, the complex norm of S is at most two times the real square root of the field cardinality. The Gauss-square identity and the unit norm of chi(-1) give norm G equal to square root q. Additive-character values have norm one, and the root-count formula bounds the quadratic root fiber by two. The triangle inequality then gives norm R at most two.

The proof uses the boundary theorem when b=0, exact nonsquare cancellation when ab is a nonsquare, and the exact evaluation plus the root-phase estimate in the remaining branch. This is a bind-only consequence of the cited identities and triangle inequality. The cardinality and boundary helpers have genuine consumers, but this final bound has no downstream mathematical consumer in this module. Compilation does not establish its admission under the repository rule or complete the broader research objective.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/SalieSum.quadraticCharacterComplex`
- Truth anchor: `D5/S3/Arith/CharacterSums/SalieSum.quadraticCharacterComplex_apply`
- Truth anchor: `D5/S3/Arith/CharacterSums/SalieSum.quadraticGaussSum`
- Truth anchor: `D5/S3/Arith/CharacterSums/SalieSum.quadraticPhase_sum_eq`
- Truth anchor: `D5/S3/Arith/CharacterSums/SalieSum.quadraticRootFiber_card`
- Truth anchor: `D5/S3/Arith/CharacterSums/SalieSum.quadraticRootPhase`
- Truth anchor: `D5/S3/Arith/CharacterSums/SalieSum.quadraticRootPhase_eq_zero_of_not_isSquare`
- Truth anchor: `D5/S3/Arith/CharacterSums/SalieSum.salieSum`
- Truth anchor: `D5/S3/Arith/CharacterSums/SalieSum.salieSum_eq`
- Truth anchor: `D5/S3/Arith/CharacterSums/SalieSum.salieSum_eq_zero_of_not_isSquare`
- Truth anchor: `D5/S3/Arith/CharacterSums/SalieSum.salieSum_norm_le`
- Truth anchor: `D5/S3/Arith/CharacterSums/SalieSum.salieSum_zero_right`
