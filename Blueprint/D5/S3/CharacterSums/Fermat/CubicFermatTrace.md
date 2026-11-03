# Cubic Fermat Counts and Eisenstein Traces

## Abstract

The actual cubic Fermat projective point count is the residue cardinality plus one minus the trace of a primary Eisenstein generator.

Let E = Z[omega] with omega^2 + omega + 1 = 0. The concrete embedding into C sends omega to (-1 + i sqrt(3))/2. It is injective, and twice the real part of the image of an Eisenstein integer is its integral quadratic-algebra trace. For a finite field F, write q = card F. Point counts below are cardinalities of the actual projective subtype defined in CharacterPointCount.

**Theorem 1.1 (The cubic count is a conjugate pair of Jacobi sums).**

$$\forall F, \operatorname{finiteField}\left(F\right), chi: \operatorname{MulChar}\left(F, C\right), \operatorname{orderOf}\left(chi\right)=3 \implies \operatorname{card}\left(\operatorname{projectivePoints}\left(F, 3\right)\right)=\operatorname{card}\left(F\right)+1+2\operatorname{Re}\left(\operatorname{J}\left(chi, chi\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/Fermat/CubicFermatTrace.cubic_projective_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Specialize the projective character-sum formula to degree three. Exact character order gives chi^2 = chi^{-1}, so only J(chi,chi) and J(chi^{-1},chi^{-1}) remain. Complex conjugation identifies these two Jacobi sums. Taking real parts gives q + 1 + 2 Re J.

**Theorem 1.2 (An Eisenstein-valued character gives an integral trace formula).**

$$\forall F, \operatorname{finiteField}\left(F\right), chi: \operatorname{MulChar}\left(F, E\right), \operatorname{orderOf}\left(chi\right)=3 \implies \operatorname{card}\left(\operatorname{projectivePoints}\left(F, 3\right)\right)=\operatorname{card}\left(F\right)+1+\operatorname{Tr}\left(\operatorname{J}\left(chi, chi\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/Fermat/CubicFermatTrace.cubic_projective_count_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transport the same character through the concrete injective embedding. Its order remains three, and ring-homomorphism compatibility transports the Jacobi sum. Replace twice its real part by the integral trace and descend the resulting equality to Z.

**Theorem 1.3 (The primary generator determines the exact projective count).**

$$\forall P: \operatorname{Ideal}\left(E\right), \operatorname{maximal}\left(P\right), \operatorname{finite}\left(\operatorname{quotient}\left(E, P\right)\right), \operatorname{mod}\left(\operatorname{card}\left(\operatorname{quotient}\left(E, P\right)\right), 3\right)=1, pi: E, \operatorname{spanSingleton}\left(pi\right)=P, \operatorname{divides}\left(3, pi-1\right) \implies \operatorname{card}\left(\operatorname{projectivePoints}\left(\operatorname{quotient}\left(E, P\right), 3\right)\right)=\operatorname{card}\left(\operatorname{quotient}\left(E, P\right)\right)+1-\operatorname{Tr}\left(pi\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/Fermat/CubicFermatTrace.cubic_projective_count_primary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cardinality congruence excludes characteristic three: if 3 belonged to P, the finite residue field would have characteristic three and cardinality divisible by three. Use the actual zero-extended Euler character attached to P. The preceding Jacobi normalization proves -J = pi for this same character and ideal. Applying the integral trace yields card(projectivePoints(E/P,3)) = card(E/P) + 1 - Tr(pi). Neither a Jacobi value nor a norm identity is assumed by the point-count theorem.

These are classical character-sum point-count identities, with no mathematical novelty claim. The formal bridge joins the actual projective point set, the fixed Euler character, the concrete complex embedding and the primary generator. It applies to all finite residue fields satisfying the stated assumptions, including prime-power cardinalities.

## References

- Truth anchor: `D5/S3/CharacterSums/Fermat/CubicFermatTrace.cubic_projective_count`
- Truth anchor: `D5/S3/CharacterSums/Fermat/CubicFermatTrace.cubic_projective_count_integral`
- Truth anchor: `D5/S3/CharacterSums/Fermat/CubicFermatTrace.cubic_projective_count_primary`
- Dependency: [D5/S3/CharacterSums/Fermat/CharacterPointCount](CharacterPointCount.md)
- Dependency: [D5/S3/Factorization/QuadraticIdeals/CubicJacobiNormalization](../../Factorization/QuadraticIdeals/CubicJacobiNormalization.md)
- Dependency: [D5/S3/Factorization/QuadraticIdeals/EisensteinOddQuotient](../../Factorization/QuadraticIdeals/EisensteinOddQuotient.md)
