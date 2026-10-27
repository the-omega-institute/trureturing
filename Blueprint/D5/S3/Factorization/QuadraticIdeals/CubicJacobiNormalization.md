# Cubic Jacobi Sums and Primary Generators

## Abstract

The Euler cubic residue character determines the sign and the chosen ideal of its Eisenstein-valued Jacobi sum.

Write E = Z[omega], where omega is the standard primitive cube root of unity in the Eisenstein order. Let P be a maximal ideal with finite residue field, put q = card(E/P), assume q is congruent to 1 modulo 3, and assume 3 is not in P. The character chi_P is the genuine multiplicative character extended by zero at zero, whose value at a nonzero residue class is the unique element of {1, omega, omega^2} reducing to x^((q-1)/3). Throughout, J_P denotes the Eisenstein-valued Jacobi sum J(chi_P,chi_P).

**Theorem 1.1 (The Euler character has exact order three).**

$$\forall P: \operatorname{Ideal}\left(E\right), \operatorname{maximal}\left(P\right), \operatorname{finite}\left(\operatorname{quotient}\left(E, P\right)\right), \operatorname{mod}\left(\operatorname{card}\left(\operatorname{quotient}\left(E, P\right)\right), 3\right)=1, \operatorname{notMem}\left(3, P\right) \implies \operatorname{orderOf}\left(\operatorname{chi}\left(P\right)\right)=3$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/CubicJacobiNormalization.cubicResidueMulChar_orderOf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing local Euler selector is multiplicative on nonzero residue classes. Extending it by zero therefore gives a MulChar. Its cube is the trivial zero-extended character. If it were itself trivial, every nonzero residue would satisfy x^((q-1)/3) = 1, contradicting the finite-field exponent criterion. The accompanying reduction theorem also covers zero.

**Theorem 1.2 (Euler reduction selects the same prime ideal).**

$$\forall P: \operatorname{Ideal}\left(E\right), \operatorname{maximal}\left(P\right), \operatorname{finite}\left(\operatorname{quotient}\left(E, P\right)\right), \operatorname{mod}\left(\operatorname{card}\left(\operatorname{quotient}\left(E, P\right)\right), 3\right)=1, \operatorname{notMem}\left(3, P\right) \implies \operatorname{mem}\left(\operatorname{J}\left(P\right), P\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/CubicJacobiNormalization.cubicJacobiSum_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reduce the Jacobi sum modulo P and expand (1-x)^m with m = (q-1)/3. Every resulting power has exponent between m and 2m, strictly between zero and q-1. The finite-field power sums vanish. Thus J_P lies in this specified P; no choice between conjugate prime ideals is assumed.

**Theorem 1.3 (The algebraic norm equals the residue cardinality).**

$$\forall P: \operatorname{Ideal}\left(E\right), \operatorname{maximal}\left(P\right), \operatorname{finite}\left(\operatorname{quotient}\left(E, P\right)\right), \operatorname{mod}\left(\operatorname{card}\left(\operatorname{quotient}\left(E, P\right)\right), 3\right)=1, \operatorname{notMem}\left(3, P\right) \implies \operatorname{Norm}\left(\operatorname{J}\left(P\right)\right)=\operatorname{card}\left(\operatorname{quotient}\left(E, P\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/CubicJacobiNormalization.cubicJacobiSum_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugation in E sends the character to its inverse. Embed E into its fraction field to apply the Jacobi product identity; the character and its square are nontrivial by exact order three. Injectivity transports the identity back to E, and the quadratic-algebra norm is J_P times its conjugate.

**Theorem 1.4 (The negative Jacobi sum is primary).**

$$\forall P: \operatorname{Ideal}\left(E\right), \operatorname{maximal}\left(P\right), \operatorname{finite}\left(\operatorname{quotient}\left(E, P\right)\right), \operatorname{mod}\left(\operatorname{card}\left(\operatorname{quotient}\left(E, P\right)\right), 3\right)=1, \operatorname{notMem}\left(3, P\right) \implies \operatorname{divides}\left(3, -\operatorname{J}\left(P\right)-1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/CubicJacobiNormalization.cubicJacobiSum_primary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The classical Jacobi congruence gives J_P = -1 + z(omega-1)^2. The identity (omega-1)^2 = -3 omega then proves that -J_P is congruent to 1 modulo 3. This fixes the primary sign rather than inserting a sign convention into the final theorem.

**Theorem 1.5 (The negative Jacobi sum generates the chosen ideal).**

$$\forall P: \operatorname{Ideal}\left(E\right), \operatorname{maximal}\left(P\right), \operatorname{finite}\left(\operatorname{quotient}\left(E, P\right)\right), \operatorname{mod}\left(\operatorname{card}\left(\operatorname{quotient}\left(E, P\right)\right), 3\right)=1, \operatorname{notMem}\left(3, P\right) \implies \operatorname{spanSingleton}\left(-\operatorname{J}\left(P\right)\right)=P$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/CubicJacobiNormalization.cubicJacobiSum_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership gives the inclusion (-J_P) contained in P. The established integral cyclotomic bridge supplies the principal-ideal structure needed by the absolute-ideal-norm API. The norm computation gives both additive subgroups the same positive finite index. Strict antitonicity of index rules out a proper inclusion, proving equality of ideals.

**Theorem 1.6 (The primary generator is exactly the negative Jacobi sum).**

$$\forall P: \operatorname{Ideal}\left(E\right), \operatorname{maximal}\left(P\right), \operatorname{finite}\left(\operatorname{quotient}\left(E, P\right)\right), \operatorname{mod}\left(\operatorname{card}\left(\operatorname{quotient}\left(E, P\right)\right), 3\right)=1, \operatorname{notMem}\left(3, P\right) \implies \forall pi: E, \operatorname{spanSingleton}\left(pi\right)=P, \operatorname{divides}\left(3, pi-1\right) \implies -\operatorname{J}\left(P\right)=pi$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/CubicJacobiNormalization.cubicJacobiSum_eq_primary_generator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal principal ideals make pi and -J_P associates. Reducing the associatedness equation modulo 3 shows that the intervening unit is congruent to 1. The Eisenstein unit norm and integer coordinate bounds force such a unit to be 1. The theorem assumes only that pi generates P and is primary; neither the Jacobi norm nor the selected ideal direction is an extra hypothesis.

These are classical cubic character-sum identities, with no mathematical novelty claim. The repository contribution is the complete formal bridge from the existing local Euler selector to exact Jacobi normalization over any finite residue field satisfying the stated assumptions. This is the J = -pi step used in section 58 of the cubic prime-period theory; by itself it does not prove that section's full cubic reciprocity theorem. The classical convention is also recorded in Dunn and Radziwill, arXiv:2109.07463v3, equations (1.4)-(1.5).

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/CubicJacobiNormalization.cubicJacobiSum_eq_primary_generator`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/CubicJacobiNormalization.cubicJacobiSum_mem`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/CubicJacobiNormalization.cubicJacobiSum_norm`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/CubicJacobiNormalization.cubicJacobiSum_primary`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/CubicJacobiNormalization.cubicJacobiSum_span`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/CubicJacobiNormalization.cubicResidueMulChar_orderOf`
- Dependency: [D5/S3/Factorization/QuadraticIdeals/CubicIdealCharacter](CubicIdealCharacter.md)
- Dependency: [D5/S3/Factorization/QuadraticIdeals/EisensteinCyclotomicBridge](EisensteinCyclotomicBridge.md)
