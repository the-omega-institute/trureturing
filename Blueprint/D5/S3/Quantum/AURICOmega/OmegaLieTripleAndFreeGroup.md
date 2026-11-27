# Lie triple curvature, dual charts, and reduced words

## Abstract

Lie triple curvature, rational dual charts, and the norm-five word theorem for Omega Math sections 4.2, 5.2, and 14.3–14.4.

**Theorem 1.1 (The triple bracket is antisymmetric).**

$$\forall u \in Vec3, v \in Vec3, w \in Vec3,\; \operatorname{lieTriple}\left(u, v, w\right) = \operatorname{neg}\left(\operatorname{lieTriple}\left(v, u, w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.lieTriple_antisymm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bracket is dot(u,w) times v minus dot(v,w) times u.

**Theorem 1.2 (The cyclic sum vanishes).**

$$\forall u \in Vec3, v \in Vec3, w \in Vec3,\; \operatorname{lieTriple}\left(u, v, w\right) + \operatorname{lieTriple}\left(v, w, u\right) + \operatorname{lieTriple}\left(w, u, v\right) = zero$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.lieTriple_jacobi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three terms cancel by symmetry of the dot product.

**Theorem 1.3 (A fixed pair acts by a derivation).**

$$\forall x \in Vec3, y \in Vec3, u \in Vec3, v \in Vec3, w \in Vec3,\; \operatorname{lieTriple}\left(x, y, \operatorname{lieTriple}\left(u, v, w\right)\right) = \operatorname{lieTriple}\left(\operatorname{lieTriple}\left(x, y, u\right), v, w\right) + \operatorname{lieTriple}\left(u, \operatorname{lieTriple}\left(x, y, v\right), w\right) + \operatorname{lieTriple}\left(u, v, \operatorname{lieTriple}\left(x, y, w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.lieTriple_derivation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The strict integer polynomial checker verifies the derivation identity in all three coordinates.

**Theorem 1.4 (The positive curvature numerator is the squared Gram area).**

$$\forall u \in Vec3, v \in Vec3,\; \operatorname{dot}\left(\operatorname{lieTriple}\left(u, v, u\right), v\right) = \operatorname{gramAreaSq}\left(u, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.lieTriple_unit_sectional_curvature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Gram area is dot(u,u) times dot(v,v) minus the square of dot(u,v).

**Theorem 1.5 (The reversed contraction is the negative squared Gram area).**

$$\forall u \in Vec3, v \in Vec3,\; \operatorname{dot}\left(\operatorname{lieTriple}\left(u, v, v\right), u\right) = \operatorname{neg}\left(\operatorname{gramAreaSq}\left(u, v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.lieTriple_sectional_curvature_reversed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This identifies the sign of the contraction in the bracket convention used here.

**Theorem 1.6 (Every nondegenerate rational plane has curvature one).**

$$\forall u \in RatVec3, v \in RatVec3,\; \operatorname{gramAreaSq}\left(\operatorname{num}\left(u\right), \operatorname{num}\left(v\right)\right) \ne 0 \Rightarrow \operatorname{Equivalent}\left(\operatorname{mul}\left(\operatorname{rationalCurvatureNumerator}\left(u, v\right), \operatorname{inv}\left(\operatorname{rationalGramAreaSq}\left(u, v\right)\right)\right), 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.lieTriple_sectional_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both contractions have the square of the product of the two positive vector denominators as their denominator.

**Theorem 1.7 (The two chart denominators sum to one).**

$$\forall a \in RatVec3, b \in RatVec3,\; \operatorname{Equivalent}\left(\operatorname{denomPlus}\left(a, b\right) + \operatorname{denomMinus}\left(a, b\right), 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.dual_chart_denom_sum_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a quaternion product with homogeneous scalar coordinate w and positive radius r, the two normalized denominators are (r+w)/(2r) and (r−w)/(2r).

**Theorem 1.8 (One chart denominator is at least one half).**

$$\forall a \in RatVec3, b \in RatVec3,\; \operatorname{value}\left(1, 2\right) \le \operatorname{denomPlus}\left(a, b\right) \lor \operatorname{value}\left(1, 2\right) \le \operatorname{denomMinus}\left(a, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.dual_chart_denom_ge_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sign of the scalar coordinate specifies which denominator reaches the bound.

**Theorem 1.9 (The selected chart stays in the closed unit ball).**

$$\forall a \in RatVec3, b \in RatVec3,\; \operatorname{dot}\left(\operatorname{output}\left(a, b\right), \operatorname{output}\left(a, b\right)\right) \le 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.dual_chart_ball_containment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose the antipodal representative with nonnegative scalar coordinate. Its stereographic output has positive denominator r+|w|.

**Theorem 1.10 (The chart denominators have the expanded MRP forms).**

$$\forall a \in RatVec3, b \in RatVec3,\; \operatorname{Equivalent}\left(\operatorname{denomPlus}\left(a, b\right), \operatorname{value}\left(\operatorname{mrpPlusNum}\left(a, b\right), \operatorname{radius}\left(\operatorname{product}\left(a, b\right)\right)\right)\right) \land \operatorname{Equivalent}\left(\operatorname{denomMinus}\left(a, b\right), \operatorname{value}\left(\operatorname{mrpMinusNum}\left(a, b\right), \operatorname{radius}\left(\operatorname{product}\left(a, b\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.dual_chart_mrp_denominators` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For squared input norms A, B and dot product C, the normalized numerators are 1+AB−2C and A+B+2C. Both share denominator (1+A)(1+B).

**Theorem 1.11 (A reduced word has nonzero split image).**

$$\forall w \in Word,\; \operatorname{IsReduced}\left(w\right) \Rightarrow \operatorname{isZero}\left(\operatorname{evalSplit5}\left(w\right)\right) = false$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.reduced_word_split5_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each edge between adjacent outer products contributes a nonzero scalar modulo five.

**Theorem 1.12 (The squared norm is five to the word length).**

$$\forall w \in Word,\; \operatorname{normSq}\left(\operatorname{evalQuat}\left(w\right)\right) = \operatorname{powFive}\left(\operatorname{length}\left(w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.reduced_word_normSq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Hamilton multiplication multiplies squared norms, and every generator has squared norm five.

**Theorem 1.13 (A reduced word is primitive at five).**

$$\forall w \in Word,\; \operatorname{IsReduced}\left(w\right) \Rightarrow \left(\neg \operatorname{AllDivisibleByFive}\left(\operatorname{evalQuat}\left(w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.reduced_word_not_div_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If five divided every quaternion coordinate, the split matrix modulo five would vanish.

**Theorem 1.14 (A nonempty reduced word evaluates to a nonscalar quaternion).**

$$\forall w \in Word,\; \left(w \ne nil \land \operatorname{IsReduced}\left(w\right)\right) \Rightarrow \left(\neg \operatorname{IsScalar}\left(\operatorname{evalQuat}\left(w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.reduced_word_non_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A scalar quaternion with squared norm a positive power of five has scalar coordinate divisible by five.

**Theorem 1.15 (Distinct reduced words give distinct rational adjoint rotations).**

$$\forall u \in Word, v \in Word,\; \left(\operatorname{IsReduced}\left(u\right) \land \operatorname{IsReduced}\left(v\right)\right) \Rightarrow \left(\left(\operatorname{Equiv}\left(\operatorname{Ad}\left(\operatorname{evalQuat}\left(u\right), \operatorname{ofInt}\left(axisX\right)\right), \operatorname{Ad}\left(\operatorname{evalQuat}\left(v\right), \operatorname{ofInt}\left(axisX\right)\right)\right) \land \operatorname{Equiv}\left(\operatorname{Ad}\left(\operatorname{evalQuat}\left(u\right), \operatorname{ofInt}\left(axisY\right)\right), \operatorname{Ad}\left(\operatorname{evalQuat}\left(v\right), \operatorname{ofInt}\left(axisY\right)\right)\right)\right) \Rightarrow u = v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.reduced_words_adjoint_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of the actions makes the relative quaternion scalar. Remove the common prefix, then reverse the first suffix and replace each letter by its opposite before appending the second suffix. If the original words differed, the result is nonempty and reduced.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.dual_chart_ball_containment`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.dual_chart_denom_ge_half`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.dual_chart_denom_sum_one`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.dual_chart_mrp_denominators`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.lieTriple_antisymm`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.lieTriple_derivation`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.lieTriple_jacobi`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.lieTriple_sectional_curvature_reversed`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.lieTriple_sectional_ratio`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.lieTriple_unit_sectional_curvature`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.reduced_word_non_scalar`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.reduced_word_normSq`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.reduced_word_not_div_five`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.reduced_word_split5_nonzero`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup.reduced_words_adjoint_injective`
