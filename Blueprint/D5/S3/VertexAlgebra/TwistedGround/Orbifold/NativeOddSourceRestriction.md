# Charge-Zero Detection for Odd Mixed Fields

## Abstract

The charge-zero odd Heisenberg states determine lawful mixed fields on the Leech lattice.

**Definition 1.1 (Mixed coefficient families).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.MixedCoefficients`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.MixedCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For lattice data D with unit Gram determinant and twisted input parity s, a coefficient at integer label n is complex-linear in the odd untwisted state and the twisted input. The output has the opposite twisted parity, and n represents physical mode n+1/2.

**Definition 1.2 (The signed mixed Borcherds identity).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.mixedBorcherds`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.mixedBorcherds` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fix a fixed state a, an odd state b, a twisted input v and integers p, q, r. At offset i, the iterate evaluates the coefficient p+q-i on the odd product a_(r+i)b and v, weighted by binom(p,i). The first product applies the fixed action of a at mode p+r-i on the output parity to the coefficient q+i of b acting on v. The second product evaluates the coefficient q+r-i on b after the fixed mode p+i on the input parity, with the extra sign epsilon(r). Both products have weight (-1)^i binom(r,i). Each of the three families has finite support over i >= 0. The iterate sum equals the first product sum minus the second.

**Definition 1.3 (Lawful signed mixed fields).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.LawfulMixedField`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.LawfulMixedField` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each odd state b and twisted vector v, all sufficiently large labels have zero coefficient on b and v. The coefficient at n on the lattice translate of b is -(n+1/2) times the coefficient at n-1 on b. The signed mixed Borcherds identity holds for all fixed states, odd states, twisted inputs and integer indices.

**Definition 1.4 (The native lawful family).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.nativeMixedField`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.nativeMixedField` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual parity-changing modes give a lawful family by their truncation, translation and signed Borcherds identities.

**Definition 1.5 (The agreement space).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.mixedAgreement`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.mixedAgreement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Intersect, over all integer labels, the kernels of the differences of the two coefficient maps in the odd source variable.

**Theorem 1.6 (Agreement at every mode).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.mem_mixedAgreement`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.mem_mixedAgreement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An odd state belongs to the agreement space precisely when the two coefficient families give equal linear operators at every integer mode label on that state.

**Theorem 1.7 (Agreement under fixed-algebra modes).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.mixedAgreement_stable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.mixedAgreement_stable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two lawful families agree on an odd state, they agree on its image under every mode of every fixed state. The signed Borcherds identity at p = 0 expresses the iterate through coefficients on the original odd state.

**Definition 1.8 (The charge-zero odd space).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.chargeZeroOdd`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.chargeZeroOdd` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the odd states whose charge support is contained in the singleton zero.

**Definition 1.9 (Antisymmetrized charged states).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.oddChargedPolynomial`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.oddChargedPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Place the oscillator polynomial at charge c and subtract its lattice-involution image.

**Definition 1.10 (The fixed exponential sum).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.fixedChargedVacuum`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.fixedChargedVacuum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Add the vacuum exponentials at charges c and -c to obtain a fixed state.

**Definition 1.11 (The current of a lattice charge).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.chargeCurrent`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.chargeCurrent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the linear combination of the actual odd basis currents with coefficients given by the coordinates of the lattice charge.

**Theorem 1.12 (The odd charged vacuum from a neutral current).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.fixedChargedVacuum_zero_chargeCurrent`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.fixedChargedVacuum_zero_chargeCurrent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying mode zero of the fixed exponential sum at charges c and -c to the neutral current in direction c gives the odd charged vacuum multiplied by minus the squared charge norm.

**Theorem 1.13 (Pairs of current modes preserve the source subspace).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.current_pair_mem_map`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.current_pair_mem_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an odd subspace stable under all fixed-algebra modes, every pair of neutral current modes sends a vector of the subspace into its image in the ambient lattice carrier. The Borcherds identity recovers the product from fixed iterates by descending from the inner truncation bound.

**Theorem 1.14 (Generation from charge zero).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.oddSource_eq_top`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.oddSource_eq_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive definite Gram matrix, an odd subspace containing all charge-zero odd vectors and stable under all fixed-algebra modes is the whole odd carrier. Fixed exponential modes supply the odd charged vacua and pairs of current modes supply their polynomial descendants.

**Definition 1.15 (Restriction of the first input).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.restrictChargeZero`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.restrictChargeZero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At every mode label, restrict the first input to odd lattice states supported at charge zero.

**Theorem 1.16 (Faithfulness on both Leech twisted parities).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.leech_restrictChargeZero_injective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.leech_restrictChargeZero_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either twisted input parity of the Leech lattice, two arbitrary lawful mixed fields with equal charge-zero restrictions are equal. Their agreement space contains the charge-zero source, and stability under the actual fixed modes forces agreement on every odd state.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.LawfulMixedField`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.MixedCoefficients`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.chargeCurrent`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.chargeZeroOdd`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.current_pair_mem_map`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.fixedChargedVacuum`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.fixedChargedVacuum_zero_chargeCurrent`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.leech_restrictChargeZero_injective`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.mem_mixedAgreement`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.mixedAgreement`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.mixedAgreement_stable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.mixedBorcherds`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.nativeMixedField`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.oddChargedPolynomial`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.oddSource_eq_top`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.restrictChargeZero`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualMixedLocality](../../LatticeActualMixedLocality.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeAllStateJacobi](../../LatticeAllStateJacobi.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner](NativeOddTwistedIntertwiner.md)
