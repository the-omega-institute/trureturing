# Colored Oscillator Partition Character

## Abstract

Every finite-color oscillator energy fiber is counted by an independent partition generating coefficient.

For a finite color type C, an occupation is a finitely supported function on C times the natural frequencies. Its energy is the sum of (frequency plus one) times occupancy. colorSplit is actual Finsupp currying followed by the finite-domain function equivalence. energy_colorSplit proves exact additivity of the total energy over colors, with the finite outer sum and each finitely supported inner sum justified by the existing sum-curry and sum-fintype laws.

**Theorem 1.1 (Exact Finite Partition Convolution).**

Lean statement: `D5/S3/VertexAlgebra/ColoredFockCharacter.energyFiber_card`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ColoredFockCharacter.energyFiber_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N and finite color type C, the cardinal of the actual energy-N occupation fiber equals coefficient N of (Nat.Partition.genFun with constant weight one) raised to card C. fiberPartitionTuple is an equivalence with the sigma family of energy compositions and tuples of partitions, with both inverse laws. Its dependent right inverse uses Function.hfunext and equality transport between energy fibers with equal underlying occupations; it does not eliminate an equality of dependent function types. Each color uses the existing PolynomialFockCharacter.energyFiberEquivPartition, not a new monochromatic partition proof. EnergyComposition is the finite univ.finsuppAntidiag N; its support and sum conditions are exact. Nat.card_sigma and Nat.card_pi count its partition tuples, and PowerSeries.coeff_prod identifies precisely the same finite convolution. The partition generating function is independent of the oscillator index cardinal.

**Theorem 1.2 (All Finite Color Counts).**

Lean statement: `D5/S3/VertexAlgebra/ColoredFockCharacter.character`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ColoredFockCharacter.character` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural c, the formal series whose N-th coefficient counts the full untruncated occupation fiber on Fin c equals genFun(one) to the c-th power. This includes c equal to zero and all N. No state cutoff or numerical level enumeration occurs.

**Theorem 1.3 (Euler Product With Finite Color Power).**

Lean statement: `D5/S3/VertexAlgebra/ColoredFockCharacter.character_euler`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ColoredFockCharacter.character_euler` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After mapping the natural coefficients to complex numbers, the character equals the c-th power of the formal Euler product over positive frequencies. This uses the existing actual monocolor lZero_character_euler_product and its actual lZero_spectrum. The finite color power remains outside the already justified infinite product: no new infinite-product interchange, analytic convergence assumption or factor truncation is asserted.

These are classical oscillator and colored partition counting results, not an originality claim. They do not construct a Monster Lie bracket, a root denominator identity, orbifold fusion, symmetry anomalies, spacetime geometry, full string theory or AdS/CFT. Source-admission enrollment and remote delivery are separate from Lean proof verification.

## References

- Truth anchor: `D5/S3/VertexAlgebra/ColoredFockCharacter.character`
- Truth anchor: `D5/S3/VertexAlgebra/ColoredFockCharacter.character_euler`
- Truth anchor: `D5/S3/VertexAlgebra/ColoredFockCharacter.energyFiber_card`
- Dependency: [D5/S3/VertexAlgebra/PolynomialFockCharacter](PolynomialFockCharacter.md)
