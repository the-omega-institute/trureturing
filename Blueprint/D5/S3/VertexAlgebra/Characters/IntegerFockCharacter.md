# Integer Fock Character

## Abstract

The true integer-frequency polynomial Fock energy character and finite multiplicities.

For every natural colour count r, the carrier is the full complex polynomial algebra MvPolynomial (Fin r × Nat) Complex. A variable (j,n) has energy n+1. Each polynomial has finite support, but the algebra has every positive integer frequency. No frequency cutoff, supplied dimension, or partition-count premise occurs.

**Definition 1.1 (Full polynomial carrier).**

Lean statement: `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.Fock`

*Formalization.* `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.Fock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex polynomial algebra on Fin r × Nat, for every natural r, including zero.

**Definition 1.2 (Integer energy fibre).**

Lean statement: `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.EnergyFiber`

*Formalization.* `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.EnergyFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every r,N : Nat, the subtype of finitely supported exponents d : (Fin r × Nat) →₀ Nat satisfying integerEnergy (Fin r) d = N. The energy definition is the accepted AnalyticIntegerOccupation.integerEnergy, the sum of d(j,n)*(n+1). Its signed trace is not used.

**Definition 1.3 (Ordinary partition tuples).**

Lean statement: `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.PartitionTuple`

*Formalization.* `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.PartitionTuple` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every r,N : Nat, a dependent pair of an energy allocation e : Fin r → Nat with sum_j e(j)=N and an ordinary partition of e(j) for each colour j. These are ordinary positive-integer partitions, with the unique empty partition allowed.

**Definition 1.4 (Actual weighted polynomial grade).**

Lean statement: `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.grade`

*Formalization.* `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.grade` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every r,N : Nat, the native Mathlib weightedHomogeneousSubmodule Complex (fun (j,n) => n+1) N in Fock r. Its elements are exactly polynomials whose nonzero monomial coefficients have integer energy N. The carrier is defined by polynomial support and energy, not by a desired count.

**Theorem 1.5 (Exact energy-preserving partition decomposition).**

Lean statement: `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.energyFiberEquivPartitionTuple`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.energyFiberEquivPartitionTuple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r,N : Nat, an equivalence EnergyFiber r N ≃ PartitionTuple r N. The accepted colourEquiv curries exponents by colour; conservation of integer energy identifies the sum of the one-colour energies. The accepted PolynomialFockCharacter.energyFiberEquivPartition then converts each colour to ordinary partitions. The generic dependent fibre equivalences retain all energy allocations.

**Theorem 1.6 (Exact finite convolution).**

Lean statement: `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.card_energyFiber`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.card_energyFiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r,N : Nat, Nat.card (EnergyFiber r N) equals the sum over e in univ.finsuppAntidiag N of the product over j : Fin r of Nat.card (Nat.Partition (e j)). The accepted energyAllocationEquivAntidiag supplies only weight-independent indexing. Finiteness follows from this actual equivalence with finite ordinary partition tuples, without assuming a finite fibre.

**Definition 1.7 (Weighted monomial basis).**

Lean statement: `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.gradeBasis`

*Formalization.* `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.gradeBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every r,N : Nat, a complex basis of the actual grade r N indexed by EnergyFiber r N. Mathlib's basisRestrictSupport is transported along weightedHomogeneousSubmodule_eq_finsupp_supported; its basis vectors are the actual monomials with coefficient one. The finite energy index proves Module.Finite Complex (grade r N).

**Theorem 1.8 (Actual finite energy dimension).**

Lean statement: `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.finrank_grade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.finrank_grade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r,N : Nat, Module.finrank Complex (grade r N) = Nat.card (PartitionTuple r N). This dimension comes from gradeBasis and the exact fibre equivalence. It is not an assumed dimension or a fresh vector space indexed by the desired count.

**Definition 1.9 (Ordinary partition series).**

Lean statement: `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.ordinaryPartitionSeries`

*Formalization.* `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.ordinaryPartitionSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex formal power series whose coefficient at N is the complex cast of Nat.card (Nat.Partition N). The accepted one-colour Fock spectrum and character identify it with the product over n : Nat of (1-X^(n+1))^(-1).

**Definition 1.10 (Actual finrank formal character).**

Lean statement: `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.character`

*Formalization.* `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.character` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every r : Nat, PowerSeries.mk (fun N => (Module.finrank Complex (grade r N) : Complex)). There is no analytic convergence or vacuum-energy normalization in this definition.

**Theorem 1.11 (All-energy ordinary bosonic character).**

Lean statement: `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.character_eq_partition_power`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.character_eq_partition_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural r, character r = ordinaryPartitionSeries ^ r. The coefficient proof consumes the actual weighted-grade finrank theorem and the exact finite convolution. It includes r=0, when the character is one, and every N=0, when the dimension is one. For r=0 and positive N the dimension is zero.

**Theorem 1.12 (Integer Euler-product character).**

Lean statement: `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.character_euler_product`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.character_euler_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural r, character r equals (product over n : Nat of (1-X^(n+1))^(-1)) ^ r as a complex formal power series with the coefficient topology. The product is reused at its exact hypotheses from PolynomialFockCharacter.lZero_character_euler_product after the actual multicolour basis and dimension bridge.

ColouredOddOccupation supplies only curry and antidiagonal bookkeeping. Its concrete weight 2*n+1 and odd character are different, as is the signed integer trace. This result is an independent polynomial-coordinate prerequisite for a transverse Fock character. It asserts no equivalence with original BRST cohomology, no analytic eta identity, no no-ghost theorem, and no completion of the VOA, Monster, string, or AdS/CFT programme.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.EnergyFiber`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.Fock`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.PartitionTuple`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.card_energyFiber`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.character`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.character_eq_partition_power`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.character_euler_product`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.energyFiberEquivPartitionTuple`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.finrank_grade`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.grade`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.gradeBasis`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.ordinaryPartitionSeries`
- Dependency: [D5/S3/Combinatorics/Partitions/AnalyticIntegerOccupation](../../Combinatorics/Partitions/AnalyticIntegerOccupation.md)
- Dependency: [D5/S3/VertexAlgebra/PolynomialFockCharacter](../PolynomialFockCharacter.md)
