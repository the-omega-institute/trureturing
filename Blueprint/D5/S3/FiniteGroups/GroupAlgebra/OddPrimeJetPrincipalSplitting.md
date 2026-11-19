# Principal-unit and scalar-label splitting

## Abstract

The actual principal-unit complement of the odd-prime jet group.

Let p be any odd prime, including 3, let F=ZMod p, and let K be a finite field in an arbitrary universe with |K|=p^n for n at least one. For every F-linear q with q(1)=0, the original group is the native subgroup of pairs of invertible F-linear operators on Polynomial.degreeLT K p and original additive-label automorphisms. The commutant kernel and its leading-unit principal subgroup are the native carriers from the preceding jet modules.

**Definition 1.1 (The actual label action on scalar units).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.fieldAction`

*Formalization.* `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.fieldAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the coefficient presentation q=Q(n,A), the label stabilizer acts on K through the field automorphism supplied by its native coefficient formula. This action is multiplicative on labels and induces the corresponding native action on K units. The construction uses the actual label group and does not choose a lift of a larger automorphism group.

**Theorem 1.2 (The coherent section is semilinear).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.coherentLift_semilinear`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.coherentLift_semilinear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed canonical shear preserves every constant polynomial, while the degree lift acts semilinearly by the native field automorphism. Therefore the coherent actual label section is semilinear on the chosen K-vector-space structure. This statement concerns the constructed section only; arbitrary elements of the full original group and arbitrary End_F(K) top maps remain unrestricted.

**Theorem 1.3 (Scalar covariance under coherent labels).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.scalar_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.scalar_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The genuine scalar operators M_a lie in the actual commutant because the original representation is K-linear before restriction to F. Conjugation by the coherent section sends M_a to M_sigma(g)(a). No centrality of scalar operators in the full commutant is used.

**Definition 1.4 (The scalar-label quotient homomorphism).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.quotientHom`

*Formalization.* `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.quotientHom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The native full-group semidirect equivalence is followed by the equivariant leading-unit map on its actual commutant kernel and the identity on the actual label group. The resulting homomorphism has target K* semidirect the actual label group with the scalar action above.

**Definition 1.5 (The scalar-times-label complement).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.complementHom`

*Formalization.* `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.complementHom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Native semidirect-product lifting combines the scalar-unit section with the coherent label section. Scalar covariance is exactly the conjugation condition required by the native lift, so the complement map is a genuine homomorphism.

**Theorem 1.6 (The complement is a right inverse).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.quotient_complement`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.quotient_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every scalar-label coordinate is sent back to an actual scalar-times-coherent-label pair, and the quotient recovers that coordinate exactly. The leading-unit retraction is the only coordinate calculation required.

**Theorem 1.7 (The quotient kernel is exactly the actual principal subgroup).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.quotient_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.quotient_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The kernel condition forces both the actual label coordinate and the leading unit to be trivial. The native principal-unit criterion then identifies the kernel with actualPrincipalUnits mapped through the native label-kernel inclusion. Conversely every such principal unit maps to the identity.

**Definition 1.8 (The native split group extension).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.principalExtension`

*Formalization.* `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.principalExtension` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The extension uses actualPrincipalUnits as its kernel, originalGroup as its middle group, and K* semidirect the actual label group as quotient. Its inclusion, kernel equality, and surjectivity are the native maps and the explicit complement right inverse.

**Theorem 1.9 (Unique principal-times-scalar-times-label factorization).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.unique_principal_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.unique_principal_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native GroupExtension.Splitting equivalence gives every actual group element a unique product of an actual principal unit and one scalar-label complement element. This is a factorization in the original group itself and does not replace the actual carriers by a toy semidirect product.

**Theorem 1.10 (Splitting for every normalized parameter).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.normalized_principal_splitting`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.normalized_principal_splitting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native coefficient bijection transports the construction from Q(n,A) to every normalized F-linear q with q(1)=0. The result retains arbitrary finite-field universes, all odd primes including 3, unrestricted End_F(K) top coordinates, and the native actual principal-unit, original-group, and label-group carriers. No cyclicity, logarithm, trace, kernel-order invertibility, scalar centrality, or split scalar/Galois-image hypothesis is introduced.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.coherentLift_semilinear`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.complementHom`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.fieldAction`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.normalized_principal_splitting`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.principalExtension`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.quotientHom`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.quotient_complement`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.quotient_kernel`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.scalar_covariance`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.unique_principal_factorization`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadicalGroup](OddPrimeJetRadicalGroup.md)
