# Compact Shared Energy Action

## Abstract

Actual compact energy-group Haar averages retain precisely the complete total-energy blocks.

**Definition 1.1 (The actual diagonal circle representation).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.energyRepresentation`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.energyRepresentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A circle phase z acts by the diagonal unitary with entries one, z and z to the power m. The integer energy labels give a continuous group homomorphism into the actual three-dimensional unitary matrices.

**Definition 1.2 (The actual compact matrix subgroup).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.energyGroup`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.energyGroup` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The energy group is the range subgroup of that continuous unitary representation. It is compact as the continuous image of the circle.

**Definition 1.3 (Normalized Haar probability).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.energyHaar`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.energyHaar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Haar measure on this actual compact matrix subgroup is normalized to total mass one.

**Definition 1.4 (Native matrix tensor powers).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.matrixCopies`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.matrixCopies` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Matrix tensor powers use the same recursive basis as native density-state copies. The empty tensor power is the scalar identity.

**Theorem 1.5 (Time evolution and its actual compact closure).**

$$\forall m\in\operatorname{Nat}(),\\\operatorname{range}((\lambda U:\operatorname{energyGroup}(m),\operatorname{matrix}(U)))=\operatorname{closure}(\operatorname{range}((\lambda t:\operatorname{Real}(),\operatorname{exp}((-\operatorname{imaginaryUnit}()\cdot t)\cdot \operatorname{totalHamiltonian}(m,1))))) \land\\\forall n\in\operatorname{Nat}(),\forall t\in\operatorname{Real}(),\operatorname{matrixCopies}(\operatorname{exp}((-\operatorname{imaginaryUnit}()\cdot t)\cdot \operatorname{totalHamiltonian}(m,1)),n)=\operatorname{exp}((-\operatorname{imaginaryUnit}()\cdot t)\cdot \operatorname{totalHamiltonian}(m,n))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.energy_group_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrices of the compact subgroup are precisely the closure of the time exponentials of the fixed Hamiltonian. Here the integer spectrum makes every circle phase an actual time value. Tensoring a time exponential gives the exponential of the sum Hamiltonian on the native tensor space, for every copy count.

**Definition 1.6 (Actual shared Haar tensor moments).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.sharedMoment`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.sharedMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each matrix coordinate is the Haar integral of the native tensor power of one conjugated density matrix. Every tensor factor uses the same matrix-group element. Finite-dimensional integration can be taken in these coordinates.

**Theorem 1.7 (Actual Haar averaging equals complete total-energy pinching).**

$$\forall m,n\in\operatorname{Nat}(),\forall r\in\operatorname{DensityState}(\operatorname{Fin}(3)),\operatorname{sharedMoment}(m,n,r)=\operatorname{pinchedCopies}(m,n,r)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.shared_haar_pinching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual compact-group Haar average equals complete total-energy pinching on every native density state. A tensor entry acquires the circle character of its total-energy difference. Equal energies give the constant character; for unequal energies a group translation negates the integrand, forcing its integral to vanish. All complex cross entries inside degenerate total-energy blocks remain.

**Theorem 1.8 (A moment determines all lower zero-weight monomials).**

$$\forall m,N\in\operatorname{Nat}(),\forall r,s\in\operatorname{DensityState}(\operatorname{Fin}(3)),\operatorname{sharedMoment}(m,N,r)=\operatorname{sharedMoment}(m,N,s) \implies\\\forall a\in\operatorname{Exponent}(),\operatorname{degree}(a)\leq N \implies \operatorname{weight}(m,a)=0 \implies \operatorname{monomial}(\operatorname{stateMatrix}(r),a)=\operatorname{monomial}(\operatorname{stateMatrix}(s),a)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.moment_determines_monomials` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of one actual shared Haar moment implies equality of every labelled zero-weight coordinate monomial of no greater degree. Taking a native partial trace removes one copy: the equal head labels cancel in the energy condition, and their diagonal sum is one. Repeating this step and using the exponent-to-word construction gives the conclusion without dividing by any entry, including at degree zero and at deficient rank.

**Definition 1.9 (Actual compact energy orbits).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.SameEnergyOrbit`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.SameEnergyOrbit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two native states have the same energy orbit when an actual matrix in the compact subgroup conjugates the first state matrix to the second.

**Theorem 1.10 (Sparse compact-orbit separation by actual Haar moments).**

$$\forall m\in\operatorname{Nat}(),2\leq m \implies \neg \operatorname{SameEnergyOrbit}(m,\operatorname{rho}(),\operatorname{sigma}(m)) \land\\(\forall n\in\operatorname{Nat}(),n<2\cdot m-1 \implies \operatorname{sharedMoment}(m,n,\operatorname{rho}())=\operatorname{sharedMoment}(m,n,\operatorname{sigma}(m))) \land\\\operatorname{sharedMoment}(m,\operatorname{copyOrder}(m),\operatorname{rho}())\neq \operatorname{sharedMoment}(m,\operatorname{copyOrder}(m),\operatorname{sigma}(m))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.sparse_compact_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least two the literal sparse positive states belong to distinct actual compact orbits. Their shared Haar moments agree at every smaller copy count and differ at the stated count. Orbit conjugation preserves each complete total-energy pinching, so the explicit high-order tensor entry excludes orbit equivalence.

**Theorem 1.11 (The exact least positive uniform copy order).**

$$\forall m\in\operatorname{Nat}(),2\leq m \implies \operatorname{IsLeast}(\{N:\operatorname{Nat}() \mid 0<N \land \forall r,s\in\operatorname{DensityState}(\operatorname{Fin}(3)),(\operatorname{sharedMoment}(m,N,r)=\operatorname{sharedMoment}(m,N,s) \iff \operatorname{SameEnergyOrbit}(m,r,s))\},2\cdot m-1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.least_uniform_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least two, twice m minus one is the least positive order at which equality of actual shared Haar moments is equivalent to membership in the same actual compact energy orbit, uniformly over every native three-dimensional density state. Every zero-weight exponent decomposes by strictly decreasing degree into labelled indecomposable exponents. Their degree bound and monomial multiplication extend one moment's equality to all zero-weight monomials. Hermitian coordinate pairs give equal moduli and identical zero supports. If the weight-one coordinate is nonzero, its phase ratio determines the common circle phase. If it vanishes, the remaining two nonzero coordinates have consecutive weights, so their zero-weight relation gives a common phase by a ratio. A single nonzero coordinate admits a circle root, and the empty support is immediate. These cases give an actual conjugating matrix, including deficient rank and m equal to two. Orbit conjugation gives the reverse implication at every order. The literal positive sparse pair excludes every smaller positive order.

The explicit sparse effect gives no Helstrom optimum, adaptive protocol bound or postselection advantage.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.SameEnergyOrbit`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.energyGroup`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.energyHaar`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.energyRepresentation`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.energy_group_realization`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.least_uniform_order`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.matrixCopies`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.moment_determines_monomials`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.sharedMoment`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.shared_haar_pinching`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCompactAction.sparse_compact_separation`
- Dependency: [D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold](SharedEnergyCopyThreshold.md)
- Dependency: [D5/S3/Quantum/Fibers/SharedEnergyGapBound](SharedEnergyGapBound.md)
