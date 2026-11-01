# Charged commutants with arbitrary matter

## Abstract

A nonzero ghost charge degree annihilates any endomorphism commuting with all tensor ghost modes.

M is an arbitrary complex module. Tensor products and endomorphisms are algebraic; no topology, finite dimension, positivity or irreducibility is assumed. The maps b, c and ghostNumber are the actual maps of BcGhostFock and BcGhostCharge. Bracketed group and module assumptions are anonymous instance arguments.

**Definition 1.1 (liftGhost).**

$$\forall M \in Type,\; [\operatorname{AddCommGroup}\left(M\right)] [\operatorname{Module}\left(Complex, M\right)] \forall T \in \operatorname{Module}.\operatorname{End}\left(Complex, Fock\right),\; \operatorname{liftGhost}\left(T\right) = \operatorname{TensorProduct}.\operatorname{map}\left(\operatorname{LinearMap}.\operatorname{id}\left(M\right), T\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostChargeTensor.liftGhost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matter factor is acted on by its identity map.

**Definition 1.2 (number).**

$$\forall M \in Type,\; [\operatorname{AddCommGroup}\left(M\right)] [\operatorname{Module}\left(Complex, M\right)] number = \operatorname{liftGhost}\left(ghostNumber\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostChargeTensor.number` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The tensor ghost-number operator.

**Definition 1.3 (B).**

$$\forall M \in Type,\; [\operatorname{AddCommGroup}\left(M\right)] [\operatorname{Module}\left(Complex, M\right)] \forall m \in Int,\; \operatorname{B}\left(m\right) = \operatorname{liftGhost}\left(\operatorname{b}\left(m\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostChargeTensor.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every integer b mode acts on the ghost factor.

**Definition 1.4 (C).**

$$\forall M \in Type,\; [\operatorname{AddCommGroup}\left(M\right)] [\operatorname{Module}\left(Complex, M\right)] \forall m \in Int,\; \operatorname{C}\left(m\right) = \operatorname{liftGhost}\left(\operatorname{c}\left(m\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostChargeTensor.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every integer c mode acts on the ghost factor.

**Definition 1.5 (partialNumber).**

$$\forall M \in Type,\; [\operatorname{AddCommGroup}\left(M\right)] [\operatorname{Module}\left(Complex, M\right)] \forall K \in \operatorname{Finset}\left(Int\right),\; \operatorname{partialNumber}\left(K\right) = \operatorname{Finset}.\operatorname{sum}\left(K, \lambda(n:Int)\mapsto(\operatorname{liftGhost}\left(\operatorname{normalTerm}\left(n\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostChargeTensor.partialNumber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite sum of the actual lifted normal bilinears.

**Theorem 1.6 (tensor finite capture).**

$$\forall M \in Type,\; [\operatorname{AddCommGroup}\left(M\right)] [\operatorname{Module}\left(Complex, M\right)] \forall x \in \operatorname{TensorProduct}\left(Complex, M, Fock\right),\; \exists K \in \operatorname{Finset}\left(Int\right),\; \forall L \in \operatorname{Finset}\left(Int\right),\; \operatorname{Finset}.\operatorname{Subset}\left(K, L\right) \Rightarrow \operatorname{partialNumber}\left(L, x\right) = \operatorname{number}\left(x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostChargeTensor.tensor_finite_capture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each pure tensor inherits a finite capture from its ghost vector. Tensor-product induction combines captures by finite union, so every larger finite set still computes number on the original tensor.

**Theorem 1.7 (number commutes of signed modes).**

$$\forall M \in Type,\; [\operatorname{AddCommGroup}\left(M\right)] [\operatorname{Module}\left(Complex, M\right)] \forall E \in \operatorname{Module}.\operatorname{End}\left(Complex, \operatorname{TensorProduct}\left(Complex, M, Fock\right)\right),\; \forall epsilon \in Complex,\; epsilon \cdot epsilon = 1 \Rightarrow \left(\left(\forall m \in Int,\; E \cdot \operatorname{B}\left(m\right) = \operatorname{smul}\left(epsilon, \operatorname{B}\left(m\right) \cdot E\right)\right) \Rightarrow \left(\left(\forall m \in Int,\; E \cdot \operatorname{C}\left(m\right) = \operatorname{smul}\left(epsilon, \operatorname{C}\left(m\right) \cdot E\right)\right) \Rightarrow number \cdot E - E \cdot number = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostChargeTensor.number_commutes_of_signed_modes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For epsilon squared equal to one, the two signs cancel in each normal bilinear. At a fixed x choose one finite union capturing x and E x. Commutation with that finite sum identifies number applied to E x with E applied to number x. Epsilon one gives commutation, and epsilon minus one covers anticommutation with both odd families.

**Theorem 1.8 (charged commutant vanishes).**

$$\forall M \in Type,\; [\operatorname{AddCommGroup}\left(M\right)] [\operatorname{Module}\left(Complex, M\right)] \forall E \in \operatorname{Module}.\operatorname{End}\left(Complex, \operatorname{TensorProduct}\left(Complex, M, Fock\right)\right),\; \left(\forall m \in Int,\; E \cdot \operatorname{B}\left(m\right) = \operatorname{B}\left(m\right) \cdot E\right) \Rightarrow \left(\left(\forall m \in Int,\; E \cdot \operatorname{C}\left(m\right) = \operatorname{C}\left(m\right) \cdot E\right) \Rightarrow \left(\forall d \in Complex,\; d \ne 0 \Rightarrow \left(number \cdot E - E \cdot number = \operatorname{smul}\left(d, E\right) \Rightarrow E = 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostChargeTensor.charged_commutant_vanishes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite normal capture first proves that the charge commutator is zero. The stipulated degree d is nonzero, so d times E equal to zero forces E itself to be zero. This uses no scalar-commutant assertion on the tensor product.

The theorem can eliminate a later BRST residual only after that residual is constructed on this tensor carrier and its mode commutation and nonzero degree are proved. It does not construct a total BRST operator, prove nilpotence, or complete the string objective.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostChargeTensor.B`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostChargeTensor.C`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostChargeTensor.charged_commutant_vanishes`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostChargeTensor.liftGhost`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostChargeTensor.number`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostChargeTensor.number_commutes_of_signed_modes`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostChargeTensor.partialNumber`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostChargeTensor.tensor_finite_capture`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostCharge](BcGhostCharge.md)
