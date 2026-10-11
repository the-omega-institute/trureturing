# The physical Clifford ground sector

## Abstract

Paired Clifford bilinears have a physical trace-one ground projector.

Natural subtraction is truncated at zero. All other divisions are in Real or Complex. Scalar casts retain their target type. Matrix products are operator products, and Matrix.conjTranspose is conjugate transpose. Subtype.val is the value of a density; Equiv.symm applied to CStarMatrix.ofMatrix recovers its ordinary matrix. Assignment N is the occupation basis Fin N → Bool. Implicit Lean mode and dimension arguments may be displayed explicitly. Bracketed Fintype, DecidableEq and Nonempty assumptions are anonymous instance arguments.

**Theorem 1.1 (Trace-one ground projector and universal lower bound).**

$$\forall kappa \in \mathit{Type},\; \forall Omega \in \mathit{Type},\; [\mathrm{Fintype}\left(\mathit{kappa}\right)] [\mathrm{DecidableEq}\left(\mathit{kappa}\right)] [\mathrm{Fintype}\left(\mathit{Omega}\right)] [\mathrm{DecidableEq}\left(\mathit{Omega}\right)] [\mathrm{Nonempty}\left(\mathit{Omega}\right)] \forall eta \in \operatorname{Sum}\left(\mathit{kappa}, \mathit{kappa}\right) \to \mathrm{Matrix}\left(\mathit{Omega}, \mathit{Omega}, \mathit{Complex}\right),\; \forall T \in \mathrm{Matrix}\left(\mathit{Omega}, \mathit{Omega}, \mathit{Complex}\right),\; ((((\operatorname{Fintype}.\operatorname{card}\left(\mathit{Omega}\right) = 2^{\operatorname{Fintype}.\operatorname{card}\left(\mathit{kappa}\right)}) \land (\forall p \in \operatorname{Sum}\left(\mathit{kappa}, \mathit{kappa}\right),\; \operatorname{Matrix}.\operatorname{IsHermitian}\left(\mathrm{val}\left(\mathit{eta}, p\right)\right))) \land (\forall p \in \operatorname{Sum}\left(\mathit{kappa}, \mathit{kappa}\right),\; \forall t \in \operatorname{Sum}\left(\mathit{kappa}, \mathit{kappa}\right),\; \mathrm{val}\left(\mathit{eta}, p\right) \cdot \mathrm{val}\left(\mathit{eta}, t\right) + \mathrm{val}\left(\mathit{eta}, t\right) \cdot \mathrm{val}\left(\mathit{eta}, p\right) = \mathrm{ite}\left(p = t, \operatorname{SMul}.\operatorname{smul}\left((2:\mathit{Complex}), (1:\mathrm{Matrix}\left(\mathit{Omega}, \mathit{Omega}, \mathit{Complex}\right))\right), 0\right))) \land (\forall p \in \operatorname{Sum}\left(\mathit{kappa}, \mathit{kappa}\right),\; T \cdot \mathrm{val}\left(\mathit{eta}, p\right) = -\left(\mathrm{val}\left(\mathit{eta}, p\right) \cdot T\right))) \Rightarrow (\exists rho \in \mathrm{DensityState}\left(\mathit{Omega}\right),\; (((\mathrm{IsStarProjection}\left(\operatorname{Equiv}.\operatorname{symm}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}\right)\left(\operatorname{Subtype}.\operatorname{val}\left(\mathit{rho}\right)\right)\right)) \land (\mathrm{Commute}\left(\operatorname{Subtype}.\operatorname{val}\left(\mathit{rho}\right), \operatorname{CStarMatrix}.\operatorname{ofMatrix}\left(T\right)\right))) \land (\sum_{k:\mathit{kappa}}(\operatorname{SMul}.\operatorname{smul}\left(\operatorname{Complex}.\operatorname{I}, \mathrm{val}\left(\mathit{eta}, \operatorname{Sum}.\operatorname{inl}\left(k\right)\right) \cdot \mathrm{val}\left(\mathit{eta}, \operatorname{Sum}.\operatorname{inr}\left(k\right)\right)\right)) \cdot \operatorname{Equiv}.\operatorname{symm}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}\right)\left(\operatorname{Subtype}.\operatorname{val}\left(\mathit{rho}\right)\right) = \operatorname{SMul}.\operatorname{smul}\left(-(\operatorname{Fintype}.\operatorname{card}\left(\mathit{kappa}\right):\mathit{Complex}), \operatorname{Equiv}.\operatorname{symm}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}\right)\left(\operatorname{Subtype}.\operatorname{val}\left(\mathit{rho}\right)\right)\right))) \land (\forall omega \in \mathrm{DensityState}\left(\mathit{Omega}\right),\; -(\operatorname{Fintype}.\operatorname{card}\left(\mathit{kappa}\right):\mathit{Real}) \le \mathrm{meanEnergy}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}\left(\sum_{k:\mathit{kappa}}(\operatorname{SMul}.\operatorname{smul}\left(\operatorname{Complex}.\operatorname{I}, \mathrm{val}\left(\mathit{eta}, \operatorname{Sum}.\operatorname{inl}\left(k\right)\right) \cdot \mathrm{val}\left(\mathit{eta}, \operatorname{Sum}.\operatorname{inr}\left(k\right)\right)\right))\right), \mathit{omega}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CliffordGroundDensity.paired_clifford_ground` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each bilinear is a Hermitian involution. A single Majorana reverses its own bilinear and preserves the others, giving a joint minus projection of trace one. Complementary plus projections bound the energy of every density.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/CliffordGroundDensity.paired_clifford_ground`
- Dependency: [D5/S3/Quantum/Fermionic/JointSignProjectors](JointSignProjectors.md)
- Dependency: [D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity](../Information/CorrelatedGibbsEnergyIdentity.md)
