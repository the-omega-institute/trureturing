# The physical Clifford ground sector

## Abstract

Paired Clifford bilinears have a physical trace-one ground projector.

Nat, Real and Complex denote natural, real and complex numbers. Matrix products are operator products, smul is scalar multiplication, densityValue is the CStarMatrix value of a density, and densityMatrix is its underlying ordinary matrix; ofMatrix and matrixOf are the canonical CStarMatrix equivalence and its inverse. Fin is the finite index type, ProdType(A, B) denotes the product type A × B (Lean A × B), Assignment(N) is Fin(N) → Bool, and numberParity(N) is exp(iπ times the number operator). siteMajorana(n,m,v,p) means majorana(finProdFinEquiv(v,fst(p)),snd(p)) on Assignment(nm). All divisions below are real or complex divisions, as indicated by asReal and asComplex; inv is the corresponding scalar inverse. edgeCard(G) means G.edgeFinset.card, and coordinateCouplingFamily(r,e,a) is the function z ↦ coordinateCoupling(r,e,a,z). SumType(kappa,kappa) is a disjoint sum with injections inl and inr. The paired quadratic operator Q(eta) is the sum over k of i eta(inl(k)) eta(inr(k)). Hermitian means equality to the conjugate transpose, IsStarProjection means Hermitian and idempotent, Commute(A,B) means AB=BA. The cardinality equation fixes the Fock dimension.

**Theorem 1.1 (Trace-one ground projector and universal lower bound).**

$$\forall kappa \in \mathit{Type},\; \forall Omega \in \mathit{Type},\; [\mathrm{Fintype}\left(\mathit{kappa}\right)] [\mathrm{DecidableEq}\left(\mathit{kappa}\right)] [\mathrm{Fintype}\left(\mathit{Omega}\right)] [\mathrm{DecidableEq}\left(\mathit{Omega}\right)] [\mathrm{Nonempty}\left(\mathit{Omega}\right)] \forall eta \in \mathrm{SumType}\left(\mathit{kappa}, \mathit{kappa}\right) \to \mathrm{Matrix}\left(\mathit{Omega}, \mathit{Omega}, \mathit{Complex}\right),\; \forall T \in \mathrm{Matrix}\left(\mathit{Omega}, \mathit{Omega}, \mathit{Complex}\right),\; ((((\mathrm{card}\left(\mathit{Omega}\right) = 2^{\mathrm{card}\left(\mathit{kappa}\right)}) \land (\forall p \in \mathrm{SumType}\left(\mathit{kappa}, \mathit{kappa}\right),\; \mathrm{IsHermitian}\left(\mathrm{val}\left(\mathit{eta}, p\right)\right))) \land (\forall p \in \mathrm{SumType}\left(\mathit{kappa}, \mathit{kappa}\right),\; \forall t \in \mathrm{SumType}\left(\mathit{kappa}, \mathit{kappa}\right),\; \mathrm{val}\left(\mathit{eta}, p\right) \cdot \mathrm{val}\left(\mathit{eta}, t\right) + \mathrm{val}\left(\mathit{eta}, t\right) \cdot \mathrm{val}\left(\mathit{eta}, p\right) = \mathrm{ite}\left(p = t, \mathrm{smul}\left(\mathrm{asComplex}\left(2\right), (1:\mathrm{Matrix}\left(\mathit{Omega}, \mathit{Omega}, \mathit{Complex}\right))\right), 0\right))) \land (\forall p \in \mathrm{SumType}\left(\mathit{kappa}, \mathit{kappa}\right),\; T \cdot \mathrm{val}\left(\mathit{eta}, p\right) = -\left(\mathrm{val}\left(\mathit{eta}, p\right) \cdot T\right))) \Rightarrow (\exists rho \in \mathrm{DensityState}\left(\mathit{Omega}\right),\; (((\mathrm{IsStarProjection}\left(\mathrm{densityMatrix}\left(\mathit{rho}\right)\right)) \land (\mathrm{Commute}\left(\mathrm{densityValue}\left(\mathit{rho}\right), \mathrm{ofMatrix}\left(T\right)\right))) \land (\sum_{k:\mathit{kappa}}(\mathrm{smul}\left(\mathit{imaginaryUnit}, \mathrm{val}\left(\mathit{eta}, \mathrm{inl}\left(k\right)\right) \cdot \mathrm{val}\left(\mathit{eta}, \mathrm{inr}\left(k\right)\right)\right)) \cdot \mathrm{densityMatrix}\left(\mathit{rho}\right) = \mathrm{smul}\left(-\mathrm{asComplex}\left(\mathrm{card}\left(\mathit{kappa}\right)\right), \mathrm{densityMatrix}\left(\mathit{rho}\right)\right))) \land (\forall omega \in \mathrm{DensityState}\left(\mathit{Omega}\right),\; -\mathrm{asReal}\left(\mathrm{card}\left(\mathit{kappa}\right)\right) \le \mathrm{meanEnergy}\left(\mathrm{ofMatrix}\left(\sum_{k:\mathit{kappa}}(\mathrm{smul}\left(\mathit{imaginaryUnit}, \mathrm{val}\left(\mathit{eta}, \mathrm{inl}\left(k\right)\right) \cdot \mathrm{val}\left(\mathit{eta}, \mathrm{inr}\left(k\right)\right)\right))\right), \mathit{omega}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CliffordGroundDensity.paired_clifford_ground` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each bilinear is a Hermitian involution. A single Majorana reverses its own bilinear and preserves the others, giving a joint minus projection of trace one. Complementary plus projections bound the energy of every density.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/CliffordGroundDensity.paired_clifford_ground`
- Dependency: [D5/S3/Quantum/Fermionic/JointSignProjectors](JointSignProjectors.md)
- Dependency: [D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity](../Information/CorrelatedGibbsEnergyIdentity.md)
