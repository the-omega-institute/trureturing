# The Gibbs product entropy budget

## Abstract

Physical Gibbs marginals yield the entropy-budget lower bound on the free gap.

Nat, Real and Complex denote natural, real and complex numbers. Matrix products are operator products, smul is scalar multiplication, densityValue is the CStarMatrix value of a density, and densityMatrix is its underlying ordinary matrix; ofMatrix and matrixOf are the canonical CStarMatrix equivalence and its inverse. Fin is the finite index type, ProdType(A, B) denotes the product type A × B (Lean A × B), Assignment(N) is Fin(N) → Bool, and numberParity(N) is exp(iπ times the number operator). siteMajorana(n,m,v,p) means majorana(finProdFinEquiv(v,fst(p)),snd(p)) on Assignment(nm). All divisions below are real or complex divisions, as indicated by asReal and asComplex; inv is the corresponding scalar inverse. edgeCard(G) means G.edgeFinset.card, and coordinateCouplingFamily(r,e,a) is the function z ↦ coordinateCoupling(r,e,a,z). setOf(x ↦ P(x)) denotes the literal predicate-defined set of real energy values, and sInf denotes its infimum. Function expressions are written with the mapsto binder. thermalState(H,hH,beta) is exp(-beta H) divided by its trace, with the Hermitian proof hH. The product of marginals is built from the actual one-site partial traces. Natural numbers in dimension logarithms are cast to Real.

**Definition 1.1 (Difference of literal energy infima).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall H \in \mathrm{CStarMatrix}\left(\mathrm{Assignment}\left(n \cdot m\right), \mathrm{Assignment}\left(n \cdot m\right), \mathit{Complex}\right),\; \mathrm{energyGap}\left(H\right) = \mathrm{sInf}\left(\mathrm{setOf}\left(\lambda(x:\mathit{Real})\mapsto(\exists rho \in \mathrm{DensityState}\left(\mathrm{Assignment}\left(n \cdot m\right)\right),\; (\mathrm{physicalProduct}\left(\mathit{rho}\right)) \land (x = \mathrm{meanEnergy}\left(H, \mathit{rho}\right)))\right)\right) - \mathrm{sInf}\left(\mathrm{setOf}\left(\lambda(x:\mathit{Real})\mapsto(\exists rho \in \mathrm{DensityState}\left(\mathrm{Assignment}\left(n \cdot m\right)\right),\; (\mathrm{physicalState}\left(\mathit{rho}\right)) \land (x = \mathrm{meanEnergy}\left(H, \mathit{rho}\right)))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/GibbsProductGap.energyGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both sets contain the actual trace energies of density states with the displayed physicality predicates. The infimum over all physical densities is subtracted from the product infimum.

**Definition 1.2 (Free energy in nats).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall H \in \mathrm{CStarMatrix}\left(\mathrm{Assignment}\left(n \cdot m\right), \mathrm{Assignment}\left(n \cdot m\right), \mathit{Complex}\right),\; \forall beta \in \mathit{Real},\; \forall rho \in \mathrm{DensityState}\left(\mathrm{Assignment}\left(n \cdot m\right)\right),\; \mathrm{freeEnergy}\left(H, \mathit{beta}, \mathit{rho}\right) = \mathrm{meanEnergy}\left(H, \mathit{rho}\right) - \frac{\mathrm{vonNeumannEntropy}\left(\mathit{rho}\right)}{\mathit{beta}}$$

*Formalization.* `D5/S3/Quantum/Fermionic/GibbsProductGap.freeEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entropy is von Neumann entropy using the natural logarithm.

**Definition 1.3 (Actual Gibbs-to-product free-energy difference).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall H \in \mathrm{CStarMatrix}\left(\mathrm{Assignment}\left(n \cdot m\right), \mathrm{Assignment}\left(n \cdot m\right), \mathit{Complex}\right),\; \forall hH \in \mathrm{IsSelfAdjoint}\left(H\right),\; \forall beta \in \mathit{Real},\; \mathrm{freeGap}\left(H, \mathit{hH}, \mathit{beta}\right) = \mathrm{freeEnergy}\left(H, \mathit{beta}, \mathrm{siteProduct}\left(n, m, \lambda(v:\mathrm{Fin}\left(n\right))\mapsto(\mathrm{oneSiteMarginal}\left(n, m, v, \mathrm{thermalState}\left(H, \mathit{hH}, \mathit{beta}\right)\right))\right)\right) - \mathrm{freeEnergy}\left(H, \mathit{beta}, \mathrm{thermalState}\left(H, \mathit{hH}, \mathit{beta}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/GibbsProductGap.freeGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The comparison state is the tensor product of the actual one-site marginals of the Gibbs density.

**Theorem 1.4 (Ground-sector entropy-budget bound).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall G \in \mathrm{SimpleGraph}\left(\mathrm{Fin}\left(n\right)\right),\; \forall K \in \mathrm{edgeSet}\left(G\right) \to \mathrm{Matrix}\left(\mathrm{ProdType}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right), \mathrm{ProdType}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right), \mathit{Real}\right),\; \forall hH \in \mathrm{IsSelfAdjoint}\left(\mathrm{averagedHamiltonian}\left(G, K\right)\right),\; \forall ground \in \mathrm{DensityState}\left(\mathrm{Assignment}\left(n \cdot m\right)\right),\; \forall E \in \mathit{Real},\; \forall beta \in \mathit{Real},\; ((((\mathrm{admissibleEdges}\left(G, K\right)) \land (\mathrm{IsStarProjection}\left(\mathrm{densityMatrix}\left(\mathit{ground}\right)\right))) \land (\mathrm{matrixOf}\left(\mathrm{averagedHamiltonian}\left(G, K\right)\right) \cdot \mathrm{densityMatrix}\left(\mathit{ground}\right) = \mathrm{smul}\left(\mathrm{asComplex}\left(E\right), \mathrm{densityMatrix}\left(\mathit{ground}\right)\right))) \land (0 < \mathit{beta})) \Rightarrow ((\mathrm{physicalProduct}\left(\mathrm{siteProduct}\left(n, m, \lambda(v:\mathrm{Fin}\left(n\right))\mapsto(\mathrm{oneSiteMarginal}\left(n, m, v, \mathrm{thermalState}\left(\mathrm{averagedHamiltonian}\left(G, K\right), \mathit{hH}, \mathit{beta}\right)\right))\right)\right)) \land (-E - \frac{\mathrm{log}\left(\mathrm{asReal}\left(\mathrm{card}\left(\mathrm{Assignment}\left(n \cdot m\right)\right)\right)\right)}{\mathit{beta}} \le \mathrm{freeGap}\left(\mathrm{averagedHamiltonian}\left(G, K\right), \mathit{hH}, \mathit{beta}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/GibbsProductGap.gibbs_product_free_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Gibbs density commutes with global parity, hence every actual site marginal commutes with its local parity. Their product has zero interaction energy. A trace-one ground projection bounds the partition function below by exp(-beta E), while the product entropy is bounded above by the logarithm of the Fock dimension.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/GibbsProductGap.energyGap`
- Truth anchor: `D5/S3/Quantum/Fermionic/GibbsProductGap.freeEnergy`
- Truth anchor: `D5/S3/Quantum/Fermionic/GibbsProductGap.freeGap`
- Truth anchor: `D5/S3/Quantum/Fermionic/GibbsProductGap.gibbs_product_free_bound`
- Dependency: [D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity](../Dynamics/EnergyEigenstateStationarity.md)
- Dependency: [D5/S3/Quantum/Fermionic/PhysicalSiteProducts](PhysicalSiteProducts.md)
- Dependency: [D5/S3/Quantum/Sharpness/FreeNegentropyBudget](../Sharpness/FreeNegentropyBudget.md)
