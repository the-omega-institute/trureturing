# Physical tensor products and partial traces

## Abstract

Tensor site densities and their actual partial traces obey local number parity.

Nat, Real and Complex denote natural, real and complex numbers. Matrix products are operator products, smul is scalar multiplication, densityValue is the CStarMatrix value of a density, and densityMatrix is its underlying ordinary matrix; ofMatrix and matrixOf are the canonical CStarMatrix equivalence and its inverse. Fin is the finite index type, ProdType(A, B) denotes the product type A × B (Lean A × B), Assignment(N) is Fin(N) → Bool, and numberParity(N) is exp(iπ times the number operator). siteMajorana(n,m,v,p) means majorana(finProdFinEquiv(v,fst(p)),snd(p)) on Assignment(nm). All divisions below are real or complex divisions, as indicated by asReal and asComplex; inv is the corresponding scalar inverse. edgeCard(G) means G.edgeFinset.card, and coordinateCouplingFamily(r,e,a) is the function z ↦ coordinateCoupling(r,e,a,z). siteOccupation(n,m,x,v) is the function j ↦ x(finProdFinEquiv(v,j)). splitSite(n,m,v) is the composition of arrowCongr(finProdFinEquiv.symm,refl Bool), curry(Fin n,Fin m,Bool) and funSplitAt(v,Assignment m). ComplementSites(n,v) is the subtype of vertices different from v.

**Definition 1.1 (Literal site tensor density).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall states \in \mathrm{Fin}\left(n\right) \to \mathrm{DensityState}\left(\mathrm{Assignment}\left(m\right)\right),\; \forall x \in \mathrm{Assignment}\left(n \cdot m\right),\; \forall y \in \mathrm{Assignment}\left(n \cdot m\right),\; \mathrm{val}\left(\mathrm{densityMatrix}\left(\mathrm{siteProduct}\left(n, m, \mathit{states}\right)\right), x, y\right) = \prod_{v:\mathrm{Fin}\left(n\right)}(\mathrm{val}\left(\mathrm{densityMatrix}\left(\mathrm{val}\left(\mathit{states}, v\right)\right), \mathrm{siteOccupation}\left(n, m, x, v\right), \mathrm{siteOccupation}\left(n, m, y, v\right)\right))$$

*Formalization.* `D5/S3/Quantum/Fermionic/PhysicalSiteProducts.siteProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix entries are the product of the site density entries, with occupation configurations transported by the site equivalence. Positivity and trace one are part of the density type.

**Definition 1.2 (Actual one-site partial trace).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall v \in \mathrm{Fin}\left(n\right),\; \forall rho \in \mathrm{DensityState}\left(\mathrm{Assignment}\left(n \cdot m\right)\right),\; \forall x \in \mathrm{Assignment}\left(m\right),\; \forall y \in \mathrm{Assignment}\left(m\right),\; \mathrm{val}\left(\mathrm{densityMatrix}\left(\mathrm{oneSiteMarginal}\left(n, m, v, \mathit{rho}\right)\right), x, y\right) = \sum_{z:\mathrm{ComplementSites}\left(n, v\right) \to \mathrm{Assignment}\left(m\right)}(\mathrm{val}\left(\mathrm{densityMatrix}\left(\mathit{rho}\right), \mathrm{val}\left(\mathrm{inverseEquiv}\left(\mathrm{splitSite}\left(n, m, v\right)\right), \mathrm{pair}\left(x, z\right)\right), \mathrm{val}\left(\mathrm{inverseEquiv}\left(\mathrm{splitSite}\left(n, m, v\right)\right), \mathrm{pair}\left(y, z\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Fermionic/PhysicalSiteProducts.oneSiteMarginal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The density is reindexed by the split-site equivalence and its complementary-site factor is traced out.

**Definition 1.3 (Global physicality).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall rho \in \mathrm{DensityState}\left(\mathrm{Assignment}\left(n \cdot m\right)\right),\; (\mathrm{physicalState}\left(\mathit{rho}\right)) \Leftrightarrow (\mathrm{Commute}\left(\mathrm{densityValue}\left(\mathit{rho}\right), \mathrm{ofMatrix}\left(\mathrm{numberParity}\left(n \cdot m\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Fermionic/PhysicalSiteProducts.physicalState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A physical density commutes with total occupation parity.

**Definition 1.4 (Physical site product).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall rho \in \mathrm{DensityState}\left(\mathrm{Assignment}\left(n \cdot m\right)\right),\; (\mathrm{physicalProduct}\left(\mathit{rho}\right)) \Leftrightarrow (\exists states \in \mathrm{Fin}\left(n\right) \to \mathrm{DensityState}\left(\mathrm{Assignment}\left(m\right)\right),\; (\forall v \in \mathrm{Fin}\left(n\right),\; \mathrm{Commute}\left(\mathrm{densityValue}\left(\mathrm{val}\left(\mathit{states}, v\right)\right), \mathrm{ofMatrix}\left(\mathrm{numberParity}\left(m\right)\right)\right)) \land (\mathit{rho} = \mathrm{siteProduct}\left(n, m, \mathit{states}\right)))$$

*Formalization.* `D5/S3/Quantum/Fermionic/PhysicalSiteProducts.physicalProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The witnesses are genuine site densities, each commuting with its local number parity. Their tensor density is the specified state.

**Definition 1.5 (Local site parity on the Fock space).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall v \in \mathrm{Fin}\left(n\right),\; \forall x \in \mathrm{Assignment}\left(n \cdot m\right),\; \forall y \in \mathrm{Assignment}\left(n \cdot m\right),\; \mathrm{val}\left(\mathrm{siteParity}\left(n, m, v\right), x, y\right) = \mathrm{ite}\left(x = y, \mathrm{val}\left(\mathrm{numberParity}\left(m\right), \mathrm{siteOccupation}\left(n, m, x, v\right), \mathrm{siteOccupation}\left(n, m, x, v\right)\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/PhysicalSiteProducts.siteParity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This diagonal operator records the occupation parity at the selected site.

**Theorem 1.6 (Physicality of every actual marginal).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall v \in \mathrm{Fin}\left(n\right),\; \forall rho \in \mathrm{DensityState}\left(\mathrm{Assignment}\left(n \cdot m\right)\right),\; (\mathrm{physicalState}\left(\mathit{rho}\right)) \Rightarrow (\mathrm{Commute}\left(\mathrm{densityValue}\left(\mathrm{oneSiteMarginal}\left(n, m, v, \mathit{rho}\right)\right), \mathrm{ofMatrix}\left(\mathrm{numberParity}\left(m\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/PhysicalSiteProducts.one_site_marginal_physical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Global parity factors through a selected site and its complement. Tracing over the complement cancels its nonzero parity signs and leaves local parity commutation.

**Theorem 1.7 (Action of site parity on Majoranas).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall v \in \mathrm{Fin}\left(n\right),\; \forall w \in \mathrm{Fin}\left(n\right),\; \forall j \in \mathrm{Fin}\left(m\right),\; \forall b \in \mathit{Bool},\; ((\mathrm{IsHermitian}\left(\mathrm{siteParity}\left(n, m, v\right)\right)) \land (\mathrm{siteParity}\left(n, m, v\right) \cdot \mathrm{siteParity}\left(n, m, v\right) = (1:\mathrm{Matrix}\left(\mathrm{Assignment}\left(n \cdot m\right), \mathrm{Assignment}\left(n \cdot m\right), \mathit{Complex}\right)))) \land (\mathrm{siteParity}\left(n, m, v\right) \cdot \mathrm{siteMajorana}\left(n, m, w, \mathrm{pair}\left(j, b\right)\right) = \mathrm{smul}\left(\mathrm{ite}\left(v = w, -\mathrm{asComplex}\left(1\right), \mathrm{asComplex}\left(1\right)\right), \mathrm{siteMajorana}\left(n, m, w, \mathrm{pair}\left(j, b\right)\right) \cdot \mathrm{siteParity}\left(n, m, v\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/PhysicalSiteProducts.site_parity_majorana` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Jordan-Wigner matrix changes precisely one occupation bit. The selected site parity therefore flips exactly the Majoranas at that site.

**Theorem 1.8 (Zero product energy).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall G \in \mathrm{SimpleGraph}\left(\mathrm{Fin}\left(n\right)\right),\; \forall K \in \mathrm{edgeSet}\left(G\right) \to \mathrm{Matrix}\left(\mathrm{ProdType}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right), \mathrm{ProdType}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right), \mathit{Real}\right),\; \forall rho \in \mathrm{DensityState}\left(\mathrm{Assignment}\left(n \cdot m\right)\right),\; (\mathrm{physicalProduct}\left(\mathit{rho}\right)) \Rightarrow (\mathrm{meanEnergy}\left(\mathrm{averagedHamiltonian}\left(G, K\right), \mathit{rho}\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/PhysicalSiteProducts.physical_products_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugation by the parity of the first endpoint preserves a physical site product and reverses the interaction. Its trace against that product is zero, and the literal average has zero energy.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/PhysicalSiteProducts.oneSiteMarginal`
- Truth anchor: `D5/S3/Quantum/Fermionic/PhysicalSiteProducts.one_site_marginal_physical`
- Truth anchor: `D5/S3/Quantum/Fermionic/PhysicalSiteProducts.physicalProduct`
- Truth anchor: `D5/S3/Quantum/Fermionic/PhysicalSiteProducts.physicalState`
- Truth anchor: `D5/S3/Quantum/Fermionic/PhysicalSiteProducts.physical_products_zero`
- Truth anchor: `D5/S3/Quantum/Fermionic/PhysicalSiteProducts.siteParity`
- Truth anchor: `D5/S3/Quantum/Fermionic/PhysicalSiteProducts.siteProduct`
- Truth anchor: `D5/S3/Quantum/Fermionic/PhysicalSiteProducts.site_parity_majorana`
- Dependency: [D5/S3/Quantum/Fermionic/CoordinateEdgeHamiltonian](CoordinateEdgeHamiltonian.md)
- Dependency: [D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity](../Information/CorrelatedGibbsEnergyIdentity.md)
