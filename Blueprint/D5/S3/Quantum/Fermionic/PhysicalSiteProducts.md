# Physical tensor products and partial traces

## Abstract

Tensor site densities and their actual partial traces obey local number parity.

Natural subtraction is truncated at zero. All other divisions are in Real or Complex. Scalar casts retain their target type. Matrix products are operator products, and Matrix.conjTranspose is conjugate transpose. Subtype.val is the value of a density; Equiv.symm applied to CStarMatrix.ofMatrix recovers its ordinary matrix. Assignment N is the occupation basis Fin N → Bool. Implicit Lean mode and dimension arguments may be displayed explicitly. Bracketed Fintype, DecidableEq and Nonempty assumptions are anonymous instance arguments.

**Definition 1.1 (Literal site tensor density).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall states \in \mathrm{Fin}\left(n\right) \to \mathrm{DensityState}\left(\mathrm{Assignment}\left(m\right)\right),\; \forall x \in \mathrm{Assignment}\left(n \cdot m\right),\; \forall y \in \mathrm{Assignment}\left(n \cdot m\right),\; \mathrm{val}\left(\operatorname{Equiv}.\operatorname{symm}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}\right)\left(\operatorname{Subtype}.\operatorname{val}\left(\mathrm{siteProduct}\left(n, m, \mathit{states}\right)\right)\right), x, y\right) = \prod_{v:\mathrm{Fin}\left(n\right)}(\mathrm{val}\left(\operatorname{Equiv}.\operatorname{symm}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}\right)\left(\operatorname{Subtype}.\operatorname{val}\left(\mathrm{val}\left(\mathit{states}, v\right)\right)\right), \lambda(j:\mathrm{Fin}\left(m\right))\mapsto(\mathrm{val}\left(x, \operatorname{finProdFinEquiv}\left(\operatorname{Prod}.\operatorname{mk}\left(v, j\right)\right)\right)), \lambda(j:\mathrm{Fin}\left(m\right))\mapsto(\mathrm{val}\left(y, \operatorname{finProdFinEquiv}\left(\operatorname{Prod}.\operatorname{mk}\left(v, j\right)\right)\right))\right))$$

*Formalization.* `D5/S3/Quantum/Fermionic/PhysicalSiteProducts.siteProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix entries are the product of the site density entries, with occupation configurations transported by the site equivalence. Positivity and trace one are part of the density type.

**Definition 1.2 (Actual one-site partial trace).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall v \in \mathrm{Fin}\left(n\right),\; \forall rho \in \mathrm{DensityState}\left(\mathrm{Assignment}\left(n \cdot m\right)\right),\; \forall x \in \mathrm{Assignment}\left(m\right),\; \forall y \in \mathrm{Assignment}\left(m\right),\; \mathrm{val}\left(\operatorname{Equiv}.\operatorname{symm}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}\right)\left(\operatorname{Subtype}.\operatorname{val}\left(\mathrm{oneSiteMarginal}\left(n, m, v, \mathit{rho}\right)\right)\right), x, y\right) = \sum_{z:\operatorname{Subtype}\left(\lambda(w:\mathrm{Fin}\left(n\right))\mapsto(w \ne v)\right) \to \mathrm{Assignment}\left(m\right)}(\mathrm{val}\left(\operatorname{Equiv}.\operatorname{symm}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}\right)\left(\operatorname{Subtype}.\operatorname{val}\left(\mathit{rho}\right)\right), \mathrm{val}\left(\operatorname{Equiv}.\operatorname{symm}\left(\operatorname{Equiv}.\operatorname{trans}\left(\operatorname{Equiv}.\operatorname{trans}\left(\operatorname{Equiv}.\operatorname{arrowCongr}\left(\operatorname{Equiv}.\operatorname{symm}\left(\operatorname{finProdFinEquiv}\right), \operatorname{Equiv}.\operatorname{refl}\left(\mathit{Bool}\right)\right), \operatorname{Equiv}.\operatorname{curry}\left(\mathrm{Fin}\left(n\right), \mathrm{Fin}\left(m\right), \mathit{Bool}\right)\right), \operatorname{Equiv}.\operatorname{funSplitAt}\left(v, \mathrm{Assignment}\left(m\right)\right)\right)\right), \operatorname{Prod}.\operatorname{mk}\left(x, z\right)\right), \mathrm{val}\left(\operatorname{Equiv}.\operatorname{symm}\left(\operatorname{Equiv}.\operatorname{trans}\left(\operatorname{Equiv}.\operatorname{trans}\left(\operatorname{Equiv}.\operatorname{arrowCongr}\left(\operatorname{Equiv}.\operatorname{symm}\left(\operatorname{finProdFinEquiv}\right), \operatorname{Equiv}.\operatorname{refl}\left(\mathit{Bool}\right)\right), \operatorname{Equiv}.\operatorname{curry}\left(\mathrm{Fin}\left(n\right), \mathrm{Fin}\left(m\right), \mathit{Bool}\right)\right), \operatorname{Equiv}.\operatorname{funSplitAt}\left(v, \mathrm{Assignment}\left(m\right)\right)\right)\right), \operatorname{Prod}.\operatorname{mk}\left(y, z\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Fermionic/PhysicalSiteProducts.oneSiteMarginal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The density is reindexed by the split-site equivalence and its complementary-site factor is traced out.

**Definition 1.3 (Global physicality).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall rho \in \mathrm{DensityState}\left(\mathrm{Assignment}\left(n \cdot m\right)\right),\; (\mathrm{physicalState}\left(\mathit{rho}\right)) \Leftrightarrow (\mathrm{Commute}\left(\operatorname{Subtype}.\operatorname{val}\left(\mathit{rho}\right), \operatorname{CStarMatrix}.\operatorname{ofMatrix}\left(\mathrm{numberParity}\left(n \cdot m\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Fermionic/PhysicalSiteProducts.physicalState` (`✓ std3`).

*Citation.* Amir-Reza Negari; Farzin Salek; Zoltán Zimborás; Aram Harrow; Patrick Hayden; Jens Eisert (2026). *Approximation theorems for fermionic Gaussian states*. DOI: [10.48550/arXiv.2610.01860](https://doi.org/10.48550/arXiv.2610.01860). URL: <https://arxiv.org/abs/2610.01860v1>.

*Commentary.*

“Physical fermionic states obey the parity superselection rule” [printed page 3]: [ρ,P] = 0. Here P is the exponential of the number operator; rho.val is the actual density matrix.

**Definition 1.4 (Physical site product).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall rho \in \mathrm{DensityState}\left(\mathrm{Assignment}\left(n \cdot m\right)\right),\; (\mathrm{physicalProduct}\left(\mathit{rho}\right)) \Leftrightarrow (\exists states \in \mathrm{Fin}\left(n\right) \to \mathrm{DensityState}\left(\mathrm{Assignment}\left(m\right)\right),\; (\forall v \in \mathrm{Fin}\left(n\right),\; \mathrm{Commute}\left(\operatorname{Subtype}.\operatorname{val}\left(\mathrm{val}\left(\mathit{states}, v\right)\right), \operatorname{CStarMatrix}.\operatorname{ofMatrix}\left(\mathrm{numberParity}\left(m\right)\right)\right)) \land (\mathit{rho} = \mathrm{siteProduct}\left(n, m, \mathit{states}\right)))$$

*Formalization.* `D5/S3/Quantum/Fermionic/PhysicalSiteProducts.physicalProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The witnesses are genuine site densities, each commuting with its local number parity. Their tensor density is the specified state.

**Definition 1.5 (Local site parity on the Fock space).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall v \in \mathrm{Fin}\left(n\right),\; \forall x \in \mathrm{Assignment}\left(n \cdot m\right),\; \forall y \in \mathrm{Assignment}\left(n \cdot m\right),\; \mathrm{val}\left(\mathrm{siteParity}\left(n, m, v\right), x, y\right) = \mathrm{ite}\left(x = y, \mathrm{val}\left(\mathrm{numberParity}\left(m\right), \lambda(j:\mathrm{Fin}\left(m\right))\mapsto(\mathrm{val}\left(x, \operatorname{finProdFinEquiv}\left(\operatorname{Prod}.\operatorname{mk}\left(v, j\right)\right)\right)), \lambda(j:\mathrm{Fin}\left(m\right))\mapsto(\mathrm{val}\left(x, \operatorname{finProdFinEquiv}\left(\operatorname{Prod}.\operatorname{mk}\left(v, j\right)\right)\right))\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/PhysicalSiteProducts.siteParity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This diagonal operator records the occupation parity at the selected site.

**Theorem 1.6 (Physicality of every actual marginal).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall v \in \mathrm{Fin}\left(n\right),\; \forall rho \in \mathrm{DensityState}\left(\mathrm{Assignment}\left(n \cdot m\right)\right),\; (\mathrm{physicalState}\left(\mathit{rho}\right)) \Rightarrow (\mathrm{Commute}\left(\operatorname{Subtype}.\operatorname{val}\left(\mathrm{oneSiteMarginal}\left(n, m, v, \mathit{rho}\right)\right), \operatorname{CStarMatrix}.\operatorname{ofMatrix}\left(\mathrm{numberParity}\left(m\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/PhysicalSiteProducts.one_site_marginal_physical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Global parity factors through a selected site and its complement. Tracing over the complement cancels its nonzero parity signs and leaves local parity commutation.

**Theorem 1.7 (Action of site parity on Majoranas).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall v \in \mathrm{Fin}\left(n\right),\; \forall w \in \mathrm{Fin}\left(n\right),\; \forall j \in \mathrm{Fin}\left(m\right),\; \forall b \in \mathit{Bool},\; ((\operatorname{Matrix}.\operatorname{IsHermitian}\left(\mathrm{siteParity}\left(n, m, v\right)\right)) \land (\mathrm{siteParity}\left(n, m, v\right) \cdot \mathrm{siteParity}\left(n, m, v\right) = (1:\mathrm{Matrix}\left(\mathrm{Assignment}\left(n \cdot m\right), \mathrm{Assignment}\left(n \cdot m\right), \mathit{Complex}\right)))) \land (\mathrm{siteParity}\left(n, m, v\right) \cdot \operatorname{majorana}\left(n \cdot m, \operatorname{finProdFinEquiv}\left(\operatorname{Prod}.\operatorname{mk}\left(w, \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{mk}\left(j, b\right)\right)\right)\right), \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{mk}\left(j, b\right)\right)\right) = \operatorname{SMul}.\operatorname{smul}\left(\mathrm{ite}\left(v = w, -(1:\mathit{Complex}), (1:\mathit{Complex})\right), \operatorname{majorana}\left(n \cdot m, \operatorname{finProdFinEquiv}\left(\operatorname{Prod}.\operatorname{mk}\left(w, \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{mk}\left(j, b\right)\right)\right)\right), \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{mk}\left(j, b\right)\right)\right) \cdot \mathrm{siteParity}\left(n, m, v\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/PhysicalSiteProducts.site_parity_majorana` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Jordan-Wigner matrix changes precisely one occupation bit. The selected site parity therefore flips exactly the Majoranas at that site.

**Theorem 1.8 (Zero product energy).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall G \in \mathrm{SimpleGraph}\left(\mathrm{Fin}\left(n\right)\right),\; \forall K \in \operatorname{SimpleGraph}.\operatorname{edgeSet}\left(G\right) \to \mathrm{Matrix}\left(\operatorname{Prod}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right), \operatorname{Prod}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right), \mathit{Real}\right),\; \forall rho \in \mathrm{DensityState}\left(\mathrm{Assignment}\left(n \cdot m\right)\right),\; (\mathrm{physicalProduct}\left(\mathit{rho}\right)) \Rightarrow (\mathrm{meanEnergy}\left(\mathrm{averagedHamiltonian}\left(G, K\right), \mathit{rho}\right) = 0)$$

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
