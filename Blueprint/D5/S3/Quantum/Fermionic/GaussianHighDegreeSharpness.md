# Sharpness of the high-degree fermionic bounds

## Abstract

The fermionic high-degree energy and free-energy constants are sharp.

Nat, Real and Complex denote natural, real and complex numbers. Matrix products are operator products, smul is scalar multiplication, densityValue is the CStarMatrix value of a density, and densityMatrix is its underlying ordinary matrix; ofMatrix and matrixOf are the canonical CStarMatrix equivalence and its inverse. Fin is the finite index type, Prod(A,B) is the product type A × B, sqrt is the real square root Real.sqrt, Assignment(N) is Fin(N) → Bool, and numberParity(N) is exp(iπ times the number operator). siteMajorana(n,m,v,p) means majorana(finProdFinEquiv(v,fst(p)),snd(p)) on Assignment(nm). All divisions below are real or complex divisions, as indicated by asReal and asComplex; inv is the corresponding scalar inverse. edgeCard(G) means G.edgeFinset.card, and coordinateCouplingFamily(r,e,a) is the function z ↦ coordinateCoupling(r,e,a,z). energyGap is the product-energy infimum minus the physical-energy infimum. freeGap compares the actual Gibbs density with the tensor product of its actual one-site marginals. The Majoranas are the concrete Jordan-Wigner matrices, with m modes at each vertex.

**Definition 1.1 (Quantified uniform sharpness).**

$$\mathit{claim} = \left(\forall m \in \mathit{Nat},\; (1 \le m) \Rightarrow (\forall c \in \mathit{Real},\; (c < 1) \Rightarrow (\forall D0 \in \mathit{Nat},\; \exists n \in \mathit{Nat},\; \exists D \in \mathit{Nat},\; \exists G \in \mathrm{SimpleGraph}\left(\mathrm{Fin}\left(n\right)\right),\; \exists K \in \mathrm{edgeSet}\left(G\right) \to \mathrm{Matrix}\left(\mathrm{Prod}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right), \mathrm{Prod}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right), \mathit{Real}\right),\; \exists hH \in \mathrm{IsSelfAdjoint}\left(\mathrm{averagedHamiltonian}\left(G, K\right)\right),\; ((((((1 \le n) \land (\mathit{D0} \le D)) \land (1 \le D)) \land (\mathrm{IsRegularOfDegree}\left(G, D\right))) \land (\mathrm{admissibleEdges}\left(G, K\right))) \land (\mathrm{energyGap}\left(\mathrm{averagedHamiltonian}\left(G, K\right)\right) = \mathrm{sqrt}\left(\frac{\mathrm{asReal}\left(2 \cdot m\right)}{\mathrm{asReal}\left(D\right)}\right))) \land (\exists beta \in \mathit{Real},\; (0 < \mathit{beta}) \land (c \cdot \mathrm{sqrt}\left(\frac{\mathrm{asReal}\left(2 \cdot m\right)}{\mathrm{asReal}\left(D\right)}\right) < \mathrm{freeGap}\left(\mathrm{averagedHamiltonian}\left(G, K\right), \mathit{hH}, \mathit{beta}\right)))))\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/GaussianHighDegreeSharpness.claim` (`✓ std3`).

*Citation.* Amir-Reza Negari; Farzin Salek; Zoltán Zimborás; Aram Harrow; Patrick Hayden; Jens Eisert (2026). *Approximation theorems for fermionic Gaussian states*. DOI: [10.48550/arXiv.2610.01860](https://doi.org/10.48550/arXiv.2610.01860). URL: <https://arxiv.org/abs/2610.01860v1>.

*Commentary.*

Section VI, printed page 26: “It remains open, however, whether the constants in the resulting high-degree energy and free-energy estimates are optimal, since their derivation also uses edge averaging, Cauchy–Schwarz, and only the operator-norm normalization of the interactions.” The displayed statement expresses uniform optimality: for every positive mode count and every degree cutoff, the energy bound is attained on a finite regular graph, and the free-energy gap exceeds every smaller prefactor at some finite positive inverse temperature.

**Theorem 1.2 (The high-degree constants are sharp).**

$$\mathit{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/GaussianHighDegreeSharpness.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a power-of-two conference order s with 2m(s−1) at least the prescribed cutoff and take the Cartesian product of 2m complete graphs on s vertices. Its normalized quadratic interactions have product energy zero and physical ground energy −sqrt(2m/D). The entropy budget of the Gibbs product is at most log of the Fock dimension; choosing a sufficiently large finite positive beta gives the strict free-gap inequality.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/GaussianHighDegreeSharpness.claim`
- Truth anchor: `D5/S3/Quantum/Fermionic/GaussianHighDegreeSharpness.result`
- Dependency: [D5/S3/Quantum/Fermionic/CoordinateAverage](CoordinateAverage.md)
- Dependency: [D5/S3/Quantum/Fermionic/FlatCliffordGround](FlatCliffordGround.md)
- Dependency: [D5/S3/Quantum/Fermionic/GibbsProductGap](GibbsProductGap.md)
