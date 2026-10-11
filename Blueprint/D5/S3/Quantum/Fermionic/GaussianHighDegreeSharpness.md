# Sharpness of the high-degree fermionic bounds

## Abstract

The fermionic high-degree energy and free-energy constants are sharp.

Natural subtraction is truncated at zero. All other divisions are in Real or Complex. Scalar casts retain their target type. Matrix products are operator products, and Matrix.conjTranspose is conjugate transpose. Subtype.val is the value of a density; Equiv.symm applied to CStarMatrix.ofMatrix recovers its ordinary matrix. Assignment N is the occupation basis Fin N → Bool. Implicit Lean mode and dimension arguments may be displayed explicitly. Bracketed Fintype, DecidableEq and Nonempty assumptions are anonymous instance arguments.

**Definition 1.1 (Quantified uniform sharpness).**

$$\mathit{claim} = \left(\forall m \in \mathit{Nat},\; (1 \le m) \Rightarrow (\forall c \in \mathit{Real},\; (c < 1) \Rightarrow (\forall D0 \in \mathit{Nat},\; \exists n \in \mathit{Nat},\; \exists D \in \mathit{Nat},\; \exists G \in \mathrm{SimpleGraph}\left(\mathrm{Fin}\left(n\right)\right),\; \exists K \in \operatorname{SimpleGraph}.\operatorname{edgeSet}\left(G\right) \to \mathrm{Matrix}\left(\mathrm{Prod}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right), \mathrm{Prod}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right), \mathit{Real}\right),\; \exists hH \in \mathrm{IsSelfAdjoint}\left(\mathrm{averagedHamiltonian}\left(G, K\right)\right),\; ((((((1 \le n) \land (\mathit{D0} \le D)) \land (1 \le D)) \land (\operatorname{SimpleGraph}.\operatorname{IsRegularOfDegree}\left(G, D\right))) \land (\mathrm{admissibleEdges}\left(G, K\right))) \land (\mathrm{energyGap}\left(\mathrm{averagedHamiltonian}\left(G, K\right)\right) = \operatorname{Real}.\operatorname{sqrt}\left(\frac{(2 \cdot m:\mathit{Real})}{(D:\mathit{Real})}\right))) \land (\exists beta \in \mathit{Real},\; (0 < \mathit{beta}) \land (c \cdot \operatorname{Real}.\operatorname{sqrt}\left(\frac{(2 \cdot m:\mathit{Real})}{(D:\mathit{Real})}\right) < \mathrm{freeGap}\left(\mathrm{averagedHamiltonian}\left(G, K\right), \mathit{hH}, \mathit{beta}\right)))))\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/GaussianHighDegreeSharpness.claim` (`✓ std3`).

*Citation.* Amir-Reza Negari; Farzin Salek; Zoltán Zimborás; Aram Harrow; Patrick Hayden; Jens Eisert (2026). *Approximation theorems for fermionic Gaussian states*. DOI: [10.48550/arXiv.2610.01860](https://doi.org/10.48550/arXiv.2610.01860). URL: <https://arxiv.org/abs/2610.01860v1>.

*Commentary.*

Section VI, printed page 26: “It remains open, however, whether the constants in the resulting high-degree energy and free-energy estimates are optimal, since their derivation also uses edge averaging, Cauchy–Schwarz, and only the operator-norm normalization of the interactions.” The displayed statement expresses uniform optimality: for every positive mode count and every degree cutoff, the energy bound is attained on a finite regular graph, and the free-energy gap exceeds every smaller prefactor at some finite positive inverse temperature.

**Theorem 1.2 (The high-degree constants are sharp).**

$$\mathit{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/GaussianHighDegreeSharpness.result` (`✓ std3`). ∎

*Resolves.* `Problems/negari-2610-01860-high-degree-constant-sharpness` (proved) by `D5/S3/Quantum/Fermionic/GaussianHighDegreeSharpness.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"negari-2610-01860-high-degree-constant-sharpness","declaration_gid":"D5/S3/Quantum/Fermionic/GaussianHighDegreeSharpness.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Amir-Reza Negari; Farzin Salek; Zoltán Zimborás; Aram Harrow; Patrick Hayden; Jens Eisert (2026). *Approximation theorems for fermionic Gaussian states*. DOI: [10.48550/arXiv.2610.01860](https://doi.org/10.48550/arXiv.2610.01860). URL: <https://arxiv.org/abs/2610.01860v1>.

*Commentary.*

Choose a power-of-two conference order s with 2m(s−1) at least the prescribed cutoff and take the Cartesian product of 2m complete graphs on s vertices. Its normalized quadratic interactions have product energy zero and physical ground energy −sqrt(2m/D). The entropy budget of the Gibbs product is at most log of the Fock dimension; choosing a sufficiently large finite positive beta gives the strict free-gap inequality.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/GaussianHighDegreeSharpness.claim`
- Truth anchor: `D5/S3/Quantum/Fermionic/GaussianHighDegreeSharpness.result`
- Dependency: [D5/S3/Quantum/Fermionic/CoordinateAverage](CoordinateAverage.md)
- Dependency: [D5/S3/Quantum/Fermionic/FlatCliffordGround](FlatCliffordGround.md)
- Dependency: [D5/S3/Quantum/Fermionic/GibbsProductGap](GibbsProductGap.md)
