# Failure of the factored Wigner deficit

## Abstract

The Wigner tensor deficit cannot factor as the equatorial state's Wigner distance times a function of the other state.

**Definition 1.1 (The tensor deficit).**

$$\forall rho \in QubitMatrix,\; \forall sigma \in QubitMatrix,\; \operatorname{deficit}\left(rho, sigma\right) = (1 + \operatorname{COne}\left(rho\right)) \cdot (1 + \operatorname{COne}\left(sigma\right)) - 1 - \operatorname{CTwo}\left(\operatorname{kronecker}\left(rho, sigma\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/QubitWignerDeficitFactorRefutation.deficit` (`✓ std3`).

*Citation.* Soumyojyoti Dutta; Tushar (2026). *A Phase-Space Geometric Measure of Magic in Qubit Systems*. DOI: [10.48550/arXiv.2603.20792](https://doi.org/10.48550/arXiv.2603.20792). URL: <https://arxiv.org/abs/2603.20792v3>.

*Commentary.*

The deficit is (1+COne(rho))(1+COne(sigma))-1-CTwo(rho tensor sigma). The one-qubit and two-qubit distances use the Wootters frame and the convex hull of actual stabilizer Wigner vectors.

**Definition 1.2 (The factorization clause of Conjecture 5.5).**

$$(claim) \Leftrightarrow (\exists f \in QubitMatrix \to \mathbb{R},\; \forall rho \in QubitMatrix,\; \forall sigma \in QubitMatrix,\; (\operatorname{IsDensity}\left(rho\right)) \Rightarrow ((\operatorname{bloch}\left(rho, Z\right) = 0) \Rightarrow ((0 < \operatorname{COne}\left(rho\right)) \Rightarrow ((\operatorname{IsDensity}\left(sigma\right)) \Rightarrow ((0 < \operatorname{bloch}\left(sigma, X\right) \cdot \operatorname{bloch}\left(sigma, Y\right) \cdot \operatorname{bloch}\left(sigma, Z\right)) \Rightarrow (\operatorname{deficit}\left(rho, sigma\right) = \operatorname{COne}\left(rho\right) \cdot \operatorname{f}\left(sigma\right)))))))$$

*Formalization.* `D5/S3/Quantum/Magic/QubitWignerDeficitFactorRefutation.claim` (`✓ std3`).

*Citation.* Soumyojyoti Dutta; Tushar (2026). *A Phase-Space Geometric Measure of Magic in Qubit Systems*. DOI: [10.48550/arXiv.2603.20792](https://doi.org/10.48550/arXiv.2603.20792). URL: <https://arxiv.org/abs/2603.20792v3>.

*Commentary.*

Conjecture 5.5 asserts that the deficit factors as COne(rho) times a universal function of sigma whenever rho is equatorial magic and sigma has positive Bloch product. Equatorial magic means IsDensity(rho), bloch(rho,Z)=0, and COne(rho)>0. IsDensity means positive semidefinite with trace one. The additional conjectured conditions on the function, including nonnegativity and dependence on absolute Pauli coordinates, imply this factorization clause.

**Theorem 1.3 (The factored deficit is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QubitWignerDeficitFactorRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/dutta-tushar-2026-wigner-distance-factored-deficit` (refuted) by `D5/S3/Quantum/Magic/QubitWignerDeficitFactorRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dutta-tushar-2026-wigner-distance-factored-deficit","declaration_gid":"D5/S3/Quantum/Magic/QubitWignerDeficitFactorRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Take the pure Bloch vectors rhoA=(3/5,4/5,0), rhoB=(5/13,12/13,0), and sigma=(1/9,4/9,8/9). Their single-qubit distances are 1/5, 2/13, and 2/9. The joint distances are 7/18 and 79/234. A sign functional bounded by 1/2 on all sixty two-qubit stabilizer Wigner vectors proves the lower bounds, and five-stabilizer mixtures attain them. Four states in each mixture are Pauli spectral products, and the fifth is the common positive eigenstate of XY and YZ. Thus factorization would give both f(sigma)=7/18 and f(sigma)=17/36, which are unequal. Both equatorial states are pure, so the same contradiction holds if the equatorial input is restricted to pure states.

## References

- Truth anchor: `D5/S3/Quantum/Magic/QubitWignerDeficitFactorRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Magic/QubitWignerDeficitFactorRefutation.deficit`
- Truth anchor: `D5/S3/Quantum/Magic/QubitWignerDeficitFactorRefutation.result`
- Dependency: [D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules](QubitWignerDistanceTensorRules.md)
