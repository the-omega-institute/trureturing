# Riemann Stabilizers and Free Zero Orbits

## Abstract

Critical-line localization fixes every nontrivial zero under conjugate reflection, while a nonreal off-line zero retains a free four-point symmetry orbit.

**Theorem 1.1 (Localization enlarges stabilizers without restoring symmetry).**

$$\begin{gathered}(\operatorname{RiemannHypothesis}) \Rightarrow (\forall \rho\in \mathbb{C}, (\operatorname{IsNontrivialZero}\left(\rho\right)) \Rightarrow (\operatorname{reflect}\left(\rho\right) = \rho)) \land\\{}\forall \rho\in \mathbb{C}, (\operatorname{IsNontrivialZero}\left(\rho\right)) \Rightarrow (\operatorname{let} \operatorname{orbit}\left(\rho\right): = \left\{\rho, \operatorname{conj}\left(\rho\right), 1-\rho, \operatorname{reflect}\left(\rho\right)\right\};\\{}(((\forall z\in \mathbb{C}, (z \in \operatorname{orbit}\left(\rho\right)) \Rightarrow (\operatorname{IsNontrivialZero}\left(z\right))) \land (\forall z\in \mathbb{C}, (z \in \operatorname{orbit}\left(\rho\right) \Leftrightarrow 1-z \in \operatorname{orbit}\left(\rho\right)))) \land (\forall z\in \mathbb{C}, (z \in \operatorname{orbit}\left(\rho\right) \Leftrightarrow \operatorname{conj}\left(z\right) \in \operatorname{orbit}\left(\rho\right)))) \land ((\operatorname{Im}(\rho) \neq 0) \Rightarrow ((\Re(\rho) \neq \frac{1}{2}) \Rightarrow (\operatorname{card}\left(\operatorname{orbit}\left(\rho\right)\right) = 4)))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/RiemannStabilizerFreeOrbit.riemann_stabilizer_free_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first public conjunct applies the pinned Riemann-hypothesis location theorem to every classical nontrivial zero and identifies the source's J action with conjugate reflection.

The second public conjunct constructs the source's literal Klein orbit from conjugation, functional reflection, and conjugate reflection. The pinned zeta covariance and reflection theorems keep every orbit member inside the nontrivial zero set, and the two generators preserve the orbit as a set.

Nonzero imaginary part and displacement from one half make the four orbit members pairwise distinct. No converse from a free orbit to the negation of the Riemann hypothesis and no real-axis nonvanishing statement is asserted.

## References

- Truth anchor: `D5/S3/Zeros/Symmetry/RiemannStabilizerFreeOrbit.riemann_stabilizer_free_orbit`
- Dependency: [D5/S3/Zeros/Symmetry/ZetaConjugationCovariance](ZetaConjugationCovariance.md)
