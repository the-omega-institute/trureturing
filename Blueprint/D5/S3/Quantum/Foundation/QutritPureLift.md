# Unique pure lifts across a qutrit face

## Abstract

Original pure lifts are unique at unit support across an actual qutrit face.

**Theorem 1.1 (Injectivity on the support-one pure slice).**

$$\forall V \in Type,\; [\mathrm{NormedAddCommGroup}\left(V\right)] [\mathrm{NormedSpace}\left(\mathbb{R}, V\right)] [\mathrm{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \mathrm{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \mathrm{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \forall g \in \mathrm{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \forall F \in \mathrm{Face}\left(C\right),\; \forall e \in \mathrm{LinearEquiv}\left(\mathbb{R}, \mathrm{span}\left(\mathbb{R}, F\right), \mathrm{HermitianMat}\left(\mathrm{Fin}\left(3\right), \mathbb{C}\right)\right),\; \left(\left(\forall x \in V,\; \left(x \in C \land x \ne 0\right) \Rightarrow 0 < u\left(x\right)\right) \land \left(\left(\forall x \in V,\; x \in C \Rightarrow 0 \le g\left(x\right)\right) \land \left(\left(\forall x \in V,\; x \in F \Rightarrow g\left(x\right) = 0\right) \land \left(\mathrm{wholePairBalls}\left(C, u\right) \land \left(\left(\forall x \in \mathrm{span}\left(\mathbb{R}, F\right),\; \mathrm{val}\left(x\right) \in F \Leftrightarrow 0 \le e\left(x\right)\right) \land \left(\forall x \in \mathrm{span}\left(\mathbb{R}, F\right),\; \mathrm{trace}\left(e\left(x\right)\right) = u\left(\mathrm{val}\left(x\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \mathrm{InjOn}\left(\mathrm{mkQ}\left(\mathrm{span}\left(\mathbb{R}, F\right)\right), \mathrm{setOf}\left(r\mapsto \exists p \in \mathrm{pure}\left(C, u\right),\; \exists a \in \mathbb{R},\; 0 < a \land \left(r = \mathrm{smul}\left(a, \mathrm{val}\left(p\right)\right) \land g\left(r\right) = 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/QutritPureLift.unique_original_pure_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg; Leonardo A. Lessa; Rodolfo Soldati (2026). *Finite density states and strong subadditivity in Physlib*. URL: <https://github.com/leanprover-community/physlib/blob/2725b6f621901d4cd330869e9b77105045c1582e/QuantumInfo/Entropy/SSA.lean>.

*Commentary.*

Let C be a real pointed cone in a finite-dimensional normed space V, and let u be a real-linear unit strictly positive on the nonzero cone elements. Purity means being an extreme point of the whole u = 1 base. For each pair of distinct original pure states, assume its actual pair face has a whole affine unit-ball chart. Let F be an actual cone face. Its real span is identified by one real-linear equivalence with all complex Hermitian three-by-three matrices. The equivalence carries F onto the positive semidefinite cone and carries the original unit to the real trace. Thus the span has nine real dimensions. Let g be real-linear, nonnegative on C and zero on F. The quotient by this exact span is injective on positive multiples of original pure states with g = 1.

Equal quotient values put the signed difference of the lifts in the span of F. The signed spectral sum from CartesianVariance.hermitian_spectral_sum pulls back to three distinct original pure points of F with real coefficients, including any zero eigenvalues. When all coefficients have one weak sign, extremality in the original normalized base makes the lifts positively proportional, and their equal support values make the proportionality one.

For mixed signs, one sign has a single nonzero term. Moving the terms to opposite sides gives a positive sum of an outside pure lift and that spectral atom on one side. Faciality puts an opposite-sign spectral atom in their actual pair ball. The two distinct spectral atoms are zeros of the same nonnegative g. The affine unit-ball formula for a support vanishing at a sphere point forces g to vanish on the whole ball if it also vanishes at a second sphere point. This contradicts the outside lift having support value one.

This is the unique-lift step of the short carrier-15 quotient proof (XIII160.34), supplied by the independent convex-geometry review. The theorem takes the actual trace-normalized qutrit face as an input. The projected-plane existence and intersection-dimension steps belong to the surrounding paper argument. The carrier-16 and carrier-17 results are outside this theorem's scope.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/QutritPureLift.unique_original_pure_lift`
- Dependency: [D5/S3/Quantum/Foundation/HermitianExclusionBall](HermitianExclusionBall.md)
- Dependency: [D5/S3/Quantum/Foundation/HitSectionGeneration](HitSectionGeneration.md)
- Dependency: [D5/S3/Quantum/Foundation/WholePairBallConfirmation](WholePairBallConfirmation.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Matrix/CartesianVariance.md)
