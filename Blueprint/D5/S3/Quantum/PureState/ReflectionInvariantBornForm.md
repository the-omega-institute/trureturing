# The Born form from one reflection

## Abstract

A normalized quadratic reading invariant under the reflection fixing one unit vector is its Born weight.

**Theorem 1.1 (A reflection-invariant normalized reading is the Born weight).**

$$\forall E \in Type,\; [NormedAddCommGroup\left(E\right)] [InnerProductSpace\left(\mathbb{C}, E\right)] \forall phi \in E,\; \left\lVert phi \right\rVert = 1 \Rightarrow \left(\forall g \in E \to \mathbb{R},\; \left(\forall c \in \mathbb{C},\; \forall psi \in E,\; g\left(smul\left(c, psi\right)\right) = \left\lVert c \right\rVert^{2} \cdot g\left(psi\right)\right) \Rightarrow \left(\left(\forall z \in \mathbb{C},\; \forall w \in E,\; \langle phi, w \rangle_{\mathbb{C}} = 0 \Rightarrow g\left(smul\left(z, phi\right) + w\right) + g\left(smul\left(z, phi\right) - w\right) = 2 \cdot g\left(smul\left(z, phi\right)\right) + 2 \cdot g\left(w\right)\right) \Rightarrow \left(\left(\forall psi \in E,\; \left\lVert psi \right\rVert = 1 \Rightarrow g\left(smul\left(2 \cdot \langle phi, psi \rangle_{\mathbb{C}}, phi\right) - psi\right) = g\left(psi\right)\right) \Rightarrow \left(g\left(phi\right) = 1 \Rightarrow \left(\left(\forall psi \in E,\; \left\lVert psi \right\rVert = 1 \Rightarrow \left(\langle phi, psi \rangle_{\mathbb{C}} = 0 \Rightarrow g\left(psi\right) = 0\right)\right) \Rightarrow \left(\forall psi \in E,\; g\left(psi\right) = \left\lVert \langle phi, psi \rangle_{\mathbb{C}} \right\rVert^{2}\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/ReflectionInvariantBornForm.eq_norm_inner_sq_of_reflection_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be a complex inner product space, φ a unit vector of E and g a real function on E. Assume five conditions on g: g(cψ) = |c|² g(ψ) for every complex scalar c and every ψ; the parallelogram law g(zφ + w) + g(zφ − w) = 2 g(zφ) + 2 g(w) for every complex z and every w orthogonal to φ; g is unchanged by the reflection ψ ↦ 2⟨φ, ψ⟩φ − ψ, which fixes φ and reverses its orthogonal complement, at every unit vector ψ; g(φ) = 1; and g vanishes at every unit vector orthogonal to φ. Then g(ψ) = |⟨φ, ψ⟩|² for every ψ in E. The statement concerns one unit vector φ; applied to each φ in turn, it gives the same conclusion for a reading f(ψ, φ) under the five conditions at every unit vector φ. Neither finite dimension nor completeness is assumed.

Proof: homogeneity extends the reflection invariance from unit vectors to all vectors, since the reflection commutes with complex scalars. Write ψ = zφ + w with z = ⟨φ, ψ⟩ and w orthogonal to φ. Rescaling w to a unit vector and using homogeneity gives g(w) = 0, and g(zφ) = |z|² g(φ) = |z|². The reflection sends zφ + w to zφ − w, so invariance makes the two terms on the left of the parallelogram law for zφ and w equal; the law then gives 2 g(ψ) = 2|z|² + 0.

A Hermitian quadratic form ψ ↦ Re⟨ψ, Tψ⟩ with T complex linear satisfies homogeneity and the parallelogram law for all pairs, so the theorem applies to such readings; any unitary covariance that includes the reflection fixing φ supplies the invariance condition. The parallelogram law cannot be dropped: g(ψ) = |⟨φ, ψ⟩|⁴ / ‖ψ‖² for ψ ≠ 0, with g(0) = 0, scales by |c|², is invariant under the reflection, equals 1 at φ and vanishes on unit vectors orthogonal to φ, yet at ψ = (φ + χ)/√2 with χ a unit vector orthogonal to φ it equals 1/4 while |⟨φ, ψ⟩|² = 1/2. Homogeneity under complex scalars cannot be weakened to real scalars: g(ψ) = (Re⟨φ, ψ⟩)² satisfies all other conditions and homogeneity for real c, yet vanishes at ψ = iφ, where |⟨φ, ψ⟩|² = 1.

The result is an elementary argument; no published source stating it in this form is known, and nothing is claimed as new.

## References

- Truth anchor: `D5/S3/Quantum/PureState/ReflectionInvariantBornForm.eq_norm_inner_sq_of_reflection_invariant`
