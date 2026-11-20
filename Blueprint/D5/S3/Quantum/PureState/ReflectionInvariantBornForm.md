# The Born form from one reflection

## Abstract

A normalized quadratic reading invariant under one reflection fixing the reference vector is the Born weight.

**Theorem 1.1 (A reflection-invariant normalized reading is the Born weight).**

$$\forall E \in Type,\; [NormedAddCommGroup\left(E\right)] [InnerProductSpace\left(\mathbb{C}, E\right)] \forall f \in E \to \left(E \to \mathbb{R}\right),\; \left(\forall phi \in E,\; \left\lVert phi \right\rVert = 1 \Rightarrow \left(\forall c \in \mathbb{C},\; \forall psi \in E,\; f\left(smul\left(c, psi\right), phi\right) = \left\lVert c \right\rVert^{2} \cdot f\left(psi, phi\right)\right)\right) \Rightarrow \left(\left(\forall phi \in E,\; \left\lVert phi \right\rVert = 1 \Rightarrow \left(\forall psi \in E, chi \in E,\; f\left(psi + chi, phi\right) + f\left(psi - chi, phi\right) = 2 \cdot f\left(psi, phi\right) + 2 \cdot f\left(chi, phi\right)\right)\right) \Rightarrow \left(\left(\forall phi \in E, psi \in E,\; \left\lVert phi \right\rVert = 1 \Rightarrow f\left(smul\left(2 \cdot \langle phi, psi \rangle_{\mathbb{C}}, phi\right) - psi, phi\right) = f\left(psi, phi\right)\right) \Rightarrow \left(\left(\forall phi \in E,\; \left\lVert phi \right\rVert = 1 \Rightarrow f\left(phi, phi\right) = 1\right) \Rightarrow \left(\left(\forall phi \in E, psi \in E,\; \left\lVert phi \right\rVert = 1 \Rightarrow \left(\left\lVert psi \right\rVert = 1 \Rightarrow \left(\langle phi, psi \rangle_{\mathbb{C}} = 0 \Rightarrow f\left(psi, phi\right) = 0\right)\right)\right) \Rightarrow \left(\forall phi \in E, psi \in E,\; \left\lVert phi \right\rVert = 1 \Rightarrow f\left(psi, phi\right) = \left\lVert \langle phi, psi \rangle_{\mathbb{C}} \right\rVert^{2}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/ReflectionInvariantBornForm.eq_norm_inner_sq_of_reflection_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be a complex inner product space and f(ψ, φ) a real number for each pair of vectors. For every unit vector φ assume five conditions on the map ψ ↦ f(ψ, φ): it scales by |c|² when ψ is multiplied by a complex scalar c; it satisfies the parallelogram law f(ψ + χ, φ) + f(ψ − χ, φ) = 2 f(ψ, φ) + 2 f(χ, φ); it is unchanged by the reflection ψ ↦ 2⟨φ, ψ⟩φ − ψ, which fixes φ and reverses its orthogonal complement; it equals 1 at ψ = φ; and it vanishes at every unit vector ψ orthogonal to φ. Then f(ψ, φ) = |⟨φ, ψ⟩|² for every vector ψ and every unit vector φ. No condition relates the readings for different φ, and neither finite dimension nor completeness is assumed.

Proof: write ψ = zφ + w with z = ⟨φ, ψ⟩ and w orthogonal to φ. Rescaling w to a unit vector and using the scaling condition gives f(w, φ) = 0, and f(zφ, φ) = |z|² f(φ, φ) = |z|². The reflection sends zφ + w to zφ − w, so invariance makes the two terms on the left of the parallelogram law for zφ and w equal; the law then gives 2 f(ψ, φ) = 2|z|² + 0.

A Hermitian quadratic form ψ ↦ Re⟨ψ, Tψ⟩ with T complex linear satisfies the scaling condition and the parallelogram law, so the theorem applies to such readings; any unitary covariance that includes the reflection fixing φ supplies the invariance condition. The parallelogram law cannot be dropped: f(ψ, φ) = |⟨φ, ψ⟩|⁴ / ‖ψ‖² scales by |c|², is invariant under the reflection, equals 1 at φ and vanishes on orthogonal unit vectors, yet at ψ = (φ + χ)/√2 with χ a unit vector orthogonal to φ it equals 1/4 while |⟨φ, ψ⟩|² = 1/2. Homogeneity under complex scalars cannot be weakened to real scalars: f(ψ, φ) = (Re⟨φ, ψ⟩)² satisfies all other conditions and the scaling condition for real c, yet vanishes at ψ = iφ, where |⟨φ, ψ⟩|² = 1.

The result is an elementary argument; no published source stating it in this form is known, and nothing is claimed as new.

## References

- Truth anchor: `D5/S3/Quantum/PureState/ReflectionInvariantBornForm.eq_norm_inner_sq_of_reflection_invariant`
