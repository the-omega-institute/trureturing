# Reflection positivity and Wilson loops on finite lattices

## Abstract

Finite Wilson reflection positivity and planar Wilson loops in the two-element gauge theory.

For a real kernel K on two copies of a finite set X, the reflection pairing of f and g is Σₓ Σᵧ K(x,y) overline(f(y)) g(x). Reflection exchanges the copies and conjugates the value of the first observable.

For every real weight w on X, the pairing of f with itself for K(x,y) = w(x)w(y) equals the squared norm of Σₓ w(x) f(x), regarded as a complex number.

**Theorem 1.1 (Powers of the interaction).**

Lean statement: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.factorized_interaction_pow_rp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.factorized_interaction_pow_rp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finitely many complex features Aᵢ and real coefficients cᵢ ≥ 0, put V(x,y) = Σᵢ cᵢ Re(Aᵢ(x) overline(Aᵢ(y))). For every natural n, the pairing of f with itself for w(x)w(y)V(x,y)ⁿ is real and nonnegative. Real and imaginary parts give real features and the product expansion gives the features for each power.

**Theorem 1.2 (Exponential reflection positivity).**

Lean statement: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.exponential_boltzmann_reflection_positivity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.exponential_boltzmann_reflection_positivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arthur Jaffe and Bas Janssens (2017). *Reflection positive doubles*. DOI: [10.1016/j.jfa.2016.11.014](https://doi.org/10.1016/j.jfa.2016.11.014). URL: <https://arxiv.org/abs/1607.07126>.

*Commentary.*

For every real half action S and β ≥ 0, the diagonal pairing with weight w(x)w(y) exp(β(S(x) + S(y) + V(x,y))) is real and nonnegative. Multiplying the product weights by exp(β S) incorporates both half actions. The exponential series then gives a convergent sum of the nonnegative power pairings.

**Theorem 1.3 (The exact coupling range).**

Lean statement: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.exponential_boltzmann_rp_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.exponential_boltzmann_rp_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At fixed β, the diagonal pairing is real and nonnegative for all finite half spaces, finite feature families with nonnegative coefficients, real weights and half actions, and complex observables, exactly when β ≥ 0. On two points take f(false) = −1 and f(true) = 1. Use f as the single feature with coefficient one, unit weights and zero half action. The pairing is the real number 4 sinh β, which is strictly negative for every β < 0.

The Wilson lattice has two open time halves of length T. Each time slice is the three-dimensional torus of side L, with T and L positive. Local transformations send an oriented link U from v to w to g(v) U g(w)⁻¹. Each plaquette contributes the real trace of the represented holonomy. The full pairing divides the weighted counting sum by the strictly positive full Wilson partition function Z. After fixing the crossing links, the half-configuration sum is multiplied by |G|^(L³)/Z.

Local transformations conjugate each plaquette holonomy at its starting site. Cyclicity preserves the trace, and summing the individual real traces preserves the Wilson action on spatial, internal time-space and crossing plaquettes. Orient each crossing link from the negative to the positive half. The gauge that is one on the negative half and U₀(x) above x on the positive half sends U₀(x) to one and applies a bijection to the half configurations.

**Theorem 1.4 (Counting in temporal gauge).**

Lean statement: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.temporal_gauge_fixing`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.temporal_gauge_fixing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any gauge-invariant summand with values in an additive commutative monoid, the full sum equals |G|^(L³) times the sum with unit crossing links. The bijection of half configurations applies separately for each crossing field.

When crossing links are one, the crossing plaquette holonomy is U₊ U₋⁻¹ for the paired spatial links at the cut. Its real trace is the sum over row and column indices of Re(rep(U₊)ₐᵦ overline(rep(U₋)ₐᵦ)).

**Theorem 1.5 (Reflection positivity of the four-dimensional Wilson action).**

Lean statement: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.lattice_ym_4d_reflection_positivity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.lattice_ym_4d_reflection_positivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arthur Jaffe and Bas Janssens (2017). *Reflection positive doubles*. DOI: [10.1016/j.jfa.2016.11.014](https://doi.org/10.1016/j.jfa.2016.11.014). URL: <https://arxiv.org/abs/1607.07126>.

*Commentary.*

For a finite gauge group, a unitary representation on a finite complex coordinate space, β ≥ 0, and a gauge-invariant positive-half observable F, the normalized reflection pairing of F with itself is real and nonnegative. In the gauge with unit crossing links, the crossing plaquette contributions are precisely the interaction features of the exponential theorem.

**Theorem 1.6 (Cauchy–Schwarz for the physical pairing).**

Lean statement: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.lattice_ym_4d_cauchy_schwarz`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.lattice_ym_4d_cauchy_schwarz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For β ≥ 0 and two gauge-invariant positive-half observables F and H, the squared norm of their reflection pairing is bounded by the product of the real diagonal pairings of F and H.

For every real β and s equal to 1 or −1, exp(βs) = cosh(β)(1 + s tanh(β)).

For every real β, the finite normalized Wilson expectation equals the sum of tanh(β)^|S| over surfaces with the prescribed boundary divided by the sum over closed surfaces. The parity character sum eliminates all other surfaces.

**Theorem 1.7 (Exact Wilson-loop area law in two dimensions).**

Lean statement: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_loop_2d_exact_area_law`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_loop_2d_exact_area_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Franz J. Wegner (2014). *Duality in generalized Ising models*. DOI: [10.48550/arXiv.1411.5815](https://doi.org/10.48550/arXiv.1411.5815). URL: <https://arxiv.org/abs/1411.5815v1>.

*Commentary.*

An R by T rectangular loop in an open M by N lattice has one plaquette filling. For every real β the expectation equals tanh(β)^(R T). For β > 0 the string tension σ = −log(tanh(β)) is positive and the same expectation equals exp(−σ R T).

**Theorem 1.8 (Area of a four-dimensional plaquette filling).**

Lean statement: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.hypercubic_4d_minimal_surface_area_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.hypercubic_4d_minimal_surface_area_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every plaquette filling of an R by T planar rectangle in an open four-dimensional box contains at least R T plaquettes. Summing the boundary along an in-plane link ray, over all transverse coordinates, forces an odd number of in-plane plaquettes above each elementary square of the rectangle.

**Theorem 1.9 (Four-dimensional strong-coupling bound).**

Lean statement: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.strong_coupling_4d_minimal_surface_expansion_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.strong_coupling_4d_minimal_surface_expansion_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an open four-dimensional box and an R by T planar rectangle in it. For β ≥ 0 the Wilson expectation is between zero and the sum of tanh(β)^|M| over inclusion-minimal fillings M in that same box. Every exponent |M| is at least R T. Choosing a minimal subfilling and its disjoint closed complement determines the original filling. The closed-surface sum cancels.

## References

- Truth anchor: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.exponential_boltzmann_reflection_positivity`
- Truth anchor: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.exponential_boltzmann_rp_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.factorized_interaction_pow_rp`
- Truth anchor: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.hypercubic_4d_minimal_surface_area_bound`
- Truth anchor: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.lattice_ym_4d_cauchy_schwarz`
- Truth anchor: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.lattice_ym_4d_reflection_positivity`
- Truth anchor: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.strong_coupling_4d_minimal_surface_expansion_bound`
- Truth anchor: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.temporal_gauge_fixing`
- Truth anchor: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_loop_2d_exact_area_law`
- Dependency: [D5/S3/StatisticalMechanics/ZTwoHighTemperatureExpansion](../../StatisticalMechanics/ZTwoHighTemperatureExpansion.md)
