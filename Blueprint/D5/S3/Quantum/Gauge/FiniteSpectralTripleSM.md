# The finite real spectral triple of the Standard Model

## Abstract

A finite real matrix model for one generation of Standard Model fermions.

**Theorem 1.1 (The KO-dimension-six identities and both order conditions).**

Lean statement: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.finite_spectral_triple_ko6`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.finite_spectral_triple_ko6` (`✓ std3`). ∎

*Citation.* Ali H. Chamseddine and Alain Connes (2008). *Why the Standard Model*. DOI: [10.48550/arXiv.0706.3688](https://doi.org/10.48550/arXiv.0706.3688). URL: <https://arxiv.org/abs/0706.3688>.

*Commentary.*

On the 32 complex fermion coordinates, the faithful action of the real algebra preserves the grading. Charge conjugation is an involution, fixes the Dirac operator under conjugation, and negates the grading under conjugation. The grading is self-adjoint and squares to one. The Dirac operator is self-adjoint and anticommutes with the grading. The left and opposite actions commute, and every Dirac commutator for the left action commutes with every opposite action, for arbitrary complex Yukawa and Majorana parameters. The Majorana entry joins the right-handed neutrino to its conjugate. Their left and opposite scalar actions coincide while their grading signs differ, so this representation fails the stronger orientability axiom on that pair. The result concerns the finite real even spectral triple identities.

**Theorem 1.2 (The one-generation dimension).**

Lean statement: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.fermion_dimension`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.fermion_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complex coordinate space has dimension 32. Each of the four chirality and charge sectors contains a lepton doublet and a weak doublet with three colors.

**Theorem 1.3 (Antiunitarity).**

Lean statement: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.realStructure_antiunitary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.realStructure_antiunitary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real structure conjugates a complex affine combination and conjugates the coordinate inner product. The particle and antiparticle permutation is bijective.

**Theorem 1.4 (The weak special unitary group).**

Lean statement: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.quatMatrix_specialUnitary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.quatMatrix_specialUnitary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two-by-two complex quaternion image of the norm-one quaternions is exactly the unitary matrices of determinant one.

**Theorem 1.5 (The normalized Hilbert–Schmidt inner product).**

Lean statement: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.quatMatrix_hs_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.quatMatrix_hs_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Half the real trace of the adjoint of the first quaternion matrix times the second is the real quaternion inner product.

**Theorem 1.6 (Independent weak directions).**

Lean statement: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.weak_generators_independent`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.weak_generators_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three imaginary quaternion units have identity Gram matrix. The three-anchor criterion then gives real linear independence.

**Theorem 1.7 (The unimodular character).**

Lean statement: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.rep_det`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.rep_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a unitary algebra triple the determinant of the represented unitary is the fourth power of the scalar times the color determinant.

**Theorem 1.8 (The determinant of the gauge lift).**

Lean statement: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.gaugeLift_det`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.gaugeLift_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On every unitary algebra triple the lift has determinant one, since its two determinant factors are complex conjugates with product one.

**Theorem 1.9 (The reduced character restriction).**

Lean statement: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.unimodularity_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.unimodularity_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unitary with scalar and quaternion entries one and color matrix diag(i, 1, 1) has both determinants one and reduced character i.

**Theorem 1.10 (Parametrization of reduced unitaries).**

Lean statement: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.reduced_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.reduced_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every unitary triple with scalar times color determinant one comes from the cover. Choose a cube root t of the scalar and multiply the original color matrix by t. The root is unitary and the new color matrix has determinant one.

**Theorem 1.11 (The phases on the cover).**

Lean statement: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.lift_particle_phase`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.lift_particle_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cover uses scalar t cubed and color matrix t inverse times g. The particle phases for the neutrino, electron, up quark, down quark, lepton doublet and quark doublet have exponents 0, −6, 4, −2, −3 and 1, respectively. The weak quaternion matrix acts on the left doublets and the conjugate of g acts on quark color.

**Theorem 1.12 (All-left-handed hypercharges).**

Lean statement: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.hypercharge_table`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.hypercharge_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The all-left-handed charges are the phase exponents divided by six, with the signs reversed for the conjugates of right-handed particles. In the order Q, u conjugate, d conjugate, L, e conjugate and neutrino conjugate the charges are 1/6, −2/3, 1/3, −1/2, 1 and 0.

**Theorem 1.13 (Four local chiral anomaly coefficients).**

Lean statement: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.anomaly_cancel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.anomaly_cancel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mixed color, mixed weak, mixed gravitational and cubic abelian coefficients are zero. The latter two sum over the sixteen all-left-handed coordinates.

**Theorem 1.14 (The central equations for the kernel).**

Lean statement: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.cover_kernel_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.cover_kernel_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a unitary scalar t, the gauge lift of the cover element is the identity exactly when t to the sixth is one, the weak matrix is t cubed times the identity, and the color matrix is t to the fourth times the identity.

**Theorem 1.15 (Self-adjoint inner fluctuations).**

Lean statement: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.inner_fluctuation_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.inner_fluctuation_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real span of represented elementary one-forms has self-adjoint part given by a single quaternion multiplying the lower particle Yukawa block, with its adjoint in the upper block.

**Theorem 1.16 (Uniqueness of the Higgs parameter).**

Lean statement: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.higgsForm_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.higgsForm_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero Yukawa coupling determines a full column of the quaternion matrix. Either column determines all four real quaternion coordinates.

**Theorem 1.17 (The quadratic Dirac moment).**

Lean statement: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.trace_dirac_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.trace_dirac_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Higgs norm square x, the squared Dirac trace is four times x times the weighted sum of squared Yukawa norms plus twice the squared Majorana norm.

**Theorem 1.18 (The quartic Dirac moment).**

Lean statement: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.trace_dirac_four`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.trace_dirac_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quartic trace is four times x squared times the weighted sum of fourth powers of the Yukawa norms, plus eight times x times the squared Majorana and neutrino Yukawa norms, plus twice the fourth power of the Majorana norm.

**Theorem 1.19 (The radial spectral-action potential).**

Lean statement: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.potential_eq_spectral_action`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.potential_eq_spectral_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quartic Dirac trace weighted by a minus the quadratic trace weighted by b equals the radial potential evaluated at the squared Higgs norm.

**Theorem 1.20 (The nonzero vacuum criterion).**

Lean statement: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.higgs_minimum_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.higgs_minimum_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive quartic weight and positive fourth Yukawa moment, the potential on nonnegative norm squares has a positive minimizer exactly when b times the second Yukawa moment exceeds twice a times the squared Majorana norm times the squared neutrino Yukawa norm.

**Theorem 1.21 (The vacuum with zero Majorana mass).**

Lean statement: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.higgs_minimum_massless`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.higgs_minimum_massless` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When both action coefficients are positive and any Yukawa coupling is nonzero, zero Majorana mass gives a positive minimizing Higgs norm square.

## References

- Truth anchor: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.anomaly_cancel`
- Truth anchor: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.cover_kernel_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.fermion_dimension`
- Truth anchor: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.finite_spectral_triple_ko6`
- Truth anchor: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.gaugeLift_det`
- Truth anchor: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.higgsForm_injective`
- Truth anchor: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.higgs_minimum_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.higgs_minimum_massless`
- Truth anchor: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.hypercharge_table`
- Truth anchor: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.inner_fluctuation_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.lift_particle_phase`
- Truth anchor: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.potential_eq_spectral_action`
- Truth anchor: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.quatMatrix_hs_inner`
- Truth anchor: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.quatMatrix_specialUnitary`
- Truth anchor: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.realStructure_antiunitary`
- Truth anchor: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.reduced_cover`
- Truth anchor: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.rep_det`
- Truth anchor: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.trace_dirac_four`
- Truth anchor: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.trace_dirac_sq`
- Truth anchor: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.unimodularity_witness`
- Truth anchor: `D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.weak_generators_independent`
- Dependency: [D5/S3/Quantum/AURICOmega/QuaternionComparisonModel](../AURICOmega/QuaternionComparisonModel.md)
- Dependency: [D5/S3/QuantumContext/ThreeAnchorGram](../../QuantumContext/ThreeAnchorGram.md)
