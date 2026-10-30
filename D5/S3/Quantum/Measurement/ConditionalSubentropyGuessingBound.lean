/- GID: D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Conditional subentropy is at most the guessing min-entropy of a finite c-q state. -/

/-
proof_shape: result: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#18776; Proved).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20025
The source simplex point is PositiveSimplexGeometryAndMixing.chart and its η is
Real.negMulLog; the existing definitions are used without redeclaration.
The public simplexCoords retains the source domain; the private simplex measure uses
RenewalMinorantMaximalityRefutation.Ak through the consumed simplexCoords_eq_Ak bridge.
The private adapters identify the simplex integral with determinant-integral subentropy
on positive semidefinite trace-one matrices, including repeated and zero eigenvalues.
The frozen conditional guessing bound then applies to arbitrary positive blocks.
There is no finite computation refuting the claim; utility is none.
Direct frozen dependencies of result (declaration statement_id, not a module pin):
D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing.chart sha256:f12940e4dca0ea47ade5588aa86134efde1ee9d876cebd7029a63dd54cf83706
D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5
D5.S3.Quantum.Information.OrthogonalRecordEntropy.mixtureState sha256:3fbfa607a1bbd397ac41fc4b8f5dfd95bd74c209e2fdf8fc34b226f210886c59
D5.S3.Quantum.Information.OrthogonalRecordEntropy.recordState sha256:82f2241204cdd35e8336a4202d244cee9e882a89e93959e291896658ab58c93a
D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.positiveBlockDiagonal sha256:a6348a7a914aad14d232dc4b4361d13353848b8bc54c1eb04c2019f6d00589d8
D5.S3.Quantum.Subentropy.Basic.matrixSubentropy sha256:1c5fdaf526e28e3e61827e243def4b593a85eee0439ad39231d25b0d4934f852
D5.S3.Quantum.Subentropy.Basic.subentropy sha256:d8be09c589dc1b6bbc2eb39baf322dc4cb031b9e00180360783a4d68a987841b
D5.S3.Quantum.Subentropy.Basic.subentropyKernel sha256:3da2f397e20d37e2e5faa36585310fb90c3e711fdef2c50b954771fb59fc526a
D5.S3.Quantum.Subentropy.ClassicalQuantumGram.conditionalSubentropy sha256:c8625574ea376aace2bc076dc3733e3554c16b23f9a9eb25a3dba220f2829f4b
D5.S3.Quantum.Subentropy.GaussianMatrix.matrix_subentropy_gaussian_entropy sha256:ddc126b442874d917e4b995ee0c2cef8bab9dae916da701befc0aa9848197b61
D5.S3.Quantum.Subentropy.GaussianQuadratic.complexGaussianCoordinates sha256:6fd2ae0a8ed8f70c0781f25b956088ff14ae0a1fd4c0cda95412fa90db63a029
D5.S3.Quantum.Subentropy.GaussianQuadratic.complexGaussianCoordinates._proof_1 sha256:000cacec289957d214a4b49c6f9b577dc1fbd95068d5256c75d8bea12a43803f
D5.S3.Quantum.Subentropy.GaussianQuadratic.complex_coordinate_transport sha256:f36cd84a7550d6fecf5e101bd44189b74a28616b34afa64514dc22feaafdfd19
D5.S3.Quantum.Subentropy.GaussianQuadratic.gaussianQuadratic sha256:45e836be7a7690d64fd7bf84825d8221683eda68c284e23112d1974a580f1edb
D5.S3.Quantum.Subentropy.GaussianQuadratic.gaussianQuadratic._proof_1 sha256:b84e336425e73337497a7d20b68a320f349cbb16c794337905b56d9f7a033df4
D5.S3.Quantum.Subentropy.GaussianQuadratic.gaussianQuadratic._proof_2 sha256:e2d8db4cb82afca1a4323b05adf84c8b719155a266d26705a448455fc173e1f0
D5.S3.Quantum.Subentropy.GaussianQuadratic.gaussianQuadratic._proof_3 sha256:fb561d851ee5a0bba49188425848e4728c1ebd593be940d16d9451f9a1f96731
D5.S3.Quantum.Subentropy.GaussianQuadratic.gaussianQuadratic.congr_simp sha256:23178faa1e9937636d7e541a05710c735649890af27c17bf8b283fe247d352d3
D5.S3.Quantum.Subentropy.GaussianQuadratic.spectral_transport sha256:728980b7131dcd083b3d9fb10318ada92af378d042d79abe177ec62898c5ab14
D5.S3.Quantum.Subentropy.GuessingProbability.pGuess sha256:9d0b3f85b9b0480be1af1207d05617b7bae17de09b1531d939cf1974fb2326c2
D5.S3.Quantum.Subentropy.GuessingProbability.successProbability sha256:41341de581429b0f229e3797b8bf02a59129ed8f9c41b75f285e205e71b504ad
D5.S3.Quantum.Subentropy.GuessingProbability.successProbabilitySet sha256:fb2cd516d4ae06aca890fd13924b9d3b9407fdd00975dad85f00f14963bc9dc1
D5.S3.Quantum.Subentropy.POVMGram.cq_conditional_subentropy_guessing sha256:d4753a2853450488b89e9befd43efcdbf99f83817d39ef95bb624b18b0910e30
D5.S3.StatisticalMechanics.RandomWalks.RenewalMinorantMaximalityRefutation.Ak sha256:1cfa7d89b18df23286fc3e5ccd024c57cb176e806ca772307ebfd19111dbdb1d
Per-declaration proof_shape; consumers are declarations of this module; all escape_witness values are none.
proof_shape: C: bind-only; consumers=harmonic_eq_one_add_C,subentropySpectrum,subentropySpectrum_as_simplex_phi,subentropySpectrum_exponential_representation
proof_shape: simplexCoords: bind-only; consumers=exponential_normalized_radial_map,simplexCoords_isClosed,simplexCoords_isCompact,simplexMeasure,simplexMeasure_probability,simplex_coord_le_one,simplex_exponential_radial_map,simplex_linear_integrable,simplex_phi_integrable,simplex_radial_lintegral,simplex_radial_weighted_lintegral,simplex_scale_domain,simplex_scaled_lintegral,simplex_scaled_open_lintegral,simplex_volume,subentropySpectrum,subentropySpectrum_as_simplex_phi
proof_shape: subentropySpectrum: bind-only; consumers=subentropy,subentropySpectrum_as_simplex_phi,subentropySpectrum_exponential_pi_representation,subentropySpectrum_exponential_representation,subentropySpectrum_gaussian_half_pos,subentropySpectrum_gaussian_half_representation,subentropy_matrix_gaussian_half
proof_shape: subentropy: bind-only; consumers=claim,result,source_eq_determinant,subentropy_matrix_gaussian_half
proof_shape: pGuess: bind-only; consumers=claim,result
proof_shape: claim: bind-only; consumers=result
proof_shape: lintegral_fin_prod: bind-only; consumers=pi_withDensity_fin
proof_shape: pi_withDensity_fin: bind-only; consumers=orthantExponential_eq_pi
proof_shape: simplexPoint_succ_snoc: bind-only; consumers=simplexLinear_radial_identity
proof_shape: phi_mul_nonneg: bind-only; consumers=phi_product_integral_ae
proof_shape: simplex_scale_domain: bind-only; consumers=simplex_scaled_lintegral
proof_shape: sumFiber: bind-only; consumers=simplex_sum_boundary_null,sumFiber_ne_top
proof_shape: sumFiber_ne_top: bind-only; consumers=simplex_sum_boundary_null
proof_shape: simplex_sum_boundary_null: bind-only; consumers=simplex_scaled_open_lintegral
proof_shape: simplex_scaled_lintegral: bind-only; consumers=simplex_scaled_open_lintegral
proof_shape: positive_ray_shift_lintegral: bind-only; consumers=simplex_radial_lintegral
proof_shape: simplex_scaled_open_lintegral: bind-only; consumers=simplex_radial_lintegral
proof_shape: simplex_radial_lintegral: bind-only; consumers=simplex_radial_weighted_lintegral
proof_shape: orthantTailMeasure: bind-only; consumers=exponentialTailMeasure,exponentialTailMeasure_eq_prod,exponentialTail_ae_domain,simplex_exponential_radial_map
proof_shape: radialCoordinateMap: bind-only; consumers=exponential_normalized_radial_map,exponential_phi_radial_factorization,exponential_radial_integral,radialCoordinateMap_measurable,simplex_exponential_radial_map,simplex_linear_first_moment,simplex_volume
proof_shape: radialCoordinateMap_measurable: bind-only; consumers=exponential_radial_integral,simplex_exponential_radial_map,simplex_volume
proof_shape: simplex_radial_weighted_lintegral: bind-only; consumers=simplex_exponential_radial_map
proof_shape: orthantExponentialMeasure: bind-only; consumers=exponentialTailMeasure_eq_prod,exponentialTailMeasure_probability,exponentialTail_linear_moment,exponential_snoc_split_map,orthantExponentialMeasure_probability,orthantExponential_coordinate_integrable,orthantExponential_coordinate_moment,orthantExponential_eq_pi,orthantExponential_integral
proof_shape: exponentialTailMeasure: bind-only; consumers=exponentialTailMeasure_eq_prod,exponentialTailMeasure_probability,exponentialTail_ae_domain,exponentialTail_linear_moment,exponential_normalized_radial_map,exponential_phi_radial_factorization,exponential_radial_integral,exponential_snoc_split_map,simplex_exponential_radial_map,simplex_linear_first_moment,simplex_volume,subentropySpectrum_exponential_pi_representation,subentropySpectrum_exponential_representation
proof_shape: unnormalizedGammaMeasure: bind-only; consumers=expMeasure_one_density,exponential_normalized_radial_map,gamma_nat_density,normalizedGamma_integral,simplex_exponential_radial_map,simplex_volume,unnormalizedGammaMeasure_mass
proof_shape: gamma_nat_density: bind-only; consumers=expMeasure_one_density,exponential_normalized_radial_map,normalizedGamma_integral
proof_shape: expMeasure_one_density: bind-only; consumers=exponentialTailMeasure_eq_prod,orthantExponential_eq_pi,stdGaussian_squared_coordinates_map
proof_shape: exponentialTailMeasure_eq_prod: bind-only; consumers=exponentialTailMeasure_probability,exponentialTail_linear_moment,exponential_snoc_split_map
proof_shape: simplex_exponential_radial_map: bind-only; consumers=exponential_normalized_radial_map,simplex_volume
proof_shape: orthant_exponential_integral: bind-only; consumers=orthantExponentialMeasure_probability
proof_shape: orthantExponentialMeasure_probability: bind-only; consumers=exponentialTailMeasure_probability,exponentialTail_linear_moment
proof_shape: positiveExponentialMeasure_probability: bind-only; consumers=baseline_integral,exponentialTailMeasure_probability,exponentialTail_linear_moment,exponential_snoc_split_map
proof_shape: exponentialTailMeasure_probability: bind-only; consumers=simplex_volume
proof_shape: gamma_integer_integral: bind-only; consumers=normalizedGamma_pow_moment,positive_exponential_integral_id,unnormalizedGammaMeasure_mass
proof_shape: unnormalizedGammaMeasure_mass: bind-only; consumers=simplex_volume
proof_shape: simplex_volume: bind-only; consumers=simplexMeasure_probability
proof_shape: simplexCoords_eq_Ak: bind-only; consumers=exponential_normalized_radial_map,simplexMeasure_probability,subentropySpectrum_as_simplex_phi
proof_shape: simplexMeasure: bind-only; consumers=exponential_normalized_radial_map,exponential_phi_radial_factorization,exponential_radial_integral,simplexMeasure_probability,simplex_linear_first_moment,simplex_linear_integrable,simplex_phi_integrable,subentropySpectrum_as_simplex_phi,subentropySpectrum_exponential_representation
proof_shape: subentropySpectrum_as_simplex_phi: bind-only; consumers=subentropySpectrum_exponential_representation
proof_shape: harmonic_eq_one_add_C: bind-only; consumers=subentropySpectrum_exponential_representation
proof_shape: normalizedGammaMeasure_probability: bind-only; consumers=exponential_phi_radial_factorization,simplex_linear_first_moment
proof_shape: simplexMeasure_probability: bind-only; consumers=exponential_phi_radial_factorization,simplex_linear_first_moment
proof_shape: exponential_normalized_radial_map: bind-only; consumers=exponential_radial_integral
proof_shape: exponential_radial_integral: bind-only; consumers=exponential_phi_radial_factorization,simplex_linear_first_moment
proof_shape: gamma_log_moment: bind-only; consumers=normalizedGamma_phi_moment
proof_shape: normalizedGamma_integral: bind-only; consumers=normalizedGamma_phi_moment,normalizedGamma_pow_moment
proof_shape: normalizedGamma_pow_moment: bind-only; consumers=normalizedGamma_first_moment
proof_shape: normalizedGamma_first_moment: bind-only; consumers=exponential_phi_radial_factorization,normalizedGamma_integrable_id,positiveExponential_first_moment,simplex_linear_first_moment
proof_shape: normalizedGamma_phi_moment: bind-only; consumers=exponential_phi_integral,exponential_phi_radial_factorization,normalizedGamma_phi_integrable
proof_shape: normalizedGamma_integrable_id: bind-only; consumers=exponential_phi_radial_factorization
proof_shape: orthantExponential_integral: bind-only; consumers=orthantExponential_coordinate_moment
proof_shape: orthant_exponential_weighted_product: bind-only; consumers=orthantExponential_coordinate_moment
proof_shape: positive_exponential_integral_id: bind-only; consumers=orthantExponential_coordinate_moment
proof_shape: orthantExponential_coordinate_moment: bind-only; consumers=exponentialTail_linear_moment,orthantExponential_coordinate_integrable
proof_shape: orthantExponential_coordinate_integrable: bind-only; consumers=exponentialTail_linear_moment
proof_shape: simplex_coord_le_one: bind-only; consumers=simplexCoords_isCompact
proof_shape: simplexCoords_isClosed: bind-only; consumers=simplexCoords_isCompact
proof_shape: simplexCoords_isCompact: bind-only; consumers=simplex_linear_integrable,simplex_phi_integrable
proof_shape: simplexPoint_continuous: bind-only; consumers=exponential_phi_radial_factorization,simplex_linear_first_moment,simplex_linear_integrable,simplex_phi_integrable
proof_shape: simplex_linear_integrable: bind-only; consumers=exponential_phi_radial_factorization
proof_shape: simplex_phi_integrable: bind-only; consumers=exponential_phi_radial_factorization
proof_shape: positiveExponential_first_moment: bind-only; consumers=exponentialTail_linear_moment,positiveExponential_integrable_id
proof_shape: positiveExponential_integrable_id: bind-only; consumers=exponentialTail_linear_moment
proof_shape: exponentialTail_linear_moment: bind-only; consumers=simplex_linear_first_moment
proof_shape: simplexLinear_radial_identity: bind-only; consumers=exponential_phi_radial_factorization,simplex_linear_first_moment
proof_shape: exponentialTail_ae_domain: bind-only; consumers=exponential_phi_radial_factorization,simplex_linear_first_moment
proof_shape: simplex_linear_first_moment: bind-only; consumers=exponential_phi_radial_factorization
proof_shape: normalizedGamma_phi_integrable: bind-only; consumers=exponential_phi_radial_factorization
proof_shape: phi_product_integral_ae: bind-only; consumers=exponential_phi_radial_factorization
proof_shape: exponential_phi_radial_factorization: bind-only; consumers=subentropySpectrum_exponential_representation
proof_shape: subentropySpectrum_exponential_representation: bind-only; consumers=subentropySpectrum_exponential_pi_representation
proof_shape: orthantExponential_eq_pi: bind-only; consumers=exponential_snoc_split_map
proof_shape: exponential_snoc_split_map: bind-only; consumers=subentropySpectrum_exponential_pi_representation
proof_shape: subentropySpectrum_exponential_pi_representation: bind-only; consumers=subentropySpectrum_gaussian_half_representation
proof_shape: square_pos_image: bind-only; consumers=square_positive_lintegral
proof_shape: square_positive_lintegral: bind-only; consumers=complex_sqnorm_radial_lintegral
proof_shape: complex_sqnorm_radial_lintegral: bind-only; consumers=complex_sqnorm_volume_map
proof_shape: complex_sqnorm_volume_map: bind-only; consumers=complex_half_sqnorm_volume_map
proof_shape: map_withDensity_composed: bind-only; consumers=stdGaussian_complex_density_product,stdGaussian_complex_half_sqnorm_map
proof_shape: stdGaussian_complex_eq_map_prod: bind-only; consumers=stdGaussian_complex_density_product
proof_shape: stdGaussian_complex_density_product: bind-only; consumers=stdGaussian_complex_density
proof_shape: gaussianPDF_complex_product: bind-only; consumers=stdGaussian_complex_density
proof_shape: stdGaussian_complex_density: bind-only; consumers=stdGaussian_complex_half_sqnorm_map
proof_shape: complex_half_sqnorm_volume_map: bind-only; consumers=stdGaussian_complex_half_sqnorm_map
proof_shape: stdGaussian_complex_half_sqnorm_map: bind-only; consumers=stdGaussian_squared_coordinates_map
proof_shape: stdGaussian_complex_pi_map: bind-only; consumers=stdGaussian_squared_coordinates_map
proof_shape: stdGaussian_squared_coordinates_map: bind-only; consumers=baseline_integral,gaussian_squared_coordinate_integral
proof_shape: gaussian_squared_coordinate_integral: bind-only; consumers=subentropySpectrum_gaussian_half_representation
proof_shape: subentropySpectrum_gaussian_half_representation: bind-only; consumers=subentropySpectrum_gaussian_half_pos
proof_shape: spectralCoordinates_quadratic: bind-only; consumers=gaussian_matrix_spectral_integral
proof_shape: spectralCoordinates_gaussian_map: bind-only; consumers=gaussian_matrix_spectral_integral
proof_shape: gaussian_matrix_spectral_integral: bind-only; consumers=subentropy_matrix_gaussian_half
proof_shape: eigenvalues0_sum: bind-only; consumers=subentropy_matrix_gaussian_half
proof_shape: trace_one_card_pos: bind-only; consumers=source_eq_determinant,subentropy_matrix_gaussian_half
proof_shape: subentropySpectrum_gaussian_half_pos: bind-only; consumers=subentropy_matrix_gaussian_half
proof_shape: subentropy_matrix_gaussian_half: bind-only; consumers=source_eq_determinant
proof_shape: exponential_phi_integral: bind-only; consumers=baseline_integral
proof_shape: baseline_integral: bind-only; consumers=source_eq_determinant
proof_shape: source_eq_determinant: bind-only; consumers=result
proof_shape: normalize_ensemble: bind-only; consumers=determinant_cq_bound
proof_shape: determinant_reindex: bind-only; consumers=determinant_cq_bound
proof_shape: determinant_cq_bound: bind-only; consumers=result
-/

import D5.S3.Quantum.Subentropy.POVMGram
import D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace
import D5.S3.Quantum.Subentropy.Basic
import D5.S3.Quantum.Subentropy.GuessingProbability
import D5.S3.Quantum.Subentropy.ClassicalQuantumGram
import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.Information.OrthogonalRecordEntropy
import D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing
import D5.S3.Quantum.Subentropy.GaussianMatrix
import D5.S3.Quantum.Subentropy.GaussianQuadratic
import D5.S3.StatisticalMechanics.RandomWalks.RenewalMinorantMaximalityRefutation
namespace D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound
open D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing (chart)
open ProbabilityTheory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory ProbabilityTheory
open scoped ComplexOrder
/-- `C_n = 1/2 + 1/3 + ⋯ + 1/n` (Equation (2)). -/
noncomputable def C (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 n, (1 : ℝ) / k
/-- The coordinates `(x₁, …, x_{n−1})` of the probability simplex `Δₙ`. -/
def simplexCoords (n : ℕ) : Set (Fin (n - 1) → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1}
/-- Equation (4): `Q = n ∫_{Δₙ} η(λ · x) dx − Cₙ`, with the normalized uniform measure
`dx = (n − 1)! dx₁ ⋯ dx_{n−1}` (Equation (3)). -/
noncomputable def subentropySpectrum (n : ℕ) (lam : Fin n → ℝ) : ℝ :=
  n * ((n - 1).factorial * ∫ y in simplexCoords n, Real.negMulLog (∑ i, lam i * (chart (n := n)) y i)) - C n
/-- The subentropy `Q(ρ)` of a Hermitian matrix, from its eigenvalues (`eigenvalues₀`, listed in order). -/
noncomputable def subentropy {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : Matrix ι ι ℂ) (hρ : ρ.IsHermitian) : ℝ :=
  subentropySpectrum (Fintype.card ι) hρ.eigenvalues₀
/-- `p_guess(X|B) = max_{POVM {E_x}} ∑ₓ pₓ Tr(Eₓ ρ_B^x)`, with `Aₓ = pₓ ρ_B^x`. -/
noncomputable def pGuess {X B : Type} [Fintype X] [Fintype B] [DecidableEq B] (A : X → Matrix B B ℂ) : ℝ :=
  sSup {s | ∃ E : X → Matrix B B ℂ, (∀ x, (E x).PosSemidef) ∧ ∑ x, E x = 1 ∧ s = (∑ x, (E x * A x).trace).re}
/-- Datta–Dorlas–Jozsa–Benatti, Conjecture 2: "For a c-q state ρ_XB, the conditional subentropy
Q(X|B) satisfies the following bound: Q(X|B) ≤ H_min(X|B) = −ln p_guess(X|B)." Here
`ρ_XB = ∑ₓ |x⟩⟨x| ⊗ Aₓ` is the block-diagonal matrix of the `Aₓ = pₓ ρ_B^x`, `ρ_B = ∑ₓ Aₓ`, and
`Q(X|B) = Q(ρ_XB) − Q(ρ_B)` (Equation (13)). -/
def claim : Prop :=
  ∀ (X B : Type) [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B] (A : X → Matrix B B ℂ),
    (∀ x, (A x).PosSemidef) → (∑ x, (A x).trace) = 1 → ∀ (hXB : (blockDiagonal A).IsHermitian) (hB : (∑ x, A x).IsHermitian), subentropy (blockDiagonal A) hXB - subentropy (∑ x, A x) hB ≤ -Real.log (pGuess A)
open MeasureTheory Set
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false in
private lemma lintegral_fin_prod {n : ℕ} {E : Fin n → Type*} {mE : ∀ i, MeasurableSpace (E i)} (μ : (i : Fin n) → Measure (E i)) [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)), f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i) ∂((μ 0).prod (Measure.pi (fun i => μ i.succ))) :=
        by
        rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]; simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ, Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂μ i.succ := by
        rw [lintegral_prod_mul (μ := μ 0) (ν := Measure.pi (fun i : Fin n => μ i.succ)) (f := f 0) (g := fun (x : (i : Fin n) → E i.succ) => ∏ i : Fin n, f i.succ (x i)) (hf 0).aemeasurable
            (by exact (Finset.measurable_prod _ (fun i _ => (hf i.succ).comp (measurable_pi_apply i))).aemeasurable),
          ih _ _ (fun i => hf i.succ)]
      _ = _ := by exact Eq.symm (Fin.prod_univ_succAbove (fun i => ∫⁻ (x : E i), f i x ∂μ i) 0)
private lemma pi_withDensity_fin {n : ℕ} {E : Fin n → Type*} {mE : ∀ i, MeasurableSpace (E i)} (μ : (i : Fin n) → Measure (E i)) [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] : Measure.pi (fun i => (μ i).withDensity (f i)) = (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) :=
  by
  apply Measure.pi_eq; intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi, lintegral_fin_prod (fun i => (μ i).restrict (s i)) f hf]
  apply Finset.prod_congr rfl; intro i _
  exact (withDensity_apply (μ := μ i) (f i) (hs i)).symm
open Matrix MeasureTheory Set
private lemma simplexPoint_succ_snoc (n : ℕ) (y : Fin n → ℝ) : (chart (n := n + 1)) y = Fin.snoc y (1 - ∑ j, y j) :=
  by exact List.ofFn_inj.mp rfl
private lemma phi_mul_nonneg {s t : ℝ}  : s * t * Real.log (s * t) = s * (t * Real.log t) + t * (s * Real.log s) :=
  by
  have h := Real.negMulLog_mul s t
  simp only [Real.negMulLog, neg_mul] at h; linarith
open scoped Pointwise
private lemma simplex_scale_domain (n : ℕ) (t : ℝ) (ht : 0 < t) : t • simplexCoords (n + 1) = {u : Fin n → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ t} :=
  by
  change t • {u : Fin n → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1} = _; ext u; constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨fun i => mul_nonneg ht.le (hy.1 i), ?_⟩
    change (∑ i, t * y i) ≤ t; rw [← Finset.mul_sum]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hy.2 ht.le
  · intro hu
    refine ⟨t⁻¹ • u, ?_, ?_⟩
    · refine ⟨fun i => mul_nonneg (inv_nonneg.mpr ht.le) (hu.1 i), ?_⟩
      change (∑ i, t⁻¹ * u i) ≤ 1; rw [← Finset.mul_sum]
      calc
        t⁻¹ * ∑ i, u i ≤ t⁻¹ * t := mul_le_mul_of_nonneg_left hu.2 (inv_nonneg.mpr ht.le)
        _ = 1 := inv_mul_cancel₀ ht.ne'
    · change t • (t⁻¹ • u) = u
      rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
private noncomputable def sumFiber (n : ℕ) (t : ℝ) : AffineSubspace ℝ (Fin n → ℝ) :=
  ({ t } : AffineSubspace ℝ ℝ).comap (∑ i : Fin n, (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ)).toAffineMap
private lemma sumFiber_ne_top (n : ℕ) (hn : 0 < n) (t : ℝ) : sumFiber n t ≠ ⊤ := by
  intro htop
  let i : Fin n := ⟨0, hn⟩
  have hmem : Pi.single i (t + 1) ∈ sumFiber n t := by rw [htop]; trivial
  change ((∑ j : Fin n, (LinearMap.proj j : (Fin n → ℝ) →ₗ[ℝ] ℝ)) (Pi.single i (t + 1))) = t at hmem; simp [Pi.single_apply, LinearMap.sum_apply] at hmem
lemma simplex_sum_boundary_null (n : ℕ) (t : ℝ) (ht : 0 < t) : volume {u : Fin n → ℝ | ∑ i, u i = t} = 0 :=
  by
  rcases n with _ | n
  · simp [ht.ne]
  · have heq : ({u : Fin (n + 1) → ℝ | ∑ i, u i = t} : Set _) = sumFiber (n + 1) t := by
      ext u; simp [sumFiber, LinearMap.sum_apply, Finset.sum_apply]
    rw [heq]; exact Measure.addHaar_affineSubspace volume (sumFiber (n + 1) t) (sumFiber_ne_top (n + 1) (by exact Nat.zero_lt_succ n) t)
open scoped ENNReal Pointwise
private lemma simplex_scaled_lintegral (n : ℕ) (t : ℝ) (ht : 0 < t) (f : (Fin n → ℝ) → ℝ≥0∞) : (∫⁻ u in {u : Fin n → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ t}, f (t⁻¹ • u)) = ENNReal.ofReal (t ^ n) * ∫⁻ y in simplexCoords (n + 1), f y :=
  by
  let e : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) := (Homeomorph.smul (Units.mk0 (t⁻¹) (inv_ne_zero ht.ne'))).toMeasurableEquiv
  have he : (e : (Fin n → ℝ) → (Fin n → ℝ)) = (t⁻¹ • ·) := rfl
  have hpre : e ⁻¹' simplexCoords (n + 1) = t • simplexCoords (n + 1) := by
    ext u; rw [mem_smul_set_iff_inv_smul_mem₀ ht.ne']
    rfl
  have hmap : Measure.map e volume = ENNReal.ofReal (t ^ n) • volume := by
    rw [he, Measure.map_addHaar_smul volume (inv_ne_zero ht.ne')]; simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, inv_pow, inv_inv, abs_of_nonneg (pow_nonneg ht.le n)]
  calc
    _ = ∫⁻ u in e ⁻¹' simplexCoords (n + 1), f (e u) := by
      rw [hpre, simplex_scale_domain n t ht]
      rfl
    _ = ∫⁻ y in simplexCoords (n + 1), f y ∂Measure.map e volume := by rw [e.measurableEmbedding.restrict_map, e.measurableEmbedding.lintegral_map]
    _ = _ := by rw [hmap, Measure.restrict_smul, lintegral_smul_measure]; rfl
private lemma positive_ray_shift_lintegral (c : ℝ) (f : ℝ → ℝ≥0∞) : (∫⁻ v : ℝ in Ioi 0, f (v + c)) = ∫⁻ t : ℝ in Ioi c, f t :=
  by
  have hpre : (fun v : ℝ => v + c) ⁻¹' Ioi c = Ioi 0 := by
    ext v
    simp
  simpa only [hpre] using (measurePreserving_add_right volume c).setLIntegral_comp_preimage_emb (MeasurableEquiv.addRight c).measurableEmbedding f (Ioi c)
private lemma simplex_scaled_open_lintegral (n : ℕ) (t : ℝ) (ht : 0 < t) (f : (Fin n → ℝ) → ℝ≥0∞) : (∫⁻ u in {u : Fin n → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i < t}, f (t⁻¹ • u)) = ENNReal.ofReal (t ^ n) * ∫⁻ y in simplexCoords (n + 1), f y :=
  by
  rw [← simplex_scaled_lintegral n t ht f]
  have hsets : {u : Fin n → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i < t} =ᵐ[volume] {u : Fin n → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ t} :=
    by
    have hae : ∀ᵐ u : Fin n → ℝ, (∑ i, u i) ≠ t := ae_iff.mpr (by simpa only [not_not] using simplex_sum_boundary_null n t ht)
    filter_upwards [hae] with u hu
    exact propext ⟨fun h => ⟨h.1, h.2.le⟩, fun h => ⟨h.1, lt_of_le_of_ne h.2 hu⟩⟩
  rw [Measure.restrict_congr_set hsets]
private lemma simplex_radial_lintegral (n : ℕ) (F : ℝ × (Fin n → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ u in {u : Fin n → ℝ | ∀ i, 0 ≤ u i}, ∫⁻ v : ℝ in Ioi 0, F (v + (∑ i, u i), (v + ∑ i, u i)⁻¹ • u)) = ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (t ^ n) * ∫⁻ y in simplexCoords (n + 1), F (t, y) := by
  classical
  let P : Set (Fin n → ℝ) := {u | ∀ i, 0 ≤ u i}
  let H : (Fin n → ℝ) → ℝ → ℝ≥0∞ := fun u t => if (∑ i, u i) < t then F (t, t⁻¹ • u) else 0
  have hH : Measurable (Function.uncurry H) :=
    by
    have hcomp : Measurable (fun p : (Fin n → ℝ) × ℝ => F (p.2, p.2⁻¹ • p.1)) := hF.comp (measurable_snd.prodMk (measurable_snd.inv.smul measurable_fst))
    have hD : MeasurableSet {p : (Fin n → ℝ) × ℝ | (∑ i, p.1 i) < p.2} := (isOpen_lt (continuous_finsetSum _ (fun i _ => (continuous_apply i).comp continuous_fst)) continuous_snd).measurableSet
    exact hcomp.ite hD measurable_const
  have hinner (u : Fin n → ℝ) : (∫⁻ t : ℝ, H u t) = ∫⁻ t : ℝ in Ioi (∑ i, u i), F (t, t⁻¹ • u) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    rfl
  have hfiber (t : ℝ) : (∫⁻ u in P, H u t) = ∫⁻ u in {u : Fin n → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i < t}, F (t, t⁻¹ • u) :=
    by
    have hD : MeasurableSet {u : Fin n → ℝ | (∑ i, u i) < t} := (isOpen_lt (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const).measurableSet
    have heq : (fun u : Fin n → ℝ => H u t) = {u : Fin n → ℝ | (∑ i, u i) < t}.indicator (fun u => F (t, t⁻¹ • u)) := rfl
    rw [heq, lintegral_indicator hD, Measure.restrict_restrict hD]
    have hs : {u : Fin n → ℝ | (∑ i, u i) < t} ∩ P = {u : Fin n → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i < t} := by exact ofPred_inter_eq_sep (fun a => ∑ i, a i < t) P
    rw [hs]
  calc
    _ = ∫⁻ u in P, ∫⁻ t : ℝ, H u t := by
      apply lintegral_congr_ae; filter_upwards [] with u; rw [hinner]
      exact positive_ray_shift_lintegral (∑ i, u i) (fun t => F (t, t⁻¹ • u))
    _ = ∫⁻ t : ℝ, ∫⁻ u in P, H u t := (lintegral_lintegral_swap hH.aemeasurable)
    _ = _ := by
      rw [← lintegral_indicator measurableSet_Ioi]; apply lintegral_congr_ae; filter_upwards [] with t; rw [hfiber]
      by_cases ht : 0 < t
      · rw [Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
        exact simplex_scaled_open_lintegral n t ht (fun y => F (t, y))
      · have hemp : {u : Fin n → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i < t} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr; intro u hu
          have hsum := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hu.1 i)
          exact ht (hsum.trans_lt hu.2)
        simp [ht, hemp]
private noncomputable def orthantTailMeasure (n : ℕ) : Measure ((Fin n → ℝ) × ℝ) :=
  (volume.restrict {u : Fin n → ℝ | ∀ i, 0 ≤ u i}).prod (volume.restrict (Ioi 0))
private noncomputable def radialCoordinateMap (n : ℕ) (p : (Fin n → ℝ) × ℝ) : ℝ × (Fin n → ℝ) :=
  (p.2 + ∑ i, p.1 i, (p.2 + ∑ i, p.1 i)⁻¹ • p.1)
private lemma radialCoordinateMap_measurable (n : ℕ) : Measurable (radialCoordinateMap n) := by
  unfold radialCoordinateMap
  fun_prop
private lemma simplex_radial_weighted_lintegral (n : ℕ) (w : ℝ → ℝ≥0∞) (hw : Measurable w) (F : ℝ × (Fin n → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ u in {u : Fin n → ℝ | ∀ i, 0 ≤ u i}, ∫⁻ v : ℝ in Ioi 0, w (v + ∑ i, u i) * F (v + ∑ i, u i, (v + ∑ i, u i)⁻¹ • u)) = ∫⁻ t : ℝ in Ioi 0, (ENNReal.ofReal (t ^ n) * w t) * ∫⁻ y in simplexCoords (n + 1), F (t, y) :=
  by
  have h := simplex_radial_lintegral n (fun p => w p.1 * F p) ((hw.comp measurable_fst).mul hF)
  rw [h]; apply lintegral_congr_ae; filter_upwards [] with t
  have hh := lintegral_const_mul (μ := volume.restrict (simplexCoords (n + 1))) (w t) (f := fun y => F (t, y)) (hF.comp (measurable_const.prodMk measurable_id))
  simpa only [mul_assoc] using congrArg (ENNReal.ofReal (t ^ n) * ·) hh
private noncomputable def orthantExponentialMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  (volume.restrict {u : Fin n → ℝ | ∀ i, 0 ≤ u i}).withDensity (fun u => ENNReal.ofReal (Real.exp (-(∑ i, u i))))
private noncomputable def exponentialTailMeasure (n : ℕ) : Measure ((Fin n → ℝ) × ℝ) :=
  (orthantTailMeasure n).withDensity (fun p => ENNReal.ofReal (Real.exp (-(p.2 + ∑ i, p.1 i))))
private noncomputable def unnormalizedGammaMeasure (n : ℕ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (t ^ n) * ENNReal.ofReal (Real.exp (-t)))
private lemma gamma_nat_density (n : ℕ) : gammaMeasure (n + 1) 1 = (n.factorial : ℝ≥0∞)⁻¹ • unnormalizedGammaMeasure n :=
  by
  unfold unnormalizedGammaMeasure; rw [gammaMeasure, ← withDensity_smul _ (by fun_prop), ← withDensity_indicator measurableSet_Ioi]; apply withDensity_congr_ae; filter_upwards [(volume : Measure ℝ).ae_ne (0 : ℝ)] with t ht
  by_cases h : 0 < t
  · simp only [gammaPDF, gammaPDFReal, if_pos h.le, Real.one_rpow, one_mul, Real.Gamma_nat_eq_factorial, add_sub_cancel_right, Real.rpow_natCast, Pi.smul_apply, smul_eq_mul]
    rw [Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from h)]; simp only [Pi.smul_apply, smul_eq_mul]; rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by exact Nat.one_div_cast_nonneg n.factorial)]; simp [ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < n.factorial), mul_assoc]
  · have hn : t < 0 := lt_of_le_of_ne (le_of_not_gt h) ht
    rw [gammaPDF_of_neg hn, Set.indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from h)]
private lemma expMeasure_one_density : expMeasure 1 = (volume.restrict (Ioi 0)).withDensity (fun t : ℝ => ENNReal.ofReal (Real.exp (-t))) := by simpa [expMeasure, Nat.factorial_zero, unnormalizedGammaMeasure] using gamma_nat_density 0
private lemma exponentialTailMeasure_eq_prod (n : ℕ) : exponentialTailMeasure n = (orthantExponentialMeasure n).prod (ProbabilityTheory.expMeasure 1) :=
  by
  unfold exponentialTailMeasure orthantExponentialMeasure orthantTailMeasure; rw [expMeasure_one_density]; rw [prod_withDensity (by fun_prop) (by fun_prop)]; congr 1; funext p; rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]; congr 2; ring
private lemma simplex_exponential_radial_map (n : ℕ) : Measure.map (radialCoordinateMap n) (exponentialTailMeasure n) = (unnormalizedGammaMeasure n).prod (volume.restrict (simplexCoords (n + 1))) :=
  by
  apply Measure.ext_of_lintegral; intro F hF
  have hd : Measurable (fun p : (Fin n → ℝ) × ℝ => ENNReal.ofReal (Real.exp (-(p.2 + ∑ i, p.1 i)))) := by fun_prop
  have hc : Measurable (fun p => F (radialCoordinateMap n p)) := hF.comp (radialCoordinateMap_measurable n)
  unfold exponentialTailMeasure; rw [lintegral_map hF (radialCoordinateMap_measurable n)]
  rw [lintegral_withDensity_eq_lintegral_mul _ hd (g := fun p => F (radialCoordinateMap n p)) hc]
  change (∫⁻ p, ENNReal.ofReal (Real.exp (-(p.2 + ∑ i, p.1 i))) * F (radialCoordinateMap n p) ∂(volume.restrict {u : Fin n → ℝ | ∀ i, 0 ≤ u i}).prod (volume.restrict (Ioi 0))) = _
  rw [lintegral_prod (fun p : (Fin n → ℝ) × ℝ => ENNReal.ofReal (Real.exp (-(p.2 + ∑ i, p.1 i))) * F (radialCoordinateMap n p)) (hd.mul hc).aemeasurable]
  change (∫⁻ u in {u : Fin n → ℝ | ∀ i, 0 ≤ u i}, ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(v + ∑ i, u i))) * F (v + ∑ i, u i, (v + ∑ i, u i)⁻¹ • u)) = _
  rw [simplex_radial_weighted_lintegral n (fun t => ENNReal.ofReal (Real.exp (-t))) (by fun_prop) F hF]
  symm; rw [lintegral_prod F hF.aemeasurable]; unfold unnormalizedGammaMeasure; exact lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hF.lintegral_prod_right'
private lemma orthant_exponential_integral (n : ℕ) : (∫ u in {u : Fin n → ℝ | ∀ i, 0 ≤ u i}, Real.exp (-(∑ i, u i))) = 1 := by
  classical
  let f : ℝ → ℝ := (Ici 0).indicator (fun t => Real.exp (-t))
  have hP : MeasurableSet {u : Fin n → ℝ | ∀ i, 0 ≤ u i} := by simpa only [Set.setOf_forall] using (isClosed_iInter (fun i : Fin n => isClosed_le continuous_const (continuous_apply i))).measurableSet
  have heq : {u : Fin n → ℝ | ∀ i, 0 ≤ u i}.indicator (fun u => Real.exp (-(∑ i, u i))) = fun u => ∏ i, f (u i) := by
    funext u
    by_cases hu : ∀ i, 0 ≤ u i
    · rw [Set.indicator_of_mem (show u ∈ {u : Fin n → ℝ | ∀ i, 0 ≤ u i} from hu)]
      have hfi : ∀ i, f (u i) = Real.exp (-u i) := fun i => Set.indicator_of_mem (show u i ∈ Ici (0 : ℝ) from hu i) _
      simp_rw [hfi]; rw [← Real.exp_sum]
      simp
    · rw [Set.indicator_of_notMem (show u ∉ {u : Fin n → ℝ | ∀ i, 0 ≤ u i} from hu)]
      obtain ⟨i, hi⟩ := not_forall.mp hu
      symm; apply Finset.prod_eq_zero (Finset.mem_univ i); exact Set.indicator_of_notMem (show u i ∉ Ici (0 : ℝ) from hi) _
  rw [← integral_indicator hP, heq, integral_fintype_prod_volume_eq_prod (fun _ : Fin n => f)]
  have hfi : ∫ t : ℝ, f t = 1 := by
    rw [show f = (Ici (0 : ℝ)).indicator (fun t => Real.exp (-t)) from rfl, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
    exact integral_exp_neg_Ioi_zero
  simp only [hfi, Finset.prod_const_one]
private lemma orthantExponentialMeasure_probability (n : ℕ) : IsProbabilityMeasure (orthantExponentialMeasure n) :=
  by
  constructor; unfold orthantExponentialMeasure; rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  have hI := orthant_exponential_integral n
  have hi : Integrable (fun u : Fin n → ℝ => Real.exp (-(∑ i, u i))) (volume.restrict {u : Fin n → ℝ | ∀ i, 0 ≤ u i}) := integrable_of_integral_eq_one hI
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun u => Real.exp_nonneg _), hI, ENNReal.ofReal_one]
private lemma positiveExponentialMeasure_probability : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
  ProbabilityTheory.isProbabilityMeasure_expMeasure zero_lt_one
private lemma exponentialTailMeasure_probability (n : ℕ) : IsProbabilityMeasure (exponentialTailMeasure n) :=
  by
  rw [exponentialTailMeasure_eq_prod]
  letI := orthantExponentialMeasure_probability n
  letI := positiveExponentialMeasure_probability
  infer_instance
private lemma gamma_integer_integral (n : ℕ) : (∫ t : ℝ in Ioi 0, t ^ n * Real.exp (-t)) = n.factorial :=
  by
  have h := integral_rpow_mul_exp_neg_rpow (p := 1) (q := (n : ℝ)) (by exact Real.zero_lt_one) (lt_of_lt_of_le (by exact neg_one_lt_zero : (-1 : ℝ) < 0) (Nat.cast_nonneg n))
  simpa [Real.rpow_natCast, Real.Gamma_nat_eq_factorial] using h
private lemma unnormalizedGammaMeasure_mass (n : ℕ) : unnormalizedGammaMeasure n Set.univ = n.factorial :=
  by
  unfold unnormalizedGammaMeasure; rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  have hI := gamma_integer_integral n
  have hi : Integrable (fun t : ℝ => t ^ n * Real.exp (-t)) (volume.restrict (Ioi 0)) := by
    apply Integrable.of_integral_ne_zero; rw [hI]
    exact_mod_cast n.factorial_ne_zero
  have hnonneg : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), 0 ≤ t := by exact ae_restrict_mem measurableSet_Ioi |>.mono fun t ht => ht.le
  have hnn : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), 0 ≤ t ^ n * Real.exp (-t) := hnonneg.mono fun t ht => mul_nonneg (pow_nonneg ht n) (Real.exp_nonneg _)
  calc
    _ = ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (t ^ n * Real.exp (-t)) := by
      apply lintegral_congr_ae; filter_upwards [hnonneg] with t ht; exact (ENNReal.ofReal_mul (pow_nonneg ht n)).symm
    _ = ENNReal.ofReal (∫ t : ℝ in Ioi 0, t ^ n * Real.exp (-t)) := (ofReal_integral_eq_lintegral_ofReal hi hnn).symm
    _ = _ := by rw [hI]; simp
lemma simplex_volume (n : ℕ) : volume (simplexCoords (n + 1)) = (n.factorial : ℝ≥0∞)⁻¹ :=
  by
  letI : IsFiniteMeasure (unnormalizedGammaMeasure n) := ⟨by rw [unnormalizedGammaMeasure_mass]; simp⟩
  letI := exponentialTailMeasure_probability n
  have h := congrArg (fun μ : Measure (ℝ × (Fin n → ℝ)) => μ Set.univ) (simplex_exponential_radial_map n)
  rw [Measure.map_apply (radialCoordinateMap_measurable n) MeasurableSet.univ, Set.preimage_univ, measure_univ] at h
  have hhprod := Measure.prod_prod (μ := unnormalizedGammaMeasure n) (ν := volume.restrict (simplexCoords (n + 1))) Set.univ Set.univ
  rw [Set.univ_prod_univ] at hhprod
  have hm := hhprod.symm.trans h.symm
  rw [unnormalizedGammaMeasure_mass, Measure.restrict_apply_univ] at hm
  have hn0 : (n.factorial : ℝ≥0∞) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hh := congrArg ((n.factorial : ℝ≥0∞)⁻¹ * ·) hm
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel hn0 (ENNReal.natCast_ne_top n.factorial), one_mul, mul_one, Measure.restrict_apply_univ] using hh
private lemma simplexCoords_eq_Ak (n : ℕ) : simplexCoords n =
    D5.S3.StatisticalMechanics.RandomWalks.RenewalMinorantMaximalityRefutation.Ak n := rfl
private noncomputable def simplexMeasure (n : ℕ) : Measure (Fin (n - 1) → ℝ) :=
  ((n - 1).factorial : ℝ≥0∞) • volume.restrict (D5.S3.StatisticalMechanics.RandomWalks.RenewalMinorantMaximalityRefutation.Ak n)
private lemma subentropySpectrum_as_simplex_phi (n : ℕ) (lam : Fin n → ℝ) : subentropySpectrum n lam = -(n : ℝ) * (∫ y, (fun a : ℝ => a * Real.log a) (∑ i, lam i * (chart (n := n)) y i) ∂simplexMeasure n) - C n :=
  by
  have heta : (fun y => Real.negMulLog (∑ i, lam i * (chart (n := n)) y i)) = -(fun y => (fun a : ℝ => a * Real.log a) (∑ i, lam i * (chart (n := n)) y i)) :=
    by
    funext y; simp [Real.negMulLog, neg_mul]
  refine (congrArg (fun domain : Set (Fin (n - 1) → ℝ) =>
    (n : ℝ) * ((n - 1).factorial * ∫ y in domain, Real.negMulLog (∑ i, lam i * (chart (n := n)) y i)) - C n)
    (simplexCoords_eq_Ak n)).trans ?_
  simp only [simplexMeasure, integral_smul_measure, ENNReal.toReal_natCast, smul_eq_mul, heta, Pi.neg_apply, integral_neg, integral_neg']; ring
private lemma harmonic_eq_one_add_C (n : ℕ) (hn : 0 < n) : (harmonic n : ℝ) = 1 + C n := by
  rw [harmonic_eq_sum_Icc]; simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]; rw [← Finset.insert_Icc_succ_left_eq_Icc (Nat.succ_le_of_lt hn)]; simp [C, one_div]
private lemma normalizedGammaMeasure_probability (n : ℕ) : IsProbabilityMeasure (ProbabilityTheory.gammaMeasure (n + 1) 1) :=
  ProbabilityTheory.isProbabilityMeasure_gammaMeasure (by positivity) zero_lt_one
private lemma simplexMeasure_probability (n : ℕ) : IsProbabilityMeasure (simplexMeasure (n + 1)) := by
  constructor; simp only [simplexMeasure, ← simplexCoords_eq_Ak, Nat.add_sub_cancel, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ, simplex_volume]; exact ENNReal.mul_inv_cancel (by exact_mod_cast n.factorial_ne_zero) (by exact ENNReal.natCast_ne_top n.factorial)
private lemma exponential_normalized_radial_map (n : ℕ) : Measure.map (radialCoordinateMap n) (exponentialTailMeasure n) = ((ProbabilityTheory.gammaMeasure (n + 1) 1)).prod (simplexMeasure (n + 1)) :=
  by
  rw [simplex_exponential_radial_map]; unfold simplexMeasure; rw [gamma_nat_density]; simp only [Nat.add_sub_cancel, ← simplexCoords_eq_Ak]; rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]; rw [ENNReal.inv_mul_cancel (by exact_mod_cast n.factorial_ne_zero) (by exact ENNReal.natCast_ne_top n.factorial), one_smul]
private lemma exponential_radial_integral (n : ℕ) (F : ℝ × (Fin n → ℝ) → ℝ) (hF : Measurable F) :
    (∫ p, F (radialCoordinateMap n p) ∂exponentialTailMeasure n) = ∫ p, F p ∂((ProbabilityTheory.gammaMeasure (n + 1) 1)).prod (simplexMeasure (n + 1)) :=
  by
  rw [← exponential_normalized_radial_map]; exact (integral_map (radialCoordinateMap_measurable n).aemeasurable hF.aestronglyMeasurable).symm
private lemma gamma_log_moment (n : ℕ) : (∫ t : ℝ in Ioi 0, t ^ n * (Real.log t * Real.exp (-t))) = n.factorial * (-Real.eulerMascheroniConstant + (harmonic n : ℝ)) :=
  by
  have h := (Real.hasDerivAt_Gamma_of_pos (show (0 : ℝ) < n + 1 by positivity)).unique (Real.hasDerivAt_Gamma_nat n)
  simpa only [add_sub_cancel_right, Real.rpow_natCast] using h
private lemma normalizedGamma_integral (n : ℕ) (f : ℝ → ℝ) : (∫ t, f t ∂(ProbabilityTheory.gammaMeasure (n + 1) 1)) = ((n.factorial : ℝ)⁻¹) * ∫ t : ℝ in Ioi 0, (t ^ n * Real.exp (-t)) * f t :=
  by
  rw [gamma_nat_density]; unfold unnormalizedGammaMeasure; rw [integral_smul_measure]; simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]; congr 1
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (Filter.Eventually.of_forall fun t => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)]
  apply integral_congr_ae; filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg ht.le n), ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  rfl
private lemma normalizedGamma_pow_moment (n k : ℕ) : (∫ t : ℝ, t ^ k ∂(ProbabilityTheory.gammaMeasure (n + 1) 1)) = ((n + k).factorial : ℝ) / n.factorial :=
  by
  rw [normalizedGamma_integral]
  have heq : (fun t : ℝ => (t ^ n * Real.exp (-t)) * t ^ k) = fun t => t ^ (n + k) * Real.exp (-t) := by
    funext t; rw [pow_add]; ring
  rw [heq, gamma_integer_integral]; ring
private lemma normalizedGamma_first_moment (n : ℕ) : (∫ t : ℝ, t ∂(ProbabilityTheory.gammaMeasure (n + 1) 1)) = n + 1 :=
  by
  have h := normalizedGamma_pow_moment n 1
  simp only [pow_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
  have hn0 : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  simpa only [mul_div_cancel_right₀ _ hn0] using h
private lemma normalizedGamma_phi_moment (n : ℕ) : (∫ t : ℝ, (fun a : ℝ => a * Real.log a) t ∂(ProbabilityTheory.gammaMeasure (n + 1) 1)) = (n + 1) * ((harmonic (n + 1) : ℝ) - Real.eulerMascheroniConstant) :=
  by
  rw [normalizedGamma_integral]
  have heq : (fun t : ℝ => (t ^ n * Real.exp (-t)) * (fun a : ℝ => a * Real.log a) t) = fun t => t ^ (n + 1) * (Real.log t * Real.exp (-t)) :=
    by
    funext t; simp only [pow_succ]; ring
  rw [heq, gamma_log_moment, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hn0 : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp [hn0] <;> ring
private lemma normalizedGamma_integrable_id (n : ℕ) : Integrable (fun t : ℝ => t) ((ProbabilityTheory.gammaMeasure (n + 1) 1)) :=
  by
  apply Integrable.of_integral_ne_zero; rw [normalizedGamma_first_moment]; positivity
private lemma orthantExponential_integral (n : ℕ) (f : (Fin n → ℝ) → ℝ) : (∫ u, f u ∂orthantExponentialMeasure n) = ∫ u in {u : Fin n → ℝ | ∀ i, 0 ≤ u i}, Real.exp (-(∑ i, u i)) * f u :=
  by
  unfold orthantExponentialMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (Filter.Eventually.of_forall fun u => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]
private lemma orthant_exponential_weighted_product (n : ℕ) (f : Fin n → ℝ → ℝ) : (∫ u in {u : Fin n → ℝ | ∀ i, 0 ≤ u i}, Real.exp (-(∑ i, u i)) * ∏ i, f i (u i)) = ∏ i, ∫ t : ℝ in Ici 0, Real.exp (-t) * f i t := by
  classical
  let g : Fin n → ℝ → ℝ := fun i => (Ici 0).indicator (fun t => Real.exp (-t) * f i t)
  have hP : MeasurableSet {u : Fin n → ℝ | ∀ i, 0 ≤ u i} := by simpa only [Set.setOf_forall] using (isClosed_iInter (fun i : Fin n => isClosed_le continuous_const (continuous_apply i))).measurableSet
  have heq : {u : Fin n → ℝ | ∀ i, 0 ≤ u i}.indicator (fun u => Real.exp (-(∑ i, u i)) * ∏ i, f i (u i)) = fun u => ∏ i, g i (u i) :=
    by
    funext u
    by_cases hu : ∀ i, 0 ≤ u i
    · rw [Set.indicator_of_mem (show u ∈ {u : Fin n → ℝ | ∀ i, 0 ≤ u i} from hu)]
      have hgi : ∀ i, g i (u i) = Real.exp (-u i) * f i (u i) := fun i => Set.indicator_of_mem (show u i ∈ Ici (0 : ℝ) from hu i) _
      simp_rw [hgi]; rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      simp
    · rw [Set.indicator_of_notMem (show u ∉ {u : Fin n → ℝ | ∀ i, 0 ≤ u i} from hu)]
      obtain ⟨i, hi⟩ := not_forall.mp hu
      symm; apply Finset.prod_eq_zero (Finset.mem_univ i); exact Set.indicator_of_notMem (show u i ∉ Ici (0 : ℝ) from hi) _
  rw [← integral_indicator hP, heq, integral_fintype_prod_volume_eq_prod g]; apply Finset.prod_congr rfl; intro i _; exact integral_indicator measurableSet_Ici
private lemma positive_exponential_integral_id : (∫ t : ℝ in Ici 0, Real.exp (-t) * t) = 1 := by
  rw [integral_Ici_eq_integral_Ioi]
  have h := gamma_integer_integral 1
  simpa only [pow_one, mul_comm, Nat.factorial_one, Nat.cast_one] using h
private lemma orthantExponential_coordinate_moment (n : ℕ) (k : Fin n) : (∫ u, u k ∂orthantExponentialMeasure n) = 1 := by
  classical
  rw [orthantExponential_integral]
  have heq : (fun u : Fin n → ℝ => Real.exp (-(∑ i, u i)) * u k) = fun u => Real.exp (-(∑ i, u i)) * ∏ i, if i = k then u i else 1 :=
    by
    funext u
    simp
  rw [heq, orthant_exponential_weighted_product n (fun i t => if i = k then t else 1)]
  apply Finset.prod_eq_one; intro i _
  by_cases hi : i = k
  · subst i
    simp only [ite_true]; exact positive_exponential_integral_id
  · simp only [hi, ite_false, mul_one]
    rw [integral_Ici_eq_integral_Ioi]; exact integral_exp_neg_Ioi_zero
private lemma orthantExponential_coordinate_integrable (n : ℕ) (k : Fin n) : Integrable (fun u => u k) (orthantExponentialMeasure n) :=
  by
  apply integrable_of_integral_eq_one; exact orthantExponential_coordinate_moment n k
private lemma simplex_coord_le_one (n : ℕ) {y : Fin (n - 1) → ℝ} (hy : y ∈ simplexCoords n) (i : Fin (n - 1)) : y i ≤ 1 := by exact (Finset.single_le_sum (fun j _ => hy.1 j) (Finset.mem_univ i)).trans hy.2
private lemma simplexCoords_isClosed (n : ℕ) : IsClosed (simplexCoords n) :=
  by
  have hpos : IsClosed {y : Fin (n - 1) → ℝ | ∀ i, 0 ≤ y i} := by simpa only [Set.setOf_forall] using isClosed_iInter (fun i : Fin (n - 1) => isClosed_le continuous_const (continuous_apply i))
  have hsum : IsClosed {y : Fin (n - 1) → ℝ | ∑ i, y i ≤ 1} := isClosed_le (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const
  exact hpos.inter hsum
private lemma simplexCoords_isCompact (n : ℕ) : IsCompact (simplexCoords n) := by
  apply isCompact_Icc.of_isClosed_subset (simplexCoords_isClosed n); intro y hy
  exact ⟨hy.1, fun i => simplex_coord_le_one n hy i⟩
private lemma simplexPoint_continuous (n : ℕ) (i : Fin n) : Continuous (fun y : Fin (n - 1) → ℝ => (chart (n := n)) y i) :=
  by
  unfold chart
  split_ifs <;> fun_prop
private lemma simplex_linear_integrable (n : ℕ) (lam : Fin n → ℝ) : Integrable (fun y => ∑ i, lam i * (chart (n := n)) y i) (simplexMeasure n) :=
  by
  apply Integrable.smul_measure _ (by exact ENNReal.natCast_ne_top (n - 1).factorial)
  exact (continuous_finsetSum _ (fun i _ => continuous_const.mul (simplexPoint_continuous n i))).continuousOn.integrableOn_compact (simplexCoords_isCompact n)
private lemma simplex_phi_integrable (n : ℕ) (lam : Fin n → ℝ) : Integrable (fun y => (fun a : ℝ => a * Real.log a) (∑ i, lam i * (chart (n := n)) y i)) (simplexMeasure n) :=
  by
  apply Integrable.smul_measure _ (by exact ENNReal.natCast_ne_top (n - 1).factorial)
  exact (Real.continuous_mul_log.comp (continuous_finsetSum _ (fun i _ => continuous_const.mul (simplexPoint_continuous n i)))).continuousOn.integrableOn_compact (simplexCoords_isCompact n)
private lemma positiveExponential_first_moment : (∫ t : ℝ, t ∂(ProbabilityTheory.expMeasure 1)) = 1 := by
  simpa only [ProbabilityTheory.expMeasure, Nat.cast_zero, zero_add] using normalizedGamma_first_moment 0
private lemma positiveExponential_integrable_id : Integrable (fun t : ℝ => t) (ProbabilityTheory.expMeasure 1) := by exact integrable_of_integral_eq_one positiveExponential_first_moment
private lemma exponentialTail_linear_moment (n : ℕ) (lam : Fin (n + 1) → ℝ) : (∫ p, (∑ i : Fin n, lam i.castSucc * p.1 i) + lam (Fin.last n) * p.2 ∂exponentialTailMeasure n) = ∑ i, lam i :=
  by
  letI := orthantExponentialMeasure_probability n
  letI := positiveExponentialMeasure_probability
  rw [exponentialTailMeasure_eq_prod]
  have hleft : Integrable (fun p : (Fin n → ℝ) × ℝ => ∑ i, lam i.castSucc * p.1 i) ((orthantExponentialMeasure n).prod (ProbabilityTheory.expMeasure 1)) :=
    (integrable_finsetSum Finset.univ (fun i _ => (orthantExponential_coordinate_integrable n i).const_mul (lam i.castSucc))).comp_fst _
  have hright := (positiveExponential_integrable_id.const_mul (lam (Fin.last n))).comp_snd (orthantExponentialMeasure n)
  rw [integral_add hleft hright, integral_fun_fst (fun u : Fin n → ℝ => ∑ i, lam i.castSucc * u i), integral_fun_snd (fun t : ℝ => lam (Fin.last n) * t)]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  rw [integral_finsetSum Finset.univ (fun i _ => (orthantExponential_coordinate_integrable n i).const_mul (lam i.castSucc))]
  simp_rw [integral_const_mul, orthantExponential_coordinate_moment, mul_one]; rw [integral_const_mul, positiveExponential_first_moment, mul_one, Fin.sum_univ_castSucc]
private lemma simplexLinear_radial_identity (n : ℕ) (lam : Fin (n + 1) → ℝ) (u : Fin n → ℝ) (v : ℝ) (ht : v + ∑ i, u i ≠ 0) :
    (v + ∑ i, u i) * (∑ i, lam i * (chart (n := n + 1)) ((v + ∑ i, u i)⁻¹ • u) i) = (∑ i : Fin n, lam i.castSucc * u i) + lam (Fin.last n) * v :=
  by
  rw [simplexPoint_succ_snoc, Fin.sum_univ_castSucc]; simp only [Fin.snoc_castSucc, Fin.snoc_last, Pi.smul_apply, smul_eq_mul]; rw [mul_add, Finset.mul_sum]
  have hi (i : Fin n) : (v + ∑ i, u i) * (lam i.castSucc * ((v + ∑ i, u i)⁻¹ * u i)) = lam i.castSucc * u i := by field_simp [ht]
  simp_rw [hi]; congr 1; rw [← Finset.mul_sum]; field_simp [ht] <;> ring
private lemma exponentialTail_ae_domain (n : ℕ) : ∀ᵐ p ∂exponentialTailMeasure n, (∀ i, 0 ≤ p.1 i) ∧ 0 < p.2 :=
  by
  unfold exponentialTailMeasure orthantTailMeasure; apply (withDensity_absolutelyContinuous _ _).ae_le
  have hP : MeasurableSet {u : Fin n → ℝ | ∀ i, 0 ≤ u i} := by simpa only [Set.ofPred_forall] using (isClosed_iInter (fun i : Fin n => isClosed_le continuous_const (continuous_apply i))).measurableSet
  apply (Measure.ae_prod_iff_ae_ae (hP.preimage measurable_fst |>.inter (measurableSet_Ioi.preimage measurable_snd))).mpr; filter_upwards [ae_restrict_mem hP] with u hu
  exact (ae_restrict_mem measurableSet_Ioi).mono fun v hv => ⟨hu, hv⟩
private lemma simplex_linear_first_moment (n : ℕ) (lam : Fin (n + 1) → ℝ) : (∫ y, (∑ i, lam i * (chart (n := n + 1)) y i) ∂simplexMeasure (n + 1)) = (∑ i, lam i) / (n + 1) :=
  by
  letI := normalizedGammaMeasure_probability n
  letI := simplexMeasure_probability n
  have h :=
    exponential_radial_integral n (fun p : ℝ × (Fin n → ℝ) => p.1 * ∑ i, lam i * (chart (n := n + 1)) p.2 i)
      (by exact measurable_fst.mul ((continuous_finsetSum _ (fun i _ => continuous_const.mul ((simplexPoint_continuous (n + 1) i).comp continuous_snd))).measurable))
  have heq : (∫ p, (radialCoordinateMap n p).1 * (∑ i, lam i * (chart (n := n + 1)) (radialCoordinateMap n p).2 i) ∂exponentialTailMeasure n) = ∑ i, lam i :=
    by
    rw [← exponentialTail_linear_moment n lam]; apply integral_congr_ae; filter_upwards [exponentialTail_ae_domain n] with p hp
    exact simplexLinear_radial_identity n lam p.1 p.2 (ne_of_gt (add_pos_of_pos_of_nonneg hp.2 (Finset.sum_nonneg fun i _ => hp.1 i)))
  rw [heq, integral_prod_mul (fun t : ℝ => t) (fun y => ∑ i, lam i * (chart (n := n + 1)) y i), normalizedGamma_first_moment] at h
  apply (eq_div_iff (by exact Nat.cast_add_one_ne_zero n : (n : ℝ) + 1 ≠ 0)).mpr; linarith
private lemma normalizedGamma_phi_integrable (n : ℕ) : Integrable (fun t : ℝ => (fun a : ℝ => a * Real.log a) t) ((ProbabilityTheory.gammaMeasure (n + 1) 1)) :=
  by
  apply Integrable.of_integral_ne_zero; rw [normalizedGamma_phi_moment]; apply mul_ne_zero (by exact Nat.cast_add_one_ne_zero n)
  have H : (1 : ℚ) ≤ harmonic (n + 1) :=
    by
    have h := Finset.single_le_sum (s := Finset.range (n + 1)) (a := 0) (f := fun i : ℕ => ((i + 1 : ℕ) : ℚ)⁻¹) (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg _)) (by simp)
    simpa [harmonic] using h
  have Hreal : (1 : ℝ) ≤ (harmonic (n + 1) : ℝ) := by exact_mod_cast H
  nlinarith [Real.eulerMascheroniConstant_lt_two_thirds]
private lemma phi_product_integral_ae {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ] (μ : Measure Ω) (ν : Measure Λ) [SFinite μ] [SFinite ν] (T : Ω → ℝ) (F : Λ → ℝ) (hTi : Integrable T μ) (hFi : Integrable F ν) (hTphi : Integrable (fun t => (fun a : ℝ => a * Real.log a) (T t)) μ) (hFphi : Integrable (fun y => (fun a : ℝ => a * Real.log a) (F y)) ν) :
    (∫ p, (fun a : ℝ => a * Real.log a) (T p.1 * F p.2) ∂μ.prod ν) = (∫ t, T t ∂μ) * (∫ y, (fun a : ℝ => a * Real.log a) (F y) ∂ν) + (∫ t, (fun a : ℝ => a * Real.log a) (T t) ∂μ) * (∫ y, F y ∂ν) :=
  by
  have heq : (fun p : Ω × Λ => (fun a : ℝ => a * Real.log a) (T p.1 * F p.2)) =ᵐ[μ.prod ν] fun p => T p.1 * (fun a : ℝ => a * Real.log a) (F p.2) + (fun a : ℝ => a * Real.log a) (T p.1) * F p.2 :=
    by
    apply Filter.Eventually.of_forall
    intro p
    change T p.1 * F p.2 * Real.log (T p.1 * F p.2) = T p.1 * (F p.2 * Real.log (F p.2)) + (T p.1 * Real.log (T p.1)) * F p.2
    rw [phi_mul_nonneg]; ring
  rw [integral_congr_ae heq, integral_add (hTi.mul_prod hFphi) (hTphi.mul_prod hFi)]
  exact congrArg₂ (· + ·) (integral_prod_mul (μ := μ) (ν := ν) T (fun y => (fun a : ℝ => a * Real.log a) (F y))) (integral_prod_mul (μ := μ) (ν := ν) (fun t => (fun a : ℝ => a * Real.log a) (T t)) F)
private lemma exponential_phi_radial_factorization (n : ℕ) (lam : Fin (n + 1) → ℝ) (htrace : ∑ i, lam i = 1) :
    (∫ p, (fun a : ℝ => a * Real.log a) ((∑ i : Fin n, lam i.castSucc * p.1 i) + lam (Fin.last n) * p.2) ∂exponentialTailMeasure n) =
      (n + 1) * (∫ y, (fun a : ℝ => a * Real.log a) (∑ i, lam i * (chart (n := n + 1)) y i) ∂simplexMeasure (n + 1)) + (harmonic (n + 1) : ℝ) - Real.eulerMascheroniConstant :=
  by
  letI := normalizedGammaMeasure_probability n
  letI := simplexMeasure_probability n
  have h :=
    exponential_radial_integral n (fun p : ℝ × (Fin n → ℝ) => (fun a : ℝ => a * Real.log a) (p.1 * ∑ i, lam i * (chart (n := n + 1)) p.2 i))
      (Real.continuous_mul_log.measurable.comp (measurable_fst.mul ((continuous_finsetSum _ (fun i _ => continuous_const.mul ((simplexPoint_continuous (n + 1) i).comp continuous_snd))).measurable)))
  have heq :
    (∫ p, (fun a : ℝ => a * Real.log a) ((radialCoordinateMap n p).1 * (∑ i, lam i * (chart (n := n + 1)) (radialCoordinateMap n p).2 i)) ∂exponentialTailMeasure n) =
      ∫ p, (fun a : ℝ => a * Real.log a) ((∑ i : Fin n, lam i.castSucc * p.1 i) + lam (Fin.last n) * p.2) ∂exponentialTailMeasure n :=
    by
    apply integral_congr_ae; filter_upwards [exponentialTail_ae_domain n] with p hp
    exact congrArg (fun a : ℝ => a * Real.log a) (simplexLinear_radial_identity n lam p.1 p.2 (ne_of_gt (add_pos_of_pos_of_nonneg hp.2 (Finset.sum_nonneg fun i _ => hp.1 i))))
  rw [heq] at h
  rw [h,
    phi_product_integral_ae ((ProbabilityTheory.gammaMeasure (n + 1) 1)) (simplexMeasure (n + 1)) (fun t : ℝ => t) (fun y => ∑ i, lam i * (chart (n := n + 1)) y i) (normalizedGamma_integrable_id n) (simplex_linear_integrable _ lam) (normalizedGamma_phi_integrable n) (simplex_phi_integrable _ lam),
    normalizedGamma_first_moment, normalizedGamma_phi_moment, simplex_linear_first_moment, htrace]
  have hn0 : (n : ℝ) + 1 ≠ 0 := by exact Nat.cast_add_one_ne_zero n
  field_simp [hn0] <;> ring
private lemma subentropySpectrum_exponential_representation (n : ℕ) (lam : Fin (n + 1) → ℝ) (htrace : ∑ i, lam i = 1) :
    subentropySpectrum (n + 1) lam = 1 - Real.eulerMascheroniConstant - ∫ p, (fun a : ℝ => a * Real.log a) ((∑ i : Fin n, lam i.castSucc * p.1 i) + lam (Fin.last n) * p.2) ∂exponentialTailMeasure n :=
  by
  rw [subentropySpectrum_as_simplex_phi, exponential_phi_radial_factorization n lam htrace, harmonic_eq_one_add_C (n + 1) (by exact Nat.zero_lt_succ n)]
  push_cast
  ring
private lemma orthantExponential_eq_pi (n : ℕ) : orthantExponentialMeasure n = Measure.pi (fun _ : Fin n => (ProbabilityTheory.expMeasure 1)) :=
  by
  letI := positiveExponentialMeasure_probability
  rw [show Measure.pi (fun _ : Fin n => (ProbabilityTheory.expMeasure 1)) = Measure.pi (fun _ : Fin n => (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t => ENNReal.ofReal (Real.exp (-t)))) from (by simp only [expMeasure_one_density]),
    pi_withDensity_fin (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ))) (fun _ t => ENNReal.ofReal (Real.exp (-t))) (fun _ => by fun_prop)]
  have hbase : Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ))) = volume.restrict {u : Fin n → ℝ | ∀ i, 0 ≤ u i} :=
    by
    simp_rw [restrict_Ioi_eq_restrict_Ici]; rw [← Measure.restrict_pi_pi, ← volume_pi]; congr 1; ext u; simp [Pi.le_def]
  rw [hbase]; unfold orthantExponentialMeasure; congr 1; funext u
  rw [← Finset.sum_neg_distrib, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.exp_nonneg _)]
private lemma exponential_snoc_split_map (n : ℕ) : Measure.map (fun z : Fin (n + 1) → ℝ => (fun i : Fin n => z i.castSucc, z (Fin.last n))) (Measure.pi (fun _ : Fin (n + 1) => (ProbabilityTheory.expMeasure 1))) = exponentialTailMeasure n :=
  by
  letI := positiveExponentialMeasure_probability
  rw [exponentialTailMeasure_eq_prod, orthantExponential_eq_pi]
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (ProbabilityTheory.expMeasure 1)) (Fin.last n)).map_eq
  have heq : (fun z : Fin (n + 1) → ℝ => (fun i : Fin n => z i.castSucc, z (Fin.last n))) = Prod.swap ∘ MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n) :=
    by
    funext z; apply Prod.ext
    · funext i
      simp [MeasurableEquiv.piFinSuccAbove, Fin.init]
    · rfl
  rw [heq, ← Measure.map_map measurable_swap (by exact MeasurableEquiv.measurable (MeasurableEquiv.piFinSuccAbove (fun x => ℝ) (Fin.last n))), h, Measure.prod_swap]
private lemma subentropySpectrum_exponential_pi_representation (n : ℕ) (lam : Fin (n + 1) → ℝ) (htrace : ∑ i, lam i = 1) :
    subentropySpectrum (n + 1) lam = 1 - Real.eulerMascheroniConstant - ∫ z : Fin (n + 1) → ℝ, (fun a : ℝ => a * Real.log a) (∑ i, lam i * z i) ∂Measure.pi (fun _ => (ProbabilityTheory.expMeasure 1)) :=
  by
  rw [subentropySpectrum_exponential_representation n lam htrace]; congr 1
  rw [← exponential_snoc_split_map n,
    integral_map (by fun_prop) (by exact (Real.continuous_mul_log.comp ((continuous_finsetSum _ (fun i _ => continuous_const.mul ((continuous_apply i).comp continuous_fst))).add (continuous_const.mul continuous_snd))).aestronglyMeasurable)]
  congr 1; funext z; congr 1
  exact (Fin.sum_univ_castSucc (fun i => lam i * z i)).symm
open Matrix MeasureTheory ProbabilityTheory Set
variable {I : Type} [Fintype I]
private lemma square_pos_image : (fun r : ℝ => r ^ 2) '' Ioi 0 = Ioi 0 :=
  Real.sqPartialHomeomorph.image_source_eq_target
private lemma square_positive_lintegral (f : ℝ → ℝ≥0∞) : (∫⁻ r : ℝ in Ioi 0, ENNReal.ofReal r * f (r ^ 2)) = (2 : ℝ≥0∞)⁻¹ * ∫⁻ t : ℝ in Ioi 0, f t :=
  by
  have hderiv : ∀ r : ℝ, HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by
    intro r
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hasDerivAt_pow 2 r
  have hinj : Set.InjOn (fun r : ℝ => r ^ 2) (Ioi 0) := by
    intro r hr s hs hrs
    exact (pow_left_strictMonoOn₀ (M₀ := ℝ) (by decide : (2 : ℕ) ≠ 0)).injOn (show 0 ≤ r from le_of_lt (show 0 < r from hr)) (show 0 ≤ s from le_of_lt (show 0 < s from hs)) hrs
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi (fun r _ => (hderiv r).hasDerivWithinAt) hinj f
  rw [square_pos_image] at h
  have hright : (∫⁻ r : ℝ in Ioi 0, ENNReal.ofReal |2 * r| * f (r ^ 2)) = 2 * ∫⁻ r : ℝ in Ioi 0, ENNReal.ofReal r * f (r ^ 2) :=
    by
    rw [← lintegral_const_mul' (2 : ℝ≥0∞) _ (by exact Ne.symm ENNReal.top_ne_ofNat)]; apply setLIntegral_congr_fun measurableSet_Ioi; intro r hr
    dsimp only
    change (0 : ℝ) < r at hr; rw [abs_of_pos (mul_pos (by exact zero_lt_two) hr), ENNReal.ofReal_mul (by exact zero_le_two)]; simp only [ENNReal.ofReal_ofNat, mul_assoc]
  rw [hright] at h
  calc
    _ = (2 : ℝ≥0∞)⁻¹ * (2 * ∫⁻ r : ℝ in Ioi 0, ENNReal.ofReal r * f (r ^ 2)) := by simp only [← mul_assoc, ENNReal.inv_mul_cancel (by exact Ne.symm (NeZero.ne' 2) : (2 : ℝ≥0∞) ≠ 0) (by exact Ne.symm ENNReal.top_ne_ofNat), one_mul]
    _ = _ := by rw [← h]
private lemma complex_sqnorm_radial_lintegral (f : ℝ → ℝ≥0∞) (hf : Measurable f) : (∫⁻ z : ℂ, f (‖z‖ ^ 2)) = ENNReal.ofReal Real.pi * ∫⁻ t : ℝ in Ioi 0, f t := by
  calc
    _ = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, ENNReal.ofReal p.1 * f (p.1 ^ 2) :=
      by
      rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]; simp_rw [Complex.norm_polarCoord_symm, sq_abs]
      rfl
    _ = (∫⁻ r : ℝ in Ioi 0, ENNReal.ofReal r * f (r ^ 2)) * ENNReal.ofReal (2 * Real.pi) :=
      by
      change (∫⁻ p, ENNReal.ofReal p.1 * f (p.1 ^ 2) ∂(volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi)) = _; rw [← Measure.prod_restrict]
      have hmeas : AEMeasurable (fun r : ℝ => ENNReal.ofReal r * f (r ^ 2)) (volume.restrict (Ioi 0)) := by fun_prop
      have hprod := lintegral_prod_mul (μ := volume.restrict (Ioi (0 : ℝ))) (ν := volume.restrict (Ioo (-Real.pi) Real.pi)) hmeas (show AEMeasurable (fun _ : ℝ => (1 : ℝ≥0∞)) _ from measurable_const.aemeasurable)
      simp only [mul_one] at hprod; rw [hprod]; simp [Real.volume_Ioo, sub_neg_eq_add, two_mul]
    _ = _ := by
      rw [square_positive_lintegral]
      rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
      simp only [ENNReal.ofReal_ofNat]
      calc
        _ = ((2 : ℝ≥0∞)⁻¹ * 2) * (ENNReal.ofReal Real.pi * ∫⁻ t : ℝ in Ioi 0, f t) := by ring
        _ = _ := by rw [ENNReal.inv_mul_cancel (by exact Ne.symm (NeZero.ne' 2)) (by exact Ne.symm ENNReal.top_ne_ofNat), one_mul]
private lemma complex_sqnorm_volume_map : Measure.map (fun z : ℂ => ‖z‖ ^ 2) volume = ENNReal.ofReal Real.pi • volume.restrict (Ioi 0) :=
  by
  apply Measure.ext_of_lintegral; intro f hf; rw [lintegral_map hf (by fun_prop), lintegral_smul_measure]; exact complex_sqnorm_radial_lintegral f hf
private lemma map_withDensity_composed {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ] (μ : Measure Ω) (f : Ω → Λ) (hf : Measurable f) (w : Λ → ℝ≥0∞) (hw : Measurable w) :
    Measure.map f (μ.withDensity (w ∘ f)) = (Measure.map f μ).withDensity w := by
  apply Measure.ext_of_lintegral; intro F hF
  rw [lintegral_map hF hf, lintegral_withDensity_eq_lintegral_mul μ (hw.comp hf) (g := fun a => F (f a)) (hF.comp hf), lintegral_withDensity_eq_lintegral_mul _ hw hF, lintegral_map (hw.mul hF) hf]
  rfl
private lemma stdGaussian_complex_eq_map_prod : stdGaussian ℂ = Measure.map Complex.measurableEquivRealProd.symm ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
  by
  rw [stdGaussian_eq_map_pi_orthonormalBasis Complex.orthonormalBasisOneI]
  have heq : (fun x : Fin 2 → ℝ => ∑ i, x i • Complex.orthonormalBasisOneI i) = Complex.measurableEquivRealProd.symm ∘ MeasurableEquiv.finTwoArrow :=
    by
    funext x; apply Complex.ext <;> simp [Fin.sum_univ_two, Complex.coe_orthonormalBasisOneI, Complex.real_smul]
  rw [heq, ← Measure.map_map (by exact MeasurableEquiv.measurable Complex.measurableEquivRealProd.symm) (by exact MeasurableEquiv.measurable MeasurableEquiv.finTwoArrow), (measurePreserving_finTwoArrow (gaussianReal 0 1)).map_eq]
private lemma stdGaussian_complex_density_product : stdGaussian ℂ = volume.withDensity (fun z : ℂ => gaussianPDF 0 1 z.re * gaussianPDF 0 1 z.im) :=
  by
  rw [stdGaussian_complex_eq_map_prod, gaussianReal_of_var_ne_zero 0 (by exact Ne.symm (zero_ne_one' NNReal)), prod_withDensity (by exact measurable_gaussianPDF 0 1) (by exact measurable_gaussianPDF 0 1)]
  let w : ℂ → ℝ≥0∞ := fun z => gaussianPDF 0 1 z.re * gaussianPDF 0 1 z.im
  have hw : Measurable w := by fun_prop
  have hd : (fun p : ℝ × ℝ => gaussianPDF 0 1 p.1 * gaussianPDF 0 1 p.2) = w ∘ Complex.measurableEquivRealProd.symm := rfl
  rw [hd, map_withDensity_composed _ _ Complex.measurableEquivRealProd.symm.measurable _ hw]; change (Measure.map Complex.measurableEquivRealProd.symm (volume : Measure (ℝ × ℝ))).withDensity w = _; rw [Complex.volume_preserving_equiv_real_prod.symm.map_eq]
private lemma gaussianPDF_complex_product (z : ℂ) : gaussianPDF 0 1 z.re * gaussianPDF 0 1 z.im = ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.exp (-‖z‖ ^ 2 / 2)) :=
  by
  rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]; congr 1; simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  have hS : (Real.sqrt (2 * Real.pi)) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  have hE : Real.exp (-z.re ^ 2 / 2) * Real.exp (-z.im ^ 2 / 2) = Real.exp (-‖z‖ ^ 2 / 2) := by
    rw [← Real.exp_add]; congr 1; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  calc
    _ = ((Real.sqrt (2 * Real.pi)) ^ 2)⁻¹ * (Real.exp (-z.re ^ 2 / 2) * Real.exp (-z.im ^ 2 / 2)) := by ring
    _ = _ := by rw [hS, hE]
private lemma stdGaussian_complex_density : stdGaussian ℂ = volume.withDensity (fun z : ℂ => ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.exp (-‖z‖ ^ 2 / 2))) :=
  by
  rw [stdGaussian_complex_density_product]; congr 1; funext z; exact gaussianPDF_complex_product z
private lemma complex_half_sqnorm_volume_map : Measure.map (fun z : ℂ => ‖z‖ ^ 2 / 2) volume = ENNReal.ofReal (2 * Real.pi) • volume.restrict (Ioi 0) :=
  by
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.smul (Units.mk0 ((1 : ℝ) / 2) (by norm_num))).toMeasurableEquiv
  have he : (e : ℝ → ℝ) = fun t => (1 / 2 : ℝ) * t := rfl
  have hpre : e ⁻¹' Ioi (0 : ℝ) = Ioi 0 := by
    ext t; change (0 : ℝ) < (1 / 2 : ℝ) * t ↔ 0 < t; constructor <;> intro h <;> linarith
  have hmap : Measure.map e volume = (2 : ℝ≥0∞) • volume := by
    rw [he]; change Measure.map (((1 : ℝ) / 2) • ·) volume = _; rw [Measure.map_addHaar_smul volume (by norm_num)]; norm_num
  have hrestrict : Measure.map e (volume.restrict (Ioi (0 : ℝ))) = (2 : ℝ≥0∞) • volume.restrict (Ioi 0) := by rw [← hpre, ← e.measurableEmbedding.restrict_map, hmap, Measure.restrict_smul, hpre]
  have hcomp : (fun z : ℂ => ‖z‖ ^ 2 / 2) = e ∘ (fun z : ℂ => ‖z‖ ^ 2) := by
    funext z; change ‖z‖ ^ 2 / 2 = (1 / 2 : ℝ) * ‖z‖ ^ 2; ring
  rw [hcomp, ← Measure.map_map e.measurable (by fun_prop), complex_sqnorm_volume_map, Measure.map_smul _ e.measurable.aemeasurable, hrestrict, smul_smul]; congr 1; rw [ENNReal.ofReal_mul (by exact zero_le_two : (0 : ℝ) ≤ 2)]; simp [mul_comm]
private lemma stdGaussian_complex_half_sqnorm_map : Measure.map (fun z : ℂ => ‖z‖ ^ 2 / 2) (stdGaussian ℂ) = (volume.restrict (Ioi 0)).withDensity (fun t : ℝ => ENNReal.ofReal (Real.exp (-t))) :=
  by
  let q : ℂ → ℝ := fun z => ‖z‖ ^ 2 / 2
  let w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.exp (-t))
  have hq : Measurable q := by fun_prop
  have hw : Measurable w := by fun_prop
  have hd : (fun z : ℂ => ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.exp (-‖z‖ ^ 2 / 2))) = w ∘ q := by
    funext z; simp only [w, q, Function.comp_apply, neg_div]
  rw [stdGaussian_complex_density, hd, map_withDensity_composed volume q hq w hw]; rw [show Measure.map q volume = ENNReal.ofReal (2 * Real.pi) • volume.restrict (Ioi 0) from complex_half_sqnorm_volume_map]; rw [withDensity_smul_measure, ← withDensity_smul _ hw]; congr 1; funext t; change ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.exp (-t)) = _
  rw [← ENNReal.ofReal_mul (by positivity), ← mul_assoc, mul_inv_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_mul]
private lemma stdGaussian_complex_pi_map : (Measure.pi (fun _ : I => stdGaussian ℂ)).map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℂ I) :=
  by
  apply Measure.ext_of_charFun (E := EuclideanSpace ℂ I)
  ext t; simp_rw [charFun_pi, charFun_stdGaussian, ← Complex.exp_sum]; congr 1; simp only [← Finset.sum_div, ← Finset.sum_neg_distrib]
  have hnorm := congrArg (fun x : ℝ => -(x : ℂ) / 2) (EuclideanSpace.norm_sq_eq t)
  simpa only [Complex.ofReal_sum, Complex.ofReal_pow, Finset.sum_div, Finset.sum_neg_distrib] using hnorm.symm
private lemma stdGaussian_squared_coordinates_map : Measure.map (fun z : EuclideanSpace ℂ I => fun i => ‖z i‖ ^ 2 / 2) (stdGaussian (EuclideanSpace ℂ I)) = Measure.pi (fun _ : I => ProbabilityTheory.expMeasure 1) :=
  by
  rw [expMeasure_one_density]; rw [← stdGaussian_complex_pi_map, Measure.map_map (by fun_prop) (by exact WithLp.measurable_toLp 2 (I → ℂ))]
  have hcomp : ((fun z : EuclideanSpace ℂ I => fun i => ‖z i‖ ^ 2 / 2) ∘ WithLp.toLp 2) = fun z : I → ℂ => fun i => ‖z i‖ ^ 2 / 2 := rfl
  rw [hcomp, Measure.pi_map_pi (f := fun _ : I => fun z : ℂ => ‖z‖ ^ 2 / 2) (fun _ : I => by fun_prop)]
  simp_rw [stdGaussian_complex_half_sqnorm_map]
open MeasureTheory ProbabilityTheory Set
private lemma gaussian_squared_coordinate_integral (n : ℕ) (F : (Fin n → ℝ) → ℝ) (hF : Measurable F) :
    (∫ z : EuclideanSpace ℂ (Fin n), F (fun i => ‖z i‖ ^ 2 / 2) ∂stdGaussian (EuclideanSpace ℂ (Fin n))) = ∫ z : Fin n → ℝ, F z ∂Measure.pi (fun _ => (ProbabilityTheory.expMeasure 1)) :=
  by
  have hmap : Measure.map (fun z : EuclideanSpace ℂ (Fin n) => fun i => ‖z i‖ ^ 2 / 2) (stdGaussian (EuclideanSpace ℂ (Fin n))) = Measure.pi (fun _ : Fin n => (ProbabilityTheory.expMeasure 1)) := stdGaussian_squared_coordinates_map
  rw [← hmap]; exact (integral_map (by fun_prop) hF.aestronglyMeasurable).symm
private lemma subentropySpectrum_gaussian_half_representation (n : ℕ) (lam : Fin (n + 1) → ℝ) (htrace : ∑ i, lam i = 1) :
    subentropySpectrum (n + 1) lam = 1 - Real.eulerMascheroniConstant - ∫ z : EuclideanSpace ℂ (Fin (n + 1)), (fun a : ℝ => a * Real.log a) (∑ i, lam i * (‖z i‖ ^ 2 / 2)) ∂stdGaussian (EuclideanSpace ℂ (Fin (n + 1))) := by
  rw [subentropySpectrum_exponential_pi_representation n lam htrace,
    gaussian_squared_coordinate_integral (n + 1) (fun z : Fin (n + 1) → ℝ => (fun a : ℝ => a * Real.log a) (∑ i, lam i * z i))
      (Real.continuous_mul_log.measurable.comp (Finset.measurable_sum _ (fun i _ => measurable_const.mul (measurable_pi_apply i))))]
open scoped InnerProductSpace
variable {I : Type} [Fintype I] [DecidableEq I]
private lemma spectralCoordinates_quadratic (R : Matrix I I ℂ) (hR : R.IsHermitian) (z : EuclideanSpace ℂ I) :
    (inner ℂ z (Matrix.toEuclideanLin R z)).re = ∑ i, hR.eigenvalues₀ i * ‖((isSymmetric_toEuclideanLin_iff.mpr hR).eigenvectorBasis finrank_euclideanSpace).repr z i‖ ^ 2 :=
  by
  have h := (D5.S3.Quantum.Subentropy.GaussianQuadratic.spectral_transport hR).1 (hR.eigenvectorBasis.repr z)
  simp only [LinearIsometryEquiv.symm_apply_apply] at h
  let e : Fin (Fintype.card I) ≃ I := Fintype.equivOfCardEq (Fintype.card_fin _)
  rw [← e.sum_comp] at h
  simp only [Matrix.IsHermitian.eigenvalues, Matrix.IsHermitian.eigenvectorBasis, e, OrthonormalBasis.repr_reindex, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe, Equiv.symm_apply_apply,
    ← Complex.sq_norm] at h
  change (inner ℂ z (Matrix.toEuclideanLin R z)).re / 2 = _ at h; linarith
private lemma spectralCoordinates_gaussian_map (R : Matrix I I ℂ) (hR : R.IsHermitian) :
    Measure.map (((isSymmetric_toEuclideanLin_iff.mpr hR).eigenvectorBasis finrank_euclideanSpace).repr) (stdGaussian (EuclideanSpace ℂ I)) = stdGaussian (EuclideanSpace ℂ (Fin (Fintype.card I))) := by
  exact
    stdGaussian_map
      { (((isSymmetric_toEuclideanLin_iff.mpr hR).eigenvectorBasis finrank_euclideanSpace).repr).toLinearEquiv.restrictScalars ℝ with
        norm_map' := (((isSymmetric_toEuclideanLin_iff.mpr hR).eigenvectorBasis finrank_euclideanSpace).repr).norm_map }
private lemma gaussian_matrix_spectral_integral (R : Matrix I I ℂ) (hR : R.IsHermitian) :
    (∫ z : EuclideanSpace ℂ I, (fun a : ℝ => a * Real.log a) ((inner ℂ z (Matrix.toEuclideanLin R z)).re / 2) ∂stdGaussian (EuclideanSpace ℂ I)) =
      ∫ y : EuclideanSpace ℂ (Fin (Fintype.card I)), (fun a : ℝ => a * Real.log a) ((∑ i, hR.eigenvalues₀ i * ‖y i‖ ^ 2) / 2) ∂stdGaussian (EuclideanSpace ℂ (Fin (Fintype.card I))) :=
  by
  calc
    _ = ∫ z : EuclideanSpace ℂ I, (fun a : ℝ => a * Real.log a) ((∑ i, hR.eigenvalues₀ i * ‖((isSymmetric_toEuclideanLin_iff.mpr hR).eigenvectorBasis finrank_euclideanSpace).repr z i‖ ^ 2) / 2) ∂stdGaussian (EuclideanSpace ℂ I) := by
      simp_rw [spectralCoordinates_quadratic R hR]
    _ = _ := by
      rw [← spectralCoordinates_gaussian_map R hR]
      exact
        (integral_map (((isSymmetric_toEuclideanLin_iff.mpr hR).eigenvectorBasis finrank_euclideanSpace).repr).continuous.measurable.aemeasurable
            (Real.continuous_mul_log.comp ((continuous_finsetSum _ (fun i _ => continuous_const.mul ((PiLp.continuous_apply 2 _ i).norm.pow 2))).div_const 2)).aestronglyMeasurable).symm
open scoped InnerProductSpace ComplexOrder
private lemma eigenvalues0_sum (R : Matrix I I ℂ) (hR : R.IsHermitian) : ∑ i, hR.eigenvalues₀ i = R.trace.re :=
  by
  rw [hR.trace_eq_sum_eigenvalues, Complex.re_sum]
  let e : Fin (Fintype.card I) ≃ I := Fintype.equivOfCardEq (Fintype.card_fin _)
  change (∑ i, hR.eigenvalues₀ i) = ∑ i : I, hR.eigenvalues₀ (e.symm i); exact (Equiv.sum_comp e.symm hR.eigenvalues₀).symm
private lemma trace_one_card_pos (R : Matrix I I ℂ) (htrace : R.trace = 1) : 0 < Fintype.card I := by
  by_contra h
  have hcard : Fintype.card I = 0 := Nat.eq_zero_of_not_pos h
  letI := Fintype.card_eq_zero_iff.mp hcard
  simp [Matrix.trace] at htrace
private lemma subentropySpectrum_gaussian_half_pos (N : ℕ) (hN : 0 < N) (lam : Fin N → ℝ) (htrace : ∑ i, lam i = 1) :
    subentropySpectrum N lam = 1 - Real.eulerMascheroniConstant - ∫ z : EuclideanSpace ℂ (Fin N), (fun a : ℝ => a * Real.log a) ((∑ i, lam i * ‖z i‖ ^ 2) / 2) ∂stdGaussian (EuclideanSpace ℂ (Fin N)) := by
  cases N with
  | zero => simp at hN
  | succ n => simpa only [Finset.sum_div, mul_div_assoc] using subentropySpectrum_gaussian_half_representation n lam htrace
private lemma subentropy_matrix_gaussian_half (R : Matrix I I ℂ) (hR : R.IsHermitian) (htrace : R.trace = 1) :
    subentropy R hR = 1 - Real.eulerMascheroniConstant - ∫ z : EuclideanSpace ℂ I, (fun a : ℝ => a * Real.log a) ((inner ℂ z (Matrix.toEuclideanLin R z)).re / 2) ∂stdGaussian (EuclideanSpace ℂ I) :=
  by
  have hsum : ∑ i, hR.eigenvalues₀ i = 1 := by rw [eigenvalues0_sum, htrace]; rfl
  unfold subentropy; rw [subentropySpectrum_gaussian_half_pos _ (trace_one_card_pos R htrace) _ hsum]
  have h := gaussian_matrix_spectral_integral R hR
  exact congrArg (fun x => 1 - Real.eulerMascheroniConstant - x) h.symm
open scoped InnerProductSpace ComplexOrder MatrixOrder CStarAlgebra
open D5.S3.Quantum.Subentropy.GaussianQuadratic
private lemma exponential_phi_integral : (∫ t : ℝ, (fun a : ℝ => a * Real.log a) t ∂(ProbabilityTheory.expMeasure 1)) = 1 - Real.eulerMascheroniConstant :=
  by
  simpa [ProbabilityTheory.expMeasure, harmonic] using normalizedGamma_phi_moment 0
private lemma baseline_integral {I : Type} [Fintype I] [DecidableEq I] (i₀ : I) :
    (∫ z : (I × Fin 2) → ℝ, Real.negMulLog (((z (i₀, 0)) ^ 2 + (z (i₀, 1)) ^ 2) / 2) ∂Measure.pi (fun _ => gaussianReal 0 1)) = Real.eulerMascheroniConstant - 1 :=
  by
  let γ := Measure.pi (fun _ : I × Fin 2 => gaussianReal 0 1)
  have hq : Measurable (fun z : EuclideanSpace ℂ I => Real.negMulLog (‖z i₀‖ ^ 2 / 2)) := by fun_prop
  have hG : Measurable (complexGaussianCoordinates : ((I × Fin 2) → ℝ) → EuclideanSpace ℂ I) := by
    unfold complexGaussianCoordinates; simp_rw [Complex.mk_eq_add_mul_I]
    fun_prop
  have h₁ := integral_map hG.aemeasurable hq.aestronglyMeasurable (μ := γ)
  rw [complex_coordinate_transport.1] at h₁; simp_rw [Complex.sq_norm, complex_coordinate_transport.2] at h₁; rw [← h₁]
  have h₂ :=
    integral_map (by fun_prop : Measurable (fun z : EuclideanSpace ℂ I => fun i => ‖z i‖ ^ 2 / 2)).aemeasurable ((Real.continuous_negMulLog.measurable.comp (measurable_pi_apply i₀)).aestronglyMeasurable) (μ :=
      stdGaussian (EuclideanSpace ℂ I))
  rw [stdGaussian_squared_coordinates_map] at h₂; simp only [Function.comp_apply, Complex.sq_norm] at h₂; rw [← h₂]
  letI := positiveExponentialMeasure_probability
  change (∫ y : I → ℝ, Real.negMulLog (y i₀) ∂Measure.pi (fun _ => (ProbabilityTheory.expMeasure 1))) = _
  have heval := integral_map (measurable_pi_apply i₀).aemeasurable Real.continuous_negMulLog.aestronglyMeasurable (μ := Measure.pi (fun _ : I => (ProbabilityTheory.expMeasure 1)))
  rw [(measurePreserving_eval (fun _ : I => (ProbabilityTheory.expMeasure 1)) i₀).map_eq] at heval
  rw [← heval]
  have hneg : Real.negMulLog = -(fun a : ℝ => a * Real.log a) := by funext t; simp [Real.negMulLog, neg_mul]
  rw [hneg, integral_neg', exponential_phi_integral]; ring
private lemma source_eq_determinant {I : Type} [Fintype I] [DecidableEq I] (R : Matrix I I ℂ) (hR : R.PosSemidef) (ht : R.trace = 1) : subentropy R hR.isHermitian = D5.S3.Quantum.Subentropy.Basic.matrixSubentropy R :=
  by
  have hcard := trace_one_card_pos R ht
  let i₀ : I := Classical.choice (Fintype.card_pos_iff.mp hcard)
  have h := (D5.S3.Quantum.Subentropy.GaussianMatrix.matrix_subentropy_gaussian_entropy R hR ht i₀).2
  rw [baseline_integral] at h; rw [subentropy_matrix_gaussian_half R hR.isHermitian ht, h]
  have heq : (fun z : EuclideanSpace ℂ I => Real.negMulLog (gaussianQuadratic R z)) = -(fun z => (fun a : ℝ => a * Real.log a) ((inner ℂ z (Matrix.toEuclideanLin R z)).re / 2)) :=
    by
    funext z; simp [Real.negMulLog, gaussianQuadratic, neg_mul]
  rw [heq]; rw [integral_neg']; ring
open Matrix
open scoped ComplexOrder MatrixOrder CStarAlgebra Kronecker
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.ClassicalQuantumGram
open D5.S3.Quantum.Subentropy.GuessingProbability
open D5.S3.Quantum.Information.OrthogonalRecordEntropy
open D5.S3.Quantum.Information.PartialTraceMutualInformation
private theorem normalize_ensemble {X B : Type} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B] (A : X → Matrix B B ℂ) (hA : ∀ x, (A x).PosSemidef) (ht : ∑ x, (A x).trace = 1) :
    ∃ (p : X → ℝ) (_ : ∀ x, 0 ≤ p x) (_ : ∑ x, p x = 1) (ρ : X → DensityState B), ∀ x, p x • CStarMatrix.ofMatrix.symm (ρ x).1 = A x := by
  classical
  let p : X → ℝ := fun x => (A x).trace.re
  have hp : ∀ x, 0 ≤ p x := fun x => (Complex.nonneg_iff.mp (hA x).trace_nonneg).1
  have htrace (x : X) : (A x).trace = (p x : ℂ) := by
    apply Complex.ext
    · rfl
    · exact ((Complex.nonneg_iff.mp (hA x).trace_nonneg).2).symm
  have hs : ∑ x, p x = 1 := by simpa [p, Complex.re_sum] using congrArg Complex.re ht
  let σ : DensityState B :=
    ⟨CStarMatrix.ofMatrix (∑ x, A x), map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (Matrix.posSemidef_sum _ (fun x _ => hA x)).nonneg,
      by
      change Matrix.trace (∑ x, A x) = 1
      simpa using ht⟩
  have hσ (x : X) (hx : p x ≠ 0) : Matrix.trace ((p x)⁻¹ • A x) = 1 := by
    rw [Matrix.trace_smul, htrace, Complex.real_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hx]
    rfl
  have hex (x : X) : ∃ r : DensityState B, p x • CStarMatrix.ofMatrix.symm r.1 = A x := by
    by_cases hx : p x = 0
    · have hz : A x = 0 := (hA x).trace_eq_zero_iff.mp (by exact (htrace x).trans (congrArg Complex.ofReal hx))
      refine ⟨σ, ?_⟩; rw [hx, zero_smul, hz]
    · refine ⟨⟨CStarMatrix.ofMatrix ((p x)⁻¹ • A x), map_nonneg CStarMatrix.ofMatrixStarAlgEquiv ((hA x).smul (inv_nonneg.mpr (hp x))).nonneg, hσ x hx⟩, ?_⟩
      change p x • ((p x)⁻¹ • A x) = A x; rw [smul_smul, mul_inv_cancel₀ hx, one_smul]
  choose ρ hρ using hex
  exact ⟨p, hp, hs, ρ, hρ⟩
private theorem determinant_reindex {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] (R : Matrix I I ℂ) (e : J ≃ I) : matrixSubentropy (R.submatrix e e) = matrixSubentropy R :=
  by
  unfold matrixSubentropy subentropyKernel; apply MeasureTheory.integral_congr_ae; apply Filter.Eventually.of_forall; intro t
  have h : (1 : Matrix J J ℂ) + (t⁻¹ : ℝ) • R.submatrix e e = (1 + (t⁻¹ : ℝ) • R).submatrix e e := by
    ext i j; simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.submatrix_apply]; rw [Matrix.one_apply, Matrix.one_apply]; simp only [EmbeddingLike.apply_eq_iff_eq]
  dsimp only
  rw [h, Matrix.det_submatrix_equiv_self]
private theorem determinant_cq_bound {X B : Type} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B] (A : X → Matrix B B ℂ) (hA : ∀ x, (A x).PosSemidef) (ht : ∑ x, (A x).trace = 1) :
    matrixSubentropy (blockDiagonal A) - matrixSubentropy (∑ x, A x) ≤ -Real.log (sSup {s | ∃ E : X → Matrix B B ℂ, (∀ x, (E x).PosSemidef) ∧ ∑ x, E x = 1 ∧ s = (∑ x, (E x * A x).trace).re}) := by
  classical
  obtain ⟨p, hp, hs, ρ, hρ⟩ := normalize_ensemble A hA ht
  have hm : CStarMatrix.ofMatrix.symm (mixtureState p hp hs ρ).1 = ∑ x, A x := by
    change (∑ x, p x • CStarMatrix.ofMatrix.symm (ρ x).1) = ∑ x, A x; simp_rw [hρ]
  have hr : (CStarMatrix.ofMatrix.symm (recordState p hp hs ρ).1).submatrix (Equiv.prodComm B X) (Equiv.prodComm B X) = blockDiagonal A :=
    by
    ext i j
    change (∑ x, p x • ((diagonal (fun k => if k = x then (1 : ℂ) else 0)) ⊗ₖ CStarMatrix.ofMatrix.symm (ρ x).1)) (i.2, i.1) (j.2, j.1) = _
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.kronecker_apply, Matrix.diagonal, Complex.real_smul, blockDiagonal_apply]
    by_cases hij : i.2 = j.2
    · subst_vars
      simpa [hij, ← mul_assoc] using congrFun (congrFun (hρ i.2) i.1) j.1
    · simp [hij]
  have hrec : matrixSubentropy (blockDiagonal A) = D5.S3.Quantum.Subentropy.Basic.subentropy (recordState p hp hs ρ) :=
    by
    rw [← hr, determinant_reindex]
    rfl
  have hmix : matrixSubentropy (∑ x, A x) = D5.S3.Quantum.Subentropy.Basic.subentropy (mixtureState p hp hs ρ) := by exact Real.ext_cauchy (congrArg Real.cauchy (congrArg matrixSubentropy (id (Eq.symm hm))))
  have hg : D5.S3.Quantum.Subentropy.GuessingProbability.pGuess p ρ = sSup {s | ∃ E : X → Matrix B B ℂ, (∀ x, (E x).PosSemidef) ∧ ∑ x, E x = 1 ∧ s = (∑ x, (E x * A x).trace).re} :=
    by
    unfold D5.S3.Quantum.Subentropy.GuessingProbability.pGuess successProbabilitySet; congr 1; ext s; congr 3; unfold successProbability; simp_rw [← hρ]; simp [Matrix.mul_smul, Matrix.trace_smul, Complex.real_smul, Complex.re_sum]
  rw [hrec, hmix, ← hg]
  have hb := D5.S3.Quantum.Subentropy.POVMGram.cq_conditional_subentropy_guessing p hp hs ρ
  exact hb.1.trans hb.2
theorem result : claim := by
  intro X B _ _ _ _ A hA ht hXB hB
  have hp : (blockDiagonal A).PosSemidef := by
    rw [← Matrix.blockDiagonal'_submatrix_eq_blockDiagonal]; exact (D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.positiveBlockDiagonal A hA).submatrix _
  have hq : (∑ x, A x).PosSemidef := Matrix.posSemidef_sum _ (fun x _ => hA x)
  have hpt : (blockDiagonal A).trace = 1 := by rw [Matrix.trace_blockDiagonal]; exact ht
  have hqt : (∑ x, A x).trace = 1 := by simpa using ht
  change subentropy (blockDiagonal A) hp.isHermitian - subentropy (∑ x, A x) hq.isHermitian ≤ _; rw [source_eq_determinant _ hp hpt, source_eq_determinant _ hq hqt]; exact determinant_cq_bound A hA ht
end D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound
