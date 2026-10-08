/- GID: D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformPerturbedParameters.perturbed_kernel_stability; premises=D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.rational_solve,D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.k_value,D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.ell_value,D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.aa_anchor,D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor.schur_det_negative
   digest: The uniform anchor parameters and spectral stability estimates. -/

/- Judgement form (implementation assessment; each helper retains its own classification).
   proof_shape: Uniform.epsilon_pos: bind-only; consumer=UniformParameterAnchor.Uniform.alpha_anchor_distance.
   proof_shape: Uniform.alpha_norm: bind-only; consumer=MaximalBirankEdgeStates.Small.alpha0_norm_le.
   proof_shape: Uniform.admissible: bind-only; consumer=MaximalBirankEdgeStates.Small.certificate_sound.
   proof_shape: Uniform.alpha_anchor_distance: bind-only; consumer=MaximalBirankEdgeStates.Small.alpha_error.
   proof_shape: Uniform.operator_perturbation: content; consumer=UniformPerturbedParameters.Anchor.perturbed_kernel_stability; same-delivery-content=D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.norm_toEuclideanLin_le_of_entry_le.
   proof_shape: Uniform.uniform_coordinate_lower: bind-only; consumer=UniformPerturbedParameters.Anchor.coordinate_bounds.
   proof_shape: Uniform.three_halfplanes_star: content; consumer=MaximalBirankEdgeStates.Small.certificate_sound; same-delivery-content=D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.halfplane_star.
   proof_shape: Uniform.band_hermitian: bind-only; consumer=UniformParameterAnchor.Anchor.interior_hermitian.
   proof_shape: Uniform.band_row_bound: bind-only; consumer=UniformParameterAnchor.Anchor.interior_posDef.
   proof_shape: Uniform.spike_lower: bind-only; consumer=UniformParameterAnchor.Anchor.ell_positive.
   proof_shape: Uniform.phase_aligned_stability: content; consumer=UniformPerturbedParameters.Anchor.perturbed_kernel_stability; same-delivery-content=D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.aligned_eigenvector_stability.
   proof_shape: Uniform.surviving_projection: bind-only; consumer=UniformPerturbedParameters.Anchor.stable_halfplanes.
   proof_shape: Uniform.perturbation_error_small: bind-only; consumer=UniformParameterAnchor.Uniform.shifted_gap.
   proof_shape: Uniform.shifted_gap: bind-only; consumer=UniformPerturbedParameters.Anchor.perturbed_sorted_gap.
   proof_shape: Uniform.stability_error_budget: bind-only; consumer=UniformPerturbedParameters.Anchor.stable_halfplanes.
   proof_shape: Uniform.resolvent_isUnit: bind-only; consumer=UniformParameterAnchor.Uniform.anchorInterior_solve.
   proof_shape: Uniform.anchorInterior_solve: bind-only; consumer=UniformParameterAnchor.Anchor.interior_U_solve.
   proof_shape: Uniform.anchorInterior_positive: content; consumer=UniformParameterAnchor.Anchor.ell_positive; same-delivery-content=D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchor_interior_positive.
   proof_shape: Uniform.band_reverse: bind-only; consumer=UniformParameterAnchor.Uniform.resolvent_reverse.
   proof_shape: Uniform.anchorInterior_upper: content; consumer=UniformPerturbedParameters.Anchor.coordinate_bounds; same-delivery-content=D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior_coordinateNorm_upper.
   proof_shape: Uniform.pencil_top_largest: bind-only; consumer=MaximalBirankEdgeStates.Finite.root_and_kernel_enclosure.
   proof_shape: Uniform.simple_root_of_rank: bind-only; consumer=MaximalBirankEdgeStates.Finite.root_and_kernel_enclosure.
   proof_shape: Uniform.negative_eigenvalue_perturbation: content; consumer=UniformPerturbedParameters.Anchor.perturbed_sorted_gap; same-delivery-content=D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.abs_eigenvalues0_sub_le_of_entry_le.
   proof_shape: Uniform.top_root_simple: bind-only; consumer=UniformPerturbedParameters.Anchor.perturbed_top_simple.
   proof_shape: Anchor17Probe.rational_solve: bind-only; consumer=UniformPerturbedParameters.Anchor.U17_value.
   proof_shape: Anchor17Probe.k_value: bind-only; consumer=UniformPerturbedParameters.Anchor.k17_value.
   proof_shape: Anchor17Probe.ell_value: bind-only; consumer=UniformPerturbedParameters.Anchor.ell17_value.
   proof_shape: Anchor17Probe.aa_anchor: bind-only; consumer=UniformPerturbedParameters.Anchor.schur17_negative.
   proof_shape: Anchor17Probe.schur_det_negative: bind-only; consumer=UniformPerturbedParameters.Anchor.schur17_negative.
   proof_shape: Anchor.phase_def: bind-only; consumer=MaximalBirankEdgeStates.Small.anchor_alpha_error.
   proof_shape: Anchor.phase_unit: bind-only; consumer=UniformParameterAnchor.Anchor.d_unit.
   proof_shape: Anchor.phase_mul_conj: bind-only; consumer=UniformParameterAnchor.Anchor.anchor_reindex.
   proof_shape: Anchor.anchor_reindex: bind-only; consumer=UniformParameterAnchor.Anchor.actual_kernel.
   proof_shape: Anchor.a_cartesian: bind-only; consumer=MaximalBirankEdgeStates.Small.anchor_phase_error.
   proof_shape: Anchor.h_positive: bind-only; consumer=UniformParameterAnchor.Anchor.d_im_pos.
   proof_shape: Anchor.ell_positive: content; consumer=UniformParameterAnchor.Anchor.zeta_norm_pos; same-delivery-content=D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior_positive.
   proof_shape: Anchor.zeta_re: bind-only; consumer=UniformParameterAnchor.Anchor.zeta_norm_pos.
   proof_shape: Anchor.zeta_im: bind-only; consumer=UniformPerturbedParameters.Anchor.imaginary_bounds.
   proof_shape: Anchor.zeta_norm_pos: content; consumer=UniformParameterAnchor.Anchor.b_unit; same-delivery-content=D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.ell_positive.
   proof_shape: Anchor.b_unit: content; consumer=UniformParameterAnchor.Anchor.block_kernel; same-delivery-content=D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.zeta_norm_pos.
   proof_shape: Anchor.d_unit: content; consumer=UniformPerturbedParameters.Anchor.direction_bounds; same-delivery-content=D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.b_unit.
   proof_shape: Anchor.d_im_pos: content; consumer=UniformPerturbedParameters.Anchor.direction_bounds; same-delivery-content=D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.zeta_norm_pos.
   proof_shape: Anchor.coupling_real: bind-only; consumer=UniformParameterAnchor.Anchor.block_kernel.
   proof_shape: Anchor.actual_kernel: content; consumer=UniformPerturbedParameters.Anchor.perturbed_kernel_stability; same-delivery-content=D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.block_kernel.
   proof_shape: Anchor.interior_hermitian: bind-only; consumer=UniformParameterAnchor.Anchor.interior_posDef.
   proof_shape: Anchor.interior_posDef: bind-only; consumer=UniformParameterAnchor.Anchor.inverseCoupling_eq.
   proof_shape: Anchor.inverseCoupling_solve: bind-only; consumer=UniformParameterAnchor.Anchor.inverseCoupling_eq.
   proof_shape: Anchor.inverseCoupling_eq: bind-only; consumer=UniformParameterAnchor.Anchor.schur_eq.
   proof_shape: Anchor.schur_eq: bind-only; consumer=UniformPerturbedParameters.Anchor.block_det_schur.
   escape_witness: Anchor.actual_kernel and Uniform.phase_aligned_stability, used by the perturbed kernel construction.
   Computational utility: Anchor17Probe.numerators and its integer/rational solve,
   dot-product values and Schur determinant certificates are numeric reductions.
   Private integer_solve, k_integer and ell_integer are carried by public
   Anchor17Probe.rational_solve, k_value and ell_value.
   Classification totals: 19 content; 68 bind-only.
   admission_basis: escape-witness
   Direct frozen dependencies: D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.s2; statement_id=sha256:ef4ae1e2fc1bec9bf605d06598d58ce332db9ba1a90facd16a497c70ae0336f7.
   Other dependencies are pinned Mathlib and same-delivery modules.
   Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction
import D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence
import D5.S3.SpectralTopology.HermitianEigenvaluePerturbation

noncomputable section
namespace D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor
open scoped ComplexConjugate
open Matrix
namespace Uniform
set_option backward.isDefEq.respectTransparency false
def epsilon (n : ℕ) : ℝ := 1 / (1000000000 * (n : ℝ)^6)
def angle (n : ℕ) (i : Fin n) : ℝ := if i.val = 0 then 0 else if i.val + 1 = n then Real.pi else Real.pi * (1/4 + (i.val : ℝ) * epsilon n)
def alpha (n : ℕ) (i : Fin n) : ℂ := Complex.exp (Complex.I * angle n i)
def beta (n : ℕ) : Fin n → ℂ := fun _ => 1
def anchorAlpha (n : ℕ) (i : Fin n) : ℂ := if i.val = 0 then 1 else if i.val + 1 = n then -1 else Complex.exp (Complex.I * (Real.pi / 4 : ℝ))
theorem epsilon_pos {n : ℕ} (hn : 0 < n) : 0 < epsilon n := by
  unfold epsilon; positivity
private theorem interior_fraction_lt {n : ℕ} (hn : 3 ≤ n) (i : Fin n) : (i.val : ℝ) * epsilon n < 1/4 := by
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hir : (i.val : ℝ) < n := by exact_mod_cast i.isLt
  have hn1 : (1 : ℝ) ≤ (n : ℝ)^5 := one_le_pow₀ (by linarith); have hn6 : (n : ℝ) ≤ (n : ℝ)^6 := by
    calc (n : ℝ) = (n : ℝ) * 1 := by ring
      _ ≤ (n : ℝ) * (n : ℝ)^5 := mul_le_mul_of_nonneg_left hn1 (by positivity)
      _ = (n : ℝ)^6 := by ring
  unfold epsilon; rw [mul_one_div, div_lt_iff₀ (by positivity)]; nlinarith
private theorem angle_in_range {n : ℕ} (hn : 3 ≤ n) (i : Fin n) : 0 ≤ angle n i ∧ angle n i ≤ Real.pi := by
  unfold angle
  split_ifs
  · exact ⟨le_rfl, Real.pi_pos.le⟩
  · exact ⟨Real.pi_pos.le, le_rfl⟩
  have hf := interior_fraction_lt hn i; have he := epsilon_pos (by omega : 0 < n)
  constructor
  · positivity
  · nlinarith [Real.pi_pos, mul_nonneg (show 0 ≤ (i.val : ℝ) by positivity) he.le]
private theorem angle_strictMono {n : ℕ} (hn : 3 ≤ n) : StrictMono (angle n) := by
  intro i j hij; have hiv : i.val < j.val := hij; have hnj := j.isLt; have hni := i.isLt; have he := epsilon_pos (by omega : 0 < n); have hir : (i.val : ℝ) < j.val := by exact_mod_cast hiv
  have hpi := Real.pi_pos; unfold angle
  split_ifs with hi hj hi' hj' <;> try omega
  all_goals have hfi := interior_fraction_lt hn i
  all_goals have hfj := interior_fraction_lt hn j
  all_goals nlinarith [mul_nonneg (show 0 ≤ (i.val : ℝ) by positivity) he.le,
    mul_nonneg (show 0 ≤ (j.val : ℝ) by positivity) he.le,
    mul_lt_mul_of_pos_right hir he]
private theorem alpha_injective {n : ℕ} (hn : 3 ≤ n) : Function.Injective (alpha n) := by
  intro i j hij; have hi := angle_in_range hn i; have hj := angle_in_range hn j; have heq := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (x := Complex.I * (angle n i : ℂ)) (y := Complex.I * (angle n j : ℂ))
    (by simp; linarith [Real.pi_pos]) (by simpa using hi.2)
    (by simp; linarith [Real.pi_pos]) (by simpa using hj.2) hij
  apply (angle_strictMono hn).injective
  simpa using congrArg Complex.im heq
theorem alpha_norm (n : ℕ) (i : Fin n) : ‖alpha n i‖ = 1 := by
  exact Complex.norm_exp_I_mul_ofReal _
theorem admissible {n : ℕ} (hn : 3 ≤ n) : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Admissible (alpha n) (beta n) := by
  refine ⟨fun i => ⟨alpha_norm n i, by simp [beta]⟩, ?_, ?_, ?_⟩
  · simp [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.phaseAt, alpha, angle, show 0 < n by omega]
  · simp [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.phaseAt, beta]
  · intro i j hij heq
    have hai : alpha n i ≠ 0 := by
      exact Complex.exp_ne_zero _
    have heq' : (alpha n i)⁻¹ * alpha n j = 1 := by simpa [beta] using heq
    have haij : alpha n i = alpha n j := by
      calc alpha n i = alpha n i * 1 := by ring
        _ = alpha n i * ((alpha n i)⁻¹ * alpha n j) := by rw [heq']
        _ = alpha n j := by rw [← mul_assoc, mul_inv_cancel₀ hai, one_mul]
    exact (ne_of_lt hij) ((alpha_injective hn) haij)
private theorem phase_difference (x y : ℝ) : ‖Complex.exp (Complex.I * x) - Complex.exp (Complex.I * y)‖ ≤ |x-y| := by
  have hfactor : Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ)) =
      Complex.exp (Complex.I * (y : ℂ)) * (Complex.exp (Complex.I * ((x-y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add]; congr 1
    · congr 1; push_cast; ring
    · ring
  rw [hfactor, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  simpa [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := x-y)
theorem alpha_anchor_distance {n : ℕ} (hn : 3 ≤ n) (i : Fin n) : ‖alpha n i - anchorAlpha n i‖ ≤ Real.pi * n * epsilon n := by
  have he := epsilon_pos (by omega : 0 < n); have hp : 0 ≤ Real.pi * n * epsilon n := by positivity
  unfold alpha anchorAlpha angle
  split_ifs with hi hl
  · simpa using hp
  · simp only [mul_comm Complex.I, Complex.exp_pi_mul_I, sub_self, norm_zero]
    exact hp
  · have h := phase_difference (Real.pi * (1/4 + (i.val : ℝ) * epsilon n)) (Real.pi/4)
    have heq : Real.pi * (1/4 + (i.val : ℝ) * epsilon n) - Real.pi/4 =
        Real.pi * i.val * epsilon n := by ring
    rw [heq, abs_of_nonneg (by positivity)] at h; refine h.trans ?_
    gcongr
    exact_mod_cast i.isLt.le
private theorem anchor_norm (n : ℕ) (i : Fin n) : ‖anchorAlpha n i‖ = 1 := by
  unfold anchorAlpha
  split_ifs
  · simp
  · simp
  · convert Complex.norm_exp_I_mul_ofReal (Real.pi/4) using 1
private theorem unit_product_difference {x y x₀ y₀ : ℂ} (hx : ‖x‖ = 1) (hy : ‖y₀‖ = 1) : ‖x * conj y - x₀ * conj y₀‖ ≤ ‖y-y₀‖ + ‖x-x₀‖ := by
  calc ‖x * conj y - x₀ * conj y₀‖ =
      ‖x * conj (y-y₀) + (x-x₀) * conj y₀‖ := by congr 1; simp [map_sub]; ring
    _ ≤ ‖x * conj (y-y₀)‖ + ‖(x-x₀) * conj y₀‖ := norm_add_le _ _
    _ = ‖y-y₀‖ + ‖x-x₀‖ := by rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, hx, hy]; ring
private theorem entry_perturbation {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) (r : ℝ) : ‖D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha n) (beta n) r i j - D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (anchorAlpha n) (beta n) r i j‖ ≤
    2 * (Real.pi * n * epsilon n) := by
  have hp : 0 ≤ Real.pi * n * epsilon n := by positivity [epsilon_pos (by omega : 0<n)]
  have hi := alpha_anchor_distance hn i; have hj := alpha_anchor_distance hn j; unfold D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D
  split_ifs
  all_goals try simp only [sub_self, norm_zero]; try linarith
  all_goals try (simpa only [one_mul, ← map_sub, Complex.norm_conj] using hj.trans (by linarith))
  all_goals try (simpa only [one_mul] using hi.trans (by linarith))
  all_goals try (simpa only [← mul_sub, norm_mul, Complex.norm_ofNat, ← map_sub, Complex.norm_conj] using
    mul_le_mul_of_nonneg_left hj (by norm_num : (0:ℝ)≤2))
  all_goals try (simpa only [← mul_sub, norm_mul, Complex.norm_ofNat] using
    mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ)≤2))
  all_goals
    have h := unit_product_difference (y := alpha n j) (x₀ := anchorAlpha n i)
      (alpha_norm n i) (anchor_norm n j)
    exact h.trans (by linarith)
theorem operator_perturbation {n : ℕ} (hn : 3 ≤ n) (r : ℝ) : (norm ∘ (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha n) (beta n) r - D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (anchorAlpha n) (beta n) r) ≤ 2 *
    Real.pi / (1000000000 * (n : ℝ)^4) := by
  let E := D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha n) (beta n) r - D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (anchorAlpha n) (beta n) r; have hpoint := D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.norm_toEuclideanLin_le_of_entry_le
    (A := E) (fun i j => entry_perturbation hn i j r)
  have hnorm : (norm ∘ (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))) E ≤ n * (2 * (Real.pi * n * epsilon n)) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [epsilon_pos (by omega : 0<n)]); exact hpoint
  have hnz : (n : ℝ) ≠ 0 := by positivity
  have heq : (n : ℝ) * (2 * (Real.pi * n * epsilon n)) =
      2 * Real.pi / (1000000000 * (n : ℝ)^4) := by
    unfold epsilon; field_simp
  simpa only [heq] using hnorm
section Neumann
open scoped Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem geometric_dominates_identity {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j) (hsmall : ‖A‖ < 1) (i j : ι) : (1 : Matrix ι ι ℝ) i j ≤
    (∑' k : ℕ, A^k) i j := by
  have hs := summable_geometric_of_norm_lt_one hsmall; have hsrow := Pi.summable.mp hs i; have hsentry := Pi.summable.mp hsrow j; have hrow : (∑' k : ℕ, A^k) i = ∑' k : ℕ, (A^k) i := tsum_apply hs
  have hentry : (∑' k : ℕ, (A^k) i) j = ∑' k : ℕ, (A^k) i j := tsum_apply hsrow; have heq : (∑' k : ℕ, A^k) i j = ∑' k : ℕ, (A^k) i j :=
    (congrFun hrow j).trans hentry
  rw [heq]
  simpa only [pow_zero] using hsentry.le_tsum 0 (fun k _ => Matrix.pow_apply_nonneg hA k i j)
private theorem geometric_mulVec_lower {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j) (hsmall : ‖A‖ < 1) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (i : ι) : f i ≤
    ((∑' k : ℕ, A^k) *ᵥ f) i := by
  calc f i = ((1 : Matrix ι ι ℝ) *ᵥ f) i := by rw [Matrix.one_mulVec]
    _ ≤ ((∑' k : ℕ, A^k) *ᵥ f) i := by
      apply Finset.sum_le_sum
      intro j _; exact mul_le_mul_of_nonneg_right (geometric_dominates_identity hA hsmall i j) (hf j)
private theorem squared_neumann_lower {T : Matrix ι ι ℝ} {r : ℝ} (hT : ∀ i j, 0 ≤ T i j) (hr : 5 < r) (hsmall : ‖(r^2)⁻¹ • (T*T)‖ < 1) (c u : ι → ℝ) (hc
    : ∀ i, 1 ≤ c i) (hTc : ∀ i, (T *ᵥ c) i ≤ 5*c i) (hsolve : (r • (1 : Matrix ι ι ℝ) + T) *ᵥ u = c) : ∀ i, (r-5)/r^2 ≤ u i := by
  let A := (r^2)⁻¹ • (T*T); let f : ι → ℝ := (r^2)⁻¹ • (r • c - T *ᵥ c); have hrz : r ≠ 0 := by linarith
  have hr2 : 0 < r^2 := sq_pos_of_ne_zero hrz; have hfirst (i : ι) : r*u i + (T *ᵥ u) i = c i := by
    simpa only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congrFun hsolve i
  have ht := congrArg (T.mulVec) hsolve; simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec] at ht
  have hsecond (i : ι) : r*(T *ᵥ u) i + ((T*T) *ᵥ u) i = (T *ᵥ c) i := by
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congrFun ht i
  have hscaled : (1-A) *ᵥ u = f := by
    ext i
    simp only [A, f, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    apply (mul_left_cancel₀ (pow_ne_zero 2 hrz)); rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hrz), one_mul,
      ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hrz), one_mul]
    nlinarith [congrArg (fun t : ℝ => r*t) (hfirst i), hsecond i]
  have hAnonneg : ∀ i j, 0 ≤ A i j := by
    intro i j; exact mul_nonneg (inv_nonneg.mpr hr2.le)
      (Finset.sum_nonneg fun k _ => mul_nonneg (hT i k) (hT k j))
  have hflower (i : ι) : (r-5)/r^2 ≤ f i := by
    simp only [f, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; rw [div_eq_inv_mul]; apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hr2.le); nlinarith [hTc i, mul_nonneg (sub_pos.mpr hr).le (sub_nonneg.mpr (hc i))]
  have hf : ∀ i, 0 ≤ f i := fun i =>
    (div_nonneg (sub_pos.mpr hr).le hr2.le).trans (hflower i)
  have hrep : u = (∑' k : ℕ, A^k) *ᵥ f := by
    rw [← hscaled, Matrix.mulVec_mulVec]; have hg : (∑' k : ℕ, A^k) * (1-A) = 1 := geom_series_mul_neg A hsmall; rw [hg, Matrix.one_mulVec]
  intro i; rw [hrep]; exact (hflower i).trans (geometric_mulVec_lower hAnonneg hsmall f hf i)
private theorem squared_neumann_small {T : Matrix ι ι ℝ} {r : ℝ} (hr : 5 < r) (hTnorm : ‖T‖ ≤ 4) : ‖(r^2)⁻¹ • (T*T)‖ < 1 := by
  have hr2 : 0 < r^2 := sq_pos_of_ne_zero (by linarith); have hTT : ‖T*T‖ ≤ 16 := by
    calc ‖T*T‖ ≤ ‖T‖*‖T‖ := norm_mul_le _ _
      _ ≤ 4*4 := mul_le_mul hTnorm hTnorm (norm_nonneg _) (by norm_num)
      _ = 16 := by norm_num
  calc ‖(r^2)⁻¹ • (T*T)‖ = (r^2)⁻¹ * ‖T*T‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr2.le)]
    _ ≤ (r^2)⁻¹ * 16 := mul_le_mul_of_nonneg_left hTT (inv_nonneg.mpr hr2.le)
    _ < 1 := by rw [inv_mul_eq_div, div_lt_one hr2]; nlinarith
private theorem positive_resolvent_coordinates {T : Matrix ι ι ℝ} {r : ℝ} (hT : ∀ i j, 0 ≤ T i j) (hr : 5 < r) (hTnorm : ‖T‖ ≤ 4) (c u : ι → ℝ) (hc : ∀
    i, 1 ≤ c i) (hTc : ∀ i, (T *ᵥ c) i ≤ 5*c i) (hsolve : (r • (1 : Matrix ι ι ℝ) + T) *ᵥ u = c) : ∀ i, 0 < u i ∧ (r-5)/r^2 ≤ u i := by
  have hlower := squared_neumann_lower hT hr (squared_neumann_small hr hTnorm) c u hc hTc hsolve
  intro i; exact ⟨lt_of_lt_of_le (div_pos (by linarith) (sq_pos_of_ne_zero (by linarith)))
    (hlower i), hlower i⟩
theorem uniform_coordinate_lower {n : ℕ} (hn : 17 ≤ n) {r x : ℝ} (hr : 161/32 < r) (hsq : r^2 ≤ 9*n) (hx : (r-5)/r^2 ≤ x) : 1/(288*(n:ℝ)) < x := by
  have hnr : (17 : ℝ) ≤ n := by exact_mod_cast hn
  have hr2 : 0 < r^2 := sq_pos_of_ne_zero (by linarith); apply lt_of_lt_of_le _ hx; rw [div_lt_div_iff₀ (by positivity) hr2]; have hb : (1/32 : ℝ) < r-5 := by linarith
  have hmul := mul_lt_mul_of_pos_left hb (show 0 < 288*(n:ℝ) by positivity); nlinarith
end Neumann
private theorem alpha_support_dichotomy {n : ℕ} (hn : 3 ≤ n) {s : Finset (Fin n)} (hs : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.AllowedSupport n true s) : (∀ i ∈ s, i.val+1 ≠ n) ∨ (∀ i ∈ s,
    i.val=0 ∨ i.val+1=n) := by
  by_cases hlast : ∃ i ∈ s, i.val+1=n
  · right
    obtain ⟨i, hi, hilast⟩ := hlast; simp only [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.AllowedSupport, ite_true] at hs
    rcases hs with hsmall | ⟨p,q,hp,hq,hpq,hp2,hq2,hcover⟩
    · have hb := hsmall i hi; omega
    · have hiq := hcover i hi
      have hqbound := q.isLt; have hpbound := p.isLt; have hqval : q.val+1=n := by
        rcases hiq with heq | hle
        · subst i; exact hilast
        · omega
      intro j hj; have hjq := hcover j hj
      rcases hjq with heq | hle
      · subst j; exact Or.inr hqval
      · left; omega
  · left; intro i hi h; exact hlast ⟨i,hi,h⟩
private theorem beta_support_excludes_first {n : ℕ} (hn : 3 ≤ n) {s : Finset (Fin n)} (hs : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.AllowedSupport n false s) : ∀ i ∈ s, i.val ≠ 0 := by
  simp only [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.AllowedSupport, Bool.false_eq_true, ite_false] at hs
  rcases hs with hlarge | ⟨p,q,hp,hq,hpq,hp2,hq2,hcover⟩
  · intro i hi hz; have h := hlarge i hi; omega
  · intro i hi hz
    have hh := hcover i hi; have hpbound := p.isLt; have hqbound := q.isLt
    rcases hh with heq | hineq
    · subst i; omega
    · omega
private theorem halfplane_star {n : ℕ} (a b w : Fin n → ℂ) (hplane : ∀ (isAlpha : Bool) (s : Finset (Fin n)), s.Nonempty → D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.AllowedSupport n isAlpha s
    → ∃ z : ℂ, ∀ i ∈ s, 0 < (z * ((if isAlpha then a i else b i) * conj (w i))).re) : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.StarCondition a b w := by
  intro isAlpha s hs hallowed u hu hus hzero
  obtain ⟨z,hz⟩ := hplane isAlpha s hs hallowed; have hout (i : Fin n) (hi : i ∉ s) : u i = 0 := by
    by_contra h; exact hi ((hus i).mp h)
  have hsum : 0 < ∑ i : Fin n, u i *
      (z * ((if isAlpha then a i else b i) * conj (w i))).re := by
    apply Finset.sum_pos'
    · intro i _
      by_cases hi : i ∈ s
      · exact mul_nonneg (hu i) (hz i hi).le
      · simp [hout i hi]
    · obtain ⟨i,hi⟩ := hs
      exact ⟨i, Finset.mem_univ i,
        mul_pos (lt_of_le_of_ne (hu i) (Ne.symm ((hus i).mpr hi))) (hz i hi)⟩
  have heq : (z * ∑ i : Fin n, ((u i : ℂ) * (if isAlpha then a i else b i)) * conj (w i)).re =
      ∑ i : Fin n, u i * (z * ((if isAlpha then a i else b i) * conj (w i))).re := by
    rw [Finset.mul_sum, Complex.re_sum]; apply Finset.sum_congr rfl
    intro i _; have hh : z * (((u i : ℂ) * (if isAlpha then a i else b i)) * conj (w i)) =
        (u i : ℂ) * (z * ((if isAlpha then a i else b i) * conj (w i))) := by ring
    rw [hh]
    cases isAlpha <;> simp [Complex.mul_re]
  rw [← heq, hzero, mul_zero, Complex.zero_re] at hsum; exact (lt_irrefl 0) hsum
theorem three_halfplanes_star {n : ℕ} (hn : 3 ≤ n) (a b w : Fin n → ℂ) (zAlpha zBeta zEnds : ℂ) (ha : ∀ i : Fin n, i.val+1 ≠ n → 0 < (zAlpha * (a
    i * conj (w i))).re) (hb : ∀ i : Fin n, i.val ≠ 0 → 0 < (zBeta * (b i * conj (w i))).re) (he : ∀ i : Fin n, i.val=0 ∨ i.val+1=n → 0 < (zEnds
    * (a i * conj (w i))).re) : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.StarCondition a b w := by
  apply halfplane_star
  intro t s hs hallowed
  cases t
  · exact ⟨zBeta, fun i hi => hb i (beta_support_excludes_first hn hallowed i hi)⟩
  · rcases alpha_support_dichotomy hn hallowed with hnot | hends
    · exact ⟨zAlpha, fun i hi => ha i (hnot i hi)⟩
    · exact ⟨zEnds, fun i hi => he i (hends i hi)⟩
section Band
open scoped Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem hermitian_norm_of_row_bound {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {R : ℝ} (hR : 0 ≤ R) (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R) : ‖A‖ ≤ R := by
  have hev (j : ι) : |hA.eigenvalues j| ≤ R := by
    have hμ : Module.End.HasEigenvalue (Matrix.toLin' A) (hA.eigenvalues j) := by
      apply Module.End.hasEigenvalue_of_hasEigenvector (x := fun i => hA.eigenvectorBasis j i); refine ⟨?_, ?_⟩
      · exact Module.End.mem_eigenspace_iff.mpr (hA.mulVec_eigenvectorBasis j)
      · exact (WithLp.ofLp_eq_zero 2).ne.2 (hA.eigenvectorBasis.orthonormal.ne_zero j)
    obtain ⟨i,hi⟩ := eigenvalue_mem_ball hμ; have hi' : ‖hA.eigenvalues j - A i i‖ ≤ ∑ k ∈ Finset.univ.erase i, ‖A i k‖ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hi
    calc |hA.eigenvalues j| = ‖hA.eigenvalues j‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖hA.eigenvalues j-A i i‖ + ‖A i i‖ := by simpa [add_comm, norm_sub_rev] using norm_le_insert (A i i) (hA.eigenvalues j)
      _ ≤ (∑ k ∈ Finset.univ.erase i, ‖A i k‖) + ‖A i i‖ := add_le_add hi' le_rfl
      _ = ∑ k, ‖A i k‖ := Finset.sum_erase_add _ _ (Finset.mem_univ i)
      _ ≤ R := hrow i
  rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]; change ‖((hA.eigenvectorUnitary : Matrix ι ι ℝ) *
    diagonal (RCLike.ofReal ∘ hA.eigenvalues)) * (star hA.eigenvectorUnitary : Matrix ι ι ℝ)‖ ≤ R
  have hstar := Unitary.coe_star (U := hA.eigenvectorUnitary); rw [← hstar]; rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]; apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  simpa only [Function.comp_apply, RCLike.norm_ofReal] using hev i
def band (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := fun i j =>
  if i.val+1=j.val ∨ j.val+1=i.val ∨ i.val+2=j.val ∨ j.val+2=i.val then 1 else 0
private theorem band_nonnegative (m : ℕ) (i j : Fin m) : 0 ≤ band m i j := by
  unfold band; split_ifs <;> norm_num
theorem band_hermitian (m : ℕ) : (band m).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]; unfold band
  split_ifs <;> first | rfl | tauto
theorem band_row_bound (m : ℕ) (i : Fin m) : ∑ j, ‖band m i j‖ ≤ 4 := by
  have hentry (j : Fin m) : ‖band m i j‖ ≤
      (if i.val+1=j.val then 1 else 0) + (if j.val+1=i.val then 1 else 0) +
      (if i.val+2=j.val then 1 else 0) + (if j.val+2=i.val then 1 else 0) := by
    unfold band; split_ifs <;> norm_num <;> omega
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hentry j); simp only [Finset.sum_add_distrib] at hsum; have h1 := D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Path.sum_indicator_le (fun j : Fin m => i.val+1=j.val)
    (fun j k hj hk => Fin.ext (by omega)) 1 (by norm_num)
  have h2 := D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Path.sum_indicator_le (fun j : Fin m => j.val+1=i.val)
    (fun j k hj hk => Fin.ext (by omega)) 1 (by norm_num)
  have h3 := D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Path.sum_indicator_le (fun j : Fin m => i.val+2=j.val)
    (fun j k hj hk => Fin.ext (by omega)) 1 (by norm_num)
  have h4 := D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Path.sum_indicator_le (fun j : Fin m => j.val+2=i.val)
    (fun j k hj hk => Fin.ext (by omega)) 1 (by norm_num)
  linarith
private theorem band_norm_bound (m : ℕ) : ‖band m‖ ≤ 4 := hermitian_norm_of_row_bound (band_hermitian m) (by norm_num) (band_row_bound m)
def spike (m : ℕ) : Fin m → ℝ := fun i => if i.val=1 then 2 else 1
theorem spike_lower (m : ℕ) (i : Fin m) : 1 ≤ spike m i := by
  unfold spike; split_ifs <;> norm_num
private theorem band_spike_dominance (m : ℕ) (i : Fin m) : (band m *ᵥ spike m) i ≤ 5 * spike m i := by
  have heq (j : Fin m) : band m i j * spike m j =
      band m i j + (if j.val=1 then band m i j else 0) := by
    unfold spike; split_ifs <;> ring
  have he : (band m *ᵥ spike m) i =
      (∑ j, band m i j) + ∑ j, if j.val=1 then band m i j else 0 := by
    simp only [Matrix.mulVec, dotProduct, heq, Finset.sum_add_distrib]
  have hbase : (∑ j, band m i j) ≤ 4 := by
    simpa only [Real.norm_of_nonneg (band_nonnegative m i _)] using band_row_bound m i
  have hextra : (∑ j : Fin m, if j.val=1 then band m i j else 0) ≤ 1 := by
    apply le_trans (Finset.sum_le_sum (fun j _ => ?_))
      (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Path.sum_indicator_le (fun j : Fin m => j.val=1)
        (fun j k hj hk => Fin.ext (by omega)) 1 (by norm_num))
    split_ifs
    · unfold band; split_ifs <;> norm_num
    · exact le_rfl
  rw [he]; linarith [spike_lower m i]
private theorem anchor_interior_positive (m : ℕ) {r : ℝ} (hr : 5 < r) (u : Fin m → ℝ) (hu : (r • (1 : Matrix (Fin m) (Fin m) ℝ) + band m) *ᵥ u = spike m)
    : ∀ i, 0 < u i ∧ (r-5)/r^2 ≤ u i :=
  positive_resolvent_coordinates (band_nonnegative m) hr (band_norm_bound m)
    (spike m) u (spike_lower m) (band_spike_dominance m) hu
end Band
section Stability
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
private theorem aligned_unit_distance (p q : H) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (him : (⟪p,q⟫_ℂ).im = 0) (hpos : 0 ≤ (⟪p,q⟫_ℂ).re) : ‖q-p‖ ≤ 2*‖q-⟪p,q⟫_ℂ • p‖ := by
  let c := ⟪p,q⟫_ℂ; have hcreal : c = (c.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using him
  have hc1 : c.re ≤ 1 := by
    calc c.re ≤ ‖c‖ := Complex.re_le_norm _
      _ ≤ ‖p‖*‖q‖ := norm_inner_le_norm _ _
      _ = 1 := by rw [hp,hq]; ring
  have hcnorm : ‖c‖ = c.re := by
    rw [hcreal, Complex.norm_real]; exact Real.norm_of_nonneg hpos
  have hic : (⟪q,c • p⟫_ℂ).re = c.re^2 := by
    rw [inner_smul_right, ← inner_conj_symm]; change (c * conj c).re = c.re^2; rw [hcreal]
    simp
    ring
  have hproj : ‖q-c • p‖^2 = 1-c.re^2 := by
    rw [norm_sub_sq (𝕜 := ℂ), hq, norm_smul, hcnorm, hp]; change 1^2 - 2*(⟪q,c • p⟫_ℂ).re + (c.re*1)^2 = _; rw [hic]; ring
  have hdist : ‖q-p‖^2 = 2-2*c.re := by
    rw [norm_sub_sq (𝕜 := ℂ), hq,hp, inner_re_symm]; change 1^2 - 2*c.re + 1^2 = _; ring
  have hprod : 0 ≤ (1-c.re)*(4*c.re+2) := mul_nonneg (by linarith) (by linarith); change ‖q-p‖ ≤ 2*‖q-c • p‖; nlinarith [norm_nonneg (q-p),norm_nonneg (q-c • p)]
private theorem aligned_eigenvector_stability (A E : H →L[ℂ] H) (q q' : H) (lam lam' g e : ℝ) (hg : 0 < g) (hq : ‖q‖ = 1) (hq' : ‖q'‖ = 1) (hker : A q =
    (lam : ℂ) • q) (heig : (A+E) q' = (lam' : ℂ) • q') (hgap : ∀ v : H, ⟪q,v⟫_ℂ=0 → g*‖v‖ ≤ ‖A v-(lam : ℂ) • v‖) (hshift : |lam'-lam| ≤ e) (hE :
    ‖E‖ ≤ e) (him : (⟪q,q'⟫_ℂ).im=0) (hpos : 0 ≤ (⟪q,q'⟫_ℂ).re) : ‖q'-q‖ ≤ 4*e/g := by
  let c := ⟪q,q'⟫_ℂ; let z := q'-c • q; have horth : ⟪q,z⟫_ℂ = 0 := by
    simp only [z,inner_sub_right,inner_smul_right,inner_self_eq_norm_sq_to_K,hq]; change c-c*(1:ℂ)^2=0; ring
  have hAq' : A q' = (lam' : ℂ) • q'-E q' := by
    have h := heig; simp only [ContinuousLinearMap.add_apply] at h; exact eq_sub_of_add_eq h
  have hres : A z-(lam : ℂ) • z = ((lam'-lam : ℝ) : ℂ) • q'-E q' := by
    simp only [z,map_sub,map_smul,hAq',hker,smul_sub,smul_smul,Complex.ofReal_sub]
    module
  have hresbound : ‖A z-(lam : ℂ) • z‖ ≤ 2*e := by
    rw [hres]
    calc ‖((lam'-lam : ℝ) : ℂ) • q'-E q'‖ ≤
        ‖((lam'-lam : ℝ) : ℂ) • q'‖+‖E q'‖ := norm_sub_le _ _
      _ ≤ e+e := by
        apply add_le_add
        · rw [norm_smul,hq',mul_one,Complex.norm_real,Real.norm_eq_abs]
          exact hshift
        · calc ‖E q'‖ ≤ ‖E‖*‖q'‖ := E.le_opNorm q'
            _ ≤ e := by simpa [hq'] using hE
      _ = 2*e := by ring
  have hgb := (hgap z horth).trans hresbound; have hd := aligned_unit_distance q q' hq hq' him hpos; apply (le_div_iff₀ hg).mpr; have hm := mul_le_mul_of_nonneg_right hd hg.le; change ‖q'-q‖*g ≤ 4*e; nlinarith
end Stability
section PhaseAlignment
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem phase_aligned_stability (A E : H →L[ℂ] H) (q q' : H) (lam lam' g e : ℝ) (hg : 0 < g) (hq : ‖q‖ = 1) (hq' : ‖q'‖ = 1) (hker : A q = (lam :
    ℂ) • q) (heig : (A+E) q' = (lam' : ℂ) • q') (hgap : ∀ v : H, @inner ℂ H InnerProductSpace.toInner q v=0 → g*‖v‖ ≤ ‖A v-(lam : ℂ) • v‖) (hshift : |lam'-lam| ≤ e) (hE : ‖E‖ ≤
    e) : ∃ z : ℂ, ‖z‖=1 ∧ ‖z • q'-q‖ ≤ 4*e/g := by
  obtain ⟨z,hz,hcz⟩ := Complex.exists_norm_eq_mul_self ⟪q,q'⟫_ℂ; refine ⟨z,hz,aligned_eigenvector_stability A E q (z • q') lam lam' g e hg hq ?_
    hker ?_ hgap hshift hE ?_ ?_⟩
  · simp [norm_smul,hz,hq']
  · rw [map_smul,heig,smul_smul,smul_smul,mul_comm]
  · rw [inner_smul_right,← hcz]; simp
  · rw [inner_smul_right,← hcz]; simpa using norm_nonneg ⟪q,q'⟫_ℂ
end PhaseAlignment
private theorem projection_error {n : ℕ} (a a' : Fin n → ℂ) (q q' : EuclideanSpace ℂ (Fin n)) (z : ℂ) (i : Fin n) (hz : ‖z‖=1) (ha : ‖a' i‖=1) (hq :
    ‖q‖=1) : |(z*(a' i*conj (q' i))).re-(z*(a i*conj (q i))).re| ≤ ‖q'-q‖+‖a' i-a i‖ := by
  have hqi : ‖q i‖ ≤ 1 := (PiLp.norm_apply_le q i).trans_eq hq; have hdi : ‖q' i-q i‖ ≤ ‖q'-q‖ := PiLp.norm_apply_le (q'-q) i
  calc
    _ = |(z*(a' i*conj (q' i)-a i*conj (q i))).re| := by rw [mul_sub,Complex.sub_re]
    _ ≤ ‖z*(a' i*conj (q' i)-a i*conj (q i))‖ := Complex.abs_re_le_norm _
    _ = ‖a' i*conj (q' i)-a i*conj (q i)‖ := by rw [norm_mul,hz,one_mul]
    _ = ‖a' i*conj (q' i-q i)+(a' i-a i)*conj (q i)‖ := by
      congr 1; simp only [map_sub]; ring
    _ ≤ ‖a' i*conj (q' i-q i)‖+‖(a' i-a i)*conj (q i)‖ := norm_add_le _ _
    _ ≤ ‖q'-q‖+‖a' i-a i‖ := by
      rw [norm_mul,norm_mul,Complex.norm_conj,Complex.norm_conj,ha,one_mul]; exact add_le_add hdi (mul_le_of_le_one_right (norm_nonneg _) hqi)
theorem surviving_projection {n : ℕ} (hn : 17 ≤ n) (a a' : Fin n → ℂ) (q q' : EuclideanSpace ℂ (Fin n)) (z : ℂ) (i : Fin n) (hz : ‖z‖=1) (ha :
    ‖a' i‖=1) (hq : ‖q‖=1) (hmargin : 1/(100000*(n:ℝ)^3) ≤ (z*(a i*conj (q i))).re) (herror : ‖q'-q‖+‖a' i-a i‖ ≤
    73*Real.pi/(1000000000*(n:ℝ)^3)) : 1/(200000*(n:ℝ)^3) ≤ (z*(a' i*conj (q' i))).re := by
  have hnpos : 0 < (n:ℝ)^3 := by positivity
  have hnum : 73*Real.pi/(1000000000*(n:ℝ)^3) < 1/(200000*(n:ℝ)^3) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith [Real.pi_le_four]
  have hdiff := (abs_le.mp ((projection_error a a' q q' z i hz ha hq).trans herror)).1; have heq : 1/(100000*(n:ℝ)^3) = 2*(1/(200000*(n:ℝ)^3)) := by ring
  linarith
theorem perturbation_error_small {n : ℕ} (hn : 17 ≤ n) : 2*Real.pi/(1000000000*(n:ℝ)^4) < 1/(36*(n:ℝ)) := by
  have hnr : (17:ℝ) ≤ n := by exact_mod_cast hn
  have hn3 : (1:ℝ) ≤ (n:ℝ)^3 := one_le_pow₀ (by linarith); rw [div_lt_div_iff₀ (by positivity) (by positivity)]; have hpower : (n:ℝ)^4 = n*(n:ℝ)^3 := by ring
  rw [hpower]; nlinarith [Real.pi_le_four]
theorem shifted_gap {n : ℕ} (hn : 17 ≤ n) {x y x' y' : ℝ} (hgap : 1/(9*(n:ℝ)) ≤ x-y) (hx : |x'-x| ≤ 2*Real.pi/(1000000000*(n:ℝ)^4)) (hy : |y'-y|
    ≤ 2*Real.pi/(1000000000*(n:ℝ)^4)) : 1/(18*(n:ℝ)) ≤ x'-y' := by
  have he := perturbation_error_small hn; have hx' := abs_le.mp hx; have hy' := abs_le.mp hy; have hfrac : 1/(9*(n:ℝ)) = 4*(1/(36*(n:ℝ))) := by ring
  have hfrac' : 1/(18*(n:ℝ)) = 2*(1/(36*(n:ℝ))) := by ring
  linarith
theorem stability_error_budget {n : ℕ} (hn : 17 ≤ n) {g e : ℝ} (hg : 1/(9*(n:ℝ)) ≤ g) (he : 0 ≤ e) (hebound : e ≤ 2*Real.pi/(1000000000*(n:ℝ)^4))
    : 4*e/g + Real.pi*n*epsilon n ≤ 73*Real.pi/(1000000000*(n:ℝ)^3) := by
  have hnr : (17:ℝ) ≤ n := by exact_mod_cast hn
  have hgpos : 0 < g := lt_of_lt_of_le (by positivity) hg; have hnz : (n:ℝ) ≠ 0 := by positivity
  have hquot : 4*e/g ≤ 72*Real.pi/(1000000000*(n:ℝ)^3) := by
    calc 4*e/g ≤ (4*(2*Real.pi/(1000000000*(n:ℝ)^4))) / (1/(9*(n:ℝ))) :=
        div_le_div₀ (by positivity) (by nlinarith) (by positivity) hg
      _ = 72*Real.pi/(1000000000*(n:ℝ)^3) := by field_simp; ring
  have hsmall : Real.pi*n*epsilon n ≤ Real.pi/(1000000000*(n:ℝ)^3) := by
    unfold epsilon; rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]; have hn2 : (1:ℝ) ≤ (n:ℝ)^2 := one_le_pow₀ (by linarith)
    have hm := mul_le_mul_of_nonneg_left hn2 (show 0 ≤ Real.pi*(n:ℝ)^4 by positivity); nlinarith
  have heq : 72*Real.pi/(1000000000*(n:ℝ)^3) + Real.pi/(1000000000*(n:ℝ)^3) =
      73*Real.pi/(1000000000*(n:ℝ)^3) := by ring
  linarith
section AnchorTools
open scoped Matrix.Norms.L2Operator
def resolvent (m : ℕ) (r : ℝ) : Matrix (Fin m) (Fin m) ℝ := r • 1 + band m
theorem resolvent_isUnit (m : ℕ) {r : ℝ} (hr : 5 < r) : IsUnit (resolvent m r) := by
  have hrpos : 0 < r := by linarith
  have hsmall : ‖-(r⁻¹ • band m)‖ < 1 := by
    rw [norm_neg,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hrpos.le)]
    calc r⁻¹*‖band m‖ ≤ r⁻¹*4 := mul_le_mul_of_nonneg_left (band_norm_bound m) (by positivity)
      _ < 1 := by rw [inv_mul_eq_div,div_lt_one hrpos]; linarith
  have hu := isUnit_one_sub_of_norm_lt_one hsmall; have hfact : resolvent m r = (r • (1 : Matrix (Fin m) (Fin m) ℝ))*(1-(-(r⁻¹ • band m))) := by
    unfold resolvent; simp only [sub_neg_eq_add,Matrix.mul_add,Matrix.smul_mul,Matrix.one_mul,
      Matrix.mul_smul,smul_smul]
    rw [inv_mul_cancel₀ hrpos.ne']
    simp
  rw [hfact]; apply IsUnit.mul _ hu
  simpa only [Algebra.algebraMap_eq_smul_one] using
    (isUnit_iff_ne_zero.mpr hrpos.ne').map (algebraMap ℝ (Matrix (Fin m) (Fin m) ℝ))
def anchorInterior (m : ℕ) (r : ℝ) : Fin m → ℝ := (resolvent m r)⁻¹ *ᵥ spike m
theorem anchorInterior_solve (m : ℕ) {r : ℝ} (hr : 5 < r) : resolvent m r *ᵥ anchorInterior m r = spike m := by
  letI := (resolvent_isUnit m hr).invertible; unfold anchorInterior; rw [Matrix.mulVec_mulVec,Matrix.mul_inv_of_invertible,Matrix.one_mulVec]
theorem anchorInterior_positive (m : ℕ) {r : ℝ} (hr : 5 < r) : ∀ i, 0 < anchorInterior m r i ∧ (r-5)/r^2 ≤ anchorInterior m r i :=
  anchor_interior_positive m hr _ (anchorInterior_solve m hr)
theorem band_reverse (m : ℕ) (i j : Fin m) : band m i.rev j.rev = band m i j := by
  unfold band; have hi := i.isLt; have hj := j.isLt; simp only [Fin.val_rev]
  split_ifs <;> first | rfl | omega
private theorem resolvent_reverse (m : ℕ) (r : ℝ) (i j : Fin m) : resolvent m r i.rev j.rev = resolvent m r i j := by
  simp only [resolvent,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,
    (Fin.rev_injective.eq_iff),band_reverse]
private theorem reverse_solve (m : ℕ) {r : ℝ} (hr : 5 < r) : resolvent m r *ᵥ (fun i => anchorInterior m r i.rev) = fun i => spike m i.rev := by
  ext i
  have hs := congrFun (anchorInterior_solve m hr) i.rev; simp only [Matrix.mulVec,dotProduct] at hs ⊢; rw [← Equiv.sum_comp (Fin.revPerm)]; simp only [Fin.revPerm_apply,Fin.rev_rev]
  calc (∑ x, resolvent m r i x.rev * anchorInterior m r x) =
      ∑ x, resolvent m r i.rev x * anchorInterior m r x := by
        apply Finset.sum_congr rfl
        intro x hx; rw [← resolvent_reverse m r i x.rev,Fin.rev_rev]
    _ = spike m i.rev := hs
end AnchorTools
section CoordinateBounds
private theorem band_mul_coordinateNorm (m : ℕ) (v : Fin m → ℝ) : norm (band m *ᵥ v) ≤ 4*norm v := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  calc ‖(band m *ᵥ v) i‖ ≤ ∑ j, ‖band m i j*v j‖ := by
        simpa only [Matrix.mulVec,dotProduct] using norm_sum_le Finset.univ (fun j => band m i j*v j)
    _ = ∑ j, ‖band m i j‖*‖v j‖ := by simp only [norm_mul]
    _ ≤ ∑ j, ‖band m i j‖*‖v‖ := by
      apply Finset.sum_le_sum
      intro j hj; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg _)
    _ = (∑ j, ‖band m i j‖)*‖v‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ 4*‖v‖ := mul_le_mul_of_nonneg_right (band_row_bound m i) (norm_nonneg _)
private theorem spike_norm_upper (m : ℕ) : norm (spike m) ≤ 2 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro i; unfold spike
  split_ifs <;> norm_num
private theorem anchorInterior_coordinateNorm_upper (m : ℕ) {r : ℝ} (hr : 5 < r) : norm (anchorInterior m r) ≤ 2/(r-4) := by
  have hs := anchorInterior_solve m hr; simp only [resolvent,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec] at hs; have hseq : r • anchorInterior m r = spike m-band m *ᵥ anchorInterior m r :=
    eq_sub_of_add_eq hs
  have hnorm : r*‖anchorInterior m r‖ ≤ 2+4*‖anchorInterior m r‖ := by
    calc r*‖anchorInterior m r‖ = ‖r • anchorInterior m r‖ := by
          rw [norm_smul,Real.norm_of_nonneg (by linarith)]
      _ = ‖spike m-band m *ᵥ anchorInterior m r‖ := congrArg norm hseq
      _ ≤ ‖spike m‖+‖band m *ᵥ anchorInterior m r‖ := norm_sub_le _ _
      _ ≤ 2+4*‖anchorInterior m r‖ := add_le_add (spike_norm_upper m) (band_mul_coordinateNorm m _)
  apply (le_div_iff₀ (by linarith : 0<r-4)).mpr; nlinarith
theorem anchorInterior_upper (m : ℕ) {r : ℝ} (hr : 5 < r) (i : Fin m) : anchorInterior m r i ≤ 2/(r-4) := by
  exact (le_abs_self _).trans ((norm_le_pi_norm (anchorInterior m r) i).trans
    (anchorInterior_coordinateNorm_upper m hr))
end CoordinateBounds
theorem pencil_top_largest {n : ℕ} (hn : 0 < n) {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) : let k₀ : Fin (Fintype.card (Fin n)) := ⟨0,by simpa using hn⟩
    let r := hA.eigenvalues₀ k₀
    (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.pencil A r).det=0 ∧ ∀ s : ℝ, (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.pencil A s).det=0 → s ≤ r := by
  dsimp only; let k₀ : Fin (Fintype.card (Fin n)) := ⟨0,by simpa using hn⟩; let e : Fin (Fintype.card (Fin n)) ≃ Fin n := Fintype.equivOfCardEq (Fintype.card_fin _)
  have hmax (i : Fin n) : hA.eigenvalues i ≤ hA.eigenvalues₀ k₀ :=
    hA.eigenvalues₀_antitone (show k₀ ≤ e.symm i from Nat.zero_le _)
  constructor
  · rw [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.det_pencil hA]
    apply Finset.prod_eq_zero (Finset.mem_univ (e k₀)); have he : hA.eigenvalues (e k₀) = hA.eigenvalues₀ k₀ := by
      simp [Matrix.IsHermitian.eigenvalues,e]
    rw [he]; simp [k₀]
  · intro s hs
    rw [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.det_pencil hA] at hs
    obtain ⟨i,hi,hsi⟩ := Finset.prod_eq_zero_iff.mp hs; have hsi' : s=hA.eigenvalues i := by
      exact sub_eq_zero.mp (Complex.ofReal_eq_zero.mp hsi)
    exact hsi'.le.trans (hmax i)
theorem simple_root_of_rank {n : ℕ} (hn : 0<n) {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) {r : ℝ} (hroot : (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.pencil A
    r).det=0) (hrank : (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.pencil A r).rank=n-1) : ∃ d : ℝ, d≠0 ∧ HasDerivAt (fun s : ℝ=>(D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.pencil A s).det.re) d r := by
  let f : Fin n→ℝ := fun i=>r-hA.eigenvalues i; have hprod : ∏ i,f i=0 := by rw [←D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.det_pencil_re hA,hroot]; rfl
  obtain ⟨i,hi,hfi⟩ := Finset.prod_eq_zero_iff.mp hprod; have hrd : (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.pencil A r).rank=(diagonal (fun i=>((f i:ℝ):ℂ))).rank := by
    rw [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.pencil_conjugate hA,Unitary.conjStarAlgAut_apply,←Unitary.coe_star]; rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.UnitaryGroup.det_isUnit (star hA.eigenvectorUnitary)),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.UnitaryGroup.det_isUnit hA.eigenvectorUnitary)]
  have hcard : Fintype.card {j // f j=0}=1 := by
    rw [hrd,Matrix.rank_diagonal] at hrank; let e : {j // (f j:ℂ)≠0} ≃ {j // ¬f j=0} := Equiv.subtypeEquivRight (fun j=>by simp); rw [Fintype.card_congr e,Fintype.card_subtype_compl] at hrank
    have hpos : 0<Fintype.card {j // f j=0} := Fintype.card_pos_iff.mpr ⟨⟨i,hfi⟩⟩; simp only [Fintype.card_fin] at hrank; have hle : Fintype.card {j // f j=0}≤n := by
      simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun j=>f j=0)
    omega
  have hsub : Subsingleton {j // f j=0} := Fintype.card_le_one_iff_subsingleton.mp hcard.le; have hu : ∀ j,f j=0→j=i := by
    intro j hj; exact congrArg Subtype.val (hsub.elim (⟨j,hj⟩:{j // f j=0}) ⟨i,hfi⟩)
  let d := ∏ j∈Finset.univ.erase i,f j; have hd : d≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj hz; exact (Finset.mem_erase.mp hj).1 (hu j hz)
  have hsum : (∑ k : Fin n,∏ j∈Finset.univ.erase k,f j)=d := by
    apply Finset.sum_eq_single i
    · intro k hk hki
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hki,Finset.mem_univ i⟩) hfi
    · simp
  refine ⟨d,hd,?_⟩; have hh := HasDerivAt.fun_finsetProd (u:=Finset.univ) (f:=fun i s=>s-hA.eigenvalues i)
    (f':=fun _=>(1:ℝ)) (fun i _=>(hasDerivAt_id r).sub_const (hA.eigenvalues i))
  have hh' : HasDerivAt (fun s : ℝ=>(D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.pencil A s).det.re)
      (∑ k : Fin n,∏ j∈Finset.univ.erase k,f j) r := by
    simpa only [←D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.det_pencil_re hA,smul_eq_mul,mul_one,f] using hh
  rwa [hsum] at hh'
theorem negative_eigenvalue_perturbation {n : ℕ} (hn : 3≤n) (k : Fin (Fintype.card (Fin n))) : |((D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_hermitian hn (alpha n) (beta n)
    0).neg).eigenvalues₀ k- ((D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_hermitian hn (anchorAlpha n) (beta n) 0).neg).eigenvalues₀ k|≤ 2*Real.pi/(1000000000*(n:ℝ)^4) := by
  have hh := D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.abs_eigenvalues0_sub_le_of_entry_le
    (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_hermitian hn (anchorAlpha n) (beta n) 0).neg
    (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_hermitian hn (alpha n) (beta n) 0).neg
    (fun i j=>by simpa only [Matrix.neg_apply,neg_sub_neg,norm_sub_rev] using entry_perturbation hn i j 0) k
  have hnz : (n:ℝ)≠0 := by positivity
  have heq : (n:ℝ)*(2*(Real.pi*n*epsilon n))=2*Real.pi/(1000000000*(n:ℝ)^4) := by
    unfold epsilon; field_simp
  simpa only [heq] using hh
theorem top_root_simple {n : ℕ} (hn : 0<n) {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hstrict : ∀ k : Fin (Fintype.card (Fin
    n)),k.val≠0→ hA.eigenvalues₀ k<hA.eigenvalues₀ ⟨0,by simpa using hn⟩) : let r := hA.eigenvalues₀ ⟨0,by simpa using hn⟩
    ∃ d : ℝ,d≠0 ∧ HasDerivAt (fun s : ℝ=>(D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.pencil A s).det.re) d r := by
  let k₀ : Fin (Fintype.card (Fin n)) := ⟨0,by simpa using hn⟩; let r := hA.eigenvalues₀ k₀; let e : Fin (Fintype.card (Fin n)) ≃ Fin n := Fintype.equivOfCardEq (Fintype.card_fin _)
  have he (j : Fin n) : r-hA.eigenvalues j=0 ↔ j=e k₀ := by
    change r-hA.eigenvalues₀ (e.symm j)=0 ↔ j=e k₀
    constructor
    · intro hj
      by_contra hne
      have hval : (e.symm j).val≠0 := by
        intro hh; have hh' : e.symm j=k₀ := Fin.ext hh; exact hne (by rw [←hh',Equiv.apply_symm_apply])
      have hs:=hstrict (e.symm j) hval; have hEq:=sub_eq_zero.mp hj; exact (ne_of_lt hs) hEq.symm
    · rintro rfl
      simp [r]
  have hrank : (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.pencil A r).rank=n-1 := by
    rw [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.pencil_conjugate hA,Unitary.conjStarAlgAut_apply,←Unitary.coe_star]; rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.UnitaryGroup.det_isUnit (star hA.eigenvectorUnitary)),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.UnitaryGroup.det_isUnit hA.eigenvectorUnitary),Matrix.rank_diagonal]
    let e' : {j // ((r-hA.eigenvalues j:ℝ):ℂ)≠0} ≃ {j // ¬j=e k₀} :=
      Equiv.subtypeEquivRight (fun j=>by simpa only [ne_eq,Complex.ofReal_eq_zero] using not_congr (he j))
    rw [Fintype.card_congr e',Fintype.card_subtype_compl,Fintype.card_subtype_eq]; simp only [Fintype.card_fin]
  exact simple_root_of_rank hn hA (pencil_top_largest hn hA).1 hrank
end Uniform

open Matrix
open scoped ComplexConjugate
namespace Anchor17Probe
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
abbrev R : ℝ := 161/32
abbrev den : ℤ := 467481426546007099229949447217505
def numerators : Fin 15 → ℤ := ![54327066786808963613640806075424,162449231862550997644964313113664,31699139912323503403854828536864,31613948584422024541176559469600,59604881628347486929523162482720,54670494327411800278812578252832,49610783029226477391942069717024,51590888719220490214531871213600,52010909755231607428873297004576,51622580565559122738458025199648,52977284525991984008498705532960,51176235075093681300178634180640,46129738378725518219680378619936,59271390354165390221788584643616,71966270372793280156716617928736]
private def mint : Matrix (Fin 15) (Fin 15) ℤ := fun i j =>
  if i=j then 161 else if i.val+1=j.val ∨ j.val+1=i.val ∨ i.val+2=j.val ∨ j.val+2=i.val then 32 else 0
private def cint : Fin 15 → ℤ := fun i => if i.val=1 then 2 else 1
def u : Fin 15 → ℝ := fun i => (numerators i : ℝ) / den
private theorem integer_solve : mint *ᵥ numerators = (32*den) • cint := by decide
private theorem entry_scale (i j : Fin 15) : (mint i j : ℝ) = 32*((R • (1 : Matrix (Fin 15) (Fin 15) ℝ) + Uniform.band 15) i j) := by
  by_cases hij : i=j
  · subst j
    norm_num [mint,R,Uniform.band, Matrix.one_apply]
  · simp only [mint,hij,if_false,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Uniform.band]
    split_ifs <;> norm_num
theorem rational_solve : (R • (1 : Matrix (Fin 15) (Fin 15) ℝ) + Uniform.band 15) *ᵥ u = Uniform.spike 15 := by
  ext i
  have hc := congrArg (fun v : ℤ => (v:ℝ)) (congrFun integer_solve i); simp only [Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul,Int.cast_sum,
    Int.cast_mul,Int.cast_ofNat] at hc
  have hci : (cint i : ℝ) = Uniform.spike 15 i := by unfold cint Uniform.spike; split_ifs <;> norm_num
  rw [hci] at hc; have hsum : ((R • (1 : Matrix (Fin 15) (Fin 15) ℝ) + Uniform.band 15) *ᵥ u) i =
      (∑ j, (mint i j : ℝ)*(numerators j : ℝ))/(32*(den:ℝ)) := by
    simp only [Matrix.mulVec,dotProduct,u]; rw [Finset.sum_div]; apply Finset.sum_congr rfl
    intro j hj; rw [entry_scale]; field_simp
  rw [hsum]; rw [hc]; norm_num [den]
abbrev knum : ℤ := 1043170075740423325737604745085504
abbrev lnum : ℤ := 939992234232037718314429016615456
private theorem k_integer : ∑ i, cint i*numerators i = knum := by decide
private theorem ell_integer : ∑ i, cint i*numerators i.rev = lnum := by decide
theorem k_value : Uniform.spike 15 ⬝ᵥ u = (knum:ℝ)/den := by
  have h := congrArg (fun x : ℤ => (x:ℝ)) k_integer; push_cast at h; unfold dotProduct u; simp only [← mul_div_assoc]; rw [← Finset.sum_div]; congr 1
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi; unfold cint Uniform.spike
  split_ifs <;> norm_num
  norm_num [knum]
theorem ell_value : Uniform.spike 15 ⬝ᵥ (fun i => u i.rev) = (lnum:ℝ)/den := by
  have h := congrArg (fun x : ℤ => (x:ℝ)) ell_integer; push_cast at h; unfold dotProduct u; simp only [← mul_div_assoc]; rw [← Finset.sum_div]; congr 1
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi; unfold cint Uniform.spike
  split_ifs <;> norm_num
  norm_num [lnum]
def aa : ℂ := (Real.sqrt 2/2:ℝ) + (Real.sqrt 2/2:ℝ)*Complex.I
theorem aa_anchor : aa=Complex.exp (Complex.I*(Real.pi/4:ℝ)) := by
  rw [mul_comm,Complex.exp_mul_I]; change aa=Complex.cos ((Real.pi/4:ℝ):ℂ)+Complex.sin ((Real.pi/4:ℝ):ℂ)*Complex.I; rw [←Complex.ofReal_cos,←Complex.ofReal_sin,Real.cos_pi_div_four,Real.sin_pi_div_four]; simp [aa]
def probeSchur : Matrix (Fin 2) (Fin 2) ℂ := !![((R-(knum:ℝ)/den:ℝ):ℂ),-1-conj aa*((lnum:ℝ)/den:ℝ);-1-aa*((lnum:ℝ)/den:ℝ),((R-(knum:ℝ)/den:ℝ):ℂ)]
theorem schur_det_negative : (det probeSchur).re < 0 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num); have hp : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _; have hl : 7/5 < Real.sqrt 2 := by nlinarith
  norm_num [probeSchur,Matrix.det_fin_two,R,knum,lnum,den,aa,Complex.mul_re,
    Complex.mul_im,Complex.conj_re,Complex.conj_im,Complex.sub_re,Complex.add_re,
    Complex.sub_im,Complex.add_im,map_div,map_ofNat]
  nlinarith
end Anchor17Probe

open Matrix
open scoped ComplexConjugate ComplexOrder
namespace Anchor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
def a : ℂ := Complex.exp (Complex.I*(Real.pi:ℂ)*(1/4))
def address (m : ℕ) : Fin 2 ⊕ Fin m ≃ Fin (m+2) :=
  (Equiv.sumCongr (finSumFinEquiv (m := 1) (n := 1)).symm (Equiv.refl (Fin m))).trans
    ((Equiv.sumAssoc (Fin 1) (Fin 1) (Fin m)).trans
      ((Equiv.sumCongr (Equiv.refl (Fin 1)) (Equiv.sumComm (Fin 1) (Fin m))).trans
        ((Equiv.sumCongr (Equiv.refl (Fin 1)) (finSumFinEquiv (m := m) (n := 1))).trans
          ((finSumFinEquiv (m := 1) (n := m + 1)).trans (finCongr (by omega))))))
def endpoints (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![(r:ℂ),-1;-1,(r:ℂ)]
def coupling (m : ℕ) : Matrix (Fin m) (Fin 2) ℂ := fun i j => if j.val=0 then a*(Uniform.spike m i : ℂ) else (Uniform.spike m i.rev : ℂ)
def interior (m : ℕ) (r : ℝ) : Matrix (Fin m) (Fin m) ℂ := Matrix.map (Uniform.resolvent m r) Complex.ofReal
def block (m : ℕ) (r : ℝ) : Matrix (Fin 2 ⊕ Fin m) (Fin 2 ⊕ Fin m) ℂ := Matrix.fromBlocks (endpoints r) (coupling m)ᴴ (coupling m) (interior m r)
theorem phase_def : Complex.exp (Complex.I*(Real.pi/4 : ℝ)) = a := by
  unfold a; congr 1; push_cast; ring
theorem phase_unit : ‖a‖=1 := by
  rw [← phase_def]; exact Complex.norm_exp_I_mul_ofReal _
theorem phase_mul_conj : a*conj a=1 := by
  have h := Complex.mul_conj a
  simpa [Complex.normSq_eq_norm_sq,phase_unit] using h
theorem anchor_reindex (m : ℕ) (hm : 4 ≤ m) (r : ℝ) : (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (Uniform.anchorAlpha (m+2)) (Uniform.beta (m+2)) r).submatrix (address m)
    (address m) = block m r := by
  have hleft (i : Fin 2) : address m (Sum.inl i) =
      if i.val = 0 then ⟨0, by omega⟩ else ⟨m+1, by omega⟩ := by
    fin_cases i <;> apply Fin.ext <;>
      simp [address, finSumFinEquiv, Fin.addCases, Equiv.sumAssoc, Equiv.sumComm]
  have hright (i : Fin m) : address m (Sum.inr i) = ⟨i.val+1, by omega⟩ := by
    apply Fin.ext
    simp [address, finSumFinEquiv, Nat.add_comm]
  ext s t
  cases s with
  | inl i =>
    cases t with
    | inl j => fin_cases i <;> fin_cases j <;>
        simp [hleft,hright,block,endpoints,D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D,Uniform.anchorAlpha,Uniform.beta] <;> omega
    | inr j =>
      have hj := j.isLt
      fin_cases i <;>
        simp [hleft,hright,block,coupling,D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D,Uniform.anchorAlpha,Uniform.beta,
          Uniform.spike,Fin.val_rev,phase_def,map_mul] <;> split_ifs <;> simp_all [phase_mul_conj] <;> first | omega | (solve | ring) | (solve | simp only [a,Complex.ofReal_div,Complex.ofReal_ofNat,div_eq_mul_inv,mul_assoc,one_mul,mul_comm]) | (solve | simpa only [a,div_eq_mul_inv,mul_assoc,one_mul,mul_comm] using phase_mul_conj)
  | inr i =>
    have hi := i.isLt
    cases t with
    | inl j => fin_cases j <;>
        simp [hleft,hright,block,coupling,D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D,Uniform.anchorAlpha,Uniform.beta,
          Uniform.spike,Fin.val_rev,phase_def] <;> split_ifs <;> simp_all [phase_mul_conj] <;> first | omega | (solve | ring) | (solve | simp only [a,Complex.ofReal_div,Complex.ofReal_ofNat,div_eq_mul_inv,mul_assoc,one_mul,mul_comm]) | (solve | simpa only [a,div_eq_mul_inv,mul_assoc,one_mul,mul_comm] using phase_mul_conj)
    | inr j =>
      have hj := j.isLt
      by_cases hij : i=j
      · subst j; simp [hleft,hright,block,interior,Uniform.resolvent,Uniform.band,D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D]
      · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
        simp [hleft,hright,block,interior,Uniform.resolvent,Uniform.band,D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D,
          Uniform.anchorAlpha,Uniform.beta,hij,hv,phase_mul_conj] <;>
          split_ifs <;> simp_all [phase_def,phase_mul_conj] <;> first | omega | (solve | ring) | (solve | simp only [a,Complex.ofReal_div,Complex.ofReal_ofNat,div_eq_mul_inv,mul_assoc,one_mul,mul_comm]) | (solve | simpa only [a,div_eq_mul_inv,mul_assoc,one_mul,mul_comm] using phase_mul_conj)
def k (m : ℕ) (r : ℝ) : ℝ := Uniform.spike m ⬝ᵥ Uniform.anchorInterior m r
def ell (m : ℕ) (r : ℝ) : ℝ := Uniform.spike m ⬝ᵥ (fun (m : ℕ) (r : ℝ) (i : Fin m) => Uniform.anchorInterior m r i.rev) m r
private theorem reflected_k (m : ℕ) (r : ℝ) : (fun i => Uniform.spike m i.rev) ⬝ᵥ (fun (m : ℕ) (r : ℝ) (i : Fin m) => Uniform.anchorInterior m r i.rev) m r = k m r := by
  unfold k dotProduct; exact (Equiv.sum_comp Fin.revPerm (fun i => Uniform.spike m i*Uniform.anchorInterior m r i))
private theorem reflected_ell (m : ℕ) {r : ℝ} (hr : 5<r) : (fun i => Uniform.spike m i.rev) ⬝ᵥ Uniform.anchorInterior m r = ell m r := by
  have hsym : (Uniform.resolvent m r)ᵀ = Uniform.resolvent m r := by
    rw [Uniform.resolvent,Matrix.transpose_add,Matrix.transpose_smul,Matrix.transpose_one]; congr 1
    ext i j
    simpa only [Matrix.transpose_apply,Matrix.conjTranspose_apply,star_trivial] using
      congrFun (congrFun (Uniform.band_hermitian m) i) j
  have h := dotProduct_transpose_mulVec (Uniform.resolvent m r) (Uniform.anchorInterior m r) ((fun (m : ℕ) (r : ℝ) (i : Fin m) => Uniform.anchorInterior m r i.rev) m r); change Uniform.anchorInterior m r ⬝ᵥ (Uniform.resolvent m r)ᵀ *ᵥ (fun i => Uniform.anchorInterior m r i.rev) =
    (fun i => Uniform.anchorInterior m r i.rev) ⬝ᵥ Uniform.resolvent m r *ᵥ Uniform.anchorInterior m r at h
  rw [hsym,Uniform.reverse_solve m hr,Uniform.anchorInterior_solve m hr] at h; unfold ell
  calc (fun i => Uniform.spike m i.rev) ⬝ᵥ Uniform.anchorInterior m r =
      Uniform.anchorInterior m r ⬝ᵥ (fun i => Uniform.spike m i.rev) := dotProduct_comm _ _
    _ = _ := h.trans (dotProduct_comm _ _)
def zeta (m : ℕ) (r : ℝ) : ℂ := 1+a*(ell m r:ℂ)
def b (m : ℕ) (r : ℝ) : ℂ := NormedSpace.normalize (zeta m r)
def kernelBlock (m : ℕ) (r : ℝ) : Fin 2 ⊕ Fin m → ℂ := Sum.elim ![conj (b m r),1] (fun i => -(a*conj (b m r)*(Uniform.anchorInterior m r i : ℂ)+((fun (m : ℕ) (r : ℝ) (i : Fin m) => Uniform.anchorInterior m r i.rev) m r i : ℂ)))
def kernel (m : ℕ) (r : ℝ) : Fin (m+2) → ℂ := fun i => kernelBlock m r ((address m).symm i)
private theorem interior_U_solve (m : ℕ) {r : ℝ} (hr : 5<r) : interior m r *ᵥ (fun i => (Uniform.anchorInterior m r i : ℂ)) = fun i => (Uniform.spike m i : ℂ) := by
  ext i
  have h := congrArg (fun x : ℝ => (x:ℂ)) (congrFun (Uniform.anchorInterior_solve m hr) i)
  simpa only [interior,Matrix.map_apply,Matrix.mulVec,dotProduct,Complex.ofReal_sum,Complex.ofReal_mul] using h
private theorem interior_V_solve (m : ℕ) {r : ℝ} (hr : 5<r) : interior m r *ᵥ (fun i => ((fun (m : ℕ) (r : ℝ) (i : Fin m) => Uniform.anchorInterior m r i.rev) m r i : ℂ)) = fun i => (Uniform.spike m i.rev : ℂ) := by
  ext i
  have h := congrArg (fun x : ℝ => (x:ℂ)) (congrFun (Uniform.reverse_solve m hr) i)
  simpa only [interior,Matrix.map_apply,Matrix.mulVec,dotProduct,Complex.ofReal_sum,Complex.ofReal_mul] using h
theorem a_cartesian : a=((D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2.re):ℂ)+((D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2.re):ℂ)*Complex.I := by
  rw [← phase_def,mul_comm,Complex.exp_mul_I]; change Complex.cos ((Real.pi/4:ℝ):ℂ)+Complex.sin ((Real.pi/4:ℝ):ℂ)*Complex.I = _; rw [← Complex.ofReal_cos,← Complex.ofReal_sin,Real.cos_pi_div_four,Real.sin_pi_div_four]
  rfl
theorem h_positive : 0<(D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2.re) := by
  change 0 < Real.sqrt 2 / 2
  positivity
theorem ell_positive {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 5<r) : 0<ell m r := by
  unfold ell dotProduct; apply Finset.sum_pos'
  · intro i hi
    exact mul_nonneg (by linarith [Uniform.spike_lower m i])
      (Uniform.anchorInterior_positive m hr i.rev).1.le
  · exact ⟨⟨0,hm⟩,Finset.mem_univ _,mul_pos
      (by linarith [Uniform.spike_lower m ⟨0,hm⟩])
      (Uniform.anchorInterior_positive m hr (Fin.rev ⟨0,hm⟩)).1⟩
theorem zeta_re (m : ℕ) (r : ℝ) : (zeta m r).re=1+(D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2.re)*ell m r := by simp [zeta,a_cartesian,Complex.mul_re]
theorem zeta_im (m : ℕ) (r : ℝ) : (zeta m r).im=(D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2.re)*ell m r := by simp [zeta,a_cartesian,Complex.mul_im]
theorem zeta_norm_pos {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 5<r) : 0<‖zeta m r‖ := by
  have hp : 0<(zeta m r).re := by
    rw [zeta_re]
    exact add_pos (by norm_num) (mul_pos h_positive (ell_positive hm hr))
  exact hp.trans_le (Complex.re_le_norm _)
theorem b_unit {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 5<r) : ‖b m r‖=1 := by
  exact NormedSpace.norm_normalize (norm_pos_iff.mp (zeta_norm_pos hm hr))
def d (m : ℕ) (r : ℝ) : ℂ := a*conj (b m r)
theorem d_unit {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 5<r) : ‖d m r‖=1 := by
  simp [d,norm_mul,Complex.norm_conj,phase_unit,b_unit hm hr]
theorem d_im_pos {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 5<r) : 0<(d m r).im := by
  have hn := zeta_norm_pos hm hr; have hz : d m r=(a+(ell m r:ℂ))/(‖zeta m r‖:ℂ) := by
    have hb : b m r = zeta m r / (‖zeta m r‖ : ℂ) := by
      simp only [b, NormedSpace.normalize, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]
    unfold d; rw [hb]; unfold zeta; simp only [map_div₀,map_add,map_mul,map_one,Complex.conj_ofReal]; rw [←mul_div_assoc,mul_add]; congr 1
    linear_combination (ell m r:ℂ)*phase_mul_conj
  rw [hz,Complex.div_ofReal_im]; simp only [Complex.add_im,Complex.ofReal_im,add_zero]; rw [a_cartesian]
  simpa using div_pos h_positive hn
theorem coupling_real (m : ℕ) (f : Fin m → ℝ) : (coupling m)ᴴ *ᵥ (fun i => (f i:ℂ)) = ![conj a*((Uniform.spike m ⬝ᵥ f:ℝ):ℂ), (((fun i =>
    Uniform.spike m i.rev) ⬝ᵥ f:ℝ):ℂ)] := by
  ext j
  fin_cases j <;> simp [Matrix.mulVec,dotProduct,Matrix.conjTranspose_apply,coupling,
    map_mul,Complex.conj_ofReal,←Complex.ofReal_sum,←Complex.ofReal_mul,
    ←Finset.mul_sum,mul_assoc]
private theorem block_kernel {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 5<r) (heq : r-k m r = ‖zeta m r‖) : block m r *ᵥ kernelBlock m r = 0 := by
  have hu := interior_U_solve m hr; have hv := interior_V_solve m hr; have hU := coupling_real m (Uniform.anchorInterior m r); have hV := coupling_real m ((fun (m : ℕ) (r : ℝ) (i : Fin m) => Uniform.anchorInterior m r i.rev) m r); rw [reflected_ell m hr] at hU; rw [reflected_k] at hV
  change (coupling m)ᴴ *ᵥ (fun i => (Uniform.anchorInterior m r i:ℂ)) = ![conj a*(k m r:ℂ),(ell m r:ℂ)] at hU; change (coupling m)ᴴ *ᵥ (fun i => ((fun (m : ℕ) (r : ℝ) (i : Fin m) => Uniform.anchorInterior m r i.rev) m r i:ℂ)) = ![conj a*(ell m r:ℂ),(k m r:ℂ)] at hV; have hn := zeta_norm_pos hm hr
  have hz : (‖zeta m r‖:ℂ)*b m r=zeta m r := by
    simpa only [b, Complex.real_smul] using NormedSpace.norm_smul_normalize (zeta m r)
  have hzc := congrArg conj hz; simp only [map_mul,Complex.conj_ofReal] at hzc; have hb : b m r*conj (b m r)=1 := by
    simpa [b_unit hm hr] using Complex.mul_conj' (b m r)
  simp only [block,Matrix.fromBlocks_mulVec,kernelBlock,Function.comp_def,Sum.elim_inl,Sum.elim_inr]
  ext s
  cases s with
  | inl j =>
    have hcy : (coupling m)ᴴ *ᵥ (fun i => -(a*conj (b m r)*(Uniform.anchorInterior m r i:ℂ)+((fun (m : ℕ) (r : ℝ) (i : Fin m) => Uniform.anchorInterior m r i.rev) m r i:ℂ))) =
        -((a*conj (b m r)) • ((coupling m)ᴴ *ᵥ (fun i => (Uniform.anchorInterior m r i:ℂ)))+
          (coupling m)ᴴ *ᵥ (fun i => ((fun (m : ℕ) (r : ℝ) (i : Fin m) => Uniform.anchorInterior m r i.rev) m r i:ℂ))) := by
      change (coupling m)ᴴ *ᵥ (-((a*conj (b m r)) • (fun i => (Uniform.anchorInterior m r i:ℂ)) +
        (fun i => ((fun (m : ℕ) (r : ℝ) (i : Fin m) => Uniform.anchorInterior m r i.rev) m r i:ℂ)))) = _
      rw [Matrix.mulVec_neg,Matrix.mulVec_add,Matrix.mulVec_smul]
    rw [hcy,hU,hV]
    fin_cases j
    · simp [endpoints,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Pi.smul_apply,smul_eq_mul] at ⊢
      have hc : ((r-k m r:ℝ):ℂ)*conj (b m r)=1+conj a*(ell m r:ℂ) := by
        rw [heq]
        simpa [zeta,map_add,map_mul,Complex.conj_ofReal] using hzc
      have ha := phase_mul_conj; push_cast at hc; simp [Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Pi.smul_apply]
      linear_combination hc - (k m r:ℂ)*conj (b m r)*ha
    · simp [endpoints,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Pi.smul_apply,smul_eq_mul]
      have hc : ((r-k m r:ℝ):ℂ)=(1+a*(ell m r:ℂ))*conj (b m r) := by
        calc ((r-k m r:ℝ):ℂ) = (‖zeta m r‖:ℂ) := congrArg Complex.ofReal heq
          _ = ((‖zeta m r‖:ℂ)*b m r)*conj (b m r) := by rw [mul_assoc,hb,mul_one]
          _ = (1+a*(ell m r:ℂ))*conj (b m r) := by rw [hz]; rfl
      push_cast at hc; simp [Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Pi.smul_apply]
      linear_combination hc
  | inr i =>
    have hby : interior m r *ᵥ (fun i => -(a*conj (b m r)*(Uniform.anchorInterior m r i:ℂ)+((fun (m : ℕ) (r : ℝ) (i : Fin m) => Uniform.anchorInterior m r i.rev) m r i:ℂ))) =
        -((a*conj (b m r)) • (fun i => (Uniform.spike m i:ℂ))+
          (fun i => (Uniform.spike m i.rev:ℂ))) := by
      change interior m r *ᵥ (-((a*conj (b m r)) • (fun i => (Uniform.anchorInterior m r i:ℂ)) +
        (fun i => ((fun (m : ℕ) (r : ℝ) (i : Fin m) => Uniform.anchorInterior m r i.rev) m r i:ℂ)))) = _
      rw [Matrix.mulVec_neg,Matrix.mulVec_add,Matrix.mulVec_smul,hu,hv]
    rw [hby]; simp [Matrix.mulVec,dotProduct,coupling,Fin.sum_univ_two,Pi.smul_apply,smul_eq_mul]; ring
theorem actual_kernel {m : ℕ} (hm : 4 ≤ m) {r : ℝ} (hr : 5<r) (heq : r-k m r = ‖zeta m r‖) : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (Uniform.anchorAlpha (m+2)) (Uniform.beta
    (m+2)) r *ᵥ kernel m r = 0 := by
  have hb := block_kernel (by omega : 0 < m) hr heq; rw [←anchor_reindex m hm r,Matrix.submatrix_mulVec_equiv] at hb
  ext i
  obtain ⟨s,rfl⟩ := (address m).surjective i; exact congrFun hb s
theorem interior_hermitian (m : ℕ) (r : ℝ) : (interior m r).IsHermitian := by
  ext i j
  have hb := congrFun (congrFun (Uniform.band_hermitian m) i) j; have hb' : Uniform.band m j i=Uniform.band m i j := by
    simpa only [Matrix.conjTranspose_apply,star_trivial] using hb
  simp [Matrix.conjTranspose_apply,interior,Uniform.resolvent,Matrix.one_apply,eq_comm,hb']
theorem interior_posDef (m : ℕ) {r : ℝ} (hr : 5<r) : (interior m r).PosDef := by
  apply D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Path.scaled_dominance_posDef (interior_hermitian m r) (fun _ => 1) (by simp)
  intro i; simp only [inv_one,one_mul,mul_one]; have hrow : (∑ j∈Finset.univ.erase i,‖interior m r i j‖) ≤ 4 := by
    calc _ = ∑ j∈Finset.univ.erase i,‖Uniform.band m i j‖ := by
          apply Finset.sum_congr rfl
          intro j hj; have hne := (Finset.mem_erase.mp hj).1; simp [interior,Uniform.resolvent,Matrix.one_apply,Ne.symm hne,Complex.norm_real]
      _ ≤ ∑ j,‖Uniform.band m i j‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun j hj hj' => norm_nonneg _)
      _ ≤ 4 := Uniform.band_row_bound m i
  have hdiag : (interior m r i i).re=r := by simp [interior,Uniform.resolvent,Uniform.band]
  rw [hdiag]; linarith
def inverseCoupling (m : ℕ) (r : ℝ) : Matrix (Fin m) (Fin 2) ℂ := fun i j => if j.val=0 then a*(Uniform.anchorInterior m r i:ℂ) else ((fun (m : ℕ) (r : ℝ) (i : Fin m) => Uniform.anchorInterior m r i.rev) m r i:ℂ)
theorem inverseCoupling_solve (m : ℕ) {r : ℝ} (hr : 5<r) : interior m r * inverseCoupling m r = coupling m := by
  ext i j
  fin_cases j
  · have hu := congrFun (interior_U_solve m hr) i
    simp only [Matrix.mul_apply,inverseCoupling,coupling,Fin.val_zero,ite_true]
    calc (∑ x,interior m r i x*(a*(Uniform.anchorInterior m r x:ℂ))) =
          a*(interior m r *ᵥ (fun x => (Uniform.anchorInterior m r x:ℂ))) i := by
            simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]; congr 1; ext x; ring
      _ = _ := by rw [hu]
  · simpa only [Matrix.mul_apply,Matrix.mulVec,dotProduct,inverseCoupling,coupling,
      show (1:Fin 2).val=1 from rfl,show ¬(1:ℕ)=0 by omega,ite_false] using congrFun (interior_V_solve m hr) i
theorem inverseCoupling_eq (m : ℕ) {r : ℝ} (hr : 5<r) : (interior m r)⁻¹*coupling m = inverseCoupling m r := by
  letI := (interior_posDef m hr).isUnit.invertible; rw [←inverseCoupling_solve m hr,←Matrix.mul_assoc,Matrix.inv_mul_of_invertible,Matrix.one_mul]
def schur (m : ℕ) (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![((r-k m r:ℝ):ℂ),-1-conj a*(ell m r:ℂ);-1-a*(ell m r:ℂ),((r-k m r:ℝ):ℂ)]
theorem schur_eq (m : ℕ) {r : ℝ} (hr : 5<r) : endpoints r-(coupling m)ᴴ*(interior m r)⁻¹*coupling m = schur m r := by
  rw [Matrix.mul_assoc,inverseCoupling_eq m hr]; have hU := coupling_real m (Uniform.anchorInterior m r); have hV := coupling_real m ((fun (m : ℕ) (r : ℝ) (i : Fin m) => Uniform.anchorInterior m r i.rev) m r); rw [reflected_ell m hr] at hU; rw [reflected_k] at hV
  ext i j
  fin_cases j
  · have hc : ((coupling m)ᴴ*inverseCoupling m r) i 0 =
        a*((coupling m)ᴴ *ᵥ (fun x => (Uniform.anchorInterior m r x:ℂ))) i := by
      simp only [Matrix.mul_apply,inverseCoupling,Fin.val_zero,ite_true,Matrix.mulVec,dotProduct,Finset.mul_sum]; apply Finset.sum_congr rfl
      intro x hx; ring
    change endpoints r i 0 - ((coupling m)ᴴ*inverseCoupling m r) i 0 = schur m r i 0; rw [hc,hU]
    fin_cases i <;> simp [endpoints,schur,k,ell,Complex.ofReal_sub,phase_mul_conj,mul_assoc,mul_comm]
    linear_combination ((Uniform.spike m ⬝ᵥ Uniform.anchorInterior m r:ℝ):ℂ)*phase_mul_conj
  · have hc : ((coupling m)ᴴ*inverseCoupling m r) i 1 =
        ((coupling m)ᴴ *ᵥ (fun x => ((fun (m : ℕ) (r : ℝ) (i : Fin m) => Uniform.anchorInterior m r i.rev) m r x:ℂ))) i := by
      simp only [Matrix.mul_apply,inverseCoupling,show (1:Fin 2).val=1 from rfl,
        show ¬(1:ℕ)=0 by omega,ite_false,Matrix.mulVec,dotProduct]
    change endpoints r i 1 - ((coupling m)ᴴ*inverseCoupling m r) i 1 = schur m r i 1; rw [hc,hV]
    fin_cases i <;> simp [endpoints,schur,k,ell,Complex.ofReal_sub]
end Anchor
#print axioms Uniform.admissible
#print axioms Uniform.operator_perturbation
#print axioms Uniform.anchorInterior_positive
#print axioms Uniform.phase_aligned_stability
#print axioms Anchor.actual_kernel

end D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor
