/- GID: D5/S3/Quantum/Completion/PhaseOverlapReconstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/PhaseOverlapReconstruction
   mirror-E: none(waiver:unit-sphere-readout-bridge)
   anchors: []
   utility: none
   digest: Three phase-shifted pairwise distances reconstruct the complex unit-sphere overlap. -/

import D5.S3.QuadraticForms.ThreeWayPositiveKernel

/-! Three phase-shifted pairwise distances reconstruct a complex overlap. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators ComplexConjugate ComplexOrder
namespace D5.S3.Quantum.Completion.PhaseOverlapReconstruction
open D5.S3.QuadraticForms.ThreeWayPositiveKernel

private theorem norm_sub_smul_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x y : H) (α : ℂ) (hα : conj α * α = 1) :
    ‖x - α • y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * (inner ℂ x (α • y)).re := by
  have hi : inner ℂ (x - α • y) (x - α • y) =
      inner ℂ x x - inner ℂ x (α • y) - inner ℂ (α • y) x + inner ℂ (α • y) (α • y) := by
    simp only [sub_eq_add_neg, inner_add_left, inner_add_right, inner_neg_left,
      inner_neg_right]
    ring
  have hxy : inner ℂ x (α • y) = α * inner ℂ x y := inner_smul_right _ _ _
  have hyx : inner ℂ (α • y) x = conj α * inner ℂ y x := inner_smul_left _ _ _
  have hyy : inner ℂ (α • y) (α • y) = conj α * α * inner ℂ y y := by
    rw [inner_smul_left, inner_smul_right]
    ring
  rw [hxy, hyx, hyy] at hi
  have hr := congrArg Complex.re hi
  have hselfx : (inner ℂ x x).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hselfy : (inner ℂ y y).re = ‖y‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hselfz : (inner ℂ (x - α • y) (x - α • y)).re = ‖x - α • y‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hαre : α.re * α.re + α.im * α.im = 1 := by
    have h := congrArg Complex.re hα
    simpa [Complex.mul_re, Complex.conj_re, Complex.conj_im] using h
  have hαim : (conj α * α).im = 0 := by
    have h := congrArg Complex.im hα
    simpa [Complex.mul_im, Complex.conj_re, Complex.conj_im] using h
  simp only [Complex.mul_re, Complex.sub_re, Complex.add_re,
    Complex.conj_re, Complex.conj_im] at hr
  rw [hselfx, hselfy, hselfz, hαim] at hr
  have hconj : conj (inner ℂ y x) = inner ℂ x y := inner_conj_symm _ _
  have hcrossre : (inner ℂ y x).re = (inner ℂ x y).re := by
    have h := congrArg Complex.re hconj
    simpa only [Complex.conj_re] using h
  have hcrossim : (inner ℂ y x).im = -(inner ℂ x y).im := by
    have h := congrArg Complex.im hconj
    have h' : -(inner ℂ y x).im = (inner ℂ x y).im := by
      simpa only [Complex.conj_im] using h
    linarith
  rw [hcrossre, hcrossim] at hr
  have hxy_re : (inner ℂ x (α • y)).re =
      α.re * (inner ℂ x y).re - α.im * (inner ℂ x y).im := by
    rw [hxy]
    rfl
  rw [hxy_re]
  nlinarith [hr, hαre]

/-- The complex overlap reconstructed from three phase-shifted real comparisons. -/
def phaseOverlap {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x y : H) : ℂ :=
  (1 / 3 : ℂ) * (
    ((2 - ‖x - y‖ ^ 2 : ℝ) : ℂ) +
      conj omega * ((2 - ‖x - omega • y‖ ^ 2 : ℝ) : ℂ) +
      conj (omega ^ 2) * ((2 - ‖x - (omega ^ 2) • y‖ ^ 2 : ℝ) : ℂ))

private theorem omega_unit : conj omega * omega = 1 := by
  have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [omega, Complex.mul_re, Complex.mul_im] <;> nlinarith

private theorem omega_sq_coordinates : omega ^ 2 = ⟨-1 / 2, -Real.sqrt 3 / 2⟩ := by
  have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;>
    norm_num [omega, pow_two, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [hsqrt]

private theorem omega_sq_unit : conj (omega ^ 2) * omega ^ 2 = 1 := by
  rw [map_pow]
  calc
    (conj omega) ^ 2 * omega ^ 2 = (conj omega * omega) ^ 2 := by ring
    _ = 1 := by rw [omega_unit]; norm_num

private theorem phase_overlap_real_readouts {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (2 - ‖x - y‖ ^ 2 : ℝ) = 2 * (inner ℂ x y).re ∧
    (2 - ‖x - omega • y‖ ^ 2 : ℝ) =
      2 * (omega * inner ℂ x y).re ∧
    (2 - ‖x - (omega ^ 2) • y‖ ^ 2 : ℝ) =
      2 * (omega ^ 2 * inner ℂ x y).re := by
  have hnx : ‖x‖ ^ 2 = 1 := by rw [hx]; norm_num
  have hny : ‖y‖ ^ 2 = 1 := by rw [hy]; norm_num
  have h0 := norm_sub_smul_sq x y 1 (by norm_num)
  have h1 := norm_sub_smul_sq x y omega omega_unit
  have h2 := norm_sub_smul_sq x y (omega ^ 2) omega_sq_unit
  simp only [one_smul] at h0
  have h0' : ‖x - y‖ ^ 2 = 2 - 2 * (inner ℂ x y).re := by
    nlinarith [h0, hnx, hny]
  rw [inner_smul_right] at h1 h2
  have h1' : ‖x - omega • y‖ ^ 2 = 2 - 2 * (omega * inner ℂ x y).re := by
    simp only [Complex.mul_re] at h1 ⊢
    simp [omega] at h1 ⊢
    nlinarith [h1, hnx, hny]
  have h2' : ‖x - (omega ^ 2) • y‖ ^ 2 =
      2 - 2 * (omega ^ 2 * inner ℂ x y).re := by
    rw [omega_sq_coordinates] at h2 ⊢
    simp only [Complex.mul_re] at h2 ⊢
    nlinarith [h2, hnx, hny]
  constructor
  · linarith [h0']
  · constructor
    · linarith [h1']
    · linarith [h2']

/-- On the unit sphere, the three real phase comparisons recover the complex inner product. -/
theorem phaseOverlap_eq_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    phaseOverlap x y = inner ℂ x y := by
  rcases phase_overlap_real_readouts x y hx hy with ⟨h0, h1, h2⟩
  unfold phaseOverlap
  rw [h0, h1, h2]
  have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrt3 : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
    calc
      Real.sqrt 3 ^ 3 = Real.sqrt 3 ^ 2 * Real.sqrt 3 := by ring
      _ = 3 * Real.sqrt 3 := by rw [hsqrt]
  have hsqrt4 : Real.sqrt 3 ^ 4 = 9 := by
    calc
      Real.sqrt 3 ^ 4 = (Real.sqrt 3 ^ 2) ^ 2 := by ring
      _ = 9 := by rw [hsqrt]; norm_num
  apply Complex.ext <;>
    simp [omega, pow_two, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im] <;>
    ring_nf <;>
    simp only [hsqrt3, hsqrt4, hsqrt] <;>
    ring

/-- The reconstructed Born overlap has unit upper bound on normalized vectors. -/
theorem phaseOverlap_normSq_le_one {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    Complex.normSq (phaseOverlap x y) ≤ 1 := by
  rw [phaseOverlap_eq_inner x y hx hy]
  have hinner : ‖inner ℂ x y‖ ≤ 1 := by
    simpa [hx, hy] using (norm_inner_le_norm x y)
  have hsquare : ‖inner ℂ x y‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (by norm_num)).2 hinner
  rw [← Complex.sq_norm]
  simpa using hsquare

end D5.S3.Quantum.Completion.PhaseOverlapReconstruction
