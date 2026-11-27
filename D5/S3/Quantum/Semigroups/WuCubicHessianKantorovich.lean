import D5.S3.Quantum.Semigroups.WuCubicRelativeAnticommutator

/-! The Kantorovich moment estimate for the mixed-generator term of the conditioned
two-CAR Wu cubic Hessian. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Semigroups.WuCubicHessianKantorovich

open WuCubicOperatorBridge (Mat G GInv generator)
open WuCubicThermalBasis (Index degree coefficient)
open WuCubicTranslationEnergy (baseEntry sandwich vPairing)
open WuCubicConditionedHessian (embeddedGenerator mixedDual mixed_energy_ge_of_dual_moment
  mixed_energy_ge_of_dual_moment_bound)
open WuCubicRelativeAnticommutator (Entry Operator physicalRelative physicalWeight_bounds
  physicalRelative_normalized weightedVec weightedVec_sandwich_pairing
  physicalRelative_mixedDual_mulVec physicalRelative_quadratic)
open private G_mul_GInv GInv_mul_G from D5.S3.Quantum.Semigroups.WuCubicOperatorBridge

private theorem finite_kantorovich_sq {ι : Type*} [Fintype ι]
    {R C : ℝ} (hR : 1 ≤ R) (hfactor : (R + 1) ^ 2 ≤ 4 * R * C ^ 2)
    (p z : ι → ℝ) (hp : ∀ i, 1 ≤ p i ∧ p i ≤ R)
    (hz : ∀ i, 0 ≤ z i) :
    (∑ i, (p i) ^ 2 * z i) * (∑ i, z i) ≤ (C * ∑ i, p i * z i) ^ 2 := by
  let A : ℝ := ∑ i, z i
  let B : ℝ := ∑ i, p i * z i
  let Q : ℝ := ∑ i, (p i) ^ 2 * z i
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg (fun i _ => hz i)
  have hpoint (i : ι) : (p i) ^ 2 ≤ (R + 1) * p i - R := by
    have h := mul_nonneg (sub_nonneg.mpr (hp i).1)
      (sub_nonneg.mpr (hp i).2)
    nlinarith only [h]
  have hQ : Q ≤ (R + 1) * B - R * A := by
    dsimp only [Q, B, A]
    calc
      _ ≤ ∑ i, ((R + 1) * p i - R) * z i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hpoint i) (hz i)
      _ = _ := by
        calc
          _ = ∑ i, ((R + 1) * (p i * z i) - R * z i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = _ := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h4R : 0 < 4 * R := mul_pos (by norm_num) (zero_lt_one.trans_le hR)
  have hQA : (4 * R) * (Q * A) ≤ (R + 1) ^ 2 * B ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hQ hA) h4R.le
    have hs := sq_nonneg ((R + 1) * B - 2 * R * A)
    nlinarith only [hmul, hs]
  change Q * A ≤ (C * B) ^ 2
  apply le_of_mul_le_mul_left _ h4R
  calc
    _ ≤ (R + 1) ^ 2 * B ^ 2 := hQA
    _ ≤ (4 * R * C ^ 2) * B ^ 2 := mul_le_mul_of_nonneg_right hfactor (sq_nonneg B)
    _ = _ := by rw [mul_pow, mul_assoc]

theorem kantorovich_324 {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (u : ι → ℂ) (hp : ∀ i, 1 ≤ p i ∧ p i ≤ 324 / 125) :
    64 * (∑ i, (p i) ^ 2 * Complex.normSq (u i)) *
        (∑ i, Complex.normSq (u i)) ≤
      81 * (∑ i, p i * Complex.normSq (u i)) ^ 2 := by
  have hm := finite_kantorovich_sq (R := 324 / 125) (C := 9 / 8)
    (by norm_num) (by norm_num) p (fun i => Complex.normSq (u i)) hp
    (fun i => Complex.normSq_nonneg _)
  nlinarith only [hm]

private theorem weighted_dotProduct_re (x : Entry → ℂ) (a b : Entry → ℝ) :
    (star (fun i => (a i : ℂ) * x i) ⬝ᵥ (fun i => (b i : ℂ) * x i)).re =
      ∑ i, a i * b i * Complex.normSq (x i) := by
  rw [dotProduct, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (star ((a i : ℂ) * x i) * ((b i : ℂ) * x i)).re = _
  simp only [Complex.star_def, map_mul, Complex.conj_ofReal]
  rw [show (a i : ℂ) * conj (x i) * ((b i : ℂ) * x i) =
      ((a i : ℂ) * (b i : ℂ)) * (x i * conj (x i)) by ring,
    Complex.mul_conj, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- Kantorovich's squared norm bound in the actual entry space. The eigenvalues are
normalized by a positive lower endpoint of the relative operator. -/
private theorem relative_moment (P : Operator) (hP : P.IsHermitian) (u : Entry → ℂ)
    {a R C : ℝ} (ha : 0 < a) (hR : 1 ≤ R) (hfactor : (R + 1) ^ 2 ≤ 4 * R * C ^ 2)
    (hp : ∀ i, 1 ≤ hP.eigenvalues i / a ∧ hP.eigenvalues i / a ≤ R) :
    (star (P *ᵥ u) ⬝ᵥ (P *ᵥ u)).re * (star u ⬝ᵥ u).re ≤
      (C * (star (P *ᵥ u) ⬝ᵥ u).re) ^ 2 := by
  let p := fun i => hP.eigenvalues i / a
  have he (i : Entry) : hP.eigenvalues i = a * p i := by
    dsimp [p]
    field_simp [ha.ne']
  let V : Operator := hP.eigenvectorUnitary
  let w := Vᴴ *ᵥ u
  have hVrows : V * Vᴴ = 1 := Unitary.coe_mul_star_self hP.eigenvectorUnitary
  have hdot (x y : Entry → ℂ) :
      star (Vᴴ *ᵥ x) ⬝ᵥ (Vᴴ *ᵥ y) = star x ⬝ᵥ y := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, hVrows, Matrix.one_mulVec]
  have hD : Vᴴ * P * V = diagonal (fun i => (hP.eigenvalues i : ℂ)) := by
    dsimp [V]
    simpa only [Unitary.conjStarAlgAut_star_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      hP.conjStarAlgAut_star_eigenvectorUnitary
  have hDP : Vᴴ * P = diagonal (fun i => (hP.eigenvalues i : ℂ)) * Vᴴ := by
    simpa only [Matrix.mul_assoc, hVrows, Matrix.mul_one] using congrArg (· * Vᴴ) hD
  have hPu : Vᴴ *ᵥ (P *ᵥ u) = fun i => (hP.eigenvalues i : ℂ) * w i := by
    rw [Matrix.mulVec_mulVec, hDP, ← Matrix.mulVec_mulVec]
    funext i
    exact Matrix.mulVec_diagonal _ _ i
  have hu : (star u ⬝ᵥ u).re = ∑ i, Complex.normSq (w i) := by
    rw [← hdot u u]
    simpa only [Complex.ofReal_one, one_mul] using weighted_dotProduct_re w (fun _ => 1) (fun _ => 1)
  have hPnorm : (star (P *ᵥ u) ⬝ᵥ (P *ᵥ u)).re =
      a ^ 2 * ∑ i, p i ^ 2 * Complex.normSq (w i) := by
    rw [← hdot (P *ᵥ u) (P *ᵥ u), hPu, weighted_dotProduct_re, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [he i]
    ring
  have hQ : (star (P *ᵥ u) ⬝ᵥ u).re =
      a * ∑ i, p i * Complex.normSq (w i) := by
    rw [← hdot (P *ᵥ u) u, hPu]
    change (star (fun i => (hP.eigenvalues i : ℂ) * w i) ⬝ᵥ w).re = _
    have heq := weighted_dotProduct_re w hP.eigenvalues (fun _ => 1)
    simp only [Complex.ofReal_one, one_mul, mul_one] at heq
    rw [heq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [he i]
    ring
  have hm := finite_kantorovich_sq hR hfactor p (fun i => Complex.normSq (w i)) hp
    (fun i => Complex.normSq_nonneg _)
  rw [hPnorm, hu, hQ]
  nlinarith only [mul_le_mul_of_nonneg_left hm (sq_nonneg a)]

private theorem physical_dual_moment {r a R C : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5)
    (M H : Mat) (hM : M.IsHermitian) (hW : (sandwich r H).IsHermitian)
    (ha : 0 < a) (hlo : (a : ℂ) • (1 : Mat) ≤ M) (hMhi : M ≤ 1)
    (hR : 1 ≤ R) (hRatio : (36 / 25 : ℝ) / a ≤ R)
    (hfactor : (R + 1) ^ 2 ≤ 4 * R * C ^ 2) :
    (vPairing r (mixedDual r M H) (mixedDual r M H)).re * (vPairing r H H).re ≤
      (C * (M * (sandwich r H) ^ 2).trace.re) ^ 2 := by
  classical
  obtain ⟨hP, heLo, heRatio⟩ := physicalRelative_normalized hr hhi M a ha hlo hMhi
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ hP.eigenvalues Finset.univ_nonempty
  have hjpos : 0 < hP.eigenvalues j := by
    have hr0 : 0 < r := zero_lt_one.trans_le hr
    have hb := (physicalWeight_bounds hr).1
    exact (div_pos ha (by positivity)).trans_le (heLo j)
  have hp (i : Entry) :
      1 ≤ hP.eigenvalues i / hP.eigenvalues j ∧
        hP.eigenvalues i / hP.eigenvalues j ≤ R := by
    refine ⟨(le_div_iff₀ hjpos).mpr ?_, (heRatio i j).trans hRatio⟩
    simpa only [one_mul] using hj i (Finset.mem_univ i)
  let u := weightedVec (baseEntry r) (sandwich r H)
  have hm := relative_moment (physicalRelative r M) hP u hjpos hR hfactor hp
  have hdual : physicalRelative r M *ᵥ u =
      weightedVec (baseEntry r) (sandwich r (mixedDual r M H)) :=
    physicalRelative_mixedDual_mulVec hr M H hM hW
  rw [show (star (physicalRelative r M *ᵥ u) ⬝ᵥ u).re =
      (M * (sandwich r H) ^ 2).trace.re from
    congrArg Complex.re (physicalRelative_quadratic hr M H hM hW),
    hdual, weightedVec_sandwich_pairing hr, show u = weightedVec (baseEntry r) (sandwich r H)
      by rfl, weightedVec_sandwich_pairing hr] at hm
  exact hm

private theorem sandwich_inverse {r : ℝ} (hr : 1 ≤ r) (W : Mat) :
    sandwich r (GInv r * W * GInv r) = W := by
  calc
    sandwich r (GInv r * W * GInv r) = (G r * GInv r) * W * (GInv r * G r) := by
      dsimp only [sandwich]
      noncomm_ring
    _ = W := by rw [G_mul_GInv hr, GInv_mul_G hr, one_mul, mul_one]

/-- The mixed-generator term used by `physical_curvature_ge`, for the actual
two-CAR generator and a Hermitian embedded direction of degrees at least two. -/
theorem wu_relative_mixed_generator {r : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5)
    (M W : Mat) (hM : M.PosDef) (hW : W.IsHermitian)
    (hlo : ((5 / 9 : ℝ) : ℂ) • (1 : Mat) ≤ M) (hMhi : M ≤ 1)
    (hdegree : ∀ k : Index, degree k < 2 → coefficient r (GInv r * W * GInv r) k = 0) :
    (15 / 4 : ℝ) * (M * W ^ 2).trace.re ≤
      ((M * W + W * M) * (G r * generator r (GInv r * W * GInv r) * G r)).trace.re := by
  let H := GInv r * W * GInv r
  have hWs : sandwich r H = W := sandwich_inverse hr W
  have hWH : (sandwich r H).IsHermitian := hWs.symm ▸ hW
  have hm := physical_dual_moment (a := 5 / 9) (R := 324 / 125) (C := 9 / 8)
    hr hhi M H hM.isHermitian hWH (by norm_num) hlo hMhi
    (by norm_num) (by norm_num) (by norm_num)
  simpa only [hWs, embeddedGenerator] using
    mixed_energy_ge_of_dual_moment hr M H hM.posSemidef hWH hdegree hm

/-- The physical mixed-generator estimate on the normalized spectral band `[21/40, 1]`. -/
theorem wu_relative_mixed_generator_wider {r : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5)
    (M W : Mat) (hM : M.PosDef) (hW : W.IsHermitian)
    (hlo : ((21 / 40 : ℝ) : ℂ) • (1 : Mat) ≤ M) (hMhi : M ≤ 1)
    (hdegree : ∀ k : Index, degree k < 2 → coefficient r (GInv r * W * GInv r) k = 0) :
    (187 / 50 : ℝ) * (M * W ^ 2).trace.re ≤
      ((M * W + W * M) * (G r * generator r (GInv r * W * GInv r) * G r)).trace.re := by
  let H := GInv r * W * GInv r
  have hWs : sandwich r H = W := sandwich_inverse hr W
  have hWH : (sandwich r H).IsHermitian := hWs.symm ▸ hW
  have hm := physical_dual_moment (a := 21 / 40) (R := 96 / 35) (C := 113 / 100)
    hr hhi M H hM.isHermitian hWH (by norm_num) hlo hMhi
    (by norm_num) (by norm_num) (by norm_num)
  simpa only [hWs, embeddedGenerator, show (6 - 2 * (113 / 100) : ℝ) = 187 / 50 by norm_num]
    using mixed_energy_ge_of_dual_moment_bound hr (by norm_num : 0 ≤ (113 / 100 : ℝ))
      M H hM.posSemidef hWH hdegree hm

#print axioms kantorovich_324
#print axioms wu_relative_mixed_generator
#print axioms wu_relative_mixed_generator_wider

end D5.S3.Quantum.Semigroups.WuCubicHessianKantorovich
