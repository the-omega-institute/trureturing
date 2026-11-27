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
open WuCubicTranslationEnergy (baseEntry sandwich)
open WuCubicConditionedHessian (embeddedGenerator mixedDual mixed_energy_ge_of_dual_moment)
open WuCubicRelativeAnticommutator (Entry Operator physicalRelative physicalWeight_bounds
  physicalRelative_normalized weightedVec weightedVec_sandwich_pairing
  physicalRelative_mixedDual_mulVec physicalRelative_quadratic)
open private G_mul_GInv GInv_mul_G from D5.S3.Quantum.Semigroups.WuCubicOperatorBridge

private theorem finite_kantorovich_sq {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (hp : ∀ i, 1 ≤ p i ∧ p i ≤ 324 / 125)
    (hz : ∀ i, 0 ≤ z i) :
    64 * (∑ i, (p i) ^ 2 * z i) * (∑ i, z i) ≤
      81 * (∑ i, p i * z i) ^ 2 := by
  let A : ℝ := ∑ i, z i
  let B : ℝ := ∑ i, p i * z i
  let C : ℝ := ∑ i, (p i) ^ 2 * z i
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg (fun i _ => hz i)
  have hpoint (i : ι) : (p i) ^ 2 ≤ (449 / 125 : ℝ) * p i - 324 / 125 := by
    have h := mul_nonneg (sub_nonneg.mpr (hp i).1)
      (sub_nonneg.mpr (hp i).2)
    nlinarith only [h]
  have hC : C ≤ (449 / 125 : ℝ) * B - (324 / 125 : ℝ) * A := by
    dsimp only [C, B, A]
    calc
      _ ≤ ∑ i, ((449 / 125 : ℝ) * p i - 324 / 125) * z i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hpoint i) (hz i)
      _ = _ := by
        calc
          _ = ∑ i, ((449 / 125 : ℝ) * (p i * z i) - (324 / 125 : ℝ) * z i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = _ := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hCA : 4 * (324 / 125 : ℝ) * C * A ≤
      (449 / 125 : ℝ) ^ 2 * B ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hC hA
    have hs : 0 ≤ ((449 / 125 : ℝ) * B - 2 * (324 / 125 : ℝ) * A) ^ 2 :=
      sq_nonneg _
    nlinarith only [hmul, hs]
  have hfactor : 16 * (449 / 125 : ℝ) ^ 2 ≤ 81 * (324 / 125 : ℝ) := by
    norm_num
  have hfac := mul_le_mul_of_nonneg_right hfactor (sq_nonneg B)
  have hmul : 64 * (324 / 125 : ℝ) * C * A ≤
      81 * (324 / 125 : ℝ) * B ^ 2 := by
    calc
      64 * (324 / 125 : ℝ) * C * A ≤
          16 * (449 / 125 : ℝ) ^ 2 * B ^ 2 := by nlinarith only [hCA]
      _ ≤ _ := hfac
  have hab : 0 < (324 / 125 : ℝ) := by norm_num
  have hfinal : 64 * C * A ≤ 81 * B ^ 2 := by
    apply le_of_mul_le_mul_left _ hab
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul
  simpa only [A, B, C] using hfinal

theorem kantorovich_324 {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (u : ι → ℂ) (hp : ∀ i, 1 ≤ p i ∧ p i ≤ 324 / 125) :
    64 * (∑ i, (p i) ^ 2 * Complex.normSq (u i)) *
        (∑ i, Complex.normSq (u i)) ≤
      81 * (∑ i, p i * Complex.normSq (u i)) ^ 2 := by
  apply finite_kantorovich_sq p (fun i => Complex.normSq (u i)) hp
  exact fun i => Complex.normSq_nonneg _

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
    {a : ℝ} (ha : 0 < a)
    (hp : ∀ i, 1 ≤ hP.eigenvalues i / a ∧ hP.eigenvalues i / a ≤ 324 / 125) :
    (star (P *ᵥ u) ⬝ᵥ (P *ᵥ u)).re * (star u ⬝ᵥ u).re ≤
      ((9 / 8 : ℝ) * (star (P *ᵥ u) ⬝ᵥ u).re) ^ 2 := by
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
  have hm := mul_le_mul_of_nonneg_left (kantorovich_324 p w hp) (sq_nonneg a)
  rw [hPnorm, hu, hQ]
  nlinarith only [hm]

/-- The mixed-generator term used by `physical_curvature_ge`, for the actual
two-CAR generator and a Hermitian embedded direction of degrees at least two. -/
theorem wu_relative_mixed_generator {r : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5)
    (M W : Mat) (hM : M.PosDef) (hW : W.IsHermitian)
    (hlo : ((5 / 9 : ℝ) : ℂ) • (1 : Mat) ≤ M) (hMhi : M ≤ 1)
    (hdegree : ∀ k : Index, degree k < 2 → coefficient r (GInv r * W * GInv r) k = 0) :
    (15 / 4 : ℝ) * (M * W ^ 2).trace.re ≤
      ((M * W + W * M) * (G r * generator r (GInv r * W * GInv r) * G r)).trace.re := by
  classical
  let H := GInv r * W * GInv r
  have hWs : sandwich r H = W := by
    calc
      sandwich r H = (G r * GInv r) * W * (GInv r * G r) := by
        dsimp only [H, sandwich]
        noncomm_ring
      _ = W := by rw [G_mul_GInv hr, GInv_mul_G hr, one_mul, mul_one]
  have hWH : (sandwich r H).IsHermitian := hWs.symm ▸ hW
  obtain ⟨hP, heLo, heRatio⟩ := physicalRelative_normalized hr hhi M (5 / 9)
    (by norm_num) hlo hMhi
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ hP.eigenvalues Finset.univ_nonempty
  have ha : 0 < hP.eigenvalues j := by
    have hr0 : 0 < r := zero_lt_one.trans_le hr
    have hb := (physicalWeight_bounds hr).1
    exact (div_pos (by norm_num) (by positivity)).trans_le (heLo j)
  have hp (i : Entry) :
      1 ≤ hP.eigenvalues i / hP.eigenvalues j ∧
        hP.eigenvalues i / hP.eigenvalues j ≤ 324 / 125 := by
    refine ⟨(le_div_iff₀ ha).mpr (by simpa using hj i (Finset.mem_univ i)), ?_⟩
    exact (heRatio i j).trans (by norm_num)
  let u := weightedVec (baseEntry r) (sandwich r H)
  have hm := relative_moment (physicalRelative r M) hP u ha hp
  have hdual : physicalRelative r M *ᵥ u =
      weightedVec (baseEntry r) (sandwich r (mixedDual r M H)) :=
    physicalRelative_mixedDual_mulVec hr M H hM.isHermitian hWH
  rw [show (star (physicalRelative r M *ᵥ u) ⬝ᵥ u).re =
      (M * (sandwich r H) ^ 2).trace.re from
    congrArg Complex.re (physicalRelative_quadratic hr M H hM.isHermitian hWH),
    hdual, weightedVec_sandwich_pairing hr, show u = weightedVec (baseEntry r) (sandwich r H)
      by rfl, weightedVec_sandwich_pairing hr] at hm
  simpa only [hWs, embeddedGenerator] using
    mixed_energy_ge_of_dual_moment hr M H hM.posSemidef hWH hdegree hm

#print axioms kantorovich_324
#print axioms wu_relative_mixed_generator

end D5.S3.Quantum.Semigroups.WuCubicHessianKantorovich
