/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortMarginalBoxError
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform quadrature error for the first three scaled marginal inputs. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortJointLower

/-! Symmetric mesh error for the scaled marginal in the compact short-gap score. -/

noncomputable section

namespace RefinedBMV.PositiveCenter

open CompactTaylorModel (InBox Model)
open D5.S3.Weil.ZetaPntBase.EulerMaclaurinSixth (abs_meshRemainder_le meshRemainder)

/-- Symmetric radius for the mesh error in the scaled marginal and its first two derivatives. -/
def shortMarginalMeshError (upper radius : ℚ) (expOrder : ℕ) (j : Fin 3) : ℚ :=
  let P0 := radius ^ 4 * (3 + upper) + 6 * radius ^ 3
  let P1 := 4 * radius ^ 3 * (3 + upper) + 18 * radius ^ 2
  let P2 := 12 * radius ^ 2 * (3 + upper) + 36 * radius
  upper ^ 6 / 15360 * 3 * (11 / 4) ^ expOrder *
    ![P0, P1 + 2 * P0, P2 + 4 * P1 + 4 * P0] j

private def marginalMeshDensity (j : Fin 3) (h t : ℝ) : ℝ → ℝ :=
  ![(fun x ↦ t ^ 3 * Real.exp (t * x) * (t * (2 + h - x) - 6)),
    compactMarginalRemainderFirst h t, compactMarginalRemainderSecond h t] j

private theorem exp_mul_le_shortMarginal {t x : ℝ} {N : ℕ}
    (hneg : -(N : ℝ) ≤ t) (hpos : 2 * t ≤ (N : ℝ)) (hx : x ∈ Set.Icc (-1 : ℝ) 2) :
    Real.exp (t * x) ≤ (11 / 4 : ℝ) ^ N := by
  have htx : t * x ≤ (N : ℝ) := by
    rcases le_total 0 t with ht | ht
    · exact (mul_le_mul_of_nonneg_left hx.2 ht).trans (by linarith)
    · exact (mul_le_mul_of_nonpos_left hx.1 ht).trans (by linarith)
  calc
    _ ≤ Real.exp (N : ℝ) := Real.exp_le_exp.mpr htx
    _ = Real.exp 1 ^ N := by rw [← Real.exp_nat_mul, mul_one]
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg 1) (by linarith [Real.exp_one_lt_d9]) N

private theorem marginalMeshDensity_abs_le (j : Fin 3) {h H R t x : ℝ} {N : ℕ}
    (hh : 0 ≤ h) (hH : h ≤ H) (ht : |t| ≤ R) (hneg : -(N : ℝ) ≤ t)
    (hpos : 2 * t ≤ (N : ℝ)) (hx : x ∈ Set.Icc (-1 : ℝ) 2) :
    let P0 := R ^ 4 * (3 + H) + 6 * R ^ 3
    let P1 := 4 * R ^ 3 * (3 + H) + 18 * R ^ 2
    let P2 := 12 * R ^ 2 * (3 + H) + 36 * R
    |marginalMeshDensity j h t x| ≤ (11 / 4 : ℝ) ^ N *
      ![P0, P1 + 2 * P0, P2 + 4 * P1 + 4 * P0] j := by
  let P0 := R ^ 4 * (3 + H) + 6 * R ^ 3
  let P1 := 4 * R ^ 3 * (3 + H) + 18 * R ^ 2
  let P2 := 12 * R ^ 2 * (3 + H) + 36 * R
  let w := 2 + h - x
  let A0 := t ^ 4 * w - 6 * t ^ 3
  let A1 := 4 * t ^ 3 * w - 18 * t ^ 2
  let A2 := 12 * t ^ 2 * w - 36 * t
  have hw : 0 ≤ w := by dsimp [w]; linarith [hx.2]
  have hwH : w ≤ 3 + H := by dsimp [w]; linarith [hx.1]
  have hR : 0 ≤ R := (abs_nonneg t).trans ht
  have hc (c : ℝ) (hc : 0 ≤ c) (k : ℕ) : |c * t ^ k| ≤ c * R ^ k := by
    rw [abs_mul, abs_of_nonneg hc, abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg t) ht k) hc
  have hcw (c : ℝ) (h : 0 ≤ c) (k : ℕ) : |c * t ^ k * w| ≤ c * R ^ k * (3 + H) := by
    rw [abs_mul, abs_of_nonneg hw]
    exact mul_le_mul (hc c h k) hwH hw (by positivity)
  have ha0 : |A0| ≤ P0 := by
    dsimp only [A0, P0]
    exact (abs_sub _ _).trans
      (add_le_add (by simpa only [one_mul] using hcw 1 one_pos.le 4) (hc 6 (by norm_num) 3))
  have ha1 : |A1| ≤ P1 :=
    (abs_sub _ _).trans (add_le_add (hcw 4 (by norm_num) 3) (hc 18 (by norm_num) 2))
  have ha2 : |A2| ≤ P2 :=
    (abs_sub _ _).trans (add_le_add (hcw 12 (by norm_num) 2)
      (by simpa only [pow_one] using hc 36 (by norm_num) 1))
  have hxabs : |x| ≤ 2 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  have h2x : |2 * x| ≤ 4 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have hxsq : |x ^ 2| ≤ 4 := by
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg x) hxabs 2).trans_eq (by norm_num)
  have scale {a b : ℝ} (hab : |a| ≤ b) :
      |Real.exp (t * x) * a| ≤ (11 / 4 : ℝ) ^ N * b := by
    rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_mul (exp_mul_le_shortMarginal hneg hpos hx) hab (abs_nonneg _) (by positivity)
  fin_cases j
  · change |t ^ 3 * Real.exp (t * x) * (t * (2 + h - x) - 6)| ≤ _
    rw [show t ^ 3 * Real.exp (t * x) * (t * (2 + h - x) - 6) =
      Real.exp (t * x) * A0 by dsimp [A0, w]; ring]
    exact scale ha0
  · change |Real.exp (t * x) * (A1 + x * A0)| ≤ _
    apply scale
    exact (abs_add_le _ _).trans (add_le_add ha1 (by
      rw [abs_mul]
      exact mul_le_mul hxabs ha0 (abs_nonneg _) (by norm_num)))
  · change |Real.exp (t * x) * (A2 + 2 * x * A1 + x ^ 2 * A0)| ≤ _
    apply scale
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ha2 ?_)) ?_)
    · rw [abs_mul]
      exact mul_le_mul h2x ha1 (abs_nonneg _) (by norm_num)
    · rw [abs_mul]
      exact mul_le_mul hxsq ha0 (abs_nonneg _) (by norm_num)

private theorem abs_marginalMeshRemainder_le {p : ℕ} (hp : 0 < p) {H C : ℝ}
    (hH : 3 / (p : ℝ) ≤ H) {f : ℝ → ℝ} (hf : Continuous f)
    (hC : ∀ x ∈ Set.Icc (-1 : ℝ) 2, |f x| ≤ C) :
    |meshRemainder (-1) (3 / (p : ℝ)) p f| ≤ H ^ 6 / 15360 * (3 * C) := by
  let h : ℝ := 3 / (p : ℝ)
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hspan : (-1 : ℝ) + (p : ℝ) * h = 2 := by
    dsimp [h]
    rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hp.ne')]
    norm_num
  have hmesh := abs_meshRemainder_le (a := -1) (n := p) hh hf
  rw [hspan] at hmesh
  refine hmesh.trans (mul_le_mul ?_ ?_ ?_ (by positivity))
  · exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hh hH 6) (by norm_num)
  · have hi := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (g := fun _ ↦ C) (by norm_num : (-1 : ℝ) ≤ 2)
      (hf.abs.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _) hC
    norm_num [intervalIntegral.integral_const, smul_eq_mul] at hi
    exact hi
  · exact intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ abs_nonneg _)

/-- The direct symmetric error between the scaled marginal derivative and its closed quadrature. -/
theorem compactScaledMarginal_meshError_le {p : ℕ} (hp : 0 < p) {t : ℝ}
    {upper radius : ℚ} {N : ℕ} (hupper : 3 / (p : ℝ) ≤ (upper : ℝ))
    (hradius : |t| ≤ (radius : ℝ)) (hneg : -(N : ℝ) ≤ t) (hpos : 2 * t ≤ (N : ℝ))
    (j : Fin 3) :
    let h : ℝ := 3 / (p : ℝ)
    let J := (3 + h) * (3 + 2 * h) / 2
    let q (y : ℝ) := (J * compactKappa p) * compactZ p y
    let Q := compactClosedQuadrature h
      (fun x ↦ iteratedDeriv (j : ℕ) (fun y ↦ regularizedMarginalIntegrand h y x) t)
    |iteratedDeriv (j : ℕ) q t - Q| ≤ (shortMarginalMeshError upper radius N j : ℝ) := by
  let h : ℝ := 3 / (p : ℝ)
  let J := (3 + h) * (3 + 2 * h) / 2
  let q (y : ℝ) := (J * compactKappa p) * compactZ p y
  let Q (k : ℕ) := compactClosedQuadrature h
    (fun x ↦ iteratedDeriv k (fun y ↦ regularizedMarginalIntegrand h y x) t)
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hf : Continuous (marginalMeshDensity j h t) := by
    fin_cases j
    · change Continuous (fun x ↦ t ^ 3 * Real.exp (t * x) * (t * (2 + h - x) - 6))
      fun_prop
    · change Continuous (compactMarginalRemainderFirst h t)
      unfold compactMarginalRemainderFirst
      fun_prop
    · change Continuous (compactMarginalRemainderSecond h t)
      unfold compactMarginalRemainderSecond
      fun_prop
  have hsplit : iteratedDeriv (j : ℕ) q t = Q j + meshRemainder (-1) h p
      (marginalMeshDensity j h t) := by
    obtain ⟨h0, h1, h2⟩ := compactScaledMarginal_eq_closed_add_remainder hp t
    fin_cases j
    · rw [iteratedDeriv_zero]
      exact h0
    · rw [iteratedDeriv_one]
      exact h1
    · exact h2
  change |iteratedDeriv (j : ℕ) q t - Q j| ≤ _
  rw [hsplit, add_sub_cancel_left]
  refine (abs_marginalMeshRemainder_le hp hupper hf
    (fun x hx ↦ marginalMeshDensity_abs_le j hh hupper hradius hneg hpos hx)).trans_eq ?_
  fin_cases j <;>
    simp [shortMarginalMeshError, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow] <;> ring

/-- Widen the actual closed-quadrature model to enclose the corresponding scaled marginal
derivative. The mesh radius uses the same upper spacing and parameter radius as the model. -/
theorem marginalClosedQuadratureModel_widen_meshError_sound
    {s t z offset : ℝ} {upper center radius width : ℚ} {terms order N p : ℕ} (j : Fin 3)
    {H X : Model} (hb : InBox s t z) (hp : 0 < p)
    (hH : H.Encloses s t z (3 / (p : ℝ))) (hX : X.Encloses s t z offset)
    (hupper : 3 / (p : ℝ) ≤ (upper : ℝ)) (horder : order ≤ terms) (hterms : 3 ≤ terms)
    (hr : |(center : ℝ)| + |offset| ≤ (radius : ℝ)) (hw : |offset| ≤ (width : ℝ))
    (hratio : 2 * (radius : ℝ) < (terms : ℝ) - 2)
    (hneg : -(N : ℝ) ≤ (center : ℝ) + offset) (hpos : 2 * ((center : ℝ) + offset) ≤ (N : ℝ)) :
    let h : ℝ := 3 / (p : ℝ)
    let J := (3 + h) * (3 + 2 * h) / 2
    let q (y : ℝ) := (J * compactKappa p) * compactZ p y
    ((marginalClosedQuadratureModel upper radius width center j terms order H X).widen
      (shortMarginalMeshError upper radius N j)).Encloses s t z
      (iteratedDeriv (j : ℕ) q ((center : ℝ) + offset)) := by
  have hh : 0 ≤ 3 / (p : ℝ) := by positivity
  exact Model.widen_sound
    (marginalClosedQuadratureModel_sound hb hH hX hh hupper horder hterms hr hw hratio)
    (compactScaledMarginal_meshError_le hp hupper ((abs_add_le _ _).trans hr) hneg hpos j)

end RefinedBMV.PositiveCenter
