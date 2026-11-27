import D5.S3.Quantum.Semigroups.WuCubicBoundaryThermal
import D5.S3.Quantum.Semigroups.WuCubicBoundaryEntropy
import OmegaBuild.Commands

/-! Pure level curvature for fixed-frame interpolation of the Wu cubic deficit. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrumLevelInterpolation

open _root_.Matrix Set
open scoped BigOperators Matrix Topology

open WuCubicDirectedOccupationCap (Mat)
open WuRepeatedMiddleCubic (alpha weight imbalance)
open WuCubicAngularCertificate (physicalFrame normalizedDeficit thermalCenter)
open WuCubicBoundaryThermal (jumpContribution normalizedDeficit_eq_jumpContribution)
open WuCubicOccupationTaylor (alpha_bounds_of_one_le)
open WuCubicCornerInterpolation (corner_interpolation corner_floor)
open private h c e bias row_weight col_weight from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private levelsAt totalAt cubic from D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
open private physicalFrame_columns physicalFrame_rows from
  D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
open private massEntropy massEntropy_hasDerivAt massEntropy_profile_hasDerivAt from
  D5.S3.Quantum.Semigroups.WuCubicBoundaryEntropy
open private coefficient_bounds weight_nonneg imbalance_le_one edge edgeFirst edgeSecond
  edge_hasDerivAt edgeFirst_hasDerivAt edge_second_le from
  D5.S3.Quantum.Semigroups.WuCubicBoundaryEntropy

/-- The slice of the normalized deficit along one of the three free levels. -/
def levelSlice (r : ℝ) (U : unitary Mat) (x : Fin 3 → ℝ) (k : Fin 3) : ℝ → ℝ :=
  fun t => normalizedDeficit r U (Function.update x k t 0)
    (Function.update x k t 1) (Function.update x k t 2)

private def levels (x : Fin 3 → ℝ) : Fin 4 → ℝ := Fin.lastCases 1 x

private theorem levels_eq (x : Fin 3 → ℝ) :
    levels x = levelsAt (x 0) (x 1) (x 2) := by
  funext i
  fin_cases i <;> rfl

private theorem levels_update (x : Fin 3 → ℝ) (k : Fin 3) (t : ℝ) :
    levels (Function.update x k t) = Function.update (levels x) k.castSucc t := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [levels, Fin.lastCases_last, Function.update_of_ne (Fin.castSucc_ne_last k).symm]
  ·
    by_cases hj : j = k
    · subst j
      simp [levels]
    · have hj' : j.castSucc ≠ k.castSucc := fun he => hj (Fin.castSucc_injective _ he)
      simp [levels, Function.update_of_ne hj, Function.update_of_ne hj']

private def otherLevels (k : Fin 3) : Finset (Fin 4) := Finset.univ.erase k.castSucc

private def fixedMass (x : Fin 3 → ℝ) (k : Fin 3) : ℝ :=
  ∑ j ∈ otherLevels k, levels x j ^ 3

private theorem sum_levels_update (g : Fin 4 → ℝ → ℝ) (x : Fin 3 → ℝ) (k : Fin 3)
    (t : ℝ) :
    ∑ i, g i (levels (Function.update x k t) i) =
      (∑ j ∈ otherLevels k, g j (levels x j)) + g k.castSucc t := by
  rw [levels_update, ← Finset.sum_erase_add _ _ (Finset.mem_univ k.castSucc)]
  rw [Function.update_self]
  congr 1
  exact Finset.sum_congr rfl fun j hj => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

private theorem total_update (x : Fin 3 → ℝ) (k : Fin 3) (t : ℝ) :
    let y := Function.update x k t
    totalAt (y 0) (y 1) (y 2) = fixedMass x k + t ^ 3 := by
  intro y
  have hs := sum_levels_update (fun _ z => z ^ 3) x k t
  change (∑ i, levels y i ^ 3) = _ at hs
  rw [levels_eq, Fin.sum_univ_four] at hs
  simpa [levelsAt, totalAt, fixedMass] using hs

private theorem mem_Icc_levels {x : Fin 3 → ℝ}
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) (j : Fin 4) :
    levels x j ∈ Icc (0 : ℝ) 1 := by
  induction j using Fin.lastCases with
  | last => exact ⟨zero_le_one, le_rfl⟩
  | cast i => simpa [levels] using hx i

private theorem fixedMass_nonneg {x : Fin 3 → ℝ} (k : Fin 3)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) : 0 ≤ fixedMass x k :=
  Finset.sum_nonneg fun j _ => pow_nonneg (mem_Icc_levels hx j).1 3

private theorem jump_update (r : ℝ) (U : unitary Mat) (x : Fin 3 → ℝ) (k : Fin 3) (t : ℝ) :
    let y := Function.update x k t
    let V := physicalFrame U
    jumpContribution U (y 0) (y 1) (y 2) r =
      (∑ j ∈ otherLevels k, edge r V k.castSucc j (levels x j) t) +
      ∑ i ∈ otherLevels k, ∑ j ∈ otherLevels k,
        weight V i j * cubic (c r) (e r) (levels x i) (levels x j) := by
  intro y V
  let κ := k.castSucc
  let S := otherLevels k
  let K (i j : Fin 4) (a b : ℝ) := weight V i j * cubic (c r) (e r) a b
  change (∑ i, ∑ j, K i j (levelsAt (y 0) (y 1) (y 2) i) (levelsAt (y 0) (y 1) (y 2) j)) = _
  simp_rw [← levels_eq]
  rw [show levels y = Function.update (levels x) κ t from levels_update x k t]
  let z := Function.update (levels x) κ t
  change (∑ i, ∑ j, K i j (z i) (z j)) = _
  have hsplit (i : Fin 4) :
      (∑ j, K i j (z i) (z j)) = (∑ j ∈ S, K i j (z i) (levels x j)) + K i κ (z i) t := by
    simpa only [levels_update] using sum_levels_update (fun j b => K i j (z i) b) x k t
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ κ)]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, show z κ = t by simp [z]]
  have hfixed (i : Fin 4) (hi : i ∈ S) : z i = levels x i :=
    Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _
  have hrest : (∑ i ∈ S, ∑ j ∈ S, K i j (z i) (levels x j)) =
      ∑ i ∈ S, ∑ j ∈ S, K i j (levels x i) (levels x j) :=
    Finset.sum_congr rfl fun i hi => by rw [hfixed i hi]
  have hcol : (∑ i ∈ S, K i κ (z i) t) = ∑ i ∈ S, K i κ (levels x i) t :=
    Finset.sum_congr rfl fun i hi => by rw [hfixed i hi]
  have hdiag : K κ κ t t = 0 := by simp [K, cubic]
  change (∑ i ∈ S, ∑ j ∈ S, K i j (z i) (levels x j)) +
      (∑ i ∈ S, K i κ (z i) t) + ((∑ j ∈ S, K κ j t (levels x j)) + K κ κ t t) = _
  rw [hrest, hcol, hdiag, add_zero]
  simp only [edge, Finset.sum_add_distrib, ← show S = otherLevels k from rfl, K]
  ring

private def scalarCoeff (r : ℝ) (U : unitary Mat) (k : Fin 3) : ℝ :=
  h r + bias r * imbalance (physicalFrame U) k.castSucc

private def varyingPart (r : ℝ) (U : unitary Mat) (x : Fin 3 → ℝ) (k : Fin 3) (t : ℝ) : ℝ :=
  scalarCoeff r U k * t ^ 3 +
    (∑ j ∈ otherLevels k, edge r (physicalFrame U) k.castSucc j (levels x j) t) +
    alpha r * massEntropy (fixedMass x k) t

private theorem levelSlice_eq {r : ℝ} (hr : 1 ≤ r) (U : unitary Mat)
    {x : Fin 3 → ℝ} (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) (k : Fin 3) {t : ℝ} (ht : 0 ≤ t) :
    levelSlice r U x k t =
      varyingPart r U x k t + (levelSlice r U x k 0 - varyingPart r U x k 0) := by
  let V := physicalFrame U
  let S := otherLevels k
  let A := fixedMass x k
  let K := h r * A -
    alpha r * (∑ j ∈ S, levels x j ^ 3 * Real.log (levels x j ^ 3)) +
    (∑ i ∈ S, ∑ j ∈ S, weight V i j * cubic (c r) (e r) (levels x i) (levels x j)) +
    bias r * ∑ j ∈ S, imbalance V j * levels x j ^ 3
  have hmodel (u : ℝ) (hu : 0 ≤ u) : levelSlice r U x k u = varyingPart r U x k u + K := by
    let y := Function.update x k u
    have hy (i : Fin 3) : 0 ≤ y i := by
      by_cases hi : i = k
      · subst i
        simpa [y] using hu
      · simpa [y, Function.update_of_ne hi] using (hx i).1
    have hmass := total_update x k u
    change totalAt (y 0) (y 1) (y 2) = A + u ^ 3 at hmass
    have hentropy := sum_levels_update (fun _ z => z ^ 3 * Real.log (z ^ 3)) x k u
    have hcharge := sum_levels_update (fun j z => imbalance V j * z ^ 3) x k u
    change (∑ i, levels y i ^ 3 * Real.log (levels y i ^ 3)) = _ at hentropy
    change (∑ i, imbalance V i * levels y i ^ 3) = _ at hcharge
    rw [levels_eq, Fin.sum_univ_four] at hentropy hcharge
    simp [levelsAt] at hentropy hcharge
    change normalizedDeficit r U (y 0) (y 1) (y 2) = _
    rw [normalizedDeficit_eq_jumpContribution U hr (hy 0) (hy 1) (hy 2),
      thermalCenter, hmass, jump_update r U x k u]
    dsimp only [varyingPart, scalarCoeff, massEntropy, K, A, V, S] at *
    simp only [Real.log_pow]
    linear_combination -alpha r * hentropy + bias r * hcharge
  rw [hmodel t ht, hmodel 0 le_rfl]
  ring

private def firstProfile (r : ℝ) (U : unitary Mat) (x : Fin 3 → ℝ) (k : Fin 3) (t : ℝ) : ℝ :=
  scalarCoeff r U k * (3 * t ^ 2) +
    (∑ j ∈ otherLevels k, edgeFirst r (physicalFrame U) k.castSucc j (levels x j) t) +
    alpha r * (3 * t ^ 2 * Real.log ((fixedMass x k + t ^ 3) / (4 * t ^ 3)))

private def secondProfile (r : ℝ) (U : unitary Mat) (x : Fin 3 → ℝ) (k : Fin 3) (t : ℝ) : ℝ :=
  let z := (fixedMass x k + t ^ 3) / (4 * t ^ 3)
  6 * t * scalarCoeff r U k +
    (∑ j ∈ otherLevels k, edgeSecond r (physicalFrame U) k.castSucc j (levels x j) t) +
    alpha r * t * (6 * Real.log z + 9 / (4 * z) - 9)

private theorem levelSlice_hasDerivAt {r : ℝ} (hr : 1 ≤ r) (U : unitary Mat)
    {x : Fin 3 → ℝ} (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) (k : Fin 3) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (levelSlice r U x k) (firstProfile r U x k t) t := by
  have hjump := HasDerivAt.fun_sum (u := otherLevels k)
    (fun j _ => edge_hasDerivAt r (physicalFrame U) k.castSucc j (levels x j) t)
  have hvar := (((hasDerivAt_pow 3 t).const_mul (scalarCoeff r U k)).fun_add hjump).fun_add
    ((massEntropy_hasDerivAt (fixedMass_nonneg k hx) ht).const_mul (alpha r))
  have hmodel : HasDerivAt (varyingPart r U x k) (firstProfile r U x k t) t := by
    simpa [varyingPart, firstProfile] using hvar
  apply (hmodel.add_const (levelSlice r U x k 0 - varyingPart r U x k 0)).congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with u hu
  exact levelSlice_eq hr U hx k hu.le

/-- Exact pure level second derivative for any of the three free coordinates. -/
theorem levelSlice_second_hasDerivAt {r : ℝ} (hr : 1 ≤ r) (U : unitary Mat)
    {x : Fin 3 → ℝ} (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) (k : Fin 3) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (deriv (levelSlice r U x k)) (secondProfile r U x k t) t := by
  have hjump := HasDerivAt.fun_sum (u := otherLevels k)
    (fun j _ => edgeFirst_hasDerivAt r (physicalFrame U) k.castSucc j (levels x j) t)
  have hscalar := ((hasDerivAt_pow 2 t).const_mul (3 : ℝ)).const_mul (scalarCoeff r U k)
  have hent := (massEntropy_profile_hasDerivAt (fixedMass_nonneg k hx) ht).const_mul (alpha r)
  have hd := (hscalar.fun_add hjump).fun_add hent
  have hfirst : HasDerivAt (firstProfile r U x k) (secondProfile r U x k t) t := by
    convert hd using 1
    · rfl
    · simp only [secondProfile, Nat.cast_ofNat, Nat.reduceSub, pow_one]
      ring
  apply hfirst.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with u hu
  exact (levelSlice_hasDerivAt hr U hx k hu).deriv

private theorem massEntropy_continuous (A : ℝ) : Continuous (massEntropy A) := by
  have hp : Continuous (fun t : ℝ => t ^ 3) := continuous_id.pow 3
  have hm : Continuous (fun t : ℝ => (A + t ^ 3) / 4) := (continuous_const.add hp).div_const 4
  have hq := (Real.continuous_mul_log.comp hm).const_mul (4 : ℝ)
  convert hq.sub (Real.continuous_mul_log.comp hp) using 1
  funext t
  dsimp [massEntropy]
  ring

private theorem levelSlice_continuousOn {r : ℝ} (hr : 1 ≤ r) (U : unitary Mat)
    {x : Fin 3 → ℝ} (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) (k : Fin 3) :
    ContinuousOn (levelSlice r U x k) (Ici 0) := by
  have hjump : Continuous (fun t : ℝ => ∑ j ∈ otherLevels k,
      edge r (physicalFrame U) k.castSucc j (levels x j) t) := by
    exact continuous_finset_sum _ fun j _ => continuous_iff_continuousAt.mpr fun t =>
      (edge_hasDerivAt r (physicalFrame U) k.castSucc j (levels x j) t).continuousAt
  have hp : Continuous (varyingPart r U x k) :=
    ((continuous_const.mul (continuous_id.pow 3)).add hjump).add
      ((massEntropy_continuous (fixedMass x k)).const_mul (alpha r))
  apply (hp.add continuous_const).continuousOn.congr
  intro t ht
  exact levelSlice_eq hr U hx k ht

private theorem entropy_second_upper {r A t : ℝ} (hr : 1 ≤ r)
    (hA : 0 ≤ A) (ht : 0 < t) (hT : A + t ^ 3 ≤ 4) :
    let z := (A + t ^ 3) / (4 * t ^ 3)
    alpha r * t * (6 * Real.log z + 9 / (4 * z) - 9) ≤ 9 / 2 := by
  intro z
  have hTpos : 0 < A + t ^ 3 := by positivity
  have hz : 0 < z := by dsimp [z]; positivity
  have hzlo : 1 / 4 ≤ z := (le_div_iff₀ (by positivity)).2 (by linarith)
  have hzhi : z ≤ (t ^ 3)⁻¹ := by
    dsimp [z]
    rw [← div_div]
    exact (div_le_div_of_nonneg_right ((div_le_one (by norm_num)).2 hT) (by positivity)).trans_eq
      (one_div _)
  have hlog := Real.log_le_log hz hzhi
  rw [Real.log_inv, Real.log_pow] at hlog
  have hfrac : 9 / (4 * z) ≤ 9 := (div_le_iff₀ (by positivity)).2 (by linarith)
  have he : -t * Real.log t ≤ 1 / 2 := by
    have hs := Real.one_sub_inv_le_log_of_pos (mul_pos (Real.exp_pos 1) ht)
    rw [Real.log_mul (Real.exp_ne_zero 1) ht.ne', Real.log_exp, mul_inv] at hs
    have hinv : t * (Real.exp 1)⁻¹ * t⁻¹ = (Real.exp 1)⁻¹ := by field_simp
    have H := mul_le_mul_of_nonneg_left hs ht.le
    rw [mul_sub, mul_one, ← mul_assoc, hinv, mul_add, mul_one] at H
    have hhalf : (Real.exp 1)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div, div_le_iff₀ (Real.exp_pos 1)]
      linarith [Real.add_one_le_exp (1 : ℝ)]
    linarith only [H, hhalf]
  have hbr : t * (6 * Real.log z + 9 / (4 * z) - 9) ≤ 9 := by
    norm_num at hlog
    have hh := mul_le_mul_of_nonneg_left hlog ht.le
    have hf := mul_le_mul_of_nonneg_left hfrac ht.le
    nlinarith only [hh, hf, he]
  obtain ⟨hα, hαhi⟩ := alpha_bounds_of_one_le hr
  calc
    _ = alpha r * (t * (6 * Real.log z + 9 / (4 * z) - 9)) := mul_assoc _ _ _
    _ ≤ alpha r * 9 := mul_le_mul_of_nonneg_left hbr hα
    _ ≤ 9 / 2 := by linarith

private theorem incidence_le (U : unitary Mat) (k : Fin 3) :
    (∑ j ∈ otherLevels k, (weight (physicalFrame U) k.castSucc j +
      weight (physicalFrame U) j k.castSucc)) ≤ 2 := by
  let V := physicalFrame U
  let κ := k.castSucc
  have hrow := row_weight V (physicalFrame_columns U) (physicalFrame_rows U) κ
  have hcol := col_weight V (physicalFrame_columns U) (physicalFrame_rows U) κ
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ κ)] at hrow hcol
  rw [Finset.sum_add_distrib]
  exact (by
    change (∑ j ∈ otherLevels k, weight V κ j) +
      (∑ j ∈ otherLevels k, weight V j κ) ≤ 2
    linarith only [hrow, hcol, weight_nonneg V κ κ])

/-- The upper pure second-derivative bound on the entire spectral cube.
The two fixed levels can be zero and the varying level can coincide with either. -/
theorem levelSlice_deriv2_le (U : unitary Mat) {r : ℝ} (hr : r ∈ Icc (1 : ℝ) (6 / 5))
    {x : Fin 3 → ℝ} (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) (k : Fin 3)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    deriv (deriv (levelSlice r U x k)) t ≤ 24 := by
  let V := physicalFrame U
  let y := Function.update x k t
  obtain ⟨hh, hb, hbHi, hc, hcHi, he, heHi⟩ := coefficient_bounds hr.1 hr.2 hr.2
  have himb := imbalance_le_one V (physicalFrame_columns U) (physicalFrame_rows U) k.castSucc
  have hscalar : 6 * t * scalarCoeff r U k ≤ 6 * (39 / 100 : ℝ) := by
    have hcoeff : scalarCoeff r U k ≤ 39 / 100 := by
      have hmul := mul_le_mul_of_nonneg_left himb hb
      unfold scalarCoeff
      change h r + bias r * imbalance V k.castSucc ≤ _
      norm_num at hh hbHi
      linarith only [hh, hbHi, hmul]
    calc
      _ ≤ 6 * t * (39 / 100) := mul_le_mul_of_nonneg_left hcoeff (by positivity)
      _ ≤ _ := by nlinarith only [ht.2]
  have hjump :
      (∑ j ∈ otherLevels k, edgeSecond r V k.castSucc j (levels x j) t) ≤ 2 * (279 / 40 : ℝ) := by
    have hterm (j : Fin 4) :
        edgeSecond r V k.castSucc j (levels x j) t ≤
          (weight V k.castSucc j + weight V j k.castSucc) * (279 / 40 : ℝ) := by
      have hyj := mem_Icc_levels hx j
      have hh := edge_second_le V k.castSucc j hc hcHi he heHi
        (low := 0) (b := 1) le_rfl ht.1.le ht.2 le_rfl hyj.1 hyj.2
      norm_num at hh
      exact hh
    calc
      _ ≤ ∑ j ∈ otherLevels k, (weight V k.castSucc j + weight V j k.castSucc) * (279 / 40) :=
        Finset.sum_le_sum fun j _ => hterm j
      _ ≤ _ := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (incidence_le U k) (by norm_num)
  have hy (i : Fin 3) : y i ∈ Icc (0 : ℝ) 1 := by
    by_cases hi : i = k
    · subst i
      simpa [y] using (show t ∈ Icc (0 : ℝ) 1 from ⟨ht.1.le, ht.2⟩)
    · simpa [y, Function.update_of_ne hi] using hx i
  have hcube (i : Fin 3) : y i ^ 3 ≤ 1 := by
    simpa using pow_le_pow_left₀ (hy i).1 (hy i).2 3
  have hT : fixedMass x k + t ^ 3 ≤ 4 := by
    rw [← total_update x k t]
    change totalAt (y 0) (y 1) (y 2) ≤ _
    unfold totalAt
    linarith only [hcube 0, hcube 1, hcube 2]
  have hent := entropy_second_upper hr.1 (fixedMass_nonneg k hx) ht.1 hT
  rw [(levelSlice_second_hasDerivAt hr.1 U hx k ht.1).deriv]
  unfold secondProfile
  linarith only [hscalar, hjump, hent]

private theorem levelSlice_interpolation_hypotheses (U : unitary Mat)
    {r : ℝ} (hr : r ∈ Icc (1 : ℝ) (6 / 5))
    {x : Fin 3 → ℝ} (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) (k : Fin 3)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    let f := levelSlice r U x k
    ContinuousOn f (Icc a b) ∧ DifferentiableOn ℝ f (Ioo a b) ∧
      DifferentiableOn ℝ (deriv f) (Ioo a b) ∧ (∀ t ∈ Ioo a b, deriv^[2] f t ≤ 24) := by
  refine ⟨(levelSlice_continuousOn hr.1 U hx k).mono fun _ ht => ha.trans ht.1, ?_, ?_, ?_⟩
  · exact fun t ht =>
      (levelSlice_hasDerivAt hr.1 U hx k (ha.trans_lt ht.1)).differentiableAt.differentiableWithinAt
  · exact fun t ht =>
      (levelSlice_second_hasDerivAt hr.1 U hx k (ha.trans_lt ht.1)).differentiableAt
        |>.differentiableWithinAt
  · intro t ht
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
      levelSlice_deriv2_le U hr hx k ⟨ha.trans_lt ht.1, ht.2.le.trans hb⟩

/-- The chord lower estimate on any nondegenerate level interval in the cube. -/
theorem levelSlice_chord (U : unitary Mat) {r : ℝ} (hr : r ∈ Icc (1 : ℝ) (6 / 5))
    {x : Fin 3 → ℝ} (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) (k : Fin 3)
    {a b t : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (ht : t ∈ Icc a b) :
    let f := levelSlice r U x k
    (b - t) / (b - a) * f a + (t - a) / (b - a) * f b -
      12 * (t - a) * (b - t) ≤ f t := by
  obtain ⟨hcont, hdiff, hdiff', hC⟩ := levelSlice_interpolation_hypotheses U hr hx k ha hb
  simpa only [show (24 : ℝ) / 2 = 12 by norm_num] using
    corner_interpolation 24 a b t hab hcont hdiff hdiff' hC ht.1 ht.2

/-- A common endpoint floor loses at most three times the squared level interval width. -/
theorem levelSlice_floor (U : unitary Mat) {r : ℝ} (hr : r ∈ Icc (1 : ℝ) (6 / 5))
    {x : Fin 3 → ℝ} (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) (k : Fin 3)
    {a b t L : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (ht : t ∈ Icc a b)
    (hlo : L ≤ levelSlice r U x k a) (hhi : L ≤ levelSlice r U x k b) :
    L - 3 * (b - a) ^ 2 ≤ levelSlice r U x k t := by
  obtain ⟨hcont, hdiff, hdiff', hC⟩ := levelSlice_interpolation_hypotheses U hr hx k ha hb
  convert corner_floor 24 a b t L (ht.1.trans ht.2) hcont hdiff hdiff' hC
    (by norm_num) hlo hhi ht.1 ht.2 using 1
  ring_nf

#print axioms levelSlice_second_hasDerivAt
#print axioms levelSlice_deriv2_le
#print axioms levelSlice_chord
#print axioms levelSlice_floor

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrumLevelInterpolation
