import D5.S3.Quantum.Semigroups.WuCubicHotOuter
import D5.S3.Quantum.Semigroups.WuCubicGibbsEquality

/-! The tracial endpoint of the equal-cap two-mode cubic inequality. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matrix ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Semigroups.WuCubicTracialEndpoint

open WuCubicDirectedOccupationCap (Mat)
open WuCubicAngularCertificate (normalizedDeficit)
open WuCubicOperatorNormalization (operatorDeficit)
open WuCubicGibbsEquality (operatorDeficit_nonneg_and_eq_zero_iff)
open WuCubicHotOuter (adjacentSum edgeFloor edgeGamma mass spread squareDeficit squareEnergy
  squareFloor tracialSquare)
open WuCubicSpectralVariance (thermalLambda thermalMassCoefficient)
open WuRepeatedMiddleCubic (alpha)
open private levelsAt from D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
open private c gamma bias e from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private adjacent angular_excess diagonal edgeFloor_nonneg edgeGamma_antitone fraction_bounds
  sorted_levels source_split symmetricEnergy from D5.S3.Quantum.Semigroups.WuCubicHotOuter

private theorem edgeFloor_ge_quartic {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    (b - a)^4 * (157 / 200) / 8 ≤ edgeFloor a b := by
  have hsum : 0 < a + b := add_pos_of_nonneg_of_pos ha (ha.trans_lt hab)
  have hk : 0 ≤ (b - a) / (a + b) := div_nonneg (sub_nonneg.mpr hab.le) hsum.le
  have hk₁ : (b - a) / (a + b) ≤ 1 := (div_le_one hsum).2 (by linarith)
  have hΓ : (157 / 200 : ℝ) ≤ edgeGamma ((b - a) / (a + b)) := by
    calc
      (157 / 200 : ℝ) = edgeGamma 1 := by norm_num [edgeGamma]
      _ ≤ _ := edgeGamma_antitone hk hk₁
  unfold edgeFloor
  calc
    _ ≤ (b - a)^4 * (157 / 200) / (4 * (a + b)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith [hab.le])
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hΓ (by positivity))
      (by positivity)

/-- A quartic bound in the full ordered tracial domain, uniform over complex frames. -/
theorem normalizedDeficit_tracial_quartic (U : unitary Mat) {m n q : ℝ}
    (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq : q ≤ 1) (hm₁ : m < 1) :
    (157 / 25600 : ℝ) * (1 - m)^4 ≤ normalizedDeficit 1 U m n q := by
  let x := levelsAt m n q
  have hn := hm.trans hmn
  have hq₀ := hn.trans hnq
  have hx : Monotone x := sorted_levels hmn hnq hq
  have hs : 0 < spread x := sub_pos.mpr hm₁
  have hx₀ (i : Fin 4) : 0 ≤ x i := hm.trans (hx (Fin.zero_le i))
  have hsum (i : Fin 3) : 0 ≤ adjacentSum x i :=
    add_nonneg (hx₀ i.castSucc) (hx₀ i.succ)
  have hc : 0 ≤ c 1 := by norm_num [c, gamma]
  have hdiag (i : Fin 3) : 0 ≤ diagonal x i := by
    unfold diagonal
    exact mul_nonneg (sq_nonneg _) (hsum i)
  have hadj (i j : Fin 3) : 0 ≤ adjacent x i j := by
    unfold adjacent
    exact mul_nonneg (mul_nonneg (fraction_bounds hx hs i).1 (fraction_bounds hx hs j).1)
        (add_nonneg (hsum i) (hsum j))
  have hang := angular_excess hx hm hs U (fun _ => 0) 0 0 (c 1)
    (fun _ => le_rfl) le_rfl le_rfl
    (fun i => mul_nonneg hc (hdiag i)) (mul_nonneg hc (hadj 0 1))
    (mul_nonneg hc (hadj 1 2)) hc
  simp only [zero_add, zero_mul, zero_div, add_zero] at hang
  have hangular : 0 ≤ c 1 * (symmetricEnergy U x - squareEnergy x) := by
    simpa only [zero_mul] using (le_div_iff₀ (pow_pos hs 2)).mp hang
  have hLambda : thermalLambda 0 = 1 := by norm_num [thermalLambda]
  have hα : alpha 1 = 1 / 2 := by norm_num [alpha]
  have hmass : thermalMassCoefficient 0 = 0 := by
    norm_num [thermalMassCoefficient, Real.log_one]
  have hbias : bias 1 = 0 := by norm_num [bias]
  have he : e 1 = 0 := by norm_num [e]
  have hsplit := source_split (t := 0) le_rfl hm hmn hnq U
  simp only [add_zero, hLambda, hα, hmass, hbias, he, sub_self, zero_mul,
    sub_zero, one_mul, zero_add] at hsplit
  have hfloor : squareFloor x ≤ normalizedDeficit 1 U m n q := by
    rw [hsplit]
    exact (tracialSquare x hx hm rfl).trans (le_add_of_nonneg_right hangular)
  have hnonneg₀ := edgeFloor_nonneg hm hmn
  have hnonneg₁ := edgeFloor_nonneg hm (hmn.trans hnq)
  have hnonneg₂ := edgeFloor_nonneg hn (hnq.trans hq)
  have hnonneg₃ := edgeFloor_nonneg hq₀ hq
  have hdet : 0 ≤ 4 * (x 0 ^ 3 - (x 1 * x 2)^3)^2 / mass x ^ 3 := by
    have hM : 0 ≤ mass x := Finset.sum_nonneg fun i _ => pow_nonneg (hx₀ i) 3
    positivity
  have hlarge {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hgap : (1 - m) / 2 ≤ b - a) :
      (157 / 25600 : ℝ) * (1 - m)^4 ≤ edgeFloor a b := by
    have hhalf : 0 ≤ (1 - m) / 2 := by linarith
    have hab : a < b := by linarith
    calc
      _ = ((1 - m) / 2)^4 * (157 / 200) / 8 := by ring
      _ ≤ (b - a)^4 * (157 / 200) / 8 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hhalf hgap 4) (by norm_num)) (by norm_num)
      _ ≤ _ := edgeFloor_ge_quartic ha hab hb
  apply le_trans _ hfloor
  change _ ≤ edgeFloor m n + edgeFloor m q + edgeFloor n 1 + edgeFloor q 1 +
    4 * (x 0 ^ 3 - (x 1 * x 2)^3)^2 / mass x ^ 3
  by_cases hgap : (1 - m) / 2 ≤ n - m
  · have h := hlarge hm (hnq.trans hq) hgap
    linarith only [h, hnonneg₁, hnonneg₂, hnonneg₃, hdet]
  · have h := hlarge hn le_rfl (show (1 - m) / 2 ≤ 1 - n by linarith)
    linarith only [h, hnonneg₀, hnonneg₁, hnonneg₃, hdet]

/-- Every nonscalar ordered spectrum has strictly positive deficit at the tracial endpoint. -/
theorem normalizedDeficit_tracial_pos (U : unitary Mat) {m n q : ℝ}
    (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq : q ≤ 1) (hm₁ : m < 1) :
    0 < normalizedDeficit 1 U m n q :=
  (mul_pos (show (0 : ℝ) < 157 / 25600 by norm_num) (pow_pos (sub_pos.mpr hm₁) 4)).trans_le
    (normalizedDeficit_tracial_quartic U hm hmn hnq hq hm₁)

/-- The ordinary-trace cubic inequality at the tracial endpoint, with scalar equality. -/
theorem operatorDeficit_tracial_nonneg_and_eq_zero_iff
    {X : WuCubicOperatorBridge.Mat} (hX : X.PosSemidef) :
    0 ≤ operatorDeficit 1 X ∧
      (operatorDeficit 1 X = 0 ↔
        ∃ c : ℝ, 0 ≤ c ∧ X = (c : ℂ) • (1 : WuCubicOperatorBridge.Mat)) := by
  refine operatorDeficit_nonneg_and_eq_zero_iff (r := 1) le_rfl ?_ hX
  intro U m n q hm hmn hnq hq hne
  apply normalizedDeficit_tracial_pos U hm hmn hnq hq
  by_contra! h
  have hm₁ : m = 1 := le_antisymm (hmn.trans (hnq.trans hq)) h
  have hn₁ : n = 1 := le_antisymm (hnq.trans hq) (h.trans hmn)
  have hq₁ : q = 1 := le_antisymm hq (h.trans (hmn.trans hnq))
  exact hne (by norm_num [hm₁, hn₁, hq₁])

end D5.S3.Quantum.Semigroups.WuCubicTracialEndpoint
