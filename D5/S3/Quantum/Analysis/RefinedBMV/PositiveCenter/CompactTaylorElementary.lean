/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactTaylorElementary
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Centered Taylor enclosures for the exponential and regularized gaps. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorModel
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactScalarTails
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactPositiveMomentTails

/-! Centered Taylor models for the elementary functions in the compact comparison. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel

open scoped BigOperators

/-- The coefficient of degree `m` after translating a finite series by `center`. -/
def shiftedSeriesCoeff (coeff : ℕ → ℝ) (terms : ℕ) (center : ℝ) (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico m terms, coeff n * (n.choose m : ℝ) * center ^ (n - m)

private theorem shiftedMonomialTail_le {n order : ℕ} (horder : order ≤ n)
    {center offset radius width : ℝ} (hr : |center| + |offset| ≤ radius)
    (hw : |offset| ≤ width) :
    (∑ m ∈ Finset.Ico order (n + 1),
      (n.choose m : ℝ) * |center| ^ (n - m) * |offset| ^ m) ≤
      width ^ order * ((n.choose order : ℝ) * radius ^ (n - order)) := by
  have hchoose (m : ℕ) (hm : order ≤ m) :
      (n.choose m : ℝ) ≤ (n.choose order : ℝ) * ((n - order).choose (m - order) : ℝ) := by
    exact_mod_cast calc
      n.choose m = n.choose m * 1 := (Nat.mul_one _).symm
      _ ≤ n.choose m * m.choose order := Nat.mul_le_mul_left _ (Nat.choose_pos hm)
      _ = _ := Nat.choose_mul hm
  calc
    _ ≤ ∑ m ∈ Finset.Ico order (n + 1), width ^ order * (n.choose order : ℝ) *
        (((n - order).choose (m - order) : ℝ) *
          |center| ^ (n - m) * |offset| ^ (m - order)) := by
      apply Finset.sum_le_sum
      intro m hm
      have hm₁ := (Finset.mem_Ico.mp hm).1
      have he : m = order + (m - order) := (Nat.add_sub_of_le hm₁).symm
      conv_lhs => arg 2; rw [he, pow_add]
      calc
        _ ≤ ((n.choose order : ℝ) * ((n - order).choose (m - order) : ℝ)) *
            |center| ^ (n - m) * (width ^ order * |offset| ^ (m - order)) := by
          gcongr
          exact hchoose m hm₁
        _ = _ := by ring
    _ = width ^ order * (n.choose order : ℝ) * (|offset| + |center|) ^ (n - order) := by
      rw [← Finset.mul_sum, Finset.sum_Ico_eq_sum_range, add_pow]
      have hlen : n + 1 - order = n - order + 1 := by omega
      rw [hlen]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have he : n - (order + j) = n - order - j := by omega
      rw [he, Nat.add_sub_cancel_left]
      ring
    _ ≤ _ := by
      have hwidth : 0 ≤ width := (abs_nonneg offset).trans hw
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (pow_nonneg hwidth _) (Nat.cast_nonneg _))
      exact pow_le_pow_left₀ (by positivity) (by simpa [add_comm] using hr) _

/-- Translate and truncate a finite series with a single absolute error bound on the
discarded terms. The bound uses the coefficient majorant at the outer radius. -/
theorem shiftedSeries_error_le (coeff : ℕ → ℝ) {terms order : ℕ} (horder : order ≤ terms)
    {center offset radius width : ℝ} (hr : |center| + |offset| ≤ radius)
    (hw : |offset| ≤ width) :
    |(∑ n ∈ Finset.range terms, coeff n * (center + offset) ^ n) -
      (∑ m ∈ Finset.range order, shiftedSeriesCoeff coeff terms center m * offset ^ m)| ≤
      width ^ order * ∑ n ∈ Finset.Ico order terms,
        |coeff n| * (n.choose order : ℝ) * radius ^ (n - order) := by
  have hshift :
      (∑ m ∈ Finset.range terms, shiftedSeriesCoeff coeff terms center m * offset ^ m) =
      ∑ n ∈ Finset.range terms, coeff n * (center + offset) ^ n := by
    simp only [shiftedSeriesCoeff, Finset.sum_mul, ← Nat.Ico_zero_eq_range]
    rw [Finset.sum_Ico_Ico_comm]
    apply Finset.sum_congr rfl
    intro n _
    rw [Nat.Ico_zero_eq_range, add_comm center offset, add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [← hshift, ← Finset.sum_range_add_sum_Ico _ horder, add_sub_cancel_left]
  simp only [shiftedSeriesCoeff, Finset.sum_mul]
  rw [Finset.sum_Ico_Ico_comm]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simp only [abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
  simp_rw [show ∀ m : ℕ,
    |coeff n| * (n.choose m : ℝ) * |center| ^ (n - m) * |offset| ^ m =
      |coeff n| * ((n.choose m : ℝ) * |center| ^ (n - m) * |offset| ^ m) from
        fun m => by ring]
  rw [← Finset.mul_sum]
  calc
    _ ≤ |coeff n| * (width ^ order * ((n.choose order : ℝ) * radius ^ (n - order))) :=
      mul_le_mul_of_nonneg_left (shiftedMonomialTail_le (Finset.mem_Ico.mp hn).1 hr hw)
        (abs_nonneg _)
    _ = _ := by ring

/-- Enclose a finite series using the shifted coefficient models and the
certified error for the discarded terms. -/
theorem Model.shiftedSeries_sound {s t z center offset radius width : ℝ} {X : Model}
    (hb : InBox s t z) (hx : X.Encloses s t z offset) {terms order : ℕ}
    (horder : order ≤ terms) (hr : |center| + |offset| ≤ radius) (hw : |offset| ≤ width)
    (coeff : ℕ → ℝ) (models : ℕ → Model)
    (hmodels : ∀ m < order, (models m).Encloses s t z (shiftedSeriesCoeff coeff terms center m))
    {error : ℚ} (he : width ^ order * ∑ n ∈ Finset.Ico order terms,
        |coeff n| * (n.choose order : ℝ) * radius ^ (n - order) ≤ (error : ℝ)) :
    ((Model.series order models X).widen error).Encloses s t z
      (∑ n ∈ Finset.range terms, coeff n * (center + offset) ^ n) :=
  Model.widen_sound (Model.series_sound hb hx _ _ _ hmodels)
    ((shiftedSeries_error_le coeff horder hr hw).trans he)

private def expGeometricModel (order : ℕ) (radius : ℚ) (x : Model) : Model :=
  (Model.series order (fun n => Model.ofRat (1 / (n.factorial : ℚ))) x).widen
    (radius ^ order / (order.factorial : ℚ) / (1 - radius / (order.succ : ℚ)))

private theorem expGeometricModel_sound {s t z x : ℝ} {X : Model} {order : ℕ} {radius : ℚ}
    (hb : InBox s t z) (hx : X.Encloses s t z x) (horder : 2 ≤ order)
    (hr : |x| ≤ (radius : ℝ)) (hsmall : (radius : ℝ) / (order.succ : ℝ) < 1) :
    (expGeometricModel order radius X).Encloses s t z (Real.exp x) := by
  apply Model.widen_sound
    (g := ∑ n ∈ Finset.range order, x ^ n / (n.factorial : ℝ))
  · simp only [div_eq_inv_mul]
    apply Model.series_sound hb hx
    intro n _
    simpa using Model.ofRat_sound (1 / (n.factorial : ℚ)) s t z
  · push_cast
    simpa only [Nat.cast_succ] using
      compactExp_sub_truncation_geometric_le horder hr hsmall

private def expCenteredModel (center : ℚ) (halvings : ℕ) (radius : ℚ) (x : Model) : Model :=
  let reduced := center / (2 : ℚ) ^ halvings
  let constant := expGeometricModel 31 (51 / 100) (Model.ofRat reduced)
  let offset := expGeometricModel 31 radius (x.sub (Model.ofRat center))
  (constant.pow (2 ^ halvings)).mul offset

private theorem expCenteredModel_sound {s t z x : ℝ} {X : Model} {center radius : ℚ} {halvings : ℕ}
    (hb : InBox s t z) (hx : X.Encloses s t z x)
    (hcenter : |(center : ℝ) / (2 : ℝ) ^ halvings| ≤ 51 / 100)
    (hr : |x - (center : ℝ)| ≤ (radius : ℝ)) (hsmall : (radius : ℝ) / 32 < 1) :
    (expCenteredModel center halvings radius X).Encloses s t z (Real.exp x) := by
  have h := Model.ofRat_sound (center / (2 : ℚ) ^ halvings) s t z
  push_cast at h
  have hc := expGeometricModel_sound (order := 31) (radius := 51 / 100) hb h
    (by decide) (by push_cast; exact hcenter) (by norm_num)
  have ho := expGeometricModel_sound (order := 31) hb
    (Model.sub_sound hx (Model.ofRat_sound center s t z)) (by decide) hr (by simpa using hsmall)
  have he := Model.mul_sound hb (Model.pow_sound hb hc (2 ^ halvings)) ho
  rw [← Real.exp_nat_mul, ← Real.exp_add] at he
  have harg : ((2 ^ halvings : ℕ) : ℝ) * ((center : ℝ) / (2 : ℝ) ^ halvings) +
      (x - (center : ℝ)) = x := by
    push_cast
    field_simp
    ring
  rw [harg] at he
  exact he

def phiGeometricModel (radius : ℚ) (x : Model) : Model :=
  (Model.series 25 (fun n => Model.ofRat (1 / ((n + 1).factorial : ℚ))) x).widen
    (radius ^ 25 / ((25 : ℕ).factorial : ℚ) / (1 - radius / 26))

theorem phiGeometricModel_sound {s t z x : ℝ} {X : Model} {radius : ℚ}
    (hb : InBox s t z) (hx : X.Encloses s t z x) (hx₀ : x ≠ 0)
    (hr : |x| ≤ (radius : ℝ)) (hsmall : (radius : ℝ) ≤ 2) :
    (phiGeometricModel radius X).Encloses s t z ((Real.exp x - 1) / x) := by
  apply Model.widen_sound (g := compactPhiTaylor x)
  · unfold compactPhiTaylor
    simp only [div_eq_inv_mul]
    apply Model.series_sound hb hx
    intro n _
    simpa using Model.ofRat_sound (1 / ((n + 1).factorial : ℚ)) s t z
  · push_cast
    exact compactPhi_sub_taylor_geometric_le hx₀ hr hsmall

def sinhcGeometricModel (radius : ℚ) (x : Model) : Model :=
  (Model.series 25 (fun n => Model.ofRat (if n % 2 = 0 then 1 / ((n + 1).factorial : ℚ) else 0)) x)
    |>.widen (radius ^ 25 / ((25 : ℕ).factorial : ℚ) / (1 - radius / 26))

theorem sinhcGeometricModel_sound {s t z x : ℝ} {X : Model} {radius : ℚ}
    (hb : InBox s t z) (hx : X.Encloses s t z x) (hx₀ : x ≠ 0)
    (hr : |x| ≤ (radius : ℝ)) (hsmall : (radius : ℝ) ≤ 2) :
    (sinhcGeometricModel radius X).Encloses s t z (Real.sinh x / x) := by
  apply Model.widen_sound (g := compactSinhcTaylor x)
  · unfold compactSinhcTaylor
    have he : (∑ n ∈ Finset.range 25, (if Even n then x ^ n / ((n + 1).factorial : ℝ) else 0)) =
        ∑ n ∈ Finset.range 25,
          ((if n % 2 = 0 then 1 / ((n + 1).factorial : ℚ) else 0 : ℚ) : ℝ) * x ^ n := by
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : n % 2 = 0
      · simp [hn, Nat.even_iff, div_eq_mul_inv, mul_comm]
      · simp [hn, Nat.even_iff]
    rw [he]
    exact Model.series_sound hb hx 25 _ _ (fun n _ => Model.ofRat_sound _ s t z)
  · push_cast
    exact compactSinhc_sub_taylor_geometric_le hx₀ hr hsmall

def Model.argumentRadius (p : Model) : ℚ := (p.absUpper : ℚ) / (scale : ℚ)

theorem Model.argumentRadius_sound {p : Model} {s t z f : ℝ}
    (hb : InBox s t z) (hp : p.Encloses s t z f) :
    |f| ≤ (p.argumentRadius : ℝ) := by
  simpa [Model.argumentRadius] using Model.absUpper_sound hb hp

private def Model.center (p : Model) : ℚ :=
  let constant := p.polynomial.terms.find? fun a => a.exponents == (0, 0, 0)
  (((constant.map (·.coefficient)).getD 0 : ℤ) : ℚ) / (scale : ℚ)

private def Model.expHalvings (p : Model) : ℕ :=
  ((List.range 10).find? fun n => decide (|p.center / (2 : ℚ) ^ n| ≤ 1 / 2)).getD 9

def Model.centeredExp (p : Model) : Model :=
  expCenteredModel p.center p.expHalvings
    (p.sub (Model.ofRat p.center)).argumentRadius p

theorem Model.centeredExp_sound {p : Model} {s t z f : ℝ}
    (hb : InBox s t z) (hp : p.Encloses s t z f)
    (hcenter : |p.center / (2 : ℚ) ^ p.expHalvings| ≤ 51 / 100)
    (hsmall : (p.sub (Model.ofRat p.center)).argumentRadius < 32) :
    p.centeredExp.Encloses s t z (Real.exp f) := by
  apply expCenteredModel_sound hb hp
  · have hcast : ((|p.center / (2 : ℚ) ^ p.expHalvings| : ℚ) : ℝ) ≤
        ((51 / 100 : ℚ) : ℝ) := Rat.cast_le.mpr hcenter
    simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using hcast
  · exact Model.argumentRadius_sound hb (Model.sub_sound hp (Model.ofRat_sound p.center s t z))
  · exact (div_lt_iff₀ (by norm_num : (0 : ℝ) < 32)).2 (by exact_mod_cast hsmall)

def Model.expChecks (p : Model) : Prop :=
  |p.center / (2 : ℚ) ^ p.expHalvings| ≤ 51 / 100 ∧
    (p.sub (Model.ofRat p.center)).argumentRadius < 32

theorem Model.expChecks_sound {p : Model} {s t z f : ℝ}
    (hb : InBox s t z) (hp : p.Encloses s t z f) (hcheck : p.expChecks) :
    p.centeredExp.Encloses s t z (Real.exp f) :=
  Model.centeredExp_sound hb hp hcheck.1 hcheck.2

def positiveRateGapModel (H X : Model) : Model :=
  let product := H.mul X
  X.mul (phiGeometricModel product.argumentRadius product)

theorem positiveRateGapModel_sound {H X : Model} {s t z x h : ℝ}
    (hb : InBox s t z) (hh : H.Encloses s t z h) (hx : X.Encloses s t z x)
    (hh₀ : h ≠ 0) (hx₀ : x ≠ 0) (hsmall : (H.mul X).argumentRadius ≤ 2) :
    (positiveRateGapModel H X).Encloses s t z ((Real.exp (h * x) - 1) / h) := by
  have hprod := Model.mul_sound hb hh hx
  have hphi := phiGeometricModel_sound hb hprod (mul_ne_zero hh₀ hx₀)
    (Model.argumentRadius_sound hb hprod) (by exact_mod_cast hsmall)
  have hgap := Model.mul_sound hb hx hphi
  have he : x * ((Real.exp (h * x) - 1) / (h * x)) =
      (Real.exp (h * x) - 1) / h := by field_simp
  rw [he] at hgap
  exact hgap

end RefinedBMV.PositiveCenter.CompactTaylorModel
