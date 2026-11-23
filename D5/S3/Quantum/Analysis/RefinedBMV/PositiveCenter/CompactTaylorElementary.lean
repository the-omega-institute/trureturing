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
