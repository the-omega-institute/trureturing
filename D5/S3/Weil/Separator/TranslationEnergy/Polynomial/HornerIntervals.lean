/- GID: D5/S3/Weil/Separator/TranslationEnergy/Polynomial/HornerIntervals
   generality: G
   mirror-B: D5/B/S3/Weil/Separator/TranslationEnergy/Polynomial/HornerIntervals
   mirror-E: none(waiver:exact-rational-and-analytic-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Weil/Separator/TranslationEnergy/Generic/Certificate.full_certificate; instance=D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.center_certificate
   digest: Exact rational Horner expressions have checked enclosures and controlled width. -/

import D5.S3.Weil.Separator.TranslationEnergy.Polynomial.ProductIntervals

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Separator.TranslationEnergy.Polynomial

open D5.S0.Certificates.BoxCover.RationalIntervalExpression

def exactConstant (c : Rat) : Expr 1 := .const c c c

def exactInput (a b : Rat) : Expr 1 := .input 0 a b

def intervalAdd (e f : Expr 1) : Expr 1 :=
  .add ((bounds e).1 + (bounds f).1) ((bounds e).2 + (bounds f).2) e f

def intervalMul (e f : Expr 1) : Expr 1 :=
  .mul (productLower (bounds e).1 (bounds e).2 (bounds f).1 (bounds f).2)
    (productUpper (bounds e).1 (bounds e).2 (bounds f).1 (bounds f).2) e f

def hornerInterval (a b : Rat) : List Rat → Expr 1
  | [] => exactConstant 0
  | [c] => exactConstant c
  | c :: d :: ds => intervalAdd (exactConstant c)
      (intervalMul (exactInput a b) (hornerInterval a b (d :: ds)))
termination_by cs => cs.length
decreasing_by simp_wf

def amplitude (B : Rat) : List Rat → Rat
  | [] => 0
  | c :: cs => |c| + B * amplitude B cs

def slope (B : Rat) : List Rat → Rat
  | [] => 0
  | _ :: cs => amplitude B cs + B * slope B cs

theorem amplitude_nonneg (B : Rat) (hB : 0 ≤ B) (cs : List Rat) :
    0 ≤ amplitude B cs := by
  induction cs with
  | nil => simp [amplitude]
  | cons c cs ih => simp only [amplitude]; positivity

theorem horner_check (a b : Rat) (hab : a ≤ b) (cs : List Rat) :
    check (fun _ : Fin 1 => (a, b)) (hornerInterval a b cs) = true := by
  induction cs with
  | nil => simp [hornerInterval, exactConstant, check]
  | cons c cs ih =>
    cases cs with
    | nil => simp [hornerInterval, exactConstant, check]
    | cons d ds =>
      let t := hornerInterval a b (d :: ds)
      have ht : check (fun _ : Fin 1 => (a, b)) t = true := ih
      have hcorners :
          productLower a b (bounds t).1 (bounds t).2 ≤
            productUpper a b (bounds t).1 (bounds t).2 ∧
          productLower a b (bounds t).1 (bounds t).2 ≤ a * (bounds t).1 ∧
          productLower a b (bounds t).1 (bounds t).2 ≤ a * (bounds t).2 ∧
          productLower a b (bounds t).1 (bounds t).2 ≤ b * (bounds t).1 ∧
          productLower a b (bounds t).1 (bounds t).2 ≤ b * (bounds t).2 ∧
          a * (bounds t).1 ≤ productUpper a b (bounds t).1 (bounds t).2 ∧
          a * (bounds t).2 ≤ productUpper a b (bounds t).1 (bounds t).2 ∧
          b * (bounds t).1 ≤ productUpper a b (bounds t).1 (bounds t).2 ∧
          b * (bounds t).2 ≤ productUpper a b (bounds t).1 (bounds t).2 := by
        simp [productLower, productUpper]
      let m := intervalMul (exactInput a b) t
      have hm : check (fun _ : Fin 1 => (a, b)) m = true := by
        simp only [intervalMul, bounds, exactInput, Fin.isValue, check,
          Std.le_refl, and_self, and_true, ht, Bool.true_and,
          Bool.and_eq_true, decide_eq_true_eq, m]
        exact ⟨hab, decide_eq_true hcorners⟩
      have hmo : (bounds m).1 ≤ (bounds m).2 := hcorners.1
      have hc : check (fun _ : Fin 1 => (a, b)) (exactConstant c) = true := by
        simp [exactConstant, check]
      have hsum : (bounds (exactConstant c)).1 + (bounds m).1 ≤
          (bounds (exactConstant c)).2 + (bounds m).2 := by
        simpa [exactConstant, bounds] using add_le_add_right hmo c
      have hadd : check (fun _ : Fin 1 => (a, b))
          (intervalAdd (exactConstant c) m) = true := by
        simp [intervalAdd, check, hc, hm, hsum]
      simpa only [hornerInterval] using hadd

theorem horner_interval_bounds (a b B : Rat) (hab : a ≤ b)
    (hB : 0 ≤ B) (ha : -B ≤ a) (hb : b ≤ B) (cs : List Rat) :
    let e := hornerInterval a b cs;
    -amplitude B cs ≤ (bounds e).1 ∧
    (bounds e).1 ≤ (bounds e).2 ∧
    (bounds e).2 ≤ amplitude B cs ∧
    (bounds e).2 - (bounds e).1 ≤ slope B cs * (b - a) := by
  induction cs with
  | nil =>
    simp [hornerInterval, exactConstant, bounds, amplitude, slope]
  | cons c cs ih =>
    cases cs with
    | nil =>
      simp only [hornerInterval, amplitude, slope, amplitude,
        mul_zero, add_zero, exactConstant, bounds, sub_self, zero_mul]
      refine ⟨neg_abs_le c, le_refl _, le_abs_self c, le_refl _⟩
    | cons d ds =>
      have ht := ih
      let t := hornerInterval a b (d :: ds)
      have htlo : -amplitude B (d :: ds) ≤ (bounds t).1 := ht.1
      have htord : (bounds t).1 ≤ (bounds t).2 := ht.2.1
      have hthi : (bounds t).2 ≤ amplitude B (d :: ds) := ht.2.2.1
      have htwidth := ht.2.2.2
      have hAmp : 0 ≤ amplitude B (d :: ds) := amplitude_nonneg B hB _
      have hxa : |a| ≤ B := abs_le.mpr ⟨ha, hab.trans hb⟩
      have hxb : |b| ≤ B := abs_le.mpr ⟨by linarith, hb⟩
      have htl : |(bounds t).1| ≤ amplitude B (d :: ds) :=
        abs_le.mpr ⟨htlo, htord.trans hthi⟩
      have htu : |(bounds t).2| ≤ amplitude B (d :: ds) :=
        abs_le.mpr ⟨by linarith, hthi⟩
      let m := intervalMul (exactInput a b) t
      have hmwidth := product_width a b (bounds t).1 (bounds t).2
        (amplitude B (d :: ds)) B hab htord hxa hxb htl htu hAmp hB
      have hmord : (bounds m).1 ≤ (bounds m).2 :=
        by simp [m, intervalMul, exactInput, bounds, productLower, productUpper]
      simp only [hornerInterval, amplitude, slope] at ⊢
      change -( |c| + B * amplitude B (d :: ds)) ≤
          (bounds (intervalAdd (exactConstant c) m)).1 ∧
        (bounds (intervalAdd (exactConstant c) m)).1 ≤
          (bounds (intervalAdd (exactConstant c) m)).2 ∧
        (bounds (intervalAdd (exactConstant c) m)).2 ≤
          |c| + B * amplitude B (d :: ds) ∧
        (bounds (intervalAdd (exactConstant c) m)).2 -
          (bounds (intervalAdd (exactConstant c) m)).1 ≤
          (amplitude B (d :: ds) + B * slope B (d :: ds)) * (b - a)
      refine ⟨?_, ?_, ?_, ?_⟩
      · change -( |c| + B * amplitude B (d :: ds)) ≤
          c + productLower a b (bounds t).1 (bounds t).2
        have := hmwidth.1
        dsimp [m, intervalMul, bounds] at this
        linarith [neg_abs_le c]
      · change c + productLower a b (bounds t).1 (bounds t).2 ≤
          c + productUpper a b (bounds t).1 (bounds t).2
        exact add_le_add_right hmord c
      · change c + productUpper a b (bounds t).1 (bounds t).2 ≤
          |c| + B * amplitude B (d :: ds)
        have := hmwidth.2.1
        dsimp [m, intervalMul, bounds] at this
        linarith [le_abs_self c]
      · change c + productUpper a b (bounds t).1 (bounds t).2 -
          (c + productLower a b (bounds t).1 (bounds t).2) ≤
          (amplitude B (d :: ds) + B * slope B (d :: ds)) * (b - a)
        change (bounds t).2 - (bounds t).1 ≤
          slope B (d :: ds) * (b - a) at htwidth
        nlinarith [hmwidth.2.2, mul_le_mul_of_nonneg_left htwidth hB]

#print axioms product_width
#print axioms horner_check
#print axioms horner_interval_bounds

end D5.S3.Weil.Separator.TranslationEnergy.Polynomial
