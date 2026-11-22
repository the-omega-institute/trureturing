/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterMiddleGapJet
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Directional specialization of quadratic Taylor coefficients. -/

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # The six quadratic coefficients used for the middle-gap certificate -/

namespace RefinedBMV.PositiveCenter

/-- The value, two first-order coefficients and three quadratic coefficients. -/
structure QuadraticJet (R : Type*) where
  value : R
  firstH : R
  firstD : R
  secondH : R
  mixed : R
  secondD : R

namespace QuadraticJet

def const [Zero R] (x : R) : QuadraticJet R := ⟨x, 0, 0, 0, 0, 0⟩

instance [Add R] : Add (QuadraticJet R) where
  add x y := ⟨x.value + y.value, x.firstH + y.firstH, x.firstD + y.firstD,
    x.secondH + y.secondH, x.mixed + y.mixed, x.secondD + y.secondD⟩

instance [Sub R] : Sub (QuadraticJet R) where
  sub x y := ⟨x.value - y.value, x.firstH - y.firstH, x.firstD - y.firstD,
    x.secondH - y.secondH, x.mixed - y.mixed, x.secondD - y.secondD⟩

instance [Add R] [Mul R] : Mul (QuadraticJet R) where
  mul x y := ⟨x.value * y.value,
    x.value * y.firstH + x.firstH * y.value,
    x.value * y.firstD + x.firstD * y.value,
    x.value * y.secondH + x.firstH * y.firstH + x.secondH * y.value,
    x.value * y.mixed + x.firstH * y.firstD + x.firstD * y.firstH + x.mixed * y.value,
    x.value * y.secondD + x.firstD * y.firstD + x.secondD * y.value⟩

/-- Evaluation in a direction gives the ordinary Taylor data along that segment. -/
structure IsLineAt (j : QuadraticJet ℝ) (f : ℝ → ℝ) (s x y : ℝ) : Prop where
  smooth : ContDiffAt ℝ 2 f s
  value_eq : f s = j.value
  first_eq : deriv f s = j.firstH * x + j.firstD * y
  second_eq : iteratedDeriv 2 f s = 2 * (j.secondH * x ^ 2 + j.mixed * x * y + j.secondD * y ^ 2)

theorem IsLineAt.const (s x y c : ℝ) : IsLineAt (QuadraticJet.const c) (fun _ ↦ c) s x y := by
  refine ⟨contDiffAt_const, rfl, ?_, ?_⟩
  · simp [QuadraticJet.const]
  · simp [QuadraticJet.const, iteratedDeriv_succ, iteratedDeriv_one]

theorem IsLineAt.add {s x y : ℝ} {a b : QuadraticJet ℝ} {f g : ℝ → ℝ}
    (ha : a.IsLineAt f s x y) (hb : b.IsLineAt g s x y) :
    (a + b).IsLineAt (f + g) s x y := by
  refine ⟨ha.smooth.add hb.smooth, ?_, ?_, ?_⟩
  · exact congrArg₂ (· + ·) ha.value_eq hb.value_eq
  · have h₁ := ha.smooth.differentiableAt (by norm_num)
    have h₂ := hb.smooth.differentiableAt (by norm_num)
    rw [deriv_add h₁ h₂, ha.first_eq, hb.first_eq]
    change _ = (a.firstH + b.firstH) * x + (a.firstD + b.firstD) * y
    ring
  · rw [iteratedDeriv_add ha.smooth hb.smooth, ha.second_eq, hb.second_eq]
    change _ = 2 * ((a.secondH + b.secondH) * x ^ 2 + (a.mixed + b.mixed) * x * y +
      (a.secondD + b.secondD) * y ^ 2)
    ring

theorem IsLineAt.sub {s x y : ℝ} {a b : QuadraticJet ℝ} {f g : ℝ → ℝ}
    (ha : a.IsLineAt f s x y) (hb : b.IsLineAt g s x y) :
    (a - b).IsLineAt (f - g) s x y := by
  refine ⟨ha.smooth.sub hb.smooth, ?_, ?_, ?_⟩
  · exact congrArg₂ (· - ·) ha.value_eq hb.value_eq
  · have h₁ := ha.smooth.differentiableAt (by norm_num)
    have h₂ := hb.smooth.differentiableAt (by norm_num)
    rw [deriv_sub h₁ h₂, ha.first_eq, hb.first_eq]
    change _ = (a.firstH - b.firstH) * x + (a.firstD - b.firstD) * y
    ring
  · rw [iteratedDeriv_sub ha.smooth hb.smooth, ha.second_eq, hb.second_eq]
    change _ = 2 * ((a.secondH - b.secondH) * x ^ 2 + (a.mixed - b.mixed) * x * y +
      (a.secondD - b.secondD) * y ^ 2)
    ring

theorem IsLineAt.mul {s x y : ℝ} {a b : QuadraticJet ℝ} {f g : ℝ → ℝ}
    (ha : a.IsLineAt f s x y) (hb : b.IsLineAt g s x y) :
    (a * b).IsLineAt (f * g) s x y := by
  refine ⟨ha.smooth.mul hb.smooth, ?_, ?_, ?_⟩
  · exact congrArg₂ (· * ·) ha.value_eq hb.value_eq
  · have h₁ := ha.smooth.differentiableAt (by norm_num)
    have h₂ := hb.smooth.differentiableAt (by norm_num)
    rw [deriv_mul h₁ h₂, ha.first_eq, hb.first_eq, ha.value_eq, hb.value_eq]
    change _ = (a.value * b.firstH + a.firstH * b.value) * x +
      (a.value * b.firstD + a.firstD * b.value) * y
    ring
  · rw [iteratedDeriv_mul ha.smooth hb.smooth]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDeriv_zero, iteratedDeriv_one,
      Nat.choose_zero_right, Nat.choose_self, Nat.reduceSub, Nat.cast_one, Nat.choose_one_right,
      zero_add, one_mul, ha.value_eq, hb.value_eq, ha.first_eq, hb.first_eq,
      ha.second_eq, hb.second_eq]
    change _ = 2 * ((a.value*b.secondH+a.firstH*b.firstH+a.secondH*b.value)*x^2 +
      (a.value*b.mixed+a.firstH*b.firstD+a.firstD*b.firstH+a.mixed*b.value)*x*y +
      (a.value*b.secondD+a.firstD*b.firstD+a.secondD*b.value)*y^2)
    norm_num <;> ring

end QuadraticJet

end RefinedBMV.PositiveCenter
