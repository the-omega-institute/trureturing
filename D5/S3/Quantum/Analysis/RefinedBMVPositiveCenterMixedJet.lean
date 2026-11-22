/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterMixedJet
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mixed derivative rules for the interval certificate of the BMV kernel. -/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Mixed derivatives in the positive-center BMV certificate -/

open Filter
open scoped Topology

namespace RefinedBMV.PositiveCenter

/-- Value, two partial derivatives, and the derivative in the second variable
of the first partial derivative. -/
structure MixedJet (R : Type*) where
  value : R
  du : R
  dv : R
  duv : R

namespace MixedJet

variable {R : Type*}

def add [Add R] (a b : MixedJet R) : MixedJet R :=
  ⟨a.value + b.value, a.du + b.du, a.dv + b.dv, a.duv + b.duv⟩

def sub [Sub R] (a b : MixedJet R) : MixedJet R :=
  ⟨a.value - b.value, a.du - b.du, a.dv - b.dv, a.duv - b.duv⟩

def mul [Add R] [Mul R] (a b : MixedJet R) : MixedJet R :=
  ⟨a.value * b.value,
    a.du * b.value + a.value * b.du,
    a.dv * b.value + a.value * b.dv,
    a.duv * b.value + a.du * b.dv + a.dv * b.du + a.value * b.duv⟩

def reciprocal [OfNat R 1] [OfNat R 2] [Neg R] [Sub R] [Mul R] [Div R]
    (a : MixedJet R) : MixedJet R :=
  let q := 1 / a.value
  let q₂ := q * q
  ⟨q, -(q₂ * a.du), -(q₂ * a.dv), q₂ * (2 * q * a.du * a.dv - a.duv)⟩

def sqrtFrom [OfNat R 1] [OfNat R 2] [Sub R] [Mul R] [Div R]
    (a : MixedJet R) (r : R) : MixedJet R :=
  let q := 1 / (2 * r)
  ⟨r, q * a.du, q * a.dv, q * a.duv - q * q * (1 / r) * a.du * a.dv⟩

/-- The first partial is represented on a neighborhood so the mixed
partial is the derivative of that same function there. -/
def IsAt (f : ℝ → ℝ → MixedJet ℝ) (u v : ℝ) : Prop :=
  (∀ᶠ y in 𝓝 v, HasDerivAt (fun x ↦ (f x y).value) (f u y).du u) ∧
  HasDerivAt (fun y ↦ (f u y).value) (f u v).dv v ∧
  HasDerivAt (fun y ↦ (f u y).du) (f u v).duv v

theorem IsAt.add {f g : ℝ → ℝ → MixedJet ℝ} {u v : ℝ}
    (hf : IsAt f u v) (hg : IsAt g u v) : IsAt (fun x y ↦ add (f x y) (g x y)) u v := by
  refine ⟨?_, HasDerivAt.add hf.2.1 hg.2.1, HasDerivAt.add hf.2.2 hg.2.2⟩
  filter_upwards [hf.1, hg.1] with y hfy hgy
  exact HasDerivAt.add hfy hgy

theorem IsAt.sub {f g : ℝ → ℝ → MixedJet ℝ} {u v : ℝ}
    (hf : IsAt f u v) (hg : IsAt g u v) : IsAt (fun x y ↦ sub (f x y) (g x y)) u v := by
  refine ⟨?_, HasDerivAt.sub hf.2.1 hg.2.1, HasDerivAt.sub hf.2.2 hg.2.2⟩
  filter_upwards [hf.1, hg.1] with y hfy hgy
  exact HasDerivAt.sub hfy hgy

theorem IsAt.mul {f g : ℝ → ℝ → MixedJet ℝ} {u v : ℝ}
    (hf : IsAt f u v) (hg : IsAt g u v) : IsAt (fun x y ↦ mul (f x y) (g x y)) u v := by
  refine ⟨?_, hf.2.1.mul hg.2.1, ?_⟩
  · filter_upwards [hf.1, hg.1] with y hfy hgy
    exact hfy.mul hgy
  · have hleft := hf.2.2.mul hg.2.1
    have hright := hf.2.1.mul hg.2.2
    have hs := HasDerivAt.add hleft hright
    convert hs using 1
    · funext y
      rfl
    · change _ + _ + _ + _ = (_ + _) + (_ + _)
      ring

private theorem hasDerivAt_reciprocal {g : ℝ → ℝ} {a x : ℝ}
    (hg : HasDerivAt g a x) (h : g x ≠ 0) :
    HasDerivAt (fun y ↦ 1 / g y) (-((1 / g x) * (1 / g x) * a)) x := by
  convert HasDerivAt.inv hg h using 1
  · funext y
    change 1 / g y = (g y)⁻¹
    exact one_div _
  · field_simp

theorem IsAt.reciprocal {f : ℝ → ℝ → MixedJet ℝ} {u v : ℝ}
    (hf : IsAt f u v) (h : (f u v).value ≠ 0) :
    IsAt (fun x y ↦ reciprocal (f x y)) u v := by
  have hv := hasDerivAt_reciprocal hf.2.1 h
  refine ⟨?_, hv, ?_⟩
  · have hnear : ∀ᶠ y in 𝓝 v, (f u y).value ≠ 0 :=
      hf.2.1.continuousAt.eventually_ne h
    filter_upwards [hf.1, hnear] with y hy hny
    exact hasDerivAt_reciprocal hy hny
  · have hm := HasDerivAt.neg ((hv.mul hv).mul hf.2.2)
    convert hm using 1
    · funext y
      rfl
    · change (1 / (f u v).value) * (1 / (f u v).value) *
        (2 * (1 / (f u v).value) * (f u v).du * (f u v).dv - (f u v).duv) = _
      dsimp only [Pi.mul_apply]
      ring

theorem IsAt.sqrtFrom {f : ℝ → ℝ → MixedJet ℝ} {u v : ℝ}
    (hf : IsAt f u v) (h : 0 < (f u v).value) :
    IsAt (fun x y ↦ sqrtFrom (f x y) (Real.sqrt (f x y).value)) u v := by
  have hr := hf.2.1.sqrt h.ne'
  have hroot := (Real.sqrt_pos.2 h).ne'
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hf.1, hf.2.1.continuousAt.tendsto.eventually (eventually_gt_nhds h)]
      with y hy hpy
    simpa only [MixedJet.sqrtFrom, div_eq_mul_inv, one_mul, mul_comm] using hy.sqrt hpy.ne'
  · simpa only [MixedJet.sqrtFrom, div_eq_mul_inv, one_mul, mul_comm] using hr
  · have hq := hasDerivAt_reciprocal (hr.const_mul 2) (mul_ne_zero (by norm_num) hroot)
    have hm := hq.mul hf.2.2
    have hm' : HasDerivAt (fun y ↦ (1 / (2 * Real.sqrt (f u y).value)) * (f u y).du)
        _ v := hm
    convert hm' using 1
    · funext y
      rfl
    · change (1 / (2 * Real.sqrt (f u v).value)) * (f u v).duv -
        (1 / (2 * Real.sqrt (f u v).value)) * (1 / (2 * Real.sqrt (f u v).value)) *
          (1 / Real.sqrt (f u v).value) * (f u v).du * (f u v).dv = _
      field_simp [hroot] <;> ring

#print axioms IsAt.mul
#print axioms IsAt.reciprocal
#print axioms IsAt.sqrtFrom

end MixedJet

end RefinedBMV.PositiveCenter
