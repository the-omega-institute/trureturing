/- GID: D5/S3/MeasureTheory/BoundedRing
   generality: G
   mirror-B: none(waiver:covered-by-observer-crossed-product-entropy-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Essentially bounded almost-everywhere classes form a ring. -/

import OmegaBuild.Commands
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Omega original.

Essentially bounded almost-everywhere classes form a ring. An idempotent in that
ring determines a corner with the idempotent as its multiplicative identity.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Omega.MeasureTheory.BoundedRing

open _root_.MeasureTheory

variable {X R : Type*} [MeasurableSpace X] [NormedRing R] {μ : Measure X}

@[reducible] scoped instance : NatCast (X →ₘ[μ] R) := ⟨fun k => AEEqFun.const X k⟩
@[reducible] scoped instance : IntCast (X →ₘ[μ] R) := ⟨fun k => AEEqFun.const X k⟩

@[reducible] scoped instance : Ring (X →ₘ[μ] R) :=
  AEEqFun.toGerm_injective.ring _ AEEqFun.zero_toGerm AEEqFun.one_toGerm
    AEEqFun.add_toGerm AEEqFun.mul_toGerm AEEqFun.neg_toGerm AEEqFun.sub_toGerm
    AEEqFun.smul_toGerm AEEqFun.smul_toGerm AEEqFun.pow_toGerm (fun _ => rfl) (fun _ => rfl)

/-- The ring of essentially bounded measurable classes. -/
def boundedSubring : Subring (X →ₘ[μ] R) where
  carrier := {A | ∃ C : ℝ, ∀ᵐ y ∂μ, ‖A y‖ ≤ C}
  zero_mem' := ⟨0, AEEqFun.coeFn_zero.mono fun y h => by
    change ‖(0 : X →ₘ[μ] R) y‖ ≤ 0
    rw [h]
    simp⟩
  one_mem' := ⟨‖(1 : R)‖, AEEqFun.coeFn_one.mono fun y h => by
    change ‖(1 : X →ₘ[μ] R) y‖ ≤ _
    rw [h]
    exact le_rfl⟩
  add_mem' {A B} := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    filter_upwards [ha, hb, AEEqFun.coeFn_add A B] with y hA hB h
    change ‖(A + B) y‖ ≤ a + b
    rw [h, Pi.add_apply]
    exact (norm_add_le (A y) (B y)).trans (add_le_add hA hB)
  neg_mem' {A} := by
    rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    filter_upwards [ha, AEEqFun.coeFn_neg A] with y hA h
    change ‖(-A) y‖ ≤ a
    simpa [h] using hA
  mul_mem' {A B} := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨max a 0 * max b 0, ?_⟩
    filter_upwards [ha, hb, AEEqFun.coeFn_mul A B] with y hA hB h
    change ‖(A * B) y‖ ≤ max a 0 * max b 0
    rw [h, Pi.mul_apply]
    exact (norm_mul_le _ _).trans (mul_le_mul (hA.trans (le_max_left ..))
      (hB.trans (le_max_left ..)) (norm_nonneg _) (le_max_right ..))

variable {S : Type*} [Ring S]

/-- The subring fixed by multiplying by the same element on either side. -/
def corner (e : S) : NonUnitalSubring S where
  carrier := {a | e * a = a ∧ a * e = a}
  zero_mem' := by simp
  add_mem' {_ _} ha hb := by simp only [Set.mem_ofPred_eq, mul_add, add_mul,
    ha.1, ha.2, hb.1, hb.2, and_self]
  neg_mem' {_} ha := by simp only [Set.mem_ofPred_eq, mul_neg, neg_mul, ha.1, ha.2, and_self]
  mul_mem' {_ _} ha hb :=
    ⟨by rw [← mul_assoc, ha.1], by rw [mul_assoc, hb.2]⟩

/-- For idempotent e, two-sided compression fixes exactly the corner. -/
theorem mem_corner_iff {e : S} (he : e * e = e) (a : S) :
    a ∈ corner e ↔ e * a * e = a := by
  constructor
  · rintro ⟨h₁, h₂⟩
    rw [h₁, h₂]
  · intro h
    constructor
    · calc
        e * a = e * (e * a * e) := by rw [h]
        _ = a := by rw [← mul_assoc, ← mul_assoc, he, h]
    · calc
        a * e = (e * a * e) * e := by rw [h]
        _ = a := by rw [mul_assoc, he, h]

/-- The distinguished element of an idempotent corner. -/
def cornerUnit {e : S} (he : e * e = e) : corner e := ⟨e, he, he⟩

/-- A weighted linear observable of a bounded field is integrable when the weight
is integrable on the measurable support of the field. -/
theorem integrable_weighted_linear [NormedSpace ℂ R] (A : X →ₘ[μ] R)
    (hA : A ∈ boundedSubring) (L : R →L[ℂ] ℂ) {s : Set X} (hs : MeasurableSet s)
    {w : X → ℝ} (hw : Measurable w) (hw₀ : ∀ x, 0 ≤ w x) (hwi : IntegrableOn w s μ)
    (hAs : ∀ᵐ x ∂μ, x ∉ s → A x = 0) :
    Integrable (fun x => (w x : ℂ) * L (A x)) μ := by
  obtain ⟨C, hC⟩ := hA
  let bound := fun x => ‖L‖ * max C 0 * w x
  have hb : IntegrableOn bound s μ := hwi.const_mul _
  have hm := (Complex.continuous_ofReal.comp_aestronglyMeasurable hw.aestronglyMeasurable).mul
    (L.continuous.comp_aestronglyMeasurable A.aestronglyMeasurable)
  refine (hb.integrable_indicator hs).mono' hm ?_
  filter_upwards [hC, hAs] with x hx hzero
  by_cases h : x ∈ s
  · rw [Set.indicator_of_mem h, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw₀ x)]
    have hnorm := (L.le_opNorm (A x)).trans
      (mul_le_mul_of_nonneg_left (hx.trans (le_max_left C 0)) (norm_nonneg L))
    exact (mul_le_mul_of_nonneg_left hnorm (hw₀ x)).trans_eq (mul_comm ..)
  · simp [h, hzero h]

end Omega.MeasureTheory.BoundedRing
