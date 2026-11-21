/- GID: D5/S3/Analytic/Probability/UniformFiberCoupling
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/UniformFiberCoupling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every probability law on a homomorphism fiber is the displacement law of a coupling of uniform fibers. -/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

open Finset
open scoped Classical

noncomputable section

namespace D5.S3.Analytic.Probability.UniformFiberCoupling

variable {G H : Type*} [Group G] [Group H]

abbrev Fiber (φ : G →* H) (t : H) := {x : G // φ x = t}

private def leftTranslate (φ : G →* H) {t : H} (x : Fiber φ 1) : Fiber φ t ≃ Fiber φ t where
  toFun y := ⟨x.val⁻¹ * y.val, by simp [x.property, y.property]⟩
  invFun d := ⟨x.val * d.val, by simp [x.property, d.property]⟩
  left_inv y := Subtype.ext (by simp)
  right_inv d := Subtype.ext (by simp)

private def rightTranslate (φ : G →* H) {t : H} (y : Fiber φ t) : Fiber φ 1 ≃ Fiber φ t where
  toFun x := ⟨x.val⁻¹ * y.val, by simp [x.property, y.property]⟩
  invFun d := ⟨y.val * d.val⁻¹, by simp [y.property, d.property]⟩
  left_inv x := Subtype.ext (by simp)
  right_inv d := Subtype.ext (by simp [mul_assoc])

scoped instance fiberFintype (φ : G →* H) (t : H) [Finite (Fiber φ 1)] :
    Fintype (Fiber φ t) :=
  if inhabited : Nonempty (Fiber φ t) then
    letI := Fintype.ofFinite (Fiber φ 1)
    Fintype.ofEquiv (Fiber φ 1) (rightTranslate φ (Classical.choice inhabited))
  else
    letI : IsEmpty (Fiber φ t) := ⟨fun x => inhabited ⟨x⟩⟩
    Fintype.ofIsEmpty

private theorem card_left_pos (φ : G →* H) [Finite (Fiber φ 1)] : (0 : ℝ) < Fintype.card (Fiber φ 1) := by
  let instanceValue : Nonempty (Fiber φ 1) := ⟨⟨1, φ.map_one⟩⟩
  exact_mod_cast Fintype.card_pos

def displacement (φ : G →* H) (t : H) [Finite (Fiber φ 1)]
    (w : Fiber φ 1 → Fiber φ t → ℝ) (d : Fiber φ t) : ℝ :=
  ∑ x, ∑ y, if leftTranslate φ x y = d then w x y else 0

/-- The law of the displacement between the two uniform fibers may be any law on the target fiber. -/
theorem displacement_iff (φ : G →* H) (t : H) [Finite (Fiber φ 1)]
    (ρ : Fiber φ t → ℝ) :
    ((∀ d, 0 ≤ ρ d) ∧ ∑ d, ρ d = 1) ↔
    ∃ w : Fiber φ 1 → Fiber φ t → ℝ,
      (∀ x y, 0 ≤ w x y) ∧
      (∀ x, ∑ y, w x y = 1 / (Fintype.card (Fiber φ 1) : ℝ)) ∧
      (∀ y, ∑ x, w x y = 1 / (Fintype.card (Fiber φ t) : ℝ)) ∧
      displacement φ t w = ρ := by
  let C : ℝ := Fintype.card (Fiber φ 1)
  have Cpos : 0 < C := card_left_pos φ
  constructor
  · rintro ⟨hρ, total⟩
    let w (x : Fiber φ 1) (y : Fiber φ t) := ρ (leftTranslate φ x y) / C
    refine ⟨w, fun x y => div_nonneg (hρ _) Cpos.le, ?_, ?_, ?_⟩
    · intro x
      rw [show (∑ y, w x y) = (∑ y, ρ (leftTranslate φ x y)) / C by simp only [w, sum_div],
        (leftTranslate φ x).sum_comp ρ, total]
    · intro y
      have count_eq := Fintype.card_congr (rightTranslate φ y)
      simp only [w, ← sum_div]
      change (∑ x, ρ (rightTranslate φ y x)) / C = _
      rw [(rightTranslate φ y).sum_comp ρ, total, ← count_eq]
    · funext d
      unfold displacement
      have inner (x : Fiber φ 1) :
          (∑ y, if leftTranslate φ x y = d then w x y else 0) = ρ d / C := by
        calc
          _ = ∑ a : Fiber φ t, (if a = d then ρ a / C else 0) :=
            (leftTranslate φ x).sum_comp (fun a => if a = d then ρ a / C else 0)
          _ = _ := by simp
      simp_rw [inner]
      simp only [sum_const, card_univ, nsmul_eq_mul]
      change C * (ρ d / C) = ρ d
      field_simp
  · rintro ⟨w, wn, wleft, _, rfl⟩
    constructor
    · intro d
      exact sum_nonneg fun x _ => sum_nonneg fun y _ => by split <;> simp [wn]
    · unfold displacement
      rw [sum_comm]
      have inner (x : Fiber φ 1) :
          (∑ d : Fiber φ t, ∑ y : Fiber φ t,
            if leftTranslate φ x y = d then w x y else 0) = 1 / C := by
        rw [sum_comm]
        simp only [sum_ite_eq, mem_univ, ite_true]
        exact wleft x
      simp_rw [inner]
      simp only [sum_const, card_univ, nsmul_eq_mul]
      change C * (1 / C) = 1
      field_simp

end D5.S3.Analytic.Probability.UniformFiberCoupling
