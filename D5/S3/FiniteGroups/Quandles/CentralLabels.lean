/- GID: D5/S3/FiniteGroups/Quandles/CentralLabels
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Quandles/CentralLabels
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Central-label classification of all good involutions of a whole-group conjugation quandle. -/

import D5.S3.FiniteGroups.Quandles.ConjugationSubquandle
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Tactic.Group

/-! The central-label classification is the whole-group specialization of
Ta, arXiv:2505.08090v5, Theorem 6.7. All auxiliary declarations below
are consumed by the complete three-invariant refutation. -/

namespace D5.S3.FiniteGroups.Quandles.CentralLabels

variable {G : Type*} [Group G]

/-- Ta's pointwise definition, with the inverse conjugation written explicitly. -/
def IsGood (ρ : G → G) : Prop :=
  Function.Involutive ρ ∧
  (∀ g x, ρ (g * x * g⁻¹) = g * ρ x * g⁻¹) ∧
  ∀ x y, ρ x * y * (ρ x)⁻¹ = x⁻¹ * y * x

/-- Good maps, counted as functions, without quotienting by isomorphism. -/
def Good (G : Type*) [Group G] := {ρ : G → G // IsGood ρ}

private theorem central_twist_iff (a b : G) :
    a * b ∈ Subgroup.center G ↔ ∀ y, a * y * a⁻¹ = b⁻¹ * y * b := by
  constructor
  · intro h y
    have hcomm := Subgroup.mem_center_iff.mp h (b⁻¹ * y * b)
    calc
      a * y * a⁻¹ = (a * b) * (b⁻¹ * y * b) * (a * b)⁻¹ := by group
      _ = b⁻¹ * y * b := by rw [← hcomm]; group
  · intro h
    apply Subgroup.mem_center_iff.mpr
    intro y
    have he : (a * b) * y * (a * b)⁻¹ = y := by
      calc
        _ = a * (b * y * b⁻¹) * a⁻¹ := by group
        _ = b⁻¹ * (b * y * b⁻¹) * b := h _
        _ = y := by group
    exact ((mul_inv_eq_iff_eq_mul).mp he).symm

/-- Class-invariant central labels with exactly the compatibility needed for
squaring the associated twisted inversion to the identity. -/
def Label (G : Type*) [Group G] :=
  {z : G → Subgroup.center G //
    (∀ g x, z (g * x * g⁻¹) = z x) ∧
    ∀ x, z ((z x : G) * x⁻¹) = z x}

/-- The complete central-label bijection; this is not a count of a chosen family. -/
def goodLabelEquiv : Good G ≃ Label G where
  toFun ρ := by
    let z : G → Subgroup.center G := fun x =>
      ⟨ρ.val x * x, (central_twist_iff _ _).mpr (ρ.property.2.2 x)⟩
    refine ⟨z, ?_, ?_⟩
    · intro g x
      apply Subtype.ext
      change ρ.val (g * x * g⁻¹) * (g * x * g⁻¹) = ρ.val x * x
      rw [ρ.property.2.1]
      calc
        _ = g * (ρ.val x * x) * g⁻¹ := by group
        _ = ρ.val x * x := by
          have hc : g * (ρ.val x * x) = (ρ.val x * x) * g :=
            Subgroup.mem_center_iff.mp (z x).property g
          rw [hc]
          group
    · intro x
      apply Subtype.ext
      change ρ.val ((ρ.val x * x) * x⁻¹) * ((ρ.val x * x) * x⁻¹) = ρ.val x * x
      simp only [mul_inv_cancel_right, ρ.property.1 x]
      have h := ρ.property.2.2 x x
      have hc : ρ.val x * x = x * ρ.val x := by
        apply (mul_inv_eq_iff_eq_mul).mp
        simpa [mul_assoc] using h
      exact hc.symm
  invFun z := by
    let ρ : G → G := fun x => (z.val x : G) * x⁻¹
    refine ⟨ρ, ?_, ?_, ?_⟩
    · intro x
      change (z.val ((z.val x : G) * x⁻¹) : G) * ((z.val x : G) * x⁻¹)⁻¹ = x
      rw [z.property.2]
      have hc := Subgroup.mem_center_iff.mp (z.val x).property x
      simp only [mul_inv_rev, inv_inv]
      rw [← mul_assoc, ← hc]
      simp
    · intro g x
      change (z.val (g * x * g⁻¹) : G) * (g * x * g⁻¹)⁻¹ =
        g * ((z.val x : G) * x⁻¹) * g⁻¹
      rw [z.property.1]
      have hc := Subgroup.mem_center_iff.mp (z.val x).property g
      simp only [mul_inv_rev, inv_inv]
      calc
        _ = ((z.val x : G) * g) * x⁻¹ * g⁻¹ := by group
        _ = (g * (z.val x : G)) * x⁻¹ * g⁻¹ := by rw [hc]
        _ = _ := by group
    · intro x
      apply (central_twist_iff _ _).mp
      simpa only [ρ, inv_mul_cancel_right] using (z.val x).property
  left_inv ρ := by
    apply Subtype.ext
    funext x
    exact mul_inv_cancel_right _ _
  right_inv z := by
    apply Subtype.ext
    funext x
    apply Subtype.ext
    exact inv_mul_cancel_right _ _

/-- Reuse the repository's subquandle definition on the entire carrier. -/
def wholeGoodEquiv [Fintype G] [DecidableEq G] :
    Good G ≃ D5.S3.FiniteGroups.Quandles.ConjugationSubquandle.Good
      (Finset.univ : Finset G) (by intro x hx y hy; exact Finset.mem_univ _) where
  toFun ρ := by
    refine ⟨fun x => ⟨ρ.val x.val, Finset.mem_univ _⟩, ?_, ?_⟩
    · intro x
      apply Subtype.ext
      exact ρ.property.1 x.val
    · intro x
      refine ⟨?_, ?_, ?_⟩
      · funext y
        apply Subtype.ext
        exact ρ.property.2.1 x.val y.val
      · intro y
        apply Subtype.ext
        change ρ.val x.val * (x.val * y.val * x.val⁻¹) * (ρ.val x.val)⁻¹ = y.val
        rw [ρ.property.2.2]
        group
      · intro y
        apply Subtype.ext
        change x.val * (ρ.val x.val * y.val * (ρ.val x.val)⁻¹) * x.val⁻¹ = y.val
        rw [ρ.property.2.2]
        group
  invFun ρ := by
    let f : G → G := fun x => (ρ.val ⟨x, Finset.mem_univ _⟩).val
    refine ⟨f, ?_, ?_, ?_⟩
    · intro x
      exact congrArg Subtype.val (ρ.property.1 ⟨x, Finset.mem_univ _⟩)
    · intro g x
      exact congrArg Subtype.val (congrFun (ρ.property.2 ⟨g, Finset.mem_univ _⟩).1
        ⟨x, Finset.mem_univ _⟩)
    · intro x y
      have h := congrArg Subtype.val ((ρ.property.2 ⟨x, Finset.mem_univ _⟩).2.1
        ⟨x⁻¹ * y * x, Finset.mem_univ _⟩)
      change f x * (x * (x⁻¹ * y * x) * x⁻¹) * (f x)⁻¹ = x⁻¹ * y * x at h
      simpa [mul_assoc] using h
  left_inv ρ := by apply Subtype.ext; rfl
  right_inv ρ := by apply Subtype.ext; rfl

end D5.S3.FiniteGroups.Quandles.CentralLabels
