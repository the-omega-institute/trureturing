/- GID: D5/S3/Resource/HorizonPermutationCost
   generality: G
   mirror-B: D5/B/S3/Resource/HorizonPermutationCost
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite initialized permutation simulation has exact minimum state cost equal to the source size plus horizon times missing-image size. -/

import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Function.Iterate
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Resource.HorizonPermutationCost

universe u v

/-- A fixed, total readout reproduces the source dynamics for every initialized
state through the specified horizon. No law is imposed on other trajectories. -/
def IsSimulation {X : Type u} {E : Type v} (f : X → X) (H : ℕ)
    (P : Equiv.Perm E) (readout : E → X) (init : X → E) : Prop :=
  ∀ x t, t ≤ H → readout ((P : E → E)^[t] (init x)) = f^[t] x

private theorem init_injective {X : Type u} {E : Type v}
    {f : X → X} {H : ℕ} {P : Equiv.Perm E} {readout : E → X} {init : X → E}
    (hs : IsSimulation f H P readout init) : Function.Injective init := by
  intro x y h
  have hx := hs x 0 (Nat.zero_le _)
  have hy := hs y 0 (Nat.zero_le _)
  simpa using hx.symm.trans ((congrArg readout h).trans hy)

/-- Cancelling the earlier time exposes a forbidden predecessor of a leaf. -/
private theorem leaf_collision {X : Type u} {E : Type v}
    {f : X → X} {H : ℕ} {P : Equiv.Perm E} {readout : E → X} {init : X → E}
    (hs : IsSimulation f H P readout init)
    (l : {x : X // x ∉ Set.range f}) (x : X) (t s : ℕ)
    (hts : t ≤ s) (hsH : s ≤ H)
    (heq : (P : E → E)^[t] (init l) = (P : E → E)^[s] (init x)) :
    t = s ∧ (l : X) = x := by
  have hc : init l = (P : E → E)^[s - t] (init x) := by
    apply P.injective.iterate t
    rw [← Function.iterate_add_apply]
    simpa [Nat.add_sub_of_le hts] using heq
  have hr : (l : X) = f^[s - t] x := by
    have h0 := hs l 0 (Nat.zero_le _)
    have hd := hs x (s - t) (by omega)
    simpa using h0.symm.trans ((congrArg readout hc).trans hd)
  have hst : s - t = 0 := by
    by_contra hn
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
    apply l.property
    refine ⟨f^[k] x, ?_⟩
    simpa [hk, Function.iterate_succ_apply'] using hr.symm
  constructor
  · omega
  · simpa [hst] using hr

private theorem lower_bound {X : Type u} {E : Type v} [Finite X] [Finite E]
    (f : X → X) (H : ℕ) (P : Equiv.Perm E) (readout : E → X) (init : X → E)
    (hs : IsSimulation f H P readout init) :
    Nat.card X + H * Nat.card {x : X // x ∉ Set.range f} ≤ Nat.card E := by
  classical
  let embed : X ⊕ ({x : X // x ∉ Set.range f} × Fin H) → E :=
    Sum.elim (fun x => (P : E → E)^[H] (init x))
      (fun a => (P : E → E)^[a.2.val] (init a.1))
  have hinj : Function.Injective embed := by
    intro a b hab
    cases a with
    | inl x =>
      cases b with
      | inl y =>
        exact congrArg Sum.inl (init_injective hs (P.injective.iterate H hab))
      | inr a =>
        have h := leaf_collision hs a.1 x a.2.val H (by omega) (le_refl _) hab.symm
        exact False.elim (by have := a.2.isLt; omega)
    | inr a =>
      cases b with
      | inl x =>
        have h := leaf_collision hs a.1 x a.2.val H (by omega) (le_refl _) hab
        exact False.elim (by have := a.2.isLt; omega)
      | inr b =>
        by_cases ht : a.2.val ≤ b.2.val
        · obtain ⟨htime, hleaf⟩ := leaf_collision hs a.1 b.1 a.2.val b.2.val
            ht (by have := b.2.isLt; omega) hab
          have hl : a.1 = b.1 := Subtype.ext hleaf
          have hf : a.2 = b.2 := Fin.ext htime
          simp [hl, hf]
        · obtain ⟨htime, hleaf⟩ := leaf_collision hs b.1 a.1 b.2.val a.2.val
            (by omega) (by have := a.2.isLt; omega) hab.symm
          have hl : a.1 = b.1 := Subtype.ext hleaf.symm
          have hf : a.2 = b.2 := Fin.ext htime.symm
          simp [hl, hf]
  simpa [Nat.card_sum, Nat.card_prod, Nat.card_fin, Nat.mul_comm] using
    Nat.card_le_card_of_injective embed hinj

end D5.S3.Resource.HorizonPermutationCost
