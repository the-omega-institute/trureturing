/- GID: D5/S3/Resource/HorizonPermutationCost
   generality: G
   mirror-B: D5/B/S3/Resource/HorizonPermutationCost
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact state cost for finite-horizon initialized permutation simulation. -/

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
  apply Function.LeftInverse.injective (g := readout)
  intro x
  simpa using hs x 0 (Nat.zero_le _)

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
          exact congrArg Sum.inr (Prod.ext hl hf)
        · obtain ⟨htime, hleaf⟩ := leaf_collision hs b.1 a.1 b.2.val a.2.val
            (by omega) (by have := a.2.isLt; omega) hab.symm
          have hl : a.1 = b.1 := Subtype.ext hleaf.symm
          have hf : a.2 = b.2 := Fin.ext htime.symm
          exact congrArg Sum.inr (Prod.ext hl hf)
  simpa [Nat.card_sum, Nat.card_prod, Nat.card_fin, Nat.mul_comm] using
    Nat.card_le_card_of_injective embed hinj

/-- A permutation completing one selected predecessor of each image point. -/
private theorem predecessor_permutation {X : Type u} [Finite X] (f : X → X) :
    ∃ q : Equiv.Perm X, ∀ x, q x ∈ Set.range f → q x = f x := by
  classical
  obtain ⟨q, hq⟩ := Equiv.Perm.exists_extending_pair (Set.rangeSplitting f)
    Subtype.val (Set.rangeSplitting_injective f) Subtype.val_injective
  refine ⟨q, ?_⟩
  intro x hx
  let y : Set.range f := ⟨q x, hx⟩
  have hpx : Set.rangeSplitting f y = x := q.injective (hq y)
  exact (Set.apply_rangeSplitting f y).symm.trans (congrArg f hpx)

section Delay

variable {X : Type u} (f : X → X) (H : ℕ) (hH : 0 < H) (q : Equiv.Perm X)

local notation "Leaves" => {x : X // x ∉ Set.range f}
local notation "States" => X ⊕ (Leaves × Fin H)

/-- Subdivide every edge of q entering a missing-image point by H states. -/
private noncomputable def delayNext : States → States := by
  classical
  exact Sum.elim
    (fun x => if h : q x ∉ Set.range f then Sum.inr (⟨q x, h⟩, ⟨0, hH⟩)
      else Sum.inl (q x))
    (fun a => if h : a.2.val + 1 < H then Sum.inr (a.1, ⟨a.2.val + 1, h⟩)
      else Sum.inl a.1.val)

/-- The predecessor of an original leaf is the last added state; zero delay
positions have the original terminal as predecessor. -/
private noncomputable def delayPrev : States → States := by
  classical
  exact Sum.elim
    (fun x => if h : x ∉ Set.range f then Sum.inr (⟨x, h⟩, ⟨H - 1, by omega⟩)
      else Sum.inl (q.symm x))
    (fun a => if h : a.2.val = 0 then Sum.inl (q.symm a.1.val)
      else Sum.inr (a.1, ⟨a.2.val - 1, by have := a.2.isLt; omega⟩))

private theorem delay_left_inverse :
    Function.LeftInverse (delayPrev f H hH q) (delayNext f H hH q) := by
  classical
  intro e
  cases e with
  | inl x =>
    by_cases hx : q x ∉ Set.range f
    · simp only [delayNext, Sum.elim_inl, dif_pos hx, delayPrev, Sum.elim_inr,
        dite_true, Equiv.symm_apply_apply]
    · simp only [delayNext, Sum.elim_inl, delayPrev, Sum.elim_inl,
        dif_neg hx, Equiv.symm_apply_apply]
  | inr a =>
    by_cases hj : a.2.val + 1 < H
    · simp only [delayNext, Sum.elim_inr, dif_pos hj, delayPrev, Sum.elim_inr,
        ]
      rw [dif_neg (by omega : ¬ a.2.val + 1 = 0)]
      exact congrArg Sum.inr (Prod.ext rfl (Fin.ext (Nat.add_sub_cancel a.2.val 1)))
    · simp only [delayNext, Sum.elim_inr, dif_neg hj, delayPrev, Sum.elim_inl,
        dif_pos a.1.property]
      apply congrArg Sum.inr
      apply Prod.ext
      · rfl
      · apply Fin.ext
        change H - 1 = a.2.val
        have := a.2.isLt
        omega

private theorem delay_right_inverse :
    Function.RightInverse (delayPrev f H hH q) (delayNext f H hH q) := by
  classical
  intro e
  cases e with
  | inl x =>
    by_cases hx : x ∉ Set.range f
    · simp only [delayPrev, Sum.elim_inl, dif_pos hx, delayNext, Sum.elim_inr,
        ]
      rw [dif_neg (by omega : ¬ H - 1 + 1 < H)]
    · simp only [delayPrev, Sum.elim_inl, delayNext, Sum.elim_inl,
        Equiv.apply_symm_apply, dif_neg hx]
  | inr a =>
    by_cases hj : a.2.val = 0
    · simp only [delayPrev, Sum.elim_inr, dif_pos hj, delayNext, Sum.elim_inl,
        Equiv.apply_symm_apply, dif_pos a.1.property]
      apply congrArg Sum.inr
      exact Prod.ext rfl (Fin.ext hj.symm)
    · simp only [delayPrev, Sum.elim_inr, dif_neg hj, delayNext, Sum.elim_inr,
        ]
      rw [dif_pos (by have := a.2.isLt; omega : a.2.val - 1 + 1 < H)]
      apply congrArg Sum.inr
      apply Prod.ext
      · rfl
      · apply Fin.ext
        change a.2.val - 1 + 1 = a.2.val
        omega

private noncomputable def delayPerm : Equiv.Perm States where
  toFun := delayNext f H hH q
  invFun := delayPrev f H hH q
  left_inv := delay_left_inverse f H hH q
  right_inv := delay_right_inverse f H hH q

/-- Added states read the forward orbit of the terminal whose edge was cut. -/
private def delayReadout : States → X :=
  Sum.elim id (fun a => f^[a.2.val + 1] (q.symm a.1.val))

/-- The number of added states traversed since leaving an original terminal. -/
private def delayAge : States → ℕ :=
  Sum.elim (fun _ => 0) (fun a => a.2.val + 1)

private theorem delay_step
    (hq : ∀ x, q x ∈ Set.range f → q x = f x)
    (e : States) (he : delayAge f H e < H) :
    delayReadout f H q (delayPerm f H hH q e) = f (delayReadout f H q e) ∧
      delayAge f H (delayPerm f H hH q e) ≤ delayAge f H e + 1 := by
  classical
  cases e with
  | inl x =>
    by_cases hx : q x ∉ Set.range f
    · simp only [delayPerm, Equiv.coe_fn_mk, delayNext, Sum.elim_inl, dif_pos hx,
        delayReadout, Sum.elim_inr, Equiv.symm_apply_apply,
        zero_add, Function.iterate_one, id_eq, delayAge, le_refl, and_self]
    · have hqx : q x = f x := hq x (not_not.mp hx)
      simp only [delayPerm, Equiv.coe_fn_mk, delayNext, Sum.elim_inl, dif_neg hx,
        delayReadout, id_eq, delayAge, zero_add]
      exact ⟨hqx, Nat.zero_le _⟩
  | inr a =>
    have hj : a.2.val + 1 < H := he
    simp only [delayPerm, Equiv.coe_fn_mk, delayNext, Sum.elim_inr, dif_pos hj,
      delayReadout, delayAge]
    exact ⟨Function.iterate_succ_apply' f (a.2.val + 1) (q.symm a.1.val), le_refl _⟩

private theorem delay_simulates
    (hq : ∀ x, q x ∈ Set.range f → q x = f x) :
    IsSimulation f H (delayPerm f H hH q) (delayReadout f H q) Sum.inl := by
  intro x t ht
  have trajectory : ∀ n, n ≤ H →
      delayReadout f H q ((delayPerm f H hH q : States → States)^[n] (Sum.inl x)) =
        f^[n] x ∧
      delayAge f H ((delayPerm f H hH q : States → States)^[n] (Sum.inl x)) ≤ n := by
    intro n
    induction n with
    | zero =>
      intro _
      simp only [Function.iterate_zero_apply, delayReadout, delayAge, Sum.elim_inl,
        id_eq, le_refl, and_self]
    | succ n ih =>
      intro hn
      obtain ⟨hr, ha⟩ := ih (by omega)
      have step := delay_step f H hH q hq
        ((delayPerm f H hH q : States → States)^[n] (Sum.inl x)) (by omega)
      rw [Function.iterate_succ_apply']
      constructor
      · rw [step.1, hr, Function.iterate_succ_apply']
      · exact le_trans step.2 (Nat.add_le_add_right ha 1)
  exact (trajectory t ht).1

end Delay

/-- Every finite initialized permutation simulation obeys the state lower bound,
and a finite simulation attains it, including the empty source and zero horizon. -/
theorem result {X : Type u} [Finite X] (f : X → X) (H : ℕ) :
    (∀ (E : Type v) (_ : Finite E) (P : Equiv.Perm E)
      (readout : E → X) (init : X → E),
      IsSimulation f H P readout init →
        Nat.card X + H * Nat.card {x : X // x ∉ Set.range f} ≤ Nat.card E) ∧
    (∃ (E : Type u) (_ : Finite E) (P : Equiv.Perm E)
      (readout : E → X) (init : X → E),
      IsSimulation f H P readout init ∧
        Nat.card E = Nat.card X + H * Nat.card {x : X // x ∉ Set.range f}) := by
  constructor
  · intro E hE P readout init hs
    have : Finite E := hE
    exact lower_bound f H P readout init hs
  · cases H with
    | zero =>
      refine ⟨X, inferInstance, Equiv.refl X, id, id, ?_, ?_⟩
      · intro x t ht
        have ht0 : t = 0 := by omega
        subst t
        rfl
      · simp
    | succ n =>
      obtain ⟨q, hq⟩ := predecessor_permutation f
      let E := X ⊕ ({x : X // x ∉ Set.range f} × Fin (n + 1))
      refine ⟨E, inferInstance, delayPerm f (n + 1) (by omega) q,
        delayReadout f (n + 1) q, Sum.inl,
        delay_simulates f (n + 1) (by omega) q hq, ?_⟩
      simp only [E, Nat.card_sum, Nat.card_prod, Nat.card_fin, Nat.mul_comm]

end D5.S3.Resource.HorizonPermutationCost
