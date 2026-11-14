/- GID: D5/S3/Combinatorics/Graph/LinearForests/CompatibleCycleInventory
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LinearForests/CompatibleCycleInventory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Option]
   utility: none
   digest: Exhaustive insertion and two-state inventories of labelled compatible cycles. -/

import D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion
import D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch
import Mathlib.GroupTheory.Perm.Option
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

/-! Label-preserving insertion on the actual permutation carrier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Graph.LinearForests.CompatibleCycleInventory
open Equiv
open D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing
open D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch (same_cycle_perm_congr)
attribute [local instance] Classical.propDecidable

universe u v
variable {C : Type u} {A : Type v}

/-- Actual nonempty single cycles obeying the prescribed labelled transitions. -/
abbrev Compatible (s d : C → Bool) :=
  {ρ : Perm C // Nonempty C ∧ ρ.IsCycleOn Set.univ ∧ ∀ x, d x = s (ρ x)}

private def insertLabel [DecidableEq A] (ρ : Perm A) (y : A) : Perm (Option A) :=
  swap none (some y) * ρ.optionCongr

private theorem insert_none [DecidableEq A] (ρ : Perm A) (y : A) :
    insertLabel ρ y none = some y := by simp [insertLabel]

private theorem insert_some [DecidableEq A] (ρ : Perm A) (y x : A) :
    insertLabel ρ y (some x) = if ρ x = y then none else some (ρ x) := by
  by_cases h : ρ x = y <;> simp [insertLabel, h, swap_apply_def]

private theorem insert_cycle_iff [Finite A] [DecidableEq A] (ρ : Perm A) (y : A) :
    (insertLabel ρ y).IsCycleOn Set.univ ↔ ρ.IsCycleOn Set.univ := by
  let g := insertLabel ρ y
  let S : Set (Option A) := Set.range (some : A → Option A)
  let e : A ≃ S := Equiv.ofInjective some (Option.some_injective _)
  have he (x : A) : (e x : Option A) = some x := rfl
  have jump (z : S) : ∃ n : ℕ, FirstVisit g S z n ∧
      (g ^ n) z = (e.permCongr ρ z : S) := by
    obtain ⟨x, rfl⟩ := e.surjective z
    by_cases hx : ρ x = y
    · refine ⟨2, ⟨by omega, ?_, ?_⟩, ?_⟩
      · change g (g (some x)) ∈ S
        simp only [g, insert_some, hx, ite_true, insert_none]
        exact ⟨y, rfl⟩
      · intro k hk hk2
        have : k = 1 := by omega
        subst k
        change g (some x) ∉ S
        simp [g, insert_some, hx, S]
      · simp only [pow_two, Perm.mul_apply, Equiv.permCongr_apply,
          Equiv.symm_apply_apply, he]
        simp only [g, insert_some, hx, ite_true, insert_none]
    · refine ⟨1, ⟨by omega, ?_, by intro k hk hk1; omega⟩, ?_⟩
      · change g (some x) ∈ S
        simp only [g, insert_some, hx, ite_false]
        exact ⟨ρ x, rfl⟩
      · simp only [pow_one, Equiv.permCongr_apply, Equiv.symm_apply_apply, he]
        simp only [g, insert_some, hx, ite_false]
  have marked (x z : A) : g.SameCycle (some x) (some z) ↔ ρ.SameCycle x z :=
    (same_cycle_of_first_visit g S (e.permCongr ρ) jump (e x) (e z)).trans
      (same_cycle_perm_congr e ρ x z)
  have hn : g.SameCycle none (some y) := by
    exact ⟨1, by simpa only [zpow_one] using insert_none ρ y⟩
  constructor
  · intro h
    exact ⟨ρ.bijective.bijOn_univ, fun x _ z _ =>
      (marked x z).mp (h.2 (Set.mem_univ _) (Set.mem_univ _))⟩
  · intro h
    refine ⟨g.bijective.bijOn_univ, ?_⟩
    intro x _ z _
    have hc (a b : A) := (marked a b).mpr (h.2 (Set.mem_univ _) (Set.mem_univ _))
    cases x with
    | none =>
      cases z with
      | none => exact Perm.SameCycle.refl g none
      | some z => exact hn.trans (hc y z)
    | some x =>
      cases z with
      | none => exact (hc x y).trans hn.symm
      | some z => exact hc x z

private theorem insert_compatible_iff [DecidableEq A]
    (s d : A → Bool) (c : Bool) (ρ : Perm A) (y : A) :
    (∀ x, Option.elim' c d x = Option.elim' c s (insertLabel ρ y x)) ↔
      s y = c ∧ ∀ x, d x = s (ρ x) := by
  constructor
  · intro h
    have hy : s y = c := by simpa only [insert_none, Option.elim'_none,
      Option.elim'_some] using (h none).symm
    refine ⟨hy, fun x => ?_⟩
    have hx := h (some x)
    by_cases he : ρ x = y
    · simpa [insert_some, he, hy] using hx
    · simpa [insert_some, he] using hx
  · rintro ⟨hy, h⟩ (_ | x)
    · simpa [insert_none] using hy.symm
    · by_cases he : ρ x = y
      · simpa [insert_some, he, hy] using h x
      · simpa [insert_some, he] using h x

/-- Delete one loop label and retain its actual successor as the insertion slot. -/
private def loopInsertionEquiv [Finite A] [Nonempty A] [DecidableEq A]
    (s d : A → Bool) (c : Bool) :
    ({y : A // s y = c} × Compatible s d) ≃
      Compatible (Option.elim' c s) (Option.elim' c d) := by
  let F : ({y : A // s y = c} × Compatible s d) →
      Compatible (Option.elim' c s) (Option.elim' c d) := fun z =>
    ⟨insertLabel z.2.1 z.1.1, inferInstance,
      (insert_cycle_iff _ _).mpr z.2.2.2.1,
      (insert_compatible_iff s d c _ _).mpr ⟨z.1.2, z.2.2.2.2⟩⟩
  apply Equiv.ofBijective F
  constructor
  · intro z w he
    have hp := congrArg (fun σ => Perm.decomposeOption σ.1) he
    have hz : Perm.decomposeOption (insertLabel z.2.1 z.1.1) =
        (some z.1.1, z.2.1) := by
      simpa [Perm.decomposeOption, Equiv.symm, insertLabel] using
        Perm.decomposeOption.apply_symm_apply (some z.1.1, z.2.1)
    have hw : Perm.decomposeOption (insertLabel w.2.1 w.1.1) =
        (some w.1.1, w.2.1) := by
      simpa [Perm.decomposeOption, Equiv.symm, insertLabel] using
        Perm.decomposeOption.apply_symm_apply (some w.1.1, w.2.1)
    change Perm.decomposeOption (insertLabel z.2.1 z.1.1) =
      Perm.decomposeOption (insertLabel w.2.1 w.1.1) at hp
    rw [hz, hw] at hp
    exact Prod.ext (Subtype.ext (Option.some_injective _ (congrArg Prod.fst hp)))
      (Subtype.ext (congrArg Prod.snd hp))
  · intro σ
    have hn : σ.1 none ≠ none :=
      σ.2.2.1.apply_ne Set.nontrivial_univ (Set.mem_univ _)
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hn
    let ρ : Perm A := Equiv.removeNone σ.1
    have he : insertLabel ρ y = σ.1 := by
      have h := Perm.decomposeOption.symm_apply_apply σ.1
      change insertLabel (Equiv.removeNone σ.1) y = σ.1
      simpa [Perm.decomposeOption, hy, insertLabel] using h
    have hc : ρ.IsCycleOn Set.univ := (insert_cycle_iff ρ y).mp (he ▸ σ.2.2.1)
    have hp := (insert_compatible_iff s d c ρ y).mp (he ▸ σ.2.2.2)
    exact ⟨(⟨y, hp.1⟩, ⟨ρ, inferInstance, hc, hp.2⟩), Subtype.ext he⟩

private def compatibleTransport (e : C ≃ A) (s d : C → Bool) :
    Compatible s d ≃ Compatible (s ∘ e.symm) (d ∘ e.symm) :=
  Equiv.subtypeEquiv e.permCongr (fun ρ => by
    constructor
    · rintro ⟨hne, hc, hd⟩
      refine ⟨hne.map e, ⟨(e.permCongr ρ).bijective.bijOn_univ, ?_⟩, ?_⟩
      · intro x _ y _
        simpa only [Equiv.apply_symm_apply] using
          (same_cycle_perm_congr e ρ (e.symm x) (e.symm y)).mpr
            (hc.2 (Set.mem_univ _) (Set.mem_univ _))
      · intro x
        simpa using hd (e.symm x)
    · rintro ⟨hne, hc, hd⟩
      refine ⟨hne.map e.symm, ⟨ρ.bijective.bijOn_univ, ?_⟩, ?_⟩
      · intro x _ y _
        exact (same_cycle_perm_congr e ρ x y).mp
          (hc.2 (Set.mem_univ _) (Set.mem_univ _))
      · intro x
        simpa using hd (e x))

private abbrev Side (s : C → Bool) (b : Bool) := {x : C // s x = b}

private def crossPermutation (s : C → Bool)
    (f : Side s false ≃ Side s true) (g : Side s true ≃ Side s false) : Perm C :=
  Equiv.subtypeCongr f
    ((Equiv.subtypeEquivRight (fun x => by cases s x <;> simp)).trans
      (g.trans (Equiv.subtypeEquivRight (fun x => by cases s x <;> simp))))

private theorem cross_false (s : C → Bool)
    (f : Side s false ≃ Side s true) (g : Side s true ≃ Side s false)
    (x : Side s false) : crossPermutation s f g x = f x := by
  simp [crossPermutation, Equiv.subtypeCongr, x.2]

private theorem cross_true (s : C → Bool)
    (f : Side s false ≃ Side s true) (g : Side s true ≃ Side s false)
    (x : Side s true) : crossPermutation s f g x = g x := by
  have hx : s x ≠ false := by simp [x.2]
  simp [crossPermutation, Equiv.subtypeCongr, hx, Equiv.subtypeEquivRight, Equiv.subtypeEquiv]

private theorem cross_cycle_iff [Finite C] (s : C → Bool)
    (f : Side s false ≃ Side s true) (g : Side s true ≃ Side s false) :
    (crossPermutation s f g).IsCycleOn Set.univ ↔
      Perm.IsCycleOn (f.trans g) Set.univ := by
  let σ := crossPermutation s f g
  let S : Set C := {x | s x = false}
  have jump (x : S) : ∃ n : ℕ, FirstVisit σ S x n ∧
      (σ ^ n) x = (f.trans g x : S) := by
    refine ⟨2, ⟨by omega, ?_, ?_⟩, ?_⟩
    · change σ (σ x) ∈ S
      rw [show σ x = f x from cross_false s f g x, cross_true s f g]
      exact (g (f x)).2
    · intro k hk hk2
      have : k = 1 := by omega
      subst k
      change σ x ∉ S
      rw [show σ x = f x from cross_false s f g x]
      change s (f x) ≠ false
      simp [(f x).2]
    · simp only [pow_two, Perm.mul_apply, Equiv.trans_apply]
      rw [show σ x = f x from cross_false s f g x, cross_true s f g]
  have marked (x y : S) : σ.SameCycle x y ↔ Perm.SameCycle (f.trans g) x y :=
    same_cycle_of_first_visit σ S (f.trans g) jump x y
  constructor
  · intro h
    exact ⟨(f.trans g).bijective.bijOn_univ,
      fun x _ y _ => (marked x y).mp (h.2 (Set.mem_univ _) (Set.mem_univ _))⟩
  · intro h
    have every (x : C) : ∃ z : S, σ.SameCycle x z := by
      by_cases hx : s x = false
      · exact ⟨⟨x, hx⟩, Perm.SameCycle.refl σ x⟩
      · have ht : s x = true := by cases he : s x <;> simp_all
        refine ⟨g ⟨x, ht⟩, ?_⟩
        exact ⟨1, by simpa only [zpow_one] using cross_true s f g ⟨x, ht⟩⟩
    refine ⟨σ.bijective.bijOn_univ, ?_⟩
    intro x _ y _
    obtain ⟨a, ha⟩ := every x
    obtain ⟨b, hb⟩ := every y
    exact ha.trans (((marked a b).mpr (h.2 (Set.mem_univ _) (Set.mem_univ _))).trans hb.symm)

end D5.S3.Combinatorics.Graph.LinearForests.CompatibleCycleInventory
