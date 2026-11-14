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
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic

/-! Label-preserving insertion on the actual permutation carrier.

The positive-inventory formula is the two-state specialization of the classical
BEST Euler-tour count for labelled directed multigraphs (Creed and Cryan,
DOI 10.37236/2377, Theorem 1). The proof here uses exhaustive loop insertion
and a two-fiber first-return equivalence, rather than importing general BEST.
Ordinary raw-forest contraction is supplied by DirectedForestCompletion.
-/

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

abbrev Side (s : C → Bool) (b : Bool) := {x : C // s x = b}

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

private def crossInventoryEquiv [Finite C] (s : C → Bool) [Nonempty (Side s false)] :
    ((Side s false ≃ Side s true) ×
      DirectedForestCompletion.FullCycle (Side s false)) ≃
        Compatible s (fun x => !(s x)) := by
  let F : ((Side s false ≃ Side s true) ×
      DirectedForestCompletion.FullCycle (Side s false)) →
      Compatible s (fun x => !(s x)) := fun z =>
    ⟨crossPermutation s z.1 (z.1.symm.trans z.2.1),
      (inferInstance : Nonempty (Side s false)).map Subtype.val,
      (cross_cycle_iff s _ _).mpr (by
        have hr : z.1.trans (z.1.symm.trans z.2.1) = z.2.1 := by
          ext x
          simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
        rw [hr]
        exact z.2.2), by
        intro x
        cases hx : s x with
        | false =>
          rw [show crossPermutation s z.1 (z.1.symm.trans z.2.1) x = z.1 ⟨x, hx⟩ from
            cross_false s _ _ ⟨x, hx⟩]
          simp [hx, (z.1 ⟨x, hx⟩).2]
        | true =>
          rw [show crossPermutation s z.1 (z.1.symm.trans z.2.1) x =
            (z.1.symm.trans z.2.1) ⟨x, hx⟩ from cross_true s _ _ ⟨x, hx⟩]
          change (!(s x)) = s (z.2.1 (z.1.symm ⟨x, hx⟩))
          rw [hx]
          exact (z.2.1 (z.1.symm ⟨x, hx⟩)).2.symm⟩
  apply Equiv.ofBijective F
  constructor
  · rintro ⟨f, ρ⟩ ⟨g, η⟩ h
    have hs : crossPermutation s f (f.symm.trans ρ.1) =
        crossPermutation s g (g.symm.trans η.1) := congrArg Subtype.val h
    have hfg : f = g := by
      ext x
      simpa only [cross_false] using congrArg (fun σ : Perm C => σ x) hs
    subst g
    refine Prod.ext rfl (Subtype.ext ?_)
    ext x
    have he := congrArg (fun σ : Perm C => σ (f x)) hs
    simpa only [cross_true, Equiv.trans_apply, Equiv.symm_apply_apply] using he
  · intro σ
    have hf (x : C) : s x = false ↔ s (σ.1 x) = true := by
      have h := σ.2.2.2 x
      cases hx : s x <;> cases hy : s (σ.1 x) <;>
        simp only [hx, hy, Bool.not_false, Bool.not_true,
          Bool.false_eq_true, Bool.true_eq_false] at h ⊢
    have hg (x : C) : s x = true ↔ s (σ.1 x) = false := by
      have h := σ.2.2.2 x
      cases hx : s x <;> cases hy : s (σ.1 x) <;>
        simp only [hx, hy, Bool.not_false, Bool.not_true,
          Bool.false_eq_true, Bool.true_eq_false] at h ⊢
    let f : Side s false ≃ Side s true := Equiv.subtypeEquiv σ.1 hf
    let g : Side s true ≃ Side s false := Equiv.subtypeEquiv σ.1 hg
    have he : crossPermutation s f g = σ.1 := by
      ext x
      cases hx : s x with
      | false => exact cross_false s f g ⟨x, hx⟩
      | true => exact cross_true s f g ⟨x, hx⟩
    let ρ : Perm (Side s false) := f.trans g
    have hc : ρ.IsCycleOn Set.univ := (cross_cycle_iff s f g).mp (he ▸ σ.2.2.1)
    refine ⟨(f, ⟨ρ, hc⟩), Subtype.ext ?_⟩
    change crossPermutation s f (f.symm.trans ρ) = σ.1
    have hr : f.symm.trans ρ = g := by ext x; simp [ρ]
    rw [hr, he]

private theorem fullCycle_card_nonempty [Finite C] [Nonempty C] :
    Nat.card (DirectedForestCompletion.FullCycle C) = (Nat.card C - 1).factorial := by
  by_cases h : 2 ≤ Nat.card C
  · exact DirectedForestCompletion.full_cycle_card h
  · have hc : Nat.card C = 1 := by have := Nat.card_pos (α := C); omega
    letI := Fintype.ofFinite C
    letI : Subsingleton C := Fintype.card_le_one_iff_subsingleton.mp (by
      simpa only [Nat.card_eq_fintype_card] using (show Nat.card C ≤ 1 by omega))
    have hi : (1 : Perm C).IsCycleOn Set.univ := Perm.isCycleOn_of_subsingleton _ _
    letI : Nonempty (DirectedForestCompletion.FullCycle C) := ⟨⟨1, hi⟩⟩
    letI : Unique (DirectedForestCompletion.FullCycle C) := uniqueOfSubsingleton ⟨1, hi⟩
    rw [Nat.card_unique, hc]
    rfl

/-- Cardinality of the inventory retaining both endpoint states of every label. -/
def inventory (s d : C → Bool) (a b : Bool) : ℕ :=
  Nat.card {x : C // s x = a ∧ d x = b}

private theorem side_card [Finite C] (s d : C → Bool) (a : Bool) :
    Nat.card (Side s a) = inventory s d a false + inventory s d a true := by
  letI := Fintype.ofFinite C
  classical
  simp only [inventory, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun x => s x = a)) (fun x => d x = false)
  simpa only [Finset.filter_filter, Bool.not_eq_false] using h.symm

private theorem option_inventory [Finite A] (s d : A → Bool) (c a b : Bool) :
    inventory (Option.elim' c s) (Option.elim' c d) a b =
      inventory s d a b + if c = a ∧ c = b then 1 else 0 := by
  letI := Fintype.ofFinite A
  classical
  simp only [inventory, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter, Fintype.sum_option, Option.elim'_none, Option.elim'_some]
  exact Nat.add_comm _ _

private theorem option_side [Finite A] (s : A → Bool) (c a : Bool) :
    Nat.card (Side (Option.elim' c s) a) = Nat.card (Side s a) + if c = a then 1 else 0 := by
  letI := Fintype.ofFinite A
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    Fintype.sum_option, Option.elim'_none, Option.elim'_some]
  exact Nat.add_comm _ _

private theorem inventory_transport (e : C ≃ A) (s d : A → Bool) (a b : Bool) :
    inventory (s ∘ e) (d ∘ e) a b = inventory s d a b :=
  Nat.card_congr (Equiv.subtypeEquivOfSubtype (p := fun x : A => s x = a ∧ d x = b) e)

private theorem side_transport (e : C ≃ A) (s : A → Bool) (a : Bool) :
    Nat.card (Side (s ∘ e) a) = Nat.card (Side s a) :=
  Nat.card_congr (Equiv.subtypeEquivOfSubtype (p := fun x : A => s x = a) e)

private theorem inventory_le_side [Finite C] (s d : C → Bool) (a b : Bool) :
    inventory s d a b ≤ Nat.card (Side s a) :=
  Nat.card_le_card_of_injective (fun x : {x : C // s x = a ∧ d x = b} =>
      (⟨x.1, x.2.1⟩ : Side s a))
    (fun x y h => Subtype.ext (congrArg (fun z : Side s a => (z : C)) h))

private theorem cross_inventory [Finite C] (s : C → Bool) (b : Bool) :
    inventory s (fun x => !(s x)) b (!b) = Nat.card (Side s b) := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun x => by cases hs : s x <;> cases b <;> simp [hs])

private theorem no_loop_card [Finite C] (s d : C → Bool)
    (hd : ∀ x, s x ≠ d x)
    (hb : inventory s d false true = inventory s d true false)
    (hp : 0 < inventory s d false true) :
    Nat.card (Compatible s d) = inventory s d false true *
      (Nat.card (Side s false) - 1).factorial * (Nat.card (Side s true) - 1).factorial := by
  have he : d = fun x => !(s x) := by
    funext x
    have h := hd x
    cases hs : s x <;> cases ht : d x <;> simp_all
  subst d
  have hr := cross_inventory s false
  have ht := cross_inventory s true
  simp only [Bool.not_false, Bool.not_true] at hr ht
  have hside : Nat.card (Side s false) = Nat.card (Side s true) := by omega
  have hpos : 0 < Nat.card (Side s false) := by omega
  letI : Nonempty (Side s false) := (Nat.card_pos_iff.mp hpos).1
  letI := Fintype.ofFinite C
  let e : Side s false ≃ Side s true := Fintype.equivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card] using hside)
  have hcard : Nat.card (Side s false ≃ Side s true) = (Nat.card (Side s false)).factorial := by
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_equiv e
  rw [← Nat.card_congr (crossInventoryEquiv s), Nat.card_prod, hcard,
    fullCycle_card_nonempty, hr, ← hside]
  have hfac : (Nat.card (Side s false)).factorial =
      Nat.card (Side s false) * (Nat.card (Side s false) - 1).factorial := by
    simpa only [Nat.sub_add_cancel hpos] using Nat.factorial_succ (Nat.card (Side s false) - 1)
  rw [hfac]

private theorem positive_inventory_card [Finite C] (s d : C → Bool)
    (hb : inventory s d false true = inventory s d true false)
    (hp : 0 < inventory s d false true) :
    Nat.card (Compatible s d) = inventory s d false true *
      (Nat.card (Side s false) - 1).factorial * (Nat.card (Side s true) - 1).factorial := by
  suffices aux : ∀ n : ℕ, ∀ (T : Type u) [Finite T], Nat.card T = n →
      ∀ s d : T → Bool,
      inventory s d false true = inventory s d true false →
      0 < inventory s d false true →
      Nat.card (Compatible s d) = inventory s d false true *
        (Nat.card (Side s false) - 1).factorial *
        (Nat.card (Side s true) - 1).factorial by
    exact aux (Nat.card C) C rfl s d hb hp
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro T _ hn s d hb hp
    classical
    by_cases hl : ∃ x, s x = d x
    · obtain ⟨c, hc⟩ := hl
      let A := {x : T // x ≠ c}
      let e : Option A ≃ T := Equiv.optionSubtypeNe c
      let s' : A → Bool := fun x => s x
      let d' : A → Bool := fun x => d x
      have hs : s ∘ e = Option.elim' (s c) s' := by funext x; cases x <;> rfl
      have hd : d ∘ e = Option.elim' (s c) d' := by
        funext x
        cases x with
        | none => exact hc.symm
        | some x => rfl
      have cross (a b : Bool) (hab : a ≠ b) : inventory s' d' a b = inventory s d a b := by
        have h := inventory_transport e s d a b
        rw [hs, hd, option_inventory] at h
        have hz : ¬ (s c = a ∧ s c = b) := fun h => hab (h.1.symm.trans h.2)
        simpa only [if_neg hz, Nat.add_zero] using h
      have hft := cross false true Bool.false_ne_true
      have htf := cross true false (by decide : true ≠ false)
      have hb' : inventory s' d' false true = inventory s' d' true false := by omega
      have hp' : 0 < inventory s' d' false true := by omega
      letI : Nonempty A := (Nat.card_pos_iff.mp hp').1.map Subtype.val
      have hlt : Nat.card A < n := by
        have h := Finite.card_subtype_lt (p := fun x : T => x ≠ c) (x := c) (by simp)
        exact h.trans_eq hn
      have hi := ih (Nat.card A) hlt A rfl s' d' hb' hp'
      have sides (a : Bool) : Nat.card (Side s a) =
          Nat.card (Side s' a) + if s c = a then 1 else 0 := by
        have h := side_transport e s a
        rw [hs, option_side] at h
        exact h.symm
      have hrec : Nat.card (Compatible s d) =
          Nat.card (Side s' (s c)) * Nat.card (Compatible s' d') := by
        have h := Nat.card_congr (compatibleTransport e.symm s d)
        simp only [Equiv.symm_symm] at h
        rw [hs, hd] at h
        rw [h, ← Nat.card_congr (loopInsertionEquiv s' d' (s c)), Nat.card_prod]
      have hr : 0 < Nat.card (Side s' false) :=
        lt_of_lt_of_le hp' (inventory_le_side s' d' false true)
      have ht : 0 < Nat.card (Side s' true) :=
        lt_of_lt_of_le (by omega : 0 < inventory s' d' true false)
          (inventory_le_side s' d' true false)
      have hfac (r : ℕ) (hr : 0 < r) : r * (r - 1).factorial = r.factorial := by
        simpa only [Nat.sub_add_cancel hr] using (Nat.factorial_succ (r - 1)).symm
      rw [hrec, hi, ← hft, sides false, sides true]
      cases he : s c with
      | false =>
        simp only [he, Bool.false_eq_true, ite_true, ite_false, Nat.add_zero,
          Nat.add_sub_cancel]
        calc
          _ = inventory s' d' false true *
              (Nat.card (Side s' false) * (Nat.card (Side s' false) - 1).factorial) *
              (Nat.card (Side s' true) - 1).factorial := by ring
          _ = _ := by rw [hfac _ hr]
      | true =>
        simp only [he, Bool.true_eq_false, ite_true, ite_false, Nat.add_zero,
          Nat.add_sub_cancel]
        calc
          _ = inventory s' d' false true * (Nat.card (Side s' false) - 1).factorial *
              (Nat.card (Side s' true) * (Nat.card (Side s' true) - 1).factorial) := by ring
          _ = _ := by rw [hfac _ ht]
    · exact no_loop_card s d (not_exists.mp hl) hb hp

private theorem inventory_zero [Finite C] (s d : C → Bool) (a b : Bool)
    (hz : inventory s d a b = 0) (x : C) (hs : s x = a) (hd : d x = b) : False := by
  letI : Nonempty {x : C // s x = a ∧ d x = b} := ⟨⟨x, hs, hd⟩⟩
  have hp : 0 < inventory s d a b := Nat.card_pos
  omega

private theorem preserved_color_constant [Finite C] (s : C → Bool) (ρ : Perm C)
    (hc : ρ.IsCycleOn Set.univ) (hs : ∀ x, s (ρ x) = s x) (x y : C) : s x = s y := by
  obtain ⟨n, hn⟩ := (hc.2 (Set.mem_univ x) (Set.mem_univ y)).exists_nat_pow_eq
  have hpow (n : ℕ) : s ((ρ ^ n) x) = s x := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [pow_succ', Perm.mul_apply, hs] using ih
  exact (hpow n).symm.trans (congrArg s hn)

/-- Exhaustive labelled two-state cycle count, including the empty carrier and
the disconnected zero-crossing inventory. No extension or connectivity premise is supplied. -/
theorem compatible_cycle_card [Finite C] (s d : C → Bool)
    (hb : inventory s d false true = inventory s d true false) :
    Nat.card (Compatible s d) =
      if Nat.card C = 0 then 0
      else if 0 < inventory s d false true then
        inventory s d false true * (Nat.card (Side s false) - 1).factorial *
          (Nat.card (Side s true) - 1).factorial
      else if inventory s d false false = 0 ∨ inventory s d true true = 0 then
        (Nat.card C - 1).factorial else 0 := by
  classical
  by_cases hC : Nat.card C = 0
  · rw [if_pos hC]
    letI : IsEmpty (Compatible s d) := ⟨fun σ => by
      letI : Nonempty C := σ.2.1
      have h := Nat.card_pos (α := C)
      omega⟩
    simp
  · rw [if_neg hC]
    letI : Nonempty C := (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hC)).1
    by_cases hp : 0 < inventory s d false true
    · rw [if_pos hp]
      exact positive_inventory_card s d hb hp
    · rw [if_neg hp]
      have hm : inventory s d false true = 0 := by omega
      have hm' : inventory s d true false = 0 := by omega
      have hd (x : C) : d x = s x := by
        cases hs : s x <;> cases ht : d x
        · rfl
        · exact (inventory_zero s d false true hm x hs ht).elim
        · exact (inventory_zero s d true false hm' x hs ht).elim
        · rfl
      by_cases hz : inventory s d false false = 0 ∨ inventory s d true true = 0
      · rw [if_pos hz]
        have hconst : ∃ b, ∀ x, s x = b := by
          rcases hz with hz | hz
          · refine ⟨true, fun x => ?_⟩
            cases hs : s x with
            | false => exact (inventory_zero s d false false hz x hs ((hd x).trans hs)).elim
            | true => rfl
          · refine ⟨false, fun x => ?_⟩
            cases hs : s x with
            | false => rfl
            | true => exact (inventory_zero s d true true hz x hs ((hd x).trans hs)).elim
        obtain ⟨b, hs⟩ := hconst
        let e : Compatible s d ≃ DirectedForestCompletion.FullCycle C := {
          toFun := fun σ => ⟨σ.1, σ.2.2.1⟩
          invFun := fun ρ => ⟨ρ.1, inferInstance, ρ.2,
            fun x => (hd x).trans ((hs x).trans (hs (ρ.1 x)).symm)⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
        rw [Nat.card_congr e, fullCycle_card_nonempty]
      · rw [if_neg hz]
        have hx : Nonempty {x : C // s x = false ∧ d x = false} :=
          (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero (not_or.mp hz).1)).1
        have hy : Nonempty {x : C // s x = true ∧ d x = true} :=
          (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero (not_or.mp hz).2)).1
        obtain ⟨x, hx⟩ := hx
        obtain ⟨y, hy⟩ := hy
        letI : IsEmpty (Compatible s d) := ⟨fun σ => by
          have h := preserved_color_constant s σ.1 σ.2.2.1
            (fun x => (σ.2.2.2 x).symm.trans (hd x)) x y
          exact Bool.false_ne_true (hx.1.symm.trans (h.trans hy.1))⟩
        simp


open DirectedForestCompletion Relation
variable {V : Type u}

/-- Actual alternating completions, with the empty carrier explicitly excluded. -/
abbrev AlternatingCompletion (E : V → V → Prop) (k : V → Bool) :=
  {σ : Perm V // Nonempty V ∧ σ.IsCycleOn Set.univ ∧
    (∀ x y, E x y → σ x = y) ∧ ∀ x, k (σ x) ≠ k x}

private theorem bool_opposite (a b : Bool) : (!a) = b ↔ a ≠ b := by
  cases a <;> cases b <;> decide

private theorem split_card [Finite V] (p q : V → Prop) :
    Nat.card {x : V // p x} = Nat.card {x : V // p x ∧ q x} +
      Nat.card {x : V // p x ∧ ¬ q x} := by
  classical
  letI := Fintype.ofFinite V
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa only [Finset.filter_filter] using
    (Finset.card_filter_add_card_filter_not (s := Finset.univ.filter p) q).symm

private theorem endpoint_balance [Finite V] (E : V → V → Prop) (k : V → Bool)
    (hout : Relator.RightUnique E) (hin : Relator.LeftUnique E)
    (hk : ∀ x y, E x y → k x ≠ k y)
    (hb : Nat.card (Side k false) = Nat.card (Side k true)) :
    Nat.card {x : Tail E // k x = false} = Nat.card {x : Head E // k x = true} := by
  classical
  let e := edgeEquiv E hout hin
  have he (x : {x : V // ∃ y, E x y}) : k x ≠ k (e x) :=
    hk _ _ (edgeMap_edge E x)
  let f : {x : {x : V // ∃ y, E x y} // k x = false} ≃
      {x : {y : V // ∃ x, E x y} // k x = true} :=
    Equiv.subtypeEquiv e (fun x => by
      have h := he x
      cases hx : k x <;> cases hy : k (e x) <;> simp_all)
  have hocc := Nat.card_congr f
  have norm (p : V → Prop) (b : Bool) :
      Nat.card {x : {x : V // p x} // k x = b} =
        Nat.card {x : V // k x = b ∧ p x} :=
    Nat.card_congr {
      toFun := fun x => ⟨x.1.1, x.2, x.1.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [norm, norm] at hocc
  have hr := split_card (fun x => k x = false) (fun x => ∃ y, E x y)
  have ht := split_card (fun x => k x = true) (fun x => ∃ y, E y x)
  change Nat.card {x : {x : V // ¬ ∃ y, E x y} // k x = false} =
    Nat.card {x : {y : V // ¬ ∃ x, E x y} // k x = true}
  rw [norm, norm]
  change Nat.card {x : V // k x = false} = Nat.card {x : V // k x = true} at hb
  omega

private theorem inventory_balanced [Finite C] (s d : C → Bool)
    (h : Nat.card (Side s true) = Nat.card (Side d true)) :
    inventory s d false true = inventory s d true false := by
  have hs := side_card s d true
  have ht := side_card d s true
  have swap (a b : Bool) : inventory d s a b = inventory s d b a :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun _ => and_comm))
  rw [swap true false, swap true true] at ht
  omega

private theorem raw_classification [Finite V] (E : V → V → Prop) (k : V → Bool)
    (hout : Relator.RightUnique E) (hin : Relator.LeftUnique E)
    (ha : ∀ x, ¬ TransGen E x x) (hk : ∀ x y, E x y → k x ≠ k y) :
    ∃ (t : Component E ≃ Tail E) (h : Component E ≃ Head E)
      (Φ : AlternatingCompletion E k ≃
        Compatible (fun A => k (h A)) (fun A => !(k (t A)))),
      (∀ A, Quotient.mk (EqvGen.setoid E) (t A).1 = A) ∧
      (∀ A, Quotient.mk (EqvGen.setoid E) (h A).1 = A) ∧
      ∀ σ A, σ.1 (t A) = h ((Φ σ).1 A) := by
  obtain ⟨t, h, Ψ, ht, hh, hΨ⟩ := full_cycle_completion_equiv E hout hin ha
  have nonempty_iff : Nonempty V ↔ Nonempty (Component E) :=
    ⟨fun hv => hv.map (Quotient.mk _), fun hc => hc.map Quotient.out⟩
  have alt (σ : CycleCompletion E) :
      (∀ x, k (σ.1 x) ≠ k x) ↔
        ∀ A, (!(k (t A))) = k (h ((Ψ σ).1 A)) := by
    constructor
    · intro hs A
      apply (bool_opposite _ _).mpr
      simpa only [hΨ σ A] using (hs (t A)).symm
    · intro hs x
      by_cases hx : ∃ y, E x y
      · obtain ⟨y, he⟩ := hx
        rw [σ.2.2 _ _ he]
        exact (hk x y he).symm
      · let A := t.symm ⟨x, hx⟩
        have hx' : (t A).1 = x := congrArg Subtype.val (t.apply_symm_apply ⟨x, hx⟩)
        have he := (bool_opposite _ _).mp (hs A)
        rw [← hΨ σ A, hx'] at he
        exact he.symm
  let F : AlternatingCompletion E k ≃
      Compatible (fun A => k (h A)) (fun A => !(k (t A))) := {
    toFun := fun σ =>
      ⟨(Ψ ⟨σ.1, σ.2.2.1, σ.2.2.2.1⟩).1,
        nonempty_iff.mp σ.2.1, (Ψ ⟨σ.1, σ.2.2.1, σ.2.2.2.1⟩).2,
        (alt ⟨σ.1, σ.2.2.1, σ.2.2.2.1⟩).mp σ.2.2.2.2⟩
    invFun := fun ρ =>
      ⟨(Ψ.symm ⟨ρ.1, ρ.2.2.1⟩).1, nonempty_iff.mpr ρ.2.1,
        (Ψ.symm ⟨ρ.1, ρ.2.2.1⟩).2.1, (Ψ.symm ⟨ρ.1, ρ.2.2.1⟩).2.2,
        (alt (Ψ.symm ⟨ρ.1, ρ.2.2.1⟩)).mpr (by
          simpa only [Ψ.apply_symm_apply] using ρ.2.2.2)⟩
    left_inv := by
      intro σ
      apply Subtype.ext
      change (Ψ.symm (Ψ ⟨σ.1, σ.2.2.1, σ.2.2.2.1⟩)).1 = σ.1
      exact congrArg Subtype.val (Ψ.symm_apply_apply ⟨σ.1, σ.2.2.1, σ.2.2.2.1⟩)
    right_inv := by
      intro ρ
      apply Subtype.ext
      change (Ψ (Ψ.symm ⟨ρ.1, ρ.2.2.1⟩)).1 = ρ.1
      exact congrArg Subtype.val (Ψ.apply_symm_apply ⟨ρ.1, ρ.2.2.1⟩) }
  exact ⟨t, h, F, ht, hh, fun σ A => hΨ ⟨σ.1, σ.2.2.1, σ.2.2.2.1⟩ A⟩


private theorem bool_total [Finite C] (s : C → Bool) :
    Nat.card C = Nat.card (Side s false) + Nat.card (Side s true) := by
  simpa only [true_and, Nat.card_subtype_true, Bool.not_eq_false] using
    split_card (fun _ : C => True) (fun x => s x = false)

/-- The four counts on the actual component carrier. The colors false and true
represent R and B. Endpoint membership and the connector identity are retained. -/
theorem alternating_completion_classification [Finite V] (n : ℕ)
    (E : V → V → Prop) (k : V → Bool)
    (hout : Relator.RightUnique E) (hin : Relator.LeftUnique E)
    (ha : ∀ x, ¬ TransGen E x x) (hk : ∀ x y, E x y → k x ≠ k y)
    (hr : Nat.card (Side k false) = n) (hb : Nat.card (Side k true) = n) :
    ∃ (t : Component E ≃ Tail E) (h : Component E ≃ Head E)
      (Φ : AlternatingCompletion E k ≃
        Compatible (fun A => k (h A)) (fun A => !(k (t A)))),
      (∀ A, Quotient.mk (EqvGen.setoid E) (t A).1 = A) ∧
      (∀ A, Quotient.mk (EqvGen.setoid E) (h A).1 = A) ∧
      (∀ σ A, σ.1 (t A) = h ((Φ σ).1 A)) ∧
      let s := fun A => k (h A)
      let d := fun A => !(k (t A))
      let a := inventory s d false true
      let b := inventory s d true false
      let p := inventory s d false false
      let q := inventory s d true true
      a = b ∧ Nat.card (Component E) = a + b + p + q ∧
      (n ≠ 0 → 0 < Nat.card (Component E)) ∧
      Nat.card (AlternatingCompletion E k) =
        if n = 0 then 0
        else if 0 < a then a * (a + p - 1).factorial * (a + q - 1).factorial
        else if p * q = 0 then (p + q - 1).factorial else 0 := by
  classical
  obtain ⟨t, h, Φ, ht, hh, hΦ⟩ := raw_classification E k hout hin ha hk
  refine ⟨t, h, Φ, ht, hh, hΦ, ?_⟩
  let s := fun A => k (h A)
  let d := fun A => !(k (t A))
  change inventory s d false true = inventory s d true false ∧ _
  have hep := endpoint_balance E k hout hin hk (hr.trans hb.symm)
  have hs : Nat.card (Side s true) = Nat.card {x : Head E // k x = true} :=
    side_transport h (fun x => k x) true
  have hd : Nat.card (Side d true) = Nat.card {x : Tail E // k x = false} := by
    calc
      _ = Nat.card {x : Tail E // (!(k x)) = true} :=
        side_transport t (fun x => !(k x)) true
      _ = _ := Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
        cases k x <;> simp))
  have hbal := inventory_balanced s d (hs.trans (hep.symm.trans hd.symm))
  have hsf := side_card s d false
  have hst := side_card s d true
  have htot := bool_total s
  have hsum : Nat.card (Component E) = inventory s d false true +
      inventory s d true false + inventory s d false false + inventory s d true true := by
    omega
  have hne : Nonempty V ↔ Nonempty (Component E) :=
    ⟨fun hv => hv.map (Quotient.mk _), fun hc => hc.map Quotient.out⟩
  have hzero : Nat.card (Component E) = 0 ↔ n = 0 := by
    constructor
    · intro hz
      by_contra hn
      have hp : 0 < Nat.card (Side k false) := by omega
      have hv := (Finite.card_pos_iff.mp hp).map Subtype.val
      have hc := hne.mp hv
      have : 0 < Nat.card (Component E) := Finite.card_pos_iff.mpr hc
      omega
    · intro hn
      apply Finite.card_eq_zero_iff.mpr
      refine ⟨fun A => ?_⟩
      let x := Quotient.out A
      have hbad (b : Bool) (hx : k x = b) (he : Nat.card (Side k b) = 0) : False := by
        have hp : 0 < Nat.card (Side k b) :=
          Finite.card_pos_iff.mpr ⟨⟨x, hx⟩⟩
        omega
      cases hx : k x with
      | false => exact hbad false hx (hr.trans hn)
      | true => exact hbad true hx (hb.trans hn)
  refine ⟨hbal, hsum, (fun hn => Nat.pos_of_ne_zero (mt hzero.mp hn)), ?_⟩
  have hcard := compatible_cycle_card s d hbal
  rw [Nat.card_congr Φ]
  change Nat.card (Compatible s d) =
    if n = 0 then 0 else if 0 < inventory s d false true then
      inventory s d false true *
        (inventory s d false true + inventory s d false false - 1).factorial *
        (inventory s d false true + inventory s d true true - 1).factorial
    else if inventory s d false false * inventory s d true true = 0 then
      (inventory s d false false + inventory s d true true - 1).factorial else 0
  rw [hcard]
  have hsf' : Nat.card (Side s false) = inventory s d false true +
      inventory s d false false := by omega
  have hst' : Nat.card (Side s true) = inventory s d false true +
      inventory s d true true := by omega
  rw [hsf', hst']
  by_cases hn : n = 0
  · simp only [hn, hzero.mpr hn, ite_true]
  · have hc : Nat.card (Component E) ≠ 0 := mt hzero.mp hn
    simp only [hn, hc, ite_false]
    by_cases hm : 0 < inventory s d false true
    · simp only [hm, ite_true]
    · have hm0 : inventory s d false true = 0 := by omega
      have hcount : Nat.card (Component E) =
          inventory s d false false + inventory s d true true := by omega
      simp only [hm, ite_false, hcount, Nat.mul_eq_zero]

end D5.S3.Combinatorics.Graph.LinearForests.CompatibleCycleInventory
