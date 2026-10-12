/- GID: D5/S3/Combinatorics/EdgeLabeling/CubicARGraphCounting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/EdgeLabeling/CubicARGraphCounting
   mirror-E: none(waiver:helper-for-open-problem-resolution)
   anchors: []
   utility: none
   digest: Counts extensions of finite partial injections and gives a finite union bound. -/

import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.EdgeLabeling.CubicARGraphCounting

open scoped BigOperators

private def extensionPermEquiv {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (s : Finset α) (base : α ≃ β) :
    {e : α ≃ β // ∀ x : s, e x = base x} ≃
      {p : Equiv.Perm α // ∀ x : s, p x = x} where
  toFun e := ⟨e.val.trans base.symm, by
    intro x
    simp only [Equiv.trans_apply, e.property x, Equiv.symm_apply_apply]⟩
  invFun p := ⟨p.val.trans base, by
    intro x
    simp only [Equiv.trans_apply, p.property x]⟩
  left_inv e := by
    apply Subtype.ext
    ext x
    simp
  right_inv p := by
    apply Subtype.ext
    ext x
    simp

/-- A bijection on two equally sized finite types extending an injection on j specified
points has exactly (k-j)! possibilities. -/
private theorem card_equiv_extensions {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (s : Finset α) (f : s → β)
    (hf : Function.Injective f) (hcard : Fintype.card α = Fintype.card β) :
    Fintype.card {e : α ≃ β // ∀ x : s, e x = f x} =
      Nat.factorial (Fintype.card α - s.card) := by
  classical
  obtain ⟨base⟩ := Fintype.card_eq.mp hcard
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair
    (fun x : s => base x) f (base.injective.comp Subtype.val_injective) hf
  let ext : α ≃ β := base.trans p
  have hext (x : s) : ext x = f x := hp x
  let transport : {e : α ≃ β // ∀ x : s, e x = f x} ≃
      {e : α ≃ β // ∀ x : s, e x = ext x} :=
    Equiv.subtypeEquivRight (fun e => by simp only [hext])
  rw [Fintype.card_congr (transport.trans (extensionPermEquiv s ext))]
  have hmem (p : Equiv.Perm α) :
      p ∈ permsOfFinset sᶜ ↔ ∀ x : s, p x = x := by
    rw [mem_perms_of_finset_iff]
    constructor
    · intro h x
      by_contra hne
      have hnot := h hne
      exact (Finset.mem_compl.mp hnot) x.property
    · intro h x hne
      simp only [Finset.mem_compl]
      intro hx
      exact hne (h ⟨x, hx⟩)
  rw [Fintype.card_of_subtype (permsOfFinset sᶜ) hmem,
    card_perms_of_finset, Finset.card_compl]

/-- The extension count with the prescribed domain specified by an injective index map. -/
private theorem card_equiv_constraints {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (d : ι → α) (l : ι → β)
    (hd : Function.Injective d) (hl : Function.Injective l)
    (hcard : Fintype.card α = Fintype.card β) :
    Fintype.card {e : α ≃ β // ∀ i, e (d i) = l i} =
      Nat.factorial (Fintype.card α - Fintype.card ι) := by
  classical
  let s : Finset α := Finset.univ.image d
  let de : ι ≃ s := Equiv.ofBijective (fun i =>
      (⟨d i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩ : s))
    ⟨fun i j h => hd (congrArg Subtype.val h), by
      intro x
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp x.property
      exact ⟨i, Subtype.ext he⟩⟩
  let f : s → β := fun x => l (de.symm x)
  have hde (i : ι) : (de i).val = d i := rfl
  have hpred (e : α ≃ β) : (∀ i, e (d i) = l i) ↔ (∀ x : s, e x = f x) := by
    constructor
    · intro h x
      have hdx : d (de.symm x) = x := congrArg Subtype.val (de.apply_symm_apply x)
      change e x = l (de.symm x)
      rw [← hdx]
      exact h (de.symm x)
    · intro h i
      have hi := h (de i)
      simpa only [f, de.symm_apply_apply, hde] using hi
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hpred),
    card_equiv_extensions s f (hl.comp de.symm.injective) hcard]
  congr 1
  simp only [s, Finset.card_image_of_injective _ hd, Finset.card_univ]

/-- An instance-independent form of the indexed constraint count. -/
theorem nat_card_equiv_constraints {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (d : ι → α) (l : ι → β)
    (hd : Function.Injective d) (hl : Function.Injective l)
    (hcard : Fintype.card α = Fintype.card β) :
    Nat.card {e : α ≃ β // ∀ i, e (d i) = l i} =
      Nat.factorial (Fintype.card α - Fintype.card ι) := by
  classical
  exact Nat.card_eq_fintype_card.trans (card_equiv_constraints d l hd hl hcard)

/-- If the sum of the sizes of a finite family of bad events is below the size of the
sample space, one outcome avoids every bad event. -/
theorem exists_avoiding_of_sum_card_lt {ι Ω : Type*} [Fintype ι] [Fintype Ω]
    (bad : ι → Finset Ω)
    (h : (∑ i, (bad i).card) < Fintype.card Ω) :
    ∃ outcome : Ω, ∀ i, outcome ∉ bad i := by
  classical
  have hbound : (Finset.univ.biUnion bad).card < Fintype.card Ω :=
    lt_of_le_of_lt Finset.card_biUnion_le h
  have hne : Finset.univ.biUnion bad ≠ Finset.univ := by
    intro heq
    simpa [heq] using hbound
  have hmissing : ∃ outcome : Ω, outcome ∉ Finset.univ.biUnion bad := by
    by_contra hn
    push Not at hn
    apply hne
    exact Finset.eq_univ_iff_forall.mpr hn
  obtain ⟨outcome, houtcome⟩ := hmissing
  refine ⟨outcome, ?_⟩
  intro i hi
  exact houtcome (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩)

end D5.S3.Combinatorics.EdgeLabeling.CubicARGraphCounting
