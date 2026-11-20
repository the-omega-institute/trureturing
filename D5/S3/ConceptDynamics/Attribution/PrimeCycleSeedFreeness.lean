/- GID: D5/S3/ConceptDynamics/Attribution/PrimeCycleSeedFreeness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/PrimeCycleSeedFreeness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime-cycle test profiles force every positive calibrating seed to have trivial stabilizer. -/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! Freeness of equivariant seed actions detected by prime-cycle profiles. -/

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.PrimeCycleSeedFreeness

open Finset
open Equiv.Perm

private abbrev Profile (I : Type*) [Fintype I] (m : ℕ) :=
  {p : I → ℕ // ∑ i, p i = m}

private abbrev relabel {I : Type*} [Fintype I] {m : ℕ} (g : Equiv.Perm I) (p : Profile I m) :
    Profile I m :=
  ⟨fun i => p.val (g⁻¹ i), (Equiv.sum_comp (g⁻¹ : Equiv.Perm I) p.val).trans p.property⟩

theorem free_of_prime_divisibility {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]
    [MulAction (Equiv.Perm I) S] {m : ℕ}
    (divisible : ∀ p : ℕ, p.Prime → p ≤ Fintype.card I → p ∣ m)
    (w : S → ℝ) (positive : ∀ s, 0 < w s) (f : Profile I m → S → I)
    (mass : ∀ p i, ∑ s, (if f p s = i then w s else 0) = (p.val i : ℝ))
    (covariant : ∀ g p s, f (relabel g p) (g • s) = g (f p s)) :
    ∀ s : S, MulAction.stabilizer (Equiv.Perm I) s = ⊥ := by
  classical
  intro s
  let H := MulAction.stabilizer (Equiv.Perm I) s
  apply (Subgroup.eq_bot_iff_forall H).mpr
  intro h fixing
  by_contra nontrivial
  let _ : Fintype H := Fintype.ofFinite H
  let _ : Nontrivial H := ⟨⟨⟨h, fixing⟩, 1, fun eq => nontrivial (congrArg Subtype.val eq)⟩⟩
  obtain ⟨p, prime, divides⟩ := Nat.exists_prime_and_dvd (ne_of_gt (Fintype.one_lt_card : 1 < Fintype.card H))
  let _ : Fact p.Prime := ⟨prime⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card (G := H) p divides
  let u : Equiv.Perm I := g.val
  have uOrd : orderOf u = p := (orderOf_injective H.subtype Subtype.val_injective g).trans hg
  have uNe : u ≠ 1 := by
    intro h
    have one := orderOf_eq_one_iff.mpr h
    rw [uOrd] at one
    exact prime.ne_one one
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr
    (fun eq => uNe (support_eq_empty_iff.mp eq))
  have moved : u i ≠ i := mem_support.mp hi
  let cycle := u.cycleOf i
  have cycleOrd : orderOf cycle = p := by
    have d := orderOf_cycleOf_dvd_orderOf u i
    rw [uOrd] at d
    have h := (Nat.dvd_prime prime).mp d
    refine h.resolve_left fun one => moved ?_
    have isOne : cycle = 1 := orderOf_eq_one_iff.mp one
    simpa only [← cycleOf_apply_self u i, show u.cycleOf i = 1 from isOne] using
      (show (1 : Equiv.Perm I) i = i from rfl)
  let block := cycle.support
  have bCard : block.card = p := (isCycle_cycleOf u moved).orderOf.symm.trans cycleOrd
  have bDiv : block.card ∣ m := by
    rw [bCard]
    exact divisible p prime (bCard ▸ Finset.card_le_univ block)
  let prob : Profile I m := ⟨fun j => if j ∈ block then m/block.card else 0, by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul, Nat.cast_id, Nat.mul_comm, Nat.div_mul_cancel bDiv]⟩
  have preserved (j : I) : u j ∈ block ↔ j ∈ block := by
    rw [mem_support_cycleOf_iff' moved, mem_support_cycleOf_iff' moved]
    exact ⟨fun h => h.trans (u.sameCycle_apply_right.1 (SameCycle.refl _ _)),
      fun h => h.trans (u.sameCycle_apply_right.2 (SameCycle.refl _ _))⟩
  have invariant : relabel u prob = prob := by
    apply Subtype.ext
    funext j
    change (if u⁻¹ j ∈ block then m/block.card else 0) = if j ∈ block then m/block.card else 0
    have eq := (preserved (u⁻¹ j)).symm
    rw [show u (u⁻¹ j) = j from u.apply_symm_apply j] at eq
    simp only [eq]
  have fixesSeed : u • s = s := MulAction.mem_stabilizer_iff.mp g.property
  let j := f prob s
  have fixedLabel : u j = j := by
    simpa only [j, invariant, fixesSeed] using (covariant u prob s).symm
  have outside : j ∉ block := fun hj => mem_support.mp (support_cycleOf_le u i hj) fixedLabel
  have zero : (∑ t, if f prob t = j then w t else 0) = 0 := by
    have eq := mass prob j
    change _ = ((if j ∈ block then m/block.card else 0 : ℕ) : ℝ) at eq
    simpa only [ite_eq_right outside, Nat.cast_zero] using eq
  have dominated := Finset.single_le_sum (s := Finset.univ)
    (f := fun t => if f prob t = j then w t else 0)
    (fun t _ => by split <;> first | exact (positive t).le | exact le_rfl)
    (Finset.mem_univ s)
  rw [zero, ite_eq_left (show f prob s = j from rfl)] at dominated
  exact (not_lt_of_ge dominated) (positive s)

end D5.S3.ConceptDynamics.Attribution.PrimeCycleSeedFreeness
