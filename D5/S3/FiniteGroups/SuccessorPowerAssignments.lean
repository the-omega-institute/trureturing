/- GID: D5/S3/FiniteGroups/SuccessorPowerAssignments
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SuccessorPowerAssignments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Squaring assignments on a finite successor permutation are roots of unity and finite. -/

import D5.S3.FiniteGroups.SuccessorQuotient
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

/-! A common return time for a finite permutation puts every compatible unit
coordinate in a finite group of roots of unity. This proves actual finiteness;
cyclewise evaluation and independent realization give the exact cardinality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.FiniteGroups.SuccessorPowerAssignments

open D5.S3.FiniteGroups.SuccessorQuotient

variable {Q K : Type*} [Field K]

abbrev SquareAssignments (β : Equiv.Perm Q) :=
  {v : Q → Kˣ // ∀ q, v (β q) = v q ^ 2}

theorem iterate_square (β : Equiv.Perm Q) (v : SquareAssignments (K := K) β)
    (k : ℕ) (q : Q) : v.val ((β ^ k) q) = v.val q ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, v.property, ih, ← pow_mul, ← Nat.pow_succ]

private theorem root_condition [Finite Q] (β : Equiv.Perm Q)
    (v : SquareAssignments (K := K) β) (q : Q) :
    v.val q ^ (2 ^ orderOf β - 1) = 1 := by
  have hp : 0 < 2 ^ orderOf β := pow_pos (by decide) _
  have hh := iterate_square β v (orderOf β) q
  rw [pow_orderOf_eq_one] at hh
  change v.val q = v.val q ^ (2 ^ orderOf β) at hh
  apply mul_right_cancel (b := v.val q)
  rw [one_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp.ne')]
  exact hh.symm

/-- Actual finiteness of all unit assignments, before taking their natural cardinality. -/
theorem square_assignments_finite [Finite Q] (β : Equiv.Perm Q) :
    Finite (SquareAssignments (K := K) β) := by
  have hn : 0 < orderOf β := orderOf_pos β
  have htwo : 2 ≤ 2 ^ orderOf β := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
    simpa using this
  letI : NeZero (2 ^ orderOf β - 1) := ⟨by omega⟩
  let F : SquareAssignments (K := K) β → (Q → rootsOfUnity (2 ^ orderOf β - 1) K) :=
    fun v q => ⟨v.val q, (mem_rootsOfUnity _ _).mpr (root_condition β v q)⟩
  exact Finite.of_injective F (by
    intro v w h
    apply Subtype.ext
    funext q
    exact congrArg Subtype.val (congrFun h q))

/-- The least quotient transfers the root-of-unity finiteness proof to the original relation. -/
theorem relation_square_assignments_finite {V : Type*} [Finite V]
    (R : V → V → Prop) (hout : ∀ x, ∃ y, R x y) (hin : ∀ y, ∃ x, R x y) :
    Finite (Assignments R (fun z : Kˣ => z ^ 2)) := by
  haveI : Finite (QuotientAssignments R (fun z : Kˣ => z ^ 2) hout) :=
    square_assignments_finite (K := K) (beta R hout hin)
  exact Finite.of_injective (assignmentEquiv R (fun z : Kˣ => z ^ 2) hout)
    (Equiv.injective _)


private theorem root_at_return (β : Equiv.Perm Q) (v : SquareAssignments (K := K) β)
    (q : Q) (l : ℕ) (hl : 0 < l) (hr : (β ^ l) q = q) :
    v.val q ^ (2 ^ l - 1) = 1 := by
  have hp : 0 < 2 ^ l := pow_pos (by decide) _
  have hh := iterate_square β v l q
  rw [hr] at hh
  apply mul_right_cancel (b := v.val q)
  rw [one_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp.ne')]
  exact hh.symm

section CycleCount

variable [Fintype Q] [DecidableEq Q] (β : Equiv.Perm Q)

private noncomputable def cycleRepresentative (c : β.cycleFactorsFinset) : Q :=
  Classical.choose ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.property).1.nonempty_support)

private theorem representative_mem (c : β.cycleFactorsFinset) :
    cycleRepresentative β c ∈ c.val.support :=
  Classical.choose_spec ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.property).1.nonempty_support)

private theorem cycle_root (v : SquareAssignments (K := K) β) (c : β.cycleFactorsFinset) :
    v.val (cycleRepresentative β c) ^ (2 ^ c.val.support.card - 1) = 1 := by
  have hcyc := Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset c.property
  exact root_at_return β v _ _ (Finset.card_pos.mpr ⟨_, representative_mem β c⟩)
    (hcyc.pow_card_apply (representative_mem β c))

private theorem fixed_value (v : SquareAssignments (K := K) β) {q : Q} (hq : β q = q) :
    v.val q = 1 := by
  have h := v.property q
  rw [hq, pow_two] at h
  exact (mul_left_cancel (show v.val q * v.val q = v.val q * 1 by simpa using h.symm))

private theorem cycle_evaluation_injective : Function.Injective
    (fun v : SquareAssignments (K := K) β => fun c : β.cycleFactorsFinset =>
      v.val (cycleRepresentative β c)) := by
  intro v w h
  apply Subtype.ext
  funext q
  by_cases hq : β q = q
  · rw [fixed_value β v hq, fixed_value β w hq]
  · let c : β.cycleFactorsFinset := ⟨β.cycleOf q,
      (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff).mpr (Equiv.Perm.mem_support.mpr hq)⟩
    have hs : β.SameCycle (cycleRepresentative β c) q := by
      exact ((Equiv.Perm.mem_support_cycleOf_iff' hq).mp (representative_mem β c)).symm
    obtain ⟨k, hk⟩ := hs.exists_nat_pow_eq
    rw [← hk, iterate_square, iterate_square]
    exact congrArg (fun z : Kˣ => z ^ (2 ^ k)) (congrFun h c)


private noncomputable def cyclePosition (c : β.cycleFactorsFinset) (q : Q)
    (hq : q ∈ c.val.support) : ℕ :=
  Classical.choose ((Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset c.property).exists_pow_eq
    (representative_mem β c) hq)

private theorem position_spec (c : β.cycleFactorsFinset) (q : Q)
    (hq : q ∈ c.val.support) :
    cyclePosition β c q hq < c.val.support.card ∧
      (β ^ cyclePosition β c q hq) (cycleRepresentative β c) = q :=
  Classical.choose_spec ((Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset c.property).exists_pow_eq
    (representative_mem β c) hq)

private theorem position_representative (c : β.cycleFactorsFinset) :
    cyclePosition β c (cycleRepresentative β c) (representative_mem β c) = 0 := by
  have hc := Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset c.property
  apply hc.injOn_pow_apply (representative_mem β c)
    (position_spec β c _ _).1
    (Finset.card_pos.mpr ⟨_, representative_mem β c⟩)
  simpa using (position_spec β c _ _).2

private theorem position_successor (c : β.cycleFactorsFinset) (q : Q)
    (hq : q ∈ c.val.support)
    (hbq : β q ∈ c.val.support) :
    cyclePosition β c (β q) hbq = (cyclePosition β c q hq + 1) % c.val.support.card := by
  have hc := Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset c.property
  have he : (β ^ cyclePosition β c (β q) hbq) (cycleRepresentative β c) =
      (β ^ (cyclePosition β c q hq + 1)) (cycleRepresentative β c) := by
    rw [(position_spec β c _ _).2, pow_succ', Equiv.Perm.mul_apply,
      (position_spec β c _ _).2]
  have hm := (hc.pow_apply_eq_pow_apply (representative_mem β c)).mp he
  exact (Nat.mod_eq_of_lt (position_spec β c _ _).1).symm.trans hm

private theorem root_power_return (c : β.cycleFactorsFinset)
    (z : rootsOfUnity (2 ^ c.val.support.card - 1) K) :
    (z.val : Kˣ) ^ (2 ^ c.val.support.card) = z.val := by
  have hp : 1 ≤ 2 ^ c.val.support.card := Nat.one_le_pow _ _ (by decide)
  have hz := (mem_rootsOfUnity _ _).mp z.property
  calc
    (z.val : Kˣ) ^ (2 ^ c.val.support.card) =
        z.val ^ ((2 ^ c.val.support.card - 1) + 1) :=
      congrArg (fun j : ℕ => (z.val : Kˣ) ^ j) (Nat.sub_add_cancel hp).symm
    _ = z.val := by rw [pow_succ, hz, one_mul]

private noncomputable def cycleRealization (c : β.cycleFactorsFinset)
    (z : rootsOfUnity (2 ^ c.val.support.card - 1) K) : SquareAssignments (K := K) β := by
  classical
  refine ⟨fun q => if hq : q ∈ c.val.support then
    z.val ^ (2 ^ cyclePosition β c q hq) else 1, ?_⟩
  intro q
  have hc := Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset c.property
  by_cases hq : q ∈ c.val.support
  · have hbq : β q ∈ c.val.support := hc.apply_mem_iff.mpr hq
    simp only [dif_pos hq, dif_pos hbq]
    rw [position_successor β c q hq hbq]
    have hk := (position_spec β c q hq).1
    by_cases hlt : cyclePosition β c q hq + 1 < c.val.support.card
    · rw [Nat.mod_eq_of_lt hlt, Nat.pow_succ, pow_mul]
    · have he : cyclePosition β c q hq + 1 = c.val.support.card := by omega
      rw [he, Nat.mod_self]
      simp only [pow_zero, pow_one]
      rw [← pow_mul, ← Nat.pow_succ]
      change (z.val : Kˣ) = z.val ^ (2 ^ (cyclePosition β c q hq + 1))
      rw [he, root_power_return]
  · have hbq : β q ∉ c.val.support := fun h => hq (hc.apply_mem_iff.mp h)
    simp [hq, hbq]

private theorem cycleRealization_at (c : β.cycleFactorsFinset)
    (z : rootsOfUnity (2 ^ c.val.support.card - 1) K) :
    (cycleRealization β c z).val (cycleRepresentative β c) = z.val := by
  dsimp only [cycleRealization]
  rw [dif_pos (representative_mem β c), position_representative]
  simp

/-- Independent choices of roots on the successor cycles, with fixed points forced to one. -/
noncomputable def cycleEvaluationEquiv : SquareAssignments (K := K) β ≃
    (∀ c : β.cycleFactorsFinset, rootsOfUnity (2 ^ c.val.support.card - 1) K) where
  toFun v c := ⟨v.val (cycleRepresentative β c), (mem_rootsOfUnity _ _).mpr (cycle_root β v c)⟩
  invFun z := ⟨fun q => ∏ c : β.cycleFactorsFinset, (cycleRealization β c (z c)).val q, by
    intro q
    simp only [(cycleRealization β _ _).property q, Finset.prod_pow]⟩
  left_inv v := by
    apply cycle_evaluation_injective β
    funext c
    change (∏ d : β.cycleFactorsFinset,
      (cycleRealization β d _).val (cycleRepresentative β c)) = _
    rw [Finset.prod_eq_single c]
    · exact cycleRealization_at β c _
    · intro d hd hdc
      have hdis := (β.cycleFactorsFinset_pairwise_disjoint d.property c.property
        (Subtype.coe_ne_coe.mpr hdc)).disjoint_support
      have hn : cycleRepresentative β c ∉ d.val.support := by
        intro h
        exact Finset.disjoint_left.mp hdis h (representative_mem β c)
      dsimp only [cycleRealization]
      rw [dif_neg hn]
    · simp
  right_inv z := by
    funext c
    apply Subtype.ext
    change (∏ d : β.cycleFactorsFinset,
      (cycleRealization β d (z d)).val (cycleRepresentative β c)) = (z c).val
    rw [Finset.prod_eq_single c]
    · exact cycleRealization_at β c _
    · intro d hd hdc
      have hdis := (β.cycleFactorsFinset_pairwise_disjoint d.property c.property
        (Subtype.coe_ne_coe.mpr hdc)).disjoint_support
      have hn : cycleRepresentative β c ∉ d.val.support := by
        intro h
        exact Finset.disjoint_left.mp hdis h (representative_mem β c)
      dsimp only [cycleRealization]
      rw [dif_neg hn]
    · simp

/-- The exact complex diagonal assignment cardinality, including the neutral singleton factors. -/
theorem square_assignments_cycle_card :
    Nat.card (SquareAssignments (K := ℂ) β) =
      ∏ c : β.cycleFactorsFinset, (2 ^ c.val.support.card - 1) := by
  classical
  rw [Nat.card_congr (cycleEvaluationEquiv (K := ℂ) β), Nat.card_pi]
  apply Finset.prod_congr rfl
  intro c hc
  have hl := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.property).1.two_le_card_support
  have hp : 2 ≤ 2 ^ c.val.support.card := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      (show 1 ≤ c.val.support.card by omega)
  letI : NeZero (2 ^ c.val.support.card - 1) := ⟨by omega⟩
  exact Complex.card_rootsOfUnity _

end CycleCount


/-- Product of the root factors on the permutation's nontrivial cycles.
The omitted singleton cycles have factor one. -/
noncomputable def cycleWeight [Finite Q] (β : Equiv.Perm Q) : ℕ := by
  classical
  letI := Fintype.ofFinite Q
  exact ∏ c : β.cycleFactorsFinset, (2 ^ c.val.support.card - 1)

theorem square_assignments_weight_card [Finite Q] (β : Equiv.Perm Q) :
    Nat.card (SquareAssignments (K := ℂ) β) = cycleWeight β := by
  classical
  letI := Fintype.ofFinite Q
  exact square_assignments_cycle_card β

end D5.S3.FiniteGroups.SuccessorPowerAssignments
