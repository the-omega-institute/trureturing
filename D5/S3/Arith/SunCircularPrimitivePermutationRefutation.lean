/- GID: D5/S3/Arith/SunCircularPrimitivePermutationRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/SunCircularPrimitivePermutationRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/SunCircularPrimitivePermutationRefutation.claim; result=D5/S3/Arith/SunCircularPrimitivePermutationRefutation.result; claim=D5/S3/Arith/SunCircularPrimitivePermutationRefutation.claim
   digest: Two vertices with the same two possible neighbours obstruct Sun's circular primitive permutation over the field of eleven elements. -/

import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.SplitIfs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.SunCircularPrimitivePermutationRefutation

/-- Sun's circular primitive permutation conjecture, with every nonzero element
appearing exactly once and the last position adjacent to the first. -/
def claim : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
    7 < Fintype.card F → ∀ a₀ : F,
      ∃ e : Fin (Fintype.card F - 1) ≃ {x : F // x ≠ 0},
        ∀ i, IsPrimitiveRoot
          (a₀ + (e i : F) * (e (finRotate _ i) : F)) (Fintype.card F - 1)

/-- In a cycle of length greater than four, two distinct vertices cannot both
have their predecessor and successor in one set of at most two vertices. -/
theorem twin_neighbour_obstruction {α : Type*} [DecidableEq α]
    {m : ℕ} (hm : 4 < m) (e : Fin m ≃ α) (u w : α) (huw : u ≠ w)
    (S : Finset α) (hS : S.card ≤ 2)
    (hu : e (finRotate m (e.symm u)) ∈ S ∧
      e ((finRotate m).symm (e.symm u)) ∈ S)
    (hw : e (finRotate m (e.symm w)) ∈ S ∧
      e ((finRotate m).symm (e.symm w)) ∈ S) : False := by
  cases m with
  | zero => omega
  | succ n =>
    have next_val (i : Fin (n + 1)) :
        (finRotate (n + 1) i).val = if i.val = n then 0 else i.val + 1 := by
      rw [coe_finRotate]
      simp only [Fin.ext_iff, Fin.val_last]
    have distinct (i : Fin (n + 1)) :
        e (finRotate (n + 1) i) ≠ e ((finRotate (n + 1)).symm i) := by
      intro he
      have hi := congrArg Fin.val (e.injective he)
      have hc := congrArg Fin.val ((finRotate (n + 1)).apply_symm_apply i)
      have hnext := next_val i
      have hprev := next_val ((finRotate (n + 1)).symm i)
      have hlt := i.isLt
      have hplt := ((finRotate (n + 1)).symm i).isLt
      split_ifs at hnext hprev <;> omega
    have pair_eq (i : Fin (n + 1))
        (hi : e (finRotate (n + 1) i) ∈ S ∧
          e ((finRotate (n + 1)).symm i) ∈ S) :
        {e (finRotate (n + 1) i), e ((finRotate (n + 1)).symm i)} = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hi.1
        · exact hi.2
      · rw [Finset.card_pair (distinct i)]
        exact hS
    have hpairs := (pair_eq (e.symm u) hu).trans (pair_eq (e.symm w) hw).symm
    have hnext : e (finRotate (n + 1) (e.symm u)) ∈
        ({e (finRotate (n + 1) (e.symm w)),
          e ((finRotate (n + 1)).symm (e.symm w))} : Finset α) := by
      rw [← hpairs]
      simp
    have hprev : e ((finRotate (n + 1)).symm (e.symm u)) ∈
        ({e (finRotate (n + 1) (e.symm w)),
          e ((finRotate (n + 1)).symm (e.symm w))} : Finset α) := by
      rw [← hpairs]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton, e.injective.eq_iff] at hnext hprev
    rcases hnext with hnext | hnext
    · exact huw (e.symm.injective ((finRotate (n + 1)).injective hnext))
    rcases hprev with hprev | hprev
    · have hn := congrArg Fin.val hnext
      have hp := congrArg Fin.val hprev
      have huc := congrArg Fin.val ((finRotate (n + 1)).apply_symm_apply (e.symm u))
      have hwc := congrArg Fin.val ((finRotate (n + 1)).apply_symm_apply (e.symm w))
      have hun := next_val (e.symm u)
      have hwn := next_val (e.symm w)
      have hup := next_val ((finRotate (n + 1)).symm (e.symm u))
      have hwp := next_val ((finRotate (n + 1)).symm (e.symm w))
      have hu_lt := (e.symm u).isLt
      have hw_lt := (e.symm w).isLt
      have hup_lt := ((finRotate (n + 1)).symm (e.symm u)).isLt
      have hwp_lt := ((finRotate (n + 1)).symm (e.symm w)).isLt
      split_ifs at hun hwn hup hwp <;> omega
    · exact huw (e.symm.injective ((finRotate (n + 1)).symm.injective hprev))

private theorem primitive_eleven (z : ZMod 11) (hz : IsPrimitiveRoot z 10) :
    z ∈ ({2, 6, 7, 8} : Finset (ZMod 11)) := by
  let : Fact (1 < 11) := ⟨by decide⟩
  have hcert : ∀ z : ZMod 11,
      z ∈ ({2, 6, 7, 8} : Finset (ZMod 11)) ∨ z = 0 ∨ z ^ 5 = 1 ∨ z ^ 2 = 1 := by
    decide
  rcases hcert z with h | h | h | h
  · exact h
  · exact False.elim (hz.ne_zero (by decide) h)
  · exact False.elim (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide) h)
  · exact False.elim (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide) h)

/-- At eleven elements and offset two, the vertices two and nine both require
the neighbours three and eight, which cannot occur in a ten-cycle. -/
theorem result : ¬ claim := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  intro h
  have hcard : Fintype.card (ZMod 11) = 11 := ZMod.card 11
  have hs := h (ZMod 11) (by rw [hcard]; decide) 2
  rw [hcard] at hs
  obtain ⟨e, he⟩ := hs
  let u : {x : ZMod 11 // x ≠ 0} := ⟨2, by decide⟩
  let w : {x : ZMod 11 // x ≠ 0} := ⟨9, by decide⟩
  let S : Finset {x : ZMod 11 // x ≠ 0} := {⟨3, by decide⟩, ⟨8, by decide⟩}
  have no_fixed : ∀ i : Fin 10, finRotate 10 i ≠ i ∧ (finRotate 10).symm i ≠ i := by
    decide
  have forced : ∀ x y : ZMod 11, (x = 2 ∨ x = 9) → y ≠ 0 →
      y ≠ x → 2 + x * y ∈ ({2, 6, 7, 8} : Finset (ZMod 11)) → y = 3 ∨ y = 8 := by
    decide
  have neighbours (x : {x : ZMod 11 // x ≠ 0}) (hx : x.val = 2 ∨ x.val = 9) :
      e (finRotate 10 (e.symm x)) ∈ S ∧
      e ((finRotate 10).symm (e.symm x)) ∈ S := by
    have different (j : Fin 10) (hj : j ≠ e.symm x) : (e j).val ≠ x.val := by
      intro hval
      apply hj
      apply e.injective
      apply Subtype.ext
      simpa using hval
    constructor
    · have hp := primitive_eleven _ (he (e.symm x))
      rw [e.apply_symm_apply] at hp
      have hy := forced _ _ hx (e (finRotate 10 (e.symm x))).property
        (different _ (no_fixed (e.symm x)).1) hp
      simpa [S, Subtype.ext_iff] using hy
    · have hp := primitive_eleven _ (he ((finRotate 10).symm (e.symm x)))
      rw [Equiv.apply_symm_apply, e.apply_symm_apply, mul_comm] at hp
      have hy := forced _ _ hx (e ((finRotate 10).symm (e.symm x))).property
        (different _ (no_fixed (e.symm x)).2) hp
      simpa [S, Subtype.ext_iff] using hy
  exact twin_neighbour_obstruction (by decide) e u w (by decide) S
    (by decide) (neighbours u (Or.inl rfl)) (neighbours w (Or.inr rfl))

end D5.S3.Arith.SunCircularPrimitivePermutationRefutation
