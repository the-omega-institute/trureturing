/- GID: D5/S3/Combinatorics/Posets/GradedGamma/OrdinalSumProduct
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Posets/GradedGamma/OrdinalSumProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Fin.Tuple.Basic]
   utility: none
   digest: Ordinal-sum extensions split into both block extensions and their descents. -/

import D5.S3.Combinatorics.Posets.GradedGamma.OrdinalSumPartitions
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Interval.Finset.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Posets.GradedGamma

open D5.S3.Combinatorics.Posets.PPartitions
noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β]
    [PartialOrder α] [PartialOrder β]

private theorem lexCard :
    Fintype.card (α ⊕ₗ β) = Fintype.card α + Fintype.card β := by
  exact (Fintype.card_congr (ofLex : α ⊕ₗ β ≃ α ⊕ β)).trans Fintype.card_sum

def ordinalAppendExtension (u : EnumeratingExtension α)
    (v : EnumeratingExtension β) : EnumeratingExtension (α ⊕ₗ β) := by
  let ev : Fin (Fintype.card (α ⊕ₗ β)) ≃ α ⊕ₗ β :=
    (finCongr lexCard).trans <|
      finSumFinEquiv.symm.trans ((Equiv.sumCongr u.1 v.1).trans toLex)
  have hleft (x : α) : ev.symm (toLex (.inl x)) =
      (finCongr lexCard).symm
        (Fin.castAdd (Fintype.card β) (u.1.symm x)) := by
    rfl
  have hright (y : β) : ev.symm (toLex (.inr y)) =
      (finCongr lexCard).symm
        (Fin.natAdd (Fintype.card α) (v.1.symm y)) := by
    rfl
  refine ⟨ev, ?_⟩
  intro x y hxy
  induction x using Lex.rec with
  | h sx =>
    induction y using Lex.rec with
    | h sy =>
      cases sx with
      | inl x =>
        cases sy with
        | inl y =>
          have h := u.2 (Sum.Lex.inl_lt_inl_iff.mp hxy)
          rw [hleft x, hleft y]
          apply Fin.lt_def.mpr
          change (u.1.symm x).val < (u.1.symm y).val
          exact Fin.lt_def.mp h
        | inr y =>
          rw [hleft x, hright y]
          apply Fin.lt_def.mpr
          change (u.1.symm x).val < Fintype.card α + (v.1.symm y).val
          omega
      | inr x =>
        cases sy with
        | inl y => exact False.elim (Sum.Lex.not_inr_lt_inl hxy)
        | inr y =>
          have h := v.2 (Sum.Lex.inr_lt_inr_iff.mp hxy)
          rw [hright x, hright y]
          apply Fin.lt_def.mpr
          change Fintype.card α + (v.1.symm x).val <
            Fintype.card α + (v.1.symm y).val
          omega

private theorem ordinalAppendExtension_left (u : EnumeratingExtension α)
    (v : EnumeratingExtension β) (i : Fin (Fintype.card α)) :
    (ordinalAppendExtension u v)
      ((finCongr lexCard).symm (Fin.castAdd (Fintype.card β) i)) =
        toLex (.inl (u i)) := by
  change ((finCongr lexCard).trans
    (finSumFinEquiv.symm.trans ((Equiv.sumCongr u.1 v.1).trans toLex)))
      ((finCongr lexCard).symm (Fin.castAdd (Fintype.card β) i)) = _
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply,
    finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply]
  rfl

private theorem ordinalAppendExtension_right (u : EnumeratingExtension α)
    (v : EnumeratingExtension β) (j : Fin (Fintype.card β)) :
    (ordinalAppendExtension u v)
      ((finCongr lexCard).symm (Fin.natAdd (Fintype.card α) j)) =
        toLex (.inr (v j)) := by
  change ((finCongr lexCard).trans
    (finSumFinEquiv.symm.trans ((Equiv.sumCongr u.1 v.1).trans toLex)))
      ((finCongr lexCard).symm (Fin.natAdd (Fintype.card α) j)) = _
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply,
    finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply]
  rfl

private theorem rightPosition_ge (e : EnumeratingExtension (α ⊕ₗ β))
    (y : β) : Fintype.card α ≤
      (e.1.symm (toLex (.inr y))).val := by
  classical
  let position : α → Fin (Fintype.card (α ⊕ₗ β)) :=
    fun x => e.1.symm (toLex (.inl x))
  have hmaps : Set.MapsTo position (Finset.univ : Finset α)
      (Finset.Iio (e.1.symm (toLex (.inr y)))) := by
    intro x _
    simpa only [Finset.mem_coe, Finset.mem_Iio] using
      (e.2 (Sum.Lex.inl_lt_inr x y))
  have hinj : Function.Injective position := by
    intro x z hx
    exact Sum.inl_injective (ofLex.injective (e.1.symm.injective hx))
  have hcard := Finset.card_le_card_of_injOn position hmaps
    (fun x _ z _ hx => hinj hx)
  simpa only [Finset.card_univ, Fin.card_Iio] using hcard

private theorem leftAt (e : EnumeratingExtension (α ⊕ₗ β))
    (i : Fin (Fintype.card α)) :
    ∃ x : α, e
      ((finCongr lexCard).symm (Fin.castAdd (Fintype.card β) i)) =
        toLex (.inl x) := by
  let k := (finCongr lexCard).symm (Fin.castAdd (Fintype.card β) i)
  cases h : ofLex (e k) with
  | inl x => exact ⟨x, by simpa [k] using congrArg toLex h⟩
  | inr y =>
      have he : e.1.symm (toLex (.inr y)) = k := by
        have h' : e k = toLex (.inr y) := by simpa using congrArg toLex h
        exact h' ▸ e.1.symm_apply_apply k
      have hb := rightPosition_ge e y
      rw [he] at hb
      have hi := i.isLt
      change Fintype.card α ≤ i.val at hb
      omega

private def leftRestriction (e : EnumeratingExtension (α ⊕ₗ β)) :
    Fin (Fintype.card α) → α :=
  fun i => Classical.choose (leftAt e i)

private theorem leftRestriction_spec (e : EnumeratingExtension (α ⊕ₗ β))
    (i : Fin (Fintype.card α)) :
    e ((finCongr lexCard).symm (Fin.castAdd (Fintype.card β) i)) =
      toLex (.inl (leftRestriction e i)) :=
  Classical.choose_spec (leftAt e i)

private theorem leftRestriction_bijective
    (e : EnumeratingExtension (α ⊕ₗ β)) :
    Function.Bijective (leftRestriction e) := by
  apply (Fintype.bijective_iff_injective_and_card (leftRestriction e)).2
  constructor
  · intro i j hij
    have he : e.1
        ((finCongr lexCard).symm (Fin.castAdd (Fintype.card β) i)) =
        e.1 ((finCongr lexCard).symm (Fin.castAdd (Fintype.card β) j)) := by
      rw [leftRestriction_spec, leftRestriction_spec, hij]
    have hpos := e.1.injective he
    have hcast := (finCongr lexCard).symm.injective hpos
    exact (Fin.castAdd_injective _ _) hcast
  · simp

private theorem rightAt (e : EnumeratingExtension (α ⊕ₗ β))
    (j : Fin (Fintype.card β)) :
    ∃ y : β, e
      ((finCongr lexCard).symm (Fin.natAdd (Fintype.card α) j)) =
        toLex (.inr y) := by
  let k := (finCongr lexCard).symm (Fin.natAdd (Fintype.card α) j)
  cases h : ofLex (e k) with
  | inr y => exact ⟨y, by simpa [k] using congrArg toLex h⟩
  | inl x =>
      obtain ⟨i, hi⟩ := (leftRestriction_bijective e).2 x
      have h' : e k = toLex (.inl x) := by simpa using congrArg toLex h
      have he : e
          ((finCongr lexCard).symm (Fin.castAdd (Fintype.card β) i)) =
          e k := by rw [leftRestriction_spec, hi, h']
      have hp := e.1.injective he
      have hc := (finCongr lexCard).symm.injective hp
      have hv := congrArg Fin.val hc
      change i.val = Fintype.card α + j.val at hv
      omega

private def rightRestriction (e : EnumeratingExtension (α ⊕ₗ β)) :
    Fin (Fintype.card β) → β :=
  fun j => Classical.choose (rightAt e j)

private theorem rightRestriction_spec (e : EnumeratingExtension (α ⊕ₗ β))
    (j : Fin (Fintype.card β)) :
    e ((finCongr lexCard).symm (Fin.natAdd (Fintype.card α) j)) =
      toLex (.inr (rightRestriction e j)) :=
  Classical.choose_spec (rightAt e j)

private theorem rightRestriction_bijective
    (e : EnumeratingExtension (α ⊕ₗ β)) :
    Function.Bijective (rightRestriction e) := by
  apply (Fintype.bijective_iff_injective_and_card (rightRestriction e)).2
  constructor
  · intro i j hij
    have he : e.1
        ((finCongr lexCard).symm (Fin.natAdd (Fintype.card α) i)) =
        e.1 ((finCongr lexCard).symm (Fin.natAdd (Fintype.card α) j)) := by
      rw [rightRestriction_spec, rightRestriction_spec, hij]
    have hpos := e.1.injective he
    have hcast := (finCongr lexCard).symm.injective hpos
    apply Fin.ext
    have hv := congrArg Fin.val hcast
    change Fintype.card α + i.val = Fintype.card α + j.val at hv
    omega
  · simp

private def leftExtension (e : EnumeratingExtension (α ⊕ₗ β)) :
    EnumeratingExtension α := by
  let f : Fin (Fintype.card α) ≃ α :=
    Equiv.ofBijective (leftRestriction e) (leftRestriction_bijective e)
  refine ⟨f, ?_⟩
  intro x y hxy
  have hp := e.2 (Sum.Lex.inl_lt_inl_iff.mpr hxy)
  have hx : e.1.symm (toLex (.inl x)) =
      (finCongr lexCard).symm
        (Fin.castAdd (Fintype.card β) (f.symm x)) := by
    apply e.1.injective
    rw [e.1.apply_symm_apply]
    rw [leftRestriction_spec]
    exact congrArg (fun t : α => toLex (Sum.inl t))
      (f.apply_symm_apply x).symm
  have hy : e.1.symm (toLex (.inl y)) =
      (finCongr lexCard).symm
        (Fin.castAdd (Fintype.card β) (f.symm y)) := by
    apply e.1.injective
    rw [e.1.apply_symm_apply]
    rw [leftRestriction_spec]
    exact congrArg (fun t : α => toLex (Sum.inl t))
      (f.apply_symm_apply y).symm
  rw [hx, hy] at hp
  apply Fin.lt_def.mpr
  have hv := Fin.lt_def.mp hp
  change (f.symm x).val < (f.symm y).val at hv
  exact hv

private def rightExtension (e : EnumeratingExtension (α ⊕ₗ β)) :
    EnumeratingExtension β := by
  let f : Fin (Fintype.card β) ≃ β :=
    Equiv.ofBijective (rightRestriction e) (rightRestriction_bijective e)
  refine ⟨f, ?_⟩
  intro x y hxy
  have hp := e.2 (Sum.Lex.inr_lt_inr_iff.mpr hxy)
  have hx : e.1.symm (toLex (.inr x)) =
      (finCongr lexCard).symm
        (Fin.natAdd (Fintype.card α) (f.symm x)) := by
    apply e.1.injective
    rw [e.1.apply_symm_apply]
    rw [rightRestriction_spec]
    exact congrArg (fun t : β => toLex (Sum.inr t))
      (f.apply_symm_apply x).symm
  have hy : e.1.symm (toLex (.inr y)) =
      (finCongr lexCard).symm
        (Fin.natAdd (Fintype.card α) (f.symm y)) := by
    apply e.1.injective
    rw [e.1.apply_symm_apply]
    rw [rightRestriction_spec]
    exact congrArg (fun t : β => toLex (Sum.inr t))
      (f.apply_symm_apply y).symm
  rw [hx, hy] at hp
  apply Fin.lt_def.mpr
  have hv := Fin.lt_def.mp hp
  change Fintype.card α + (f.symm x).val <
    Fintype.card α + (f.symm y).val at hv
  omega

/-- Every linear extension of an ordinal sum is exactly a pair of linear
extensions of the two blocks. -/
def ordinalExtensionEquiv :
    EnumeratingExtension (α ⊕ₗ β) ≃
      EnumeratingExtension α × EnumeratingExtension β := by
  let join : EnumeratingExtension α × EnumeratingExtension β →
      EnumeratingExtension (α ⊕ₗ β) :=
    fun p => ordinalAppendExtension p.1 p.2
  have hinj : Function.Injective join := by
    intro p q hpq
    rcases p with ⟨u, v⟩
    rcases q with ⟨u', v'⟩
    have hu : u = u' := by
      apply Subtype.ext
      apply Equiv.ext
      intro i
      have h := congrArg (fun e : EnumeratingExtension (α ⊕ₗ β) =>
        e ((finCongr lexCard).symm (Fin.castAdd (Fintype.card β) i))) hpq
      rw [ordinalAppendExtension_left, ordinalAppendExtension_left] at h
      exact Sum.inl_injective (ofLex.injective h)
    have hv : v = v' := by
      apply Subtype.ext
      apply Equiv.ext
      intro j
      have h := congrArg (fun e : EnumeratingExtension (α ⊕ₗ β) =>
        e ((finCongr lexCard).symm (Fin.natAdd (Fintype.card α) j))) hpq
      rw [ordinalAppendExtension_right, ordinalAppendExtension_right] at h
      exact Sum.inr_injective (ofLex.injective h)
    exact Prod.ext hu hv
  have hsurj : Function.Surjective join := by
    intro e
    refine ⟨(leftExtension e, rightExtension e), ?_⟩
    change ordinalAppendExtension (leftExtension e) (rightExtension e) = e
    apply Subtype.ext
    apply Equiv.ext
    intro k
    have h (t : Fin (Fintype.card α + Fintype.card β)) :
        (ordinalAppendExtension (leftExtension e) (rightExtension e))
          ((finCongr lexCard).symm t) =
        e ((finCongr lexCard).symm t) := by
      refine Fin.addCases (fun i => ?_) (fun j => ?_) t
      · calc
          (ordinalAppendExtension (leftExtension e) (rightExtension e))
              ((finCongr lexCard).symm (Fin.castAdd (Fintype.card β) i)) =
            toLex (.inl (leftExtension e i)) := ordinalAppendExtension_left _ _ i
          _ = e ((finCongr lexCard).symm
              (Fin.castAdd (Fintype.card β) i)) := by
            exact (leftRestriction_spec e i).symm
      · calc
          (ordinalAppendExtension (leftExtension e) (rightExtension e))
              ((finCongr lexCard).symm (Fin.natAdd (Fintype.card α) j)) =
            toLex (.inr (rightExtension e j)) := ordinalAppendExtension_right _ _ j
          _ = e ((finCongr lexCard).symm
              (Fin.natAdd (Fintype.card α) j)) := by
            exact (rightRestriction_spec e j).symm
    simpa only [Equiv.symm_apply_apply] using h (finCongr lexCard k)
  exact (Equiv.ofBijective join ⟨hinj, hsurj⟩).symm

end
end D5.S3.Combinatorics.Posets.GradedGamma
