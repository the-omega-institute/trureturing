/- GID: D5/S3/Combinatorics/Posets/GradedGamma/OrdinalSumPartitions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Posets/GradedGamma/OrdinalSumPartitions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Sum.Order]
   utility: none
   digest: Partitions of a labelled ordinal sum split at their cross-block bound. -/

import D5.S3.Combinatorics.Posets.PPartitions.Series
import Mathlib.Data.Sum.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Posets.GradedGamma

open D5.S3.Combinatorics.Posets.PPartitions
noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β]
    [PartialOrder α] [PartialOrder β]

def weakSumLabel (ω : α → ℕ) (ν : β → ℕ) (x : α ⊕ₗ β) : ℕ :=
  match ofLex x with
  | .inl a => ω a
  | .inr b => Fintype.card α + ν b

def strictSumLabel (ω : α → ℕ) (ν : β → ℕ) (x : α ⊕ₗ β) : ℕ :=
  match ofLex x with
  | .inl a => Fintype.card β + ω a
  | .inr b => ν b

def directSumLabel (ω : α → ℕ) (ν : β → ℕ) (x : α ⊕ₗ β) : ℕ :=
  match ofLex x with
  | .inl a => ω a
  | .inr b => ν b

/-- A weakly joined partition is a pair of partitions whose left values
dominate every right value. -/
def weakSumPartitionEquiv (ω : α → ℕ) (ν : β → ℕ)
    (hω : ∀ x, ω x < Fintype.card α) (bound : ℕ) :
    PPartition (weakSumLabel ω ν) bound ≃
      {p : PPartition ω bound × PPartition ν bound //
        ∀ x y, (p.2.1 y) ≤ (p.1.1 x)} := by
  let forward (p : PPartition (weakSumLabel ω ν) bound) :
      {v : PPartition ω bound × PPartition ν bound //
        ∀ x y, (v.2.1 y) ≤ (v.1.1 x)} := by
    let left : PPartition ω bound := ⟨fun x => p.1 (toLex (.inl x)), by
      constructor
      · intro x y hxy
        exact p.2.1 (Sum.Lex.inl_le_inl_iff.mpr hxy)
      · intro x y hxy hlabel
        exact p.2.2 (Sum.Lex.inl_lt_inl_iff.mpr hxy)
          (by simpa [weakSumLabel] using hlabel)⟩
    let right : PPartition ν bound := ⟨fun y => p.1 (toLex (.inr y)), by
      constructor
      · intro x y hxy
        exact p.2.1 (Sum.Lex.inr_le_inr_iff.mpr hxy)
      · intro x y hxy hlabel
        exact p.2.2 (Sum.Lex.inr_lt_inr_iff.mpr hxy)
          (by simpa [weakSumLabel] using
            (show Fintype.card α + ν y < Fintype.card α + ν x by omega))⟩
    exact ⟨(left, right), fun x y =>
      p.2.1 (Sum.Lex.inl_le_inr x y)⟩
  let backward (v : {p : PPartition ω bound × PPartition ν bound //
        ∀ x y, (p.2.1 y) ≤ (p.1.1 x)}) :
      PPartition (weakSumLabel ω ν) bound := by
    refine ⟨fun z => match ofLex z with
      | .inl x => v.1.1.1 x
      | .inr y => v.1.2.1 y, ?_, ?_⟩
    · intro x y hxy
      induction x using Lex.rec with
      | h sx =>
        induction y using Lex.rec with
        | h sy =>
          cases sx with
          | inl x =>
            cases sy with
            | inl y => exact v.1.1.2.1 (Sum.Lex.inl_le_inl_iff.mp hxy)
            | inr y => exact v.2 x y
          | inr x =>
            cases sy with
            | inl y => exact False.elim (Sum.Lex.not_inr_le_inl hxy)
            | inr y => exact v.1.2.2.1 (Sum.Lex.inr_le_inr_iff.mp hxy)
    · intro x y hxy hlabel
      induction x using Lex.rec with
      | h sx =>
        induction y using Lex.rec with
        | h sy =>
          cases sx with
          | inl x =>
            cases sy with
            | inl y => exact v.1.1.2.2 (Sum.Lex.inl_lt_inl_iff.mp hxy) hlabel
            | inr y =>
              have hb := hω x
              have hn : Fintype.card α + ν y < ω x := by
                simpa [weakSumLabel] using hlabel
              omega
          | inr x =>
            cases sy with
            | inl y => exact False.elim (Sum.Lex.not_inr_lt_inl hxy)
            | inr y =>
              have hn : ν y < ν x := by simpa [weakSumLabel] using hlabel
              exact v.1.2.2.2 (Sum.Lex.inr_lt_inr_iff.mp hxy) hn
  exact {
    toFun := forward
    invFun := backward
    left_inv := by
      intro p
      apply Subtype.ext
      funext z
      induction z using Lex.rec with
      | h sz => cases sz <;> rfl
    right_inv := by
      intro v
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        funext x
        rfl
      · apply Subtype.ext
        funext y
        rfl }

/-- Reversing the label order at the join forces a strict decrease of the
partition value between the two nonempty blocks. -/
def strictSumPartitionEquiv (ω : α → ℕ) (ν : β → ℕ)
    (hν : ∀ y, ν y < Fintype.card β) (bound : ℕ) :
    PPartition (strictSumLabel ω ν) bound ≃
      {p : PPartition ω bound × PPartition ν bound //
        ∀ x y, (p.2.1 y) < (p.1.1 x)} := by
  let forward (p : PPartition (strictSumLabel ω ν) bound) :
      {v : PPartition ω bound × PPartition ν bound //
        ∀ x y, (v.2.1 y) < (v.1.1 x)} := by
    let left : PPartition ω bound := ⟨fun x => p.1 (toLex (.inl x)), by
      constructor
      · intro x y hxy
        exact p.2.1 (Sum.Lex.inl_le_inl_iff.mpr hxy)
      · intro x y hxy hlabel
        exact p.2.2 (Sum.Lex.inl_lt_inl_iff.mpr hxy)
          (by simpa [strictSumLabel] using
            (show Fintype.card β + ω y < Fintype.card β + ω x by omega))⟩
    let right : PPartition ν bound := ⟨fun y => p.1 (toLex (.inr y)), by
      constructor
      · intro x y hxy
        exact p.2.1 (Sum.Lex.inr_le_inr_iff.mpr hxy)
      · intro x y hxy hlabel
        exact p.2.2 (Sum.Lex.inr_lt_inr_iff.mpr hxy)
          (by simpa [strictSumLabel] using hlabel)⟩
    exact ⟨(left, right), fun x y =>
      p.2.2 (Sum.Lex.inl_lt_inr x y) (by
        change ν y < Fintype.card β + ω x
        exact (hν y).trans_le (Nat.le_add_right _ _))⟩
  let backward (v : {p : PPartition ω bound × PPartition ν bound //
        ∀ x y, (p.2.1 y) < (p.1.1 x)}) :
      PPartition (strictSumLabel ω ν) bound := by
    refine ⟨fun z => match ofLex z with
      | .inl x => v.1.1.1 x
      | .inr y => v.1.2.1 y, ?_, ?_⟩
    · intro x y hxy
      induction x using Lex.rec with
      | h sx =>
        induction y using Lex.rec with
        | h sy =>
          cases sx with
          | inl x =>
            cases sy with
            | inl y => exact v.1.1.2.1 (Sum.Lex.inl_le_inl_iff.mp hxy)
            | inr y => exact (v.2 x y).le
          | inr x =>
            cases sy with
            | inl y => exact False.elim (Sum.Lex.not_inr_le_inl hxy)
            | inr y => exact v.1.2.2.1 (Sum.Lex.inr_le_inr_iff.mp hxy)
    · intro x y hxy hlabel
      induction x using Lex.rec with
      | h sx =>
        induction y using Lex.rec with
        | h sy =>
          cases sx with
          | inl x =>
            cases sy with
            | inl y =>
              have hn : ω y < ω x := by simpa [strictSumLabel] using hlabel
              exact v.1.1.2.2 (Sum.Lex.inl_lt_inl_iff.mp hxy) hn
            | inr y => exact v.2 x y
          | inr x =>
            cases sy with
            | inl y => exact False.elim (Sum.Lex.not_inr_lt_inl hxy)
            | inr y => exact v.1.2.2.2 (Sum.Lex.inr_lt_inr_iff.mp hxy) hlabel
  exact {
    toFun := forward
    invFun := backward
    left_inv := by
      intro p
      apply Subtype.ext
      funext z
      induction z using Lex.rec with
      | h sz => cases sz <;> rfl
    right_inv := by
      intro v
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        funext x
        rfl
      · apply Subtype.ext
        funext y
        rfl }

/-- At a strict join, subtracting one from every left value removes exactly
one unit of available height. Both blocks must be nonempty for this inverse. -/
def strictWeakPartitionEquiv [Nonempty α] [Nonempty β]
    (ω : α → ℕ) (ν : β → ℕ)
    (hω : ∀ x, ω x < Fintype.card α)
    (hν : ∀ y, ν y < Fintype.card β) (q : ℕ) :
    PPartition (strictSumLabel ω ν) (q + 1) ≃
      PPartition (weakSumLabel ω ν) q := by
  let strictPairs :=
    {p : PPartition ω (q + 1) × PPartition ν (q + 1) //
      ∀ x y, (p.2.1 y) < (p.1.1 x)}
  let weakPairs :=
    {p : PPartition ω q × PPartition ν q //
      ∀ x y, (p.2.1 y) ≤ (p.1.1 x)}
  let shift : strictPairs ≃ weakPairs := by
    let forward (p : strictPairs) : weakPairs := by
      let y₀ : β := Classical.choice inferInstance
      let x₀ : α := Classical.choice inferInstance
      have hleft (x : α) : 0 < (p.1.1.1 x).val := by
        have hp := p.2 x y₀
        omega
      have hright (y : β) : (p.1.2.1 y).val < q := by
        have hp := p.2 x₀ y
        have hx := (p.1.1.1 x₀).isLt
        omega
      let left : PPartition ω q := ⟨fun x =>
        ⟨(p.1.1.1 x).val - 1, by
          have hx := (p.1.1.1 x).isLt
          have hpos := hleft x
          omega⟩, by
        constructor
        · intro x y hxy
          have hp := p.1.1.2.1 hxy
          have hx := hleft x
          have hy := hleft y
          exact Fin.mk_le_mk.mpr (by omega)
        · intro x y hxy hlabel
          have hp := p.1.1.2.2 hxy hlabel
          have hx := hleft x
          have hy := hleft y
          exact Fin.mk_lt_mk.mpr (by omega)⟩
      let right : PPartition ν q := ⟨fun y =>
        ⟨(p.1.2.1 y).val, hright y⟩, by
        constructor
        · intro x y hxy
          exact Fin.mk_le_mk.mpr (p.1.2.2.1 hxy)
        · intro x y hxy hlabel
          exact Fin.mk_lt_mk.mpr (p.1.2.2.2 hxy hlabel)⟩
      exact ⟨(left, right), by
        intro x y
        have hp := p.2 x y
        have hx := hleft x
        exact Fin.mk_le_mk.mpr (by omega)⟩
    let backward (p : weakPairs) : strictPairs := by
      let left : PPartition ω (q + 1) := ⟨fun x =>
        ⟨(p.1.1.1 x).val + 1, by have hx := (p.1.1.1 x).isLt; omega⟩, by
        constructor
        · intro x y hxy
          exact Fin.mk_le_mk.mpr (by have hp := p.1.1.2.1 hxy; omega)
        · intro x y hxy hlabel
          exact Fin.mk_lt_mk.mpr (by have hp := p.1.1.2.2 hxy hlabel; omega)⟩
      let right : PPartition ν (q + 1) := ⟨fun y =>
        ⟨(p.1.2.1 y).val, by have hy := (p.1.2.1 y).isLt; omega⟩, by
        constructor
        · intro x y hxy
          exact Fin.mk_le_mk.mpr (p.1.2.2.1 hxy)
        · intro x y hxy hlabel
          exact Fin.mk_lt_mk.mpr (p.1.2.2.2 hxy hlabel)⟩
      exact ⟨(left, right), by
        intro x y
        have hp := p.2 x y
        exact Fin.mk_lt_mk.mpr (by omega)⟩
    exact {
      toFun := forward
      invFun := backward
      left_inv := by
        intro p
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext
          funext x
          apply Fin.ext
          dsimp [forward, backward]
          have hx := (forward p).1.1.1 x
          have hp := p.2 x (Classical.choice (inferInstance : Nonempty β))
          change (p.1.1.1 x).val - 1 + 1 = (p.1.1.1 x).val
          omega
        · apply Subtype.ext
          funext y
          rfl
      right_inv := by
        intro p
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext
          funext x
          apply Fin.ext
          change (p.1.1.1 x).val + 1 - 1 = (p.1.1.1 x).val
          omega
        · apply Subtype.ext
          funext y
          rfl }
  exact (strictSumPartitionEquiv ω ν hν (q + 1)).trans <|
    shift.trans (weakSumPartitionEquiv ω ν hω q).symm

end
end D5.S3.Combinatorics.Posets.GradedGamma
