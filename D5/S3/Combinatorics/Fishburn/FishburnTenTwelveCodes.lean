/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenTwelveCodes
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenTwelveCodes
   mirror-E: none(waiver:two-transition-path-code-bijection)
   anchors: []
   utility: none
   digest: Nonzero state walks have one straight code or a unique ordered pair of turn codes. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenTwelvePaths

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenTwelveCodes

open D5.S3.Combinatorics.Fishburn.FishburnTenTwelveSuccession
open D5.S3.Combinatorics.Fishburn.FishburnTenTwelvePaths

theorem walk_codes (steps : ℕ) :
    Nonempty ((Walk .B steps ≃ PUnit.{1}) ×
      (Walk .D steps ≃ Fin (steps + 1)) ×
      (Walk .C steps ≃
        Option {pair : Fin (steps + 1) × Fin (steps + 1) // pair.1 < pair.2}) ×
      (Walk .A steps ≃ Option {pair : Fin steps × Fin steps // pair.1 < pair.2})) := by
  induction steps with
  | zero =>
    have hempty (bound : ℕ) (hsmall : bound ≤ 1) :
        PUnit.{1} ≃ Option {pair : Fin bound × Fin bound // pair.1 < pair.2} := {
      toFun := fun _ => none
      invFun := fun _ => PUnit.unit
      left_inv := fun base => by cases base; rfl
      right_inv := fun code => by
        cases code with
        | none => rfl
        | some pair =>
          have hfirst := pair.val.1.isLt
          have hsecond := pair.val.2.isLt
          have horder := pair.property
          change pair.val.1.val < pair.val.2.val at horder
          omega }
    have hone : PUnit.{1} ≃ Fin 1 := {
      toFun := fun _ => 0
      invFun := fun _ => PUnit.unit
      left_inv := fun base => by cases base; rfl
      right_inv := fun index => by apply Fin.ext; have hb := index.isLt; omega }
    exact ⟨Equiv.refl PUnit, hone, hempty 1 (by omega), hempty 0 (by omega)⟩
  | succ steps ih =>
    obtain ⟨bcode, dcode, ccode, _⟩ := ih
    let appendLast : Fin (steps + 1) ⊕ PUnit.{1} ≃ Fin (steps + 2) := {
      toFun := fun code => match code with
        | Sum.inl index => index.castSucc
        | Sum.inr _ => Fin.last (steps + 1)
      invFun := fun index =>
        if hbound : index.val < steps + 1 then Sum.inl ⟨index.val, hbound⟩
        else Sum.inr PUnit.unit
      left_inv := fun code => by
        cases code with
        | inl index => simp only [Fin.val_castSucc, dif_pos index.isLt]
        | inr base =>
          cases base
          simp only [Fin.val_last, lt_self_iff_false, dite_false]
      right_inv := fun index => by
        by_cases hbound : index.val < steps + 1
        · simp only [dif_pos hbound]
          rfl
        · simp only [dif_neg hbound]
          apply Fin.ext
          have hb := index.isLt
          simp only [Fin.val_last]
          omega }
    let appendPair :
        (Option {pair : Fin (steps + 1) × Fin (steps + 1) // pair.1 < pair.2} ⊕
          Fin (steps + 1)) ≃
            Option {pair : Fin (steps + 2) × Fin (steps + 2) // pair.1 < pair.2} := {
      toFun := fun code => match code with
        | Sum.inl none => none
        | Sum.inl (some pair) =>
          some ⟨(pair.val.1.castSucc, pair.val.2.castSucc), pair.property⟩
        | Sum.inr index =>
          some ⟨(index.castSucc, Fin.last (steps + 1)), index.isLt⟩
      invFun := fun code => match code with
        | none => Sum.inl none
        | some pair =>
          if hbound : pair.val.2.val < steps + 1 then
            Sum.inl (some ⟨(⟨pair.val.1.val, by
              have horder := pair.property
              change pair.val.1.val < pair.val.2.val at horder
              omega⟩, ⟨pair.val.2.val, hbound⟩), pair.property⟩)
          else Sum.inr ⟨pair.val.1.val, by
            have horder := pair.property
            change pair.val.1.val < pair.val.2.val at horder
            have hsecond := pair.val.2.isLt
            omega⟩
      left_inv := fun code => by
        cases code with
        | inl oldcode =>
          cases oldcode with
          | none => rfl
          | some pair =>
            simp only [Fin.val_castSucc, dif_pos pair.val.2.isLt]
        | inr index =>
          simp only [Fin.val_last, dif_neg (Nat.lt_irrefl (steps + 1))]
          rfl
      right_inv := fun code => by
        cases code with
        | none => rfl
        | some pair =>
          by_cases hbound : pair.val.2.val < steps + 1
          · simp only [dif_pos hbound]
            apply congrArg some
            apply Subtype.ext
            exact Prod.ext (Fin.ext rfl) (Fin.ext rfl)
          · simp only [dif_neg hbound]
            apply congrArg some
            apply Subtype.ext
            refine Prod.ext ?_ ?_
            · apply Fin.ext
              rfl
            · apply Fin.ext
              have hb := pair.val.2.isLt
              simp only [Fin.val_last]
              omega }
    exact ⟨bcode, (Equiv.sumCongr dcode bcode).trans appendLast,
      (Equiv.sumCongr ccode dcode).trans appendPair, ccode⟩

end D5.S3.Combinatorics.Fishburn.FishburnTenTwelveCodes
