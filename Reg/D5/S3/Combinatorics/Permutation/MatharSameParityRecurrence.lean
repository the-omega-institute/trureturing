import D5.S3.Combinatorics.Permutation.MatharSameParityRecurrence
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

noncomputable section

namespace Reg.D5.S3.Combinatorics.Permutation.MatharSameParityRecurrence
open _root_.D5.S3.Combinatorics.Permutation.MatharSameParityRecurrence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

abbrev bad : Realization signature :=
  realize signature (fun _ _ n => if n = 4 then a n + 1 else a n) (fun e => nomatch e)

/-- The entire recurrence is retained; the leading count is the selected observation. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ), 4 ≤ n →
    (3 - (n : ℤ)) * r.readout () () n + 2 * ((n : ℤ) - 2) * a (n - 1) +
      ((n : ℤ) - 1) * ((n : ℤ) - 2) * ((n : ℤ) - 3) * a (n - 2) = 0

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hb := h 4 (by decide)
  have ht := result 4 (by decide)
  norm_num [bad, realize] at hb
  norm_num at ht
  linarith

private theorem count_four_pos : 0 < a 4 := by
  classical
  let T := {p : Equiv.Perm (Fin 4) //
    ((p 0).val + 1) % 2 = ((p 1).val + 1) % 2}
  have hn : Nonempty T := ⟨⟨Equiv.swap 1 2, by norm_num [Equiv.swap_apply_def]⟩⟩
  have hc : 0 < Nat.card T := Nat.card_pos_iff.mpr ⟨hn, inferInstance⟩
  simpa [a, T] using (Int.natCast_pos.mpr hc)

def evidence : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 4, ?_⟩
    change a 0 ≠ a 4
    have hz : a 0 = 0 := by simp [a]
    rw [hz]
    exact ne_of_lt count_four_pos

def result_registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Combinatorics.Permutation.MatharSameParityRecurrence.result)
      (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Permutation.MatharSameParityRecurrence.count_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.MatharSameParityRecurrence.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.MatharSameParityRecurrence
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms result_registration

end Reg.D5.S3.Combinatorics.Permutation.MatharSameParityRecurrence
