import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.ThreeBitSource
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.ThreeBitSource

open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.ThreeBitSource

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin p.1 → ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p b => actualSource p.1 (1 + 2 ^ p.2 + 2 ^ b))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k a b : ℕ) (_ha : 0 < a) (_hab : a < b) (_hbk : b < k),
    ∃ word : List (Fin k), word.Perm (List.finRange k) ∧
      (∀ n : ℕ, ((word.take n).map (R.readout () ⟨k, a⟩ b)).sum ∈
        Set.Icc (0 : ℤ) ((2 : ℤ) ^ (k - 1) - 1)) ∧
      (word.map (R.readout () ⟨k, a⟩ b)).sum = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨word, hperm, _, htotal⟩ := h 3 1 2 (by decide) (by decide) (by decide)
  have hlength : word.length = 3 := by simpa using hperm.length_eq
  norm_num [rejected, realize, List.map_const', hlength] at htotal

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨5, 1⟩, 2, 3, ?_⟩
  intro h
  have hv := congrFun h ⟨0, by decide⟩
  norm_num [actual, realize, actualSource, centered, modulus] at hv

def source_registration : Registration arena (type_of% (@three_bit_source_order)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨three_bit_source_order, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

#print axioms source_registration


def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.ThreeBitSource.three_bit_source_order)
    (type_of% (realize signature
      (fun _ p b => actualSource p.1 (1 + 2 ^ p.2 + 2 ^ b)) (fun e => nomatch e)))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.ThreeBitSource.three_bit_source_order.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.ThreeBitSource.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p b => actualSource p.1 (1 + 2 ^ p.2 + 2 ^ b)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.ThreeBitSource
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms audit

end Reg.D5.S3.Combinatorics.Circle.ThreeBitSource
