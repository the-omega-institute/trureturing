import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.SourceWidth
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.SourceWidth

/-- Every residue is a state. The output retains every physical label. -/
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ k := Fin k → ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ k t => actualSource k t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : ℕ, 3 ≤ k → ∀ t : ℕ,
    ∃ word : List (Fin k), word.Nodup ∧ word.toFinset = Finset.univ ∧
      ∀ n : ℕ, n ≤ k →
        ((word.take n).map (R.readout () k t)).sum ∈ Set.Icc (0 : ℤ) (capacity k)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨word, hnodup, hcomplete, hheight⟩ := h 3 (by decide) 0
  have hmem : (0 : Fin 3) ∈ word := List.mem_toFinset.mp (by rw [hcomplete]; simp)
  cases word with
  | nil => simp at hmem
  | cons x xs =>
    have hh := hheight 1 (by decide)
    change ([-1] : List ℤ).sum ∈ Set.Icc (0 : ℤ) (capacity 3) at hh
    norm_num at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨3, 0, 1, ?_⟩
  intro he
  have hh := congrFun he (0 : Fin 3)
  norm_num [actual, realize, actualSource, centered, modulus] at hh

def source_registration : Registration arena (type_of% (@universal_source_width)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨universal_source_width, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.SourceWidth.universal_source_width)
    (type_of% (realize signature (fun _ k t => actualSource k t) (fun e => nomatch e)))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.SourceWidth.universal_source_width.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.SourceWidth.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k t => actualSource k t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.SourceWidth
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "arg", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
end Reg.D5.S3.Combinatorics.Circle.SourceWidth
