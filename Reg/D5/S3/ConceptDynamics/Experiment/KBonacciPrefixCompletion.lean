import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Experiment.KBonacciPrefixCompletion
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.ConceptDynamics.Experiment.KBonacciPrefixCompletion

open _root_.D5.S3.ConceptDynamics.Experiment.KBonacciPrefixCompletion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

private def one : World 3 where
  c := fun _ => 1
  ell := fun _ => 1
  c_pos := by intro i; norm_num
  ell_nonneg := by intro i; norm_num
  ell_ne_zero := by intro he; have h := congrFun he 0; norm_num at h

private def two : World 3 where
  c := fun _ => 2
  ell := fun _ => 1
  c_pos := by intro i; norm_num
  ell_nonneg := by intro i; norm_num
  ell_ne_zero := by intro he; have h := congrFun he 0; norm_num at h

private lemma targets_ne : target one ≠ target two := by
  intro he
  have h := congrFun (congrFun he 0) 0
  norm_num [target, one, two] at h

private lemma initials_ne : initial one ≠ initial two := by
  norm_num [initial, one, two, Fin.sum_univ_succ]

abbrev signature : Signature where
  Params := ℕ
  State k := World k
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ k := World k → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ k w v => SameData (offDiagonal k) w v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ), 3 ≤ k → ∀ w v : World k,
    R.readout () k w v → target w = target v

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact targets_ne (h 3 (by decide) one two trivial)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨3,one,two,?_⟩
  intro he
  have same : SameData (offDiagonal 3) one one := ⟨rfl, fun _ _ => rfl⟩
  have other : SameData (offDiagonal 3) two one := by
    exact Eq.mp (congrFun he one) same
  exact initials_ne other.1.symm

def registration : Registration arena (type_of% off_diagonal_identifies) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨off_diagonal_identifies,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Experiment.KBonacciPrefixCompletion.off_diagonal_identifies)
    (Realization signature) Unit Unit := {
  unitName := `D5.S3.ConceptDynamics.Experiment.KBonacciPrefixCompletion.off_diagonal_identifies.__information_unit,
  realizationName := `Reg.D5.S3.ConceptDynamics.Experiment.KBonacciPrefixCompletion.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun _ k w v => SameData (offDiagonal k) w v) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

abbrev patternSignature : Signature where
  Params := (k : ℕ) × Finset (Fin k × Fin k)
  State p := World p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := World p.1 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def patternActual : Realization patternSignature :=
  realize patternSignature (fun _ p w v => SameData p.2 w v) (fun e => nomatch e)

def patternRejected : Realization patternSignature :=
  realize patternSignature (fun _ _ _ _ => True) (fun e => nomatch e)

abbrev patternArena : Arena where
  signature := patternSignature
  Law R := ∀ (k : ℕ), 3 ≤ k → ∀ S : Finset (Fin k × Fin k), S.card ≤ k*(k-1) →
    ((∀ w v : World k, R.readout () ⟨k,S⟩ w v → target w = target v) ↔ S = offDiagonal k)

private theorem pattern_rejected_law : ¬ patternArena.Law patternRejected := by
  intro h
  have card : (offDiagonal 3).card ≤ 3*(3-1) := by decide
  have ident := (h 3 (by decide) (offDiagonal 3) card).mpr rfl
  exact targets_ne (ident one two trivial)

private theorem pattern_dependence : ObservationalDependence patternSignature patternActual := by
  intro i
  refine ⟨⟨3,∅⟩,one,two,?_⟩
  intro he
  have same : SameData ∅ one one := ⟨rfl,fun _ _ => rfl⟩
  have other : SameData ∅ two one := Eq.mp (congrFun he one) same
  exact initials_ne other.1.symm

def patternRegistration : Registration patternArena (type_of% endpoint_pattern_classification) where
  actual := patternActual
  bridge := Iff.rfl
  variation := ⟨endpoint_pattern_classification,patternRejected,pattern_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨patternRejected,?_,rfl,pattern_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := pattern_dependence

noncomputable def patternAudit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Experiment.KBonacciPrefixCompletion.endpoint_pattern_classification)
    (Realization patternSignature) Unit Unit := {
  unitName := `D5.S3.ConceptDynamics.Experiment.KBonacciPrefixCompletion.endpoint_pattern_classification.__information_unit,
  realizationName := `Reg.D5.S3.ConceptDynamics.Experiment.KBonacciPrefixCompletion.patternRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨patternArena⟩,
  objectArena := .source ⟨patternArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source patternArena ⟨patternRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize patternSignature
    (fun _ p w v => SameData p.2 w v) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S3.ConceptDynamics.Experiment.KBonacciPrefixCompletion
