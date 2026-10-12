import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumContext.HanceTwentyFourCellThreshold
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.QuantumContext.HanceTwentyFourCellThreshold

noncomputable section
namespace Reg.D5.S3.QuantumContext.HanceTwentyFourCellThreshold
universe u

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ lambda => admissible.{u} lambda) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (lambda : ℝ), lambda ∈ Set.Icc (0 : ℝ) 1 →
    (R.readout () () lambda ↔ lambda ≤ 1/2)

def statement : Prop := ∀ (lambda : ℝ), lambda ∈ Set.Icc (0 : ℝ) 1 →
  (admissible.{u} lambda ↔ lambda ≤ 1/2)

def registration : Registration arena statement.{u} := by
  have hRejected : ¬ arena.Law rejected := by
    intro h
    have hh := (h 0 (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)).mpr (by norm_num)
    exact hh
  exact {
    actual := actual.{u}
    bridge := Iff.rfl
    variation := ⟨result.{u}, rejected, hRejected⟩
    sensitivity := by
      constructor
      · intro i
        refine ⟨rejected, ?_, rfl, hRejected⟩
        intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · intro e
        exact nomatch e
    dependence := by
      intro ⟨⟩
      refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
      intro he
      have hz : admissible.{u} 0 := (result.{u} 0 (by norm_num)).mpr (by norm_num)
      have ho : admissible.{u} 1 := Eq.mp he hz
      have := (result.{u} 1 (by norm_num)).mp ho
      norm_num at this
  }

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.QuantumContext.HanceTwentyFourCellThreshold.result.{u})
      (type_of% (realize signature (fun _ _ lambda => admissible.{u} lambda)
        (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.QuantumContext.HanceTwentyFourCellThreshold.result
    "Reg.D5.S3.QuantumContext.HanceTwentyFourCellThreshold/Reg.D5.S3.QuantumContext.HanceTwentyFourCellThreshold.arena/[anonymous]")
    "__information_unit"
  realizationName := `Reg.D5.S3.QuantumContext.HanceTwentyFourCellThreshold.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ lambda => admissible.{u} lambda)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumContext.HanceTwentyFourCellThreshold
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration
#print axioms registration_1
end Reg.D5.S3.QuantumContext.HanceTwentyFourCellThreshold
