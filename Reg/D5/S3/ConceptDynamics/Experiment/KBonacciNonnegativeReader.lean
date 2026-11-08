import D5.S3.ConceptDynamics.Experiment.KBonacciNonnegativeReader
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Whole-source target-family audit for the actual-history preparation obstruction. -/

namespace Reg.D5.S3.ConceptDynamics.Experiment.KBonacciNonnegativeReader

open _root_.D5.S3.ConceptDynamics.Experiment.KBonacciNonnegativeReader
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := World
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Mat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ w => target w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O :=
    let T : World → Mat := O.readout () ()
    let correct : Protocol → Prop := fun π => ∀ w, π.output w = T w
    let value : ENNReal := ⨅ π : {π : Protocol // correct π}, worstPreparations π.val
    (∀ word : Window, ∃ p t : Fin 2,
      (word.val.takeWhile id).length = p.val ∧ live word.val = endpoint p t) ∧
    (∀ p t : Fin 2, ∃ word : Window, live word.val = endpoint p t) ∧
    (∀ w : World, 0 < read ([], none) w) ∧
    (∀ (π : Protocol) (w : World), paidReads (π.history w) =
      preparations (π.history w) + windows (π.history w)) ∧
    (∀ π : Protocol, correct π → ¬ (∀ w, preparations (π.history w) ≤ 1)) ∧
    (∀ π : Protocol, correct π → (2 : ENNReal) ≤ worstPreparations π) ∧
    (2 : ENNReal) ≤ value ∧
    value ≠ 1 ∧
    ¬ (∃ π : Protocol, correct π ∧ ∀ w,
      preparations (π.history w) ≤ 1 ∧ windows (π.history w) ≤ 2 ∧
        paidReads (π.history w) ≤ 3)

def stopZero : Protocol where
  policy := fun _ => .inr 0
  history := fun _ => []
  output := fun _ => 0
  terminates := fun _ => ⟨1, rfl⟩
  lawful := fun _ => True.intro

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h.2.2.2.2.1 stopZero (fun _ => rfl) (fun _ => by
    norm_num [stopZero, preparations])

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  let u : World := ⟨![1, 1], ![1, 0],
    by intro i; fin_cases i <;> norm_num,
    by intro i; fin_cases i <;> norm_num, by norm_num⟩
  let v : World := ⟨![2, 2], ![1, 0],
    by intro i; fin_cases i <;> norm_num,
    by intro i; fin_cases i <;> norm_num, by norm_num⟩
  refine ⟨(), u, v, ?_⟩
  intro he
  have hf := congrArg (fun R : Mat => R 0 0) he
  norm_num [actual, realize, target, u, v, Matrix.vecMulVec_apply] at hf

def family : Registration arena (type_of% complete_source_8_2) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨complete_source_8_2, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@complete_source_8_2) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.ConceptDynamics.Experiment.KBonacciNonnegativeReader.complete_source_8_2.__information_unit
  realizationName :=
    `Reg.D5.S3.ConceptDynamics.Experiment.KBonacciNonnegativeReader.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Experiment.KBonacciNonnegativeReader
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }]

#print axioms family

end
end Reg.D5.S3.ConceptDynamics.Experiment.KBonacciNonnegativeReader
