import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal152
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ _ : Side, List Return
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ p D => execute p.1 p.2 D) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (K : ℕ) (d : ℝ) (strict : Bool) (j : Side)
  (execution : List Return) (D : ℝ),
  GuardTrace K d strict j execution D ↔
  ∀ (before : List Return) (a : Return) (after : List Return),
    execution = before ++ a :: after →
    a.r ≤ K ∧ (a.r = K →
      if strict then d < r.readout () ⟨j, before⟩ D
      else d ≤ execute j before D)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  let a : Return := ⟨1, 1, by decide, by decide⟩
  have left : GuardTrace 1 0 true .high [a] 1 := by
    norm_num [GuardTrace, a]
  have impossible := ((h 1 0 true .high [a] 1).mp left [] a [] rfl).2 rfl
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.uniform_guard_trace_iff_split) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.uniform_guard_trace_iff_split, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨Side.high, []⟩, 0, 1, ?_⟩
    norm_num [actual, realize, execute]

def uniform_guard_trace_iff_split_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.uniform_guard_trace_iff_split)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ p D => execute p.1 p.2 D) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal152.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal152.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ p D => execute p.1 p.2 D) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
    definition := none
    coordinates := #[3, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "body", "body", "body", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms uniform_guard_trace_iff_split_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal152

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal154
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ _ : Side, List Return
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ p D => execute p.1 p.2 D) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (j : Side) (budget : ℝ) (execution : List Return) (D : ℝ),
  StrictControl j budget execution D ↔
  ∀ (before : List Return) (a : Return) (after : List Return),
    execution = before ++ a :: after →
    lam - g ^ 2 * chi ^ a.r * r.readout () ⟨j, before⟩ D < budget

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  let a : Return := ⟨1, 1, by decide, by decide⟩
  have gp : 0 < g := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    dsimp [g, t]
    nlinarith [Real.sqrt_nonneg (5 : ℝ)]
  have cp : 0 < chi := by dsimp [chi]; positivity
  have left : StrictControl .high lam [a] 1 := by
    simp only [StrictControl, a, pow_one, mul_one, and_true]
    nlinarith [mul_pos (sq_pos_of_pos gp) cp]
  have impossible := (h .high lam [a] 1).mp left [] a [] rfl
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.exact_control_iff_split) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.exact_control_iff_split, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨Side.high, []⟩, 0, 1, ?_⟩
    norm_num [actual, realize, execute]

def exact_control_iff_split_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.exact_control_iff_split)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ p D => execute p.1 p.2 D) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal154.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal154.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ p D => execute p.1 p.2 D) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms exact_control_iff_split_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal154

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal149
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ execution : List Return, Σ j : Side, ℕ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ q z => execute q.2.1 (q.1.take q.2.2) z) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ q _ => aSide q.2.1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (model : Model) (execution : List Return),
      (∀ (j : Side) (p : ℕ),
        aSide j < r.readout () ⟨execution, ⟨j,p⟩⟩ (initial j model) ∧
        execute j (execution.take p) (initial j model) < hSide j) ∧
      (∀ p : ℕ, execute .high (execution.take p) (initial .high model) <
        execute .low (execution.take p) (initial .low model)) ∧
      (∀ (j : Side) (p n k : ℕ),
        let D := execute j (execution.take p) (initial j model)
        let z := hSide j - rho ^ k * (hSide j - chi ^ n * D)
        0 < z ∧ z < hSide j ∧
        0 ≤ c0 + sign j * z ∧ c0 + sign j * z ≤ T2) ∧
      (∀ (p n k : ℕ),
        hSide .high - rho ^ k * (hSide .high - chi ^ n *
          execute .high (execution.take p) (initial .high model)) <
        hSide .low - rho ^ k * (hSide .low - chi ^ n *
          execute .low (execution.take p) (initial .low model))) ∧
      (∀ (j : Side) (p : ℕ),
        coordinate (sourcePrefix j model execution)
          ((stem j).length + listWeight (execution.drop p)) =
        c0 + sign j * execute j (execution.take p) (initial j model))

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  exact (lt_irrefl (aSide Side.high)) ((h .original []).1 .high 0).1

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.actual_complete_boundary_geometry) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.actual_complete_boundary_geometry, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨[], Side.high, 0⟩, 0, 1, ?_⟩
    norm_num [actual, realize, execute]

def actual_complete_boundary_geometry_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.actual_complete_boundary_geometry)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ q z => execute q.2.1 (q.1.take q.2.2) z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal149.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal149.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ q z => execute q.2.1 (q.1.take q.2.2) z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
    definition := none
    coordinates := #[1, 2, 3]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "body", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_complete_boundary_geometry_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal149
