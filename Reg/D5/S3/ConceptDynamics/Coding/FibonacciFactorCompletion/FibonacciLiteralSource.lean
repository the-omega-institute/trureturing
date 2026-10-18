import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FibonacciLiteralSource
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal203
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ z => compose C z) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => c0 + 1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (j : Side) (model : Model) (execution : List Return),
      LegalWord .G0 .G0 (sourcePrefix j model execution) ∧
      (∀ p, source j model execution ((observedPrefix j model execution).length + p) =
        address (tailPrefix j) p) ∧
      (∀ p, coordinate (sourcePrefix j model execution)
          ((observedPrefix j model execution).length + p) = coordinate (tailPrefix j) p) ∧
      coordinate (externalWord j execution ++ anchor j model ++ tailPrefix j) 0 =
        c0 + sign j * execute j execution (initial j model) ∧
      (observedPrefix j model execution).length = observationOffset model + listWeight execution ∧
      (history model execution).length = observationOffset model + listWeight execution ∧
      (∀ D, r.readout () () (c0 + sign j * D) = c0 + sign j * (chi * D)) ∧
      (∀ D, compose (block j) (c0 + sign j * D) =
        c0 + sign j * (aSide j + rho * D)) ∧
      (∀ (a : Return) D, compose (returnWord j a) (c0 + sign j * D) =
        c0 + sign j * returnMap j a D) ∧
      (∀ (xs : List Return) D, compose (externalWord j xs) (c0 + sign j * D) =
        c0 + sign j * execute j xs D) ∧
      compose (tailPrefix j) 0 = c0 + sign j * xSide j

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h .high .original []).2.2.2.2.2.2.1 0
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.paired_source_reconstruction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.paired_source_reconstruction, rejected, rejected_law⟩
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
    refine ⟨(), c0, c0 + 1, ?_⟩
    have hc := (paired_source_reconstruction .high .original []).2.2.2.2.2.2.1
    have hc0 := hc 0
    have hc1 := hc 1
    simp only [sign, mul_zero, add_zero, one_mul, mul_one] at hc0 hc1
    have gp : 0 < g := by
      have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
      dsimp [g, t]
      nlinarith [Real.sqrt_nonneg (5 : ℝ)]
    have cp : 0 < chi := pow_pos gp 20
    change compose C c0 ≠ compose C (c0 + 1)
    rw [hc0, hc1]
    exact ne_of_lt (lt_add_of_pos_right c0 cp)

def paired_source_reconstruction_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.paired_source_reconstruction)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ z => compose C z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal203.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal203.evidence
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
    (fun _ _ z => compose C z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms paired_source_reconstruction_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal203

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal202
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => List Label) (fun _ => ℝ → ℝ)

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ w => compose w) (fun e => nomatch e)

def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => fun _ => (1 : ℝ)) (fun e => nomatch e)

theorem actual_dependence : ObservationalDependence observationSignature actual := by
  intro i
  refine ⟨(), [], [Label.L2], ?_⟩
  intro heq
  have h := congrFun heq (0 : ℝ)
  norm_num [actual, realize, compose, branch, shift] at h

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r :=     (∀ (s e : Guard) (w : List Label) (z : ℝ), LegalWord s e w → InSupport e z →
      InSupport s (compose w z)) ∧
    (∀ (left B right : List Label) (p : ℕ), p ≤ B.length →
      coordinate (left ++ B ++ right) (left.length + p) =
        compose (B.drop p) c0 + (-g) ^ (B.length - p) * (coordinate right 0 - c0)) ∧
    (∀ (w : List Label) (n p : ℕ), coordinate (w ++ List.replicate n Label.L0) p =
      coordinate w p) ∧
    (∀ (w : List Label) (x y : ℝ),
      compose w (x + y) = compose w x + (-g) ^ w.length * y) ∧
    (∀ (w v : List Label) (z : ℝ), r.readout () () (w ++ v) z = compose w (compose v z))

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have h := h.2.2.2.2 [] [] 0
  norm_num [rejected, realize, compose] at h

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.literal_source_geometry) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.literal_source_geometry, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law
  dependence := actual_dependence

def literal_source_geometry_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.literal_source_geometry)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ w => compose w) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal202.literal_source_geometry_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal202.evidence
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
        (fun _ _ w => compose w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "arg", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms literal_source_geometry_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal202

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

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
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
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
