import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Information.ProductMarginQubitOrder
noncomputable section
namespace Reg.D5.S3.Quantum.Information.ProductMarginQubitOrder
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Information.ProductMarginQubitOrder
open _root_.D5.S3.Quantum.Information.QubitNormalFormState
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open scoped Kronecker MatrixOrder ComplexOrder
namespace Pure
abbrev signature.{u} : Signature where
  Params := Type u
  State n := Matrix (Fin 2 × n) (Fin 2 × n) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix (Fin 2 × n) (Fin 2 × n) ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def readout.{u} : Realization signature.{u} := realize signature (fun _ _ X => Eq X) (fun e => nomatch e)
def bad.{u} : Realization signature.{u} := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem dependence.{u} : ObservationalDependence signature.{u} readout := by
  intro i
  refine ⟨ULift.{u} Unit, 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : Matrix (Fin 2 × ULift.{u} Unit) (Fin 2 × ULift.{u} Unit) ℂ) = 0) = (1 = 0) at he
  exact one_ne_zero (Eq.mp he rfl)

abbrev arena.{u} : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] {x z : ℝ},
    0 ≤ x → x < 1 → x ^ 2 + z ^ 2 = 1 →
    ∀ (P Q : Matrix n n ℂ) {K : Matrix (Fin 2 × n) (Fin 2 × n) ℂ},
    K.PosSemidef → K ≤ qubitMatrix x z ⊗ₖ P → K ≤ qubitMatrix x (-z) ⊗ₖ Q →
      R.readout () n K 0
private theorem bad_law.{u} : ¬ arena.{u}.Law bad := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance 0 1
    (by norm_num) (by norm_num) (by norm_num) 0 0 0
    Matrix.PosSemidef.zero (by simp) (by simp)
def family.{u} : Registration arena.{u} (type_of% (@common_lower_zero_of_pure_left.{u})) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨@common_lower_zero_of_pure_left.{u}, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨bad, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, bad_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration.{u} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@common_lower_zero_of_pure_left.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Information.ProductMarginQubitOrder.Pure.unit
  realizationName := `Reg.D5.S3.Quantum.Information.ProductMarginQubitOrder.Pure.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ X => Eq X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.ProductMarginQubitOrder
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end Pure
namespace Trace
abbrev signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def readout : Realization signature := realize signature (fun _ _ p q => p ≤ q) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature readout := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  norm_num [readout, realize] at he

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {xC zC xD zD : ℝ},
    0 ≤ xC → xC < 1 → 0 ≤ xD → xD < 1 →
    xC ^ 2 + zC ^ 2 ≤ 1 → xD ^ 2 + zD ^ 2 ≤ 1 →
    ∀ {K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ},
    K.PosSemidef → K ≤ qubitMatrix xC zC ⊗ₖ qubitMatrix xD zD →
    K ≤ qubitMatrix xC (-zC) ⊗ₖ qubitMatrix xD (-zD) →
    R.readout () () K.trace.re
      ((1 - Real.sqrt ((zC ^ 2 / (1 - xC ^ 2)) * (zD ^ 2 / (1 - xD ^ 2)))) /
        (1 + Real.sqrt ((zC ^ 2 / (1 - xC ^ 2)) * (zD ^ 2 / (1 - xD ^ 2)))))
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hp : 0 ≤ qubitMatrix 0 0 ⊗ₖ qubitMatrix 0 0 := by
    exact (density_posSemidef (productState (qubitState 0 0 (by norm_num))
      (qubitState 0 0 (by norm_num)))).nonneg
  exact @h 0 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 0 Matrix.PosSemidef.zero hp (by simpa only [neg_zero] using hp)
def family : Registration arena (type_of% (@common_lower_trace_bound)) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨@common_lower_trace_bound, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law readout bad bad_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@common_lower_trace_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Information.ProductMarginQubitOrder.Trace.unit
  realizationName := `Reg.D5.S3.Quantum.Information.ProductMarginQubitOrder.Trace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p q => p ≤ q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.ProductMarginQubitOrder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end Trace
end Reg.D5.S3.Quantum.Information.ProductMarginQubitOrder
