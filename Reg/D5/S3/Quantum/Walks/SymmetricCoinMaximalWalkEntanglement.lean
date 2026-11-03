import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement
import Reg.Support.DependentFamily

/-! Source-bound audit of symmetric-coin maximal walk entanglement. -/

namespace Reg.D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement

open _root_.D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators ComplexConjugate

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe real comparison at the lower endpoint of the entanglement bound. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ lower upper => lower ≤ upper) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ lower upper => lower < upper) (fun e => nomatch e)

/-- Retain every original parameter, normalization hypothesis and local instance. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (p : ℕ) (hp : 1 ≤ p) (n : ℕ) (c : Fin 2 → ℂ),
    _root_.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor c →
    letI : NeZero p := ⟨by omega⟩
    r.readout () () (geometricEntanglement (walkState p n c))
      (geometricEntanglement (walkState p n cStar))

private lemma cStar_unit :
    _root_.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor cStar := by
  have hs : Complex.normSq (Real.sqrt 2 : ℂ) = 2 := by
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num)]
  norm_num [D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor,
    Fin.sum_univ_two, cStar, hs]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 (by norm_num) 0 cStar cStar_unit
  change geometricEntanglement (walkState 1 0 cStar) <
    geometricEntanglement (walkState 1 0 cStar) at hbad
  exact (lt_irrefl _) hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hle : (0 : ℝ) ≤ 0 := le_rfl
  change (fun upper : ℝ => 0 ≤ upper) = (fun upper : ℝ => 1 ≤ upper) at h
  have hfalse : (1 : ℝ) ≤ 0 := (congrFun h 0).mp hle
  exact (not_le_of_gt zero_lt_one) hfalse

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement.source_registration
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
    (fun _ _ lower upper => lower ≤ upper) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement
    definition := some {
      owner := `D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement
      name := `D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement
