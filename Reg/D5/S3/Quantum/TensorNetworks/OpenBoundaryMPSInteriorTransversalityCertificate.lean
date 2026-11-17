import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorTransversalityCertificate
import Reg.Support.DependentFamily

/-! The source readout is the integer product cast to ZMod 5. The law retains
both positive-length premises and both integer nonvanishing conclusions. -/
namespace Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorTransversalityCertificate
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorTransversalityCertificate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
set_option autoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ZMod 5
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p q => ((U p * V q : ℤ) : ZMod 5)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law Z := ∀ (p q : ℕ), 1 ≤ p → 1 ≤ q →
    U p ≠ 0 ∧ V q ≠ 0 ∧
      Z.readout () p q = 2 * (-1)^(q+1) * 3^q

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 1 1 (by omega) (by omega)).2.2
  change (0 : ZMod 5) = 2 * (-1)^(1+1) * 3^1 at he
  exact (by decide : (0 : ZMod 5) ≠ 2 * (-1)^(1+1) * 3^1) he

private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  have hc := (certificate_nonzero 1 1 (by omega) (by omega)).2.2
  change ((U 1 * V 0 : ℤ) : ZMod 5) ≠ ((U 1 * V 1 : ℤ) : ZMod 5)
  rw [hc]
  simp only [V, mul_zero, Int.cast_zero]
  decide

def source_registration : Registration arena (type_of% @certificate_nonzero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@certificate_nonzero, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@certificate_nonzero) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorTransversalityCertificate.certificate_nonzero.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorTransversalityCertificate.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p q => ((U p * V q : ℤ) : ZMod 5))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorTransversalityCertificate
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration
end
end Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorTransversalityCertificate
