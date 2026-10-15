import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumBounds.UnentangledOddPrimeCommunication
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.QuantumBounds.UnentangledOddPrimeCommunication
open _root_.D5.S3.QuantumBounds.UnentangledOddPrimeCommunication
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the individual-strategy bound at its dimension coordinate. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ d => 2 / ((d : ℝ) + 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ d => 1 / ((d : ℝ) + 1)) (fun e => nomatch e)

/-- Preserve the odd-prime telescope, mixture bound and exact attainment clause. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    ∀ (d : ℕ) (hp : d.Prime), Odd d →
      letI : NeZero d := ⟨hp.ne_zero⟩
      ((∀ α β M, Valid (d := d) α β M →
          score (d := d) α β M ≤ R.readout () () d) ∧
       (∀ (L : ℕ) (q : Fin L → ℝ) α β M, (∀ l, 0 ≤ q l) → ∑ l, q l = 1 →
          (∀ l, Valid (d := d) (α l) (β l) (M l)) →
            mixtureScore (d := d) q α β M ≤ 2 / ((d : ℝ) + 1))) ∧
      (∃ α β M, Valid (d := d) α β M ∧
        score (d := d) α β M = 2 / ((d : ℝ) + 1))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : Nat.Prime 3 := by norm_num
  have hodd : Odd (3 : ℕ) := by norm_num
  obtain ⟨α, β, M, hv, hs⟩ := (result 3 hp hodd).2
  have bad := (h 3 hp hodd).1.1 α β M hv
  change score α β M ≤ 1 / ((3 : ℝ) + 1) at bad
  rw [hs] at bad
  norm_num at bad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuantumBounds.UnentangledOddPrimeCommunication.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumBounds.UnentangledOddPrimeCommunication.unit
  realizationName := `Reg.D5.S3.QuantumBounds.UnentangledOddPrimeCommunication.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => 2 / ((d : ℝ) + 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.UnentangledOddPrimeCommunication
    definition := some {
      owner := `D5.S3.QuantumBounds.UnentangledOddPrimeCommunication
      name := `D5.S3.QuantumBounds.UnentangledOddPrimeCommunication.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg",
        "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms signature
#print axioms actual
#print axioms rejected
#print axioms arena
#print axioms rejected_law
#print axioms dependence
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.QuantumBounds.UnentangledOddPrimeCommunication
