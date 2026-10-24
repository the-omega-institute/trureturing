import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.SpinChains.TemporalBellContractionIdentity
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the real endpoint propagator contraction. -/

namespace Reg.D5.S3.Quantum.SpinChains.TemporalBellContractionIdentity

open _root_.D5.S3.Quantum.SpinChains.TemporalBellContractionIdentity
open _root_.D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the real coordinate of the endpoint propagator difference. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => z.re) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Preserve the complete parameter telescope and both vacuum contractions. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N : ℕ) (hN : 2 ≤ N) (J μ t : ℝ),
    let first : Fin N := ⟨0, by omega⟩
    let last : Fin N := ⟨N - 1, by omega⟩
    let X := evolve J μ t (sigmaXLast N (by omega))
    ((fullC last * fullC first * X * (fullC first)ᴴ)
        (vacuumIndex N) (vacuumIndex N) +
      (fullC last * fullC first * X * (fullC last)ᴴ)
        (vacuumIndex N) (vacuumIndex N)).re =
      R.readout () () (propagator N J μ t last last - propagator N J μ t first last)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 2 (by decide) 0 0 0
  have htrue := result 2 (by decide) 0 0 0
  have hone : (propagator 2 0 0 0 (1 : Fin 2) 1 -
      propagator 2 0 0 0 (0 : Fin 2) 1).re = 1 := by
    simp [propagator]
  exact zero_ne_one (hbad.symm.trans (htrue.trans hone))

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
      (@_root_.D5.S3.Quantum.SpinChains.TemporalBellContractionIdentity.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.TemporalBellContractionIdentity.unit
  realizationName :=
    `Reg.D5.S3.Quantum.SpinChains.TemporalBellContractionIdentity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.TemporalBellContractionIdentity
    definition := some {
      owner := `D5.S3.Quantum.SpinChains.TemporalBellContractionIdentity
      name := `D5.S3.Quantum.SpinChains.TemporalBellContractionIdentity.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.SpinChains.TemporalBellContractionIdentity
