import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.Quantum.Foundation.FiniteHermitianSign
import D5.S3.Quantum.QuantumChannels.CouplingWassersteinEquality

set_option autoImplicit false

noncomputable section
namespace Reg.D5.S3.Quantum.QuantumChannels.CouplingWassersteinEquality
open Matrix
open scoped ComplexOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Quantum.QuantumChannels.CouplingWassersteinEquality
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open _root_.D5.S3.Quantum.QuantumChannels.CouplingWassersteinTriangleRefutation (wasserstein)
open _root_.Reg.D5.S3.Quantum.Foundation.FiniteHermitianSign (Mat normSignature normActual normShifted normDependence)

abbrev transportArena : DependentFamily.Arena where
  signature := normSignature
  Law := fun R => ∀ {n : ℕ} {ρ σ : Mat n}
    (_ : 0 < n) (hρ : ρ.PosSemidef) (_ : ρ.trace = 1)
    (hσ : σ.PosSemidef) (_ : σ.trace = 1),
    wasserstein ρ σ = (show ℝ from R.readout () n (ρ - σ)) / 2 ↔
      HasSpectralCertificate (hρ.isHermitian.sub hσ.isHermitian)

theorem transportShiftFails : ¬ transportArena.Law normShifted := by
  intro bad
  let ρ : Mat 1 := 1
  have hρ : ρ.PosSemidef := PosSemidef.one
  have htr : ρ.trace = 1 := by simp [ρ]
  have hcert : HasSpectralCertificate (hρ.isHermitian.sub hρ.isHermitian) := by
    exact ⟨ρ, 0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, hρ,
      fun i => i.elim0, by simp, by simp⟩
  have exactCost := (wasserstein_eq_traceNorm_iff (by decide) hρ htr hρ htr).mpr hcert
  have shiftedCost := (bad (by decide) hρ htr hρ htr).mpr hcert
  change wasserstein ρ ρ = (traceNorm (ρ - ρ) + 2) / 2 at shiftedCost
  linarith

def transportFamily : DependentFamily.Registration transportArena
    (∀ {n : ℕ} {ρ σ : Mat n} (_ : 0 < n) (hρ : ρ.PosSemidef) (_ : ρ.trace = 1)
      (hσ : σ.PosSemidef) (_ : σ.trace = 1),
      wasserstein ρ σ = traceNorm (ρ - σ) / 2 ↔
        HasSpectralCertificate (hρ.isHermitian.sub hσ.isHermitian)) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨@wasserstein_eq_traceNorm_iff, normShifted, transportShiftFails⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨normShifted, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, transportShiftFails⟩
    · intro e
      exact nomatch e
  dependence := normDependence


noncomputable def equalityRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@wasserstein_eq_traceNorm_iff) (DependentFamily.Realization normSignature) Unit Unit where
  unitName := `D5.S3.Quantum.QuantumChannels.CouplingWassersteinEquality.wasserstein_eq_traceNorm_iff.__information_unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.CouplingWassersteinEquality.transportFamily
  realizationSource := none
  generated := false
  arena := .source ⟨transportArena⟩
  objectArena := .source ⟨transportArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source transportArena ⟨transportFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize normSignature (fun _ (n : ℕ) (A : Mat n) => traceNorm A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.CouplingWassersteinEquality
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.QuantumChannels.CouplingWassersteinEquality
