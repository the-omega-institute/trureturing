import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.CartesianVariance
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of Hermitian spectral reconstruction. -/

namespace Reg.D5.S3.Quantum.Matrix.CartesianVariance
open _root_.D5.S3.Quantum.Matrix.CartesianVariance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HermitianSpectralSum

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Matrix (Fin n) (Fin n) ℂ)
    (fun n => Matrix (Fin n) (Fin n) ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ X Y => X ≠ Y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.IsHermitian),
    R.readout () n ρ (∑ i, hρ.eigenvalues i •
      Matrix.vecMulVec (WithLp.ofLp (hρ.eigenvectorBasis i))
        (star (WithLp.ofLp (hρ.eigenvectorBasis i))))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 1 1 Matrix.isHermitian_one (hermitian_spectral_sum 1 Matrix.isHermitian_one)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  intro h
  exact one_ne_zero (Eq.mp (congrFun h 0) rfl)

def source_registration : Registration arena (type_of% @hermitian_spectral_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hermitian_spectral_sum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@hermitian_spectral_sum) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Matrix.CartesianVariance.hermitian_spectral_sum.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CartesianVariance.HermitianSpectralSum.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CartesianVariance
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end HermitianSpectralSum

end
end Reg.D5.S3.Quantum.Matrix.CartesianVariance
