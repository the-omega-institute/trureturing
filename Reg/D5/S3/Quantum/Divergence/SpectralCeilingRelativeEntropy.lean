import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy

noncomputable section
universe u
open Matrix
open scoped ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (M : ℝ) (hM : 0 < M)
    (ceilingA : A ≤ (M : ℂ) • (1 : Matrix n n ℂ))
    (ceilingB : B ≤ (M : ℂ) • (1 : Matrix n n ℂ))
    (support : ∀ v, B *ᵥ v = 0 → A *ᵥ v = 0),
    R.readout () () (((A - B)ᴴ * (A - B)).trace.re / (2 * M))
      ((A * (cfc Real.log A - cfc Real.log B)).trace.re - A.trace.re + B.trace.re)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hc : (0 : Matrix (ULift.{u} (Fin 0)) (ULift.{u} (Fin 0)) ℂ) ≤
      (1 : ℂ) • 1 := le_of_eq (Subsingleton.elim _ _)
  exact h (n := ULift.{u} (Fin 0)) 0 0 Matrix.PosSemidef.zero Matrix.PosSemidef.zero
    1 zero_lt_one hc hc (by intro v _; simp)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 0
  norm_num [actual, realize] at h

def family : Registration arena.{u}
    (type_of% @actual_matrix_spectral_ceiling_strong_klein.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_matrix_spectral_ceiling_strong_klein, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_matrix_spectral_ceiling_strong_klein.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy.actual_matrix_spectral_ceiling_strong_klein.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms actual_matrix_spectral_ceiling_strong_klein
#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy
