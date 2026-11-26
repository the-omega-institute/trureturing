import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fermionic.OrderedSlaterFixedFilling
import Reg.Support.DependentFamily

/-! # Source registration for the coordinate-projector spectrum -/

namespace Reg.D5.S3.Quantum.Fermionic.OrderedSlaterFixedFilling.ProjectorSpectrum
open _root_.D5.S3.Quantum.Fermionic.OrderedSlaterFixedFilling
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Polynomial

universe u
noncomputable section

abbrev Params := Σ ι : Type u, Σ _ : Fintype ι, Σ _ : DecidableEq ι, Finset ι

abbrev signature : Signature where
  Params := Params.{u}
  State θ := θ.1 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ[X]
  Anchor := Empty
  finiteAnchor := inferInstance

def observe (θ : Params.{u}) (v : θ.1 → ℂ) : ℂ[X] := by
  obtain ⟨ι, finite, eq, T⟩ := θ
  exact (Matrix.vecMulVec v (fun i => star (v i)) +
    Matrix.diagonal (fun i => if i ∈ T then (1 : ℂ) else 0)).charpoly

def actual : Realization signature.{u} :=
  realize signature (fun _ => observe) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [finite : Fintype ι] [eq : DecidableEq ι]
    (T : Finset ι) (v : ι → ℂ), (∑ i, v i * star (v i) = 1) →
    (∀ i ∈ T, v i = 0) →
    R.readout () ⟨ι, finite, eq, T⟩ v =
      (X : ℂ[X]) ^ (Fintype.card ι - T.card - 1) * (X - 1) ^ (T.card + 1)

private abbrev singletonParams : Params.{u} := ⟨ULift.{u} (Fin 1), inferInstance, inferInstance, ∅⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he := h (ι := ULift.{u} (Fin 1)) ∅ 1 (by simp) (by simp)
  have h0 := congrArg (Polynomial.eval (0 : ℂ)) he
  norm_num [rejected, realize] at h0

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨singletonParams, 0, 1, ?_⟩
  intro h
  change observe singletonParams 0 = observe singletonParams 1 at h
  have h0 : observe singletonParams 0 = X := by
    simp only [observe, Matrix.vecMulVec, Pi.zero_apply, star_zero, mul_zero,
      Finset.notMem_empty, ite_false, Matrix.diagonal_zero, add_zero]
    change (0 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ).charpoly = X
    simp [Matrix.charpoly_zero]
  have h1 : observe singletonParams 1 = X - 1 := by
    simpa [observe, singletonParams] using
      (spectator_projector_charpoly (ι := ULift.{u} (Fin 1)) ∅ 1 (by simp) (by simp))
  rw [h0, h1] at h
  have he := congrArg (Polynomial.eval (0 : ℂ)) h
  norm_num at he

def source : Registration arena.{u} (type_of% @spectator_projector_charpoly.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@spectator_projector_charpoly.{u}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@spectator_projector_charpoly.{u}) (Realization signature.{u}) Unit Unit := {
  unitName :=
    .str `D5.S3.Quantum.Fermionic.OrderedSlaterFixedFilling.spectator_projector_charpoly
      "__information_unit"
  realizationName := `Reg.D5.S3.Quantum.Fermionic.OrderedSlaterFixedFilling.ProjectorSpectrum.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ => observe) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.OrderedSlaterFixedFilling
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Fermionic.OrderedSlaterFixedFilling.ProjectorSpectrum
