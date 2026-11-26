import Reg.D5.S3.Fourier.Concentration.FiniteSineMissingWindow
import D5.S3.Fourier.Concentration.DiffuseSincProduct

/-! Observation of the real argument in the diffuse-product bound. -/

namespace Reg.D5.S3.Fourier.Concentration.DiffuseSincProduct

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.DiffuseSincProduct
open FiniteSineMissingWindow (oneRole sensitivity)
open LeanInformationAudit Finset

noncomputable section

universe u

abbrev timeSignature : Signature :=
  oneRole Unit (fun _ => ℝ)

private def actual : Realization timeSignature :=
  realize timeSignature (fun _ _ t => t) (fun e => nomatch e)

private def rejected : Realization timeSignature :=
  realize timeSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev timeArena : Arena where
  signature := timeSignature
  Law A := ∀ {J : Type u} (s : Finset J) (c : J → ℝ)
    (_ : (∑ j ∈ s, c j ^ 4) ≤ (∑ i ∈ s, c i ^ 2) ^ 2 / 2) (t : ℝ),
    (∏ j ∈ s, |Real.sinc (c j * t)|) ≤
      (1 + (∑ j ∈ s, c j ^ 2) * (A.readout () () t) ^ 2 / 15)⁻¹

private theorem rejected_law : ¬ timeArena.{u}.Law rejected := by
  intro law
  let s : Finset (ULift.{u} (Fin 2)) := univ
  have hc : (∑ _ ∈ s, (1 : ℝ) ^ 4) ≤ (∑ _ ∈ s, (1 : ℝ) ^ 2) ^ 2 / 2 := by
    norm_num [s]
  have h := law s (fun _ => 1) hc 0
  change (∏ _ ∈ s, |Real.sinc ((1 : ℝ) * 0)|) ≤
    (1 + (∑ _ ∈ s, (1 : ℝ) ^ 2) * 1 ^ 2 / 15)⁻¹ at h
  norm_num [s] at h

private theorem dependence : ObservationalDependence timeSignature actual := by
  intro _
  exact ⟨(), 0, 1, zero_ne_one⟩

def timeEvidence :
    Registration timeArena.{u} (type_of% @diffuse_sinc_product_le.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@diffuse_sinc_product_le.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity timeArena.Law actual rejected rejected_law
  dependence := dependence

def timeRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@diffuse_sinc_product_le.{u}) (Realization timeSignature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.DiffuseSincProduct.timeUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.DiffuseSincProduct.timeEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨timeArena.{u}⟩
  objectArena := .source ⟨timeArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source timeArena.{u} ⟨timeEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize timeSignature (fun _ _ t => t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.DiffuseSincProduct
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg",
        "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms timeRegistration

end

end Reg.D5.S3.Fourier.Concentration.DiffuseSincProduct
