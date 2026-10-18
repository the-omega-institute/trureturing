import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.AlphaGeometry.CubeRootSpectralMonotonicity
import Reg.Support.SingleDependentReadout

/-! Source-bound registration of the pair-mixing identity. -/

namespace Reg.D5.S3.Geometry.AlphaGeometry.CubeRootSpectralMonotonicity
open _root_.D5.S3.Geometry.AlphaGeometry.CubeRootSpectralMonotonicity.Pair
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    (Σ n : ℕ, Σ _ : Fin n → ℝ, Σ _ : Fin n, Fin n)
    (fun _ => ℝ) (fun p => Fin p.1 → ℝ)

def actual : Realization signature :=
  realize signature
    (fun _ p t => (1 - t) • p.2.1 +
      t • (p.2.1 ∘ Equiv.swap p.2.2.1 p.2.2.2)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (l : Fin n → ℝ) (i j : Fin n) (_hij : i ≠ j) (t : ℝ),
    R.readout () ⟨n, l, i, j⟩ t = pairLine l i j (t * (l i - l j))

abbrev sourceScope := type_of% (@mixPair_eq_pairLine)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (fun _ : Fin 2 => (1 : ℝ)) 0 1 (by decide) 0
  have hv := congrFun hh 0
  norm_num [rejected, realize, pairLine] at hv
  change (0 : ℝ) = 1 at hv
  norm_num at hv

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, (fun k => if k = 0 then 1 else 0), 0, 1⟩, 0, 1, ?_⟩
  intro h
  have hv := congrFun h 0
  norm_num [actual, realize, Function.comp_def] at hv

def source_registration : Registration arena sourceScope where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@mixPair_eq_pairLine, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@mixPair_eq_pairLine) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Geometry.AlphaGeometry.CubeRootSpectralMonotonicity.unit
  realizationName :=
    `Reg.D5.S3.Geometry.AlphaGeometry.CubeRootSpectralMonotonicity.source_registration
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
    (fun _ p t => (1 - t) • p.2.1 +
      t • (p.2.1 ∘ Equiv.swap p.2.2.1 p.2.2.2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.AlphaGeometry.CubeRootSpectralMonotonicity
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Geometry.AlphaGeometry.CubeRootSpectralMonotonicity
