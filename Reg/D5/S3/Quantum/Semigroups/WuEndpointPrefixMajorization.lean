import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization

/-! Source-bound readouts for the proper spectral prefix comparison. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix BigOperators
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.WuRankOneEndpointFloor

namespace Reg.D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (by norm_num : ¬ (1 : ℝ) ≤ 0) (Eq.mp (congrFun h 0) (le_refl 0))

namespace SpectralPrefix

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (X : TwoMode) (hX : X.IsHermitian) (k : Fin 3),
    R.readout () () (endpointPrefixSum (A₁_isHermitian X hX).eigenvalues₀ k)
      (endpointPrefixSum (endpointClassical hX.eigenvalues₀) k)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 Matrix.isHermitian_zero 0

def family : Registration arena (type_of% @A₁_spectral_prefix) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@A₁_spectral_prefix, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@A₁_spectral_prefix) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization.A₁_spectral_prefix.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization.SpectralPrefix.family
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
    owner := `D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SpectralPrefix

namespace SpectralMajorization

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (X : TwoMode) (hX : X.IsHermitian),
    Antitone (endpointClassical hX.eigenvalues₀) ∧
    (∀ k : Fin 3, R.readout () () (endpointPrefixSum (A₁_isHermitian X hX).eigenvalues₀ k)
      (endpointPrefixSum (endpointClassical hX.eigenvalues₀) k)) ∧
    (∑ i : Fin 4, (A₁_isHermitian X hX).eigenvalues₀ i) =
      ∑ i : Fin 4, endpointClassical hX.eigenvalues₀ i

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h 0 Matrix.isHermitian_zero).2.1 0

def family : Registration arena (type_of% @A₁_spectral_majorization) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@A₁_spectral_majorization, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@A₁_spectral_majorization) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization.A₁_spectral_majorization.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization.SpectralMajorization.family
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
    owner := `D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SpectralMajorization

end Reg.D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization
