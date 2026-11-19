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

def family : Registration arena (type_of% @A1_spectral_prefix) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@A1_spectral_prefix, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@A1_spectral_prefix) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization.A1_spectral_prefix.audit
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

def family : Registration arena (type_of% @A1_spectral_majorization) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@A1_spectral_majorization, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@A1_spectral_majorization) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization.A1_spectral_majorization.audit
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

namespace TraceEqualities

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ)
    (fun _ => ℂ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (one_ne_zero : (1 : ℂ) ≠ 0) (Eq.mp (congrFun h 0) rfl)

namespace TracePairing

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ P Q : TwoMode, R.readout () () (P * A₁ Q).trace (Q * A₁ P).trace

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0

def family : Registration arena (type_of% @A₁_trace_pair_swap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@A₁_trace_pair_swap, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@A₁_trace_pair_swap) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization.A₁_trace_pair_swap.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization.TraceEqualities.TracePairing.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TracePairing


namespace TracePreservation

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ X : TwoMode, R.readout () () (A₁ X).trace X.trace

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0

def family : Registration arena (type_of% @A₁_trace) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@A₁_trace, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@A₁_trace) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization.A₁_trace.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization.TraceEqualities.TracePreservation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TracePreservation

end TraceEqualities
namespace MatrixEqualities

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => TwoMode)
    (fun _ => TwoMode → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (one_ne_zero : (1 : TwoMode) ≠ 0) (Eq.mp (congrFun h 0) rfl)

namespace Unitality

private abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () (A₁ 1) 1

private theorem rejected_law : ¬ arena.Law rejected := by
  exact id

def family : Registration arena (type_of% @A₁_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@A₁_one, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@A₁_one) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization.A₁_one.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization.MatrixEqualities.Unitality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Unitality

end MatrixEqualities
namespace SpectralEqualities

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (one_ne_zero : (1 : ℝ) ≠ 0) (Eq.mp (congrFun h 0) rfl)

namespace SpectralTotal

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (X : TwoMode) (hX : X.IsHermitian),
    R.readout () () (∑ i : Fin 4, (A₁_isHermitian X hX).eigenvalues₀ i)
      (∑ i : Fin 4, endpointClassical hX.eigenvalues₀ i)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 Matrix.isHermitian_zero

def family : Registration arena (type_of% @A₁_spectral_total) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@A₁_spectral_total, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@A₁_spectral_total) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization.A₁_spectral_total.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization.SpectralEqualities.SpectralTotal.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SpectralTotal

end SpectralEqualities

namespace HermitianImageObservation

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => TwoMode)
    (fun _ => TwoMode)

private def actual : Realization signature :=
  realize signature (fun _ _ x => A₁ x) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => Complex.I • (1 : TwoMode)) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  change A₁ 0 ≠ A₁ 1
  rw [map_zero, A₁_one]
  exact zero_ne_one

namespace Source

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (X : TwoMode), X.IsHermitian → (R.readout () () X).IsHermitian

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 0 Matrix.isHermitian_zero).apply (0, 0) (0, 0)
  have hi := congrArg Complex.im he
  norm_num [rejected, realize, Matrix.one_apply, Complex.star_def] at hi

def family : Registration arena (type_of% @A₁_isHermitian) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@A₁_isHermitian, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@A₁_isHermitian) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization.A₁_isHermitian.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization.HermitianImageObservation.Source.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => A₁ x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Source

end HermitianImageObservation
namespace ClassicalOrderObservation

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 4 → ℝ)
    (fun _ => Fin 4 → ℝ)

private def actual : Realization signature :=
  realize signature (fun _ _ x => endpointClassical x) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun i : Fin 4 => (i.val : ℝ)) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  change endpointClassical 0 = endpointClassical 1 at h
  have h0 := congrFun h 0
  have hs := congrArg (fun x : ℝ => x ^ 2) endpointAlpha_add_beta
  simp [endpointClassical] at h0
  nlinarith

namespace Source

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x : Fin 4 → ℝ), Antitone x → Antitone (R.readout () () x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0 (fun _ _ _ => le_rfl) (show (0 : Fin 4) ≤ 1 by decide)
  norm_num [rejected, realize] at he

def family : Registration arena (type_of% @endpointClassical_antitone) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@endpointClassical_antitone, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@endpointClassical_antitone) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization.endpointClassical_antitone.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization.ClassicalOrderObservation.Source.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => endpointClassical x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Source

end ClassicalOrderObservation

end Reg.D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization
