import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuEndpointProjectionBounds

/-! Source-bound readouts for the measured projection comparisons. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open scoped InnerProductSpace
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.WuRankOneEndpointFloor

namespace Reg.D5.S3.Quantum.Semigroups.WuEndpointProjectionBounds

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

private abbrev standardBasis : OrthonormalBasis (Fin 4) ℂ EndpointVector :=
  (EuclideanSpace.basisFun Mode ℂ).reindex
    (Fintype.equivFinOfCardEq (by decide : Fintype.card Mode = 4))

namespace RankOne

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (u v : EndpointVector), ‖u‖ = 1 → ‖v‖ = 1 →
    endpointBeta ^ 2 ≤ (endpointProjector u * A₁ (endpointProjector v)).trace.re ∧
      R.readout () () (endpointProjector u * A₁ (endpointProjector v)).trace.re
        (endpointAlpha ^ 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h (standardBasis 0) (standardBasis 0)
    (standardBasis.orthonormal.1 0) (standardBasis.orthonormal.1 0)).2

def family : Registration arena (type_of% @A1_rankOne_rankOne) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@A1_rankOne_rankOne, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@A1_rankOne_rankOne) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointProjectionBounds.A1_rankOne_rankOne.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointProjectionBounds.RankOne.family
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
    owner := `D5.S3.Quantum.Semigroups.WuEndpointProjectionBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RankOne

namespace RankTwo

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (u : EndpointVector), ‖u‖ = 1 →
    ∀ (B : OrthonormalBasis (Fin 4) ℂ EndpointVector),
      R.readout () () (endpointProjector u *
        A₁ (endpointProjector (B 0) + endpointProjector (B 1))).trace.re endpointAlpha

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (standardBasis 0) (standardBasis.orthonormal.1 0) standardBasis

def family : Registration arena (type_of% @A1_rankOne_rankTwo_basis) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@A1_rankOne_rankTwo_basis, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@A1_rankOne_rankTwo_basis) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointProjectionBounds.A1_rankOne_rankTwo_basis.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointProjectionBounds.RankTwo.family
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
    owner := `D5.S3.Quantum.Semigroups.WuEndpointProjectionBounds
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

end RankTwo

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

namespace ProjectorTrace

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ v : EndpointVector, R.readout () () (endpointProjector v).trace (↑(‖v‖ ^ 2) : ℂ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0

def family : Registration arena (type_of% @trace_endpointProjector) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@trace_endpointProjector, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@trace_endpointProjector) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointProjectionBounds.trace_endpointProjector.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointProjectionBounds.TraceEqualities.ProjectorTrace.family
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
    owner := `D5.S3.Quantum.Semigroups.WuEndpointProjectionBounds
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

end ProjectorTrace


namespace ProjectorPairing

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (u : EndpointVector) (X : TwoMode),
    R.readout () () (endpointProjector u * X).trace ⟪u, X.toEuclideanLin u⟫_ℂ

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0

def family : Registration arena (type_of% @trace_endpointProjector_mul) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@trace_endpointProjector_mul, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@trace_endpointProjector_mul) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointProjectionBounds.trace_endpointProjector_mul.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointProjectionBounds.TraceEqualities.ProjectorPairing.family
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
    owner := `D5.S3.Quantum.Semigroups.WuEndpointProjectionBounds
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

end ProjectorPairing

end TraceEqualities
namespace ProjectorEqualities

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

namespace Resolution

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ B : OrthonormalBasis (Fin 4) ℂ EndpointVector, R.readout () () (∑ i, endpointProjector (B i)) 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h standardBasis

def family : Registration arena (type_of% @sum_endpointProjector) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sum_endpointProjector, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sum_endpointProjector) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointProjectionBounds.sum_endpointProjector.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointProjectionBounds.ProjectorEqualities.Resolution.family
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
    owner := `D5.S3.Quantum.Semigroups.WuEndpointProjectionBounds
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

end Resolution

end ProjectorEqualities

end Reg.D5.S3.Quantum.Semigroups.WuEndpointProjectionBounds
