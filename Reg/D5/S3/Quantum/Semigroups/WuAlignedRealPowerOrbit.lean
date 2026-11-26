import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuAlignedRealPowerOrbit

/-! Source-bound affine equalities for each directed CAR trace and the full deficit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuCubicOperatorBridge (Occupation)
open _root_.D5.S3.Quantum.Semigroups.WuAlignedCubicOrbit
  (Block AlignedData orbitMatrix diagonalFrame antidiagonalFrame)
open _root_.D5.S3.Quantum.Semigroups.WuAlignedRealPowerOrbit

namespace Reg.D5.S3.Quantum.Semigroups.WuAlignedRealPowerOrbit

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ x y => x ≠ y) (fun e => nomatch e)

private def zeroData : AlignedData := ⟨0, 0, 0⟩

private theorem one_unitary : (1 : Block)ᴴ * 1 = 1 := by simp

private theorem dependence (i : signature.Role) :
    ∃ (p : signature.Params) (x y : signature.State p),
      actual.readout i p x ≠ actual.readout i p y := by
  refine ⟨(), 0, 1, ?_⟩
  intro hreadout
  exact (one_ne_zero : (1 : ℝ) ≠ 0) (Eq.mp (congrFun hreadout 0) rfl)

namespace MixedTrace

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U : Block) (hU : Uᴴ * U = 1) (M N : AlignedData)
      (k : Fin 2) (reverse : Bool),
    let J := directedJump k reverse
    let p := Complex.normSq (U 0 0)
    let V := diagonalFrame U.det
    let W := antidiagonalFrame U.det
    R.readout () () (orbitMatrix U N * (Jᴴ * orbitMatrix U M * J)).trace.re
      (p * (orbitMatrix V N * (Jᴴ * orbitMatrix V M * J)).trace.re +
        (1 - p) * (orbitMatrix W N * (Jᴴ * orbitMatrix W M * J)).trace.re)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 one_unitary zeroData zeroData 0 false
    (mode_mixed_trace_affine 1 one_unitary zeroData zeroData 0 false)

def family : Registration arena (type_of% @mode_mixed_trace_affine) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@mode_mixed_trace_affine, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mode_mixed_trace_affine) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuAlignedRealPowerOrbit.mode_mixed_trace_affine.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuAlignedRealPowerOrbit.MixedTrace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
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
    owner := `D5.S3.Quantum.Semigroups.WuAlignedRealPowerOrbit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0, functionOperand := true, stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MixedTrace

namespace Deficit

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (s α : ℝ) (projectionRate mixedRate : Fin 2 → Bool → ℝ)
      (logDensity : Occupation → ℝ) (U : Block) (hU : Uᴴ * U = 1) (d : AlignedData),
    let p := Complex.normSq (U 0 0)
    let V := diagonalFrame U.det
    let W := antidiagonalFrame U.det
    let deficit := weightedDeficit s α projectionRate mixedRate logDensity
    0 ≤ p ∧ p ≤ 1 ∧
    R.readout () () (deficit (orbitMatrix U d))
      (p * deficit (orbitMatrix V d) + (1 - p) * deficit (orbitMatrix W d))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h 2 0 0 0 0 1 one_unitary zeroData).2.2
    (realPowerDeficit_affine 2 0 0 0 0 1 one_unitary zeroData).2.2

def family : Registration arena (type_of% @realPowerDeficit_affine) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@realPowerDeficit_affine, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@realPowerDeficit_affine) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuAlignedRealPowerOrbit.realPowerDeficit_affine.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuAlignedRealPowerOrbit.Deficit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
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
    owner := `D5.S3.Quantum.Semigroups.WuAlignedRealPowerOrbit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "fn"]
      stateBinder := 0, functionOperand := true, stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Deficit

end Reg.D5.S3.Quantum.Semigroups.WuAlignedRealPowerOrbit
