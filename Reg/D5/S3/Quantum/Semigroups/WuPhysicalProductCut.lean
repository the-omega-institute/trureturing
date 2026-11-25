import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuPhysicalProductCut

/-! Source-bound readouts for the imbalance and distance of the physical cut. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix Kronecker
open scoped Matrix
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (pauliMatrix)
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.WuRankOneEndpointFloor

namespace Reg.D5.S3.Quantum.Semigroups.WuPhysicalProductCut

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
  exact (zero_ne_one : (0 : ℝ) ≠ 1) (Eq.mp (congrFun h 0) rfl).symm

private abbrev testCut : TwoMode := carProductCut (carDirection 1 0 0 0) 0 1

private theorem testCut_projection :
    testCut.IsHermitian ∧ testCut * testCut = testCut ∧ testCut.trace = 2 :=
  let ⟨h, hi, ht, _⟩ := carProductCut_projection 1 0 0 0 0 1 (by norm_num) (by norm_num)
  ⟨h, hi, ht⟩

namespace Projection

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ a b c d u rho : ℝ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1 →
    u ^ 2 + rho ^ 2 = 1 →
    let Q := carProductCut (carDirection a b c d) u rho
    Q.IsHermitian ∧ Q * Q = Q ∧ Q.trace = 2 ∧
      W.readout () () (carImbalance * Q).trace.re rho

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h 1 0 0 0 0 1 (by norm_num) (by norm_num)).2.2.2

def family : Registration arena (type_of% @carProductCut_projection) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@carProductCut_projection, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@carProductCut_projection) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuPhysicalProductCut.carProductCut_projection.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuPhysicalProductCut.Projection.family
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
    owner := `D5.S3.Quantum.Semigroups.WuPhysicalProductCut
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Projection

namespace Distance

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ (P : TwoMode), P.IsHermitian → P * P = P → P.trace = 2 →
    ∀ a b c d u rho : ℝ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1 →
    u ^ 2 + rho ^ 2 = 1 →
    let G := carDirection a b c d
    let H := (2 : ℂ) • P - 1
    let Q := carProductCut G u rho
    W.readout () () ((P - Q)ᴴ * (P - Q)).trace.re
      (2 - (u * (H * G).trace.re + rho * (H * carPartner G).trace.re) / 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨hs, hi, ht⟩ := testCut_projection
  exact h testCut hs hi ht 1 0 0 0 0 1 (by norm_num) (by norm_num)

def family : Registration arena (type_of% @carProductCut_distance) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@carProductCut_distance, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@carProductCut_distance) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuPhysicalProductCut.carProductCut_distance.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuPhysicalProductCut.Distance.family
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
    owner := `D5.S3.Quantum.Semigroups.WuPhysicalProductCut
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Distance

namespace Transport

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ (P : TwoMode), P.IsHermitian → P * P = P → P.trace = 2 →
    let H := (2 : ℂ) • P - 1
    let k := carFirstNorm H
    let R := (carImbalance * P).trace.re
    let theta := Real.sqrt (k ^ 2 + R ^ 2)
    ∃ a b c d u rho : ℝ,
      a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1 ∧ u ^ 2 + rho ^ 2 = 1 ∧
      theta ≤ 1 ∧ theta * u = k ∧ theta * rho = R ∧
      (let Q := carProductCut (carDirection a b c d) u rho
       Q.IsHermitian ∧ Q * Q = Q ∧ Q.trace = 2 ∧
       (carImbalance * Q).trace.re = rho ∧
       W.readout () () ((P - Q)ᴴ * (P - Q)).trace.re (2 * (1 - theta)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨hs, hi, ht⟩ := testCut_projection
  obtain ⟨a, b, c, d, u, rho, _, _, _, _, _, _, _, _, _, contradiction⟩ := h testCut hs hi ht
  exact contradiction

def family : Registration arena (type_of% @carProductCut_transport) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@carProductCut_transport, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@carProductCut_transport) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuPhysicalProductCut.carProductCut_transport.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuPhysicalProductCut.Transport.family
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
    owner := `D5.S3.Quantum.Semigroups.WuPhysicalProductCut
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "body", "arg", "body", "arg", "arg", "arg", "arg",
        "arg", "body", "arg", "arg", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Transport

namespace ModeRotation

private abbrev matrixSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => TwoMode)
    (fun _ => TwoMode → Prop)

private def matrixEquality : Realization matrixSignature :=
  realize matrixSignature (fun _ _ x y => x = y) (fun e => nomatch e)

private def impossible : Realization matrixSignature :=
  realize matrixSignature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem matrixDependence : ObservationalDependence matrixSignature matrixEquality := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (zero_ne_one : (0 : TwoMode) ≠ 1) (Eq.mp (congrFun h 0) rfl).symm

private abbrev arena : Arena where
  signature := matrixSignature
  Law W := ∀ a b c d u rho : ℝ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1 →
    let z := (a : ℂ) - (b : ℂ) * Complex.I
    let w := (c : ℂ) - (d : ℂ) * Complex.I
    let J₁ : TwoMode := Matrix.single (0, 0) (0, 1) 1 - Matrix.single (1, 0) (1, 1) 1
    let J₂ : TwoMode := Matrix.single (0, 0) (1, 0) 1 + Matrix.single (0, 1) (1, 1) 1
    let q : Qubit :=
      (1 / 2 : ℂ) • (1 + (u : ℂ) • pauliMatrix .X + (rho : ℂ) • pauliMatrix .Z)
    ∃ U : TwoMode, U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧ U * carImbalance = carImbalance * U ∧
      W.readout () () (U * ((1 : Qubit) ⊗ₖ q) * Uᴴ)
        (carProductCut (carDirection a b c d) u rho) ∧
      U * J₁ * Uᴴ = z • J₁ + w • J₂ ∧ U * J₂ * Uᴴ = (-star w) • J₁ + star z • J₂

private theorem rejected_law : ¬ arena.Law impossible := by
  intro h
  obtain ⟨U, _, _, _, contradiction, _, _⟩ := h 1 0 0 0 0 1 (by norm_num)
  exact contradiction

def family : Registration arena (type_of% @carProductCut_modeRotation) where
  actual := matrixEquality
  bridge := Iff.rfl
  variation := ⟨@carProductCut_modeRotation, impossible, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law matrixEquality impossible rejected_law
  dependence := matrixDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@carProductCut_modeRotation) (Realization matrixSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuPhysicalProductCut.carProductCut_modeRotation.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuPhysicalProductCut.ModeRotation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuPhysicalProductCut
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body", "arg", "arg",
        "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ModeRotation

end Reg.D5.S3.Quantum.Semigroups.WuPhysicalProductCut
