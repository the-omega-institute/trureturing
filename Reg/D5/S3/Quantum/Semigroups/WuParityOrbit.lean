import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuParityOrbit

/-! Source-bound comparisons for the cubic parity identity and inequality. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix LeanInformationAudit
open scoped BigOperators ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuCubicOperatorBridge (D G Mat generator)
open _root_.D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic (alpha)
open _root_.D5.S3.Quantum.Semigroups.WuParityOrbit

namespace Reg.D5.S3.Quantum.Semigroups.WuParityOrbit

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

namespace OrbitIdentity

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ x y => x ≠ y) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ {r : ℝ}, 1 ≤ r → ∀ (c : ℝ) {A B : Qubit}
    (hA : A.IsHermitian) (hB : B.IsHermitian),
    let v := hA.eigenvalues
    let w := hB.eigenvalues
    let p := Complex.normSq ((hA.eigenvectorUnitary : Qubit) 0 1)
    let q := Complex.normSq ((hB.eigenvectorUnitary : Qubit) 0 1)
    let endpoint (x y : Fin 2 → ℝ) := cubicDeficit r c (diagonalEndpoint x y)
    W.readout () ()
      (cubicDeficit r c (parityBlocks ![A,B]))
      (((1 - p) * (1 - q)) * endpoint v w +
        ((1 - p) * q) * endpoint v ![w 1, w 0] +
        (p * (1 - q)) * endpoint ![v 1, v 0] w +
        (p * q) * endpoint ![v 1, v 0] ![w 1, w 0])

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hlaw
  have hzero : (0 : Qubit).IsHermitian := Matrix.isHermitian_zero
  exact (hlaw (r := 1) le_rfl 0 (A := 0) (B := 0) hzero hzero)
    (cubicDeficit_parity_orbit (r := 1) le_rfl 0 hzero hzero)

def family : Registration arena (type_of% @cubicDeficit_parity_orbit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cubicDeficit_parity_orbit, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro hreadout
    exact (one_ne_zero : (1 : ℝ) ≠ 0) (Eq.mp (congrFun hreadout 0) rfl)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cubicDeficit_parity_orbit) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuParityOrbit.cubicDeficit_parity_orbit.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuParityOrbit.OrbitIdentity.family
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
    owner := `D5.S3.Quantum.Semigroups.WuParityOrbit
    definition := none
    coordinates := #[]
    readouts := #[{
      -- Seven quantified binders and five let bodies lead to Eq on ℝ.
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end OrbitIdentity

namespace ParityInequality

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ {r : ℝ}, 1 ≤ r → ∀ {X : Mat}, X.PosSemidef → Commute parityOperator X →
    let M := G r * X * G r
    W.readout () ()
      (alpha r * ((M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D r))).trace.re -
        (M ^ 3).trace.re * Real.log (M ^ 3).trace.re))
      ((9 / 8 : ℝ) * (M ^ 2 * (G r * generator r X * G r)).trace.re)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hlaw
  have hzero : (0 : Mat).PosSemidef := Matrix.PosSemidef.zero
  have hcommute : Commute parityOperator (0 : Mat) := Commute.zero_right parityOperator
  have hstrict := hlaw (r := 1) le_rfl (X := 0) hzero hcommute
  have hbad : (0 : ℝ) < 0 := by
    simpa only [rejected, realize, mul_zero, zero_mul, Matrix.trace_zero, Complex.zero_re,
      sub_zero, zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (2 : ℕ) ≠ 0)]
      using hstrict
  exact (lt_irrefl 0) hbad

def family : Registration arena (type_of% @cubic_inequality_of_commute_parity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cubic_inequality_of_commute_parity, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro hreadout
    have h : (0 : ℝ) ≤ 0 := le_rfl
    have h' : (1 : ℝ) ≤ 0 := Eq.mp (congrFun hreadout 0) h
    exact (not_le_of_gt zero_lt_one) h'

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cubic_inequality_of_commute_parity) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuParityOrbit.cubic_inequality_of_commute_parity.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuParityOrbit.ParityInequality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
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
    owner := `D5.S3.Quantum.Semigroups.WuParityOrbit
    definition := none
    coordinates := #[]
    readouts := #[{
      -- Five quantified binders and one let body lead to LE.le on ℝ.
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ParityInequality

end Reg.D5.S3.Quantum.Semigroups.WuParityOrbit
