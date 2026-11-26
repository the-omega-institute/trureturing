import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuCubicConditionalTensorization
import Batteries.Tactic.OpenPrivate

/-! Source-bound readout of the real order in the occupation-conditioned cubic bound. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix LeanInformationAudit
open scoped BigOperators ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuCubicOperatorBridge (D G GInv Mat generator)
open _root_.D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic (alpha)
open _root_.D5.S3.Quantum.Semigroups.WuCubicConditionalTensorization (occupation_conditional_bound)
open private Qubit from D5.S3.Quantum.Semigroups.WuCubicConditionalTensorization

namespace Reg.D5.S3.Quantum.Semigroups.WuCubicConditionalTensorization

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def strict : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ {r : ℝ} (_hr : 1 ≤ r) {A B : Qubit}
    (_hA : A.PosSemidef) (_hB : B.PosSemidef),
    let M := (Matrix.blockDiagonal ![A,B]).submatrix Prod.swap Prod.swap
    let X := GInv r * M * GInv r
    W.readout () ()
      (alpha r * ((M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D r))).trace.re -
        (M ^ 3).trace.re * Real.log (M ^ 3).trace.re))
      ((9 / 8 : ℝ) * (M ^ 2 * (G r * generator r X * G r)).trace.re)

private theorem strict_fails : ¬ arena.Law strict := by
  intro hlaw
  have hpsd : (0 : Qubit).PosSemidef := Matrix.PosSemidef.zero
  have hbad := hlaw (r := 1) le_rfl (A := 0) (B := 0) hpsd hpsd
  have hblocks : ![(0 : Qubit), 0] = (0 : Fin 2 → Qubit) := by
    funext i
    fin_cases i <;> rfl
  have hM : (Matrix.blockDiagonal ![(0 : Qubit), 0]).submatrix Prod.swap Prod.swap = (0 : Mat) := by
    rw [hblocks, Matrix.blockDiagonal_zero, Matrix.submatrix_zero]
    rfl
  have hstrict : (0 : ℝ) < 0 := by
    simpa only [strict, realize, hM, zero_pow (by decide : (3 : ℕ) ≠ 0),
      zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, Matrix.trace_zero, Complex.zero_re,
      sub_zero, mul_zero] using hbad
  exact (lt_irrefl 0) hstrict

def family : Registration arena (type_of% @occupation_conditional_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@occupation_conditional_bound, strict, strict_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual strict strict_fails
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro hreadout
    exact (not_le_of_gt zero_lt_one) (Eq.mp (congrFun hreadout 0) (le_rfl : (0 : ℝ) ≤ 0))

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@occupation_conditional_bound) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Semigroups.WuCubicConditionalTensorization.occupation_conditional_bound.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicConditionalTensorization.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicConditionalTensorization
    definition := none
    coordinates := #[]
    readouts := #[{
      -- Six quantified binders and two let bodies precede the real-order readout.
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Semigroups.WuCubicConditionalTensorization
