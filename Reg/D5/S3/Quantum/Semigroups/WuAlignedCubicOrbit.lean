import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuAlignedCubicOrbit

/-! Source-bound comparisons for both directed mixed traces and the cubic inequality. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix LeanInformationAudit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuAlignedCubicOrbit
open _root_.D5.S3.Quantum.Semigroups.WuCubicOperatorBridge (D G GInv Mat)
open _root_.D5.S3.Quantum.Semigroups.WuPhysicalHighHigh (phi psi)
open _root_.D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic (alpha)
open private GInv_mul_G G_mul_GInv from D5.S3.Quantum.Semigroups.WuCubicOperatorBridge

namespace Reg.D5.S3.Quantum.Semigroups.WuAlignedCubicOrbit

private def zeroData : AlignedData := ⟨0, 0, 0⟩

private theorem one_unitary : (1 : Block)ᴴ * 1 = 1 := by simp

namespace MixedTraces

private abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected (i : Bool) : Realization signature :=
  realize signature (fun j _ x y => if j = i then x ≠ y else x = y) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U : Block) (hU : Uᴴ * U = 1) (V : Block) (hV : Vᴴ * V = 1)
      (M N : AlignedData),
    let p := Complex.normSq (U 0 0)
    let D := diagonalFrame U.det
    let S := antidiagonalFrame U.det
    0 ≤ p ∧ p ≤ 1 ∧
    R.readout true () (oddConj V hV (orbitMatrix U N) * phi (oddConj V hV (orbitMatrix U M))).trace.re
      (p * (orbitMatrix D N * phi (orbitMatrix D M)).trace.re +
        (1 - p) * (orbitMatrix S N * phi (orbitMatrix S M)).trace.re) ∧
    R.readout false () (oddConj V hV (orbitMatrix U N) * psi (oddConj V hV (orbitMatrix U M))).trace.re
      (p * (orbitMatrix D N * psi (orbitMatrix D M)).trace.re +
        (1 - p) * (orbitMatrix S N * psi (orbitMatrix S M)).trace.re)

private theorem rejected_law (i : Bool) : ¬ arena.Law (rejected i) := by
  intro h
  have hbad := h 1 one_unitary 1 one_unitary zeroData zeroData
  have heq := directed_mixed_traces_affine 1 one_unitary 1 one_unitary zeroData zeroData
  cases i
  · have hpsi := hbad.2.2.2
    simp only [rejected, realize, if_pos rfl] at hpsi
    exact hpsi heq.2.2.2
  · have hphi := hbad.2.2.1
    simp only [rejected, realize, if_pos rfl] at hphi
    exact hphi heq.2.2.1

def family : Registration arena (type_of% @directed_mixed_traces_affine) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@directed_mixed_traces_affine, rejected true, rejected_law true⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j hj
      funext p x
      simp only [actual, rejected, realize, if_neg hj]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro hreadout
    exact (one_ne_zero : (1 : ℝ) ≠ 0) (Eq.mp (congrFun hreadout 0) rfl)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@directed_mixed_traces_affine) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuAlignedCubicOrbit.directed_mixed_traces_affine.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuAlignedCubicOrbit.MixedTraces.family
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
    owner := `D5.S3.Quantum.Semigroups.WuAlignedCubicOrbit
    definition := none
    coordinates := #[]
    readouts := #[
      -- Bool.fintype lists true first. Six binders and three lets precede the conjunctions.
      { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
          "arg", "arg", "fn", "arg", "fn", "fn"]
        stateBinder := 0, functionOperand := true, stateOperand := none
        booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
          "arg", "arg", "arg", "fn", "fn"]
        stateBinder := 0, functionOperand := true, stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MixedTraces

namespace CubicInequality

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ x y => ¬ x ≤ y) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r : ℝ}, 1 ≤ r → ∀ {X : Mat} (U : Block),
    Uᴴ * U = 1 → ∀ (V : Block) (hV : Vᴴ * V = 1) (d : AlignedData),
    (∀ i, (pairedBlock d i).PosSemidef) →
    G r * X * G r = oddConj V hV (orbitMatrix U d) →
    let M := G r * X * G r
    R.readout () ()
      (alpha r * ((M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D r))).trace.re -
        (M ^ 3).trace.re * Real.log (M ^ 3).trace.re))
      ((9 / 8 : ℝ) * (M ^ 2 * (G r * wickGenerator r X * G r)).trace.re)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hlaw
  have hr : (1 : ℝ) ≤ 1 := le_rfl
  have hd (i : Fin 2) : (pairedBlock zeroData i).PosSemidef := by
    have hz : pairedBlock zeroData i = 0 := by
      ext j k
      fin_cases j <;> fin_cases k <;> simp [pairedBlock, zeroData]
    rw [hz]
    exact Matrix.PosSemidef.zero
  let M := oddConj 1 one_unitary (orbitMatrix 1 zeroData)
  let X := GInv 1 * M * GInv 1
  have hAligned : G 1 * X * G 1 = M := by
    calc
      _ = (G 1 * GInv 1) * M * (GInv 1 * G 1) := by simp only [X, Matrix.mul_assoc]
      _ = _ := by rw [G_mul_GInv hr, GInv_mul_G hr, Matrix.one_mul, Matrix.mul_one]
  have hbad := hlaw hr (X := X) 1 one_unitary 1 one_unitary zeroData hd hAligned
  simp only [rejected, realize] at hbad
  exact hbad (cubic_inequality_rotated_aligned hr (X := X) 1 one_unitary 1 one_unitary
    zeroData hd hAligned)

def family : Registration arena (type_of% @cubic_inequality_rotated_aligned) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cubic_inequality_rotated_aligned, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro hreadout
    have h : (0 : ℝ) ≤ 0 := le_rfl
    have h' : (1 : ℝ) ≤ 0 := Eq.mp (congrFun hreadout 0) h
    exact (not_le_of_gt zero_lt_one) h'

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cubic_inequality_rotated_aligned) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuAlignedCubicOrbit.cubic_inequality_rotated_aligned.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuAlignedCubicOrbit.CubicInequality.family
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
    owner := `D5.S3.Quantum.Semigroups.WuAlignedCubicOrbit
    definition := none
    coordinates := #[]
    readouts := #[{
      -- Ten quantified binders and one let body lead to LE.le on ℝ.
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0, functionOperand := true, stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CubicInequality

end Reg.D5.S3.Quantum.Semigroups.WuAlignedCubicOrbit
