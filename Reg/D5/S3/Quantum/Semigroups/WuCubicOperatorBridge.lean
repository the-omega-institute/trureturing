import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
import Batteries.Tactic.OpenPrivate

/-! The comparison of the cubic Gibbs entropy and Dirichlet term, with equality at zero. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix LeanInformationAudit
open scoped BigOperators ComplexOrder Matrix MatrixOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
open _root_.D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic (alpha)

namespace Reg.D5.S3.Quantum.Semigroups.WuCubicOperatorBridge

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ {r : ℝ}, 1 ≤ r →
    ∀ (U : Frame), Uᴴ * U = 1 → U * Uᴴ = 1 →
    ∀ {m n L : ℝ}, 0 ≤ m → m ≤ n → n ≤ L →
    let v : Fin 4 → ℝ := ![m, n, n, L]
    let M := U * diagonal (fun i => (v i : ℂ)) * Uᴴ
    let X := GInv r * M * GInv r
    W.readout () ()
      (alpha r * ((M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D r))).trace.re -
        (M ^ 3).trace.re * Real.log (M ^ 3).trace.re))
      ((9 / 8 : ℝ) * (M ^ 2 * (G r * generator r X * G r)).trace.re)

private abbrev occupationEquiv : Occupation ≃ Fin 4 := finProdFinEquiv

private abbrev testFrame : Frame :=
  (1 : Matrix (Fin 4) (Fin 4) ℂ).submatrix occupationEquiv (Equiv.refl _)

private theorem testFrame_unitary : testFrameᴴ * testFrame = 1 ∧
    testFrame * testFrameᴴ = 1 := by
  constructor <;> simp only [testFrame, conjTranspose_submatrix, conjTranspose_one,
    submatrix_mul_equiv, mul_one, submatrix_one_equiv]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hlaw
  have hstrict := hlaw (r := 1) le_rfl testFrame testFrame_unitary.1
    testFrame_unitary.2 (m := 0) (n := 0) (L := 0) le_rfl le_rfl le_rfl
  dsimp only [rejected, realize] at hstrict
  have hLevels : (fun i => ((![0, 0, 0, 0] : Fin 4 → ℝ) i : ℂ)) = fun _ => 0 := by
    funext i
    fin_cases i <;> simp
  -- Here both M and X vanish, so the strict comparator reads 0 < 0.
  simpa [hLevels] using hstrict

def family : Registration arena (type_of% @source_operator_inequality_unnormalized) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@source_operator_inequality_unnormalized, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro hreadout
    have h : (0 : ℝ) ≤ 0 := le_rfl
    have h' : (1 : ℝ) ≤ 0 := Eq.mp (congrFun hreadout 0) h
    exact (by norm_num : ¬ (1 : ℝ) ≤ 0) h'

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@source_operator_inequality_unnormalized) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Semigroups.WuCubicOperatorBridge.source_operator_inequality_unnormalized.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicOperatorBridge.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      -- Eleven quantified binders and three let bodies lead to the binary comparator.
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace ModularIdentity

open _root_.D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison (modeJump)
open private gibbsLow gibbsHigh from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Mat)
    (fun _ => Mat → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ x y => x ≠ y) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ {r : ℝ}, 1 ≤ r → ∀ M : Mat,
    W.readout () ()
      (G r * generator r (GInv r * M * GInv r) * G r)
      (∑ k : Fin 2, ((gibbsLow r : ℂ) •
          (((modeJump k)ᴴ * modeJump k) * M + M * ((modeJump k)ᴴ * modeJump k)) -
        (2 * (gibbsLow r : ℂ) * (r : ℂ)) • ((modeJump k)ᴴ * M * modeJump k) +
        (gibbsHigh r : ℂ) •
          ((modeJump k * (modeJump k)ᴴ) * M + M * (modeJump k * (modeJump k)ᴴ)) -
        (2 * (gibbsHigh r : ℂ) * (r : ℂ)⁻¹) •
          (modeJump k * M * (modeJump k)ᴴ)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h (r := 1) le_rfl 0) (operator_trace_modular_identity (r := 1) le_rfl 0)

def family : Registration arena (type_of% @operator_trace_modular_identity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@operator_trace_modular_identity, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro hreadout
    exact (one_ne_zero : (1 : Mat) ≠ 0) (Eq.mp (congrFun hreadout 0) rfl)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@operator_trace_modular_identity) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicOperatorBridge.operator_trace_modular_identity.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicOperatorBridge.ModularIdentity.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      -- The bodies of r, hr and M lead to Eq applied to both matrix expressions.
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ModularIdentity

end Reg.D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
