import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Weil.Separator.WeilSmallSupportCoercive
import D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData

/-! The squared L² mass in the margin is the selected readout in each source law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Weil.Separator.WeilSmallSupportCoercive

open LeanInformationAudit MeasureTheory Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.TestFunctions
open _root_.D5.S3.Weil.ZeroSum
open _root_.D5.S3.Weil.Separator.UnconditionalExplicitFormula
open _root_.D5.S3.Weil.Separator.WeilSmallSupportCoercive
open _root_.D5.S3.Weil.ZetaBridge.PrimeJumpDecomposition
open _root_.D5.S3.Weil.ZetaBridge.SymmetricConvergentOfZetaSummable
open _root_.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
open _root_.D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData (zetaZeroData)

abbrev signature : Signature where
  Params := Unit
  State _ := WeilTestFunction
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def mass : Realization signature :=
  realize signature (fun _ _ f => l2Mass f) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private def zeroTest : WeilTestFunction where
  toFun := fun _ => 0
  contDiff' := contDiff_const
  hasCompactSupport' := by simp [HasCompactSupport]
  even' := by simp

private theorem zeroTest_apply (x : ℝ) : zeroTest x = 0 := rfl

private theorem zeroTest_support :
    tsupport (zeroTest : ℝ → ℂ) ⊆ Icc (-(1 / 20 : ℝ)) (1 / 20) := by
  change tsupport (fun _ : ℝ => (0 : ℂ)) ⊆ _
  simp

private theorem mass_dependence : ObservationalDependence signature mass := by
  intro role
  refine ⟨(), zeroTest, standardTestFunction, ?_⟩
  change l2Mass zeroTest ≠ l2Mass standardTestFunction
  have hPos : 0 < l2Mass standardTestFunction := by
    unfold l2Mass
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (Complex.continuous_normSq.comp standardTestFunction.continuous)
      (standardTestFunction.hasCompactSupport.comp_left (by simp))
      (fun x => Complex.normSq_nonneg (standardTestFunction x)) (x := 0) ?_
    simp
  simpa [l2Mass, zeroTest_apply] using (ne_of_gt hPos).symm

private theorem sensitive (law : Realization signature → Prop)
    (hBad : ¬ law rejected) : Sensitivity ⟨signature, law⟩ mass := by
  constructor
  · intro i
    exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, hBad⟩
  · intro e
    exact nomatch e

abbrev gammaArena : Arena where
  signature := signature
  Law R := ∀ (f : WeilTestFunction),
    tsupport (f : ℝ → ℂ) ⊆ Icc (-(1 / 20 : ℝ)) (1 / 20) →
      (1 / 20 : ℝ) * R.readout () () f ≤
        archimedeanConstant * l2Mass f + archimedeanJumpEnergy f

private theorem gamma_rejected : ¬ gammaArena.Law rejected := by
  intro h
  have hZero := h zeroTest zeroTest_support
  norm_num [rejected, realize, l2Mass, archimedeanJumpEnergy, translationEnergy,
    zeroTest_apply] at hZero

def gammaFamily : Registration gammaArena (type_of% @smallSupport_gamma_coercive) where
  actual := mass
  bridge := Iff.rfl
  variation := ⟨smallSupport_gamma_coercive, rejected, gamma_rejected⟩
  sensitivity := sensitive gammaArena.Law gamma_rejected
  dependence := mass_dependence

def gammaAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@smallSupport_gamma_coercive) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Weil.Separator.WeilSmallSupportCoercive.smallSupport_gamma_coercive.__information_unit
  realizationName := `Reg.D5.S3.Weil.Separator.WeilSmallSupportCoercive.gammaFamily
  realizationSource := none
  generated := false
  arena := .source ⟨gammaArena⟩
  objectArena := .source ⟨gammaArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source gammaArena ⟨gammaFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => l2Mass f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Separator.WeilSmallSupportCoercive
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "fn", "arg", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev weilArena : Arena where
  signature := signature
  Law R := ∀ (Z : ZeroData) (f : WeilTestFunction),
    tsupport (f : ℝ → ℂ) ⊆ Icc (-(1 / 20 : ℝ)) (1 / 20) →
      2 * Complex.normSq (∫ x : ℝ, Complex.exp ((x : ℂ) / 2) * f x) +
        (1 / 20 : ℝ) * R.readout () () f ≤
      (zeroSum Z (convolutionSquare f)
        (symmetricConvergent_of_zeroData Z (convolutionSquare f))).re

private theorem weil_rejected : ¬ weilArena.Law rejected := by
  intro h
  have hZero := h zetaZeroData zeroTest zeroTest_support
  change 2 * Complex.normSq (∫ x : ℝ, Complex.exp ((x : ℂ) / 2) * zeroTest x) +
      (1 / 20 : ℝ) * 1 ≤
    (zeroSum zetaZeroData (convolutionSquare zeroTest)
      (symmetricConvergent_of_zeroData zetaZeroData (convolutionSquare zeroTest))).re at hZero
  rw [energyIdentity_unconditional zetaZeroData zeroTest (1 / 20) zeroTest_support] at hZero
  norm_num [l2Mass, archimedeanJumpEnergy, arithmeticJumpEnergy, translationEnergy,
    zeroTest_apply] at hZero

def weilFamily : Registration weilArena (type_of% @smallSupport_weil_positive) where
  actual := mass
  bridge := Iff.rfl
  variation := ⟨smallSupport_weil_positive, rejected, weil_rejected⟩
  sensitivity := sensitive weilArena.Law weil_rejected
  dependence := mass_dependence

def weilAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@smallSupport_weil_positive) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Weil.Separator.WeilSmallSupportCoercive.smallSupport_weil_positive.__information_unit
  realizationName := `Reg.D5.S3.Weil.Separator.WeilSmallSupportCoercive.weilFamily
  realizationSource := none
  generated := false
  arena := .source ⟨weilArena⟩
  objectArena := .source ⟨weilArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source weilArena ⟨weilFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => l2Mass f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Separator.WeilSmallSupportCoercive
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "body", "fn", "arg", "arg", "arg"]
        stateBinder := 1
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Separator.WeilSmallSupportCoercive
