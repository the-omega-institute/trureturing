import D5.S3.Weil.Mertens.RobinAdaptiveWindow
import Reg.D5.S3.Weil.Mertens.RobinCenteredChord

/-! Observe the actual weighted mass in the whole-window error bound while
keeping the arithmetic samples and the mesh fixed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Real LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (psiErrorKernel)
open _root_.D5.S3.Weil.Mertens.RobinAdaptiveWindow
open _root_.D5.S3.Weil.Mertens.WeightedTailWindowMass (weightedNegativeMass)
open _root_.Reg.D5.S3.Weil.Mertens.RobinCenteredChord (massSignature massEvidence)

namespace Reg.D5.S3.Weil.Mertens.RobinAdaptiveWindow

private def observe (f : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Realization massSignature :=
  realize massSignature (fun _ _ => f) (fun e => nomatch e)

def samplingArena : Arena where
  signature := massSignature
  Law V := ∀ {A B : ℝ}, exp 1 ≤ A → A ≤ B →
    |V.readout () () psiErrorKernel A B - windowChordSum A B| ≤ 9 * geometricConstant ∧
    ((samplePoints A B).card : ℝ) ≤
      geometricConstant * B ^ (1 / 4 : ℝ) + (blockCount A B : ℝ) + 1 ∧
    ((samplePoints A B).card : ℝ) ≤ 2 * geometricConstant * B ^ (1 / 4 : ℝ) + 1

private def shifted : Realization massSignature :=
  observe (fun k a b => weightedNegativeMass k a b + (9 * geometricConstant + 1))

private lemma shifted_rejected : ¬ samplingArena.Law shifted := by
  intro law
  have h := (law (A := 3) (B := 3) exp_one_lt_three.le le_rfl).1
  change |weightedNegativeMass psiErrorKernel 3 3 + (9 * geometricConstant + 1) -
    windowChordSum 3 3| ≤ _ at h
  rw [(degenerate_window 3 (by norm_num)).2.1] at h
  simp only [weightedNegativeMass, intervalIntegral.integral_same, zero_add, sub_zero] at h
  linarith only [(le_abs_self (9 * geometricConstant + 1)).trans h]

def samplingEvidence : Registration samplingArena (type_of% @window_sampling) where
  actual := observe weightedNegativeMass
  bridge := Iff.rfl
  variation := ⟨@window_sampling, shifted, shifted_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    samplingArena.Law (observe weightedNegativeMass) shifted shifted_rejected
  dependence := massEvidence.dependence

def samplingAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@window_sampling) (Realization massSignature) Unit Unit where
  unitName := .str ``window_sampling "__information_unit"
  realizationName := ``samplingEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨samplingArena⟩
  objectArena := .source ⟨samplingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source samplingArena ⟨samplingEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize massSignature (fun _ _ => weightedNegativeMass) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.RobinAdaptiveWindow
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg",
        "fn", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.RobinAdaptiveWindow
