import D5.S3.Weil.Mertens.RobinAdaptiveWindow
import Reg.D5.S3.Weil.Mertens.RobinCenteredChord
import Reg.D5.S3.Weil.Mertens.RobinWeightedRamp

/-! Observe the block count, signed arithmetic values, and actual weighted mass
in adaptive Robin windows. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Real LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (psiErrorKernel)
open _root_.D5.S3.Weil.Mertens.RobinWeightedRamp (R u)
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

namespace Degenerate

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → ℕ)

private def observeCount (f : ℝ → ℝ → ℕ) : Realization signature :=
  realize signature (fun _ _ => f) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V := ∀ (A : ℝ), 0 < A →
    V.readout () () A A = 0 ∧ windowChordSum A A = 0 ∧ samplePoints A A = {A}

private def oneBlock : Realization signature := observeCount fun _ _ => 1

private lemma one_rejected : ¬ arena.Law oneBlock := by
  intro law
  have h : (1 : ℕ) = 0 := (law 1 one_pos).1
  exact Nat.one_ne_zero h

def evidence : Registration arena (type_of% @degenerate_window) where
  actual := observeCount blockCount
  bridge := Iff.rfl
  variation := ⟨@degenerate_window, oneBlock, one_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law (observeCount blockCount) oneBlock one_rejected
  dependence := by
    intro _
    refine ⟨(), (1 : ℝ), (2 : ℝ), ?_⟩
    change blockCount 1 ≠ blockCount 2
    intro h
    have heq := congrFun h 2
    have h12 : blockCount 1 2 = 1 := by
      simp [blockCount, logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    rw [h12, (degenerate_window 2 (by norm_num)).1] at heq
    exact Nat.one_ne_zero heq

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@degenerate_window) (Realization signature) Unit Unit where
  unitName := .str ``degenerate_window "__information_unit"
  realizationName := ``evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => blockCount) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.RobinAdaptiveWindow
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Degenerate

namespace ArithmeticSample

open _root_.Reg.D5.S3.Weil.Mertens.RobinWeightedRamp (signature sumEvidence)

private def observeRamp (f : ℝ → ℝ) : Realization signature :=
  realize signature (fun _ _ => f) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V := ∀ {A B x : ℝ}, exp 1 ≤ A → A ≤ B → x ∈ samplePoints A B →
    V.readout () () x = (∑ n ∈ Finset.Icc 2 ⌊B⌋₊, ArithmeticFunction.vonMangoldt n *
      max (u x / u (n : ℝ) - 1) 0) - u x * (log (log x) + eulerMascheroniConstant) + x

private def shiftedRamp : Realization signature := observeRamp fun x => R x + 1

private lemma shifted_rejected : ¬ arena.Law shiftedRamp := by
  intro law
  have hx : (3 : ℝ) ∈ samplePoints 3 3 := by
    rw [(degenerate_window 3 (by norm_num)).2.2]
    simp
  have h := law exp_one_lt_three.le le_rfl hx
  change R 3 + 1 = _ at h
  linarith only [h, sample_value_eq_sum exp_one_lt_three.le le_rfl hx]

def evidence : Registration arena (type_of% @sample_value_eq_sum) where
  actual := observeRamp R
  bridge := Iff.rfl
  variation := ⟨@sample_value_eq_sum, shiftedRamp, shifted_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law (observeRamp R) shiftedRamp shifted_rejected
  dependence := sumEvidence.dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sample_value_eq_sum) (Realization signature) Unit Unit where
  unitName := .str ``sample_value_eq_sum "__information_unit"
  realizationName := ``evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => R) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.RobinAdaptiveWindow
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ArithmeticSample

namespace ArithmeticTransfer

def arena : Arena where
  signature := massSignature
  Law V :=
    (∀ {A B : ℝ}, exp 1 ≤ A → A ≤ B → arithmeticWindowChordSum A B = windowChordSum A B) ∧
    ∀ {b : ℝ}, 1 ≤ b →
    (∀ η : ℝ, 0 < η → ∃ᶠ Y : ℝ in atTop, arithmeticWindowChordSum Y (Y ^ b) ≤ Y ^ η) →
    ∀ η : ℝ, 0 < η → ∃ᶠ Y : ℝ in atTop, V.readout () () psiErrorKernel Y (Y ^ b) ≤ Y ^ η

private def linearMass : Realization massSignature := observe fun _ a _ => a

private lemma linear_rejected : ¬ arena.Law linearMass := by
  rintro ⟨hexact, htransfer⟩
  have hsmall (η : ℝ) (_ : 0 < η) :
      ∃ᶠ Y : ℝ in atTop, arithmeticWindowChordSum Y (Y ^ (1 : ℝ)) ≤ Y ^ η := by
    apply Eventually.frequently
    filter_upwards [eventually_ge_atTop (exp 1)] with Y hY
    have hpos := (exp_pos 1).trans_le hY
    rw [rpow_one, hexact hY le_rfl, (degenerate_window Y hpos).2.1]
    exact rpow_nonneg hpos.le _
  have h := htransfer (b := (1 : ℝ)) le_rfl hsmall (1 / 2) (by norm_num)
  obtain ⟨Y, hmass, hY⟩ := (h.and_eventually (eventually_gt_atTop (1 : ℝ))).exists
  change Y ≤ Y ^ (1 / 2 : ℝ) at hmass
  exact (not_le_of_gt (rpow_lt_self_of_one_lt hY (by norm_num))) hmass

def evidence : Registration arena (type_of% @arithmetic_window_sampling) where
  actual := observe weightedNegativeMass
  bridge := Iff.rfl
  variation := ⟨@arithmetic_window_sampling, linearMass, linear_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law (observe weightedNegativeMass) linearMass linear_rejected
  dependence := massEvidence.dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@arithmetic_window_sampling) (Realization massSignature) Unit Unit where
  unitName := .str ``arithmetic_window_sampling "__information_unit"
  realizationName := ``evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
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
      path := #["arg", "body", "body", "body", "body", "body", "fn", "arg", "body",
        "fn", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ArithmeticTransfer

end Reg.D5.S3.Weil.Mertens.RobinAdaptiveWindow
