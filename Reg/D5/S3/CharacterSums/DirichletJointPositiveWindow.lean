import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.DirichletJointPositiveWindow
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Reg.Support.SingleDependentReadout

/-! Source-equivalence candidates for the finite chord observation in both window laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.CharacterSums.DirichletJointPositiveWindow

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.CharacterSums.DirichletJointPositiveWindow
open DirichletPositiveWindowChord LeanInformationAudit Set MeasureTheory

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℝ → ℝ) (fun _ => ℝ → ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ => integerChordIntegralSum) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ f Y H => integerChordIntegralSum f Y H + Y ^ 2)
    (fun e => nomatch e)

private def witnessCharacter : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

private theorem witnessCharacter_ne_one : witnessCharacter ≠ 1 := by
  intro h
  have he := congrArg (fun χ : DirichletCharacter ℂ 4 => χ (3 : ZMod 4)) h
  have hunit : IsUnit (3 : ZMod 4) := by decide
  rw [MulChar.one_apply hunit] at he
  change ((ZMod.χ₄ (3 : ℕ) : ℤ) : ℂ) = 1 at he
  rw [ZMod.χ₄_nat_three_mod_four (by decide)] at he
  norm_num at he

private theorem zeroRamp (x : ℝ) : jointRamp witnessCharacter 0 0 x = 0 := by
  simp [jointRamp]

private theorem zeroIntegral (Y H : ℝ) :
    (∫ x in Y..H, positiveDensity (jointRamp witnessCharacter 0 0) x) = 0 := by
  simp [positiveDensity, zeroRamp]

private theorem zeroChordSum (Y H : ℝ) :
    integerChordIntegralSum (fun _ => 0) Y H = 0 := by
  simp [integerChordIntegralSum, chordIntegralSum, positiveDensity, chord]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hMass : integerChordIntegralSum (fun _ => 1) 1 2 = ∫ x in (1 : ℝ)..2, weight x := by
    unfold integerChordIntegralSum chordIntegralSum
    rw [show ⌈(2 : ℝ)⌉₊ - ⌊(1 : ℝ)⌋₊ = 1 by norm_num, Finset.sum_range_one]
    rw [show integerWindowGrid 1 2 0 = 1 by norm_num [integerWindowGrid]]
    rw [show integerWindowGrid 1 2 1 = 2 by norm_num [integerWindowGrid]]
    apply intervalIntegral.integral_congr
    intro x _
    unfold positiveDensity chord
    rw [show (2 - x) / (2 - 1) * 1 + (x - 1) / (2 - 1) * 1 = 1 by ring, max_eq_left zero_le_one, one_mul]
  have hpos : 0 < ∫ x in (1 : ℝ)..2, weight x := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      exact continuousOn_id.rpow_const fun x hx =>
        Or.inl (((by norm_num : (0 : ℝ) < 1).trans_le hx.1).ne')
    · exact fun x hx => Real.rpow_pos_of_pos ((by norm_num : (0 : ℝ) < 1).trans hx.1) _
    · norm_num
  have he := congrFun (congrFun h (1 : ℝ)) (2 : ℝ)
  change integerChordIntegralSum (fun _ => 0) 1 2 =
    integerChordIntegralSum (fun _ => 1) 1 2 at he
  rw [zeroChordSum, hMass] at he
  exact hpos.ne' he.symm

namespace FiniteWindow

def arena : Arena where
  signature := signature
  Law L := ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (_hχ : χ ≠ 1) {a b Y H : ℝ} (_ha : 0 ≤ a) (_hY : 0 < Y) (_hYH : Y < H),
    let g := jointRamp χ a b
    let Q := L.readout () () g Y H
    Q ≤ (∫ x in Y..H, positiveDensity g x) ∧
      (∫ x in Y..H, positiveDensity g x) ≤
        Q + a / (4 * Y) * (Y ^ (-(1 / 2) : ℝ) - H ^ (-(1 / 2) : ℝ)) ∧
      (∫ x in Y..H, positiveDensity g x) ≤ Q + a / (4 * Y ^ (3 / 2 : ℝ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h witnessCharacter_ne_one (a := 0) (b := 0) (Y := 1) (H := 2)
    le_rfl zero_lt_one (by norm_num)).1
  change integerChordIntegralSum (jointRamp witnessCharacter 0 0) 1 2 + 1 ^ 2 ≤ _ at hbad
  have hz : jointRamp witnessCharacter 0 0 = fun _ => 0 := funext zeroRamp
  rw [zeroIntegral, hz, zeroChordSum] at hbad
  norm_num at hbad

def family : Registration arena (type_of% (@jointRamp_positive_window_bounds)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@jointRamp_positive_window_bounds, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@jointRamp_positive_window_bounds) (Realization signature) Unit Unit where
  unitName := `D5.S3.CharacterSums.DirichletJointPositiveWindow.jointRamp_positive_window_bounds.audit
  realizationName := `Reg.D5.S3.CharacterSums.DirichletJointPositiveWindow.FiniteWindow.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletJointPositiveWindow
    definition := none
    coordinates := #[]
    -- Select the observation function in Q, which is shared by all three inequalities.
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "value", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FiniteWindow

namespace SubpowerWindows

def arena : Arena where
  signature := signature
  Law L := ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (_hχ : χ ≠ 1) {a b δ : ℝ} (_ha : 0 ≤ a) (_hδ : 0 < δ),
    let g := jointRamp χ a b
    (∀ η : ℝ, 0 < η → ∀ Y₀ : ℝ, ∃ Y : ℝ, max 2 Y₀ ≤ Y ∧
      (∫ x in Y..Y ^ (1 + δ), positiveDensity g x) ≤ Y ^ η) ↔
    (∀ η : ℝ, 0 < η → ∀ Y₀ : ℝ, ∃ Y : ℝ, max 2 Y₀ ≤ Y ∧
      L.readout () () g Y (Y ^ (1 + δ)) ≤ Y ^ η)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hwindow := h witnessCharacter_ne_one (a := 0) (b := 0) (δ := 1) le_rfl zero_lt_one
  have hI : ∀ η : ℝ, 0 < η → ∀ Y₀ : ℝ, ∃ Y : ℝ, max 2 Y₀ ≤ Y ∧
      (∫ x in Y..Y ^ (1 + (1 : ℝ)), positiveDensity (jointRamp witnessCharacter 0 0) x) ≤ Y ^ η := by
    intro η _ Y₀
    refine ⟨max 2 Y₀, le_rfl, ?_⟩
    rw [zeroIntegral]
    exact Real.rpow_nonneg (by positivity) _
  obtain ⟨Y, hY, hbad⟩ := hwindow.mp hI 1 zero_lt_one 2
  change integerChordIntegralSum (jointRamp witnessCharacter 0 0) Y (Y ^ (1 + (1 : ℝ))) +
    Y ^ 2 ≤ Y ^ (1 : ℝ) at hbad
  have hz : jointRamp witnessCharacter 0 0 = fun _ => 0 := funext zeroRamp
  rw [hz, zeroChordSum, zero_add, Real.rpow_one] at hbad
  have hY2 : 2 ≤ Y := (le_max_left _ _).trans hY
  have hprod : 0 < Y * (Y - 1) := mul_pos (by linarith) (by linarith)
  nlinarith only [hbad, hprod]

def family : Registration arena (type_of% (@jointRamp_subpower_windows_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@jointRamp_subpower_windows_iff, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@jointRamp_subpower_windows_iff) (Realization signature) Unit Unit where
  unitName := `D5.S3.CharacterSums.DirichletJointPositiveWindow.jointRamp_subpower_windows_iff.audit
  realizationName := `Reg.D5.S3.CharacterSums.DirichletJointPositiveWindow.SubpowerWindows.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletJointPositiveWindow
    definition := none
    coordinates := #[]
    -- Select the observation function in the quantified chord condition.
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "body", "body", "body", "arg", "body",
        "arg", "fn", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SubpowerWindows

end Reg.D5.S3.CharacterSums.DirichletJointPositiveWindow
