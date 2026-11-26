import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
import Batteries.Tactic.OpenPrivate

/-! Source-bound readouts for the exact signed increment and the raised lower bound. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix LeanInformationAudit
open scoped BigOperators Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups
open _root_.D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open _root_.D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
open _root_.D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison (modeJump)
open private gamma h c e bias gibbsLow gibbsHigh jump_zero jump_one from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private cubic levelsAt totalAt source_centered_at from
  D5.S3.Quantum.Semigroups.WuCubicSignedTransfer

namespace Reg.D5.S3.Quantum.Semigroups.WuCubicSignedTransfer

private abbrev occupationEquiv : Occupation ≃ Fin 4 := finProdFinEquiv

private abbrev testFrame : Frame :=
  (1 : Matrix (Fin 4) (Fin 4) ℂ).submatrix occupationEquiv (Equiv.refl _)

private theorem testFrame_unitary : testFrameᴴ * testFrame = 1 ∧ testFrame * testFrameᴴ = 1 := by
  constructor
  · simp only [testFrame, conjTranspose_submatrix, conjTranspose_one,
      submatrix_mul_equiv, mul_one, submatrix_one_equiv]
  · simp only [testFrame, conjTranspose_submatrix, conjTranspose_one,
      submatrix_mul_equiv, mul_one, submatrix_one_equiv]

namespace SignedIncrement

private theorem occupationWeight (i j : Fin 4) :
    weight testFrame i j = ∑ k : Fin 2,
      Complex.normSq (modeJump k (occupationEquiv.symm i) (occupationEquiv.symm j)) := by
  simp only [weight, testFrame, conjTranspose_submatrix, conjTranspose_one,
    one_submatrix_mul, mul_submatrix_one, submatrix_apply, Function.comp_apply,
    Equiv.refl_apply, id_eq]

-- The parameters identify the measured loss of the proposed loss-free variation.
private abbrev Parameters := Σ _ : ℝ, Σ _ : Frame, Σ _ : ℝ, ℝ

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Parameters (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def withoutLoss : Realization signature :=
  realize signature (fun _ p x y =>
    let r := p.1
    let U := p.2.1
    let n := p.2.2.1
    let q := p.2.2.2
    x = y + (lossPlus r n q * weight U 3 2 + lossMinus r n q * weight U 2 3))
    (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ {r : ℝ}, 1 ≤ r →
    ∀ (U : Frame), Uᴴ * U = 1 → U * Uᴴ = 1 →
    ∀ {m n q : ℝ}, 0 ≤ m → m ≤ n → n ≤ q → q ≤ 1 →
    (W.readout () ⟨r, U, n, q⟩
      (sourceDeficitAt r U m n q - sourceDeficit r U m n)
      (scalarIncrement r U m n q + lowerIncrement r U m n q -
        (lossPlus r n q * weight U 3 2 + lossMinus r n q * weight U 2 3))) ∧
    0 ≤ lowerIncrement r U m n q ∧ 0 ≤ lossPlus r n q ∧ 0 ≤ lossMinus r n q

private theorem withoutLoss_fails : ¬ arena.Law withoutLoss := by
  intro hlaw
  -- The occupation frame and rational spectrum in section 4 of the research proof.
  have hr : (1 : ℝ) ≤ 6 / 5 := by norm_num
  have hm : (0 : ℝ) ≤ 16 / 25 := by norm_num
  have hmn : (16 / 25 : ℝ) ≤ 4 / 5 := by norm_num
  have hnq : (4 / 5 : ℝ) ≤ 81 / 100 := by norm_num
  have hq1 : (81 / 100 : ℝ) ≤ 1 := by norm_num
  have hbad := (hlaw hr testFrame testFrame_unitary.1 testFrame_unitary.2 hm hmn hnq hq1).1
  have hinc :=
    (signed_increment hr testFrame testFrame_unitary.1 testFrame_unitary.2 hm hmn hnq hq1).1
  have h2 : occupationEquiv.symm 2 = (1, 0) := by decide
  have h3 : occupationEquiv.symm 3 = (1, 1) := by decide
  have h32 : weight testFrame 3 2 = 0 := by
    norm_num [occupationWeight, h2, h3, Fin.sum_univ_two, jump_zero, jump_one,
      Matrix.kronecker_apply, Matrix.one_apply, Matrix.diagonal_apply, Complex.normSq_apply]
  have h23 : weight testFrame 2 3 = 1 := by
    norm_num [occupationWeight, h2, h3, Fin.sum_univ_two, jump_zero, jump_one,
      Matrix.kronecker_apply, Matrix.one_apply, Matrix.diagonal_apply, Complex.normSq_apply]
  have hloss : lossMinus (6 / 5) (4 / 5) (81 / 100) = 983727 / 136400000 := by
    norm_num [lossMinus, cubic, c, e, gamma]
  simp only [withoutLoss, realize, h32, h23, mul_zero, mul_one, zero_add, hloss] at hbad hinc
  linarith only [hbad, hinc]

def family : Registration arena (type_of% @signed_increment) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@signed_increment, withoutLoss, withoutLoss_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual withoutLoss withoutLoss_fails
  dependence := by
    intro role
    refine ⟨⟨1, testFrame, 0, 0⟩, 0, 1, ?_⟩
    intro hreadout
    exact one_ne_zero (Eq.mp (congrFun hreadout 0) (rfl : (0 : ℝ) = 0))

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@signed_increment) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicSignedTransfer.signed_increment.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicSignedTransfer.SignedIncrement.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
    definition := none
    coordinates := #[0, 2, 6, 7]
    readouts := #[{
      -- Twelve binders, then the equality in the first conjunct.
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SignedIncrement

namespace RaisedLowerBound

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def strict : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ {r : ℝ}, 1 ≤ r →
    ∀ (U : Frame), Uᴴ * U = 1 → U * Uᴴ = 1 →
    ∀ {m n q : ℝ}, 0 ≤ m → m ≤ n → n ≤ q → q ≤ 1 →
    let u := U.col 3
    let v := U.col 2
    let dp := lossPlus r n q
    let dm := lossMinus r n q
    let A := (dp + dm) / 2
    let rho := (dp - dm) / (dp + dm)
    W.readout () ()
      (gamma r * r * holder21 m n + gamma r * r^2 * holder12 m n + frameRemainder r U m n +
        scalarIncrement r U m n q + lowerIncrement r U m n q -
        A * (1 + rho * WuPhysicalHighHigh.imbalance u) * (1 - rho * WuPhysicalHighHigh.imbalance v) +
        A * ((2 - rho^2) / 4) * Complex.normSq (WuPhysicalHighHigh.eta u v) +
        A * Complex.normSq (WuPhysicalHighHigh.sigma u v + (rho : ℂ) * WuPhysicalHighHigh.tau u v))
      (sourceDeficitAt r U m n q)

private theorem strict_fails : ¬ arena.Law strict := by
  intro hlaw
  have hflat : sourceDeficitAt 1 testFrame 1 1 1 = 0 := by
    rw [source_centered_at le_rfl testFrame testFrame_unitary.1 testFrame_unitary.2
      zero_le_one zero_le_one zero_le_one]
    norm_num [h, gamma, gibbsLow, gibbsHigh, bias, totalAt, levelsAt, cubic,
      Fin.sum_univ_four]
  have hrep := repeated_middle_lower_bound (r := 1) le_rfl (WuOneModeCubic.one_mode_bound le_rfl)
    testFrame testFrame_unitary.1 testFrame_unitary.2 (m := 1) (n := 1) zero_le_one le_rfl le_rfl
  have hbad := hlaw (r := 1) le_rfl testFrame testFrame_unitary.1 testFrame_unitary.2
    (m := 1) (n := 1) (q := 1) zero_le_one le_rfl le_rfl le_rfl
  exact (not_lt_of_ge (add_nonneg hrep.1 hrep.2.1))
    (by simpa [strict, realize, scalarIncrement, lowerIncrement, lossPlus, lossMinus, hflat]
      using hbad)

def family : Registration arena (type_of% @raised_lower_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@raised_lower_bound, strict, strict_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual strict strict_fails
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro hreadout
    exact (by norm_num : ¬ (1 : ℝ) ≤ 0) (Eq.mp (congrFun hreadout 0) (le_rfl : (0 : ℝ) ≤ 0))

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@raised_lower_bound) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicSignedTransfer.raised_lower_bound.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicSignedTransfer.RaisedLowerBound.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
    definition := none
    coordinates := #[]
    readouts := #[{
      -- Twelve binders and six source lets, then the order relation.
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RaisedLowerBound

namespace SourceDeficitRectangle

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

private def reversed : Realization signature :=
  realize signature (fun _ _ x y => y < x) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ {r m n q : ℝ} (U : Frame), Uᴴ * U = 1 → U * Uᴴ = 1 →
    6 / 5 ≤ r → r ≤ 5 / 4 → 23 / 50 ≤ m → m ≤ 1 / 2 →
    9 / 10 ≤ n → n ≤ 23 / 25 → 0 ≤ q - n → q - n ≤ 1 / 40 →
    W.readout () () (1 / 200) (sourceDeficitAt r U m n q)

private theorem reversed_fails : ¬ arena.Law reversed := by
  intro hlaw
  have hactual := source_deficit_rectangle (r := 6 / 5) (m := 23 / 50)
    (n := 9 / 10) (q := 37 / 40) testFrame testFrame_unitary.1 testFrame_unitary.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hbad := hlaw (r := 6 / 5) (m := 23 / 50)
    (n := 9 / 10) (q := 37 / 40) testFrame testFrame_unitary.1 testFrame_unitary.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact not_lt_of_ge hactual.le hbad

def family : Registration arena (type_of% @source_deficit_rectangle) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@source_deficit_rectangle, reversed, reversed_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual reversed reversed_fails
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro hreadout
    exact (lt_irrefl (1 : ℝ)) (Eq.mp (congrFun hreadout 1) (zero_lt_one : (0 : ℝ) < 1))

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@source_deficit_rectangle) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicSignedTransfer.source_deficit_rectangle.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicSignedTransfer.SourceDeficitRectangle.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
    definition := none
    coordinates := #[]
    readouts := #[{
      -- Fifteen binders, then the order relation.
      path := #["body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SourceDeficitRectangle

end Reg.D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
