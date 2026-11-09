import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.ZeroAbscissaPower
import D5.S3.Weil.Mertens.IntegratedExplicit.RHActualHSqrtBound
import Reg.Support.SingleDependentReadout

/-! Source-bound dependent readouts for the actual weighted zero-sum estimates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.ZeroAbscissaPower
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open Filter
open scoped Topology

namespace Reg.D5.S3.Weil.Mertens.ZeroAbscissaPower

namespace Primitive

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ y => actualH y)
  (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∃ C : ℝ, 0 < C ∧ ∀ β x a b T : ℝ,
    0 ≤ β → β ≤ 1 → (∀ k : ℕ, (actualZero k).re ≤ β) →
    4 ≤ x → x / 2 ≤ a → x / 2 ≤ b → 2 ≤ T →
    ‖R.readout false () (Real.log b) / b - R.readout true () (Real.log a) / a‖ ≤
      C * |b - a| * x ^ (β - 2) * (1 + Real.log T) ^ 2 +
        C * x ^ (β - 1) * (1 + Real.log T) / T

def shifted (i : Bool) : Realization signature :=
  realize signature (fun j _ y => actualH y + if j = i then 1 else 0)
    (fun e => nomatch e)

private theorem shifted_bad (i : Bool) : ¬ arena.Law (shifted i) := by
  classical
  rintro ⟨C, hC, h⟩
  have hnorm : ‖(shifted i).readout false () (Real.log 2) / 2 -
      (shifted i).readout true () (Real.log 2) / 2‖ = (1 / 2 : ℝ) := by
    cases i
    · have he : ‖(actualH (Real.log 2) + 1) / 2 - actualH (Real.log 2) / 2‖ =
          (1 / 2 : ℝ) := by
        rw [show (actualH (Real.log 2) + 1) / 2 - actualH (Real.log 2) / 2 =
          (1 / 2 : ℂ) by ring]
        norm_num
      simpa [shifted, realize] using he
    · have he : ‖actualH (Real.log 2) / 2 - (actualH (Real.log 2) + 1) / 2‖ =
          (1 / 2 : ℝ) := by
        rw [show actualH (Real.log 2) / 2 - (actualH (Real.log 2) + 1) / 2 =
          -(1 / 2 : ℂ) by ring]
        norm_num
      simpa [shifted, realize] using he
  have heach (T : ℝ) (hT : 2 ≤ T) : (1 / 2 : ℝ) ≤ C * (1 + Real.log T) / T := by
    have hz := h 1 4 2 2 T (by norm_num) le_rfl
      (fun k => (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2.2.le)
      (by norm_num) (by norm_num) (by norm_num) hT
    norm_num at hz
    rw [hnorm] at hz
    exact hz
  have hlim : Tendsto (fun T : ℝ => C * (1 + Real.log T) / T) atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := C)).mul
      ((tendsto_inv_atTop_zero : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0)).add
        Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero)
    convert hh using 1 <;> try (simp only [add_zero, mul_zero])
    funext T
    dsimp
    ring
  have hsmall := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨T, hT, hsmallT⟩ := ((eventually_ge_atTop (2 : ℝ)).and hsmall).exists
  exact (not_lt_of_ge (heach T hT)) hsmallT

def evidence : Registration arena (type_of% @actual_primitive_low_high) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_primitive_low_high, shifted false, shifted_bad false⟩
  sensitivity := by
    classical
    constructor
    · intro i
      refine ⟨shifted i, ?_, rfl, shifted_bad i⟩
      intro j hj
      funext p y
      dsimp only [actual, shifted, realize]
      split_ifs with hji
      · exact (hj hji).elim
      · simp
        rfl
    · intro e
      exact nomatch e
  dependence := by
    intro i
    obtain ⟨y, hy⟩ := actualH_nonconstant
    exact ⟨(), (0 : ℝ), y, hy.symm⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    actual_primitive_low_high (Realization signature) (ℝ → ℂ) Unit where
  unitName := `D5.S3.Weil.Mertens.ZeroAbscissaPower.actual_primitive_low_high.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.ZeroAbscissaPower.Primitive.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.ZeroAbscissaPower
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[ "arg", "body", "arg", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn",
        "arg", "arg", "fn", "arg", "fn", "arg", "fn" ]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #[ "arg", "body", "arg", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn",
        "arg", "arg", "arg", "fn", "arg", "fn" ]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Primitive

abbrev psiSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def psiActual : Realization psiSignature := realize psiSignature (fun _ _ x => Chebyshev.psi x)
  (fun e => nomatch e)

def cubic : Realization psiSignature := realize psiSignature (fun _ _ x => x ^ (3 : ℕ))
  (fun e => nomatch e)

private theorem psi_dependence : ObservationalDependence psiSignature psiActual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change Chebyshev.psi 1 ≠ Chebyshev.psi 2
  rw [Chebyshev.psi_one]
  exact Ne.symm (by simp)

namespace Weighted

def arena : Arena where
  signature := psiSignature
  Law R := ∃ C : ℝ, 0 < C ∧ ∀ β x h T : ℝ,
    0 ≤ β → β ≤ 1 → (∀ k : ℕ, (actualZero k).re ≤ β) →
    4 ≤ x → 1 ≤ h → h ≤ x / 2 → 2 ≤ T →
    |R.readout () () x - x| ≤ h +
      C * x ^ β * (1 + Real.log T) ^ 2 +
        C * x ^ (β + 1) * (1 + Real.log T) / (h * T)

private theorem rejected_law : ¬ arena.Law cubic := by
  rintro ⟨C, hC, h⟩
  let L : ℝ := 1 + Real.log 2
  let K : ℝ := L ^ 2 + L
  let x : ℝ := C * K + 4
  have hL : 1 ≤ L := by dsimp only [L]; linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hx : 4 ≤ x := by dsimp only [x]; nlinarith
  have hx0 : 0 < x := by linarith
  have hh := h 1 x (x / 2) 2 (by norm_num) le_rfl
    (fun k => (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2.2.le)
    hx (by linarith) le_rfl (by norm_num)
  change |x ^ (3 : ℕ) - x| ≤ _ at hh
  norm_num only [Real.rpow_one, Real.rpow_two] at hh
  have hdiv : C * x ^ 2 * (1 + Real.log 2) / (x / 2 * 2) = C * x * L := by
    dsimp only [L]
    field_simp
    <;> ring
  rw [hdiv] at hh
  have hid : x / 2 + C * x * (1 + Real.log 2) ^ 2 + C * x * L = x / 2 + C * x * K := by
    dsimp only [K, L]
    ring
  rw [hid] at hh
  have hself := (le_abs_self (x ^ (3 : ℕ) - x)).trans hh
  have he : C * K = x - 4 := by dsimp only [x]; ring
  nlinarith

def evidence : Registration arena (type_of% @actual_psi_low_high) where
  actual := psiActual
  bridge := Iff.rfl
  variation := ⟨actual_psi_low_high, cubic, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law psiActual cubic rejected_law
  dependence := psi_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    actual_psi_low_high (Realization psiSignature) (ℝ → ℝ) Unit where
  unitName := `D5.S3.Weil.Mertens.ZeroAbscissaPower.actual_psi_low_high.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.ZeroAbscissaPower.Weighted.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize psiSignature psiActual.readout psiActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.ZeroAbscissaPower
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[ "arg", "body", "arg", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg",
        "arg", "fn", "arg", "fn" ]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Weighted

namespace Power

open _root_.D5.S3.Arith.Robin.ForwardKernel.KappaGap

def arena : Arena where
  signature := psiSignature
  Law R := ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |R.readout () () x - x| ≤ C * x ^ (zeroAbscissa + ε)

private theorem rejected_law : ¬ arena.Law cubic := by
  intro h
  have hΘ : zeroAbscissa ≤ 1 := by
    apply csSup_le (show (Complex.re '' {ρ : ℂ | _root_.D5.S3.Weil.ZeroSum.IsNontrivialZero ρ}).Nonempty from
      ⟨(actualZero 0).re, actualZero 0,
        actualData.zero_isNontrivial (actualOccurrenceEquiv 0).1, rfl⟩)
    rintro r ⟨ρ, hρ, rfl⟩
    exact hρ.2.2.le
  obtain ⟨C, hC⟩ := h (2 - zeroAbscissa) (by linarith)
  let x : ℝ := |C| + 4
  have hx : 4 ≤ x := by dsimp only [x]; linarith [abs_nonneg C]
  have hh := hC x (by linarith)
  change |x ^ (3 : ℕ) - x| ≤ C * x ^ (zeroAbscissa + (2 - zeroAbscissa)) at hh
  rw [show zeroAbscissa + (2 - zeroAbscissa) = 2 by ring, Real.rpow_two] at hh
  have hself := (le_abs_self (x ^ (3 : ℕ) - x)).trans hh
  have hxC : C + 4 ≤ x := by dsimp only [x]; linarith [le_abs_self C]
  have hmul := mul_le_mul_of_nonneg_right hxC (sq_nonneg x)
  nlinarith

def evidence : Registration arena (type_of% @actual_zero_abscissa_power_bound) where
  actual := psiActual
  bridge := Iff.rfl
  variation := ⟨actual_zero_abscissa_power_bound, cubic, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law psiActual cubic rejected_law
  dependence := psi_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    actual_zero_abscissa_power_bound (Realization psiSignature) (ℝ → ℝ) Unit where
  unitName := `D5.S3.Weil.Mertens.ZeroAbscissaPower.actual_zero_abscissa_power_bound.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.ZeroAbscissaPower.Power.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize psiSignature psiActual.readout psiActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.ZeroAbscissaPower
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[ "body", "body", "arg", "body", "body", "body", "fn", "arg",
        "arg", "fn", "arg", "fn" ]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Power

#print axioms Primitive.evidence
#print axioms Weighted.evidence
#print axioms Power.evidence

end Reg.D5.S3.Weil.Mertens.ZeroAbscissaPower
