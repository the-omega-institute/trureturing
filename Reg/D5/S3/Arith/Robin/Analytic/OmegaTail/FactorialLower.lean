import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialLower
import Reg.Support.SingleDependentReadout

/-! The logarithmic lower bound of the literal factorial tail. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Filter Real Finset LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialLower
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail.FarDeletion
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail.Selection (selectedCount)
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTailUpper (threshold scale)
open _root_.D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel (primeInterval)

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialLower

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def lowerBound : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev tailArena : Arena where
  signature := signature
  Law O := ∀ (r : ℕ) (hr : 2 ≤ r) (ε : ℝ) (hε : 0 < ε)
    (base : ℝ → Finset ℕ) (D : ℝ → ℝ)
    (hD : Tendsto (fun P => D P / (P / log P ^ r)) atTop (𝓝 (r.factorial : ℝ))),
    let T := fun P : ℝ => P * ∑ j ∈ range r, (j.factorial : ℝ) / log P ^ (j + 1)
    (∀ᶠ P in atTop, base P ⊆ Nat.primesLE ⌊P⌋₊ ∧
      T P < ((base P).card : ℝ) ∧
      (∑ p ∈ base P, log (p : ℝ)) ≤ P - D P ∧
      (∀ p : ℕ, Nat.Prime p → 3 * P / 4 < (p : ℝ) → (p : ℝ) ≤ P → p ∈ base P)) →
    ∀ᶠ P in atTop,
      let tailCount := ((Icc 1 ⌊exp P⌋₊).filter (fun n : ℕ =>
        T P < (ArithmeticFunction.cardDistinctFactors n : ℝ))).card
      0 < tailCount ∧
      O.readout () () ((π * sqrt (2 * (r.factorial : ℝ) / 3) - ε) *
        (P / log P ^ (((r : ℝ) + 1) / 2))) (log (tailCount : ℝ))

private theorem tail_rejected : ¬ tailArena.Law rejected := by
  intro h
  let reserve := safeReserve
  have hreserve : Tendsto (fun P => reserve P / (P / log P ^ 2)) atTop
      (𝓝 ((2 : ℕ).factorial : ℝ)) := by
    simpa [reserve, Nat.factorial_succ] using centered_reserve.2.2.2.2.2
  let good (P : ℝ) (R : Finset ℕ) :=
    R ⊆ primeInterval (P / 2) (3 / 4 * P) ∧ R.card = deletionCount P
  let R (P : ℝ) : Finset ℕ := if h : ∃ R, good P R then h.choose else ∅
  let base (P : ℝ) := Nat.primesLE ⌊P⌋₊ \ R P
  have hbase : ∀ᶠ P : ℝ in atTop,
      base P ⊆ Nat.primesLE ⌊P⌋₊ ∧
      P * (∑ j ∈ range 2, (j.factorial : ℝ) / log P ^ (j + 1)) < ((base P).card : ℝ) ∧
      (∑ p ∈ base P, log (p : ℝ)) ≤ P - reserve P ∧
      (∀ p : ℕ, Nat.Prime p → 3 * P / 4 < (p : ℝ) → (p : ℝ) ≤ P → p ∈ base P) := by
    filter_upwards [far_deletion, eventually_gt_atTop (1 : ℝ)] with P hfar hP
    have hgood : ∃ R, good P R := by
      obtain ⟨R, hsub, hcard⟩ := hfar.2.1
      exact ⟨R, hsub, hcard⟩
    have hR : good P (R P) := by
      simpa only [R, dite_eq_left hgood] using hgood.choose_spec
    obtain ⟨hcard, hsum⟩ := hfar.2.2 (R P) hR.1 hR.2
    have hT : P * (∑ j ∈ range 2, (j.factorial : ℝ) / log P ^ (j + 1)) =
        threshold 1 (exp P) := by
      simp only [sum_range_succ, sum_range_zero, zero_add, Nat.factorial_zero, Nat.factorial_one,
        Nat.cast_one, zero_add, pow_one, threshold, scale, log_exp, one_mul]
      norm_num
      field_simp [(log_pos hP).ne']
    refine ⟨sdiff_subset, ?_, hsum, ?_⟩
    · rw [hT, show (base P).card = centeredCount P from hcard]
      simpa only [centeredCount, selectedCount, Nat.cast_add, Nat.cast_one] using
        (Nat.lt_floor_add_one (threshold 1 (exp P)))
    · intro p hp hlow hhigh
      refine mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr
        ⟨(Nat.le_floor_iff (zero_lt_one.trans hP).le).mpr hhigh, hp⟩, ?_⟩
      intro hpR
      have hupper := ((hfar.1 p).mp (hR.1 hpR)).2.1
      linarith
  obtain ⟨_, _, hfalse⟩ := (h 2 (by norm_num) 1 (by norm_num) base reserve hreserve hbase).exists
  exact hfalse

def tailFamily : Registration tailArena (type_of% @factorial_tail_lower) where
  actual := lowerBound
  bridge := Iff.rfl
  variation := ⟨@factorial_tail_lower, rejected, tail_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    tailArena.Law lowerBound rejected tail_rejected
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
    norm_num at hh

def tailAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@factorial_tail_lower) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialLower.factorial_tail_lower.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialLower.tailFamily
  realizationSource := none
  generated := false
  arena := .source ⟨tailArena⟩
  objectArena := .source ⟨tailArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source tailArena ⟨tailFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature lowerBound.readout lowerBound.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialLower
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialLower
