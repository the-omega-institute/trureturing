import D5.S3.Arith.Robin.OriginalMovingCutBudget
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
open _root_.D5.S3.Arith.Robin.OriginalMovingWindowMoment
open _root_.D5.S3.Arith.Robin.OriginalMovingCutRow
open _root_.D5.S3.Arith.Robin.OriginalMovingCutBudget
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open MeasureTheory Set
open scoped BigOperators

/- Source-owner information audit is unfinished, tracked in
   https://github.com/the-omega-institute/trureturing/issues/15968.
   The exact actual/rejected laws, equivalence bridges and whole-family
   variation/sensitivity proofs below are retained. No Contract.Registration
   is fabricated: actual observational dependence on qualifying rows/sets
   and lawful sourceSelection/current binding remain missing. No validated
   four-slot registration is claimed. -/

namespace Reg.D5.S3.Arith.Robin.OriginalMovingCutBudget

abbrev rowSignature : Signature where
  Params := ℝ × ℝ × ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def rowActual : Realization rowSignature :=
  realize rowSignature (fun _ p d => latticeRowRemainder p.1 p.2.1 p.2.2 d)
    (fun e => nomatch e)

def rowRejected : Realization rowSignature :=
  realize rowSignature
    (fun _ p _ => 3 * lowerHeight p.2.2 * Real.log (2 * p.2.2) + 1)
    (fun e => nomatch e)

abbrev rowArena : Arena where
  signature := rowSignature
  Law V := ∀ {ell R t : ℝ}, 256 ≤ ell → ell < R → t ∈ Set.Icc ell R →
    ∀ {d : ℕ}, 1 ≤ d →
      |V.readout () (ell, R, t) d| ≤ 3 * lowerHeight t * Real.log (2 * t)

private theorem rowActual_law : rowArena.Law rowActual := @original_cut_row_lattice_estimate

private theorem rowRejected_law : ¬ rowArena.Law rowRejected := by
  intro h
  have hh := h (ell := 256) (R := 257) (t := 256) (by norm_num) (by norm_num)
    (by norm_num) (d := 1) (by norm_num)
  change |3 * lowerHeight 256 * Real.log (2 * 256) + 1| ≤ _ at hh
  linarith [le_abs_self (3 * lowerHeight 256 * Real.log (2 * 256) + 1)]

private theorem rowVariation : Variation rowArena rowActual :=
  ⟨rowActual_law, rowRejected, rowRejected_law⟩

private theorem rowSensitivity : Sensitivity rowArena rowActual := by
  constructor
  · intro i
    refine ⟨rowRejected, ?_, rfl, rowRejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim
  · intro e
    exact nomatch e

private theorem rowBridge :
    (type_of% (@original_cut_row_lattice_estimate)) ↔ rowArena.Law rowActual := Iff.rfl

abbrev pointArena : Arena where
  signature := rowSignature
  Law V := ∀ {ell R t : ℝ}, 256 ≤ ell → ell < R → t ∈ Set.Icc ell R →
    ∑ d ∈ Finset.Icc 1 ⌊endpoint t ^ (151 / 500 : ℝ)⌋₊,
      |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * |V.readout () (ell, R, t) d| ≤
        6 * t ^ (-99 / 500 : ℝ) * Real.log (2 * t)

def pointRejected : Realization rowSignature :=
  realize rowSignature
    (fun _ p _ => 6 * p.2.2 ^ (-99 / 500 : ℝ) * Real.log (2 * p.2.2) + 1)
    (fun e => nomatch e)

private theorem pointActual_law : pointArena.Law rowActual := @original_cut_row_pointwise_budget

private theorem pointRejected_law : ¬ pointArena.Law pointRejected := by
  intro h
  have hh := h (ell := 256) (R := 257) (t := 256) (by norm_num) (by norm_num)
    (by norm_num)
  let C : ℝ := 6 * (256 : ℝ) ^ (-99 / 500 : ℝ) * Real.log (2 * 256)
  change (∑ d ∈ Finset.Icc 1 ⌊endpoint 256 ^ (151 / 500 : ℝ)⌋₊,
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * |C + 1|) ≤ C at hh
  have hB : 1 ≤ endpoint (256 : ℝ) := by
    have hp := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 256) (4 / 5 : ℝ)
    dsimp [endpoint, width]
    linarith
  have hfloor : 1 ≤ ⌊endpoint 256 ^ (151 / 500 : ℝ)⌋₊ := by
    apply Nat.le_floor
    simpa using Real.one_le_rpow hB (by norm_num : (0 : ℝ) ≤ 151 / 500)
  have hs := Finset.single_le_sum
    (f := fun d : ℕ => |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * |C + 1|)
    (s := Finset.Icc 1 ⌊endpoint 256 ^ (151 / 500 : ℝ)⌋₊)
    (fun d _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    (Finset.mem_Icc.mpr ⟨le_rfl, hfloor⟩)
  simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, abs_one, one_mul] at hs
  linarith [le_abs_self (C + 1)]

private theorem pointVariation : Variation pointArena rowActual :=
  ⟨pointActual_law, pointRejected, pointRejected_law⟩

private theorem pointSensitivity : Sensitivity pointArena rowActual := by
  constructor
  · intro i
    refine ⟨pointRejected, ?_, rfl, pointRejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim
  · intro e
    exact nomatch e

private theorem pointBridge :
    (type_of% (@original_cut_row_pointwise_budget)) ↔ pointArena.Law rowActual := Iff.rfl


#print axioms rowBridge
#print axioms rowVariation
#print axioms rowSensitivity
#print axioms pointBridge
#print axioms pointVariation
#print axioms pointSensitivity

end Reg.D5.S3.Arith.Robin.OriginalMovingCutBudget
