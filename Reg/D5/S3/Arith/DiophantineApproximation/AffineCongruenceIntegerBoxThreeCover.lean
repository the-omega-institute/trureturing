import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Arith.DiophantineApproximation.AffineCongruenceIntegerBoxThreeCover
import Mathlib.Tactic

/-! Source registration for the reciprocal width in the denominator bound. -/

namespace Reg.D5.S3.Arith.DiophantineApproximation.AffineCongruenceIntegerBoxThreeCover

open LeanInformationAudit
open _root_.D5.S3.Arith.DiophantineApproximation.AffineCongruenceIntegerBoxThreeCover
  (ShortLabel delta errorSum phase radius short_label_miss_obstruction)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (sensitivity)
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ w => 1 / w) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N : Fin 3 → ℤ) (θ : Fin 3 → ℝ) (t w : ℝ)
    (hw : 0 < w) (hNw : ∀ i, (43 : ℝ) / 9 < (N i : ℝ) * w)
    (hmiss : ¬ ∃ (b : Fin 3 → ℤ) (a : ℤ),
      (∀ i, N i ≤ b i ∧ b i ≤ 2 * N i) ∧
      t < (∑ i, (b i : ℝ) * θ i) - (a : ℝ) ∧
      (∑ i, (b i : ℝ) * θ i) - (a : ℝ) < t + w),
    ∃ L : ShortLabel N θ w,
      (∀ L' : ShortLabel N θ w, L' = L) ∧
      (∀ n : ℤ, radius N L.h L.p θ w - (L.h : ℝ) * errorSum L.h L.p θ ≤
        |(n : ℝ) - phase N L.h L.p θ t w|) ∧
      ((L.h : ℝ) * w + ∑ i, ((N i : ℝ) - 2 * (L.h : ℝ)) * |delta L.h L.p θ i|) ≤ 1 ∧
      (L.h : ℝ) ≤ R.readout () () w

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let N : Fin 3 → ℤ := fun _ => 10
  let θ : Fin 3 → ℝ := fun _ => 0
  have hNw (i : Fin 3) : (43 : ℝ) / 9 < (N i : ℝ) * (1 / 2) := by
    norm_num [N]
  have hmiss : ¬ ∃ (b : Fin 3 → ℤ) (a : ℤ),
      (∀ i, N i ≤ b i ∧ b i ≤ 2 * N i) ∧
      (0 : ℝ) < (∑ i, (b i : ℝ) * θ i) - (a : ℝ) ∧
      (∑ i, (b i : ℝ) * θ i) - (a : ℝ) < 0 + (1 / 2 : ℝ) := by
    rintro ⟨b, a, _, hlo, hhi⟩
    simp only [θ, mul_zero, Finset.sum_const_zero, zero_sub, zero_add] at hlo hhi
    have ha : (0 : ℤ) < -a := by exact_mod_cast hlo
    have haOne : (1 : ℤ) ≤ -a := by omega
    have haReal : (1 : ℝ) ≤ -(a : ℝ) := by exact_mod_cast haOne
    linarith only [hhi, haReal]
  obtain ⟨L, _, _, _, hbound⟩ := law N θ 0 (1 / 2) (by norm_num) hNw hmiss
  have hpos : (1 : ℝ) ≤ (L.h : ℝ) := by exact_mod_cast L.positive
  change (L.h : ℝ) ≤ 0 at hbound
  linarith only [hpos, hbound]

def family : Registration arena (type_of% (@short_label_miss_obstruction)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@short_label_miss_obstruction, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 1 / 2, 1, ?_⟩
    change (1 : ℝ) / (1 / 2) ≠ 1 / 1
    norm_num

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@short_label_miss_obstruction) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.DiophantineApproximation.AffineCongruenceIntegerBoxThreeCover.short_label_miss_obstruction.__information_unit
  realizationName := `Reg.D5.S3.Arith.DiophantineApproximation.AffineCongruenceIntegerBoxThreeCover.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => 1 / w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.DiophantineApproximation.AffineCongruenceIntegerBoxThreeCover
    definition := none
    coordinates := #[]
    readouts := #[{
      -- Seven binders, the existential witness, then three right conjuncts.
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.DiophantineApproximation.AffineCongruenceIntegerBoxThreeCover
