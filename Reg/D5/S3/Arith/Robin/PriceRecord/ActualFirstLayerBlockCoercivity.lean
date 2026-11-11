import D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerBlockCoercivity
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound audits vary the upper theta observation on the full original telescope. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerBlockCoercivity

open Real
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerBlockCoercivity
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ t => Chebyshev.theta t) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change Chebyshev.theta 1 ≠ Chebyshev.theta 2
  have h1 : Nat.primesLE 1 = ∅ := by decide
  have h2 : Nat.primesLE 2 = {2} := by decide
  simp only [Chebyshev.theta_eq_sum_primesLE, Nat.floor_one, Nat.floor_ofNat,
    h1, h2, Finset.sum_empty, Finset.sum_singleton]
  exact ne_of_lt (log_pos (by norm_num))

namespace missing

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {X a b : ℝ} {m Q : ℕ}
    (_hX : 4 < X) (_hm : 2 ≤ m) (_hsupport : m.primeFactors = Nat.primesLE Q)
    (_ha : 1 < a) (_hab : a < b) (_hQa : (Q : ℝ) ≤ a) (_hbX : b + 1 / 2 < X),
    (X - b - 1 / 2) * (V.readout () () b - Chebyshev.theta a) /
      (X * (b + 1 / 2) * log b) ≤ completeFirstLayerLoss X m

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => Chebyshev.theta 2 +
    (5 * (3 + 1 / 2) * log 3) * (|completeFirstLayerLoss 5 2| + 1) / (5 - 3 - 1 / 2))
    (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : Nat.primeFactors 2 = Nat.primesLE 2 := by
    rw [Nat.prime_two.primeFactors]
    decide
  have hb := h (X := 5) (a := 2) (b := 3) (m := 2)
    (Q := 2) (by norm_num) (by norm_num) hs
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  change (5 - 3 - 1 / 2) * (Chebyshev.theta 2 +
    (5 * (3 + 1 / 2) * log 3) * (|completeFirstLayerLoss 5 2| + 1) / (5 - 3 - 1 / 2) -
    Chebyshev.theta 2) / (5 * (3 + 1 / 2) * log 3) ≤ completeFirstLayerLoss 5 2 at hb
  have hl : log (3 : ℝ) ≠ 0 := (log_pos (by norm_num)).ne'
  field_simp at hb
  nlinarith [le_abs_self (completeFirstLayerLoss 5 2),
    log_pos (show (1 : ℝ) < 3 by norm_num)]

def family : Registration arena (type_of% (@missing_block_theta_lower_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@missing_block_theta_lower_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@missing_block_theta_lower_bound) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerBlockCoercivity.missing_block_theta_lower_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerBlockCoercivity.missing.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => Chebyshev.theta t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerBlockCoercivity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end missing

namespace occupied

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {X a b : ℝ} {m Q : ℕ}
    (_hX : 4 < X) (_hm : 2 ≤ m) (_hsupport : m.primeFactors = Nat.primesLE Q)
    (_ha : 1 < a) (_hab : a < b) (_hbQ : b ≤ (Q : ℝ)) (_hXa : X < a),
    (a - X) * (V.readout () () b - Chebyshev.theta a) /
      (X * a * log b) ≤ completeFirstLayerLoss X m

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => Chebyshev.theta 6 +
    (5 * 6 * log 7) * (|completeFirstLayerLoss 5 210| + 1) / (6 - 5))
    (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : Nat.primeFactors 210 = Nat.primesLE 7 := by
    rw [show 210 = 2 * 3 * 5 * 7 by decide,
      Nat.primeFactors_mul (by decide) (by decide),
      Nat.primeFactors_mul (by decide) (by decide),
      Nat.primeFactors_mul (by decide) (by decide),
      Nat.prime_two.primeFactors, Nat.prime_three.primeFactors,
      (by decide : Nat.Prime 5).primeFactors, (by decide : Nat.Prime 7).primeFactors]
    decide
  have hb := h (X := 5) (a := 6) (b := 7) (m := 210)
    (Q := 7) (by norm_num) (by norm_num) hs
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  change (6 - 5) * (Chebyshev.theta 6 +
    (5 * 6 * log 7) * (|completeFirstLayerLoss 5 210| + 1) / (6 - 5) -
    Chebyshev.theta 6) / (5 * 6 * log 7) ≤ completeFirstLayerLoss 5 210 at hb
  have hl : log (7 : ℝ) ≠ 0 := (log_pos (by norm_num)).ne'
  field_simp at hb
  nlinarith [le_abs_self (completeFirstLayerLoss 5 210),
    log_pos (show (1 : ℝ) < 7 by norm_num)]

def family : Registration arena (type_of% (@occupied_block_theta_lower_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@occupied_block_theta_lower_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@occupied_block_theta_lower_bound) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerBlockCoercivity.occupied_block_theta_lower_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerBlockCoercivity.occupied.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => Chebyshev.theta t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerBlockCoercivity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end occupied

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerBlockCoercivity
