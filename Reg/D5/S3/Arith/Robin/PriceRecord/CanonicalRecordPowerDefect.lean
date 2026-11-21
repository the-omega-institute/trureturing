import D5.S3.Arith.Robin.PriceRecord.CanonicalRecordPowerDefect
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity

/-! Dependent-family audits for the real defect and integer first-layer loss. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.CanonicalRecordPowerDefect

open Real Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open _root_.D5.S3.Arith.Robin.ActualTwoPriceDefect
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization (FullRecord)
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open _root_.D5.S3.Arith.Robin.PriceRecord.CanonicalRecordPowerDefect
open _root_.Reg.D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity

private theorem exp_four_le_eighty_one : exp 4 ≤ 81 := by
  calc
    exp 4 = exp ((4 : ℕ) * (1 : ℝ)) := by norm_num
    _ = exp 1 ^ 4 := exp_nat_mul 1 4
    _ ≤ (3 : ℝ) ^ 4 := pow_le_pow_left₀ (exp_nonneg 1) exp_one_lt_three.le 4
    _ = 81 := by norm_num

namespace PowerDefect

abbrev arena : Arena where
  signature := DefectObservation.signature
  Law R := ∀ (X : ℝ) (_hX : exp 4 ≤ X),
    let q := referencePrice X
    let mu := firstLayerPrice (X + 1)
    let m := strictInteger mu
    let M := higherInventoryMismatch X m
    let R₀ := actualDefect X m - completeFirstLayerLoss X m
    let D := R.readout () X m
    0 < mu ∧ 2 ≤ m ∧ FullRecord m mu ∧
      (∀ p : ℕ, p ∈ m.primeFactors ↔ p.Prime ∧ (p : ℝ) < X + 1) ∧
      (1 - 3 / X) * q ≤ mu ∧ mu < q ∧
      M ≤ 800 * log X ^ 2 ∧
      0 ≤ R₀ ∧ R₀ ≤ 2400 * log X / X ^ 2 ∧
      (∀ p ∈ lossPrimes X m, layerLoss X m p 1 ≠ 0 →
        X - 1 / 2 < (p : ℝ) ∧ (p : ℝ) < X + 1) ∧
      0 ≤ completeFirstLayerLoss X m ∧ completeFirstLayerLoss X m ≤ (7 / 4) / X ^ 2 ∧
      0 ≤ D ∧ D ≤ (2400 * log X + 7 / 4) / X ^ 2

private theorem rejected_law : ¬ arena.Law DefectObservation.rejected := by
  intro h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hD, _⟩ := h 81 exp_four_le_eighty_one
  change (0 : ℝ) ≤ -1 at hD
  norm_num at hD

def family : Registration arena (type_of% (@canonical_record_power_defect)) where
  actual := DefectObservation.actual
  bridge := Iff.rfl
  variation := ⟨canonical_record_power_defect, DefectObservation.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨DefectObservation.rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := DefectObservation.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@canonical_record_power_defect) (Realization DefectObservation.signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.CanonicalRecordPowerDefect.canonical_record_power_defect.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.CanonicalRecordPowerDefect.PowerDefect.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize DefectObservation.signature
    (fun _ X n => actualDefect X n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.CanonicalRecordPowerDefect
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PowerDefect

namespace IntegerFirstLoss

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ N n => completeFirstLayerLoss (N : ℝ) n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N : ℕ) (_hN : exp 4 ≤ (N : ℝ)),
    let mu := firstLayerPrice ((N : ℝ) + 1)
    let m := strictInteger mu
    R.readout () N m = if N.Prime then 1 / (N : ℝ) - log (1 + 1 / (N : ℝ)) else 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hcomposite : ¬ Nat.Prime 81 := by decide
  have h81 := h 81 (by exact_mod_cast exp_four_le_eighty_one)
  change (-1 : ℝ) = (if Nat.Prime 81 then _ else 0) at h81
  norm_num [hcomposite] at h81

private theorem reference_first_loss_zero {X : ℝ} (hX : 1 < X) :
    completeFirstLayerLoss X (strictInteger (referencePrice X)) = 0 := by
  classical
  unfold completeFirstLayerLoss
  apply sum_eq_zero
  intro p hp
  have hprime : p.Prime := by
    rcases mem_union.mp hp with hp | hp <;> exact Nat.prime_of_mem_primeFactors hp
  have hactive : 0 < rawLayerMargin X p 1 ↔
      1 ≤ (strictInteger (referencePrice X)).factorization p := by
    rw [strictInteger_counts (reference_price_pos hX)]
    exact margin_active_iff hX hprime le_rfl
  by_cases hval : 1 ≤ (strictInteger (referencePrice X)).factorization p
  · simp only [layerLoss, ite_eq_left hval, max_eq_left (hactive.mpr hval).le, sub_self]
  · have hmargin : rawLayerMargin X p 1 ≤ 0 := le_of_not_gt (fun h => hval (hactive.mp h))
    simp only [layerLoss, ite_eq_right hval, max_eq_right hmargin, sub_self]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  have hlarge : exp 4 ≤ (83 : ℝ) := exp_four_le_eighty_one.trans (by norm_num)
  have hprime : Nat.Prime 83 := by decide
  let m := strictInteger (firstLayerPrice ((83 : ℝ) + 1))
  refine ⟨83, m, strictInteger (referencePrice 83), ?_⟩
  change completeFirstLayerLoss 83 m ≠ completeFirstLayerLoss 83 (strictInteger (referencePrice 83))
  have hfirst : completeFirstLayerLoss 83 m = 1 / (83 : ℝ) - log (1 + 1 / (83 : ℝ)) := by
    simpa only [m, Nat.cast_ofNat, ite_eq_left hprime] using
      canonical_integer_first_loss 83 (by exact_mod_cast hlarge)
  rw [hfirst, reference_first_loss_zero (by norm_num : (1 : ℝ) < 83)]
  have hlog := log_lt_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / 83 by norm_num)
    (show (1 : ℝ) + 1 / 83 ≠ 1 by norm_num)
  exact ne_of_gt (by linarith only [hlog])

def family : Registration arena (type_of% (@canonical_integer_first_loss)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨canonical_integer_first_loss, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@canonical_integer_first_loss) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.CanonicalRecordPowerDefect.canonical_integer_first_loss.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.CanonicalRecordPowerDefect.IntegerFirstLoss.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ N n => completeFirstLayerLoss (N : ℝ) n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.CanonicalRecordPowerDefect
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end IntegerFirstLoss

end Reg.D5.S3.Arith.Robin.PriceRecord.CanonicalRecordPowerDefect
