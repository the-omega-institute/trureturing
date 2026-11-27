import D5.S3.Arith.Robin.PriceRecord.CanonicalRecordHarmonicDefect
import Reg.D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity
import Reg.Support.SingleDependentReadout

/-! Dependent-family registrations for the canonical real harmonic loss bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.CanonicalRecordHarmonicDefect

open Real Filter Asymptotics LeanInformationAudit
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask (actualDefect)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference (referencePrice)
open _root_.D5.S3.Arith.GoldenResource.GoldenResourcePriceInterval (marginal_pos)
open _root_.D5.S3.Arith.Robin.ActualTwoPriceDefect (strictInteger)
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff (firstLayerPrice)
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open _root_.D5.S3.Arith.Robin.PriceRecord.CanonicalRecordHarmonicDefect
open _root_.Reg.D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity
open _root_.Reg.Support.SingleDependentReadout (sensitivity)

private theorem threshold_at_729 : max (exp 4) 729 ≤ (729 : ℝ) := by
  apply max_le _ le_rfl
  calc
    exp 4 = exp ((4 : ℕ) * (1 : ℝ)) := by norm_num
    _ = exp 1 ^ 4 := exp_nat_mul 1 4
    _ ≤ (3 : ℝ) ^ 4 := pow_le_pow_left₀ (exp_nonneg 1) exp_one_lt_three.le 4
    _ ≤ 729 := by norm_num

private theorem scale_not_little_o :
    ¬ (fun X : ℝ => log X / X ^ 2) =o[atTop] (fun X : ℝ => log X / X ^ 2) := by
  apply isLittleO_irrefl
  exact ((eventually_gt_atTop (1 : ℝ)).mono fun X hX =>
    (div_pos (log_pos hX) (sq_pos_of_pos (zero_lt_one.trans hX))).ne').frequently

namespace SecondLayerObservation

def actual : Realization DefectObservation.signature :=
  realize DefectObservation.signature (fun _ X n => completeSecondLayerLoss X n)
    (fun e => nomatch e)

theorem dependence : ObservationalDependence DefectObservation.signature actual := by
  intro i
  refine ⟨1, 2, 4, ?_⟩
  change completeSecondLayerLoss 1 2 ≠ completeSecondLayerLoss 1 4
  have href : referencePrice 1 = 0 := by simp [referencePrice]
  have hstrict : strictInteger (referencePrice 1) = 1 := by simp [href, strictInteger]
  have hsupport₂ : lossPrimes 1 2 = {2} := by simp [lossPrimes, hstrict, Nat.prime_two]
  have hpow : (4 : ℕ).primeFactors = {2} :=
    Nat.primeFactors_prime_pow (k := 2) (by norm_num) Nat.prime_two
  have hsupport₄ : lossPrimes 1 4 = {2} := by simp [lossPrimes, hstrict, hpow]
  have hvaluation : (4 : ℕ).factorization 2 = 2 :=
    Nat.factorization_pow_self Nat.prime_two (n := 2)
  have hmargin : 0 < rawLayerMargin 1 2 2 := by
    rw [rawLayerMargin, href, sub_zero]
    exact mul_pos Nat.prime_two.log_pos (marginal_pos Nat.prime_two (by decide))
  rw [completeSecondLayerLoss, completeSecondLayerLoss, hsupport₂, hsupport₄]
  simpa [layerLoss, hvaluation, Nat.prime_two.factorization_self, max_eq_left hmargin.le]
    using hmargin.ne'

end SecondLayerObservation

namespace HigherBound

def rejected : Realization DefectObservation.signature :=
  realize DefectObservation.signature
    (fun _ X n => -1 - completeHigherLayerLoss X n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := DefectObservation.signature
  Law R := ∀ {X : ℝ} (_hX : max (exp 4) 729 ≤ X),
    let m := strictInteger (firstLayerPrice (X + 1))
    let H := R.readout () X m + completeHigherLayerLoss X m
    0 ≤ H ∧ H ≤ 3 * (6 * log 2 + 1 + log (6 * log X)) / X ^ 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hnonneg := (h threshold_at_729).1
  change 0 ≤ -1 - completeHigherLayerLoss 729 _ + completeHigherLayerLoss 729 _ at hnonneg
  linarith only [hnonneg]

def family : Registration arena (type_of% (@canonical_record_higher_loss_bound)) where
  actual := SecondLayerObservation.actual
  bridge := Iff.rfl
  variation := ⟨canonical_record_higher_loss_bound, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law SecondLayerObservation.actual rejected rejected_law
  dependence := SecondLayerObservation.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@canonical_record_higher_loss_bound) (Realization DefectObservation.signature) Type Unit where
  unitName :=
    `D5.S3.Arith.Robin.PriceRecord.CanonicalRecordHarmonicDefect.canonical_record_higher_loss_bound.audit
  realizationName :=
    `Reg.D5.S3.Arith.Robin.PriceRecord.CanonicalRecordHarmonicDefect.HigherBound.family
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
    (fun _ X n => completeSecondLayerLoss X n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.CanonicalRecordHarmonicDefect
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "value", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end HigherBound

namespace CompleteBound

abbrev arena : Arena where
  signature := DefectObservation.signature
  Law R := ∀ {X : ℝ} (_hX : max (exp 4) 729 ≤ X),
    let m := strictInteger (firstLayerPrice (X + 1))
    let R₀ := actualDefect X m - completeFirstLayerLoss X m
    let D := R.readout () X m
    0 ≤ R₀ ∧ R₀ ≤ 3 * (6 * log 2 + 1 + log (6 * log X)) / X ^ 2 ∧
    0 ≤ D ∧ D ≤ (3 * (6 * log 2 + 1 + log (6 * log X)) + 7 / 4) / X ^ 2

private theorem rejected_law : ¬ arena.Law DefectObservation.rejected := by
  intro h
  have hnonneg := (h threshold_at_729).2.2.1
  change (0 : ℝ) ≤ -1 at hnonneg
  norm_num at hnonneg

def family : Registration arena (type_of% (@canonical_record_harmonic_defect)) where
  actual := DefectObservation.actual
  bridge := Iff.rfl
  variation := ⟨canonical_record_harmonic_defect, DefectObservation.rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law DefectObservation.actual DefectObservation.rejected rejected_law
  dependence := DefectObservation.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@canonical_record_harmonic_defect) (Realization DefectObservation.signature) Type Unit where
  unitName :=
    `D5.S3.Arith.Robin.PriceRecord.CanonicalRecordHarmonicDefect.canonical_record_harmonic_defect.audit
  realizationName :=
    `Reg.D5.S3.Arith.Robin.PriceRecord.CanonicalRecordHarmonicDefect.CompleteBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize DefectObservation.signature (fun _ X n => actualDefect X n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.CanonicalRecordHarmonicDefect
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CompleteBound

namespace HigherAsymptotic

def rejected : Realization DefectObservation.signature :=
  realize DefectObservation.signature
    (fun _ X n => log X / X ^ 2 - completeHigherLayerLoss X n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := DefectObservation.signature
  Law R := (fun X : ℝ =>
    let m := strictInteger (firstLayerPrice (X + 1))
    R.readout () X m + completeHigherLayerLoss X m) =o[atTop]
      (fun X : ℝ => log X / X ^ 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact scale_not_little_o (h.congr_left fun X => by
    dsimp [rejected, realize]
    ring)

def family : Registration arena (type_of% (@canonical_record_higher_loss_isLittleO)) where
  actual := SecondLayerObservation.actual
  bridge := Iff.rfl
  variation := ⟨canonical_record_higher_loss_isLittleO, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law SecondLayerObservation.actual rejected rejected_law
  dependence := SecondLayerObservation.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@canonical_record_higher_loss_isLittleO) (Realization DefectObservation.signature) Type Unit where
  unitName :=
    `D5.S3.Arith.Robin.PriceRecord.CanonicalRecordHarmonicDefect.canonical_record_higher_loss_isLittleO.audit
  realizationName :=
    `Reg.D5.S3.Arith.Robin.PriceRecord.CanonicalRecordHarmonicDefect.HigherAsymptotic.family
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
    (fun _ X n => completeSecondLayerLoss X n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.CanonicalRecordHarmonicDefect
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end HigherAsymptotic

namespace CompleteAsymptotic

def rejected : Realization DefectObservation.signature :=
  realize DefectObservation.signature (fun _ X _ => log X / X ^ 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := DefectObservation.signature
  Law R := (fun X : ℝ => R.readout () X (strictInteger (firstLayerPrice (X + 1)))) =o[atTop]
    (fun X : ℝ => log X / X ^ 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  exact scale_not_little_o

def family : Registration arena (type_of% (@canonical_record_defect_isLittleO)) where
  actual := DefectObservation.actual
  bridge := Iff.rfl
  variation := ⟨canonical_record_defect_isLittleO, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law DefectObservation.actual rejected rejected_law
  dependence := DefectObservation.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@canonical_record_defect_isLittleO) (Realization DefectObservation.signature) Type Unit where
  unitName :=
    `D5.S3.Arith.Robin.PriceRecord.CanonicalRecordHarmonicDefect.canonical_record_defect_isLittleO.audit
  realizationName :=
    `Reg.D5.S3.Arith.Robin.PriceRecord.CanonicalRecordHarmonicDefect.CompleteAsymptotic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize DefectObservation.signature (fun _ X n => actualDefect X n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.CanonicalRecordHarmonicDefect
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["fn", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CompleteAsymptotic

end Reg.D5.S3.Arith.Robin.PriceRecord.CanonicalRecordHarmonicDefect
