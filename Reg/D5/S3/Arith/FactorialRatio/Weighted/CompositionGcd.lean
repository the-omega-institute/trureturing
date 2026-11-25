import D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.Arith.FactorialRatio.Weighted.IdealTail

/-! Source-bound finite-profile and universal-certificate readouts. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd

open _root_.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd
open _root_.D5.S3.Arith.FactorialRatio.RankOneLCMGcd
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Finset
open scoped Nat
open scoped NumberField

abbrev Params := Σ _ : ℕ, ℕ
abbrev weightSignature := Reg.Support.SingleDependentReadout.signature Params
  (fun _ => ℕ → ℕ → ℕ) (fun _ => ℕ)

def weightActual : Realization weightSignature :=
  realize weightSignature (fun _ w c => weightedTail w.1 w.2 c) (fun e => nomatch e)

def weightRejected : Realization weightSignature :=
  realize weightSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem weightDependence : ObservationalDependence weightSignature weightActual := by
  intro role
  refine ⟨⟨2, 0⟩, (fun _ _ => 0), (fun _ _ => 1), ?_⟩
  change weightedTail 2 0 (fun _ _ => 0) ≠ weightedTail 2 0 (fun _ _ => 1)
  decide

namespace Minimum

abbrev signature := Reg.Support.SingleDependentReadout.signature Params (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ w q => floorMinimum w.1 w.2 q) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (H M p : ℕ), M ≤ H → p.Prime →
    ∃ a : Fin (M + 1) → ℕ, (∑ i, a i) = H - M ∧
      ∀ j : ℕ, 0 < j → floorProfile (p ^ j) a = R.readout () ⟨H, M⟩ (p ^ j)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨a, ha, heq⟩ := h 0 0 2 (by decide) Nat.prime_two
  have ha0 : a 0 = 0 := by simpa using ha
  have hh := heq 1 (by decide)
  norm_num [floorProfile, rejected, realize, Fin.sum_univ_succ, ha0] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨2, 0⟩, 1, 2, ?_⟩
  change floorMinimum 2 0 1 ≠ floorMinimum 2 0 2
  decide

def family : Registration arena (type_of% @simultaneous_floor_minimum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨simultaneous_floor_minimum, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@simultaneous_floor_minimum) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.simultaneous_floor_minimum.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.Minimum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ w q => floorMinimum w.1 w.2 q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Minimum

namespace WeightedGcd
abbrev arena : Arena where
  signature := weightSignature
  Law R := ∀ (H M : ℕ), M ≤ H → ∀ c : ℕ → ℕ → ℕ,
    (Finset.Nat.antidiagonalTuple (M + 1) (H - M)).gcd (weightedProduct H c) =
      R.readout () ⟨H, M⟩ c
private theorem rejected_law : ¬ arena.Law weightRejected := by
  intro h
  have hh := h 0 0 (by decide) (fun _ _ => 0)
  change _ = 0 at hh
  rw [weighted_composition_gcd 0 0 (by decide)] at hh
  norm_num [weightedTail] at hh

def family : Registration arena (type_of% @weighted_composition_gcd) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨weighted_composition_gcd, weightRejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law weightActual weightRejected rejected_law
  dependence := weightDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weighted_composition_gcd) (Realization weightSignature) Type Unit where
  unitName := `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.weighted_composition_gcd.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.WeightedGcd.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize weightSignature (fun _ w c => weightedTail w.1 w.2 c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℕ → ℕ → ℕ)
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end WeightedGcd

namespace Certificate
abbrev arena : Arena where
  signature := weightSignature
  Law R := ∀ (H M : ℕ), M ≤ H →
    ∀ (C : Finset (Fin (M + 1) → ℕ)),
      (∀ a ∈ C, (∑ i, a i) = H - M) →
      C.gcd factorialProduct = tailLCM H M → ∀ c : ℕ → ℕ → ℕ,
        C.gcd (weightedProduct H c) = R.readout () ⟨H, M⟩ c
private theorem rejected_law : ¬ arena.Law weightRejected := by
  intro h
  let C := Finset.Nat.antidiagonalTuple 1 0
  have hC : ∀ a ∈ C, (∑ i, a i) = 0 := fun a ha => Finset.Nat.mem_antidiagonalTuple.mp ha
  have ho : C.gcd factorialProduct = tailLCM 0 0 := (tailLCM_eq_gcd 0 0 (by decide)).symm
  have hh := h 0 0 (by decide) C hC ho (fun _ _ => 0)
  change _ = 0 at hh
  rw [exact_certificate_is_universal 0 0 (by decide) C hC ho] at hh
  norm_num [weightedTail] at hh

def family : Registration arena (type_of% @exact_certificate_is_universal) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨exact_certificate_is_universal, weightRejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law weightActual weightRejected rejected_law
  dependence := weightDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exact_certificate_is_universal) (Realization weightSignature) Type Unit where
  unitName := `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.exact_certificate_is_universal.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.Certificate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize weightSignature (fun _ w c => weightedTail w.1 w.2 c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℕ → ℕ → ℕ)
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Certificate

namespace SmallCertificate
abbrev arena : Arena where
  signature := weightSignature
  Law R := ∀ (H M : ℕ), M ≤ H →
    ∃ C : Finset (Fin (M + 1) → ℕ),
      (∀ a ∈ C, (∑ i, a i) = H - M) ∧
      C.card ≤ Nat.primeCounting (H / (M + 1)) + 1 ∧
      C.gcd factorialProduct = tailLCM H M ∧
      ∀ c : ℕ → ℕ → ℕ, C.gcd (weightedProduct H c) = R.readout () ⟨H, M⟩ c
private theorem rejected_law : ¬ arena.Law weightRejected := by
  intro h
  obtain ⟨C, hC, _, ho, hall⟩ := h 0 0 (by decide)
  have hh := hall (fun _ _ => 0)
  change _ = 0 at hh
  rw [exact_certificate_is_universal 0 0 (by decide) C hC ho] at hh
  norm_num [weightedTail] at hh

def family : Registration arena (type_of% @exists_small_universal_certificate) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨exists_small_universal_certificate, weightRejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law weightActual weightRejected rejected_law
  dependence := weightDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_small_universal_certificate) (Realization weightSignature) Type Unit where
  unitName := `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.exists_small_universal_certificate.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.SmallCertificate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize weightSignature (fun _ w c => weightedTail w.1 w.2 c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℕ → ℕ → ℕ)
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "arg", "arg", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SmallCertificate

namespace RationalPrimeIdeal

open _root_.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.NumberFieldNorm

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℕ) (fun _ => Ideal ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ p => rationalPrimeIdeal p) (fun e => nomatch e)

def zeroIdeal : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

def unitIdeal : Realization signature :=
  realize signature (fun _ _ _ => ⊤) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 2, 3, ?_⟩
  change rationalPrimeIdeal 2 ≠ rationalPrimeIdeal 3
  intro heq
  have h := congrArg Ideal.absNorm heq
  norm_num [rationalPrimeIdeal, Ideal.absNorm_span_natCast] at h

namespace Nonzero

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p : ℕ}, p.Prime → R.readout () () p ≠ ⊥

private theorem rejected_law : ¬ arena.Law zeroIdeal := by
  intro h
  exact h Nat.prime_two rfl

def family : Registration arena (type_of% @rationalPrimeIdeal_ne_bot) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rationalPrimeIdeal_ne_bot, zeroIdeal, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual zeroIdeal rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rationalPrimeIdeal_ne_bot) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.NumberFieldNorm.rationalPrimeIdeal_ne_bot.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.RationalPrimeIdeal.Nonzero.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => rationalPrimeIdeal p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Nonzero

namespace Primality

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p : ℕ}, p.Prime → (R.readout () () p).IsPrime

private theorem rejected_law : ¬ arena.Law unitIdeal := by
  intro h
  exact (h Nat.prime_two).ne_top rfl

def family : Registration arena (type_of% @rationalPrimeIdeal_isPrime) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rationalPrimeIdeal_isPrime, unitIdeal, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual unitIdeal rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rationalPrimeIdeal_isPrime) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.NumberFieldNorm.rationalPrimeIdeal_isPrime.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.RationalPrimeIdeal.Primality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => rationalPrimeIdeal p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Primality
end RationalPrimeIdeal

namespace NumberFieldGcd

universe u

open _root_.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.NumberFieldNorm

abbrev signature := Reg.D5.S3.Arith.FactorialRatio.Weighted.IdealTail.signature.{u}
abbrev actual := Reg.D5.S3.Arith.FactorialRatio.Weighted.IdealTail.actual.{u}
abbrev rejected := Reg.D5.S3.Arith.FactorialRatio.Weighted.IdealTail.rejected.{u}

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ (K : Type u) [F : Field K] [N : NumberField K] (H M : ℕ), M ≤ H →
    (∀ p : ℕ, p.Prime → ∀ j : ℕ, normWeight K p j ≤ Module.finrank ℚ K) ∧
    (∀ n ≤ H, fullRingFactorialIdeal K n = residueFactorialIdeal K H n) ∧
    (∀ n ≤ H, (fullRingFactorialIdeal K n).absNorm * normComplement K n =
      (n !) ^ Module.finrank ℚ K) ∧
    (Finset.Nat.antidiagonalTuple (M + 1) (H - M)).gcd
        (fun a => ∏ i, (fullRingFactorialIdeal K (a i)).absNorm) =
      R.readout () ⟨K, F, N, H⟩ M ∧
    (Finset.Nat.antidiagonalTuple (M + 1) (H - M)).gcd
        (fun a => ∏ i, normComplement K (a i)) =
      weightedTail H M (fun p j => Module.finrank ℚ K - normWeight K p j) ∧
    weightedTail H M (normWeight K) *
        weightedTail H M (fun p j => Module.finrank ℚ K - normWeight K p j) =
      (tailLCM H M) ^ Module.finrank ℚ K

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := (h (ULift.{u} ℚ) 0 0 (by decide)).2.2.2.1
  change _ = 0 at hh
  rw [(number_field_norm_and_complement (ULift.{u} ℚ) 0 0 (by decide)).2.2.2.1] at hh
  norm_num [weightedTail] at hh

def family : Registration arena.{u} (type_of% @number_field_norm_and_complement.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@number_field_norm_and_complement.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      have heq : j = i := @Subsingleton.elim Unit inferInstance j i
      exact (hji heq).elim
    · intro e
      exact nomatch e
  dependence := Reg.D5.S3.Arith.FactorialRatio.Weighted.IdealTail.dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@number_field_norm_and_complement.{u}) (Realization signature.{u}) Type Unit where
  unitName :=
    `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.NumberFieldNorm.number_field_norm_and_complement.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.NumberFieldGcd.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p M => by
    letI := p.field
    letI := p.numberField
    exact weightedTail p.head M (normWeight p.carrier)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end NumberFieldGcd

end Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd
