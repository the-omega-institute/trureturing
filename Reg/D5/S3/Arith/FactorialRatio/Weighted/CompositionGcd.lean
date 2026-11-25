import D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound finite-profile and universal-certificate readouts. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd

open _root_.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd
open _root_.D5.S3.Arith.FactorialRatio.RankOneLCMGcd
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Finset
open scoped Nat

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
    (@simultaneous_floor_minimum) (Realization signature) Unit Unit where
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
  escapeFrom := none
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
    (@weighted_composition_gcd) (Realization weightSignature) Unit Unit where
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
  escapeFrom := none
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
    (@exact_certificate_is_universal) (Realization weightSignature) Unit Unit where
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
  escapeFrom := none
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
    (@exists_small_universal_certificate) (Realization weightSignature) Unit Unit where
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
  escapeFrom := none
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

end Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd
