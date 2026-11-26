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

/-- Expand shared source metadata into literal registrations at the family's own universes. -/
local macro "sourceAudit" "(" target:term "," unitName:term "," realizationName:term ","
    sourceArena:term "," family:term "," readout:term "," escapeFrom:term ","
    definition:term "," coordinates:term "," path:term "," stateBinder:term ","
    stateOperand:term ")" : term =>
  `(({
    unitName := $unitName
    realizationName := $realizationName
    realizationSource := none
    generated := false
    arena := .source ⟨$sourceArena⟩
    objectArena := .source ⟨$sourceArena⟩
    catalog := .anonymous
    localNames := false
    realization := .source $sourceArena ⟨$family⟩
    correspondence := { stage := .evidence, objectStage := .evidence }
    bundleNonempty := .absent
    readout := $readout
    variation := .absent
    sensitivity := .absent
    partialSensitivity := none
    escapeFrom := $escapeFrom
    sourceSelection := some {
      owner := `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd
      definition := $definition
      coordinates := $coordinates
      readouts := #[{
        path := $path
        stateBinder := $stateBinder
        functionOperand := false
        stateOperand := $stateOperand
        booleanPredicate := false }] }
    continuation := .unknown
    familyRecord := none
    options := #[] } : Contract.Registration $target _ _ _))

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
  Law R := ∀ (H M p : ℕ), M ≤ H → (native% OmegaMathlib.Nat.Prime) p →
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
    (@simultaneous_floor_minimum) (Realization signature) Type Unit :=
  sourceAudit (@simultaneous_floor_minimum,
    `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.simultaneous_floor_minimum.__information_unit,
    `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.Minimum.family,
    arena, family,
    (some (realize signature (fun _ w q => floorMinimum w.1 w.2 q) (fun e => nomatch e))),
    (some ℕ),
    none,
    #[0, 1],
    #["body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body", "arg"],
    0,
    (some #["arg"]))

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
    (@weighted_composition_gcd) (Realization weightSignature) Type Unit :=
  sourceAudit (@weighted_composition_gcd,
    `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.weighted_composition_gcd.__information_unit,
    `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.WeightedGcd.family,
    arena, family,
    (some (realize weightSignature (fun _ w c => weightedTail w.1 w.2 c) (fun e => nomatch e))),
    (some (ℕ → ℕ → ℕ)),
    none,
    #[0, 1],
    #["body", "body", "body", "body", "arg"],
    3,
    none)

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
    (@exact_certificate_is_universal) (Realization weightSignature) Type Unit :=
  sourceAudit (@exact_certificate_is_universal,
    `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.exact_certificate_is_universal.__information_unit,
    `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.Certificate.family,
    arena, family,
    (some (realize weightSignature (fun _ w c => weightedTail w.1 w.2 c) (fun e => nomatch e))),
    (some (ℕ → ℕ → ℕ)),
    none,
    #[0, 1],
    #["body", "body", "body", "body", "body", "body", "body", "arg"],
    6,
    none)

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
    (@exists_small_universal_certificate) (Realization weightSignature) Type Unit :=
  sourceAudit (@exists_small_universal_certificate,
    `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.exists_small_universal_certificate.__information_unit,
    `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.SmallCertificate.family,
    arena, family,
    (some (realize weightSignature (fun _ w c => weightedTail w.1 w.2 c) (fun e => nomatch e))),
    (some (ℕ → ℕ → ℕ)),
    none,
    #[0, 1],
    #["body", "body", "body", "arg", "body", "arg", "arg", "arg", "body", "arg"],
    4,
    none)

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
  Law R := ∀ {p : ℕ}, (native% OmegaMathlib.Nat.Prime) p → R.readout () () p ≠ ⊥

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
    (@rationalPrimeIdeal_ne_bot) (Realization signature) Type Unit :=
  sourceAudit (@rationalPrimeIdeal_ne_bot,
    `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.NumberFieldNorm.rationalPrimeIdeal_ne_bot.__information_unit,
    `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.RationalPrimeIdeal.Nonzero.family,
    arena, family,
    (some (realize signature (fun _ _ p => rationalPrimeIdeal p) (fun e => nomatch e))),
    (some ℕ),
    none,
    #[],
    #["body", "body", "arg", "fn", "arg"],
    0,
    none)

end Nonzero

namespace Primality

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p : ℕ}, (native% OmegaMathlib.Nat.Prime) p → (R.readout () () p).IsPrime

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
    (@rationalPrimeIdeal_isPrime) (Realization signature) Type Unit :=
  sourceAudit (@rationalPrimeIdeal_isPrime,
    `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.NumberFieldNorm.rationalPrimeIdeal_isPrime.__information_unit,
    `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.RationalPrimeIdeal.Primality.family,
    arena, family,
    (some (realize signature (fun _ _ p => rationalPrimeIdeal p) (fun e => nomatch e))),
    (some ℕ),
    none,
    #[],
    #["body", "body", "arg"],
    0,
    none)

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
    (∀ p : ℕ, (native% OmegaMathlib.Nat.Prime) p → ∀ j : ℕ, normWeight K p j ≤ Module.finrank ℚ K) ∧
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
    (@number_field_norm_and_complement.{u}) (Realization signature.{u}) Type Unit :=
  sourceAudit (@number_field_norm_and_complement.{u},
    `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.NumberFieldNorm.number_field_norm_and_complement.__information_unit,
    `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.NumberFieldGcd.family,
    arena, family,
    (some (realize signature (fun _ p M => by
      letI := p.field
      letI := p.numberField
      exact weightedTail p.head M (normWeight p.carrier)) (fun e => nomatch e))),
    (some ℕ),
    none,
    #[0, 3],
    #["body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "fn", "arg", "arg"],
    4,
    none)

end NumberFieldGcd

namespace ValueNonzero

abbrev signature : Signature where
  Params := ℕ
  State _ := (ℕ → ℕ → ℕ) × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ H z => weightedValue H z.1 z.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (H : ℕ) (c : ℕ → ℕ → ℕ) (n : ℕ), R.readout () H (c, n) ≠ 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 (fun _ _ => 0) 0 rfl

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨2, ((fun _ _ => 0), 2), ((fun _ _ => 1), 2), ?_⟩
  change weightedValue 2 (fun _ _ => 0) 2 ≠ weightedValue 2 (fun _ _ => 1) 2
  decide

def family : Registration arena (type_of% @weightedValue_ne_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weightedValue_ne_zero, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weightedValue_ne_zero) (Realization signature) Type Unit :=
  sourceAudit (@weightedValue_ne_zero,
    `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.weightedValue_ne_zero.__information_unit,
    `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.ValueNonzero.family,
    arena, family,
    (some (realize signature (fun _ H z => weightedValue H z.1 z.2) (fun e => nomatch e))),
    none,
    none,
    #[0],
    #["body", "body", "body", "arg", "fn", "arg"],
    1,
    none)

end ValueNonzero

namespace TailNonzero

abbrev signature : Signature where
  Params := ℕ × ℕ
  State _ := ℕ → ℕ → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ z c => weightedTail z.1 z.2 c) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (H M : ℕ) (c : ℕ → ℕ → ℕ), R.readout () (H, M) c ≠ 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 (fun _ _ => 0) rfl

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  obtain ⟨z, c, d, h⟩ := weightDependence role
  exact ⟨(z.1, z.2), c, d, h⟩

def family : Registration arena (type_of% @weightedTail_ne_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weightedTail_ne_zero, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weightedTail_ne_zero) (Realization signature) Type Unit :=
  sourceAudit (@weightedTail_ne_zero,
    `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.weightedTail_ne_zero.__information_unit,
    `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.TailNonzero.family,
    arena, family,
    (some (realize signature (fun _ z c => weightedTail z.1 z.2 c) (fun e => nomatch e))),
    none,
    none,
    #[0, 1],
    #["body", "body", "body", "arg", "fn", "arg"],
    2,
    none)

end TailNonzero

namespace PrimeProduct

abbrev signature : Signature where
  Params := Finset ℕ × (ℕ → ℕ)
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ z p => (∏ q ∈ z.1, q ^ z.2 q).factorization p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (P : Finset ℕ) (e : ℕ → ℕ), (∀ p ∈ P, (native% OmegaMathlib.Nat.Prime) p) → ∀ p : ℕ,
    R.readout () (P, e) p = if p ∈ P then e p else 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h ∅ (fun _ => 0) (by simp) 0
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨({2}, (fun _ => 1)), 2, 3, ?_⟩
  change (∏ q ∈ ({2} : Finset ℕ), q ^ 1).factorization 2 ≠
    (∏ q ∈ ({2} : Finset ℕ), q ^ 1).factorization 3
  simp only [Finset.prod_singleton, pow_one]
  rw [Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_lt (by decide : 2 < 3)]
  decide

def family : Registration arena (type_of% @prime_product_factorization) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prime_product_factorization, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@prime_product_factorization) (Realization signature) Type Unit :=
  sourceAudit (@prime_product_factorization,
    `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.prime_product_factorization.__information_unit,
    `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.PrimeProduct.family,
    arena, family,
    (some (realize signature (fun _ z p => (∏ q ∈ z.1, q ^ z.2 q).factorization p) (fun e => nomatch e))),
    none,
    none,
    #[0, 1],
    #["body", "body", "body", "body", "fn", "arg"],
    3,
    none)

end PrimeProduct

namespace TailFactorization

abbrev signature : Signature where
  Params := ℕ × ℕ
  State _ := (ℕ → ℕ → ℕ) × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ z w => (weightedTail z.1 z.2 w.1).factorization w.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (H M : ℕ) (c : ℕ → ℕ → ℕ) {p : ℕ}, p ∈ Nat.primesLE H →
    R.readout () (H, M) (c, p) =
      ∑ j ∈ range (H + 1), c p j * floorMinimum H M (p ^ (j + 1))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 2 0 (fun _ _ => 0) (p := 2) (by decide)
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(2, 0), ((fun _ _ => 1), 2), ((fun _ _ => 1), 3), ?_⟩
  change (weightedTail 2 0 (fun _ _ => 1)).factorization 2 ≠
    (weightedTail 2 0 (fun _ _ => 1)).factorization 3
  rw [show weightedTail 2 0 (fun _ _ => 1) = 2 from by decide,
    Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_lt (by decide : 2 < 3)]
  decide

def family : Registration arena (type_of% @weightedTail_factorization) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weightedTail_factorization, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weightedTail_factorization) (Realization signature) Type Unit :=
  sourceAudit (@weightedTail_factorization,
    `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.weightedTail_factorization.__information_unit,
    `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.TailFactorization.family,
    arena, family,
    (some (realize signature (fun _ z w => (weightedTail z.1 z.2 w.1).factorization w.2) (fun e => nomatch e))),
    none,
    none,
    #[0, 1],
    #["body", "body", "body", "body", "body", "fn", "arg"],
    2,
    none)

end TailFactorization

namespace TailConstant

abbrev signature : Signature where
  Params := ℕ × ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ z d => weightedTail z.1 z.2 (fun _ _ => d)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (H M d : ℕ), R.readout () (H, M) d = tailLCM H M ^ d

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0 0
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(2, 0), 0, 1, ?_⟩
  change weightedTail 2 0 (fun _ _ => 0) ≠ weightedTail 2 0 (fun _ _ => 1)
  decide

def family : Registration arena (type_of% @weightedTail_constant) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weightedTail_constant, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weightedTail_constant) (Realization signature) Type Unit :=
  sourceAudit (@weightedTail_constant,
    `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.weightedTail_constant.__information_unit,
    `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.TailConstant.family,
    arena, family,
    (some (realize signature (fun _ z d => weightedTail z.1 z.2 (fun _ _ => d)) (fun e => nomatch e))),
    none,
    none,
    #[0, 1],
    #["body", "body", "body", "fn", "arg"],
    2,
    none)

end TailConstant

namespace TailAdd

abbrev signature : Signature where
  Params := ℕ × ℕ
  State _ := (ℕ → ℕ → ℕ) × (ℕ → ℕ → ℕ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ z w => weightedTail z.1 z.2 (fun p j => w.1 p j + w.2 p j)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (H M : ℕ) (c d : ℕ → ℕ → ℕ),
    weightedTail H M c * weightedTail H M d = R.readout () (H, M) (c, d)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0 (fun _ _ => 0) (fun _ _ => 0)
  norm_num [rejected, realize, weightedTail] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(2, 0), ((fun _ _ => 0), (fun _ _ => 0)),
    ((fun _ _ => 1), (fun _ _ => 0)), ?_⟩
  change weightedTail 2 0 (fun _ _ => 0 + 0) ≠ weightedTail 2 0 (fun _ _ => 1 + 0)
  decide

def family : Registration arena (type_of% @weightedTail_add) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weightedTail_add, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weightedTail_add) (Realization signature) Type Unit :=
  sourceAudit (@weightedTail_add,
    `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.weightedTail_add.__information_unit,
    `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.TailAdd.family,
    arena, family,
    (some (realize signature (fun _ z w => weightedTail z.1 z.2 (fun p j => w.1 p j + w.2 p j)) (fun e => nomatch e))),
    none,
    none,
    #[0, 1],
    #["body", "body", "body", "body", "arg"],
    2,
    none)

end TailAdd

namespace FullNorm
universe u

abbrev signature : Signature where
  Params := _root_.Reg.D5.S3.Arith.FactorialRatio.Weighted.IdealTail.Params.{u}
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ z n => by
    letI := z.field
    letI := z.numberField
    exact (NumberFieldNorm.fullRingFactorialIdeal z.carrier n).absNorm) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ (K : Type u) [F : Field K] [N : NumberField K] (H n : ℕ), n ≤ H →
    R.readout () ⟨K, F, N, H⟩ n = weightedValue H (NumberFieldNorm.normWeight K) n

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (ULift.{u} ℚ) 0 0 (by decide)
  change 0 = weightedValue 0 (NumberFieldNorm.normWeight (ULift.{u} ℚ)) 0 at hh
  norm_num [weightedValue] at hh

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  obtain ⟨z, x, y, hxy⟩ :=
    _root_.Reg.D5.S3.Arith.FactorialRatio.Weighted.IdealTail.dependence.{u} ()
  letI := z.field
  letI := z.numberField
  refine ⟨z, 0, z.head, ?_⟩
  change (NumberFieldNorm.fullRingFactorialIdeal z.carrier 0).absNorm ≠
    (NumberFieldNorm.fullRingFactorialIdeal z.carrier z.head).absNorm
  intro heq
  rw [NumberFieldNorm.fullRingFactorialIdeal_norm z.carrier z.head 0 (Nat.zero_le _),
    NumberFieldNorm.fullRingFactorialIdeal_norm z.carrier z.head z.head le_rfl] at heq
  have hz : weightedValue z.head (NumberFieldNorm.normWeight z.carrier) 0 = 1 := by
    simp [weightedValue, weightedExponent]
  have hone := heq.symm.trans hz
  have htail (M : ℕ) : weightedTail z.head M (NumberFieldNorm.normWeight z.carrier) = 1 := by
    apply Nat.eq_one_of_dvd_one
    rw [← hone]
    unfold weightedTail weightedValue
    apply Finset.prod_dvd_prod_of_dvd
    intro p hp
    apply pow_dvd_pow
    unfold weightedExponent
    apply Finset.sum_le_sum
    intro j hj
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  apply hxy
  change weightedTail z.head x (NumberFieldNorm.normWeight z.carrier) =
    weightedTail z.head y (NumberFieldNorm.normWeight z.carrier)
  rw [htail, htail]

def family : Registration arena.{u} (type_of% @NumberFieldNorm.fullRingFactorialIdeal_norm.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@NumberFieldNorm.fullRingFactorialIdeal_norm.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      have heq : j = i := @Subsingleton.elim Unit inferInstance j i
      exact (hji heq).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@NumberFieldNorm.fullRingFactorialIdeal_norm.{u}) (Realization signature.{u}) Type Unit :=
  sourceAudit (@NumberFieldNorm.fullRingFactorialIdeal_norm.{u},
    `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.NumberFieldNorm.fullRingFactorialIdeal_norm.__information_unit,
    `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.FullNorm.family,
    arena, family,
    (some (realize signature (fun _ z n => by
      letI := z.field
      letI := z.numberField
      exact (NumberFieldNorm.fullRingFactorialIdeal z.carrier n).absNorm) (fun e => nomatch e))),
    none,
    none,
    #[0, 3],
    #["body", "body", "body", "body", "body", "body", "fn", "arg"],
    4,
    none)

end FullNorm

namespace ComplementValue
universe u

abbrev signature : Signature where
  Params := _root_.Reg.D5.S3.Arith.FactorialRatio.Weighted.IdealTail.Params.{u}
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ z n => by
    letI := z.field
    letI := z.numberField
    exact (NumberFieldNorm.fullRingFactorialIdeal z.carrier n).absNorm) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ (K : Type u) [F : Field K] [N : NumberField K] (H n : ℕ), n ≤ H →
    (n !) ^ Module.finrank ℚ K / R.readout () ⟨K, F, N, H⟩ n =
      weightedValue H (fun p j => Module.finrank ℚ K - NumberFieldNorm.normWeight K p j) n

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (ULift.{u} ℚ) 0 0 (by decide)
  change (0 !) ^ Module.finrank ℚ (ULift.{u} ℚ) / 0 =
    weightedValue 0 (fun p j => Module.finrank ℚ (ULift.{u} ℚ) -
      NumberFieldNorm.normWeight (ULift.{u} ℚ) p j) 0 at hh
  norm_num [weightedValue] at hh

private theorem dependence : ObservationalDependence signature.{u} actual := by
  exact FullNorm.dependence

def family : Registration arena.{u} (type_of% @NumberFieldNorm.complement_eq_weightedValue.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@NumberFieldNorm.complement_eq_weightedValue.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      have heq : j = i := @Subsingleton.elim Unit inferInstance j i
      exact (hji heq).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@NumberFieldNorm.complement_eq_weightedValue.{u}) (Realization signature.{u}) Type Unit :=
  sourceAudit (@NumberFieldNorm.complement_eq_weightedValue.{u},
    `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.NumberFieldNorm.complement_eq_weightedValue.__information_unit,
    `Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.ComplementValue.family,
    arena, family,
    (some (realize signature (fun _ z n => by
      letI := z.field
      letI := z.numberField
      exact (NumberFieldNorm.fullRingFactorialIdeal z.carrier n).absNorm) (fun e => nomatch e))),
    none,
    (some { owner := `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd, name := `D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.NumberFieldNorm.normComplement, path := #["body", "body", "body", "body"] }),
    #[0, 3],
    #["body", "body", "body", "body", "arg"],
    4,
    none)

end ComplementValue

end Reg.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd
