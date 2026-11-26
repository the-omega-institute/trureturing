import D5.S3.Arith.FactorialRatio.Weighted.IdealTail
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

/-! The entire number-field telescope is retained while the tail endpoint varies. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FactorialRatio.Weighted.IdealTail

open _root_.D5.S3.Arith.FactorialRatio.Weighted.IdealTail
open _root_.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd
open _root_.D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd.NumberFieldNorm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit UniqueFactorizationMonoid IsDedekindDomain Finset
open scoped NumberField

noncomputable section

universe u

structure Params where
  carrier : Type u
  field : Field carrier
  numberField : @NumberField carrier field
  head : ℕ

abbrev signature : Signature where
  Params := Params.{u}
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p M => by
    letI := p.field
    letI := p.numberField
    exact weightedTail p.head M (normWeight p.carrier)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ (K : Type u) [F : Field K] [N : NumberField K] (H M : ℕ),
    (∀ t : ℕ,
      {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ I.absNorm ≤ t}.Finite ∧
      idealIntersection K t ≠ ⊥ ∧
      (∀ P : HeightOneSpectrum (𝓞 K),
        (normalizedFactors (idealIntersection K t)).count P.asIdeal =
          Nat.log P.asIdeal.absNorm t)) ∧
    idealIntersection K 0 = ⊤ ∧
    (idealTail K H M).absNorm = R.readout () ⟨K, F, N, H⟩ M

instance liftNumberField : NumberField (ULift.{u} ℚ) :=
  NumberField.of_ringEquiv ℚ (ULift.{u} ℚ) (ULift.ringEquiv.symm : ℚ ≃+* ULift.{u} ℚ)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := (h (ULift.{u} ℚ) 0 0).2.2
  change (idealTail (ULift.{u} ℚ) 0 0).absNorm = 0 at hh
  simpa [idealTail] using hh

theorem dependence : ObservationalDependence signature.{u} actual := by
  classical
  let K := ULift.{u} ℚ
  obtain ⟨P, _⟩ :=
    (HeightOneSpectrum.ideal_ne_top_iff_exists (NumberField.RingOfIntegers.not_isField K)
      (⊥ : Ideal (𝓞 K))).mp bot_ne_top
  let q := P.asIdeal.absNorm
  have hq0 : q ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot
  have hq1 : q ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top
  have hq : 1 < q := by omega
  have htail : idealTail K q 0 ≤ idealIntersection K q := by
    have hmem : 1 ∈ Ioc 0 q := Finset.mem_Ioc.mpr ⟨by decide, hq.le⟩
    have hd : idealIntersection K (q / 1) ∣ idealTail K q 0 :=
      Finset.dvd_prod_of_mem (fun k => idealIntersection K (q / k)) hmem
    simpa only [Nat.div_one] using Ideal.dvd_iff_le.mp hd
  have hIP : idealIntersection K q ≤ P.asIdeal := by
    exact iInf_le_of_le P.asIdeal
      (iInf_le_of_le (show P.asIdeal ≠ ⊥ ∧ P.asIdeal.absNorm ≤ q from
        ⟨P.ne_bot, le_rfl⟩) le_rfl)
  have hdiv : q ∣ weightedTail q 0 (normWeight K) := by
    rw [← (ideal_intersection_tail K q 0).2.2]
    exact Ideal.absNorm_dvd_absNorm_of_le (htail.trans hIP)
  have hunit : weightedTail q q (normWeight K) = 1 := by
    rw [← (ideal_intersection_tail K q q).2.2]
    simp [idealTail]
  intro role
  refine ⟨⟨K, inferInstance, inferInstance, q⟩, 0, q, ?_⟩
  change weightedTail q 0 (normWeight K) ≠ weightedTail q q (normWeight K)
  rw [hunit]
  intro heq
  rw [heq] at hdiv
  exact hq1 (Nat.dvd_one.mp hdiv)

def family : Registration arena.{u} (type_of% @ideal_intersection_tail.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ideal_intersection_tail.{u}, rejected, rejected_law⟩
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
    (@ideal_intersection_tail.{u}) (Realization signature.{u}) Type Unit where
  unitName :=
    `D5.S3.Arith.FactorialRatio.Weighted.IdealTail.ideal_intersection_tail.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.Weighted.IdealTail.family
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
    owner := `D5.S3.Arith.FactorialRatio.Weighted.IdealTail
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Arith.FactorialRatio.Weighted.IdealTail
