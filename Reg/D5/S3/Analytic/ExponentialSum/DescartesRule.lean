import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.ExponentialSum.DescartesRule
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Analytic.ExponentialSum.DescartesRule
open _root_.D5.S3.Analytic.ExponentialSum.DescartesRule
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Finset SignType
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev variationSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => List ℝ) (fun _ => ℕ)

def variationActual : Realization variationSignature :=
  realize variationSignature (fun _ _ a => a.signVariations) (fun e => nomatch e)

def variationRejected : Realization variationSignature :=
  realize variationSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem variationDependence :
    ObservationalDependence variationSignature variationActual := by
  intro i
  refine ⟨(), [], [1, -1], ?_⟩
  norm_num [variationActual, realize, List.signVariations, sign_apply]

private def twoCoefficients (i : Fin 2) : ℝ := if i = 0 then 1 else -1

private def twoExponents (i : Fin 2) : ℝ := -(i.val : ℝ)

private theorem twoExponents_strictAnti : StrictAnti twoExponents := by
  intro i j hij
  exact neg_lt_neg (Nat.cast_lt.mpr hij)

private theorem twoCoefficients_nonzero : ∃ i, twoCoefficients i ≠ 0 := by
  exact ⟨0, by norm_num [twoCoefficients]⟩

private theorem twoSum_zero : exponentialSum twoCoefficients twoExponents 0 = 0 := by
  norm_num [exponentialSum, twoCoefficients, twoExponents, Fin.sum_univ_two]

abbrev zeroArena : Arena where
  signature := variationSignature
  Law R := ∀ {N : ℕ} (a μ : Fin N → ℝ) (hμ : StrictAnti μ)
    (ha : ∃ i, a i ≠ 0) (Z : Finset ℝ)
    (hZ : ∀ t ∈ Z, exponentialSum a μ t = 0),
    Z.card ≤ R.readout () () (List.ofFn a)

private theorem zeroArenaRejected : ¬ zeroArena.Law variationRejected := by
  intro h
  have he := @h 2 twoCoefficients twoExponents twoExponents_strictAnti
    twoCoefficients_nonzero {0} (by
      intro t ht
      have ht0 : t = 0 := by simpa using ht
      subst t
      exact twoSum_zero)
  norm_num [variationRejected, realize] at he

def zeroArenaSource : Registration zeroArena (type_of% @zero_bound) where
  actual := variationActual
  bridge := Iff.rfl
  variation := ⟨zero_bound, variationRejected, zeroArenaRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    zeroArena.Law variationActual variationRejected zeroArenaRejected
  dependence := variationDependence

def zeroAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@zero_bound) (Realization variationSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExponentialSum.DescartesRule.zeroAuditUnit
  realizationName := `Reg.D5.S3.Analytic.ExponentialSum.DescartesRule.zeroArenaSource
  realizationSource := none
  generated := false
  arena := .source ⟨zeroArena⟩
  objectArena := .source ⟨zeroArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source zeroArena ⟨zeroArenaSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize variationSignature (fun _ _ a => a.signVariations)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExponentialSum.DescartesRule
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms zeroAudit

abbrev crossingArena : Arena where
  signature := variationSignature
  Law R := ∀ {N : ℕ} (a μ : Fin N → ℝ) (hμ : StrictAnti μ)
    (ha : ∃ i, a i ≠ 0) (Z : Finset ℝ)
    (hZ : ∀ t ∈ Z, exponentialSum a μ t = 0),
    Z.card + (Z.filter (fun z => ¬ ChangesSign (exponentialSum a μ) z)).card ≤
      R.readout () () (List.ofFn a)

private theorem crossingArenaRejected : ¬ crossingArena.Law variationRejected := by
  intro h
  have he := @h 2 twoCoefficients twoExponents twoExponents_strictAnti
    twoCoefficients_nonzero {0} (by
      intro t ht
      have ht0 : t = 0 := by simpa using ht
      subst t
      exact twoSum_zero)
  change ({0} : Finset ℝ).card + _ ≤ 0 at he
  simp only [Finset.card_singleton] at he
  omega

def crossingArenaSource : Registration crossingArena (type_of% @sign_crossing_bound) where
  actual := variationActual
  bridge := Iff.rfl
  variation := ⟨sign_crossing_bound, variationRejected, crossingArenaRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    crossingArena.Law variationActual variationRejected crossingArenaRejected
  dependence := variationDependence

def crossingAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sign_crossing_bound) (Realization variationSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExponentialSum.DescartesRule.crossingAuditUnit
  realizationName := `Reg.D5.S3.Analytic.ExponentialSum.DescartesRule.crossingArenaSource
  realizationSource := none
  generated := false
  arena := .source ⟨crossingArena⟩
  objectArena := .source ⟨crossingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source crossingArena ⟨crossingArenaSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize variationSignature (fun _ _ a => a.signVariations)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExponentialSum.DescartesRule
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms crossingAudit

abbrev signSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => SignType)

def signActual : Realization signSignature :=
  realize signSignature (fun _ _ x => SignType.sign x) (fun e => nomatch e)

def signRejected : Realization signSignature :=
  realize signSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem signDependence : ObservationalDependence signSignature signActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [signActual, realize]

abbrev signArena : Arena where
  signature := signSignature
  Law R := ∀ {N : ℕ} (a μ : Fin N → ℝ) (hμ : StrictAnti μ)
    (hlead : ∃ i, 0 < a i ∧ ∀ j, j < i → a j = 0)
    (Z : Finset ℝ) (hZ : ∀ t ∈ Z, exponentialSum a μ t = 0)
    (hcard : Z.card = (List.ofFn a).signVariations) (t : ℝ),
    R.readout () () (exponentialSum a μ t) = SignType.sign (∏ z ∈ Z, (t-z))

private theorem signArenaRejected : ¬ signArena.Law signRejected := by
  intro h
  have he := @h 1 (fun _ => 1) (fun _ => 0)
    (by
      intro i j hij
      have heq : i = j := Subsingleton.elim _ _
      subst j
      exact (lt_irrefl i hij).elim)
    (by
      refine ⟨0, by norm_num, ?_⟩
      intro j hj
      simp at hj)
    ∅ (by simp) (by simp [List.ofFn_const]) 0
  norm_num [signRejected, realize] at he

def signArenaSource : Registration signArena (type_of% @exact_sign) where
  actual := signActual
  bridge := Iff.rfl
  variation := ⟨exact_sign, signRejected, signArenaRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    signArena.Law signActual signRejected signArenaRejected
  dependence := signDependence

def signAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exact_sign) (Realization signSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExponentialSum.DescartesRule.signAuditUnit
  realizationName := `Reg.D5.S3.Analytic.ExponentialSum.DescartesRule.signArenaSource
  realizationSource := none
  generated := false
  arena := .source ⟨signArena⟩
  objectArena := .source ⟨signArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source signArena ⟨signArenaSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signSignature (fun _ _ x => SignType.sign x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExponentialSum.DescartesRule
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms signAudit

end
end Reg.D5.S3.Analytic.ExponentialSum.DescartesRule
