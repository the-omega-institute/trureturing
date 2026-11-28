import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.ResidueRings.MesyanCancellative
import Mathlib.Algebra.Ring.ULift

/-!
Source-bound registrations for the semiring classification and the local
fixing criterion. The observed operation is left submonoid multiplication.
-/

set_option autoImplicit false

namespace Reg.D5.S3.Arith.ResidueRings.MesyanCancellative

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.ResidueRings.MesyanCancellative
open scoped Pointwise

universe u

private abbrev Params :=
  (S : Type u) × (s : NonUnitalSemiring S) × @AddSubmonoid S (letI := s; inferInstance)

private def signature : Signature where
  Params := Params.{u}
  State := fun p => letI := p.2.1; AddSubmonoid p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => letI := p.2.1; AddSubmonoid p.1
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u} :=
  realize signature (fun _ p M => by
    letI := p.2.1
    exact @HMul.hMul (AddSubmonoid p.1) (AddSubmonoid p.1) (AddSubmonoid p.1)
      inferInstance p.2.2 M) (fun e => nomatch e)

private def erased : Realization signature.{u} :=
  realize signature (fun _ p _ => letI := p.2.1; (⊥ : AddSubmonoid p.1)) (fun e => nomatch e)

private def classificationArena : Arena.{u + 1, u, 0, u, 0} where
  signature := signature
  Law := fun F => ∀ {S : Type u} [s : NonUnitalSemiring S] [IsLeftCancelAdd S],
    (∃ E : AddSubmonoid S, ∀ M : AddSubmonoid S,
      F.readout () ⟨S, s, E⟩ M = M ∧ M * E = M) ↔
      (∃ u : S, ∀ x : S, u * x = x ∧ x * u = x) ∨
      ((∀ a : S, 0 < addOrderOf a) ∧
        ∀ p : Nat.Primes, ∃ u : S, (∃ j : ℕ, (p : ℕ) ^ j • u = 0) ∧
          ∀ x : S, (∃ j : ℕ, (p : ℕ) ^ j • x = 0) → u * x = x ∧ x * u = x)

private theorem classification_erased_fails : ¬ classificationArena.{u}.Law erased := by
  intro h
  have hInt := @h (ULift.{u} ℤ) _ _
  obtain ⟨E, hE⟩ := hInt.2 (Or.inl ⟨1, fun x => ⟨one_mul x, mul_one x⟩⟩)
  exact (bot_ne_top : (⊥ : AddSubmonoid (ULift.{u} ℤ)) ≠ ⊤) ((hE ⊤).1)

private theorem sensitivity (law : Realization signature.{u} → Prop)
    (hFailure : ¬ law erased) :
    Sensitivity { signature := signature, Law := law } actual := by
  constructor
  · intro i
    change Unit at i
    exact ⟨erased, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim, rfl, hFailure⟩
  · intro e
    exact nomatch e

private theorem dependence :
    ∀ i, ∃ p x y, (actual.{u}).readout i p x ≠ (actual.{u}).readout i p y := by
  intro i
  change Unit at i
  cases i
  refine ⟨⟨ULift.{u} ℤ, inferInstance, 1⟩, (⊥ : AddSubmonoid (ULift.{u} ℤ)),
    (⊤ : AddSubmonoid (ULift.{u} ℤ)), ?_⟩
  change (1 : AddSubmonoid (ULift.{u} ℤ)) * ⊥ ≠ 1 * ⊤
  simpa only [one_mul] using (bot_ne_top : (⊥ : AddSubmonoid (ULift.{u} ℤ)) ≠ ⊤)

def classificationFamily :
    Registration classificationArena.{u} (type_of% (@product_unit_iff_cancellative.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@product_unit_iff_cancellative.{u}, erased, classification_erased_fails⟩
  sensitivity := sensitivity classificationArena.Law classification_erased_fails
  dependence := dependence

def classificationRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@product_unit_iff_cancellative.{u}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.Arith.ResidueRings.MesyanCancellative.product_unit_iff_cancellative.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.ResidueRings.MesyanCancellative.classificationFamily
  realizationSource := none
  generated := false
  arena := .source ⟨classificationArena⟩
  objectArena := .source ⟨classificationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source classificationArena ⟨classificationFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p M => by
      letI := p.2.1
      exact @HMul.hMul (AddSubmonoid p.1) (AddSubmonoid p.1) (AddSubmonoid p.1)
        inferInstance p.2.2 M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.ResidueRings.MesyanCancellative
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "body",
        "body", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev CriterionParams :=
  (S : Type u) × (s : NonUnitalNonAssocSemiring S) × @AddSubmonoid S (letI := s; inferInstance)

private def criterionSignature : Signature where
  Params := CriterionParams.{u}
  State := fun p => letI := p.2.1; AddSubmonoid p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => letI := p.2.1; AddSubmonoid p.1
  Anchor := Empty
  finiteAnchor := inferInstance

private def criterionActual : Realization criterionSignature.{u} :=
  realize criterionSignature (fun _ p M => by
    letI := p.2.1
    exact @HMul.hMul (AddSubmonoid p.1) (AddSubmonoid p.1) (AddSubmonoid p.1)
      inferInstance p.2.2 M) (fun e => nomatch e)

private def criterionErased : Realization criterionSignature.{u} :=
  realize criterionSignature (fun _ p _ => letI := p.2.1; (⊥ : AddSubmonoid p.1)) (fun e => nomatch e)

private def criterionArena : Arena.{u + 1, u, 0, u, 0} where
  signature := criterionSignature
  Law := fun F => ∀ {S : Type u} [s : NonUnitalNonAssocSemiring S] (E : AddSubmonoid S),
    (∀ M : AddSubmonoid S, F.readout () ⟨S, s, E⟩ M = M ∧ M * E = M) ↔
      E = cyclicPreservingMultipliers S ∧ ∀ x : S,
        (∃ l ∈ cyclicPreservingMultipliers S, l * x = x) ∧
        (∃ r ∈ cyclicPreservingMultipliers S, x * r = x)

private theorem criterion_erased_fails : ¬ criterionArena.{u}.Law criterionErased := by
  intro h
  let S := ULift.{u} ℤ
  have hOne : (1 : S) ∈ cyclicPreservingMultipliers S := fun x =>
    ⟨⟨1, (one_nsmul x).trans (one_mul x).symm⟩,
      ⟨1, (one_nsmul x).trans (mul_one x).symm⟩⟩
  have hMul := (@h S _ (cyclicPreservingMultipliers S)).2
    ⟨rfl, fun x => ⟨⟨1, hOne, one_mul x⟩, ⟨1, hOne, mul_one x⟩⟩⟩
  exact (bot_ne_top : (⊥ : AddSubmonoid S) ≠ ⊤) ((hMul ⊤).1)

private theorem criterionSensitivity : Sensitivity criterionArena.{u} criterionActual := by
  constructor
  · intro i
    change Unit at i
    exact ⟨criterionErased, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
      rfl, criterion_erased_fails⟩
  · intro e
    exact nomatch e

private theorem criterionDependence :
    ∀ i, ∃ p x y, (criterionActual.{u}).readout i p x ≠ (criterionActual.{u}).readout i p y := by
  intro i
  change Unit at i
  cases i
  refine ⟨⟨ULift.{u} ℤ, inferInstance, 1⟩, (⊥ : AddSubmonoid (ULift.{u} ℤ)),
    (⊤ : AddSubmonoid (ULift.{u} ℤ)), ?_⟩
  change (1 : AddSubmonoid (ULift.{u} ℤ)) * ⊥ ≠ 1 * ⊤
  simpa only [one_mul] using (bot_ne_top : (⊥ : AddSubmonoid (ULift.{u} ℤ)) ≠ ⊤)

def criterionFamily :
    Registration criterionArena.{u}
      (type_of% (@product_unit_iff_eq_cyclicPreservingMultipliers.{u})) where
  actual := criterionActual
  bridge := Iff.rfl
  variation :=
    ⟨@product_unit_iff_eq_cyclicPreservingMultipliers.{u}, criterionErased, criterion_erased_fails⟩
  sensitivity := criterionSensitivity
  dependence := criterionDependence

def criterionRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@product_unit_iff_eq_cyclicPreservingMultipliers.{u}) (Realization criterionSignature.{u}) Unit Unit where
  unitName :=
    `D5.S3.Arith.ResidueRings.MesyanCancellative.product_unit_iff_eq_cyclicPreservingMultipliers.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.ResidueRings.MesyanCancellative.criterionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨criterionArena⟩
  objectArena := .source ⟨criterionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source criterionArena ⟨criterionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize criterionSignature (fun _ p M => by
      letI := p.2.1
      exact @HMul.hMul (AddSubmonoid p.1) (AddSubmonoid p.1) (AddSubmonoid p.1)
        inferInstance p.2.2 M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.ResidueRings.MesyanCancellative
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.ResidueRings.MesyanCancellative
