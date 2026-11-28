import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.ResidueRings.MesyanIdempotent
import Mathlib.Algebra.Ring.ULift
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Algebra.Tropical.Basic

/-!
Source-bound registration for the idempotent classification. The observed
operation is left submonoid multiplication.
-/

set_option autoImplicit false

namespace Reg.D5.S3.Arith.ResidueRings.MesyanIdempotent

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.ResidueRings.MesyanIdempotent
open scoped Pointwise

universe u

private abbrev Params :=
  (S : Type u) × (s : NonUnitalNonAssocSemiring S) × @AddSubmonoid S (letI := s; inferInstance)

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

private def arena : Arena.{u + 1, u, 0, u, 0} where
  signature := signature
  Law := fun F => ∀ {S : Type u} [s : NonUnitalNonAssocSemiring S] (_ : ∀ a : S, a + a = a),
    (∃ E : AddSubmonoid S, ∀ M : AddSubmonoid S,
      F.readout () ⟨S, s, E⟩ M = M ∧ M * E = M) ↔
      ∃ u : S, ∀ x : S, u * x = x ∧ x * u = x

private abbrev Witness := ULift.{u} (MinTropical (WithTop ℕ))

private theorem erased_fails : ¬ arena.{u}.Law erased := by
  intro h
  have hAdd (a : Witness.{u}) : a + a = a :=
    ULift.ext (MinTropical.add_self a.down)
  obtain ⟨E, hE⟩ := (@h Witness.{u} _ hAdd).2 ⟨1, fun x => ⟨one_mul x, mul_one x⟩⟩
  exact (bot_ne_top : (⊥ : AddSubmonoid Witness.{u}) ≠ ⊤) ((hE ⊤).1)

private theorem sensitivity : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    change Unit at i
    exact ⟨erased, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim, rfl, erased_fails⟩
  · intro e
    exact nomatch e

private theorem dependence :
    ∀ i, ∃ p x y, (actual.{u}).readout i p x ≠ (actual.{u}).readout i p y := by
  intro i
  change Unit at i
  cases i
  refine ⟨⟨Witness.{u}, inferInstance, 1⟩, (⊥ : AddSubmonoid Witness.{u}),
    (⊤ : AddSubmonoid Witness.{u}), ?_⟩
  change (1 : AddSubmonoid Witness.{u}) * ⊥ ≠ 1 * ⊤
  simpa only [one_mul] using (bot_ne_top : (⊥ : AddSubmonoid Witness.{u}) ≠ ⊤)

def classificationFamily :
    Registration arena.{u} (type_of% (@product_unit_iff.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@product_unit_iff.{u}, erased, erased_fails⟩
  sensitivity := sensitivity
  dependence := dependence

def classificationRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@product_unit_iff.{u}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.Arith.ResidueRings.MesyanIdempotent.product_unit_iff.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.ResidueRings.MesyanIdempotent.classificationFamily
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨classificationFamily⟩
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
    owner := `D5.S3.Arith.ResidueRings.MesyanIdempotent
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

end Reg.D5.S3.Arith.ResidueRings.MesyanIdempotent
