import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.ResidueRings.MesyanQuantaleClassification
import Mathlib.Algebra.Ring.ULift

set_option autoImplicit false

namespace Reg.D5.S3.Arith.ResidueRings.MesyanQuantaleClassification
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.ResidueRings.MesyanQuantaleClassification
open scoped Pointwise

universe u

private abbrev Params := (R : Type u) × (s : NonUnitalRing R) × @AddSubmonoid R (letI := s; inferInstance)

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

private def arena : Arena.{u + 1, u, 0, u, 0} where
  signature := signature
  Law := fun F => ∀ {R : Type u} [s : NonUnitalRing R],
    (∃ E : AddSubmonoid R, ∀ M : AddSubmonoid R,
      F.readout () ⟨R, s, E⟩ M = M ∧ M * E = M) ↔
      (∃ u : R, ∀ x : R, u * x = x ∧ x * u = x) ∨
      ((∀ a : R, 0 < addOrderOf a) ∧
        ∀ p : Nat.Primes, ∃ u : R, (∃ j : ℕ, (p : ℕ) ^ j • u = 0) ∧
          ∀ x : R, (∃ j : ℕ, (p : ℕ) ^ j • x = 0) → u * x = x ∧ x * u = x)

private def erased : Realization signature.{u} :=
  realize signature (fun _ p _ => letI := p.2.1; (⊥ : AddSubmonoid p.1)) (fun e => nomatch e)

private theorem erased_fails : ¬ arena.{u}.Law erased := by
  intro h
  have hInt := @h (ULift.{u} ℤ) _
  obtain ⟨E, hE⟩ := hInt.2 (Or.inl ⟨1, fun x => ⟨one_mul x, mul_one x⟩⟩)
  exact (bot_ne_top : (⊥ : AddSubmonoid (ULift.{u} ℤ)) ≠ ⊤) ((hE ⊤).1)

def family : Registration arena.{u} (type_of% (@product_unit_iff.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@product_unit_iff.{u}, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      change Unit at i
      exact ⟨erased, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim, rfl, erased_fails⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    change Unit at i
    cases i
    refine ⟨⟨ULift.{u} ℤ, inferInstance, 1⟩, (⊥ : AddSubmonoid (ULift.{u} ℤ)),
      (⊤ : AddSubmonoid (ULift.{u} ℤ)), ?_⟩
    change (1 : AddSubmonoid (ULift.{u} ℤ)) * ⊥ ≠ 1 * ⊤
    simpa only [one_mul] using (bot_ne_top : (⊥ : AddSubmonoid (ULift.{u} ℤ)) ≠ ⊤)

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@product_unit_iff.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Arith.ResidueRings.MesyanQuantaleClassification.product_unit_iff.__information_unit
  realizationName := `Reg.D5.S3.Arith.ResidueRings.MesyanQuantaleClassification.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
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
    owner := `D5.S3.Arith.ResidueRings.MesyanQuantaleClassification
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "body",
        "body", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.ResidueRings.MesyanQuantaleClassification
