import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.HomomorphismFilteredTripleCensus
import Reg.Support.DependentFamily
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.ULift

namespace Reg.D5.S3.Factorization.HomomorphismFilteredTripleCensus

open _root_.D5.S3.Factorization.HomomorphismFilteredTripleCensus
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Pointwise

universe u v

noncomputable section

abbrev parameters := Σ (G : Type u), Σ (A : Type v),
  Σ (g : AddCommGroup G), Σ (a : AddCommGroup A), by
    letI := g
    letI := a
    exact G →+ A

abbrev structureSignature : Signature where
  Params := parameters.{u,v}
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Finset p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def structureActual : Realization structureSignature.{u,v} :=
  realize structureSignature (fun _ p t => by
    letI := p.2.2.1
    exact cycle t) (fun e => nomatch e)

def structureRejected : Realization structureSignature.{u,v} :=
  realize structureSignature (fun _ p _ => (∅ : Finset p.1)) (fun e => nomatch e)

def structureArena : Arena where
  signature := structureSignature.{u,v}
  Law r := ∀ {G : Type u} {A : Type v} [g : AddCommGroup G] [a : AddCommGroup A]
    (f : G →+ A) (t : G) (_ht : t ≠ 0),
    (∀ s : Triple f, t +ᵥ s = s → 3 • t = 0 ∧ f t ≠ 0) ∧
    (¬(3 • t = 0 ∧ f t ≠ 0) → AddAction.fixedBy (Triple f) t = ∅) ∧
    (3 • t = 0 → f t ≠ 0 →
      ∃ c : Triple f, c.val = r.readout () ⟨G,A,g,a,f⟩ t ∧
        (∀ s : Triple f, t +ᵥ s = s ↔ ∃ p : G, p +ᵥ c = s) ∧
        (∀ z : G, z ∈ AddAction.stabilizer G c ↔ z ∈ c.val) ∧
        (∀ p q : G, p +ᵥ c = q +ᵥ c ↔ p - q ∈ c.val) ∧
        Nat.card (AddAction.stabilizer G c) = 3)

abbrev liftIdentity : ULift.{u} (ZMod 3) →+ ULift.{v} (ZMod 3) where
  toFun x := ⟨x.down⟩
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem structure_rejected_law : ¬ structureArena.{u,v}.Law structureRejected := by
  intro h
  have ht : (⟨1⟩ : ULift.{u} (ZMod 3)) ≠ 0 := by
    intro h
    have := congrArg ULift.down h
    exact (by decide : (1 : ZMod 3) ≠ 0) this
  have h3 : 3 • (⟨1⟩ : ULift.{u} (ZMod 3)) = 0 := by
    apply ULift.ext
    decide
  have hf : liftIdentity.{u,v} ⟨1⟩ ≠ 0 := by
    intro h
    have := congrArg ULift.down h
    exact (by decide : (1 : ZMod 3) ≠ 0) this
  obtain ⟨c, hc, _⟩ := (h liftIdentity ⟨1⟩ ht).2.2 h3 hf
  have hh := c.property.1
  change c.val = ∅ at hc
  rw [hc, Finset.card_empty] at hh
  contradiction

def structureRegistration : Registration structureArena.{u,v}
    (∀ {G : Type u} {A : Type v} [AddCommGroup G] [AddCommGroup A]
      (f : G →+ A) (t : G) (_ht : t ≠ 0),
      (∀ s : Triple f, t +ᵥ s = s → 3 • t = 0 ∧ f t ≠ 0) ∧
      (¬(3 • t = 0 ∧ f t ≠ 0) → AddAction.fixedBy (Triple f) t = ∅) ∧
      (3 • t = 0 → f t ≠ 0 →
        ∃ c : Triple f, c.val = cycle t ∧
          (∀ s : Triple f, t +ᵥ s = s ↔ ∃ p : G, p +ᵥ c = s) ∧
          (∀ z : G, z ∈ AddAction.stabilizer G c ↔ z ∈ c.val) ∧
          (∀ p q : G, p +ᵥ c = q +ᵥ c ↔ p - q ∈ c.val) ∧
          Nat.card (AddAction.stabilizer G c) = 3)) where
  actual := structureActual
  bridge := Iff.rfl
  variation := ⟨by intro G A _ _ f t ht; exact fixed_family_structure f t ht,
    structureRejected, structure_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨structureRejected, ?_, rfl, structure_rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    classical
    intro i
    letI : DecidableEq (ULift.{u} (ZMod 3)) := Classical.decEq _
    refine ⟨⟨ULift.{u} (ZMod 3), ULift.{v} (ZMod 3), inferInstance,
      inferInstance, liftIdentity⟩, (0 : ULift.{u} (ZMod 3)), (⟨1⟩ : ULift.{u} (ZMod 3)), ?_⟩
    change cycle (0 : ULift.{u} (ZMod 3)) ≠ cycle ⟨1⟩
    intro h
    have hx : (⟨1⟩ : ULift.{u} (ZMod 3)) ∈ cycle ⟨1⟩ := by
      exact Finset.mem_image.mpr ⟨1, by decide, by simp⟩
    rw [← h] at hx
    have hz : cycle (0 : ULift.{u} (ZMod 3)) = {0} := by
      ext z
      simp only [cycle, Finset.mem_image, Finset.mem_singleton, zero_nsmul]
      constructor
      · rintro ⟨k, _, hk⟩
        simpa using hk.symm
      · intro hz
        exact ⟨0, by decide, by simpa using hz.symm⟩
    rw [hz, Finset.mem_singleton] at hx
    have he := congrArg ULift.down hx
    exact (by decide : (1 : ZMod 3) ≠ 0) he

abbrev countSignature : Signature where
  Params := parameters.{u,v}
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def countActual : Realization countSignature.{u,v} :=
  realize countSignature (fun _ p t => by
    letI := p.2.2.1
    letI := p.2.2.2.1
    exact Nat.card (AddAction.fixedBy (Triple p.2.2.2.2) t)) (fun e => nomatch e)

def countRejected : Realization countSignature.{u,v} :=
  realize countSignature (fun _ _ _ => (0 : ℕ)) (fun e => nomatch e)

def countArena : Arena where
  signature := countSignature.{u,v}
  Law r := ∀ {G : Type u} {A : Type v} [g : AddCommGroup G] [a : AddCommGroup A]
    [Finite G] (f : G →+ A) (t : G) (_ht : t ≠ 0),
    r.readout () ⟨G,A,g,a,f⟩ t =
      @ite ℕ (3 • t = 0 ∧ f t ≠ 0) (Classical.propDecidable _) (Nat.card G / 3) 0

private theorem count_rejected_law : ¬ countArena.{u,v}.Law countRejected := by
  intro h
  have ht : (⟨1⟩ : ULift.{u} (ZMod 3)) ≠ 0 := by
    intro h
    exact (by decide : (1 : ZMod 3) ≠ 0) (congrArg ULift.down h)
  have he : 3 • (⟨1⟩ : ULift.{u} (ZMod 3)) = 0 ∧ liftIdentity.{u,v} ⟨1⟩ ≠ 0 := by
    constructor
    · apply ULift.ext; decide
    · intro h
      exact (by decide : (1 : ZMod 3) ≠ 0) (congrArg ULift.down h)
  have hh := h liftIdentity ⟨1⟩ ht
  change 0 = _ at hh
  rw [if_pos he, Nat.card_ulift, Nat.card_zmod] at hh
  contradiction

abbrev liftDouble : ULift.{u} (ZMod 6) →+ ULift.{v} (ZMod 6) where
  toFun x := ⟨2 * x.down⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; exact mul_add 2 x.down y.down

def countRegistration : Registration countArena.{u,v}
    (∀ {G : Type u} {A : Type v} [AddCommGroup G] [AddCommGroup A]
      [Finite G] (f : G →+ A) (t : G) (_ht : t ≠ 0),
      Nat.card (AddAction.fixedBy (Triple f) t) =
        @ite ℕ (3 • t = 0 ∧ f t ≠ 0) (Classical.propDecidable _) (Nat.card G / 3) 0) where
  actual := countActual
  bridge := Iff.rfl
  variation := ⟨by intro G A _ _ _ f t ht; exact fixed_point_census f t ht,
    countRejected, count_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨countRejected, ?_, rfl, count_rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} (ZMod 6), ULift.{v} (ZMod 6), inferInstance,
      inferInstance, liftDouble⟩, ⟨1⟩, ⟨2⟩, ?_⟩
    change Nat.card (AddAction.fixedBy (Triple liftDouble) (⟨1⟩ : ULift.{u} (ZMod 6))) ≠
      Nat.card (AddAction.fixedBy (Triple liftDouble) (⟨2⟩ : ULift.{u} (ZMod 6)))
    have ht1 : (⟨1⟩ : ULift.{u} (ZMod 6)) ≠ 0 := by
      intro h; exact (by decide : (1 : ZMod 6) ≠ 0) (congrArg ULift.down h)
    have ht2 : (⟨2⟩ : ULift.{u} (ZMod 6)) ≠ 0 := by
      intro h; exact (by decide : (2 : ZMod 6) ≠ 0) (congrArg ULift.down h)
    have hn : ¬(3 • (⟨1⟩ : ULift.{u} (ZMod 6)) = 0 ∧ liftDouble.{u,v} ⟨1⟩ ≠ 0) := by
      intro h; exact (by decide : (3 : ZMod 6) ≠ 0) (congrArg ULift.down h.1)
    have he : 3 • (⟨2⟩ : ULift.{u} (ZMod 6)) = 0 ∧ liftDouble.{u,v} ⟨2⟩ ≠ 0 := by
      constructor
      · apply ULift.ext; decide
      · intro h; exact (by decide : (4 : ZMod 6) ≠ 0) (congrArg ULift.down h)
    rw [fixed_point_census liftDouble _ ht1, if_neg hn,
      fixed_point_census liftDouble _ ht2, if_pos he, Nat.card_ulift, Nat.card_zmod]
    decide

noncomputable def structure_contract : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Factorization.HomomorphismFilteredTripleCensus.fixed_family_structure.{u,v})
    (type_of% (realize structureSignature.{u,v} (fun _ p t => by
      letI := p.2.2.1
      exact cycle t) (fun e => nomatch e))) (Unit) (Unit) where
  unitName := `fixed_family_structure_information_unit
  realizationName := `Reg.D5.S3.Factorization.HomomorphismFilteredTripleCensus.structureRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨structureArena.{u,v}⟩
  objectArena := .source ⟨structureArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (structureArena.{u,v}) ⟨structureRegistration.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize structureSignature.{u,v} (fun _ p t => by
    letI := p.2.2.1
    exact cycle t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Factorization.HomomorphismFilteredTripleCensus
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
      "arg", "arg", "body", "body", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def count_contract : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Factorization.HomomorphismFilteredTripleCensus.fixed_point_census.{u,v})
    (type_of% (realize countSignature.{u,v} (fun _ p t => by
      letI := p.2.2.1
      letI := p.2.2.2.1
      exact Nat.card (AddAction.fixedBy (Triple p.2.2.2.2) t)) (fun e => nomatch e))) (Unit) (Unit) where
  unitName := `fixed_point_census_information_unit
  realizationName := `Reg.D5.S3.Factorization.HomomorphismFilteredTripleCensus.countRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨countArena.{u,v}⟩
  objectArena := .source ⟨countArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (countArena.{u,v}) ⟨countRegistration.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize countSignature.{u,v} (fun _ p t => by
    letI := p.2.2.1
    letI := p.2.2.2.1
    exact Nat.card (AddAction.fixedBy (Triple p.2.2.2.2) t)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Factorization.HomomorphismFilteredTripleCensus
    definition := none
    coordinates := #[0, 1, 2, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
      "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms structureRegistration
#print axioms countRegistration

end

end Reg.D5.S3.Factorization.HomomorphismFilteredTripleCensus
