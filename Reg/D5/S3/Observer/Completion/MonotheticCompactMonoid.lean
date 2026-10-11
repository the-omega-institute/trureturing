import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Completion.MonotheticCompactMonoid
import Reg.Support.DependentFamily
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Group.ULift
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.ZMod.Basic

open Set Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.Completion.MonotheticCompactMonoid
open LeanInformationAudit

noncomputable section

namespace Reg.D5.S3.Observer.Completion.MonotheticCompactMonoid
universe u

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => (n : ℕ∞)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊤) (fun e => nomatch e)

/-- Only the natural-index inclusion into extended naturals is varied. -/
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {M : Type u} [AddCommMonoid M] [TopologicalSpace M]
    [ContinuousAdd M] [CompactSpace M] [T2Space M]
    (a : M) (_hd : DenseRange fun n : ℕ => n • a),
    (∃ group : AddCommGroup (core a),
      let := group
      (∀ x y : core a, ((x + y : core a) : M) = (x : M) + (y : M)) ∧
      IsTopologicalAddGroup (core a) ∧
      ∃ r : M →+ core a, Continuous r ∧
        (∀ x : M, (r x : M) = x + ((0 : core a) : M)) ∧
        (∀ x : core a, r (x : M) = x) ∧
        DenseRange (fun n : ℕ => n • r a)) ∧
    ((core a).Nonempty ∧ IsCompact (core a) ∧
    (∀ x : M, (fun z => x + z) '' core a = core a) ∧
    (∀ I : Set M, I.Nonempty → (∀ x : M, ∀ y ∈ I, x + y ∈ I) → core a ⊆ I) ∧
    (0 ∈ core a ↔ core a = univ) ∧
    ∃! t : ℕ∞,
      (∀ n : ℕ, n • a ∉ core a ↔ obs.readout () () n < t) ∧
      (core a)ᶜ = (fun n : ℕ => n • a) '' {n | (n : ℕ∞) < t} ∧
      Set.InjOn (fun n : ℕ => n • a) {n | (n : ℕ∞) < t} ∧
      (∀ n : ℕ, (n : ℕ∞) < t → IsOpen ({n • a} : Set M)))

theorem positive : arena.{u}.Law actual := @core_structure.{u}

theorem negative : ¬ arena.{u}.Law rejected := by
  intro h
  let C := ULift.{u} (Additive (WithZero Unit))
  let : TopologicalSpace C := ⊥
  have : DiscreteTopology C := ⟨rfl⟩
  have : Finite C := by
    change Finite (ULift.{u} (Option Unit))
    infer_instance
  let a : C := ⟨Additive.ofMul 0⟩
  have hd : DenseRange fun n : ℕ => n • a := by
    apply Function.Surjective.denseRange
    intro x
    rcases x with ⟨x⟩
    change Additive (WithZero Unit) at x
    rcases (x : WithZero Unit) with _ | x
    · exact ⟨1, by change 1 • a = a; exact one_nsmul a⟩
    · cases x
      exact ⟨0, rfl⟩
  have hzero : (0 : C) ∉ core a := by
    intro hz
    have hz1 := mem_iInter.mp hz 1
    have heq : tail a 1 = {a} := by
      unfold tail
      have hrange : (range fun n : ℕ => (1 + n) • a) = {a} := by
        ext x
        constructor
        · rintro ⟨n, rfl⟩
          change (1 + n) • a = a
          apply ULift.ext
          change (0 : WithZero Unit) ^ (1 + n) = 0
          simp
        · rintro rfl
          exact ⟨0, by simp⟩
      rw [hrange, isClosed_singleton.closure_eq]
    rw [heq] at hz1
    have hz' : (0 : C) = a := hz1
    have := congrArg ULift.down hz'
    change (1 : WithZero Unit) = 0 at this
    exact one_ne_zero this
  obtain ⟨t, ht, _⟩ := (h a hd).2.2.2.2.2.2
  have ht0 := (ht.1 0).mp (by simpa only [zero_nsmul] using hzero)
  exact not_top_lt ht0

theorem sensitivity : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, negative⟩
    intro j hj
    exact (hj (Subsingleton.elim j i)).elim
  · intro e
    exact nomatch e

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def evidence : Registration arena.{u} (arena.{u}.Law actual) :=
  Registration.mk actual Iff.rfl ⟨positive, rejected, negative⟩ sensitivity dependence

#print axioms evidence

def core_registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@core_structure.{u})
    (type_of% (realize signature (fun _ _ n => (n : ℕ∞)) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `D5.S3.Observer.Completion.MonotheticCompactMonoid.core_structure.__information_unit
  realizationName := `Reg.D5.S3.Observer.Completion.MonotheticCompactMonoid.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (n : ℕ∞)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Completion.MonotheticCompactMonoid
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "body",
        "fn", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms core_registration

abbrev ringSignature : Signature where
  Params := Σ S : Type u, Σ _x : S, S
  State p := HMul p.1 p.1 p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def ringActual : Realization ringSignature.{u} :=
  realize ringSignature (fun _ p op => @HMul.hMul _ _ _ op p.2.1 p.2.2)
    (fun e => nomatch e)

def ringRejected : Realization ringSignature.{u} :=
  realize ringSignature (fun _ p _ => p.2.1) (fun e => nomatch e)

/-- The multiplication operand in the global commutativity clause is varied. -/
abbrev ringArena : Arena where
  signature := ringSignature.{u}
  Law obs := ∀ {S : Type u} [Semiring S] [TopologicalSpace S]
    [ContinuousAdd S] [ContinuousMul S] [CompactSpace S] [T2Space S]
    (_hd : DenseRange fun n : ℕ => n • (1 : S)),
    (∀ x y : S, obs.readout () ⟨S, x, y⟩ (inferInstance : HMul S S S) = y * x) ∧
    ∃ ring : CommRing (core (1 : S)),
      let := ring
      (∀ x y : core (1 : S), ((x + y : core (1 : S)) : S) = (x : S) + (y : S)) ∧
      (∀ x y : core (1 : S), ((x * y : core (1 : S)) : S) = (x : S) * (y : S)) ∧
      IsTopologicalRing (core (1 : S)) ∧ CompactSpace (core (1 : S)) ∧
      ((1 : core (1 : S)) : S) = 1 + ((0 : core (1 : S)) : S) ∧
      ∃ r : S →+* core (1 : S), Continuous r ∧ Function.Surjective r ∧
        (∀ x : S, (r x : S) = x + ((0 : core (1 : S)) : S)) ∧
        (∀ x : core (1 : S), r (x : S) = x) ∧
        DenseRange (fun n : ℕ => n • (1 : core (1 : S)))

theorem ring_positive : ringArena.{u}.Law ringActual := @core_ring_retraction.{u}

theorem ring_negative : ¬ ringArena.{u}.Law ringRejected := by
  intro h
  let C := ULift.{u} (ZMod 2)
  let : TopologicalSpace C := ⊥
  have : DiscreteTopology C := ⟨rfl⟩
  have hd : DenseRange fun n : ℕ => n • (1 : C) := by
    apply Function.Surjective.denseRange
    rintro ⟨x⟩
    refine ⟨x.val, ?_⟩
    apply ULift.ext
    change x.val • (1 : ZMod 2) = x
    simpa only [nsmul_one] using ZMod.natCast_zmod_val x
  have heq := (h hd).1 1 0
  change (1 : C) = 0 * 1 at heq
  exact one_ne_zero (by simpa only [zero_mul] using heq)

theorem ring_sensitivity : Sensitivity ringArena.{u} ringActual := by
  constructor
  · intro i
    refine ⟨ringRejected, ?_, rfl, ring_negative⟩
    intro j hj
    exact (hj (Subsingleton.elim j i)).elim
  · intro e
    exact nomatch e

theorem ring_dependence : ObservationalDependence ringSignature.{u} ringActual := by
  intro i
  let B := ULift.{u} Bool
  refine ⟨⟨B, ⟨false⟩, ⟨false⟩⟩, ⟨fun _ _ => ⟨false⟩⟩,
    ⟨fun _ _ => ⟨true⟩⟩, ?_⟩
  intro h
  have h' := congrArg ULift.down h
  exact Bool.false_ne_true h'

def ringEvidence : Registration ringArena.{u} (ringArena.{u}.Law ringActual) :=
  Registration.mk ringActual Iff.rfl ⟨ring_positive, ringRejected, ring_negative⟩
    ring_sensitivity ring_dependence

#print axioms ringEvidence


def ring_registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@core_ring_retraction.{u})
    (type_of% (realize ringSignature
      (fun _ p op => @HMul.hMul _ _ _ op p.2.1 p.2.2) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `D5.S3.Observer.Completion.MonotheticCompactMonoid.core_ring_retraction.__information_unit
  realizationName := `Reg.D5.S3.Observer.Completion.MonotheticCompactMonoid.ringEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨ringArena.{u}⟩
  objectArena := .source ⟨ringArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ringArena.{u} ⟨ringEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize ringSignature
    (fun _ p op => @HMul.hMul _ _ _ op p.2.1 p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Completion.MonotheticCompactMonoid
    definition := none
    coordinates := #[0, 8, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms ring_registration

end Reg.D5.S3.Observer.Completion.MonotheticCompactMonoid
