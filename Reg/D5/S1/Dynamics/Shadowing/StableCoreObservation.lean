import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Dynamics.Shadowing.StableCoreObservation
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.Shadowing
open Set Function

namespace Reg.D5.S1.Dynamics.Shadowing.StableCoreObservation

noncomputable section
universe u v

abbrev sumSignature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def sumActual : Realization sumSignature :=
  realize sumSignature (fun _ m n => n + m) (fun e => nomatch e)

def sumRejected : Realization sumSignature :=
  realize sumSignature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Vary only the observed iterate's time in the conclusion. All topology,
continuity, core hypotheses and the complete uniform quantifiers remain. -/
abbrev tailArena : Arena where
  signature := sumSignature
  Law R := ∀ {X : Type u} {D : Type v}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace D] [DiscreteTopology D]
    (f : X → X) (q : X → D) (_hf : Continuous f) (_hq : Continuous q) (M : ℕ)
    (_hcore : ∀ a ∈ stableCore f, q (f^[M] a) = q a),
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x : X,
      q (f^[R.readout () M n] x) = q (f^[n] x)

private theorem tail_rejected_law : ¬ tailArena.{u,v}.Law sumRejected := by
  intro h
  let X := ULift.{u} Bool
  let D := ULift.{v} Bool
  let : TopologicalSpace X := ⊥
  let : DiscreteTopology X := ⟨rfl⟩
  let : TopologicalSpace D := ⊥
  let : DiscreteTopology D := ⟨rfl⟩
  let f : X → X := fun _ => ⟨true⟩
  let q : X → D := fun x => ⟨x.down⟩
  have hcore : ∀ a ∈ stableCore f, q (f^[1] a) = q a := by
    intro a ha
    obtain ⟨x, hx⟩ := Set.mem_iInter.mp ha 1
    have heq : (⟨true⟩ : X) = a := by simpa [f] using hx
    rw [← heq]
    rfl
  obtain ⟨N, hN⟩ := h f q continuous_of_discreteTopology continuous_of_discreteTopology
    1 hcore
  have heq := congrArg ULift.down (hN (N + 1) (by omega) (⟨false⟩ : X))
  change false = (f^[N + 1] (⟨false⟩ : X)).down at heq
  simp only [iterate_succ_apply', f] at heq
  contradiction

def tailRegistration : Registration tailArena.{u,v}
    (type_of% (@finite_observation_eventually_periodic_of_stable_core_periodic.{u,v})) where
  actual := sumActual
  bridge := Iff.rfl
  variation := ⟨@finite_observation_eventually_periodic_of_stable_core_periodic.{u,v},
    sumRejected, tail_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨sumRejected, ?_, rfl, tail_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    exact ⟨0, 0, 1, by change (0 : ℕ) ≠ 1; decide⟩

abbrev positiveSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def positiveActual : Realization positiveSignature :=
  realize positiveSignature (fun _ _ m => m) (fun e => nomatch e)

def positiveRejected : Realization positiveSignature :=
  realize positiveSignature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Observe the actual period inside its positive-period hypothesis, without removing the
uniform tail hypothesis or any whole-name/prefix coordinate. -/
abbrev prefixArena : Arena where
  signature := positiveSignature
  Law R := ∀ {X : Type u} {D : Type v} (f : X → X) (q : X → D) (N M : ℕ)
    (_hM : 0 < R.readout () () M)
    (_htail : ∀ n : ℕ, N ≤ n → ∀ x : X, q (f^[n + M] x) = q (f^[n] x)),
    Function.Injective (fun w : Set.range (fun x n => q (f^[n] x)) =>
      fun i : Fin (N + M) => w.1 i)

private theorem prefix_rejected_law : ¬ prefixArena.{u,v}.Law positiveRejected := by
  intro h
  let X := ULift.{u} Bool
  let D := ULift.{v} Bool
  let q : X → D := fun x => ⟨x.down⟩
  have hinj := h (id : X → X) q 0 0 (by decide) (fun _ _ _ => rfl)
  let w : Set.range (fun x n => q (id^[n] x)) := ⟨_, ⟨(⟨false⟩ : X), rfl⟩⟩
  let z : Set.range (fun x n => q (id^[n] x)) := ⟨_, ⟨(⟨true⟩ : X), rfl⟩⟩
  have hp : (fun i : Fin (0 + 0) => w.1 i) = (fun i : Fin (0 + 0) => z.1 i) :=
    funext fun i => Fin.elim0 i
  have heq := congrArg (fun a => (a.1 0).down) (hinj hp)
  change false = true at heq
  contradiction

private theorem prefix_actual_law : prefixArena.{u,v}.Law positiveActual := by
  exact @forward_name_prefix_injective_of_eventually_periodic.{u,v}

def prefixRegistration : Registration prefixArena.{u,v}
    (type_of% (@forward_name_prefix_injective_of_eventually_periodic.{u,v})) where
  actual := positiveActual
  bridge := Iff.rfl
  variation := ⟨prefix_actual_law, positiveRejected, prefix_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨positiveRejected, ?_, rfl, prefix_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    exact ⟨(), 0, 1, by change (0 : ℕ) ≠ 1; decide⟩

/-- Vary only the cardinal bound's exponent. Prefix length, finiteness,
uniform tail, positive period and the full original telescope are retained. -/
abbrev namesArena : Arena where
  signature := sumSignature
  Law R := ∀ {X : Type u} {D : Type v}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace D] [DiscreteTopology D] [Finite D]
    (f : X → X) (q : X → D) (_hf : Continuous f) (_hq : Continuous q) (M : ℕ)
    (_hM : 0 < M) (_hcore : ∀ a ∈ stableCore f, q (f^[M] a) = q a),
    ∃ N : ℕ,
      (∀ n : ℕ, N ≤ n → ∀ x : X, q (f^[n + M] x) = q (f^[n] x)) ∧
      Function.Injective (fun w : Set.range (fun x n => q (f^[n] x)) =>
        fun i : Fin (N + M) => w.1 i) ∧
      (Set.range (fun x n => q (f^[n] x))).Finite ∧
      Nat.card (Set.range (fun x n => q (f^[n] x))) ≤ Nat.card D ^ R.readout () M N

private theorem names_rejected_law : ¬ namesArena.{u,v}.Law sumRejected := by
  intro h
  let X := ULift.{u} Bool
  let D := ULift.{v} Bool
  let : TopologicalSpace X := ⊥
  let : DiscreteTopology X := ⟨rfl⟩
  let : TopologicalSpace D := ⊥
  let : DiscreteTopology D := ⟨rfl⟩
  let q : X → D := fun x => ⟨x.down⟩
  obtain ⟨N, _, hinj, hfinite, hcard⟩ :=
    h (id : X → X) q continuous_id continuous_of_discreteTopology 1 (by decide)
      (fun _ _ => rfl)
  let := hfinite.to_subtype
  let name : X → Set.range (fun x n => q (id^[n] x)) := fun x => ⟨_, ⟨x, rfl⟩⟩
  have hname : Injective name := by
    intro x y heq
    apply ULift.ext
    exact congrArg (fun a => (a.1 0).down) heq
  have htwo := Nat.card_le_card_of_injective name hname
  have hxcard : Nat.card X = 2 := by simp [X, Nat.card_eq_fintype_card]
  change Nat.card (Set.range (fun x n => q (id^[n] x))) ≤ Nat.card D ^ 0 at hcard
  rw [hxcard] at htwo
  simp only [pow_zero] at hcard
  omega

def namesRegistration : Registration namesArena.{u,v}
    (type_of% (@finite_observation_names_of_stable_core_periodic.{u,v})) where
  actual := sumActual
  bridge := Iff.rfl
  variation := ⟨@finite_observation_names_of_stable_core_periodic.{u,v},
    sumRejected, names_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨sumRejected, ?_, rfl, names_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    exact ⟨0, 0, 1, by change (0 : ℕ) ≠ 1; decide⟩

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_observation_eventually_periodic_of_stable_core_periodic.{u,v})
    (Realization sumSignature) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Shadowing.StableCoreObservation.uniformTail
  realizationName := `Reg.D5.S1.Dynamics.Shadowing.StableCoreObservation.tailRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨tailArena.{u,v}⟩
  objectArena := .source ⟨tailArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source tailArena.{u,v} ⟨tailRegistration.{u,v}⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize sumSignature (fun _ m n => n + m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Shadowing.StableCoreObservation
    definition := none
    coordinates := #[11]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg",
        "body", "body", "body", "body", "fn", "arg", "arg",
        "fn", "arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def registration_2 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@forward_name_prefix_injective_of_eventually_periodic.{u,v})
    (Realization positiveSignature) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Shadowing.StableCoreObservation.exactPrefix
  realizationName := `Reg.D5.S1.Dynamics.Shadowing.StableCoreObservation.prefixRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨prefixArena.{u,v}⟩
  objectArena := .source ⟨prefixArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source prefixArena.{u,v} ⟨prefixRegistration.{u,v}⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize positiveSignature (fun _ _ m => m)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Shadowing.StableCoreObservation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def registration_3 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_observation_names_of_stable_core_periodic.{u,v})
    (Realization sumSignature) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Shadowing.StableCoreObservation.finiteWholeNames
  realizationName := `Reg.D5.S1.Dynamics.Shadowing.StableCoreObservation.namesRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨namesArena.{u,v}⟩
  objectArena := .source ⟨namesArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source namesArena.{u,v} ⟨namesRegistration.{u,v}⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize sumSignature (fun _ m n => n + m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Shadowing.StableCoreObservation
    definition := none
    coordinates := #[12]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "body", "arg", "arg", "arg", "arg",
        "arg"]
      stateBinder := 15
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms tailRegistration
#print axioms prefixRegistration
#print axioms namesRegistration
#print axioms registration_1
#print axioms registration_2
#print axioms registration_3

end
end Reg.D5.S1.Dynamics.Shadowing.StableCoreObservation
