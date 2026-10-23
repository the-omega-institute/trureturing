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

/-- Observe the tail cutoff while retaining all source and core hypotheses. -/
abbrev tailSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def tailActual : Realization tailSignature :=
  realize tailSignature (fun _ _ N => N) (fun e => nomatch e)

def tailRejected : Realization tailSignature :=
  realize tailSignature (fun _ _ _ => 0) (fun e => nomatch e)

def tailArena : Arena where
  signature := tailSignature
  Law R := ∀ {X : Type u} {D : Type v}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace D] [DiscreteTopology D]
    (f : X → X) (q : X → D) (_hf : Continuous f) (_hq : Continuous q)
    (M : ℕ)
    (_hcore : ∀ a ∈ (⋂ n : ℕ, Set.range (f^[n])), q (f^[M] a) = q a),
    ∃ N : ℕ, ∀ n : ℕ, R.readout () () N ≤ n → ∀ x : X,
      q (f^[n + M] x) = q (f^[n] x)

/-- A two-point transient maps to its fixed stable core in one step.
Forcing the cutoff to zero loses the time-zero observation. -/
private theorem tailRejected_law : ¬ tailArena.{u,v}.Law tailRejected := by
  intro h
  let X := ULift.{u} Bool
  let D := ULift.{v} Bool
  let f : X → X := fun _ => ⟨false⟩
  let q : X → D := fun x => ⟨x.down⟩
  have hcore : ∀ a ∈ (⋂ n : ℕ, Set.range (f^[n])), q (f^[1] a) = q a := by
    intro a ha
    obtain ⟨b, hb⟩ := Set.mem_iInter.mp ha 1
    have haFalse : a = (⟨false⟩ : X) := by simpa [f] using hb.symm
    simp [haFalse, f]
  obtain ⟨N, ht⟩ := h f q (continuous_of_discreteTopology : Continuous f)
    (continuous_of_discreteTopology : Continuous q) 1 hcore
  have hh := ht 0 (by change (0 : ℕ) ≤ 0; decide) (⟨true⟩ : X)
  have hb := congrArg ULift.down hh
  simp [f, q] at hb

def tailRegistration : Registration tailArena.{u,v}
    (type_of% (@finite_observation_eventually_periodic_of_stable_core_periodic.{u,v})) where
  actual := tailActual
  bridge := Iff.rfl
  variation := ⟨@finite_observation_eventually_periodic_of_stable_core_periodic.{u,v},
    tailRejected, tailRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨tailRejected, ?_, rfl, tailRejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    exact ⟨(), (0 : ℕ), (1 : ℕ), by change (0 : ℕ) ≠ 1; decide⟩

/-- Observe the prefix length N+M, with M as its exact source coordinate. -/
abbrev prefixSignature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def prefixActual : Realization prefixSignature :=
  realize prefixSignature (fun _ M N => N + M) (fun e => nomatch e)

def prefixRejected : Realization prefixSignature :=
  realize prefixSignature (fun _ _ _ => 0) (fun e => nomatch e)

def prefixArena : Arena where
  signature := prefixSignature
  Law R := ∀ {X : Type u} {D : Type v}
    (f : X → X) (q : X → D) (N M : ℕ) (_hM : 0 < M)
    (_htail : ∀ n : ℕ, N ≤ n → ∀ x : X,
      q (f^[n + M] x) = q (f^[n] x)),
    Set.InjOn (fun w : ℕ → D => fun k : Fin (R.readout () M N) => w k)
      (Set.range (fun x n => q (f^[n] x)))

/-- The two distinct constant names of an identity system coincide on Fin 0. -/
private theorem prefixRejected_law : ¬ prefixArena.{u,v}.Law prefixRejected := by
  intro h
  let X := ULift.{u} Bool
  let D := ULift.{v} Bool
  let f : X → X := id
  let q : X → D := fun x => ⟨x.down⟩
  have htail : ∀ n : ℕ, 0 ≤ n → ∀ x : X,
      q (f^[n + 1] x) = q (f^[n] x) := by
    intro n hn x
    simp [f]
  have hinj := h f q 0 1 (by decide) htail
  have hh := hinj
    (show (fun n => q (f^[n] (⟨false⟩ : X))) ∈
      Set.range (fun x n => q (f^[n] x)) from ⟨⟨false⟩, rfl⟩)
    (show (fun n => q (f^[n] (⟨true⟩ : X))) ∈
      Set.range (fun x n => q (f^[n] x)) from ⟨⟨true⟩, rfl⟩)
    (by funext k; exact Fin.elim0 k)
  have hb := congrArg ULift.down (congrFun hh 0)
  simp [f, q] at hb

def prefixRegistration : Registration prefixArena.{u,v}
    (type_of% (@finite_observation_name_injective_of_eventually_periodic.{u,v})) where
  actual := prefixActual
  bridge := Iff.rfl
  variation := ⟨@finite_observation_name_injective_of_eventually_periodic.{u,v},
    prefixRejected, prefixRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨prefixRejected, ?_, rfl, prefixRejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    exact ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by change (0 + 1 : ℕ) ≠ 1 + 1; decide⟩

/-- Observe finiteness of the exact name set, for arbitrary alphabet universes. -/
abbrev rangeSignature : Signature where
  Params := Type v
  State D := Set (ℕ → D)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

open Classical in
def rangeActual : Realization rangeSignature.{v} :=
  realize rangeSignature (fun _ _ S => decide S.Finite) (fun e => nomatch e)

def rangeRejected : Realization rangeSignature.{v} :=
  realize rangeSignature (fun _ _ _ => false) (fun e => nomatch e)

def rangeArena : Arena where
  signature := rangeSignature.{v}
  Law R := ∀ {X : Type u} {D : Type v}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace D] [DiscreteTopology D] [Finite D]
    (f : X → X) (q : X → D) (_hf : Continuous f) (_hq : Continuous q)
    (M : ℕ) (_hM : 0 < M)
    (_hcore : ∀ a ∈ (⋂ n : ℕ, Set.range (f^[n])), q (f^[M] a) = q a),
    R.readout () D (Set.range (fun x n => q (f^[n] x))) = true

private theorem rangeActual_law : rangeArena.{u,v}.Law rangeActual := by
  classical
  intro X D _ _ _ _ _ _ f q hf hq M hM hcore
  change decide (Set.range (fun x n => q (f^[n] x))).Finite = true
  exact decide_eq_true (finite_observation_range_finite_of_stable_core_periodic
    f q hf hq M hM hcore)

private theorem rangeRejected_law : ¬ rangeArena.{u,v}.Law rangeRejected := by
  intro h
  let X := ULift.{u} Unit
  let D := ULift.{v} Unit
  let f : X → X := id
  let q : X → D := fun _ => ⟨()⟩
  have hh := h f q continuous_id continuous_const 1 (by decide) (by
    intro a ha; simp [f, q])
  change (false : Bool) = true at hh
  exact Bool.false_ne_true hh

open Classical in
def rangeRegistration : Registration rangeArena.{u,v}
    (type_of% (@finite_observation_range_finite_of_stable_core_periodic.{u,v})) where
  actual := rangeActual
  bridge := by simp only [rangeArena, rangeActual, realize, decide_eq_true_eq]
  variation := ⟨rangeActual_law, rangeRejected, rangeRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rangeRejected, ?_, rfl, rangeRejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    let D := ULift.{v} Bool
    let spike : ℕ → (ℕ → D) := fun n k => ⟨decide (k = n)⟩
    have hspike : Injective spike := by
      intro m n hmn
      have hh := congrArg ULift.down (congrFun hmn m)
      by_contra hne
      simp [spike, hne] at hh
    have : Infinite (ℕ → D) := Infinite.of_injective spike hspike
    refine ⟨D, (∅ : Set (ℕ → D)), (Set.univ : Set (ℕ → D)), ?_⟩
    change decide (∅ : Set (ℕ → D)).Finite ≠ decide (Set.univ : Set (ℕ → D)).Finite
    simp [Set.infinite_univ]

/-- These faithful four-slot attempts include explicit source selections.
Only the current report can certify source reconstruction; no validation status
is asserted by these declarations themselves. Unfinished admission is covered
by https://github.com/the-omega-institute/trureturing/issues/5214. -/
def tailAttempt : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_observation_eventually_periodic_of_stable_core_periodic.{u,v})
    (Realization tailSignature) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Shadowing.StableCoreObservation.tail
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
  readout := some (realize tailSignature (fun _ _ N => N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Shadowing.StableCoreObservation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body",
        "body","body","body","body","arg","body","body","domain","fn","arg"]
      stateBinder := 13
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def prefixAttempt : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_observation_name_injective_of_eventually_periodic.{u,v})
    (Realization prefixSignature) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Shadowing.StableCoreObservation.prefix
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
  readout := some (realize prefixSignature (fun _ M N => N + M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Shadowing.StableCoreObservation
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body",
        "fn","arg","body","domain","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

open Classical in
def rangeAttempt : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_observation_range_finite_of_stable_core_periodic.{u,v})
    (Realization rangeSignature.{v}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Shadowing.StableCoreObservation.range
  realizationName := `Reg.D5.S1.Dynamics.Shadowing.StableCoreObservation.rangeRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨rangeArena.{u,v}⟩
  objectArena := .source ⟨rangeArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rangeArena.{u,v} ⟨rangeRegistration.{u,v}⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize rangeSignature (fun _ _ S => decide S.Finite) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Shadowing.StableCoreObservation
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body",
        "body","body","body","body","body","body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms tailRegistration
#print axioms prefixRegistration
#print axioms rangeRegistration
#print axioms tailAttempt
#print axioms prefixAttempt
#print axioms rangeAttempt

end
end Reg.D5.S1.Dynamics.Shadowing.StableCoreObservation
