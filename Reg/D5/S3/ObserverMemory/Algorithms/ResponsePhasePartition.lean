import D5.S3.ObserverMemory.Algorithms.ResponsePhasePartition
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution
open D5.S3.ObserverMemory.Algorithms.ResponsePhasePartition
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Algorithms.ResponsePhasePartition

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v

@[reducible] def signature : Signature where
  Params := Σ _A : Type u, Type v
  State p := Nat → p.1 → p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Nat → p.1 → p.2
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The observation is the entire field, including every future epoch. -/
def actual : Realization signature.{u,v} :=
  realize signature.{u,v} (fun _ _ obs => obs) (fun e => nomatch e)

/-- A whole-family intervention repeats the first two epochs forever. -/
def rejected : Realization signature.{u,v} :=
  realize signature.{u,v} (fun _ _ obs j => obs (j % 2)) (fun e => nomatch e)

@[reducible] def finiteArena : Arena where
  signature := signature.{u,v}
  Law F := ∀ {A : Type u} [Fintype A] {R : Type v} {q : Nat}
    (obs : Nat → A → R) (rank : R → Fin (q + 1))
    (_injective : Function.Injective rank)
    (_monotone : ∀ a, Monotone (fun j => rank (obs j a)))
    (N J : Nat) (_lower : N ≤ J),
    ∃ blocks : List (Nat × (A → R)),
      Partition (F.readout () ⟨A, R⟩ obs) N (J + 1) blocks ∧
      blocks.IsChain (fun left right => left.2 ≠ right.2) ∧
      blocks.length + potential rank obs N ≤ potential rank obs J + 1

@[reducible] def halfLineArena : Arena where
  signature := signature.{u,v}
  Law F := ∀ {A : Type u} [Fintype A] {R : Type v} {q : Nat}
    (obs : Nat → A → R) (rank : R → Fin (q + 1))
    (_injective : Function.Injective rank)
    (_monotone : ∀ a, Monotone (fun j => rank (obs j a))) (N : Nat),
    ∃ (initial : List (Nat × (A → R))) (s : Nat) (z : A → R),
      N ≤ s ∧ (∀ j, s ≤ j → obs j = z) ∧
      (initial ++ [(s + 1, z)]).IsChain (fun left right => left.2 ≠ right.2) ∧
      initial.length + 1 ≤ q * Fintype.card A + 1 ∧
      ∀ J, s ≤ J → Partition (F.readout () ⟨A, R⟩ obs) N (J + 1)
        (initial ++ [(J + 1, z)])

private def probeRank (x : ULift.{v} Bool) : Fin 2 := if x.down then 1 else 0
private def probeObs (j : Nat) (_a : ULift.{u} Unit) : ULift.{v} Bool :=
  ⟨if j = 0 then false else true⟩

private theorem probe_injective : Function.Injective probeRank.{v} := by
  intro ⟨x⟩ ⟨y⟩ h
  cases x <;> cases y <;> simp_all [probeRank]

private theorem probe_monotone : ∀ a, Monotone (fun j => probeRank (probeObs.{u,v} j a)) := by
  intro a i j hij
  by_cases hi : i = 0
  · subst i
    simp [probeRank, probeObs]
  · have hj : j ≠ 0 := by omega
    simp [probeRank, probeObs, hi, hj]

private theorem finite_positive : finiteArena.{u,v}.Law actual.{u,v} := by
  intro A finite R q obs rank injective monotone N J lower
  exact finite_response_partition obs rank injective monotone N J lower

private theorem finite_negative : ¬ finiteArena.{u,v}.Law rejected.{u,v} := by
  intro law
  obtain ⟨blocks, partition, _adjacent, count⟩ := @law
    (ULift.{u} Unit) inferInstance (ULift.{v} Bool) 1
    probeObs probeRank probe_injective probe_monotone 2 3 (by omega)
  have short : blocks.length ≤ 1 := by
    simpa [potential, probeObs, probeRank] using count
  cases blocks with
  | nil => exact partition.elim
  | cons first rest =>
      rcases first with ⟨b, reply⟩
      cases rest with
      | nil =>
          have hb : b = 4 := partition.2.1
          have left := congrFun (partition.2.2 2 le_rfl (by omega)) (ULift.up ())
          have right := congrFun (partition.2.2 3 (by omega) (by omega)) (ULift.up ())
          have impossible := left.trans right.symm
          simp [rejected, realize, probeObs] at impossible
      | cons next rest => simp only [List.length_cons] at short; omega

private theorem half_line_positive : halfLineArena.{u,v}.Law actual.{u,v} := by
  intro A finite R q obs rank injective monotone N
  exact half_line_response_partition obs rank injective monotone N

private theorem appended_guard {A : Type u} {R : Type v} {obs : Nat → A → R}
    {N J : Nat} {z : A → R} (initial : List (Nat × (A → R)))
    (native : Partition obs N (J + 1) (initial ++ [(J + 1, z)])) :
    Guard obs z (initial.foldl (fun _ block => block.1) N) (J + 1) := by
  induction initial generalizing N with
  | nil => exact native.2.2
  | cons first rest ih =>
      rcases first with ⟨b, reply⟩
      cases rest with
      | nil => exact native.2.2.2.2
      | cons next rest => exact ih native.2.2

private theorem half_line_negative : ¬ halfLineArena.{u,v}.Law rejected.{u,v} := by
  intro law
  obtain ⟨initial, s, z, _lower, _constant, _adjacent, _count, native⟩ := @law
    (ULift.{u} Unit) inferInstance (ULift.{v} Bool) 1
    probeObs probeRank probe_injective probe_monotone 0
  let k := max s (initial.foldl (fun _ block => block.1) 0)
  have hs : s ≤ k := le_max_left _ _
  have hb : initial.foldl (fun _ block => block.1) 0 ≤ k := le_max_right _ _
  have guard := appended_guard initial (native (2 * k + 1) (by omega))
  have left := congrFun (guard (2 * k) (by omega) (by omega)) (ULift.up ())
  have right := congrFun (guard (2 * k + 1) (by omega) (by omega)) (ULift.up ())
  have impossible := left.trans right.symm
  simp [rejected, realize, probeObs, Nat.add_mod] at impossible

private theorem dependence : ObservationalDependence signature.{u,v} actual.{u,v} := by
  intro i
  refine ⟨⟨ULift.{u} Unit, ULift.{v} Bool⟩,
    (fun _ _ => ⟨false⟩), (fun _ _ => ⟨true⟩), ?_⟩
  intro same
  have impossible := congrArg (fun field => (field 0 (ULift.up ())).down) same
  cases impossible

def finiteEvidence : Registration finiteArena.{u,v}
    (type_of%
      (@finite_response_partition.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_positive, rejected, finite_negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, finite_negative⟩,
    fun i => nomatch i⟩
  dependence := dependence

def halfLineEvidence : Registration halfLineArena.{u,v}
    (type_of%
      (@half_line_response_partition.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨half_line_positive, rejected, half_line_negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, half_line_negative⟩,
    fun i => nomatch i⟩
  dependence := dependence

def finiteRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_response_partition.{u,v})
    (type_of% (realize signature.{u,v} actual.{u,v}.readout actual.{u,v}.anchor))
    Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.ResponsePhasePartition.finite_response_partition,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.ResponsePhasePartition.finiteEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨finiteArena.{u,v}⟩, objectArena := .source ⟨finiteArena.{u,v}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source finiteArena.{u,v} ⟨finiteEvidence.{u,v}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u,v} actual.{u,v}.readout actual.{u,v}.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.ResponsePhasePartition,
    definition := none, coordinates := #[0, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body", "fn",
        "arg", "fn", "fn", "fn", "arg"],
      stateBinder := 4, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def halfLineRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@half_line_response_partition.{u,v})
    (type_of% (realize signature.{u,v} actual.{u,v}.readout actual.{u,v}.anchor))
    Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.ResponsePhasePartition.half_line_response_partition,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.ResponsePhasePartition.halfLineEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨halfLineArena.{u,v}⟩, objectArena := .source ⟨halfLineArena.{u,v}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source halfLineArena.{u,v} ⟨halfLineEvidence.{u,v}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u,v} actual.{u,v}.readout actual.{u,v}.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.ResponsePhasePartition,
    definition := none, coordinates := #[0, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "body", "arg", "body", "arg",
        "body", "arg", "arg", "arg", "arg", "body", "body",
        "fn", "fn", "fn", "arg"],
      stateBinder := 4, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms finiteEvidence
#print axioms halfLineEvidence
#print axioms finiteRegistration
#print axioms halfLineRegistration
end
end Reg.D5.S3.ObserverMemory.Algorithms.ResponsePhasePartition
