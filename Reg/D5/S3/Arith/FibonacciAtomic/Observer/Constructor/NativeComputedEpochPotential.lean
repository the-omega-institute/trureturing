import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeComputedEpochPotential
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeComputedEpochPotential
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeOriginalReconstructionBridge
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedFreeExtension
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeAffineImageSaturation
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeComputedEpochPotential
noncomputable section

abbrev potentialSignature : Signature where
  Params := Σ n : Nat, Σ k : Nat, Σ m : Nat, EpochInput n k m
  State q := Fin q.2.2.1 → Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev potentialActual : Realization potentialSignature :=
  realize potentialSignature (fun _ q s => Potential q.2.2.2 s) (fun e => nomatch e)

abbrev potentialRejected : Realization potentialSignature :=
  realize potentialSignature (fun _ _ _ => False) (fun e => nomatch e)

abbrev potentialArena : Arena where
  signature := potentialSignature
  Law R := ∀ {n k m : Nat} (I : EpochInput n k m),
    CycleCondition I ↔ ∃ s : Fin m → Nat, R.readout () ⟨n, k, m, I⟩ s

private theorem potential_rejected : ¬ potentialArena.Law potentialRejected := by
  intro law
  let I : EpochInput 0 0 0 := {
    base := { equations := Fin.elim0, filters := [], indices := Fin.elim0, guard := .qf .truth }
    headPower := Fin.elim0 }
  have cycles : CycleCondition I := by intro i; exact Fin.elim0 i
  obtain ⟨s, hs⟩ := (law I).mp cycles
  exact hs

def potentialEvidence : Registration potentialArena (type_of% (@cycleCondition_iff_potential)) where
  actual := potentialActual
  bridge := Iff.rfl
  variation := ⟨@cycleCondition_iff_potential, potentialRejected, potential_rejected⟩
  sensitivity := ⟨fun i => ⟨potentialRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, potential_rejected⟩,
    fun e => nomatch e⟩
  dependence := by
    intro role
    let I : EpochInput 0 0 1 := {
      base := { equations := fun _ => some (.ground (.of false)), filters := [],
        indices := Fin.elim0, guard := .qf .truth }
      headPower := fun _ => 1 }
    have good : Potential I (fun _ => 1) := by
      intro i E he
      have hE : E = .ground (.of false) := (Option.some.inj he).symm
      subst E
      exact ⟨le_rfl, trivial⟩
    have bad : ¬ Potential I (fun _ => 0) := by
      intro h
      have impossible := (h 0 (.ground (.of false)) rfl).1
      exact Nat.not_succ_le_zero 0 impossible
    refine ⟨⟨0, 0, 1, I⟩, (fun _ => 1), (fun _ => 0), ?_⟩
    intro eq
    exact bad (Eq.mp eq good)

def potentialRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cycleCondition_iff_potential) (Realization potentialSignature)
    (potentialSignature.Params → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeComputedEpochPotential.cycleCondition_iff_potential.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeComputedEpochPotential.potentialEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨potentialArena⟩
  objectArena := .source ⟨potentialArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source potentialArena ⟨potentialEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize potentialSignature (fun _ q s => Potential q.2.2.2 s)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (fun m : Nat => Fin m → Nat)
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeComputedEpochPotential
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev transportSignature : Signature where
  Params := Σ m : Nat, Fin m → Nat
  State q := Fin q.1 → CompletionTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := Fin q.1 → CompletionTree
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev transportActual : Realization transportSignature :=
  realize transportSignature (fun _ q v => imageValues q.2 v) (fun e => nomatch e)

abbrev transportRejected : Realization transportSignature :=
  realize transportSignature (fun _ q _ => imageValues q.2 (fun _ => leaf true))
    (fun e => nomatch e)

abbrev transportArena : Arena where
  signature := transportSignature
  Law R := ∀ {n k m : Nat} (I : EpochInput n k m) (hcycle : CycleCondition I),
    ∃ s : Fin m → Nat, Potential I s ∧
      ∀ (p : Fin n → Nat) (w : Fin m → CompletionTree),
        (Legal (functionalInput I s) p ∧ SourceSatisfies (functionalInput I s) p w ∧
          SourcePasses (functionalInput I s) p w) ↔
        ∃! v, OriginalAdmissible I p v ∧ R.readout () ⟨m, s⟩ v = w

private theorem transport_rejected : ¬ transportArena.Law transportRejected := by
  intro law
  let I : EpochInput 0 0 1 := {
    base := { equations := fun _ => none, filters := [], indices := Fin.elim0, guard := .qf .truth }
    headPower := fun _ => 0 }
  have cycles : CycleCondition I := (cycleCondition_iff_potential I).mpr
    ⟨fun _ => 0, by intro i E he; cases he⟩
  obtain ⟨s, hs, correspondence⟩ := law I cycles
  let p : Fin 0 → Nat := Fin.elim0
  let v : Fin 1 → CompletionTree := fun _ => leaf false
  have admissible : OriginalAdmissible I p v := by
    refine ⟨⟨rfl, fun j => Fin.elim0 j⟩, ?_, ?_⟩
    · intro i E he; cases he
    · intro E r hr; cases hr
  have original : ∃! u, OriginalAdmissible I p u ∧ imageValues s u = imageValues s v := by
    refine ⟨v, ⟨admissible, rfl⟩, ?_⟩
    intro u hu
    funext i
    exact (rho_injective.iterate (s i)) (congrFun hu.2 i)
  have lhs := (epoch_solution_correspondence I s hs p (imageValues s v)).mpr original
  obtain ⟨u, hu, _⟩ := (correspondence p (imageValues s v)).mp lhs
  have impossible := (rho_injective.iterate (s 0)) (congrFun hu.2 0)
  change leaf true = leaf false at impossible
  have tags := congrArg (fun X => (PFunctor.M.dest X).1) impossible
  cases tags

def transportEvidence : Registration transportArena (type_of% (@cycleCondition_gives_epoch_transport)) where
  actual := transportActual
  bridge := Iff.rfl
  variation := ⟨@cycleCondition_gives_epoch_transport, transportRejected, transport_rejected⟩
  sensitivity := ⟨fun i => ⟨transportRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, transport_rejected⟩,
    fun e => nomatch e⟩
  dependence := by
    intro role
    refine ⟨⟨1, fun _ => 0⟩, (fun _ => leaf true), (fun _ => leaf false), ?_⟩
    intro eq
    have tags := congrArg (fun X => (PFunctor.M.dest X).1) (congrFun eq 0)
    cases tags

def transportRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cycleCondition_gives_epoch_transport) (Realization transportSignature)
    (transportSignature.Params → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeComputedEpochPotential.cycleCondition_gives_epoch_transport.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeComputedEpochPotential.transportEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨transportArena⟩
  objectArena := .source ⟨transportArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source transportArena ⟨transportEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize transportSignature (fun _ q v => imageValues q.2 v)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (fun m : Nat => Fin m → CompletionTree)
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeComputedEpochPotential
    definition := none
    coordinates := #[2, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body", "arg", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms potentialEvidence
#print axioms transportEvidence
end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeComputedEpochPotential
