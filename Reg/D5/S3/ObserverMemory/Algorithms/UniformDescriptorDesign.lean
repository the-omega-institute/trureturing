import D5.S3.ObserverMemory.Algorithms.UniformDescriptorDesign
import Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport

open FirstOrder Language
open D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution
open D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation
open D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport
open D5.S3.ObserverMemory.Algorithms.UniformDescriptorDesign
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorDesign
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Design
@[reducible] def signature : Signature where
  Params := Σ d : Nat, (Fin d → Nat)
  State p := presburger.Formula (Fin p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ p formula => decide (formula.Realize p.2)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {S Y : Type} {letters c charts types s q : Nat} {Tsk : Task S Y letters c}
    (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (G : Skeleton s c types) (delta : Fin (blockTotal (dims P G)) → Nat)
    (hvalid : Valid P G delta) (literals : Fin G.readCount → Tsk.Literal)
    (hreal : Realizes P G delta literals),
    ((ValidFormula P G).Realize delta ↔ Valid P G delta) ∧
    ((F.readout () ⟨blockTotal (dims P G), delta⟩ (Total P M G) = true) ↔ NativeTotal G literals) ∧
    ((Shared P M G).Realize delta ↔ NativeShared G literals)

private theorem positive : arena.Law actual := by
  classical
  intro S Y letters c charts types s q Tsk P M G delta hv literals hr
  simpa [actual, realize] using design_correct P M G delta hv literals hr

private theorem negative : ¬ arena.Law rejected := by
  intro law
  let P := _root_.Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.probePresentation
  let M := _root_.Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.probeRank
  let G := _root_.Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.probeGraph
  let literals := _root_.Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.probeLiterals
  have good := _root_.Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.good
  have tot : NativeTotal G literals := by
    intro u
    refine ⟨1, 0, rfl, ?_⟩
    exact good
  have wrong := (law P M G (fun _ => 0)
    (by intro a; simp [P, Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.probePresentation,
      Formula.Realize, BoundedFormula.Realize]) literals (by intro a; trivial)).2.1.mpr tot
  cases wrong

def evidence : Registration arena (type_of% (@design_correct)) where
  actual := actual
  bridge := by
    classical
    simp [arena, actual, realize]
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩, fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    refine ⟨⟨0, Fin.elim0⟩, ⊤, ⊥, ?_⟩
    simp [actual, realize, Formula.Realize]

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@design_correct) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorDesign.design_correct,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorDesign.Design.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorDesign,
    definition := none, coordinates := #[15], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := true}]},
  continuation := .unknown, familyRecord := none, options := #[]}
#print axioms evidence
end Design

namespace Budget
@[reducible] def signature : Signature where
  Params := Unit
  State _ := presburger.Formula (Fin 0)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ _ formula => decide (formula.Realize (Fin.elim0 : Fin 0 → Nat)))
    (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {S Y : Type} {letters c charts types q : Nat} {Tsk : Task S Y letters c}
    (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q) (K : Nat),
    F.readout () () (Psi P M K) = true ↔
      ∃ s, s+1 ≤ K ∧ ∃ G : Skeleton (s+1) c types, Feasible P G

private theorem positive : arena.Law actual := by
  classical
  intro S Y letters c charts types q Tsk P M K
  simpa [actual, realize] using budget_correct P M K

private theorem negative : ¬ arena.Law rejected := by
  intro law
  let P := _root_.Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.probePresentation
  let M := _root_.Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.probeRank
  let G : Skeleton 1 2 1 := ⟨0, #v[.halt]⟩
  have feasible : Feasible P G := by
    refine ⟨(fun _ => 0), ?_, ?_, ?_⟩
    · intro a
      have zero : G.readCount = 0 := by decide
      exact Fin.elim0 (Fin.cast zero a)
    · intro u
      exact ⟨0, 0, rfl, .refl 0 0⟩
    · intro u v h J J' hh pu pv
      rfl
  have wrong := (law P M 1).mpr ⟨0, by decide, G, feasible⟩
  cases wrong

def evidence : Registration arena (type_of% (@budget_correct)) where
  actual := actual
  bridge := by
    classical
    simp [arena, actual, realize]
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩, fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    refine ⟨(), ⊤, ⊥, ?_⟩
    simp [actual, realize, Formula.Realize]

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@budget_correct) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorDesign.budget_correct,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorDesign.Budget.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorDesign,
    definition := none, coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := true}]},
  continuation := .unknown, familyRecord := none, options := #[]}
#print axioms evidence
end Budget
namespace Valid
@[reducible] def signature : Signature where
  Params := Σ d : Nat, (Fin d → Nat)
  State p := presburger.Formula (Fin p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ p formula => decide (formula.Realize p.2))
    (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {S Y : Type} {letters c charts types s : Nat} {Tsk : Task S Y letters c}
    (P : Presentation Tsk charts types) (G : Skeleton s c types)
    (delta : Fin (blockTotal (dims P G)) → Nat),
    F.readout () ⟨blockTotal (dims P G),delta⟩ (ValidFormula P G) = true ↔ Valid P G delta

private theorem positive : arena.Law actual := by
  classical
  intro S Y letters c charts types s Tsk P G delta
  simpa [actual, realize] using valid_correct P G delta

private theorem negative : ¬ arena.Law rejected := by
  intro law
  let P := _root_.Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.probePresentation
  let G : Skeleton 1 2 1 := ⟨0,#v[.halt]⟩
  have hv : Valid P G (fun _ => 0) := by intro a; exact Fin.elim0 a
  have wrong := (law P G (fun _ => 0)).mpr hv
  cases wrong

def evidence : Registration arena (type_of% (@valid_correct)) where
  actual := actual
  bridge := by
    classical
    simp [arena, actual, realize]
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩, fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    refine ⟨⟨0,Fin.elim0⟩, ⊤, ⊥, ?_⟩
    simp [actual, realize, Formula.Realize]

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@valid_correct) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorDesign.valid_correct,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorDesign.Valid.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorDesign,
    definition := none, coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := true}]},
  continuation := .unknown, familyRecord := none, options := #[]}
#print axioms evidence
end Valid
namespace Phi
@[reducible] def signature : Signature where
  Params := Unit
  State _ := presburger.Formula (Fin 0)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ _ formula => decide (formula.Realize (Fin.elim0 : Fin 0 → Nat)))
    (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {S Y : Type} {letters c charts types s q : Nat} {Tsk : Task S Y letters c}
    (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q) (G : Skeleton s c types),
    F.readout () () (Phi P M G) = true ↔
      Feasible P G

private theorem positive : arena.Law actual := by
  classical
  intro S Y letters c charts types s q Tsk P M G
  simpa [actual, realize] using phi_correct P M G

private theorem negative : ¬ arena.Law rejected := by
  intro law
  let P := _root_.Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.probePresentation
  let M := _root_.Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.probeRank
  let G : Skeleton 1 2 1 := ⟨0, #v[.halt]⟩
  have feasible : Feasible P G := by
    refine ⟨(fun _ => 0), ?_, ?_, ?_⟩
    · intro a
      have zero : G.readCount = 0 := by decide
      exact Fin.elim0 (Fin.cast zero a)
    · intro u
      exact ⟨0, 0, rfl, .refl 0 0⟩
    · intro u v h J J' hh pu pv
      rfl
  have wrong := (law P M G).mpr feasible
  cases wrong

def evidence : Registration arena (type_of% (@phi_correct)) where
  actual := actual
  bridge := by
    classical
    simp [arena, actual, realize]
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩, fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    refine ⟨(), ⊤, ⊥, ?_⟩
    simp [actual, realize, Formula.Realize]

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@phi_correct) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorDesign.phi_correct,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorDesign.Phi.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorDesign,
    definition := none, coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := true}]},
  continuation := .unknown, familyRecord := none, options := #[]}
#print axioms evidence
end Phi
end
end Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorDesign
