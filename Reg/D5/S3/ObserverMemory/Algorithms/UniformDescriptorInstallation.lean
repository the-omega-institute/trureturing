import D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation
import Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport

open FirstOrder Language
open D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution
open D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation
open D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport
open D5.S3.ObserverMemory.Algorithms.UniformDescriptorDesign
open D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

private def P := _root_.Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.probePresentation
private def M := _root_.Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.probeRank
private def G : Skeleton 1 2 1 := ⟨0, #v[.halt]⟩
private theorem feasible : Feasible P G := by
  refine ⟨fun _ => 0, ?_, ?_, ?_⟩
  · intro a; exact Fin.elim0 a
  · intro u; exact ⟨0,0,rfl,.refl _ _⟩
  · intro u v h J J' hh pu pv; rfl

structure TaskInputs where
  S : Type
  Y : Type
  letters : Nat
  c : Nat
  task : Task S Y letters c

namespace Correct
@[reducible] def signature : Signature where
  Params := TaskInputs
  State p := InstalledTable p.task
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ _ table => decide table.Successful) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {S Y : Type} {letters c charts types s q : Nat} {Tsk : Task S Y letters c}
    (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (G : Skeleton (s+1) c types) (table : InstalledTable Tsk)
    (hi : installCandidate P M G = some table),
    ∃ delta, ∃ hv : Valid P G delta, table = materialize P M G delta hv ∧
      F.readout () ⟨S,Y,letters,c,Tsk⟩ table = true ∧ EndpointCorrect table

private theorem positive : arena.Law actual := by
  classical
  intro S Y letters c charts types s q Tsk P M G table hi
  simpa [actual,realize] using install_candidate_correct P M G table hi
private theorem negative : ¬ arena.Law rejected := by
  intro law
  obtain ⟨table,hi⟩ := (install_candidate_exists_iff P M G).mpr feasible
  obtain ⟨delta,hv,he,bad,endpoint⟩ := law P M G table hi
  cases bad

def goodTable : InstalledTable _root_.Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.probeTask :=
  ⟨1,by decide,0,#v[.halt ()]⟩
def badTable : InstalledTable _root_.Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.probeTask :=
  ⟨1,by decide,0,#v[.update 0]⟩
private theorem good : goodTable.Successful := by
  intro u
  change ∃ h J row, _
  refine ⟨(0 : Fin 1),0,(),rfl,rfl,?_⟩
  exact .refl _ _
private theorem bad : ¬ badTable.Successful := by
  intro hs
  obtain ⟨h,J,row,he,hr,path⟩ := hs ⟨(),trivial⟩
  have hz : h = (0 : Fin 1) := Fin.eq_zero h
  subst h
  cases he

def evidence : Registration arena (type_of% (@install_candidate_correct)) where
  actual := actual
  bridge := by
    classical
    simp [arena,actual,realize]
  variation := ⟨positive,rejected,negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,negative⟩,fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    refine ⟨⟨Unit,Unit,1,2,_root_.Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.probeTask⟩,
      goodTable,badTable,?_⟩
    simp [actual,realize,good,bad]

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 1, 0, 0, 0, 0, 0}
    (@install_candidate_correct) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation.install_candidate_correct,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation.Correct.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := {stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation,
    definition := none, coordinates := #[12], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := true}]},
  continuation := .unknown, familyRecord := none, options := #[]}
#print axioms evidence
end Correct

namespace Exists
@[reducible] def signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ _ proposition => decide proposition) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {S Y : Type} {letters c charts types s q : Nat} {Tsk : Task S Y letters c}
    (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (G : Skeleton (s+1) c types), (∃ table, installCandidate P M G = some table) ↔ F.readout () () (Feasible P G) = true
private theorem positive : arena.Law actual := by
  classical
  intro S Y letters c charts types s q Tsk P M G
  simpa [actual,realize] using install_candidate_exists_iff P M G
private theorem negative : ¬ arena.Law rejected := by
  intro law
  have hi := (install_candidate_exists_iff P M G).mpr feasible
  have wrong := (law P M G).mp hi
  cases wrong

def evidence : Registration arena (type_of% (@install_candidate_exists_iff)) where
  actual := actual
  bridge := by
    classical
    simp [arena,actual,realize]
  variation := ⟨positive,rejected,negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,negative⟩,fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    refine ⟨(),True,False,?_⟩
    simp [actual,realize]

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@install_candidate_exists_iff) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation.install_candidate_exists_iff,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation.Exists.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := {stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation,
    definition := none, coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := true}]},
  continuation := .unknown, familyRecord := none, options := #[]}
#print axioms evidence
end Exists

namespace None
@[reducible] def signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ _ proposition => decide proposition) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {S Y : Type} {letters c charts types s q : Nat} {Tsk : Task S Y letters c}
    (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (G : Skeleton (s+1) c types), installCandidate P M G = none ↔ F.readout () () (Feasible P G) = false
private theorem positive : arena.Law actual := by
  classical
  intro S Y letters c charts types s q Tsk P M G
  simpa [actual,realize] using install_candidate_none_iff P M G
private theorem negative : ¬ arena.Law rejected := by
  intro law
  have hi := (law P M G).mpr rfl
  exact (install_candidate_none_iff P M G).mp hi feasible

def evidence : Registration arena (type_of% (@install_candidate_none_iff)) where
  actual := actual
  bridge := by
    classical
    simp [arena,actual,realize]
  variation := ⟨positive,rejected,negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,negative⟩,fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    refine ⟨(),True,False,?_⟩
    simp [actual,realize]

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@install_candidate_none_iff) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation.install_candidate_none_iff,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation.None.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := {stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation,
    definition := none, coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"], stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := true}]},
  continuation := .unknown, familyRecord := none, options := #[]}
#print axioms evidence
end None
namespace Necessity
@[reducible] def signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ _ proposition => decide proposition) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := F.readout () () (type_of% (@successful_feasible)) = true

private theorem positive : arena.Law actual := by
  classical
  simpa only [arena,actual,realize,decide_eq_true_eq] using (@successful_feasible)
private theorem negative : ¬ arena.Law rejected := by
  simp only [arena,rejected,realize,Bool.false_eq_true,not_false_eq_true]

def evidence : Registration arena (type_of% (@successful_feasible)) where
  actual := actual
  bridge := by
    classical
    simp only [arena,actual,realize,decide_eq_true_eq]
  variation := ⟨positive,rejected,negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,negative⟩,fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    refine ⟨(),True,False,?_⟩
    simp [actual,realize]

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@successful_feasible) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation.successful_feasible,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation.Necessity.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := {stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation,
    definition := none, coordinates := #[], readouts := #[{
      path := #[], stateBinder := 0, functionOperand := false,
      stateOperand := none, booleanPredicate := true}]},
  continuation := .unknown, familyRecord := none, options := #[]}
#print axioms evidence
end Necessity

namespace Budget
@[reducible] def signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ _ proposition => decide proposition) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := F.readout () () (type_of% (@successful_budget)) = true

private theorem positive : arena.Law actual := by
  classical
  simpa only [arena,actual,realize,decide_eq_true_eq] using (@successful_budget)
private theorem negative : ¬ arena.Law rejected := by
  simp only [arena,rejected,realize,Bool.false_eq_true,not_false_eq_true]

def evidence : Registration arena (type_of% (@successful_budget)) where
  actual := actual
  bridge := by
    classical
    simp only [arena,actual,realize,decide_eq_true_eq]
  variation := ⟨positive,rejected,negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,negative⟩,fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    refine ⟨(),True,False,?_⟩
    simp [actual,realize]

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@successful_budget) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation.successful_budget,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation.Budget.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := {stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation,
    definition := none, coordinates := #[], readouts := #[{
      path := #[], stateBinder := 0, functionOperand := false,
      stateOperand := none, booleanPredicate := true}]},
  continuation := .unknown, familyRecord := none, options := #[]}
#print axioms evidence
end Budget

namespace Sound
@[reducible] def signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ _ proposition => decide proposition) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := F.readout () () (type_of% (@synthesize_sound)) = true

private theorem positive : arena.Law actual := by
  classical
  simpa only [arena,actual,realize,decide_eq_true_eq] using (@synthesize_sound)
private theorem negative : ¬ arena.Law rejected := by
  simp only [arena,rejected,realize,Bool.false_eq_true,not_false_eq_true]

def evidence : Registration arena (type_of% (@synthesize_sound)) where
  actual := actual
  bridge := by
    classical
    simp only [arena,actual,realize,decide_eq_true_eq]
  variation := ⟨positive,rejected,negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,negative⟩,fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    refine ⟨(),True,False,?_⟩
    simp [actual,realize]

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@synthesize_sound) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation.synthesize_sound,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation.Sound.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := {stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation,
    definition := none, coordinates := #[], readouts := #[{
      path := #[], stateBinder := 0, functionOperand := false,
      stateOperand := none, booleanPredicate := true}]},
  continuation := .unknown, familyRecord := none, options := #[]}
#print axioms evidence
end Sound

namespace Rejection
@[reducible] def signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ _ proposition => decide proposition) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := F.readout () () (type_of% (@synthesize_none_iff)) = true

private theorem positive : arena.Law actual := by
  classical
  simpa only [arena,actual,realize,decide_eq_true_eq] using (@synthesize_none_iff)
private theorem negative : ¬ arena.Law rejected := by
  simp only [arena,rejected,realize,Bool.false_eq_true,not_false_eq_true]

def evidence : Registration arena (type_of% (@synthesize_none_iff)) where
  actual := actual
  bridge := by
    classical
    simp only [arena,actual,realize,decide_eq_true_eq]
  variation := ⟨positive,rejected,negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,negative⟩,fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    refine ⟨(),True,False,?_⟩
    simp [actual,realize]

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@synthesize_none_iff) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation.synthesize_none_iff,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation.Rejection.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := {stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation,
    definition := none, coordinates := #[], readouts := #[{
      path := #[], stateBinder := 0, functionOperand := false,
      stateOperand := none, booleanPredicate := true}]},
  continuation := .unknown, familyRecord := none, options := #[]}
#print axioms evidence
end Rejection

namespace Runs
@[reducible] def signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ _ proposition => decide proposition) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := F.readout () () (type_of% (@corresponding_run)) = true

private theorem positive : arena.Law actual := by
  classical
  simpa only [arena,actual,realize,decide_eq_true_eq] using (@corresponding_run)
private theorem negative : ¬ arena.Law rejected := by
  simp only [arena,rejected,realize,Bool.false_eq_true,not_false_eq_true]

def evidence : Registration arena (type_of% (@corresponding_run)) where
  actual := actual
  bridge := by
    classical
    simp only [arena,actual,realize,decide_eq_true_eq]
  variation := ⟨positive,rejected,negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,negative⟩,fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    refine ⟨(),True,False,?_⟩
    simp [actual,realize]

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@corresponding_run) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation.corresponding_run,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation.Runs.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := {stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation,
    definition := none, coordinates := #[], readouts := #[{
      path := #[], stateBinder := 0, functionOperand := false,
      stateOperand := none, booleanPredicate := true}]},
  continuation := .unknown, familyRecord := none, options := #[]}
#print axioms evidence
end Runs

namespace Transfer
@[reducible] def signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ _ proposition => decide proposition) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := F.readout () () (type_of% (@corresponding_successful)) = true

private theorem positive : arena.Law actual := by
  classical
  simpa only [arena,actual,realize,decide_eq_true_eq] using (@corresponding_successful)
private theorem negative : ¬ arena.Law rejected := by
  simp only [arena,rejected,realize,Bool.false_eq_true,not_false_eq_true]

def evidence : Registration arena (type_of% (@corresponding_successful)) where
  actual := actual
  bridge := by
    classical
    simp only [arena,actual,realize,decide_eq_true_eq]
  variation := ⟨positive,rejected,negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,negative⟩,fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    refine ⟨(),True,False,?_⟩
    simp [actual,realize]

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@corresponding_successful) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation.corresponding_successful,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation.Transfer.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := {stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation,
    definition := none, coordinates := #[], readouts := #[{
      path := #[], stateBinder := 0, functionOperand := false,
      stateOperand := none, booleanPredicate := true}]},
  continuation := .unknown, familyRecord := none, options := #[]}
#print axioms evidence
end Transfer

namespace CorrespondenceBudget
@[reducible] def signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ _ proposition => decide proposition) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := F.readout () () (type_of% (@corresponding_budget)) = true

private theorem positive : arena.Law actual := by
  classical
  simpa only [arena,actual,realize,decide_eq_true_eq] using (@corresponding_budget)
private theorem negative : ¬ arena.Law rejected := by
  simp only [arena,rejected,realize,Bool.false_eq_true,not_false_eq_true]

def evidence : Registration arena (type_of% (@corresponding_budget)) where
  actual := actual
  bridge := by
    classical
    simp only [arena,actual,realize,decide_eq_true_eq]
  variation := ⟨positive,rejected,negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,negative⟩,fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    refine ⟨(),True,False,?_⟩
    simp [actual,realize]

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@corresponding_budget) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation.corresponding_budget,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation.CorrespondenceBudget.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := {stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation,
    definition := none, coordinates := #[], readouts := #[{
      path := #[], stateBinder := 0, functionOperand := false,
      stateOperand := none, booleanPredicate := true}]},
  continuation := .unknown, familyRecord := none, options := #[]}
#print axioms evidence
end CorrespondenceBudget

end
end Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation
