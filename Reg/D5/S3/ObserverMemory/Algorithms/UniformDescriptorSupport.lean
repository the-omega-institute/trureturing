import D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open FirstOrder Language
open D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution
open D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation
open D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

structure Inputs where
  S : Type
  Y : Type
  letters : Nat
  c : Nat
  charts : Nat
  types : Nat
  size : Nat
  q : Nat
  task : Task S Y letters c
  presentation : Presentation task charts types
  monotone : ReachedTransport task q
  graph : Skeleton size c types
  chart : Fin charts
  delta : Fin (blockTotal (dims presentation graph)) → Nat
  source : Fin (presentation.sourceDim chart) → Nat
  admitted : (presentation.adm chart).Realize source
  valid : Valid presentation graph delta
  literals : Fin graph.readCount → task.Literal
  realizes : Realizes presentation graph delta literals
  halt : Fin size
  epoch : Nat

@[reducible] def signature : Signature where
  Params := Inputs
  State p := Nat → p.task.Literal → Fin p.c
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun role p obs => if role = true then
    decide (∃ J, Run (literalProgram p.graph p.literals) obs
      p.graph.start p.task.entryEpoch p.halt J)
    else decide (Run (literalProgram p.graph p.literals) obs
      p.graph.start p.task.entryEpoch p.halt p.epoch)) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ p : Inputs,
    ((haltAt p.presentation p.monotone p.graph p.chart p.halt).Realize
      (Sum.elim (Sum.elim p.delta p.source) (fun _ => p.epoch)) ↔
      F.readout false p (p.task.observation (p.presentation.theta p.chart ⟨p.source, p.admitted⟩)) = true) ∧
    ((H p.presentation p.monotone p.graph p.chart p.halt).Realize (Sum.elim p.delta p.source) ↔
      F.readout true p (p.task.observation (p.presentation.theta p.chart ⟨p.source, p.admitted⟩)) = true)

private theorem positive : arena.Law actual := by
  classical
  intro p
  simpa [actual, realize] using native_support p.presentation p.monotone p.graph p.chart
    p.delta p.source p.admitted p.valid p.literals p.realizes p.halt p.epoch

def probeTask : Task Unit Unit 1 2 where
  registerEncoding := ⟨fun _ => [], fun _ => some (), fun _ => rfl⟩
  rowEncoding := ⟨fun _ => [], fun _ => some (), fun _ => rfl⟩
  original _ := True
  permitted _ := True
  permitted_decidable := fun _ => isTrue trivial
  update := id
  entryEpoch := 0
  reply _ _ := 0
  replies_positive := by decide
  target _ := ()
  row_eq := inferInstance
  defaultRow := ()

def probePresentation : Presentation probeTask 1 1 where
  sourceDim _ := 0
  adm _ := ⊤
  theta _ _ := ⟨(), trivial⟩
  theta_bijective := by
    constructor
    · rintro ⟨η, n, hn⟩ ⟨θ, m, hm⟩ he
      have hη : η = θ := Subsingleton.elim _ _
      subst θ
      have hnm : n = m := Subsingleton.elim _ _
      subst m
      rfl
    · intro u; exact ⟨⟨0, Fin.elim0, by simp [Formula.Realize, BoundedFormula.Realize]⟩,
        Subsingleton.elim _ _⟩
  same _ _ := ⊤
  same_exact := by intros; simp [probeTask, Formula.Realize, BoundedFormula.Realize]
  descriptorDim _ := 0
  valid _ := ⊤
  real _ _ _ := True
  chooseLiteral _ _ _ := ⟨[], trivial⟩
  choose_mem := by intros; trivial
  descriptorOf _ := ⟨0, Fin.elim0⟩
  coverage := by intro p; exact ⟨by simp [Formula.Realize, BoundedFormula.Realize], trivial⟩
  replyFormula _ _ c := if c=0 then ⊤ else ⊥
  reply_exact := by
    intro η b n j t hn ht p hp c
    by_cases hc : c=0
    · simp [hc, probeTask, Task.observation, Formula.Realize, BoundedFormula.Realize]
    · simp [hc, Ne.symm hc, probeTask, Task.observation, Formula.Realize, BoundedFormula.Realize]

def probeRank : ReachedTransport probeTask 1 where
  rank := id
  rank_strict := strictMono_id
  absent := none
  absent_zero := by intro a h; cases h
  Content _ := Unit
  content _ _ := ()
  decode _ _ := 0
  decode_content := by intros; rfl
  action _ _ w := w
  action_zero := by intros; rfl
  action_add := by intros; rfl
  persistent := by intros; trivial
  transport := by intros; rfl
  rank_transport := by intros; exact le_rfl

def probeGraph : Skeleton 2 2 1 :=
  ⟨0, #v[.read 0 (Vector.ofFn (fun c => if c=0 then 1 else 0)), .halt]⟩

def probeLiterals : Fin probeGraph.readCount → probeTask.Literal := fun _ => ⟨[], trivial⟩

@[reducible] private def probe : Inputs where
  S := Unit
  Y := Unit
  letters := 1
  c := 2
  charts := 1
  types := 1
  size := 2
  q := 1
  task := probeTask
  presentation := probePresentation
  monotone := probeRank
  graph := probeGraph
  chart := 0
  delta := fun _ => 0
  source := Fin.elim0
  admitted := by simp [probePresentation, Formula.Realize, BoundedFormula.Realize]
  valid := by intro a; simp [probePresentation, Formula.Realize, BoundedFormula.Realize]
  literals := probeLiterals
  realizes := by intro a; trivial
  halt := 1
  epoch := 0

theorem probe_instruction : literalProgram probeGraph probeLiterals 0 =
    .read (⟨[], trivial⟩ : probeTask.Literal) (fun c => if c=0 then 1 else 0) := by
  change Instruction.read (⟨[], trivial⟩ : probeTask.Literal)
    (Vector.ofFn (fun c : Fin 2 => if c=0 then (1 : Fin 2) else 0)).get = _
  apply congrArg (Instruction.read (⟨[], trivial⟩ : probeTask.Literal))
  funext c
  fin_cases c <;> rfl


theorem good : Run (literalProgram probeGraph probeLiterals)
    (fun _ _ => 0) 0 0 1 0 :=
  .read probe_instruction (.refl 1 0)

private theorem bad_invariant {x y : Fin 2} {a b : Nat}
    (path : Run (literalProgram probeGraph probeLiterals) (fun _ _ => 1) x a y b) :
    x=0 → y=0 := by
  induction path with
  | refl => exact id
  | read hop tail ih =>
      intro hx
      rw [hx, probe_instruction] at hop
      cases hop
      exact ih rfl
  | update hop tail ih =>
      intro hx
      rw [hx, probe_instruction] at hop
      cases hop

private theorem bad (J : Nat) : ¬ Run (literalProgram probeGraph probeLiterals)
    (fun _ _ => 1) 0 0 1 J := by
  intro path
  have wrong := bad_invariant path rfl
  cases wrong

private theorem probe_positive (role : Bool) :
    actual.readout role probe (fun _ _ => 0) = true := by
  classical
  cases role
  · exact decide_eq_true good
  · exact decide_eq_true ⟨0, good⟩

private theorem probe_negative (role : Bool) :
    actual.readout role probe (fun _ _ => 1) = false := by
  classical
  cases role
  · exact decide_eq_false (bad 0)
  · exact decide_eq_false (by rintro ⟨J, path⟩; exact bad J path)

def rejectedAt (i : Bool) : Realization signature :=
  realize signature (fun j p obs => if j=i then false else actual.readout j p obs)
    (fun e => nomatch e)

private theorem negative (i : Bool) : ¬ arena.Law (rejectedAt i) := by
  intro law
  have p := positive probe
  have hi := probe_positive i
  have obs : probe.task.observation
      (probe.presentation.theta probe.chart ⟨probe.source, probe.admitted⟩) = (fun _ _ => 0) := rfl
  cases i
  · have yes := p.1.mpr (by simpa only [obs] using hi)
    have no := (law probe).1.mp yes
    cases no
  · have yes := p.2.mpr (by simpa only [obs] using hi)
    have no := (law probe).2.mp yes
    cases no

def evidence : Registration arena (type_of% (@native_support)) where
  actual := actual
  bridge := by
    classical
    constructor
    · intro result p
      simpa [arena, actual, realize] using result p.presentation p.monotone p.graph p.chart
        p.delta p.source p.admitted p.valid p.literals p.realizes p.halt p.epoch
    · intro law S Y letters c charts types s q task P M G η delta n hn hv literals hr h J
      have result := law
        (⟨S, Y, letters, c, charts, types, s, q, task, P, M, G, η, delta, n, hn, hv, literals, hr, h, J⟩ : Inputs)
      simpa [actual, realize] using result
  variation := ⟨positive, rejectedAt false, negative false⟩
  sensitivity := ⟨fun i => ⟨rejectedAt i,
    (by intro j hj; simp [rejectedAt, realize, hj]), rfl, negative i⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨probe, (fun _ _ => 0), (fun _ _ => 1), ?_⟩
    rw [probe_positive, probe_negative]
    intro h
    cases h

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 1, 0, 0, 0, 0, 0}
    (@native_support)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.native_support,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport,
    definition := none, coordinates := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "fn", "fn", "fn", "arg"], booleanPredicate := true }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms evidence
#print axioms registration

namespace FormulaReadout
@[reducible] def signature : Signature where
  Params := Σ α : Type, (α → Nat)
  State p := presburger.Formula p.1
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

namespace Existentials
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {α : Type} {n : Nat} (φ : presburger.Formula (α ⊕ Fin n)) (v : α → Nat),
    F.readout () ⟨α, v⟩ (closeEx φ) = true ↔ ∃ w : Fin n → Nat, φ.Realize (Sum.elim v w)
private theorem positive : arena.Law actual := by
  classical
  intro α n φ v
  simpa [actual, realize] using realize_closeEx φ v
private theorem negative : ¬ arena.Law rejected := by
  intro law
  have wrong := (law (α := Unit) (n := 0) ⊤ (fun _ => 0)).mpr
    ⟨Fin.elim0, by simp [Formula.Realize, BoundedFormula.Realize]⟩
  cases wrong
def evidence : Registration arena (type_of% (@realize_closeEx)) where
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
    refine ⟨⟨Unit, fun _ => 0⟩, ⊤, ⊥, ?_⟩
    simp [actual, realize, Formula.Realize]
def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 1, 0, 0, 0, 0, 0}
    (@realize_closeEx) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.realize_closeEx,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.FormulaReadout.Existentials.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport,
    definition := none, coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := true}]},
  continuation := .unknown, familyRecord := none, options := #[]}
#print axioms evidence
end Existentials

namespace Universals
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {α : Type} {n : Nat} (φ : presburger.Formula (α ⊕ Fin n)) (v : α → Nat),
    F.readout () ⟨α, v⟩ (closeAll φ) = true ↔ ∀ w : Fin n → Nat, φ.Realize (Sum.elim v w)
private theorem positive : arena.Law actual := by
  classical
  intro α n φ v
  simpa [actual, realize] using realize_closeAll φ v
private theorem negative : ¬ arena.Law rejected := by
  intro law
  have wrong := (law (α := Unit) (n := 0) ⊤ (fun _ => 0)).mpr
    (by intro w; simp [Formula.Realize, BoundedFormula.Realize])
  cases wrong
def evidence : Registration arena (type_of% (@realize_closeAll)) where
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
    refine ⟨⟨Unit, fun _ => 0⟩, ⊤, ⊥, ?_⟩
    simp [actual, realize, Formula.Realize]
def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 1, 0, 0, 0, 0, 0}
    (@realize_closeAll) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.realize_closeAll,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.FormulaReadout.Universals.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport,
    definition := none, coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := true}]},
  continuation := .unknown, familyRecord := none, options := #[]}
#print axioms evidence
end Universals

namespace Conjunction
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {α β : Type} (l : List β) (f : β → presburger.Formula α) (v : α → Nat),
    F.readout () ⟨α, v⟩ (allF l f) = true ↔ ∀ b ∈ l, (f b).Realize v
private theorem positive : arena.Law actual := by
  classical
  intro α β l f v
  simpa [actual, realize] using realize_allF l f v
private theorem negative : ¬ arena.Law rejected := by
  intro law
  have wrong := (law (α := Unit) ([] : List Unit) (fun _ => ⊤) (fun _ => 0)).mpr
    (by intro b hb; cases hb)
  cases wrong
def evidence : Registration arena (type_of% (@realize_allF)) where
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
    refine ⟨⟨Unit, fun _ => 0⟩, ⊤, ⊥, ?_⟩
    simp [actual, realize, Formula.Realize]
def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 1, 0, 0, 0, 0, 0}
    (@realize_allF) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.realize_allF,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.FormulaReadout.Conjunction.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport,
    definition := none, coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := true}]},
  continuation := .unknown, familyRecord := none, options := #[]}
#print axioms evidence
end Conjunction

namespace Disjunction
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {α β : Type} (l : List β) (f : β → presburger.Formula α) (v : α → Nat),
    F.readout () ⟨α, v⟩ (anyF l f) = true ↔ ∃ b ∈ l, (f b).Realize v
private theorem positive : arena.Law actual := by
  classical
  intro α β l f v
  simpa [actual, realize] using realize_anyF l f v
private theorem negative : ¬ arena.Law rejected := by
  intro law
  have wrong := (law (α := Unit) [()] (fun _ => ⊤) (fun _ => 0)).mpr
    ⟨(), by simp, by simp [Formula.Realize, BoundedFormula.Realize]⟩
  cases wrong
def evidence : Registration arena (type_of% (@realize_anyF)) where
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
    refine ⟨⟨Unit, fun _ => 0⟩, ⊤, ⊥, ?_⟩
    simp [actual, realize, Formula.Realize]
def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 1, 0, 0, 0, 0, 0}
    (@realize_anyF) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.realize_anyF,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.FormulaReadout.Disjunction.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport,
    definition := none, coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := true}]},
  continuation := .unknown, familyRecord := none, options := #[]}
#print axioms evidence
end Disjunction
end FormulaReadout
end
end Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport

namespace Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace TupleMembership
@[reducible] def signature : Signature where
  Params := Σ α : Type, Σ n : Nat, (Fin n → α)
  State p := List (Fin p.2.1 → p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ p list => decide (p.2.2 ∈ list)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {α : Type} (values : List α) (n : Nat) (f : Fin n → α)
    (h : ∀ i, f i ∈ values), F.readout () ⟨α, n, f⟩ (enumTuple values n) = true

private theorem positive : arena.Law actual := by
  classical
  intro α values n f h
  simpa [actual, realize] using mem_enumTuple values n f h

private theorem negative : ¬ arena.Law rejected := by
  intro law
  have wrong := law ([] : List Unit) 0 Fin.elim0 (by intro i; exact Fin.elim0 i)
  cases wrong

def evidence : Registration arena (type_of% (@mem_enumTuple)) where
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
    refine ⟨⟨Unit, 0, Fin.elim0⟩, [Fin.elim0], [], ?_⟩
    simp [actual, realize]

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 1, 0, 0, 0, 0, 0}
    (@mem_enumTuple) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.mem_enumTuple,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.TupleMembership.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport,
    definition := none, coordinates := #[], readouts := #[{
      path := #["body", "body", "body"], stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := true}]},
  continuation := .unknown, familyRecord := none, options := #[]}
#print axioms evidence
end TupleMembership

namespace SkeletonMembership
@[reducible] def signature : Signature where
  Params := Σ s : Nat, Σ c : Nat, Σ b : Nat, Skeleton s c b
  State p := List (Skeleton p.1 p.2.1 p.2.2.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ p list => decide (p.2.2.2 ∈ list)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {s c b : Nat} (G : Skeleton s c b),
    F.readout () ⟨s, c, b, G⟩ (skeletonList s c b) = true

private theorem positive : arena.Law actual := by
  classical
  intro s c b G
  simpa [actual, realize] using skeletonList_complete G

private theorem negative : ¬ arena.Law rejected := by
  intro law
  have wrong := law (⟨0, #v[.halt]⟩ : Skeleton 1 1 0)
  cases wrong

def evidence : Registration arena (type_of% (@skeletonList_complete)) where
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
    let G : Skeleton 1 1 0 := ⟨0, #v[.halt]⟩
    refine ⟨⟨1, 1, 0, G⟩, [G], [], ?_⟩
    simp [actual, realize]

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@skeletonList_complete) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.skeletonList_complete,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.SkeletonMembership.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport,
    definition := none, coordinates := #[], readouts := #[{
      path := #["body", "body", "body"], stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := true}]},
  continuation := .unknown, familyRecord := none, options := #[]}
#print axioms evidence
end SkeletonMembership

namespace CandidateMembership
@[reducible] def signature : Signature where
  Params := Σ s : Nat, Σ c : Nat, Σ b : Nat, Skeleton (s+1) c b
  State p := List (Σ s, Skeleton (s+1) p.2.1 p.2.2.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ p list => decide ((⟨p.1, p.2.2.2⟩ : Σ s, Skeleton (s+1) p.2.1 p.2.2.1) ∈ list)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {s K c b : Nat} (G : Skeleton (s+1) c b) (h : s+1 ≤ K),
    F.readout () ⟨s, c, b, G⟩ (candidates K c b) = true

private theorem positive : arena.Law actual := by
  classical
  intro s K c b G h
  simpa [actual, realize] using candidates_complete G h

private theorem negative : ¬ arena.Law rejected := by
  intro law
  have wrong := law (K := 1) (⟨0, #v[.halt]⟩ : Skeleton 1 1 0) (by decide)
  cases wrong

def evidence : Registration arena (type_of% (@candidates_complete)) where
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
    let G : Skeleton 1 1 0 := ⟨0, #v[.halt]⟩
    refine ⟨⟨0, 1, 0, G⟩, [⟨0, G⟩], [], ?_⟩
    simp [actual, realize]

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@candidates_complete) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.candidates_complete,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.CandidateMembership.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport,
    definition := none, coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body"], stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := true}]},
  continuation := .unknown, familyRecord := none, options := #[]}
#print axioms evidence
end CandidateMembership

namespace HaltsMembership
@[reducible] def signature : Signature where
  Params := Σ s : Nat, Fin s
  State p := List (Fin p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ p list => decide (p.2 ∈ list)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {s c b : Nat} (G : Skeleton s c b) (h : Fin s),
    F.readout () ⟨s, h⟩ G.halts = true ↔ G.program h = .halt

private theorem positive : arena.Law actual := by
  classical
  intro s c b G h
  simpa [actual, realize] using Skeleton.mem_halts G h

private theorem negative : ¬ arena.Law rejected := by
  intro law
  have wrong := (law (⟨0, #v[.halt]⟩ : Skeleton 1 1 0) 0).mpr rfl
  cases wrong

def evidence : Registration arena (type_of% (@Skeleton.mem_halts)) where
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
    refine ⟨⟨1, 0⟩, [0], [], ?_⟩
    simp [actual, realize]

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@Skeleton.mem_halts) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.Skeleton.mem_halts,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.HaltsMembership.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport,
    definition := none, coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body"], stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := true}]},
  continuation := .unknown, familyRecord := none, options := #[]}
#print axioms evidence
end HaltsMembership


namespace Rank
@[reducible] def signature : Signature where
  Params := Σ q : Nat, Nat × Nat
  State p := Nat → Fin (p.1+1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ p f => decide (f p.2.1 ≤ f p.2.2)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {S Y : Type} {letters replies q : Nat} {T : Task S Y letters replies}
    (M : ReachedTransport T q) (u : T.Source) (p : T.Literal) ⦃j k : Nat⦄, j ≤ k →
    F.readout () ⟨q, j, k⟩ (fun n => M.rank (T.observation u n p)) = true
private theorem positive : arena.Law actual := by
  classical
  intro S Y letters replies q T M u p j k h
  simpa [actual, realize] using rank_monotone M u p h
private theorem negative : ¬ arena.Law rejected := by
  intro law
  have wrong := law
    _root_.Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport.probeRank
    ⟨(), trivial⟩ ⟨[], trivial⟩ (j := 0) (k := 0) le_rfl
  cases wrong

def evidence : Registration arena (type_of% (@rank_monotone)) where
  actual := actual
  bridge := by
    classical
    simp [arena, actual, realize, Monotone]
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩, fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    refine ⟨⟨1, 0, 1⟩, (fun _ => 0), (fun j => if j=0 then 1 else 0), ?_⟩
    simp [actual, realize]
def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@rank_monotone) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.rank_monotone,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.Rank.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport,
    definition := none, coordinates := #[7, 8, 9, 10], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := true}]},
  continuation := .unknown, familyRecord := none, options := #[]}
#print axioms evidence
end Rank

namespace Blocks
@[reducible] def signature : Signature where
  Params := Σ r : Nat, (Fin r → Nat)
  State p := (Σ a, Fin (p.2 a)) → Fin (blockTotal p.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ _ f => decide (Function.Injective f)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {r : Nat} (dims : Fin r → Nat),
    F.readout () ⟨r, dims⟩ (fun z => blockIndex dims z.1 z.2) = true
private theorem positive : arena.Law actual := by
  classical
  intro r dims
  simpa [actual, realize] using blockIndex_injective dims
private theorem negative : ¬ arena.Law rejected := by
  intro law
  have wrong := law (fun _ : Fin 0 => 0)
  cases wrong

def evidence : Registration arena (type_of% (@blockIndex_injective)) where
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
    let dims : Fin 1 → Nat := fun _ => 2
    refine ⟨⟨1, dims⟩, (fun z => blockIndex dims z.1 z.2), (fun _ => ⟨0, by decide⟩), ?_⟩
    have injective := blockIndex_injective dims
    have bad : ¬ Function.Injective (fun _ : Σ a, Fin (dims a) => (⟨0, by decide⟩ : Fin (blockTotal dims))) := by
      intro hi
      have wrong := hi (a₁ := ⟨0, 0⟩) (a₂ := ⟨0, 1⟩) rfl
      cases wrong
    change decide (Function.Injective (fun z : Σ a, Fin (dims a) => blockIndex dims z.1 z.2)) ≠
      decide (Function.Injective (fun _ : Σ a, Fin (dims a) =>
        (⟨0, by decide⟩ : Fin (blockTotal dims))))
    rw [decide_eq_true injective, decide_eq_false bad]
    intro h; cases h

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@blockIndex_injective) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.blockIndex_injective,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.Blocks.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport,
    definition := none, coordinates := #[0, 1], readouts := #[{
      path := #["body", "body", "arg"], stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := true}]},
  continuation := .unknown, familyRecord := none, options := #[]}
#print axioms evidence
end Blocks
end
end Reg.D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation
