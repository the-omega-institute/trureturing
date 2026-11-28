module
public import Lean
import all Init.Data.Iterators.Basic
import all Init.Data.Iterators.Combinators.Monadic.Take
public import OmegaChecks.InitInventory.Replay
meta import OmegaChecks.InitInventory.Replay

namespace OmegaChecks.InitBoundaries.TakeFiniteness
open Std Std.Iterators
universe u v

public abbrev RelationDecision := (α : Type u) → (r : α → α → Prop) → Decidable (WellFounded r)

-- Preserve the two independent universe parameters of the pinned equation.
set_option linter.checkUnivs false in
public abbrev FiniteDecision :=
  ∀ {α β : Type u} (m : Type u → Type v) [Monad m] [Iterator α m β] [Productive α m], Decidable (Finite α m)

/-- A constant unit monad permits every state type and both universe levels of the pinned decision. -/
private abbrev UnitM (_ : Type u) := PUnit.{v+1}

private instance : Monad (UnitM.{u,v}) where
  pure _ := .unit
  bind _ _ := .unit

/-- Only yielded successors carry edges of the input relation. Skips are impossible. -/
@[instance_reducible] private def iterator {α : Type u} (r : α → α → Prop) :
    Iterator α (UnitM.{u,v}) PUnit.{u+1} where
  IsPlausibleStep it
    | .yield next _ => r next.internalState it.internalState
    | .skip _ => False
    | .done => True
  step _ := PUnit.unit

private theorem productive {α : Type u} (r : α → α → Prop) : letI := iterator.{u,v} r; Productive α (UnitM.{u,v}) := by
  letI := iterator.{u,v} r
  exact ⟨⟨fun _ => .intro _ fun _ edge => False.elim edge⟩⟩

private theorem finiteIff {α : Type u} (r : α → α → Prop) :
    letI := iterator.{u,v} r
    Finite α (UnitM.{u,v}) ↔ WellFounded r := by
  letI := iterator.{u,v} r
  constructor
  · intro fin
    exact Subrelation.wf (r := InvImage IterM.IsPlausibleSuccessorOf (fun a : α => (⟨a⟩ : IterM (α := α) (UnitM.{u,v}) PUnit)))
      (fun {_ _} edge => IterM.isPlausibleSuccessorOf_of_yield (out := PUnit.unit) edge)
      (InvImage.wf _ fin.wf)
  · intro wf
    refine ⟨Subrelation.wf (r := InvImage r IterM.internalState) ?_ (InvImage.wf _ wf)⟩
    intro it' it step
    obtain ⟨s, dest, plausible⟩ := step
    cases s with
    | done => cases dest
    | skip next => exact False.elim plausible
    | yield next out =>
      cases dest
      exact plausible

@[instance_reducible] public def decideRelation (dec : FiniteDecision.{u,v}) : RelationDecision.{u} := fun α r =>
  letI := iterator.{u,v} r
  letI := productive.{u,v} r
  match @dec α PUnit (UnitM.{u,v}) _ _ _ with
  | .isTrue fin => .isTrue ((finiteIff.{u,v} r).mp fin)
  | .isFalse nfin => .isFalse (fun wf => nfin ((finiteIff.{u,v} r).mpr wf))

@[instance_reducible] public def decideFinite (dec : RelationDecision.{u}) : FiniteDecision.{u,v} := by
  intro α β m _ inst _
  cases dec (IterM (α := α) m β) IterM.IsPlausibleSuccessorOf with
  | isTrue wf => exact .isTrue ⟨wf⟩
  | isFalse nw => exact .isFalse (fun fin => nw fin.wf)


/-- A one-state relation with an edge exactly when `P` holds is well-founded
exactly when that edge is absent. -/
private theorem singletonWellFounded (P : Prop) :
    WellFounded (fun _ _ : PUnit.{u+1} => P) ↔ ¬P := by
  constructor
  · intro wf hp
    exact wf.induction (C := fun _ => False) PUnit.unit (fun x ih => ih x hp)
  · intro absent
    exact ⟨fun _ => .intro _ (fun _ edge => (absent edge).elim)⟩

/-- Even the finiteness decisions on productive, one-state iterators decide the
negation of every proposition, at the independent universes of the pinned equation. -/
public def decideNegation (dec : FiniteDecision.{u,v}) (P : Prop) : Decidable (¬P) :=
  match decideRelation @dec PUnit.{u+1} (fun _ _ => P) with
  | .isTrue wf => .isTrue ((singletonWellFounded P).mp wf)
  | .isFalse no => .isFalse (fun absent => no ((singletonWellFounded P).mpr absent))

public theorem weakExcludedMiddle (dec : FiniteDecision.{u,v}) (P : Prop) : ¬P ∨ ¬¬P :=
  match decideNegation @dec P with
  | .isTrue absent => .inl absent
  | .isFalse possible => .inr possible


open Lean Meta Elab.Command in
run_cmd
  let env ← getEnv
  let owner := `Init.Data.Iterators.Combinators.Monadic.Take
  let some idx := env.getModuleIdx? owner | throwError "missing Take module"
  let some equation := env.header.moduleData[idx]!.constants.find? (·.name == `Std.Iterators.Types.Take.Rel.eq_1)
    | throwError "missing Take relation equation in its defining module"
  let [u, v] := equation.levelParams | throwError "unexpected Take equation universes"
  let levels := [Level.param u, Level.param v]
  liftTermElabM do
    forallTelescope (equation.type.instantiateLevelParams equation.levelParams levels) fun xs conclusion => do
      let some (_, _, branches) := conclusion.eq? | throwError "missing Take relation equation"
      unless branches.isAppOfArity ``dite 5 do throwError "missing Take finiteness branches"
      let dec := branches.getAppArgs[2]!
      unless dec.isAppOfArity ``Classical.propDecidable 1 do throwError "unexpected Take finiteness decision"
      let actual ← mkForallFVars xs (← inferType dec)
      unless Kernel.isDefEqGuarded env {} actual (mkConst ``FiniteDecision levels) do
        throwError "Take finiteness decision differs from the bidirectional reduction"
  let official ← importModules #[{module := `Lean}] {} (level := .private)
  discard <| replayBoundaryDependencies official env [``decideRelation, ``decideFinite, ``weakExcludedMiddle]

end OmegaChecks.InitBoundaries.TakeFiniteness
