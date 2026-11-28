module
import all OmegaChecks.InitInventory.TransformerLaws
public import Init.Data.Range.Polymorphic.RangeIterator
import all Init.Data.Range.Polymorphic.RangeIterator
import all Init.Data.Iterators.Consumers.Monadic.Loop
/-! The optimized range loops ignore the supplied lift. The default loop uses that lift
at each step. Two successive outputs can observe which of two equal reader representatives
the lift returns, with the reader at the first output selecting the second callback. -/

public section
open Std Std.Iterators Std.PRange
namespace OmegaChecks.InitBoundaries.RangeLoopLift
open TransformerLaws.MapAfterBind
universe u v

private def first {T A : Type u} (x : Paired T A) := diagonal x.val.1
private theorem firstEq {T A : Type u} (x : Paired T A) : first x = x := by
  obtain ⟨_, rfl⟩ := diagonalExists x
  rfl
private def idLift (T : Type u) := fun (A B : Type u) (k : A → Paired T B) (a : Id A) => k a
private def firstLift (T : Type u) := fun (A B : Type u) (k : A → Paired T B) (a : Id A) => first (k a)
private theorem idLaw (T : Type u) : letI := monad T; Internal.LawfulMonadLiftBindFunction (idLift T) :=
  letI := monad T
  ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
private theorem firstLaw (T : Type u) : letI := monad T; Internal.LawfulMonadLiftBindFunction (firstLift T) := by
  letI := monad T
  constructor
  · exact fun _ _ => firstEq _
  · intros; rfl

private def next (T : Type u) (f g : T → T) (h : ∀ t, f t = g t)
    (start : Bool) (c : Option T) : Paired T {_s : ForInStep (Option T) // True} :=
  if start then diagonal (fun t => ⟨.yield (some t), trivial⟩)
  else match c with
  | none => diagonal (fun _ => ⟨.done none, trivial⟩)
  | some t => ⟨(fun _ => ⟨.done (some (f t)), trivial⟩, fun _ => ⟨.done (some (g t)), trivial⟩),
    congrArg (fun y (_ : T) => (⟨ForInStep.done (some y), trivial⟩ : {_s : ForInStep (Option T) // True})) (h t)⟩

private abbrev Lift (T : Type u) := ∀ (A B : Type u), (A → Paired T B) → Id A → Paired T B

private def twoSteps {T : Type u} (s : Bool → Option T → Paired T {_s : ForInStep (Option T) // True})
    (lift : Lift T) : Paired T (Option T) :=
  letI := monad T
  lift PUnit _ (fun _ => do
    match (← s true none).val with
    | .done z => return z
    | .yield z => lift PUnit _ (fun _ => do
        match (← s false z).val with
        | .done a => return a
        | .yield a => return a) PUnit.unit) PUnit.unit

private theorem extOfTwoSteps {T : Type u} {f g : T → T} (h : ∀ t, f t = g t)
    (e : twoSteps (next T f g h) (idLift T) = twoSteps (next T f g h) (firstLift T)) : f = g := by
  exact (congrArg (fun (x : Paired T (Option T)) t => (x.val.1 t).getD t) e).symm

/-- Equality of the two lawful ways to run the two-step reader test forces function extensionality. -/
def TwoStepsAgree.{w} : Prop := ∀ (T : Type w) (f g : T → T) (h : ∀ t, f t = g t),
  twoSteps (next T f g h) (idLift T) = twoSteps (next T f g h) (firstLift T)

theorem funextFromTwoSteps (agree : TwoStepsAgree.{max 1 u v}) : type_of% (@funext.{u,v}) := by
  apply funextFromEndomorphisms
  intro T f g h
  exact extOfTwoSteps h (agree T f g h)

private abbrev N := ULift.{u} Nat
private instance : UpwardEnumerable N where
  succ? k := some ⟨k.down+1⟩
  succMany? j k := some ⟨k.down+j⟩
private instance : LawfulUpwardEnumerable N where
  succMany?_zero a := rfl
  succMany?_add_one n a := rfl
  ne_of_lt a b := by
    rintro ⟨k, eq⟩ rfl
    have h := congrArg ULift.down (Option.some.inj eq)
    exact Nat.ne_of_gt (Nat.lt_add_of_pos_right (Nat.zero_lt_succ k)) h
private instance : LT N := ⟨fun a b => Nat.lt a.down b.down⟩
private instance : DecidableLT N := fun a b => Nat.decLt a.down b.down
private instance : LawfulUpwardEnumerableLT N where
  lt_iff a b := by
    constructor
    · intro h
      refine ⟨b.down - (a.down+1), ?_⟩
      apply congrArg some
      apply ULift.ext
      change a.down + (b.down - (a.down+1) + 1) = b.down
      change a.down+1 ≤ b.down at h
      exact (Nat.succ_add _ _).symm.trans (Nat.add_sub_cancel' h)
    · rintro ⟨j, h⟩
      have eq := congrArg ULift.down (Option.some.inj h)
      change a.down + (j+1) = b.down at eq
      change Nat.lt a.down b.down
      rw [← eq]
      exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)

private instance : Rxo.IsAlwaysFinite N where
  finite a b := by
    refine ⟨b.down, ?_⟩
    change ¬Nat.lt (a.down + b.down) b.down
    exact Nat.not_lt.mpr (Nat.le_add_left ..)

private def isStart (k : N) : Bool := k.down == 0

private def stage (k : Nat) : IterM (α := Rxo.Iterator N.{u}) Id N := ⟨⟨some ⟨k⟩, ⟨2⟩⟩⟩

private theorem openStepZero : Shrink.inflate (stage.{u} 0).step =
    ⟨.yield (stage 1) ⟨0⟩, rfl⟩ := Shrink.inflate_deflate
private theorem openStepOne : Shrink.inflate (stage.{u} 1).step =
    ⟨.yield (stage 2) ⟨1⟩, rfl⟩ := Shrink.inflate_deflate

private abbrev Action (T : Type u) := Bool → Option T → Paired T {_s : ForInStep (Option T) // True}

private def runDefault {σ : Type u} [Iterator σ Id N] [Finite σ Id] (T : Type u) (it : IterM (α := σ) Id N)
    (s : Action T) (lift : Lift T) : Paired T (Option T) := by
  letI := monad T
  exact IterM.DefaultConsumers.forIn'.wf lift (Option T) (fun _ _ _ => True)
    (IteratorLoop.wellFounded_of_finite (α := σ) (m := Id)) it none
    it.IsPlausibleIndirectOutput (fun _ h => h) (fun k _ c => s (isStart k) c)

private def runOptimized {σ : Type u} [Iterator σ Id N] (T : Type u)
    (inst : letI := monad T; IteratorLoop σ Id (Paired T))
    (it : IterM (α := σ) Id N) (s : Action T) (lift : Lift T) : Paired T (Option T) := by
  letI := monad T
  letI := inst
  exact IteratorLoop.forIn lift (Option T) (fun _ _ _ => True) it none (fun k _ c => s (isStart k) c)

private theorem defaultEq {σ : Type u} [Iterator σ Id N] [Finite σ Id] (T : Type u)
    (inst : letI := monad T; IteratorLoop σ Id (Paired T))
    (laws : letI := monad T; letI := inst; LawfulIteratorLoop σ Id (Paired T))
    (it : IterM (α := σ) Id N) (s : Action T)
    (ignores : runOptimized T inst it s (idLift T) = runOptimized T inst it s (firstLift T)) :
    runDefault T it s (idLift T) = runDefault T it s (firstLift T) := by
  letI := monad T
  letI := lawful T
  letI := inst
  letI := idLaw T
  letI := firstLaw T
  let pl := fun (_ : N) (_ : Option T) (_ : ForInStep (Option T)) => True
  let wf : IteratorLoop.WellFounded σ Id pl := IteratorLoop.wellFounded_of_finite
  let f := fun k (_ : it.IsPlausibleIndirectOutput k) c => s (isStart k) c
  have hA := laws.lawful (idLift T) (Option T) it none pl wf f
  have hB := laws.lawful (firstLift T) (Option T) it none pl wf f
  change _ = IterM.DefaultConsumers.forIn' _ _ _ _ _ _ _ _ at hA hB
  rw [IterM.DefaultConsumers.forIn'_eq_wf pl wf] at hA hB
  exact hA.symm.trans (ignores.trans hB)

private abbrev Yields {σ : Type u} [Iterator σ Id N] (it next : IterM (α := σ) Id N) (n : Nat) :=
  ∃ h, Shrink.inflate it.step = ⟨.yield next ⟨n⟩, h⟩

private theorem segment {σ : Type u} [Iterator σ Id N] [Finite σ Id] {T : Type u}
    (i j k : IterM (α := σ) Id N) (zero : Yields i j 0) (one : Yields j k 1)
    {f g : T → T} (h : ∀ t, f t = g t)
    (eq : runDefault T i (next T f g h) (idLift T) = runDefault T i (next T f g h) (firstLift T)) :
    twoSteps (next T f g h) (idLift T) = twoSteps (next T f g h) (firstLift T) := by
  letI := monad T
  obtain ⟨_, zero⟩ := zero
  obtain ⟨_, one⟩ := one
  refine Eq.trans ?_ (eq.trans ?_)
  · symm
    unfold runDefault
    rw [IterM.DefaultConsumers.forIn'.wf.eq_def]
    dsimp only [idLift]
    rw [zero]
    dsimp only
    simp only [IterM.DefaultConsumers.forIn'.wf.eq_def (it := j), idLift, one]
    rfl
  · unfold runDefault
    rw [IterM.DefaultConsumers.forIn'.wf.eq_def]
    dsimp only [firstLift]
    rw [zero]
    dsimp only
    simp only [IterM.DefaultConsumers.forIn'.wf.eq_def (it := j), firstLift, one]
    rfl

theorem twoStepsOfOpen (law : type_of% (@Rxo.Iterator.instLawfulIteratorLoop.{u,u})) :
    TwoStepsAgree.{u} := by
  intro T f g h
  letI := monad T
  letI := lawful T
  apply segment (stage 0) (stage 1) (stage 2) ⟨_, openStepZero⟩ ⟨_, openStepOne⟩ h
  exact defaultEq T _ (@law N _ _ _ _ _ (Paired T) _ _) _ _ rfl

private instance : LE N := ⟨fun a b => Nat.le a.down b.down⟩
private instance : DecidableLE N := fun a b => Nat.decLe a.down b.down
private instance : LawfulUpwardEnumerableLE N where
  le_iff a b := by
    constructor
    · intro h
      exact ⟨b.down - a.down, congrArg some (ULift.ext (Nat.add_sub_cancel' h))⟩
    · rintro ⟨j, h⟩
      have eq := congrArg ULift.down (Option.some.inj h)
      change a.down + j = b.down at eq
      change a.down ≤ b.down
      rw [← eq]
      exact Nat.le_add_right _ _
private instance : Rxc.IsAlwaysFinite N where
  finite a b := by
    refine ⟨b.down+1, ?_⟩
    change ¬ Nat.le (a.down + (b.down+1)) b.down
    exact Nat.not_le.mpr (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_left ..))

private def closedStage (k : Nat) : IterM (α := Rxc.Iterator N.{u}) Id N := ⟨⟨some ⟨k⟩, ⟨1⟩⟩⟩
private theorem closedZero : Yields (closedStage.{u} 0) (closedStage 1) 0 := ⟨rfl, Shrink.inflate_deflate⟩
private theorem closedOne : Yields (closedStage.{u} 1) (closedStage 2) 1 := ⟨rfl, Shrink.inflate_deflate⟩

theorem twoStepsOfClosed (law : type_of% (@Rxc.Iterator.instLawfulIteratorLoop.{u,u})) :
    TwoStepsAgree.{u} := by
  intro T f g h
  letI := monad T
  letI := lawful T
  apply segment _ _ _ closedZero closedOne h
  exact defaultEq T _ (@law N _ _ _ _ _ (Paired T) _ _) _ _ rfl

section Unbounded
private def within (j : Nat) : Option N := if j < 3 then some ⟨j⟩ else none
private local instance bounded : UpwardEnumerable N where
  succ? k := within (k.down+1)
  succMany?
    | 0, k => some k
    | j+1, k => within (k.down+(j+1))
private local instance : LawfulUpwardEnumerable N where
  succMany?_zero _ := rfl
  succMany?_add_one j k := by
    cases j with
    | zero => rfl
    | succ j =>
      change within (k.down+(j+2)) = (within (k.down+(j+1))).bind (fun a => within (a.down+1))
      unfold within
      by_cases h : k.down + (j+1) < 3
      · rw [ite_eq_left h]; rfl
      · rw [ite_eq_right h]
        exact ite_eq_right (fun h' => h (Nat.lt_of_succ_lt h'))
  ne_of_lt a b := by
    rintro ⟨j, h⟩ rfl
    change within (a.down+(j+1)) = some a at h
    unfold within at h
    split at h
    · exact Nat.ne_of_gt (Nat.lt_add_of_pos_right (Nat.zero_lt_succ j)) (congrArg ULift.down (Option.some.inj h))
    · cases h
private local instance : Rxi.IsAlwaysFinite N where
  finite a := by
    refine ⟨3, ?_⟩
    change within (a.down + 3) = none
    exact ite_eq_right (Nat.not_lt.mpr (Nat.le_add_left ..))
private def unboundedStage (k : Nat) : IterM (α := Rxi.Iterator N.{u}) Id N := ⟨⟨some ⟨k⟩⟩⟩
private theorem unboundedZero : Yields (unboundedStage.{u} 0) (unboundedStage 1) 0 := ⟨rfl, Shrink.inflate_deflate⟩
private theorem unboundedOne : Yields (unboundedStage.{u} 1) (unboundedStage 2) 1 := ⟨rfl, Shrink.inflate_deflate⟩

theorem twoStepsOfUnbounded (law : type_of% (@Rxi.Iterator.instLawfulIteratorLoop.{u,u})) :
    TwoStepsAgree.{u} := by
  intro T f g h
  letI := monad T
  letI := lawful T
  apply segment _ _ _ unboundedZero unboundedOne h
  exact defaultEq T _ (@law N _ _ (Paired T) _ _) _ _ rfl

end Unbounded
end OmegaChecks.InitBoundaries.RangeLoopLift
