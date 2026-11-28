module
public import Lean
import Lean.Replay
import all Lean.Util.CollectAxioms
import all Init.Data.Iterators.Combinators.Monadic.Take
import all Init.Data.Iterators.Basic
import all Init.Data.Iterators.Consumers.Monadic.Loop
import all Init.Data.Slice.Operations
public import OmegaChecks.InitInventory.Logic

public section

open Lean
namespace OmegaChecks.InitBoundaries
universe u v w z

namespace Collector

open Std Std.Iterators

private def next (f : Nat → Bool) (it : IterM (α := Nat) Id Unit) : IterStep (IterM (α := Nat) Id Unit) Unit :=
  match f it.internalState with
  | true => .done
  | false => .yield ⟨it.internalState + 1⟩ ()

@[instance_reducible] private def searchIterator (f : Nat → Bool) : Iterator Nat Id Unit where
  IsPlausibleStep it s := s = next f it
  step it :=
    let value : {s // s = next f it} := ⟨next f it, rfl⟩
    pure (cast (congrFun (Std.Internal.idOpaque (α := Type)).property.symm _) value)

private def search (k : Nat) : Iter (α := Nat) Unit := ⟨k⟩

private theorem signal_after {f : Nat → Bool} (sticky : ∀ i, f i = true → f (i+1) = true)
    {n : Nat} (hit : f n = true) {k : Nat} (le : n ≤ k) : f k = true := by
  induction le with
  | refl => exact hit
  | step _ ih => exact sticky _ ih

private theorem searchFinite {f : Nat → Bool} (sticky : ∀ i, f i = true → f (i+1) = true)
    {n : Nat} (hit : f n = true) :
    letI := searchIterator f
    Finite Nat Id := by
  letI := searchIterator f
  apply Finite.of_finitenessRelation
  refine ⟨InvImage Nat.lt (fun it : IterM (α := Nat) Id Unit => n - it.internalState),
    InvImage.wf _ Nat.lt_wfRel.wf, ?_⟩
  intro it it' h
  obtain ⟨s, dest, step⟩ := h
  change s = next f it at step
  subst s
  dsimp only [next] at dest
  cases e : f it.internalState with
  | true => rw [e] at dest; cases dest
  | false =>
    rw [e] at dest
    cases Option.some.inj dest
    have lt : it.internalState < n := Nat.lt_of_not_ge fun ge => Bool.noConfusion (e.symm.trans (signal_after sticky hit ge))
    exact Nat.pred_lt fun zero => (Nat.not_le_of_lt lt) (Nat.le_of_sub_eq_zero zero)

private theorem searchStep (f : Nat → Bool) (k : Nat) :
    letI := searchIterator f
    (search k).step.val = (match f k with | true => .done | false => .yield (search (k+1)) ()) := by
  letI := searchIterator f
  change (IterM.Step.toPure (it := (search k).toIterM) (Shrink.inflate (Shrink.deflate _))).val = _
  refine Eq.trans (congrArg (fun q => (IterM.Step.toPure (it := (search k).toIterM) q).val) Shrink.inflate_deflate) ?_
  cases e : f k <;> simp only [search, next, IterM.Step.toPure, IterStep.mapIterator,
    Iter.toIterM, IterM.toIter, e] <;> rfl

private theorem length_hits {f : Nat → Bool} (sticky : ∀ i, f i = true → f (i+1) = true)
    {n : Nat} (hit : f n = true)
    (len : Nat → Nat)
    (unroll : ∀ k, len k = (match f k with | true => 0 | false => (len (k+1)).succ))
    (k : Nat) : f (k + len k) = true := by
  generalize h : n - k = fuel
  induction fuel generalizing k with
  | zero =>
    have yes := signal_after sticky hit (Nat.le_of_sub_eq_zero h)
    have l := unroll k
    rw [yes] at l
    simpa only [l, Nat.add_zero] using yes
  | succ fuel ih =>
    have l := unroll k
    cases e : f k with
    | true => rw [e] at l; simpa only [l, Nat.add_zero] using e
    | false =>
      rw [e] at l
      change len k = (len (k+1)).succ at l
      have eq : n - (k+1) = fuel := by omega
      have out := ih (k+1) eq
      exact (congrArg f (by omega : k + len k = k + 1 + len (k + 1))).trans out

/-- The stream has signalled at or before the given index. -/
def seen (f : Nat → Bool) : Nat → Bool
  | 0 => f 0
  | n+1 => seen f n || f (n+1)

private theorem seenSticky (f : Nat → Bool) (n : Nat) (h : seen f n = true) :
    seen f (n+1) = true := by rw [seen, h]; rfl

private theorem seen_of_hit (f : Nat → Bool) (n : Nat) (hit : f n = true) :
    seen f n = true := by
  cases n with
  | zero => exact hit
  | succ n => rw [seen, hit, Bool.or_true]

private theorem hit_of_seen (f : Nat → Bool) (n : Nat) (h : seen f n = true) : ∃ k, f k = true := by
  induction n with
  | zero => exact ⟨0, h⟩
  | succ n ih =>
    cases eq : f (n+1) with
    | true => exact ⟨n+1, eq⟩
    | false => exact ih (by simpa only [seen, eq, Bool.or_false] using h)

private theorem searchProductive (f : Nat → Bool) : letI := searchIterator f; Productive Nat Id := by
  letI := searchIterator f
  constructor
  refine ⟨fun it => Acc.intro _ fun it' step => False.elim ?_⟩
  change IterStep.skip it' = next f it at step
  unfold next at step
  cases h : f it.internalState <;> rw [h] at step <;> cases step

private theorem hitOfSearchFinite (f : Nat → Bool) (finite : letI := searchIterator f; Finite Nat Id) :
    ∃ k, f k = true := by
  letI := searchIterator f
  have reaches (it : IterM (α := Nat) Id Unit) : ∃ k, f k = true := by
    induction it using finite.wf.induction with
    | h it recur =>
      cases h : f it.internalState with
      | true => exact ⟨_, h⟩
      | false =>
        apply recur ⟨it.internalState + 1⟩
        apply IterM.isPlausibleSuccessorOf_of_yield (out := ())
        change _ = next f it
        unfold next
        rw [h]
  exact reaches ⟨0⟩

/-- Deciding the finiteness test of the Take.Rel unfolding on productive, yield-only
search iterators decides whether any element of an arbitrary Boolean stream is true. -/
def limitedOmniscienceFromTakeDecision
    (classify : ∀ [Iterator Nat Id Unit] [Productive Nat Id], Decidable (Finite Nat Id))
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  letI := searchIterator (seen f)
  letI := searchProductive (seen f)
  cases classify with
  | isTrue hf =>
    exact isTrue ((hitOfSearchFinite (seen f) hf).elim fun n hit => hit_of_seen f n hit)
  | isFalse hn =>
    exact isFalse fun ⟨n, hit⟩ => hn (searchFinite (seenSticky f) (seen_of_hit f n hit))

open Lean Meta Elab.Command in
run_cmd
  liftTermElabM do
    let pinned ← getConstInfo `Std.Iterators.Types.Take.Rel.eq_1
    let rule := mkConst pinned.name (pinned.levelParams.map fun _ => 0)
    let specialized := mkApp3 rule (mkConst ``Nat) (mkConst ``Unit) (mkConst ``Id [0])
    let .forallE _ monad _ _ ← whnf (← inferType specialized) | throwError "expected Monad Id"
    forallTelescope (← inferType (mkApp specialized (← synthInstance monad))) fun args conclusion => do
      let some (_, _, rhs) := conclusion.eq? | throwError "expected the Take.Rel unfolding equation"
      unless rhs.isAppOfArity ``dite 5 do throwError "expected the finiteness-dependent branches"
      let decider := rhs.getAppArgs[2]!
      unless decider.isAppOfArity ``Classical.propDecidable 1 do throwError "unexpected finiteness decision"
      let required ← mkForallFVars args (← inferType decider)
      let reduction ← getConstInfo ``limitedOmniscienceFromTakeDecision
      unless Kernel.isDefEqGuarded (← getEnv) {} required reduction.type.bindingDomain! do
        throwError "the decision in Take.Rel.eq_1 differs from the input to the stream reduction"
    unless (← collectAxioms ``limitedOmniscienceFromTakeDecision).isEmpty do
      throwError "the stream decision reduction depends on axioms"

/-- A decider for all Boolean streams cannot examine a bounded prefix at the all-false stream. -/
theorem noContinuousSignalDecider
    (answer : (Nat → Bool) → Bool)
    (correct : ∀ f, answer f = true ↔ ∃ n, f n = true)
    (stable : ∃ k, ∀ f : Nat → Bool, (∀ i, i < k → f i = false) →
      answer f = answer (fun _ => false)) : False := by
  obtain ⟨k, same⟩ := stable
  let spike (i : Nat) := Nat.beq i k
  have yes := (correct spike).mpr ⟨k, Nat.beq_refl k⟩
  have noSignal : ¬ ∃ n : Nat, false = true := fun ⟨_, h⟩ => Bool.noConfusion h
  apply noSignal
  apply (correct (fun _ => false)).mp
  have agree (i : Nat) (lt : i < k) : spike i = false := by
    cases eq : spike i with
    | false => rfl
    | true => exact False.elim ((Nat.ne_of_lt lt) (Nat.eq_of_beq_eq_true eq))
  exact (same spike agree).symm.trans yes

private def limitedOmniscienceFromLength
    (measure : ∀ {α β : Type} [Iterator α Id β], Iter (α := α) β → Nat)
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] (it : Iter (α := α) β),
      measure it = it.toList.length) (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  let g := seen f
  letI := searchIterator g
  let len := fun k => measure (search k)
  cases h : g (len 0) with
  | true => exact isTrue (hit_of_seen f _ h)
  | false =>
    refine isFalse fun ⟨n, hit⟩ => ?_
    have gHit := seen_of_hit f n hit
    letI := searchFinite (seenSticky f) gHit
    have unroll (k : Nat) : len k = (match g k with | true => 0 | false => (len (k+1)).succ) := by
      unfold len
      rw [correct (search k), Iter.toList_eq_match_step, searchStep]
      cases e : g k with
      | true => rfl
      | false => exact congrArg Nat.succ (correct (search (k+1))).symm
    have result := length_hits (seenSticky f) gHit len unroll 0
    exact Bool.noConfusion (h.symm.trans (by simpa only [Nat.zero_add] using result))

/-- Agreement with the official collector on finite iterators gives the limited principle
of omniscience for arbitrary Boolean streams. -/
def limitedOmniscienceFromCollector (collect : type_of% (@Std.Iter.toList.{0}))
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] (it : Iter (α := α) β),
      collect it = it.toList) (f : Nat → Bool) : Decidable (∃ n, f n = true) :=
  limitedOmniscienceFromLength (fun it => (collect it).length)
    (fun it => congrArg List.length (correct it)) f

/-- A universal default loop can count outputs before the first signal. It suffices that its
identity-monad specialization agrees with the official loop on finite iterators. -/
def limitedOmniscienceFromDefaultLoop (loop : type_of% (@Std.IteratorLoop.defaultImplementation.{0,0,0,0}))
    (correct : ∀ {α β : Type} [inst : Iterator α Id β] [Finite α Id],
      @loop β α Id Id _ inst = @IteratorLoop.defaultImplementation β α Id Id _ inst)
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromLength (f := f) (fun {α β} [inst : Iterator α Id β] it =>
    letI := @loop β α Id Id _ inst
    it.length)
  intro α β inst finite it
  rw [correct]
  letI : IteratorLoop α Id Id := .defaultImplementation
  exact Iter.length_toList_eq_length.symm

/-- A default loop body that agrees on finite identity iterators can count all outputs
before the first signal. -/
def limitedOmniscienceFromDefaultForIn (run : type_of% @IterM.DefaultConsumers.forIn'.{0,0,0,0})
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id]
      (lift : ∀ δ ε : Type, (δ → Id ε) → Id δ → Id ε) (γ : Type)
      (Pl : β → γ → ForInStep γ → Prop) (it : IterM (α := α) Id β) (init : γ)
      (step : (b : β) → it.IsPlausibleIndirectOutput b → (c : γ) → Id (Subtype (Pl b c))),
      run lift γ Pl it init _ (fun _ => id) step =
        IterM.DefaultConsumers.forIn' lift γ Pl it init _ (fun _ => id) step)
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromLength (f := f) (fun {α β} [inst : Iterator α Id β] it =>
    letI : IteratorLoop α Id Id :=
      ⟨fun lift γ Pl it init => run lift γ Pl it init _ (fun _ => id)⟩
    it.length)
  intro α β inst finite it
  letI : IteratorLoop α Id Id := .defaultImplementation
  refine Eq.trans ?_ (Iter.length_toList_eq_length (it := it)).symm
  apply congrArg ULift.down
  apply correct

/-- An array collector on unrestricted iterators also gives a list collector pointwise. -/
def limitedOmniscienceFromArray (collect : type_of% (@Std.Iter.toArray.{0}))
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] (it : Iter (α := α) β),
      collect it = it.toArray) (f : Nat → Bool) : Decidable (∃ n, f n = true) :=
  limitedOmniscienceFromCollector (fun it => (collect it).toList)
    (fun it => (congrArg Array.toList (correct it)).trans Iter.toList_toArray) f

/-- Reversing the reverse collector recovers the ordinary collector on every finite iterator. -/
def limitedOmniscienceFromReverse (collect : type_of% (@Std.Iter.toListRev.{0}))
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] (it : Iter (α := α) β),
      collect it = it.toListRev) (f : Nat → Bool) : Decidable (∃ n, f n = true) :=
  limitedOmniscienceFromCollector (fun it => (collect it).reverse)
    (fun it => (congrArg List.reverse (correct it)).trans Iter.reverse_toListRev) f

/-- A slice may use the iterator itself as its internal representation. -/
def limitedOmniscienceFromSlice (collect : type_of% (@Std.Slice.toList.{0,0}))
    (correct : ∀ {γ α β : Type} [ToIterator (Slice γ) Id α β] [Iterator α Id β]
      [Finite α Id] (s : Slice γ), collect s = s.toList) (f : Nat → Bool) :
    Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromCollector (f := f) (fun {α β} [Iterator α Id β] it =>
    letI := ToIterator.of (γ := Slice (Iter (α := α) β)) α (fun s => s.internalRepresentation)
    collect ⟨it⟩)
  intro α β inst fin it
  letI := ToIterator.of (γ := Slice (Iter (α := α) β)) α (fun s => s.internalRepresentation)
  exact correct (Slice.mk it)

/-- An array-valued slice collector applies to a slice carrying the iterator itself. -/
def limitedOmniscienceFromSliceArray (collect : type_of% (@Std.Slice.toArray.{0,0}))
    (correct : ∀ {γ α β : Type} [ToIterator (Slice γ) Id α β] [Iterator α Id β]
      [Finite α Id] (s : Slice γ), collect s = s.toArray) (f : Nat → Bool) :
    Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromArray (f := f) (fun {α β} [Iterator α Id β] it =>
    letI := ToIterator.of (γ := Slice (Iter (α := α) β)) α (fun s => s.internalRepresentation)
    collect ⟨it⟩)
  intro α β inst fin it
  letI := ToIterator.of (γ := Slice (Iter (α := α) β)) α (fun s => s.internalRepresentation)
  exact correct (Slice.mk it)

/-- The corresponding reverse traversal of the slice returns the reverse iterator collection. -/
def limitedOmniscienceFromSliceReverse (collect : type_of% (@Std.Slice.toListRev.{0,0}))
    (correct : ∀ {γ α β : Type} [ToIterator (Slice γ) Id α β] [Iterator α Id β]
      [Finite α Id] (s : Slice γ), collect s = s.toListRev) (f : Nat → Bool) :
    Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromReverse (f := f) (fun {α β} [Iterator α Id β] it =>
    letI := ToIterator.of (γ := Slice (Iter (α := α) β)) α (fun s => s.internalRepresentation)
    collect ⟨it⟩)
  intro α β inst fin it
  letI := ToIterator.of (γ := Slice (Iter (α := α) β)) α (fun s => s.internalRepresentation)
  exact correct (Slice.mk it)

/-- Specializing monadic collection to the identity monad preserves the unrestricted pure interface. -/
def limitedOmniscienceFromMonadicCollector (collect : type_of% (@Std.IterM.toList.{0,0}))
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] (it : IterM (α := α) Id β),
      collect it = it.toList) (f : Nat → Bool) : Decidable (∃ n, f n = true) :=
  limitedOmniscienceFromCollector (fun it => (collect it.toIterM).run)
    (fun it => (correct it.toIterM).trans Iter.toList_eq_toList_toIterM.symm) f

/-- Only the identity-monad specialization is needed for the array collector. -/
def limitedOmniscienceFromMonadicArray (collect : type_of% (@Std.IterM.toArray.{0,0}))
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] (it : IterM (α := α) Id β),
      collect it = it.toArray) (f : Nat → Bool) : Decidable (∃ n, f n = true) :=
  limitedOmniscienceFromArray (fun it => (collect it.toIterM).run)
    (fun it => (correct it.toIterM).trans Iter.toArray_eq_toArray_toIterM.symm) f

/-- Only the identity-monad specialization is needed for the reverse collector. -/
def limitedOmniscienceFromMonadicReverse (collect : type_of% (@Std.IterM.toListRev.{0,0}))
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] (it : IterM (α := α) Id β),
      collect it = it.toListRev) (f : Nat → Bool) : Decidable (∃ n, f n = true) :=
  limitedOmniscienceFromReverse (fun it => (collect it.toIterM).run)
    (fun it => (correct it.toIterM).trans Iter.toListRev_eq_toListRev_toIterM.symm) f

/-- Rendering every output as one character makes the string length count the iterator's outputs. -/
@[instance_reducible] private def markerString (β : Type) : ToString β := ⟨fun _ => String.singleton 'x'⟩

def limitedOmniscienceFromStringList (collect : type_of% @Std.Iter.toStringList)
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] [ToString β] (it : Iter (α := α) β),
      collect it = it.toStringList) (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromLength (f := f) (fun {α β} [Iterator α Id β] it =>
    letI := markerString β
    (collect it).length)
  intro α β inst fin it
  letI := markerString β
  rw [correct, Iter.toStringList, Iter.toList_map, List.length_map]

def limitedOmniscienceFromStringArray (collect : type_of% @Std.Iter.toStringArray)
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] [ToString β] (it : Iter (α := α) β),
      collect it = it.toStringArray) (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromStringList (fun it => (collect it).toList) _ f
  intro α β inst fin fmt it
  rw [correct, Iter.toStringArray, Iter.toStringList, Iter.toList_toArray]

private theorem markerLength (xs : List β) :
    (String.join (xs.map (fun _ => String.singleton 'x'))).toList.length = xs.length := by
  rw [String.toList_join]
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rw [List.map_cons, List.flatMap_cons, String.toList_singleton, List.singleton_append]
    exact congrArg Nat.succ ih

def limitedOmniscienceFromStringJoin (join : type_of% @Std.Iter.joinString)
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] [ToString β] (it : Iter (α := α) β),
      join it = String.join (it.toList.map toString)) (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromLength (f := f) (fun {α β} [Iterator α Id β] it =>
    letI := markerString β
    (join it).toList.length)
  intro α β inst fin it
  letI := markerString β
  rw [correct]
  exact markerLength _

def limitedOmniscienceFromStringIntercalate (join : type_of% @Std.Iter.intercalateString)
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] [ToString β]
      (s : String.Slice) (it : Iter (α := α) β), join s it = s.copy.intercalate (it.toList.map toString))
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromStringJoin (fun it => join "".toSlice it) _ f
  intro α β inst fin fmt it
  rw [correct, String.copy_toSlice]
  generalize it.toList.map toString = xs
  induction xs with
  | nil => exact String.intercalate_nil.trans String.join_nil.symm
  | cons x xs ih =>
    rw [String.join_cons, ← ih]
    cases xs with
    | nil => rw [String.intercalate_singleton, String.intercalate_nil, String.append_empty]
    | cons y ys => rw [String.intercalate_cons_cons, String.append_empty]

private def indexStep (f : Nat → Bool) (it : IterM (α := Option Nat) Id Nat) :
    IterStep (IterM (α := Option Nat) Id Nat) Nat :=
  match it.internalState with
  | none => .done
  | some k => if f k then .yield ⟨none⟩ k else .skip ⟨some (k+1)⟩

@[instance_reducible] private def indexIterator (f : Nat → Bool) : Iterator (Option Nat) Id Nat where
  IsPlausibleStep it s := s = indexStep f it
  step it := pure (.deflate ⟨indexStep f it, rfl⟩)

private theorem indexFinite {f : Nat → Bool} (sticky : ∀ i, f i = true → f (i+1) = true)
    {n : Nat} (hit : f n = true) :
    letI := indexIterator f
    Finite (Option Nat) Id := by
  letI := indexIterator f
  let rank (it : IterM (α := Option Nat) Id Nat) := it.internalState.elim 0 (fun k => n - k + 1)
  apply Finite.of_finitenessRelation
  refine ⟨InvImage Nat.lt rank, InvImage.wf _ Nat.lt_wfRel.wf, ?_⟩
  intro it next h
  obtain ⟨s, dest, step⟩ := h
  change s = indexStep f it at step
  subst s
  rcases it with ⟨_ | k⟩
  · cases dest
  · dsimp only [indexStep] at dest
    cases e : f k with
    | true =>
      rw [e] at dest
      cases Option.some.inj dest
      exact Nat.zero_lt_succ _
    | false =>
      rw [e] at dest
      cases Option.some.inj dest
      have lt : k < n := Nat.lt_of_not_ge fun ge =>
        Bool.noConfusion (e.symm.trans (signal_after sticky hit ge))
      change n - (k + 1) + 1 < n - k + 1
      omega

private theorem firstIndexHit {f : Nat → Bool} (sticky : ∀ i, f i = true → f (i+1) = true)
    {n : Nat} (hit : f n = true) (k : Nat) :
    letI := indexIterator f
    ∃ j, (⟨some k⟩ : Iter (α := Option Nat) Nat).atIdxSlow? 0 = some j ∧ f j = true := by
  letI := indexIterator f
  letI := indexFinite sticky hit
  have unroll (k : Nat) :
      (⟨some k⟩ : Iter (α := Option Nat) Nat).atIdxSlow? 0 =
        if f k then some k else (⟨some (k+1)⟩ : Iter (α := Option Nat) Nat).atIdxSlow? 0 := by
    rw [Iter.atIdxSlow?_eq_match]
    have eq := congrArg (fun q => (IterM.Step.toPure (it := (⟨some k⟩ : Iter (α := Option Nat) Nat).toIterM) q).val)
      (Shrink.inflate_deflate (x := (⟨indexStep f ⟨some k⟩, rfl⟩ : (⟨some k⟩ : IterM (α := Option Nat) Id Nat).Step)))
    change (⟨some k⟩ : Iter (α := Option Nat) Nat).step.val = _ at eq
    rw [eq]
    cases e : f k <;> simp [IterM.Step.toPure, indexStep, e, IterStep.mapIterator, IterM.toIter]
  generalize heq : n - k = fuel
  induction fuel generalizing k with
  | zero =>
    have yes := signal_after sticky hit (Nat.le_of_sub_eq_zero heq)
    exact ⟨k, by rw [unroll, yes]; rfl, yes⟩
  | succ fuel ih =>
    cases e : f k with
    | true => exact ⟨k, by rw [unroll, e]; rfl, e⟩
    | false =>
      obtain ⟨j, hj, h⟩ := ih (k+1) (by omega)
      exact ⟨j, by rw [unroll, e]; exact hj, h⟩

/-- The unrestricted lookup accepts iterators that skip before their first output.
For a stream with a signal its first output can be the location of that signal. -/
def limitedOmniscienceFromLookup (lookup : type_of% (@Std.Iter.atIdxSlow?.{0}))
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] (i : Nat) (it : Iter (α := α) β),
      lookup i it = it.atIdxSlow? i) (f : Nat → Bool) : Decidable (∃ i, f i = true) := by
  letI := indexIterator (seen f)
  let it : Iter (α := Option Nat) Nat := ⟨some 0⟩
  cases h : lookup 0 it with
  | none =>
    refine isFalse fun ⟨k, hk⟩ => ?_
    have yes := seen_of_hit f k hk
    letI := indexFinite (seenSticky f) yes
    obtain ⟨j, hj, _⟩ := firstIndexHit (seenSticky f) yes 0
    cases h.symm.trans ((correct 0 it).trans hj)
  | some j =>
    cases e : seen f j with
    | true => exact isTrue (hit_of_seen f j e)
    | false =>
      refine isFalse fun ⟨k, hk⟩ => ?_
      have yes := seen_of_hit f k hk
      letI := indexFinite (seenSticky f) yes
      obtain ⟨j', hj, sign⟩ := firstIndexHit (seenSticky f) yes 0
      cases Option.some.inj (h.symm.trans ((correct 0 it).trans hj))
      exact Bool.noConfusion (e.symm.trans sign)

/-- The empty array accumulator suffices to recover the unrestricted array collector. -/
def limitedOmniscienceFromArrayAccumulator (go : type_of% @IterM.toArray.go.{0,0})
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] (it : IterM (α := α) Id β),
      go it #[] = it.toArray) (f : Nat → Bool) : Decidable (∃ n, f n = true) :=
  limitedOmniscienceFromMonadicArray (fun it => go it #[]) correct f

/-- The empty list accumulator recovers the unrestricted reverse collector. -/
def limitedOmniscienceFromReverseAccumulator (go : type_of% @IterM.toListRev.go.{0,0})
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] (it : IterM (α := α) Id β),
      go it [] = it.toListRev) (f : Nat → Bool) : Decidable (∃ n, f n = true) :=
  limitedOmniscienceFromMonadicReverse (fun it => go it []) correct f

set_option linter.deprecated false in
/-- Every iterator has a partial view, including the search for a stream's first signal. -/
def limitedOmniscienceFromPartialLookup (lookup : type_of% @Iter.Partial.atIdxSlow?.{0})
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] (n : Nat) (it : Iter (α := α) β),
      lookup n ⟨it⟩ = it.atIdxSlow? n) (f : Nat → Bool) : Decidable (∃ n, f n = true) :=
  limitedOmniscienceFromLookup (fun n it => lookup n ⟨it⟩) correct f

open Std.Iterators.Types

/-- Identity mapping carries an arbitrary input iterator through the map loop without
changing its number of outputs. -/
def limitedOmniscienceFromMapLoop (loop : type_of% (@Map.instIteratorLoop.{0,0,0,0,0}))
    (correct : ∀ {α β : Type} [inst : Iterator α Id β] [Finite α Id],
      @loop α β β Id Id Id _ _ inst (fun _ => monadLift) (fun b => pure b) =
        @Map.instIteratorLoop α β β Id Id Id _ _ inst (fun _ => monadLift) (fun b => pure b))
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromLength (f := f) (fun {α β} [inst : Iterator α Id β] it =>
    letI := @loop α β β Id Id Id _ _ inst (fun _ => monadLift) (fun b => pure b)
    (it.map id).length)
  intro α β inst finite it
  rw [correct]
  letI : IteratorLoop α Id Id := .defaultImplementation
  exact Iter.length_map.trans Iter.length_toList_eq_length.symm

/-- Attaching the constantly true predicate keeps every original output. -/
def limitedOmniscienceFromAttachLoop (loop : type_of% (@Attach.instIteratorLoop.{0,0,0,0}))
    (correct : ∀ {α β : Type} [inst : Iterator α Id β] [Finite α Id],
      @loop α β Id _ Id _ (fun _ => True) inst = @Attach.instIteratorLoop α β Id _ Id _ (fun _ => True) inst)
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromLength (f := f) (fun {α β} [inst : Iterator α Id β] it =>
    letI := @loop α β Id _ Id _ (fun _ => True) inst
    (it.attachWith (fun _ => True) (fun _ _ => trivial)).length)
  intro α β inst finite it
  rw [correct]
  letI : IteratorLoop α Id Id := .defaultImplementation
  exact Iter.length_attachWith.trans Iter.length_toList_eq_length.symm

/-- Universe lifting keeps every output, including for a same-universe lift. -/
def limitedOmniscienceFromULiftLoop (loop : type_of% (@ULiftIterator.instIteratorLoop.{0,0,0,0,0,0}))
    (correct : ∀ {α β : Type} [inst : Iterator α Id β] [Finite α Id],
      @loop α Id Id β (fun _ => monadLift) Id _ _ inst =
        @ULiftIterator.instIteratorLoop α Id Id β (fun _ => monadLift) Id _ _ inst)
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromLength (f := f) (fun {α β} [inst : Iterator α Id β] it =>
    letI := @loop α Id Id β (fun _ => monadLift) Id _ _ inst
    it.uLift.length)
  intro α β inst finite it
  rw [correct]
  letI : IteratorLoop α Id Id := .defaultImplementation
  exact Iter.length_uLift.trans Iter.length_toList_eq_length.symm

/-- A filter-map that returns every element preserves the output count. -/
def limitedOmniscienceFromFilterMapLoop (loop : type_of% (@FilterMap.instIteratorLoop.{0,0,0,0,0}))
    (correct : ∀ {α β : Type} [inst : Iterator α Id β] [Finite α Id],
      @loop α β β Id Id Id _ _ inst (fun _ => monadLift) (fun b => pure (some b)) =
        @FilterMap.instIteratorLoop α β β Id Id Id _ _ inst (fun _ => monadLift) (fun b => pure (some b)))
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromLength (f := f) (fun {α β} [inst : Iterator α Id β] it =>
    letI := @loop α β β Id Id Id _ _ inst (fun _ => monadLift) (fun b => pure (some b))
    (it.filterMap some).length)
  intro α β inst finite it
  rw [correct]
  letI := FilterMap.instIteratorLoop (α := α) (β := β) (γ := β) (m := Id) (n := Id) (o := Id)
    (lift := fun _ => monadLift) (f := fun b => pure (some b))
  exact Iter.length_toList_eq_length.symm.trans
    (congrArg List.length ((Iter.toList_filterMap (it := it) (f := some)).trans (List.filterMap_some ..)))

/-- Appending an empty list iterator preserves the entire input. -/
def limitedOmniscienceFromAppendLoop (loop : type_of% (@Append.instIteratorLoop.{0,0,0,0}))
    (correct : ∀ {α β : Type} [inst : Iterator α Id β] [Finite α Id],
      @loop Id β α (ListIterator β) Id _ _ inst _ = @Append.instIteratorLoop Id β α (ListIterator β) Id _ _ inst _)
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromLength (f := f) (fun {α β} [inst : Iterator α Id β] it =>
    letI := @loop Id β α (ListIterator β) Id _ _ inst _
    (it.append ([] : List β).iter).length)
  intro α β inst finite it
  rw [correct]
  simp only [← Iter.length_toList_eq_length, Iter.toList_append, List.toList_iter, List.append_nil]

/-- Flattening singleton list iterators preserves the full output sequence. -/
def limitedOmniscienceFromFlattenLoop (loop : type_of% (@Flatten.instIteratorLoop.{0,0,0,0}))
    (correct : ∀ {α α₂ β : Type} [out : Iterator α Id (IterM (α := α₂) Id β)]
      [inner : Iterator α₂ Id β] [Finite α Id] [Finite α₂ Id],
      @loop α α₂ β Id Id _ _ out inner = @Flatten.instIteratorLoop α α₂ β Id Id _ _ out inner)
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromLength (f := f) (fun {α β} [inst : Iterator α Id β] it =>
    letI := @loop (Map α Id Id (fun _ => monadLift) (fun b : β => pure ([b].iter.toIterM))) (ListIterator β)
      β Id Id _ _ inferInstance inferInstance
    (it.flatMap (fun b => [b].iter)).length)
  intro α β inst finite it
  rw [correct]
  letI := @Flatten.instIteratorLoop (Map α Id Id (fun _ => monadLift) (fun b : β => pure ([b].iter.toIterM)))
    (ListIterator β) β Id Id _ _ inferInstance inferInstance
  have eq := Iter.length_toList_eq_length (it := it.flatMap fun b => [b].iter)
  rw [Iter.toList_flatMap, Iter.toList_map] at eq
  simpa [List.toList_iter, ← List.flatMap_def] using eq.symm

/-- Taking one output suffices to implement lookup at index zero when searching for a signal. -/
def limitedOmniscienceFromTakeLoop (loop : type_of% (@Take.instIteratorLoop.{0,0,0,0}))
    (correct : ∀ {α β : Type} [inst : Iterator α Id β] [Finite α Id],
      @loop α Id β Id _ _ inst = @Take.instIteratorLoop α Id β Id _ _ inst)
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromLookup (f := f) (fun {α β} [inst : Iterator α Id β] n it =>
    letI := @loop α Id β Id _ _ inst
    ((it.take (n+1)).fold (init := ([] : List β)) fun xs b => b :: xs).reverse[n]?)
  intro α β inst finite n it
  rw [correct]
  letI := @Take.instIteratorLoop α Id β Id _ _ inst
  rw [← Iter.foldl_toList, List.foldl_flip_cons_eq_append', List.append_nil, List.reverse_reverse,
    Iter.toList_take_of_finite, List.getElem?_take, ite_eq_left (Nat.lt_succ_self _)]
  exact Iter.getElem?_toList_eq_atIdxSlow?

private def stopAt (g : Nat → Bool) (k : Nat) : Option Nat :=
  if g k then none else some k

@[instance_reducible] private def signalRange (g : Nat → Bool) : Std.PRange.UpwardEnumerable Nat where
  succ? k := stopAt g (k + 1)
  succMany?
    | 0, k => some k
    | n + 1, k => stopAt g (k + (n + 1))

private theorem signalRangeLaw {g : Nat → Bool} (sticky : ∀ k, g k = true → g (k+1) = true) :
    @Std.PRange.LawfulUpwardEnumerable Nat (signalRange g) := by
  letI := signalRange g
  constructor
  · intro a b
    rintro ⟨n, h⟩ rfl
    change stopAt g (a + (n+1)) = some a at h
    unfold stopAt at h
    split at h
    · cases h
    · exact Nat.ne_of_gt (Nat.lt_add_of_pos_right (Nat.zero_lt_succ n)) (Option.some.inj h)
  · intro; rfl
  · intro n a
    cases n with
    | zero => rfl
    | succ n =>
      change stopAt g (a + (n+1) + 1) = (stopAt g (a + (n+1))).bind (fun k => stopAt g (k+1))
      unfold stopAt
      cases h : g (a + (n+1)) with
      | false => rfl
      | true => rw [sticky _ h]; rfl

private theorem signalRangeFinite {g : Nat → Bool} (sticky : ∀ k, g k = true → g (k+1) = true)
    {n : Nat} (hit : g n = true) : @Rxi.IsAlwaysFinite Nat (signalRange g) := by
  letI := signalRange g
  constructor
  intro k
  refine ⟨n+1, ?_⟩
  change stopAt g (k + (n+1)) = none
  unfold stopAt
  rw [signal_after sticky hit (Nat.le_trans (Nat.le_succ n) (Nat.le_add_left ..))]
  rfl

/-- A right-unbounded range can enumerate a Boolean search up to its first signal. -/
def limitedOmniscienceFromUnboundedRange (loop : type_of% (@Rxi.Iterator.instIteratorLoop.{0,0}))
    (correct : ∀ [en : Std.PRange.UpwardEnumerable Nat] [law : Std.PRange.LawfulUpwardEnumerable Nat]
      [Rxi.IsAlwaysFinite Nat], @loop Nat en law Id _ = @Rxi.Iterator.instIteratorLoop Nat en law Id _)
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  let g := seen f
  letI := signalRange g
  letI := signalRangeLaw (seenSticky f)
  letI := @Rxi.instIteratorIteratorIdOfUpwardEnumerable Nat (signalRange g)
  let start (k : Nat) : Iter (α := Rxi.Iterator Nat) Nat := ⟨⟨stopAt g k⟩⟩
  let len (k : Nat) :=
    letI := @loop Nat (signalRange g) (signalRangeLaw (seenSticky f)) Id _
    (start k).length
  cases h : g (len 0) with
  | true => exact isTrue (hit_of_seen f _ h)
  | false =>
    refine isFalse fun ⟨n, hit⟩ => ?_
    have gHit := seen_of_hit f n hit
    letI := signalRangeFinite (seenSticky f) gHit
    have computed (k : Nat) : len k = (start k).toList.length := by
      unfold len
      have eq := congrArg (fun inst : IteratorLoop (Rxi.Iterator Nat) Id Id =>
        @Iter.length _ _ _ inst (start k)) (@correct (signalRange g) (signalRangeLaw (seenSticky f)) _)
      letI := @Rxi.Iterator.instIteratorLoop Nat (signalRange g) (signalRangeLaw (seenSticky f)) Id _
      exact eq.trans (@Iter.length_toList_eq_length _ _ _ _ (@Rxi.Iterator.instIteratorLoop Nat (signalRange g) (signalRangeLaw (seenSticky f)) Id _)
        (@Rxi.Iterator.instLawfulIteratorLoop Nat (signalRange g) (signalRangeLaw (seenSticky f)) Id _ _) (start k)).symm
    have unroll (k : Nat) : len k = (match g k with | true => 0 | false => (len (k+1)).succ) := by
      rw [computed, @Rxi.Iterator.toList_eq_match Nat (signalRange g) _ (signalRangeLaw (seenSticky f)) (start k)]
      dsimp only [start]
      cases e : g k with
      | false => simp only [stopAt, e, Bool.false_eq_true, ite_false]; exact congrArg Nat.succ (computed _).symm
      | true => simp only [stopAt, e, ite_true]; rfl
    have result := length_hits (seenSticky f) gHit len unroll 0
    exact Bool.noConfusion (h.symm.trans (by simpa only [Nat.zero_add] using result))

end Collector

end OmegaChecks.InitBoundaries
