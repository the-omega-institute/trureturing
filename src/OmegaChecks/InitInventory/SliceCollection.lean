module
public import OmegaChecks.InitInventory.Collector
import all OmegaChecks.InitInventory.Collector
public import OmegaChecks.InitInventory.Replay
meta import OmegaChecks.InitInventory.Replay
import all Init.Data.Iterators.Basic
import all Init.Data.Iterators.ToIterator
import all Init.Data.Slice.Operations
import all Init.Data.Iterators.Lemmas.Consumers.Collect

/-! A decision for whether a Boolean stream ever signals supplies a total slice collector
whose length, list, reversed list and array agree with the pinned operations on finite input. -/

public section
open Std Std.Iterators

namespace OmegaChecks.InitBoundaries.Collector

abbrev StreamDecision := (f : Nat → Bool) → Decidable (∃ n, f n = true)

/-- Read the data of the pinned step directly from the stored iterator value. -/
private def nextStep {α β : Type u} [Iterator α Id β] (it : Iter (α := α) β) :
    IterStep (Iter (α := α) β) β :=
  let raw : it.toIterM.Step :=
    cast (congrFun (Std.Internal.idOpaque (α := Type u)).property _) it.toIterM.step
  raw.val.mapIterator IterM.toIter

/-- Perform at most the indicated number of iterator steps and return all outputs upon termination. -/
def collectWithFuel {α β : Type u} [Iterator α Id β] (n : Nat) (it : Iter (α := α) β) : Option (List β) :=
  match n with
  | 0 => none
  | n + 1 =>
    match nextStep it with
    | .done => some []
    | .skip next => collectWithFuel n next
    | .yield next out => (collectWithFuel n next).map (out :: ·)

private theorem finiteCompletes {α β : Type u} [Iterator α Id β] [Finite α Id] (it : Iter (α := α) β) :
    ∃ n, collectWithFuel n it = some it.toList := by
  induction it using Iter.inductSteps with
  | step it yields skips =>
    have nextEq : nextStep it = it.step.val := rfl
    rw [Iter.toList_eq_match_step]
    generalize h : it.step = s
    cases s using PlausibleIterStep.casesOn with
    | done _ =>
      exact ⟨1, by simp only [collectWithFuel, nextEq, h]⟩
    | skip next hs =>
      obtain ⟨n, hn⟩ := skips hs
      exact ⟨n + 1, by simp only [collectWithFuel, nextEq, h]; exact hn⟩
    | yield next out hy =>
      obtain ⟨n, hn⟩ := yields hy
      exact ⟨n + 1, by simp only [collectWithFuel, nextEq, h]; exact congrArg (Option.map (out :: ·)) hn⟩

private theorem stable {α β : Type u} [Iterator α Id β] (n : Nat)
    (it : Iter (α := α) β) {xs} (done : collectWithFuel n it = some xs) (extra : Nat) :
    collectWithFuel (n + extra) it = some xs := by
  induction n generalizing it xs with
  | zero => cases done
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [collectWithFuel] at done ⊢
    cases step : nextStep it with
    | done => simpa only [step] using done
    | skip next =>
      rw [step] at done
      exact ih next done
    | yield next out =>
      simp only [step] at done
      cases tail : collectWithFuel n next with
      | none => rw [tail] at done; cases done
      | some ys =>
        rw [tail] at done
        exact (congrArg (Option.map (out :: ·)) (ih next tail)).trans done

private theorem searchNext (g : Nat → Bool) (k : Nat) :
    letI := searchIterator g
    nextStep (search k) = (match g k with | true => .done | false => .yield (search (k+1)) ()) := by
  letI := searchIterator g
  dsimp only [nextStep, IterM.step, searchIterator, Iterator.step, search, Iter.toIterM, pure, Id.instMonad]
  set_option backward.isDefEq.respectTransparency false in
    rw [cast_cast, cast_eq]
  dsimp only [Subtype.val, next]
  cases g k <;> rfl

private theorem searchOutput (g : Nat → Bool) (distance k : Nat) (hit : g (k + distance) = true) :
    letI := searchIterator g
    ∃ fuel xs, collectWithFuel fuel (search k) = some xs ∧ g (k + xs.length) = true := by
  letI := searchIterator g
  have stop (k : Nat) (yes : g k = true) :
      collectWithFuel 1 (search k) = some ([] : List Unit) := by
    rw [collectWithFuel, searchNext, yes]
  induction distance generalizing k with
  | zero => exact ⟨1, [], stop k hit, hit⟩
  | succ distance ih =>
    cases here : g k with
    | true => exact ⟨1, [], stop k here, here⟩
    | false =>
      have there : g ((k + 1) + distance) = true := (congrArg g (Nat.succ_add k distance)).trans hit
      obtain ⟨fuel, xs, done, found⟩ := ih (k + 1) there
      refine ⟨fuel + 1, () :: xs, ?_, ?_⟩
      · rw [collectWithFuel, searchNext, here]
        exact congrArg (Option.map (() :: ·)) done
      · exact (congrArg g (Nat.succ_add k xs.length).symm).trans found

/-- A total size observation that counts each finite traversal with a completed fuel run
determines whether an arbitrary Boolean stream signals. -/
def decideFromCompletedSliceLength
    (measure : ∀ {γ α β : Type} [ToIterator (Slice γ) Id α β] [Iterator α Id β], Slice γ → Nat)
    (correct : ∀ {γ α β : Type} [ToIterator (Slice γ) Id α β] [Iterator α Id β] [Finite α Id]
      (s : Slice γ) (fuel : Nat) (xs : List β),
      collectWithFuel fuel (ToIterator.iter s) = some xs → measure s = xs.length)
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  let g := seen f
  letI := searchIterator g
  letI := ToIterator.of (γ := Slice (Iter (α := Nat) Unit)) Nat (fun s => s.internalRepresentation)
  let s : Slice (Iter (α := Nat) Unit) := ⟨search 0⟩
  cases atSize : g (measure s) with
  | true => exact .isTrue (hit_of_seen f _ atSize)
  | false =>
    refine .isFalse fun ⟨n, found⟩ => ?_
    have hit := seen_of_hit f n found
    letI := searchFinite (seenSticky f) hit
    obtain ⟨fuel, xs, done, yes⟩ := searchOutput g n 0 ((congrArg g (Nat.zero_add n)).trans hit)
    have measured := correct s fuel xs done
    exact Bool.noConfusion (atSize.symm.trans ((congrArg g measured).trans
      ((congrArg g (Nat.zero_add xs.length).symm).trans yes)))

/-- The first signal is found by a constructive search once eventual success is known. -/
private noncomputable def findSignal (f : Nat → Bool) (h : ∃ n, f n = true) : {n // f n = true} := by
  let R := fun (j i : Nat) => j = i + 1 ∧ f i = false
  have terminates : Acc R 0 := by
    obtain ⟨n, yes⟩ := h
    have reachable (d j : Nat) (eq : j + d = n) : Acc R j := by
      induction d generalizing j with
      | zero =>
        have hj : j = n := eq
        constructor
        rintro _ ⟨_, no⟩
        exact False.elim (Bool.noConfusion (yes.symm.trans (hj ▸ no)))
      | succ d ih =>
        constructor
        rintro _ ⟨rfl, _⟩
        exact ih _ (by rwa [Nat.succ_add])
    exact reachable n 0 (Nat.zero_add _)
  exact WellFounded.fixF (C := fun _ => {n // f n = true})
    (fun i go => match yes : f i with
      | true => ⟨i, yes⟩
      | false => go (i + 1) ⟨rfl, yes⟩) 0 terminates

private noncomputable def collectWithDecision {α β : Type u} [Iterator α Id β]
    (dec : StreamDecision) (it : Iter (α := α) β) : List β :=
  let flag := fun n => (collectWithFuel n it).isSome
  match dec flag with
  | .isFalse _ => []
  | .isTrue h => (collectWithFuel (findSignal flag h).val it).getD []

private theorem collectCompleted {α β : Type u} [Iterator α Id β]
    (dec : StreamDecision) (it : Iter (α := α) β)
    (n : Nat) {xs : List β} (done : collectWithFuel n it = some xs) :
    collectWithDecision dec it = xs := by
  unfold collectWithDecision
  dsimp only
  cases dec (fun k => (collectWithFuel k it).isSome) with
  | isFalse no => exact False.elim (no ⟨n, by rw [done]; rfl⟩)
  | isTrue yes =>
    let w := findSignal (fun k => (collectWithFuel k it).isSome) yes
    have hits := w.property
    change (collectWithFuel w.val it).isSome = true at hits
    change (collectWithFuel w.val it).getD [] = _
    cases found : collectWithFuel w.val it with
    | none => rw [found] at hits; cases hits
    | some ys =>
      have left := stable w.val it found n
      rw [Nat.add_comm] at left
      exact Option.some.inj (left.symm.trans (stable n it done w.val))

private theorem collectWithDecision_eq {α β : Type u} [Iterator α Id β] [Finite α Id]
    (dec : StreamDecision) (it : Iter (α := α) β) :
    collectWithDecision dec it = it.toList := by
  obtain ⟨n, done⟩ := finiteCompletes it
  exact collectCompleted dec it n done

/-- The list collector returns the recorded output of a terminating traversal and defaults to an empty list otherwise. -/
noncomputable def sliceListOfStreamDecision (dec : StreamDecision) : type_of% (@Std.Slice.toList.{u,v}) :=
  fun s => collectWithDecision dec (ToIterator.iter s)

noncomputable def sliceArrayOfStreamDecision (dec : StreamDecision) : type_of% (@Std.Slice.toArray.{u,v}) :=
  fun s => (sliceListOfStreamDecision dec s).toArray

noncomputable def sliceReverseOfStreamDecision (dec : StreamDecision) : type_of% (@Std.Slice.toListRev.{u,v}) :=
  fun s => (sliceListOfStreamDecision dec s).reverse

noncomputable def sliceLengthOfStreamDecision (dec : StreamDecision) {γ : Type u} {α β : Type v}
    [ToIterator (Slice γ) Id α β] [Iterator α Id β] (s : Slice γ) : Nat :=
  (sliceListOfStreamDecision dec s).length

/-- On finite iterators the selected result satisfies the original list-valued agreement. -/
theorem sliceListOfStreamDecision_eq (dec : StreamDecision) {γ : Type u} {α β : Type v}
    [ToIterator (Slice γ) Id α β] [Iterator α Id β] [Finite α Id] (s : Slice γ) :
    sliceListOfStreamDecision dec s = s.toList :=
  collectWithDecision_eq dec (ToIterator.iter s)

/-- Conversion to an array preserves the original array-valued agreement. -/
theorem sliceArrayOfStreamDecision_eq (dec : StreamDecision) {γ : Type u} {α β : Type v}
    [ToIterator (Slice γ) Id α β] [Iterator α Id β] [Finite α Id] (s : Slice γ) :
    sliceArrayOfStreamDecision dec s = s.toArray :=
  (congrArg List.toArray (collectWithDecision_eq dec (ToIterator.iter s))).trans Iter.toArray_toList

theorem sliceReverseOfStreamDecision_eq (dec : StreamDecision) {γ : Type u} {α β : Type v}
    [ToIterator (Slice γ) Id α β] [Iterator α Id β] [Finite α Id] (s : Slice γ) :
    sliceReverseOfStreamDecision dec s = s.toListRev :=
  (congrArg List.reverse (collectWithDecision_eq dec (ToIterator.iter s))).trans Iter.toListRev_eq.symm

theorem sliceLengthOfStreamDecision_eq (dec : StreamDecision) {γ : Type u} {α β : Type v}
    [ToIterator (Slice γ) Id α β] [Iterator α Id β] [Finite α Id] (s : Slice γ) :
    sliceLengthOfStreamDecision dec s = s.toList.length :=
  congrArg List.length (sliceListOfStreamDecision_eq dec s)

/-- When the iterator is finite, the original field can be constructed and consumed using the total collector. -/
theorem lawfulSliceSizeIffFiniteLength {γ : Type u} {α β : Type v}
    [Slice.SliceSize γ] [ToIterator (Slice γ) Id α β] [Iterator α Id β] [Finite α Id] :
    Slice.LawfulSliceSize γ ↔ ∀ s : Slice γ, s.size = (ToIterator.iter s).ensureTermination.toList.length := by
  letI : IteratorLoop α Id Id := .defaultImplementation
  constructor
  · intro h s
    rw [Iter.toList_ensureTermination]
    exact (h.lawful s).trans (Iter.length_toList_eq_length (it := ToIterator.iter s)).symm
  · intro h
    refine ⟨fun s => (h s).trans ?_⟩
    rw [Iter.toList_ensureTermination]
    exact Iter.length_toList_eq_length

/-- A completed prefix determines the length chosen with a stream decision, including when global
finiteness of the underlying iterator has not been established. -/
theorem sliceLengthOfStreamDecision_of_completed (dec : StreamDecision) {γ : Type u} {α β : Type v}
    [ToIterator (Slice γ) Id α β] [Iterator α Id β] (s : Slice γ)
    (fuel : Nat) {xs : List β} (done : collectWithFuel fuel (ToIterator.iter s) = some xs) :
    sliceLengthOfStreamDecision dec s = xs.length :=
  congrArg List.length (collectCompleted dec (ToIterator.iter s) fuel done)

/-- Existence of a total size observation that is correct for finite traversals is equivalent
to existence of a decision for the occurrence of a signal in each Boolean stream. -/
theorem streamDecisionIffSliceLength : Nonempty StreamDecision ↔
    ∃ measure : ∀ {γ α β : Type} [ToIterator (Slice γ) Id α β] [Iterator α Id β], Slice γ → Nat,
      ∀ {γ α β : Type} [ToIterator (Slice γ) Id α β] [Iterator α Id β] [Finite α Id]
        (s : Slice γ) (fuel : Nat) (xs : List β),
        collectWithFuel fuel (ToIterator.iter s) = some xs → measure s = xs.length := by
  constructor
  · rintro ⟨dec⟩
    exact ⟨@sliceLengthOfStreamDecision dec,
      fun s fuel _ done => sliceLengthOfStreamDecision_of_completed dec s fuel done⟩
  · rintro ⟨measure, correct⟩
    exact ⟨decideFromCompletedSliceLength (@measure) (@correct)⟩

open Lean Elab.Command in
run_cmd
  let official ← importModules #[{module := `Init}] {} (level := .private)
  discard <| replayBoundaryDependencies official (← getEnv)
    [``sliceListOfStreamDecision, ``sliceArrayOfStreamDecision, ``sliceReverseOfStreamDecision,
     ``sliceLengthOfStreamDecision, ``collectCompleted, ``streamDecisionIffSliceLength]

end OmegaChecks.InitBoundaries.Collector
