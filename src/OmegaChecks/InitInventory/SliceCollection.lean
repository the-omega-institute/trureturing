module
public import OmegaChecks.InitInventory.Collector
public import OmegaChecks.InitInventory.Replay
meta import OmegaChecks.InitInventory.Replay
import all Init.Data.Iterators.Basic
import all Init.Data.Slice.Operations
import all Init.Data.Iterators.Lemmas.Consumers.Collect

/-! A decision for whether a Boolean stream ever signals supplies a total slice collector
that agrees with the pinned list and array collectors on finite input. -/

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

private def withFuel {α β : Type u} [Iterator α Id β] (n : Nat) (it : Iter (α := α) β) : Option (List β) :=
  match n with
  | 0 => none
  | n + 1 =>
    match nextStep it with
    | .done => some []
    | .skip next => withFuel n next
    | .yield next out => (withFuel n next).map (out :: ·)

private theorem finiteCompletes {α β : Type u} [Iterator α Id β] [Finite α Id] (it : Iter (α := α) β) :
    ∃ n, withFuel n it = some it.toList := by
  induction it using Iter.inductSteps with
  | step it yields skips =>
    have nextEq : nextStep it = it.step.val := rfl
    rw [Iter.toList_eq_match_step]
    generalize h : it.step = s
    cases s using PlausibleIterStep.casesOn with
    | done _ =>
      exact ⟨1, by simp only [withFuel, nextEq, h]⟩
    | skip next hs =>
      obtain ⟨n, hn⟩ := skips hs
      exact ⟨n + 1, by simp only [withFuel, nextEq, h]; exact hn⟩
    | yield next out hy =>
      obtain ⟨n, hn⟩ := yields hy
      exact ⟨n + 1, by simp only [withFuel, nextEq, h]; exact congrArg (Option.map (out :: ·)) hn⟩

private theorem stable {α β : Type u} [Iterator α Id β] (n : Nat)
    (it : Iter (α := α) β) {xs} (done : withFuel n it = some xs) (extra : Nat) :
    withFuel (n + extra) it = some xs := by
  induction n generalizing it xs with
  | zero => cases done
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [withFuel] at done ⊢
    cases step : nextStep it with
    | done => simpa only [step] using done
    | skip next =>
      rw [step] at done
      exact ih next done
    | yield next out =>
      simp only [step] at done
      cases tail : withFuel n next with
      | none => rw [tail] at done; cases done
      | some ys =>
        rw [tail] at done
        exact (congrArg (Option.map (out :: ·)) (ih next tail)).trans done

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
  let flag := fun n => (withFuel n it).isSome
  match dec flag with
  | .isFalse _ => []
  | .isTrue h => (withFuel (findSignal flag h).val it).getD []

private theorem collectCompleted {α β : Type u} [Iterator α Id β]
    (dec : StreamDecision) (it : Iter (α := α) β)
    (n : Nat) {xs : List β} (done : withFuel n it = some xs) :
    collectWithDecision dec it = xs := by
  unfold collectWithDecision
  dsimp only
  cases dec (fun k => (withFuel k it).isSome) with
  | isFalse no => exact False.elim (no ⟨n, by rw [done]; rfl⟩)
  | isTrue yes =>
    let w := findSignal (fun k => (withFuel k it).isSome) yes
    have hits := w.property
    change (withFuel w.val it).isSome = true at hits
    change (withFuel w.val it).getD [] = _
    cases found : withFuel w.val it with
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

open Lean Elab.Command in
run_cmd
  let official ← importModules #[{module := `Init}] {} (level := .private)
  discard <| replayBoundaryDependencies official (← getEnv)
    [``sliceListOfStreamDecision, ``sliceArrayOfStreamDecision, ``collectCompleted]

end OmegaChecks.InitBoundaries.Collector
