/- GID: D5/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Option.Basic]
   utility: none
   digest: Typed partial labelled path views refine to full behavior at any plateau. -/

import Mathlib.Data.Option.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.RefinementClosure.TypedFiniteViewKernel

universe u v w x y

variable {I : Type u} (Edge : I → I → Type v)

/-- A finite composable word of named edges, ordered by execution. -/
inductive Path : I → I → Type (max u v)
  | nil {i : I} : Path i i
  | cons {i j k : I} : Path j k → Edge i j → Path i k

/-- Number of edges in a finite word. -/
def Path.length : {i j : I} → Path Edge i j → Nat
  | _, _, .nil => 0
  | _, _, .cons p _ => p.length + 1

variable {Edge} (Label : {i j : I} → Edge i j → Type w)

/-- The ordered tuple of labels, with the type of each coordinate fixed by
its named edge. The empty path carries no label. -/
def Labels : {i j : I} → Path Edge i j → Type w
  | _, _, .nil => PUnit
  | _, _, .cons p e => Label e × Labels p

variable {S : I → Type x} {O : I → Type y}
  (q : (i : I) → S i → O i)
  (step : {i j : I} → (e : Edge i j) → S i → Option (Label e × S j))

/-- Execute an independently specified finite path. `none` means that the
path is illegal, and is never a successor state. A successful response retains
the entire label tuple and the terminal typed readout. -/
def response : {i j : I} → (p : Path Edge i j) → S i →
    Option (Labels Label p × O j)
  | _, _, .nil, s => some (PUnit.unit, q _ s)
  | _, _, .cons p e, s =>
      (step e s).bind fun next =>
        (response p next.2).map fun tail => ((next.1, tail.1), tail.2)

/-- The depth bound restricts the independently executable paths, including
every prefix and the empty path. The outer tag retains the starting type. -/
def finiteView (n : Nat) (s : Sigma S) :
    Σ i, (j : I) → (p : Path Edge i j) → p.length ≤ n →
      Option (Labels Label p × O j) :=
  ⟨s.1, fun _ p _ => response Label q step p s.2⟩

/-- Complete behavior records responses to all finite paths, with no bound
on length or branching. It is independent of the refinement relations. -/
def behavior (s : Sigma S) :
    Σ i, (j : I) → (p : Path Edge i j) → Option (Labels Label p × O j) :=
  ⟨s.1, fun _ p => response Label q step p s.2⟩

/-- Refinement inside a type: equal roots, simultaneous edge legality,
equal labels, and recursively related successors. -/
def refinement : Nat → (i : I) → S i → S i → Prop
  | 0, i, s, t => q i s = q i t
  | n + 1, i, s, t => q i s = q i t ∧
      ∀ (j : I) (e : Edge i j),
        match step e s, step e t with
        | none, none => True
        | some a, some b => a.1 = b.1 ∧ refinement n j a.2 b.2
        | _, _ => False

/-- Lift the recurrence to the full disjoint union, requiring equal type
tags before comparing the states in the corresponding fiber. -/
def E (n : Nat) (s t : Sigma S) : Prop :=
  ∃ h : s.1 = t.1, refinement Label q step n t.1 (h ▸ s.2) t.2

/-- Equality of complete finite-path behaviors on the full disjoint union. -/
def behaviorKernel (s t : Sigma S) : Prop :=
  behavior Label q step s = behavior Label q step t

/-- Finite refinement is precisely independent path-view equality; the
relations descend and intersect to the complete behavior kernel. One plateau
already equals that kernel and persists at every later depth. -/
theorem typed_finite_view_kernel :
    (∀ n s t, E Label q step n s t ↔
      finiteView Label q step n s = finiteView Label q step n t) ∧
    (∀ n s t, E Label q step (n + 1) s t → E Label q step n s t) ∧
    (behaviorKernel Label q step = fun s t => ∀ n, E Label q step n s t) ∧
    (∀ n, E Label q step n = E Label q step (n + 1) →
      E Label q step n = behaviorKernel Label q step ∧
        ∀ k, E Label q step (n + k) = E Label q step n) := by
  have path_iff : ∀ n i (s t : S i),
      refinement Label q step n i s t ↔
        ∀ j (p : Path Edge i j), p.length ≤ n →
          response Label q step p s = response Label q step p t := by
    intro n
    induction n with
    | zero =>
        intro i s t
        constructor
        · intro h j p hp
          cases p with
          | nil => exact congrArg (fun o : O i => some (PUnit.unit, o)) h
          | cons p e => simp [Path.length] at hp
        · intro h
          exact congrArg Prod.snd (Option.some.inj (h i .nil (Nat.zero_le 0)))
    | succ n ih =>
        intro i s t
        constructor
        · rintro ⟨root, edges⟩ j p hp
          cases p with
          | nil => simp [response, root]
          | @cons _ k _ p e =>
              have tailBound : p.length ≤ n := Nat.le_of_succ_le_succ hp
              have he := edges k e
              cases hs : step e s with
              | none =>
                  cases ht : step e t with
                  | none => simp [response, hs, ht]
                  | some b => simp [hs, ht] at he
              | some a =>
                  cases ht : step e t with
                  | none => simp [hs, ht] at he
                  | some b =>
                      simp only [hs, ht] at he
                      have tails := (ih k a.2 b.2).1 he.2 j p tailBound
                      simp [response, hs, ht, tails, he.1]
        · intro views
          refine ⟨?_, ?_⟩
          · exact congrArg Prod.snd (Option.some.inj (views i .nil (Nat.zero_le _)))
          · intro j e
            have one := views j (.cons .nil e) (Nat.succ_le_succ (Nat.zero_le n))
            cases hs : step e s with
            | none =>
                cases ht : step e t with
                | none => simp [hs, ht]
                | some b => simp [response, hs, ht] at one
            | some a =>
                cases ht : step e t with
                | none => simp [response, hs, ht] at one
                | some b =>
                    have labelEq : a.1 = b.1 := by
                      simpa [response, hs, ht] using congrArg
                        (fun r => r.map (fun z => z.1.1)) one
                    simp only [hs, ht]
                    refine ⟨labelEq, (ih j a.2 b.2).2 ?_⟩
                    intro k p hp
                    have longer := views k (.cons p e) (Nat.succ_le_succ hp)
                    have strip := congrArg
                      (fun r => r.map (fun z => (z.1.2, z.2))) longer
                    simpa [response, hs, ht, Option.map_map, Function.comp_def] using strip
  have fiber_view : ∀ n i (s t : S i),
      E Label q step n ⟨i, s⟩ ⟨i, t⟩ ↔
        ∀ j (p : Path Edge i j), p.length ≤ n →
          response Label q step p s = response Label q step p t := by
    intro n i s t
    simpa [E] using path_iff n i s t
  have finite_eq : ∀ n s t, E Label q step n s t ↔
      finiteView Label q step n s = finiteView Label q step n t := by
    intro n ⟨i, s⟩ ⟨j, t⟩
    constructor
    · rintro ⟨h, hr⟩
      cases h
      apply congrArg (Sigma.mk i)
      funext k p hp
      exact (path_iff n i s t).1 hr k p hp
    · intro h
      have hij := congrArg Sigma.fst h
      change i = j at hij
      cases hij
      have hf := Sigma.mk.inj h
      have same := eq_of_heq hf.2
      apply (fiber_view n i s t).2
      intro k p hp
      exact congrFun (congrFun (congrFun same k) p) hp
  have descend : ∀ n s t, E Label q step (n + 1) s t → E Label q step n s t := by
    intro n ⟨i, s⟩ ⟨j, t⟩ ⟨h, hr⟩
    cases h
    apply (fiber_view n i s t).2
    intro k p hp
    exact (path_iff (n + 1) i s t).1 hr k p (Nat.le_trans hp (Nat.le_succ n))
  have all_paths : ∀ s t, behaviorKernel Label q step s t ↔
      ∀ n, E Label q step n s t := by
    intro ⟨i, s⟩ ⟨j, t⟩
    constructor
    · intro h
      have hij := congrArg Sigma.fst h
      change i = j at hij
      cases hij
      have same := eq_of_heq (Sigma.mk.inj h).2
      intro n
      apply (fiber_view n i s t).2
      intro k p _
      exact congrFun (congrFun same k) p
    · intro h
      obtain ⟨hij, _⟩ := h 0
      cases hij
      apply congrArg (Sigma.mk i)
      funext k p
      exact (fiber_view p.length i s t).1 (h p.length) k p (Nat.le_refl _)
  refine ⟨finite_eq, descend, ?_, ?_⟩
  · funext s t
    exact propext (all_paths s t)
  · intro n plateau
    have stable : ∀ k, E Label q step (n + k) = E Label q step n := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
          funext s t
          rcases s with ⟨i, s⟩
          rcases t with ⟨j, t⟩
          have same_fiber : ∀ j (a b : S j),
              refinement Label q step (n + k) j a b ↔
                refinement Label q step n j a b := by
            intro j a b
            have h := congrFun (congrFun ih ⟨j, a⟩) ⟨j, b⟩
            simpa [E] using Iff.of_eq h
          have next : E Label q step (n + k + 1) ⟨i, s⟩ ⟨j, t⟩ ↔
              E Label q step (n + 1) ⟨i, s⟩ ⟨j, t⟩ := by
            unfold E
            apply exists_congr
            intro hij
            cases hij
            simp only [refinement]
            apply and_congr_right
            intro _
            apply forall_congr'
            intro l
            apply forall_congr'
            intro e
            cases step e s <;> cases step e t <;> simp [same_fiber]
          exact propext
            (next.trans (Iff.of_eq (congrFun (congrFun plateau ⟨i, s⟩) ⟨j, t⟩)).symm)
    refine ⟨?_, stable⟩
    funext s t
    apply propext
    rw [all_paths]
    constructor
    · intro h m
      by_cases hnm : n ≤ m
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
        rwa [stable k]
      · have hmn : m ≤ n := Nat.le_of_not_ge hnm
        have lower : ∀ d, ∀ s t, E Label q step (m + d) s t → E Label q step m s t := by
          intro d
          induction d with
          | zero => intro s t h; exact h
          | succ d ih => intro s t h; exact ih s t (descend (m + d) s t h)
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
        exact lower d s t h
    · intro h
      exact h n

#print axioms typed_finite_view_kernel

end D5.S3.ObserverMemory.RefinementClosure.TypedFiniteViewKernel
