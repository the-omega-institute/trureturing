/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeCompletionPrefixLifting
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Native infinite-tree prefixes admit simultaneous finite separation. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation
import Mathlib.Data.PFunctor.Univariate.M

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout)
open NativeDepthPatterns (Pattern Frontier fill decompose depthEquiv)
open NativeUniformResidualRealization (RankedExpr)
open NativeSimultaneousPrefixSeparation (fixedEval prefixTuple simultaneous_prefix_separation)

/-- Native leaves have no children; an ordered branch has its two Bool children. -/
def completionFunctor : PFunctor.{0,0} where
  A := Bool ⊕ Unit
  B := fun a => match a with
    | .inl _ => Empty
    | .inr _ => Bool

/-- The unrestricted final coalgebra includes finite and arbitrary infinite trees. -/
abbrev CompletionTree := PFunctor.M completionFunctor

def leaf (b : Bool) : CompletionTree := PFunctor.M.mk ⟨.inl b, Empty.elim⟩

def node (l r : CompletionTree) : CompletionTree :=
  PFunctor.M.mk ⟨.inr (), fun b : Bool => if b then r else l⟩

/-- Every address is observed. Invalid descendants return absent, never a default label. -/
def completionReadout : Address → CompletionTree → Reply
  | [], t => match PFunctor.M.dest t with
    | ⟨.inl b, _⟩ => if b then .alpha else .beta
    | ⟨.inr _, _⟩ => .branch
  | b :: a, t => match PFunctor.M.dest t with
    | ⟨.inl _, _⟩ => .absent
    | ⟨.inr _, children⟩ => completionReadout a (children b)

/-- Embed the existing finite Source without changing either leaf label or child order. -/
def embed : Source → CompletionTree
  | .of b => leaf b
  | .mul l r => node (embed l) (embed r)

/-- Cut at depth d; only reached positions at exactly depth d remain holes. -/
def cutoff : (d : Nat) → CompletionTree → Pattern d
  | 0, _ => ()
  | d + 1, t => match PFunctor.M.dest t with
    | ⟨.inl b, _⟩ => .inl b
    | ⟨.inr _, children⟩ => .inr (cutoff d (children false), cutoff d (children true))

/-- A supplied actual branch, with every finite initial word present. -/
def HasInfiniteBranch (t : CompletionTree) : Prop :=
  ∃ b : Nat → Bool, ∀ d : Nat,
    completionReadout (List.ofFn (fun i : Fin d => b i.val)) t ≠ .absent

theorem tree_cases {R : CompletionTree → Prop} (T : CompletionTree)
    (leaf_case : ∀ b, R (leaf b)) (node_case : ∀ l r, R (node l r)) : R T := by
  refine PFunctor.M.casesOn' T ?_
  intro a g
  cases a with
  | inl b =>
      have he : g = Empty.elim := funext fun e => Empty.elim e
      rw [he]
      exact leaf_case b
  | inr u =>
      cases u
      have he : g = (fun b : Bool => if b then g true else g false) := by
        funext b; cases b <;> rfl
      rw [he]
      exact node_case (g false) (g true)

theorem embed_readout (a : Address) (t : Source) :
    completionReadout a (embed t) = readout a t := by
  induction a generalizing t with
  | nil => cases t with
    | of b => cases b <;> simp [embed, leaf, completionReadout, readout]
    | mul l r => simp [embed, node, completionReadout, readout]
  | cons b a ih => cases t with
    | of c => simp [embed, leaf, completionReadout, readout]
    | mul l r => cases b <;> simp [embed, node, completionReadout, readout, ih]

private theorem cutoff_embed (d : Nat) (t : Source) :
    cutoff d (embed t) = (decompose d t).1 := by
  induction d generalizing t with
  | zero => rfl
  | succ d ih => cases t with
    | of b => simp [cutoff, embed, leaf, decompose]
    | mul l r =>
        change Sum.inr (cutoff d (embed l), cutoff d (embed r)) =
          Sum.inr ((decompose d l).1, (decompose d r).1)
        rw [ih, ih]

private theorem cutoff_readout (d : Nat) (S T : CompletionTree) :
    cutoff d S = cutoff d T ↔
      ∀ a : Address, a.length < d → completionReadout a S = completionReadout a T := by
  induction d generalizing S T with
  | zero => simp [cutoff]
  | succ d ih =>
      induction S using tree_cases with
      | leaf_case b =>
          induction T using tree_cases with
          | leaf_case c =>
              change (Sum.inl b : Bool ⊕ (Pattern d × Pattern d)) = Sum.inl c ↔ _
              rw [Sum.inl.injEq]
              constructor
              · rintro rfl a ha; rfl
              · intro h
                have root := h [] (by simp)
                cases b <;> cases c <;> simp [completionReadout, leaf] at root ⊢
          | node_case l r =>
              change (Sum.inl b : Bool ⊕ (Pattern d × Pattern d)) =
                Sum.inr (cutoff d l, cutoff d r) ↔ _
              constructor
              · intro no; cases no
              · intro h
                have root := h [] (by simp)
                cases b <;> simp [completionReadout, leaf, node] at root
      | node_case l r =>
          induction T using tree_cases with
          | leaf_case b =>
              change (Sum.inr (cutoff d l, cutoff d r) : Bool ⊕ (Pattern d × Pattern d)) =
                Sum.inl b ↔ _
              constructor
              · intro no; cases no
              · intro h
                have root := h [] (by simp)
                cases b <;> simp [completionReadout, leaf, node] at root
          | node_case l' r' =>
              change (Sum.inr (cutoff d l, cutoff d r) : Bool ⊕ (Pattern d × Pattern d)) =
                Sum.inr (cutoff d l', cutoff d r') ↔ _
              rw [Sum.inr.injEq, Prod.mk.injEq, ih, ih]
              constructor
              · rintro ⟨hl, hr⟩ a ha
                cases a with
                | nil => simp [completionReadout, node]
                | cons b a =>
                    have ha' : a.length < d := by simpa using ha
                    cases b <;> simp [completionReadout, node, hl a ha', hr a ha']
              · intro h
                constructor
                · intro a ha
                  simpa [completionReadout, node] using h (false :: a) (by simpa using ha)
                · intro a ha
                  simpa [completionReadout, node] using h (true :: a) (by simpa using ha)

/-- Both directions of the exact finite prefix cylinder. The prescribed table
includes absent addresses and every early leaf, not only existing-node labels. -/
theorem prefix_cylinder (h : Nat) (T : CompletionTree) (t : Source) :
    (∀ a : Address, a.length ≤ h → readout a t = completionReadout a T) ↔
      ∃ f : Frontier (cutoff (h+1) T) → Source,
      t = fill (cutoff (h+1) T) f := by
  have eq : (∀ a : Address, a.length ≤ h → readout a t = completionReadout a T) ↔
      (decompose (h+1) t).1 = cutoff (h+1) T := by
    rw [← cutoff_embed, cutoff_readout]
    simp only [embed_readout, Nat.lt_succ_iff]
  rw [eq]
  constructor
  · intro hp
    have back := (depthEquiv (h+1)).symm_apply_apply t
    change fill (decompose (h+1) t).1 (decompose (h+1) t).2 = t at back
    cases ht : decompose (h+1) t with
    | mk p f =>
        rw [ht] at hp back
        dsimp only at hp back
        subst p
        exact ⟨f, back.symm⟩
  · rintro ⟨f, rfl⟩
    exact congrArg Sigma.fst ((depthEquiv (h+1)).apply_symm_apply ⟨cutoff (h+1) T, f⟩)

private theorem frontier_of_present (d : Nat) (T : CompletionTree) (a : Address)
    (length : a.length = d) (present : completionReadout a T ≠ .absent) :
    Nonempty (Frontier (cutoff d T)) := by
  induction d generalizing T a with
  | zero => exact ⟨()⟩
  | succ d ih =>
      cases a with
      | nil => simp at length
      | cons b a =>
          have length' : a.length = d := by simpa using length
          induction T using tree_cases with
          | leaf_case c => simp [completionReadout, leaf] at present
          | node_case l r =>
              cases b
              · have live := ih l a length' (by simpa [completionReadout, node] using present)
                obtain ⟨x⟩ := live
                exact ⟨Sum.inl x⟩
              · have live := ih r a length' (by simpa [completionReadout, node] using present)
                obtain ⟨x⟩ := live
                exact ⟨Sum.inr x⟩

private theorem infinite_frontier (d : Nat) (T : CompletionTree) (infinite : HasInfiniteBranch T) :
    Nonempty (Frontier (cutoff d T)) := by
  obtain ⟨b, branch⟩ := infinite
  exact frontier_of_present d T (List.ofFn (fun i : Fin d => b i.val)) (by simp) (branch d)

/-- Signed Local Prefix lifting: one finite tuple simultaneously avoids the entire
list while retaining arbitrary independent complete prefixes of actual infinite
completion trees. Fixed finite coordinates, shared names and ranks are unchanged. -/
theorem simultaneous_prefix_disequality (k r m : Nat)
    (pairs : List (RankedExpr k (r + m) × RankedExpr k (r + m)))
    (n : Fin k → Nat) (f : Fin r → Source)
    (witness : ∃ z : Fin m → Source, ∀ e ∈ pairs,
      fixedEval n f z e.1 ≠ fixedEval n f z e.2)
    (T : Fin m → CompletionTree) (infinite : ∀ i, HasInfiniteBranch (T i))
    (h : Fin m → Nat) :
    ∃ z : Fin m → Source, (∀ (i : Fin m) (a : Address), a.length ≤ h i →
      readout a (z i) = completionReadout a (T i)) ∧
      ∀ e ∈ pairs, fixedEval n f z e.1 ≠ fixedEval n f z e.2 := by
  let d : Fin m → Nat := fun i => h i + 1
  let p : (i : Fin m) → Pattern (d i) := fun i => cutoff (d i) (T i)
  have live : ∀ i, Nonempty (Frontier (p i)) := fun i => infinite_frontier (d i) (T i) (infinite i)
  obtain ⟨w, hw⟩ := witness
  have separated := (simultaneous_prefix_separation k r m pairs (fun _ => True) n f d p live).mp
    ⟨w, trivial, hw⟩
  refine ⟨prefixTuple n f d p pairs, ?_, separated.2.2⟩
  intro i
  apply (prefix_cylinder (h i) (T i) _).mpr
  refine ⟨fun x => NativeUniformResidualRealization.uniformSeparator
    (NativeSimultaneousPrefixSeparation.expandedList n f d p pairs)
    (NativeSimultaneousPrefixSeparation.holeNumbering d p ⟨i, x⟩), rfl⟩

#print axioms prefix_cylinder
#print axioms simultaneous_prefix_disequality

end D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
