/- GID: D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/TotalCopyNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict total copy trees normalize exactly and yield total native one-hole zero slices. -/

import D5.S3.ConceptDynamics.Spacetime.LeafSquareReadout
import D5.S3.ConceptDynamics.Spacetime.TemporalComposition
import D5.S3.ConceptDynamics.Spacetime.ComplementFibers
import D5.S3.ConceptDynamics.Observation.StrictOneHoleContexts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Spacetime.TotalCopyNormalization

open D5.S0.History.Spacetime.ArchiveCarrier
open D5.S0.History.Spacetime.HFEncoding
open D5.S0.History.Spacetime.SourceTreeEncoding
open D5.S3.ConceptDynamics.Observation.StrictOneHoleContexts
open ComplementCharge
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev B := BalancedRich 3
abbrev SourceTimedAttribute := (Fin 3 → Int) × {s : Int // s = 1 ∨ s = -1} × SourceTree × Int

/-- The source order is position, signed integer, source tree, time. -/
def sourceAttributeEquiv : Attributes 3 ≃ SourceTimedAttribute where
  toFun a := (a.position, ⟨if a.positive then 1 else -1, by cases a.positive <;> simp⟩,
    a.source, a.time)
  invFun a := ⟨a.2.2.2, a.1, decide (a.2.1.val = 1), a.2.2.1⟩
  left_inv a := by cases a with | mk t p b r => cases b <;> rfl
  right_inv a := by
    rcases a with ⟨p, ⟨s, hs⟩, r, t⟩
    rcases hs with rfl | rfl <;> rfl

private def filterBalanced (P : (c : Context 3) → c.Event → Prop) (x : B) : B :=
  ⟨⟨x.val.1, ⟨x.val.2.val.filter (P x.val.1),
    (Finset.filter_subset _ _).trans x.val.2.property⟩⟩, x.property⟩

inductive Unary where
  | complement
  | spatial (S : Set (Fin 3 → Int))
  | source (L : Set SourceTree)
  | causal (Q : Set SourceTimedAttribute)
  | shift (k : Int)

inductive Binary where
  | parallel | product | temporal
  deriving DecidableEq

/-- Every filter changes only selection; targets are current, possibly unselected. -/
def unary : Unary → B → B
  | .complement, x => complementBalanced x
  | .spatial S, x => filterBalanced (fun c e => (c.archive.attributes e).position ∈ S) x
  | .source L, x => LeafSquareReadout.sourceFilterBalanced L x
  | .causal Q, x => filterBalanced (fun c e => ∃ d ∈ c.current,
      sourceAttributeEquiv (c.archive.attributes d) ∈ Q ∧ (e = d ∨ c.archive.causal e d)) x
  | .shift k, x => ⟨TemporalComposition.shiftRich x.val k, x.property⟩

def binary : Binary → B → B → Option B
  | .parallel, x, y => some (ParallelComposition.parallelBalanced x y)
  | .product, x, y => some (GeneratedProduct.productBalanced x y)
  | .temporal, x, y => if h : TemporalComposition.Guard x.val.1.archive y.val.1.archive
      then some (TemporalComposition.temporalBalanced x y h) else none

/-- This is the very same interpreter used at nodes of the copy syntax. -/
abbrev nativeSignature : PartialSignature B (Unary ⊕ Binary) where
  arity | .inl _ => 1 | .inr _ => 2
  operation | .inl f, xs => some (unary f (xs 0))
            | .inr f, xs => binary f (xs 0) (xs 1)

/-- The index counts occurrences in left-to-right order, including repeated inputs. -/
inductive CopyTerm : Nat → Type where
  | input : CopyTerm 1
  | param (x : B) : CopyTerm 0
  | unary {n : Nat} (f : Unary) (a : CopyTerm n) : CopyTerm n
  | binary {n m : Nat} (f : Binary) (a : CopyTerm n) (b : CopyTerm m) : CopyTerm (n + m)

/-- Success requires all children to succeed, even under erasing operations. -/
def eval : {n : Nat} → CopyTerm n → (Fin n → B) → Option B
  | _, .input, v => some (v 0)
  | _, .param x, _ => some x
  | _, .unary f a, v => (eval a v).map (unary f)
  | _, @CopyTerm.binary n m f a b, v =>
      (eval a (fun i => v (i.castAdd m))).bind fun x =>
      (eval b (fun i => v (i.natAdd n))).bind (binary f x)

def evalDiagonal {n : Nat} (C : CopyTerm n) (X : B) : Option B := eval C (fun _ => X)
def DiagonalTotal {n : Nat} (C : CopyTerm n) : Prop := ∀ X, ∃ Y, evalDiagonal C X = some Y

def zero : B := ComplementFibers.balancedSection 3 0

private theorem zero_empty : zero.val.1.archive.events = ∅ ∧
    zero.val.1.current = ∅ ∧ zero.val.2.val = ∅ :=
  IntegerRepresentatives.representative_zero_empty 3

private theorem unary_success {n : Nat} (f : Unary) (a : CopyTerm n) (X Y : B)
    (h : evalDiagonal (.unary f a) X = some Y) :
    ∃ x, evalDiagonal a X = some x ∧ unary f x = Y := by
  change (evalDiagonal a X).map (unary f) = some Y at h
  exact Option.map_eq_some_iff.mp h

private theorem subtree_success {n m : Nat} (f : Binary) (a : CopyTerm n) (b : CopyTerm m)
    (X Y : B) (h : evalDiagonal (.binary f a b) X = some Y) :
    ∃ x y, evalDiagonal a X = some x ∧ evalDiagonal b X = some y ∧ binary f x y = some Y := by
  change (evalDiagonal a X).bind (fun x => (evalDiagonal b X).bind (binary f x)) = some Y at h
  obtain ⟨x, hx, hrest⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨y, hy, hz⟩ := Option.bind_eq_some_iff.mp hrest
  exact ⟨x, y, hx, hy, hz⟩

private theorem total_unary {n : Nat} (f : Unary) (a : CopyTerm n)
    (h : DiagonalTotal (.unary f a)) : DiagonalTotal a := by
  intro X
  obtain ⟨Y, hY⟩ := h X
  obtain ⟨x, hx, _⟩ := unary_success f a X Y hY
  exact ⟨x, hx⟩

private theorem total_binary {n m : Nat} (f : Binary) (a : CopyTerm n) (b : CopyTerm m)
    (h : DiagonalTotal (.binary f a b)) : DiagonalTotal a ∧ DiagonalTotal b := by
  have hh X := (h X).imp fun Y hY => subtree_success f a b X Y hY
  exact ⟨fun X => by obtain ⟨_, x, _, hx, _, _⟩ := hh X; exact ⟨x, hx⟩,
    fun X => by obtain ⟨_, _, y, _, hy, _⟩ := hh X; exact ⟨y, hy⟩⟩

private theorem closed_eval_constant (C : CopyTerm 0) (X : B) :
    evalDiagonal C X = evalDiagonal C zero :=
  congrArg (eval C) (funext fun i => Fin.elim0 i)

private def unaryShift : Unary → Int | .shift k => k | _ => 0

private def pathShift : {n : Nat} → CopyTerm n → Fin n → Int
  | _, .input, _ => 0
  | _, .param _, i => Fin.elim0 i
  | _, .unary f a, i => pathShift a i + unaryShift f
  | _, .binary _ a b, i => Fin.addCases (pathShift a) (pathShift b) i

private theorem unary_persistence (f : Unary) (X : B) :
    ∃ e : X.val.1.Event ↪ (unary f X).val.1.Event, ∀ a,
      ((unary f X).val.1.archive.attributes (e a)).time =
        (X.val.1.archive.attributes a).time + unaryShift f := by
  cases f <;> exact ⟨Function.Embedding.refl _, fun _ => by simp [unary, unaryShift,
    filterBalanced, complementBalanced, complementRich, LeafSquareReadout.sourceFilterBalanced,
    LeafSquareReadout.sourceFilter, TemporalComposition.shiftRich, TemporalComposition.shiftContext,
    TemporalComposition.shiftArchive]⟩

private theorem binary_persistence (f : Binary) (X Y Z : B) (h : binary f X Y = some Z) :
    ∃ l : X.val.1.Event ↪ Z.val.1.Event, ∃ r : Y.val.1.Event ↪ Z.val.1.Event,
      (∀ a, (Z.val.1.archive.attributes (l a)).time = (X.val.1.archive.attributes a).time) ∧
      (∀ a, (Z.val.1.archive.attributes (r a)).time = (Y.val.1.archive.attributes a).time) := by
  cases f with
  | parallel =>
    cases Option.some.inj h
    exact ⟨ParallelComposition.left _ _, ParallelComposition.right _ _,
      fun a => congrArg Attributes.time (ParallelComposition.attributes_left _ _ a),
      fun a => congrArg Attributes.time (ParallelComposition.attributes_right _ _ a)⟩
  | product =>
    cases Option.some.inj h
    exact ⟨GeneratedProduct.left _ _, GeneratedProduct.right _ _,
      fun a => congrArg Attributes.time (GeneratedProduct.attributes_left _ _ a),
      fun a => congrArg Attributes.time (GeneratedProduct.attributes_right _ _ a)⟩
  | temporal =>
    change (if g : TemporalComposition.Guard X.val.1.archive Y.val.1.archive
      then some (TemporalComposition.temporalBalanced X Y g) else none) = some Z at h
    by_cases hg : TemporalComposition.Guard X.val.1.archive Y.val.1.archive
    · rw [dif_pos hg] at h
      cases Option.some.inj h
      refine ⟨Function.Embedding.inl.trans (TemporalComposition.equiv _ _ hg).toEmbedding,
        Function.Embedding.inr.trans (TemporalComposition.equiv _ _ hg).toEmbedding, ?_, ?_⟩
      · intro a
        exact congrArg Attributes.time (TemporalComposition.attributes_equiv _ _ hg (.inl a))
      · intro a
        exact congrArg Attributes.time (TemporalComposition.attributes_equiv _ _ hg (.inr a))
    · rw [dif_neg hg] at h
      cases h

/-- An arbitrary occurrence path carries every old event, with a syntax-fixed offset. -/
private theorem archive_path_persistence {n : Nat} (C : CopyTerm n) (i : Fin n) (X Y : B)
    (h : evalDiagonal C X = some Y) :
    ∃ e : X.val.1.Event ↪ Y.val.1.Event, ∀ a,
      (Y.val.1.archive.attributes (e a)).time =
        (X.val.1.archive.attributes a).time + pathShift C i := by
  induction C generalizing Y with
  | input =>
    cases Option.some.inj h
    exact ⟨Function.Embedding.refl _, fun _ => by simp [pathShift]⟩
  | param => exact Fin.elim0 i
  | unary f a ih =>
    obtain ⟨v, hv, rfl⟩ := unary_success f a X Y h
    obtain ⟨e, he⟩ := ih i v hv
    obtain ⟨j, hj⟩ := unary_persistence f v
    refine ⟨e.trans j, fun x => ?_⟩
    rw [Function.Embedding.trans_apply, hj, he]
    simp [pathShift, add_assoc]
  | binary f a b iha ihb =>
    obtain ⟨v, w, hv, hw, hz⟩ := subtree_success f a b X Y h
    obtain ⟨l, r, hl, hr⟩ := binary_persistence f v w Y hz
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · obtain ⟨e, he⟩ := iha i v hv
      exact ⟨e.trans l, fun x => by simpa [pathShift] using (hl (e x)).trans (he x)⟩
    · obtain ⟨e, he⟩ := ihb i w hw
      exact ⟨e.trans r, fun x => by simpa [pathShift] using (hr (e x)).trans (he x)⟩

private def inactiveCode : Bool ↪ HF :=
  ⟨fun b => IntegerRepresentatives.eventName 0 b,
    by
      intro b c h
      have hp : (0, b) = (0, c) := IntegerRepresentatives.eventName_injective h
      exact congrArg Prod.snd hp⟩

private def inactive (lo hi : Int) : B :=
  let c := TaggedPresentation.contextOf inactiveCode
    (fun b => (⟨if b then hi else lo, 0, true, FreeMagma.of 0⟩ : Attributes 3))
    (fun _ _ => False) (fun _ h => h) (fun _ _ _ h _ => h) (fun _ _ h => h.elim) ∅
  ⟨⟨c, emptySelection c⟩, by simp [Balanced, background, charge, c,
    TaggedPresentation.contextOf]⟩

private theorem inactive_times_spec (lo hi : Int) :
    ∃ X : B, X.val.1.current = ∅ ∧ X.val.2.val = ∅ ∧
      ∃ l r : X.val.1.Event, l ≠ r ∧
        X.val.1.archive.events = {l.val, r.val} ∧
        (X.val.1.archive.attributes l).time = lo ∧
        (X.val.1.archive.attributes r).time = hi := by
  refine ⟨inactive lo hi, by simp [inactive, TaggedPresentation.contextOf], rfl,
    TaggedPresentation.eventEquiv inactiveCode false,
    TaggedPresentation.eventEquiv inactiveCode true, ?_, ?_, ?_, ?_⟩
  · intro h
    have := (TaggedPresentation.eventEquiv inactiveCode).injective h
    cases this
  · change TaggedPresentation.events inactiveCode = {inactiveCode false, inactiveCode true}
    simp [TaggedPresentation.events, Fintype.univ_bool, Finset.pair_comm]
  · dsimp [inactive, TaggedPresentation.contextOf, TaggedPresentation.archiveOf]
    simp only [Equiv.symm_apply_apply, Bool.false_eq_true, ↓reduceIte]
  · dsimp [inactive, TaggedPresentation.contextOf, TaggedPresentation.archiveOf]
    simp only [Equiv.symm_apply_apply, ↓reduceIte]

private theorem temporal_success (X Y Z : B) (h : binary .temporal X Y = some Z) :
    TemporalComposition.Guard X.val.1.archive Y.val.1.archive := by
  by_contra hg
  change (if g : TemporalComposition.Guard X.val.1.archive Y.val.1.archive
    then some (TemporalComposition.temporalBalanced X Y g) else none) = some Z at h
  rw [dif_neg hg] at h
  cases h

/-- Shared diagonal inputs with unbounded inactive times rule out every other temporal node. -/
private theorem temporal_node_has_closed_empty_side {n m : Nat}
    (a : CopyTerm n) (b : CopyTerm m) (hp : 0 < n + m)
    (ht : DiagonalTotal (.binary .temporal a b)) :
    (n = 0 ∧ ∃ z, evalDiagonal a zero = some z ∧ z.val.1.archive.events = ∅) ∨
    (m = 0 ∧ ∃ z, evalDiagonal b zero = some z ∧ z.val.1.archive.events = ∅) := by
  have totals := total_binary .temporal a b ht
  by_cases hn : n = 0
  · subst n
    obtain ⟨z, hz⟩ := totals.1 zero
    refine Or.inl ⟨rfl, z, hz, ?_⟩
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    let s := (z.val.1.archive.attributes ⟨e, he⟩).time
    let i : Fin m := ⟨0, by omega⟩
    let L := max 0 (pathShift b i - s)
    obtain ⟨X, _, _, l, r, _, _, hl, _⟩ := inactive_times_spec (-L) L
    obtain ⟨Y, hY⟩ := ht X
    obtain ⟨v, w, hv, hw, hh⟩ := subtree_success .temporal a b X Y hY
    rw [closed_eval_constant, hz] at hv
    cases Option.some.inj hv
    obtain ⟨f, hf⟩ := archive_path_persistence b i X w hw
    have guard := temporal_success z w Y hh ⟨e, he⟩ (f l)
    rw [hf, hl] at guard
    have := le_max_right 0 (pathShift b i - s)
    change s < -L + pathShift b i at guard
    dsimp [L] at guard
    omega
  · by_cases hm : m = 0
    · subst m
      obtain ⟨z, hz⟩ := totals.2 zero
      refine Or.inr ⟨rfl, z, hz, ?_⟩
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      let s := (z.val.1.archive.attributes ⟨e, he⟩).time
      let i : Fin n := ⟨0, by omega⟩
      let L := max 0 (s - pathShift a i)
      obtain ⟨X, _, _, l, r, _, _, _, hr⟩ := inactive_times_spec (-L) L
      obtain ⟨Y, hY⟩ := ht X
      obtain ⟨v, w, hv, hw, hh⟩ := subtree_success .temporal a b X Y hY
      rw [closed_eval_constant, hz] at hw
      cases Option.some.inj hw
      obtain ⟨f, hf⟩ := archive_path_persistence a i X v hv
      have guard := temporal_success v z Y hh (f r) ⟨e, he⟩
      rw [hf, hr] at guard
      have := le_max_right 0 (s - pathShift a i)
      change L + pathShift a i < s at guard
      dsimp [L] at guard
      omega
    · let i : Fin n := ⟨0, by omega⟩
      let j : Fin m := ⟨0, by omega⟩
      let L := max 0 (pathShift b j - pathShift a i)
      obtain ⟨X, _, _, l, r, _, _, hl, hr⟩ := inactive_times_spec (-L) L
      obtain ⟨Y, hY⟩ := ht X
      obtain ⟨v, w, hv, hw, hh⟩ := subtree_success .temporal a b X Y hY
      obtain ⟨f, hf⟩ := archive_path_persistence a i X v hv
      obtain ⟨g, hg⟩ := archive_path_persistence b j X w hw
      have guard := temporal_success v w Y hh (f r) (g l)
      rw [hf, hg, hl, hr] at guard
      have hL := le_max_left 0 (pathShift b j - pathShift a i)
      have hgap := le_max_right 0 (pathShift b j - pathShift a i)
      dsimp [L] at guard
      omega


private theorem temporal_eq_parallel_empty_left (X Y : B)
    (h : X.val.1.archive.events = ∅)
    (g : TemporalComposition.Guard X.val.1.archive Y.val.1.archive) :
    TemporalComposition.temporalBalanced X Y g = ParallelComposition.parallelBalanced X Y := by
  have he : TemporalComposition.edge X.val.1.archive Y.val.1.archive =
      ParallelComposition.internal X.val.1.archive Y.val.1.archive := by
    funext a b
    cases a with
    | inl e => exact False.elim (by have := e.property; simp [h] at this)
    | inr e => cases b <;> rfl
  apply Subtype.ext
  unfold TemporalComposition.temporalBalanced TemporalComposition.temporal
    ParallelComposition.parallelBalanced ParallelComposition.parallel
    TemporalComposition.context TemporalComposition.selection
    ParallelComposition.context ParallelComposition.selection
    TaggedPresentation.contextOf TaggedPresentation.selectionOf TaggedPresentation.archiveOf
  congr! 5
  funext a b
  exact congrFun (congrFun he _) _

private theorem temporal_eq_parallel_empty_right (X Y : B)
    (h : Y.val.1.archive.events = ∅)
    (g : TemporalComposition.Guard X.val.1.archive Y.val.1.archive) :
    TemporalComposition.temporalBalanced X Y g = ParallelComposition.parallelBalanced X Y := by
  have he : TemporalComposition.edge X.val.1.archive Y.val.1.archive =
      ParallelComposition.internal X.val.1.archive Y.val.1.archive := by
    funext a b
    cases b with
    | inr e => exact False.elim (by have := e.property; simp [h] at this)
    | inl e => cases a <;> rfl
  apply Subtype.ext
  unfold TemporalComposition.temporalBalanced TemporalComposition.temporal
    ParallelComposition.parallelBalanced ParallelComposition.parallel
    TemporalComposition.context TemporalComposition.selection
    ParallelComposition.context ParallelComposition.selection
    TaggedPresentation.contextOf TaggedPresentation.selectionOf TaggedPresentation.archiveOf
  congr! 5
  funext a b
  exact congrFun (congrFun he _) _

def TemporalFree : {n : Nat} → CopyTerm n → Prop
  | _, .input => True
  | _, .param _ => True
  | _, .unary _ a => TemporalFree a
  | _, .binary f a b => f ≠ .temporal ∧ TemporalFree a ∧ TemporalFree b

private def withoutTemporal : Binary → Binary
  | .temporal => .parallel | f => f

/-- Closed subtrees become their complete values; every surviving temporal node becomes parallel. -/
inductive Normalizes : {n : Nat} → CopyTerm n → CopyTerm n → Prop where
  | closed (C : CopyTerm 0) (z : B) (h : evalDiagonal C zero = some z) :
      Normalizes C (.param z)
  | input : Normalizes .input .input
  | unary {n : Nat} {a a' : CopyTerm n} (hp : 0 < n) (f : Unary)
      (h : Normalizes a a') : Normalizes (.unary f a) (.unary f a')
  | binary {n m : Nat} {a a' : CopyTerm n} {b b' : CopyTerm m}
      (hp : 0 < n + m) (f : Binary) (ha : Normalizes a a') (hb : Normalizes b b') :
      Normalizes (.binary f a b) (.binary (withoutTemporal f) a' b')

private theorem normalize_closed (C : CopyTerm 0) (h : DiagonalTotal C) :
    ∃ N, Normalizes C N ∧ TemporalFree N ∧ ∀ X, evalDiagonal C X = evalDiagonal N X := by
  obtain ⟨z, hz⟩ := h zero
  exact ⟨.param z, .closed C z hz, True.intro,
    fun X => (closed_eval_constant C X).trans hz⟩

private theorem normalize_total_correct {n : Nat} (C : CopyTerm n) (h : DiagonalTotal C) :
    ∃ N, Normalizes C N ∧ TemporalFree N ∧ ∀ X, evalDiagonal C X = evalDiagonal N X := by
  induction C with
  | input => exact ⟨.input, .input, True.intro, fun _ => rfl⟩
  | param x => exact normalize_closed (.param x) h
  | @unary n f a ih =>
    by_cases hn : n = 0
    · subst n; exact normalize_closed (.unary f a) h
    · obtain ⟨N, hN, hf, he⟩ := ih (total_unary f a h)
      refine ⟨.unary f N, .unary (by omega) f hN, hf, fun X => ?_⟩
      exact congrArg (Option.map (unary f)) (he X)
  | @binary n m f a b iha ihb =>
    by_cases hz : n + m = 0
    · have hn : n = 0 := by omega
      have hm : m = 0 := by omega
      subst n; subst m; exact normalize_closed (.binary f a b) h
    · obtain ⟨ha, hb⟩ := total_binary f a b h
      obtain ⟨N, hN, hfN, heN⟩ := iha ha
      obtain ⟨M, hM, hfM, heM⟩ := ihb hb
      refine ⟨.binary (withoutTemporal f) N M, .binary (by omega) f hN hM,
        ⟨by cases f <;> simp [withoutTemporal], hfN, hfM⟩, fun X => ?_⟩
      obtain ⟨Y, hY⟩ := h X
      obtain ⟨v, w, hv, hw, hh⟩ := subtree_success f a b X Y hY
      change (evalDiagonal a X).bind (fun x => (evalDiagonal b X).bind (binary f x)) =
        (evalDiagonal N X).bind (fun x => (evalDiagonal M X).bind (binary (withoutTemporal f) x))
      rw [← heN X, ← heM X, hv, hw]
      simp only [Option.bind_some]
      cases f with
      | parallel => rfl
      | product => rfl
      | temporal =>
        have g := temporal_success v w Y hh
        have empty := temporal_node_has_closed_empty_side a b (by omega) h
        have eqv : TemporalComposition.temporalBalanced v w g =
            ParallelComposition.parallelBalanced v w := by
          rcases empty with ⟨hn, z, hz, he⟩ | ⟨hm, z, hz, he⟩
          · subst n
            rw [closed_eval_constant, hz] at hv
            cases Option.some.inj hv
            exact temporal_eq_parallel_empty_left v w he g
          · subst m
            rw [closed_eval_constant, hz] at hw
            cases Option.some.inj hw
            exact temporal_eq_parallel_empty_right v w he g
        change (if h : TemporalComposition.Guard v.val.1.archive w.val.1.archive
          then some (TemporalComposition.temporalBalanced v w h) else none) =
            some (ParallelComposition.parallelBalanced v w)
        rw [dif_pos g]
        exact congrArg some eqv

private theorem temporal_free_total {n : Nat} (C : CopyTerm n) (h : TemporalFree C)
    (v : Fin n → B) : ∃ Y, eval C v = some Y := by
  induction C with
  | input => exact ⟨v 0, rfl⟩
  | param x => exact ⟨x, rfl⟩
  | unary f a ih =>
    obtain ⟨x, hx⟩ := ih h v
    refine ⟨unary f x, ?_⟩
    change (eval a v).map (unary f) = some (unary f x)
    rw [hx]; rfl
  | @binary n m f a b iha ihb =>
    obtain ⟨x, hx⟩ := iha h.2.1 (fun i => v (i.castAdd m))
    obtain ⟨y, hy⟩ := ihb h.2.2 (fun i => v (i.natAdd n))
    have he : eval (.binary f a b) v = binary f x y := by
      change (eval a (fun i => v (i.castAdd m))).bind
        (fun x => (eval b (fun i => v (i.natAdd n))).bind (binary f x)) = _
      rw [hx, hy]; rfl
    cases f with
    | parallel => exact ⟨ParallelComposition.parallelBalanced x y, he⟩
    | product => exact ⟨GeneratedProduct.productBalanced x y, he⟩
    | temporal => exact (h.1 rfl).elim

private def unaryGenerator (f : Unary) : Generator nativeSignature :=
  ⟨.inl f, (0 : Fin 1), fun j => (j.property (Subsingleton.elim (j.val : Fin 1) 0)).elim⟩

private def binaryGenerator (f : Binary) (slot : Fin 2) (z : B) : Generator nativeSignature :=
  ⟨.inr f, slot, fun _ => z⟩

private def extendCopy (C : CopyTerm 1) (g : Generator nativeSignature) : CopyTerm 1 :=
  match g with
  | ⟨.inl f, _, _⟩ => .unary f C
  | ⟨.inr f, i, p⟩ => if h : i = (0 : Fin 2) then
      .binary f C (.param (p ⟨(1 : Fin 2), by simp [h]⟩))
    else .binary f (.param (p ⟨(0 : Fin 2), Ne.symm h⟩)) C

/-- Reify every source word with exactly one input occurrence, including the empty word. -/
def wordToCopy (w : List (Generator nativeSignature)) : CopyTerm 1 := w.foldl extendCopy .input

private theorem extendCopy_denote (C : CopyTerm 1) (g : Generator nativeSignature) (X : B) :
    evalDiagonal (extendCopy C g) X = strictStep nativeSignature g (evalDiagonal C X) := by
  rcases g with ⟨f, i, p⟩
  cases f with
  | inl f =>
    have hi : i = (0 : Fin 1) := Subsingleton.elim (i : Fin 1) _
    subst i
    change (evalDiagonal C X).map (unary f) = (evalDiagonal C X).bind
      (fun x => some (unary f (if _ : (0 : Fin 1) = 0 then x else _)))
    cases evalDiagonal C X <;> rfl
  | inr f =>
    change Fin 2 at i
    change {j : Fin 2 // j ≠ i} → B at p
    have hi : (i : Fin 2) = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · change (evalDiagonal C X).bind (fun x => binary f x (p ⟨1, by decide⟩)) =
        (evalDiagonal C X).bind (fun x => binary f
          (if _ : (0 : Fin 2) = 0 then x else _)
          (if h : (1 : Fin 2) = 0 then x else p ⟨1, h⟩))
      rfl
    · change (evalDiagonal C X).bind (binary f (p ⟨0, by decide⟩)) =
        (evalDiagonal C X).bind (fun x => binary f
          (if h : (0 : Fin 2) = 1 then x else p ⟨0, h⟩)
          (if _ : (1 : Fin 2) = 1 then x else _))
      rfl

private theorem word_to_copy_denote (w : List (Generator nativeSignature)) (X : B) :
    evalDiagonal (wordToCopy w) X = contextDenote nativeSignature w X := by
  let step := fun (s : Option B) (g : Generator nativeSignature) => strictStep nativeSignature g s
  have run_fold (w : List (Generator nativeSignature)) (s : Option B) :
      D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality.runWord
        (strictStep nativeSignature) w s = w.foldl step s := by
    induction w generalizing s with
    | nil => rfl
    | cons g w ih => exact ih (strictStep nativeSignature g s)
  change evalDiagonal (w.foldl extendCopy .input) X =
    D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality.runWord
      (strictStep nativeSignature) w (some X)
  rw [run_fold]
  exact (List.foldl_hom (fun C : CopyTerm 1 => evalDiagonal C X)
    (g₁ := extendCopy) (g₂ := step) (l := w) (init := .input)
    (fun C g => (extendCopy_denote C g X).symm)).symm

/-- A word is temporal-free when each of its fixed generators is temporal-free. -/
def WordTemporalFree (w : List (Generator nativeSignature)) : Prop :=
  ∀ g ∈ w, g.symbol ≠ .inr .temporal

/-- Complete zero-input value used when folding the siblings of an occurrence path. -/
def zeroValue {n : Nat} (C : CopyTerm n) : B := (evalDiagonal C zero).getD zero

private theorem zeroValue_correct {n : Nat} (C : CopyTerm n) (h : TemporalFree C) :
    evalDiagonal C zero = some (zeroValue C) := by
  obtain ⟨z, hz⟩ := temporal_free_total C h (fun _ => zero)
  change evalDiagonal C zero = some z at hz
  simp only [zeroValue, hz, Option.getD_some]

/-- Keep one ordered occurrence and replace each off-path subtree by its complete zero value. -/
def foldedSlice : {n : Nat} → (C : CopyTerm n) → Fin n → CopyTerm 1
  | _, .input, _ => .input
  | _, .param _, i => Fin.elim0 i
  | _, .unary f a, i => .unary f (foldedSlice a i)
  | _, .binary f a b, i => Fin.addCases
      (fun j => .binary f (foldedSlice a j) (.param (zeroValue b)))
      (fun j => .binary f (.param (zeroValue a)) (foldedSlice b j)) i

private def sliceWord : {n : Nat} → (C : CopyTerm n) → Fin n → List (Generator nativeSignature)
  | _, .input, _ => []
  | _, .param _, i => Fin.elim0 i
  | _, .unary f a, i => sliceWord a i ++ [unaryGenerator f]
  | _, .binary f a b, i => Fin.addCases
      (fun j => sliceWord a j ++ [binaryGenerator f 0 (zeroValue b)])
      (fun j => sliceWord b j ++ [binaryGenerator f 1 (zeroValue a)]) i

private theorem sliceWord_reify {n : Nat} (C : CopyTerm n) (i : Fin n) :
    wordToCopy (sliceWord C i) = foldedSlice C i := by
  induction C with
  | input => rfl
  | param => exact Fin.elim0 i
  | unary f a ih =>
    simpa [sliceWord, wordToCopy, List.foldl_append, extendCopy, unaryGenerator, foldedSlice]
      using congrArg (CopyTerm.unary f) (ih i)
  | binary f a b iha ihb =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [sliceWord, foldedSlice, wordToCopy, List.foldl_append, extendCopy, binaryGenerator]
        using congrArg (fun t => CopyTerm.binary f t (.param (zeroValue b))) (iha j)
    · simpa [sliceWord, foldedSlice, wordToCopy, List.foldl_append, extendCopy, binaryGenerator]
        using congrArg (fun t => CopyTerm.binary f (.param (zeroValue a)) t) (ihb j)

/-- The selected occurrence receives X; every other occurrence receives the actual empty history. -/
def sliceAssignment {n : Nat} (i : Fin n) (X : B) : Fin n → B :=
  fun j => if j = i then X else zero

private theorem foldedSlice_correct {n : Nat} (C : CopyTerm n) (i : Fin n)
    (h : TemporalFree C) (X : B) :
    evalDiagonal (foldedSlice C i) X = eval C (sliceAssignment i X) := by
  induction C with
  | input => have hi : i = 0 := Subsingleton.elim _ _; subst i; rfl
  | param => exact Fin.elim0 i
  | unary f a ih => exact congrArg (Option.map (unary f)) (ih i h)
  | @binary n m f a b iha ihb =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have hl : (fun k : Fin n => sliceAssignment (j.castAdd m) X (k.castAdd m)) =
          sliceAssignment j X := by funext k; simp [sliceAssignment, Fin.ext_iff]
      have hr : (fun k : Fin m => sliceAssignment (j.castAdd m) X (k.natAdd n)) =
          fun _ => zero := by
        funext k
        have hh : k.natAdd n ≠ j.castAdd m := by
          intro he
          have := congrArg Fin.val he
          simp at this
          omega
        simp [sliceAssignment, hh]
      simp only [foldedSlice, Fin.addCases_left]
      change (evalDiagonal (foldedSlice a j) X).bind (fun x => binary f x (zeroValue b)) = _
      rw [iha j h.2.1]
      change _ = (eval a _).bind (fun x => (eval b _).bind (binary f x))
      rw [hl, hr, show eval b (fun _ => zero) = some (zeroValue b) from zeroValue_correct b h.2.2]
      rfl
    · have hl : (fun k : Fin n => sliceAssignment (j.natAdd n) X (k.castAdd m)) =
          fun _ => zero := by
        funext k
        have hh : k.castAdd m ≠ j.natAdd n := by
          intro he
          have := congrArg Fin.val he
          simp at this
          omega
        simp [sliceAssignment, hh]
      have hr : (fun k : Fin m => sliceAssignment (j.natAdd n) X (k.natAdd n)) =
          sliceAssignment j X := by funext k; simp [sliceAssignment, Fin.ext_iff]
      simp only [foldedSlice, Fin.addCases_right]
      change (evalDiagonal (foldedSlice b j) X).bind (binary f (zeroValue a)) = _
      rw [ihb j h.2.2]
      change _ = (eval a _).bind (fun x => (eval b _).bind (binary f x))
      rw [hl, hr, show eval a (fun _ => zero) = some (zeroValue a) from zeroValue_correct a h.2.1]
      rfl

private theorem sliceWord_free {n : Nat} (C : CopyTerm n) (i : Fin n) (h : TemporalFree C) :
    WordTemporalFree (sliceWord C i) := by
  induction C with
  | input => simp [sliceWord, WordTemporalFree]
  | param => exact Fin.elim0 i
  | unary f a ih =>
    intro g hg
    simp only [sliceWord, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact ih i h g hg
    · simp [unaryGenerator]
  | binary f a b iha ihb =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · intro g hg
      simp only [sliceWord, Fin.addCases_left, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact iha j h.2.1 g hg
      · simpa [binaryGenerator] using h.1
    · intro g hg
      simp only [sliceWord, Fin.addCases_right, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact ihb j h.2.2 g hg
      · simpa [binaryGenerator] using h.1

private theorem slice_word_correct {n : Nat} (C : CopyTerm n) (h : TemporalFree C) (i : Fin n) :
    ∃ w : List (Generator nativeSignature), WordTemporalFree w ∧
      wordToCopy w = foldedSlice C i ∧
      (∀ X, contextDenote nativeSignature w X = eval C (sliceAssignment i X)) ∧
      (∀ X, ∃ Y, contextDenote nativeSignature w X = some Y) := by
  refine ⟨sliceWord C i, sliceWord_free C i h, sliceWord_reify C i, ?_, ?_⟩
  · intro X
    rw [← word_to_copy_denote, sliceWord_reify, foldedSlice_correct C i h]
  · intro X
    obtain ⟨Y, hY⟩ := temporal_free_total C h (sliceAssignment i X)
    exact ⟨Y, by rw [← word_to_copy_denote, sliceWord_reify, foldedSlice_correct C i h]; exact hY⟩

/-- Full exact normalization and every one-hole zero slice for arbitrary finite diagonal copies. -/
theorem total_copy_normalization {n : Nat} (C : CopyTerm n) (_hp : 0 < n)
    (ht : DiagonalTotal C) :
    zero.val.1.archive.events = ∅ ∧ zero.val.1.current = ∅ ∧ zero.val.2.val = ∅ ∧
    ∃ N : CopyTerm n, Normalizes C N ∧ TemporalFree N ∧
      (∀ X, evalDiagonal C X = evalDiagonal N X) ∧
      (∀ v : Fin n → B, ∃ Y, eval N v = some Y) ∧
      ∃ w : Fin n → List (Generator nativeSignature),
        (∀ i, WordTemporalFree (w i) ∧ wordToCopy (w i) = foldedSlice N i) ∧
        (∀ i X, contextDenote nativeSignature (w i) X = eval N (sliceAssignment i X)) ∧
        (∀ i X, ∃ Y, contextDenote nativeSignature (w i) X = some Y) ∧
        (∃ Z, evalDiagonal C zero = some Z ∧
          ∀ i, contextDenote nativeSignature (w i) zero = some Z) := by
  obtain ⟨N, hN, hf, he⟩ := normalize_total_correct C ht
  have slices := fun i : Fin n => slice_word_correct N hf i
  choose w hw hr hd hs using slices
  refine ⟨zero_empty.1, zero_empty.2.1, zero_empty.2.2, N, hN, hf, he,
    temporal_free_total N hf, w, fun i => ⟨hw i, hr i⟩, hd, hs, ?_⟩
  obtain ⟨Z, hZ⟩ := ht zero
  refine ⟨Z, hZ, fun i => ?_⟩
  rw [hd]
  have hz : sliceAssignment i zero = fun _ => zero := by funext j; simp [sliceAssignment]
  rw [hz]
  exact (he zero).symm.trans hZ

/-- Exact all-input Def16 consequence; the word bridge supplies the one occurrence. -/
example (w : List (Generator nativeSignature))
    (ht : ∀ X : B, ∃ Y, contextDenote nativeSignature w X = some Y) :
    ∃ w' : List (Generator nativeSignature), WordTemporalFree w' ∧
      (∀ X, contextDenote nativeSignature w X = contextDenote nativeSignature w' X) ∧
      (∀ X, ∃ Y, contextDenote nativeSignature w' X = some Y) ∧
      (∃ Z, contextDenote nativeSignature w zero = some Z ∧
        contextDenote nativeSignature w' zero = some Z) := by
  have hc : DiagonalTotal (wordToCopy w) := by
    intro X
    simpa only [word_to_copy_denote] using ht X
  obtain ⟨_, _, _, N, _, _, he, _, ws, hw, hd, hs, Z, hz, hz'⟩ :=
    total_copy_normalization (wordToCopy w) (by decide) hc
  refine ⟨ws 0, (hw 0).1, fun X => ?_, hs 0, Z, ?_, hz' 0⟩
  · have hv : sliceAssignment (0 : Fin 1) X = fun _ => X := by
      funext j; have hj : j = 0 := Subsingleton.elim _ _; subst j; rfl
    rw [hd, hv]
    exact (word_to_copy_denote w X).symm.trans (he X)
  · simpa only [word_to_copy_denote] using hz

end
end D5.S3.ConceptDynamics.Spacetime.TotalCopyNormalization
