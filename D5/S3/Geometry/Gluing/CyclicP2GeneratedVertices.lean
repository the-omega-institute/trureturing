/- GID: D5/S3/Geometry/Gluing/CyclicP2GeneratedVertices
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/CyclicP2GeneratedVertices
   mirror-E: none(waiver:displayed-face-p2-generated-endpoint-classes)
   anchors: [mathlib/module/Mathlib.Logic.Relation,
     mathlib/module/Mathlib.SetTheory.Cardinal.Finite]
   utility: none
   digest: Oriented cyclic P2 subdivision preserves generated endpoint classes at the original face positions. -/

/-
Selected definitions adapted from LeanPool/ClassificationOfSurfaces/FiniteCyclicP2.lean
and P1.castSuccDart at edbe5bd56f476cc2965564676b66199f281ab714.
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Authors: Ryan McCorvie, Jack McCarthy.
Released under Apache 2.0; see docs/reports/licenses/lean-pool-surface/LICENSE.txt
and the complete accompanying NOTICE.txt. The displayed-face core is followed by
a minimal oriented-cut adapter, including signed inverse words, cyclic rotation
and the original old-position/fresh-last target indexing.
-/

import D5.S3.Geometry.Gluing.CyclicP1GeneratedVertices
import Mathlib.Data.List.Rotate
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.TakeDrop

set_option autoImplicit false
noncomputable section

namespace D5.S3.Geometry.Gluing.CyclicP2GeneratedVertices

open D5.S3.Geometry.Gluing.CyclicP1GeneratedVertices

/-- The selected occurrence is a list position, even when other words are equal. -/
structure DisplayedCut where
  edgeCount : ℕ
  «prefix» : List (List (SignedDart (Fin edgeCount)))
  suffix : List (List (SignedDart (Fin edgeCount)))
  left : List (SignedDart (Fin edgeCount))
  right : List (SignedDart (Fin edgeCount))

def before (C : DisplayedCut) : FiniteCyclicPresentation where
  edgeCount := C.edgeCount
  faces := C.prefix ++ [C.left ++ C.right] ++ C.suffix

/-- Faithful castSucc on each signed old edge, retaining its sign. -/
def retainDart {n : ℕ} : SignedDart (Fin n) → SignedDart (Fin (n + 1))
  | .pos e => .pos e.castSucc
  | .neg e => .neg e.castSucc

def retainWord {n : ℕ} (w : List (SignedDart (Fin n))) := w.map retainDart

def leftChild (C : DisplayedCut) := retainWord C.left ++ [.pos (Fin.last C.edgeCount)]
def rightChild (C : DisplayedCut) := .neg (Fin.last C.edgeCount) :: retainWord C.right

/-- Only the displayed occurrence is replaced; no face or endpoint is deduplicated. -/
def split (C : DisplayedCut) : FiniteCyclicPresentation where
  edgeCount := C.edgeCount + 1
  faces := C.prefix.map retainWord ++ [leftChild C, rightChild C] ++
    C.suffix.map retainWord

def oldEndpoint {n : ℕ} (x : Endpoint n) : Endpoint (n + 1) := (x.1.castSucc, x.2)
def p (n : ℕ) : Endpoint (n + 1) := (Fin.last n, false)
def q (n : ℕ) : Endpoint (n + 1) := (Fin.last n, true)

/-- Fresh positive initial endpoint: head R, falling back to head L only if R is empty. -/
def anchor₀ (C : DisplayedCut) (hne : C.left ++ C.right ≠ []) : Endpoint C.edgeCount :=
  initial ((C.right ++ C.left).head (by
    cases hL : C.left <;> cases hR : C.right <;> simp_all))

/-- Fresh positive terminal endpoint: head L, falling back to head R only if L is empty. -/
def anchor₁ (C : DisplayedCut) (hne : C.left ++ C.right ≠ []) : Endpoint C.edgeCount :=
  initial ((C.left ++ C.right).head hne)

/-- Collapse to actual old endpoints, with both anchors inside the selected word. -/
def collapse (C : DisplayedCut) (hne : C.left ++ C.right ≠ []) :
    Endpoint (C.edgeCount + 1) → Endpoint C.edgeCount
  | (e, b) => Fin.lastCases
      (match b with | false => anchor₀ C hne | true => anchor₁ C hne)
      (fun a => (a, b)) e

@[simp] private theorem collapse_old (C : DisplayedCut) (hne : C.left ++ C.right ≠ [])
    (x : Endpoint C.edgeCount) : collapse C hne (oldEndpoint x) = x := by
  rcases x with ⟨e,b⟩
  simp [collapse, oldEndpoint]

@[simp] private theorem collapse_p (C : DisplayedCut) (hne : C.left ++ C.right ≠ []) :
    collapse C hne (p C.edgeCount) = anchor₀ C hne := by simp [collapse, p]

@[simp] private theorem collapse_q (C : DisplayedCut) (hne : C.left ++ C.right ≠ []) :
    collapse C hne (q C.edgeCount) = anchor₁ C hne := by simp [collapse, q]

@[simp] private theorem initial_retain {n : ℕ} (d : SignedDart (Fin n)) :
    initial (retainDart d) = oldEndpoint (initial d) := by cases d <;> rfl

@[simp] private theorem terminal_retain {n : ℕ} (d : SignedDart (Fin n)) :
    terminal (retainDart d) = oldEndpoint (terminal d) := by cases d <;> rfl

/- Walk and Cycle express the seam constraints of the inherited presentation. -/

private theorem walk_retain {n : ℕ}
    (S : Endpoint (n + 1) → Endpoint (n + 1) → Prop)
    (a b : Endpoint n) (w : List (SignedDart (Fin n))) :
    Walk S (oldEndpoint a) (retainWord w) (oldEndpoint b) ↔
      Walk (fun x y => S (oldEndpoint x) (oldEndpoint y)) a w b := by
  induction w generalizing a with
  | nil => rfl
  | cons d ds ih =>
    simp only [retainWord, List.map_cons, Walk, initial_retain, terminal_retain]
    exact and_congr Iff.rfl (ih (terminal d))

private theorem cycle_retain {n : ℕ}
    (S : Endpoint (n + 1) → Endpoint (n + 1) → Prop)
    (w : List (SignedDart (Fin n))) :
    Cycle S (retainWord w) ↔
      Cycle (fun x y => S (oldEndpoint x) (oldEndpoint y)) w := by
  cases w with
  | nil => rfl
  | cons d ds =>
    simpa only [retainWord, List.map_cons, Cycle, initial_retain, terminal_retain]
      using walk_retain S (terminal d) (initial d) ds

/-- Split a literal walk just before a specified next dart, retaining its seam. -/
private theorem walk_append_cons {n : ℕ} (S : Endpoint n → Endpoint n → Prop)
    (a b : Endpoint n) (u : List (SignedDart (Fin n))) (d : SignedDart (Fin n))
    (v : List (SignedDart (Fin n))) :
    Walk S a (u ++ d :: v) b ↔
      Walk S a u (initial d) ∧ Walk S (terminal d) v b := by
  induction u generalizing a with
  | nil => rfl
  | cons e es ih => simp only [List.cons_append, Walk, ih, and_assoc]

/-- Only the last seam changes, using transitivity of the actual generated relation. -/
private theorem walk_end_change (P : FiniteCyclicPresentation)
    (a b c : Endpoint P.edgeCount) (w : List (SignedDart (Fin P.edgeCount)))
    (hw : Walk (Related P) a w b) (hbc : Related P b c) :
    Walk (Related P) a w c := by
  induction w generalizing a with
  | nil => exact hw.trans _ _ _ hbc
  | cons d ds ih => exact ⟨hw.1, ih (terminal d) hw.2⟩

private theorem walk_collapse_retain (C : DisplayedCut)
    (hne : C.left ++ C.right ≠ []) (S : Endpoint C.edgeCount → Endpoint C.edgeCount → Prop)
    (a b : Endpoint (C.edgeCount + 1)) (w : List (SignedDart (Fin C.edgeCount))) :
    Walk (fun x y => S (collapse C hne x) (collapse C hne y)) a (retainWord w) b ↔
      Walk S (collapse C hne a) w (collapse C hne b) := by
  induction w generalizing a with
  | nil => rfl
  | cons d ds ih =>
    simp only [retainWord, List.map_cons, Walk, initial_retain, terminal_retain,
      collapse_old]
    simpa only [collapse_old] using
      and_congr Iff.rfl (ih (oldEndpoint (terminal d)))

private theorem cycle_collapse_retain (C : DisplayedCut)
    (hne : C.left ++ C.right ≠ []) (S : Endpoint C.edgeCount → Endpoint C.edgeCount → Prop)
    (w : List (SignedDart (Fin C.edgeCount))) :
    Cycle (fun x y => S (collapse C hne x) (collapse C hne y)) (retainWord w) ↔
      Cycle S w := by
  cases w with
  | nil => rfl
  | cons d ds =>
    simpa only [retainWord, List.map_cons, Cycle, initial_retain, terminal_retain,
      collapse_old] using walk_collapse_retain C hne S
        (oldEndpoint (terminal d)) (oldEndpoint (initial d)) ds

private theorem left_cycle_cons {n : ℕ}
    (S : Endpoint (n + 1) → Endpoint (n + 1) → Prop)
    (d : SignedDart (Fin n)) (ds : List (SignedDart (Fin n))) :
    Cycle S (retainWord (d :: ds) ++ [.pos (Fin.last n)]) ↔
      Walk S (oldEndpoint (terminal d)) (retainWord ds) (p n) ∧
        S (q n) (oldEndpoint (initial d)) := by
  simp only [retainWord, List.map_cons, List.cons_append, Cycle, initial_retain,
    terminal_retain, walk_append_cons, Walk, initial, terminal, p, q]

private theorem right_cycle_cons {n : ℕ}
    (S : Endpoint (n + 1) → Endpoint (n + 1) → Prop)
    (d : SignedDart (Fin n)) (ds : List (SignedDart (Fin n))) :
    Cycle S (.neg (Fin.last n) :: retainWord (d :: ds)) ↔
      S (p n) (oldEndpoint (initial d)) ∧
        Walk S (oldEndpoint (terminal d)) (retainWord ds) (q n) := by
  simp only [retainWord, List.map_cons, Cycle, Walk, initial_retain,
    terminal_retain, initial, terminal, p, q]

/-- Old selected seams lift, and BOTH fresh endpoints reach their prescribed anchors.
The nil/cons and cons/nil branches use the fresh monogon's closing generator. -/
private theorem selected_lift (C : DisplayedCut) (hne : C.left ++ C.right ≠ []) :
    Cycle (fun x y => Related (split C) (oldEndpoint x) (oldEndpoint y))
      (C.left ++ C.right) ∧
    Related (split C) (p C.edgeCount) (oldEndpoint (anchor₀ C hne)) ∧
    Related (split C) (q C.edgeCount) (oldEndpoint (anchor₁ C hne)) := by
  have hleft := generated_cycles (split C) (leftChild C) (by simp [split])
  have hright := generated_cycles (split C) (rightChild C) (by simp [split])
  cases hL : C.left with
  | nil =>
    cases hR : C.right with
    | nil => exact (hne (by simp [hL,hR])).elim
    | cons r rs =>
      have hl : Related (split C) (q C.edgeCount) (p C.edgeCount) := by
        simpa [leftChild, hL, retainWord, Cycle, Walk, initial, terminal, p, q] using hleft
      have hr := (right_cycle_cons (Related (split C)) r rs).mp
        (by simpa [rightChild,hR] using hright)
      have hwrap := walk_end_change (split C) _ _ _ (retainWord rs) hr.2
        (hl.trans _ _ _ hr.1)
      refine ⟨?_, ?_, ?_⟩
      · simpa [hL,hR,Cycle] using
          (walk_retain (Related (split C)) (terminal r) (initial r) rs).mp hwrap
      · simpa [anchor₀,hL,hR] using hr.1
      · simpa [anchor₁,hL,hR] using hl.trans _ _ _ hr.1
  | cons l ls =>
    have hl := (left_cycle_cons (Related (split C)) l ls).mp
      (by simpa [leftChild,hL] using hleft)
    cases hR : C.right with
    | nil =>
      have hr : Related (split C) (p C.edgeCount) (q C.edgeCount) := by
        simpa [rightChild,hR,retainWord,Cycle,Walk,initial,terminal,p,q] using hright
      have hwrap := walk_end_change (split C) _ _ _ (retainWord ls) hl.1
        (hr.trans _ _ _ hl.2)
      refine ⟨?_, ?_, ?_⟩
      · simpa [hL,hR,Cycle] using
          (walk_retain (Related (split C)) (terminal l) (initial l) ls).mp hwrap
      · simpa [anchor₀,hL,hR] using hr.trans _ _ _ hl.2
      · simpa [anchor₁,hL,hR] using hl.2
    | cons r rs =>
      have hr := (right_cycle_cons (Related (split C)) r rs).mp
        (by simpa [rightChild,hR] using hright)
      have hls := walk_end_change (split C) _ _ _ (retainWord ls) hl.1 hr.1
      have hrs := walk_end_change (split C) _ _ _ (retainWord rs) hr.2 hl.2
      refine ⟨?_, ?_, ?_⟩
      · have hs := (walk_append_cons
          (fun x y => Related (split C) (oldEndpoint x) (oldEndpoint y))
          (terminal l) (initial l) ls r rs).mpr
            ⟨(walk_retain (Related (split C)) (terminal l) (initial r) ls).mp hls,
             (walk_retain (Related (split C)) (terminal r) (initial l) rs).mp hrs⟩
        simpa [hL,hR,Cycle] using hs
      · simpa [anchor₀,hL,hR] using hr.1
      · simpa [anchor₁,hL,hR] using hl.2

/-- Every literal seam in either child collapses to an old generated relation. -/
private theorem selected_collapse (C : DisplayedCut) (hne : C.left ++ C.right ≠ []) :
    Cycle (fun x y => Related (before C) (collapse C hne x) (collapse C hne y))
      (leftChild C) ∧
    Cycle (fun x y => Related (before C) (collapse C hne x) (collapse C hne y))
      (rightChild C) := by
  let S := fun x y => Related (before C) (collapse C hne x) (collapse C hne y)
  have hold := generated_cycles (before C) (C.left ++ C.right) (by simp [before])
  cases hL : C.left with
  | nil =>
    cases hR : C.right with
    | nil => exact (hne (by simp [hL,hR])).elim
    | cons r rs =>
      have hw : Walk (Related (before C)) (terminal r) rs (initial r) := by
        simpa [hL,hR,Cycle] using hold
      have hqp : S (q C.edgeCount) (p C.edgeCount) := by
        simpa [S,anchor₀,anchor₁,hL,hR] using
          (Relation.EqvGen.refl (initial r) : Related (before C) (initial r) (initial r))
      refine ⟨?_, ?_⟩
      · simpa [S,leftChild,hL,retainWord,Cycle,Walk,initial,terminal,p,q,collapse] using hqp
      · change Cycle S (rightChild C)
        rw [rightChild,hR]
        apply (right_cycle_cons S r rs).mpr
        constructor
        · simpa [S,anchor₀,hL,hR] using
            (Relation.EqvGen.refl (initial r) : Related (before C) (initial r) (initial r))
        · apply (walk_collapse_retain C hne (Related (before C)) _ _ rs).mpr
          simpa [anchor₁,hL,hR] using hw
  | cons l ls =>
    cases hR : C.right with
    | nil =>
      have hw : Walk (Related (before C)) (terminal l) ls (initial l) := by
        simpa [hL,hR,Cycle] using hold
      have hpq : S (p C.edgeCount) (q C.edgeCount) := by
        simpa [S,anchor₀,anchor₁,hL,hR] using
          (Relation.EqvGen.refl (initial l) : Related (before C) (initial l) (initial l))
      refine ⟨?_, ?_⟩
      · change Cycle S (leftChild C)
        rw [leftChild,hL]
        apply (left_cycle_cons S l ls).mpr
        constructor
        · apply (walk_collapse_retain C hne (Related (before C)) _ _ ls).mpr
          simpa [anchor₀,hL,hR] using hw
        · simpa [S,anchor₁,hL,hR] using
            (Relation.EqvGen.refl (initial l) : Related (before C) (initial l) (initial l))
      · simpa [S,rightChild,hR,retainWord,Cycle,Walk,initial,terminal,p,q,collapse] using hpq
    | cons r rs =>
      have hw : Walk (Related (before C)) (terminal l) (ls ++ r :: rs) (initial l) := by
        simpa [hL,hR,Cycle] using hold
      have parts := (walk_append_cons (Related (before C))
        (terminal l) (initial l) ls r rs).mp hw
      refine ⟨?_, ?_⟩
      · change Cycle S (leftChild C)
        rw [leftChild,hL]
        apply (left_cycle_cons S l ls).mpr
        constructor
        · apply (walk_collapse_retain C hne (Related (before C)) _ _ ls).mpr
          simpa [anchor₀,hL,hR] using parts.1
        · simpa [S,anchor₁,hL,hR] using
            (Relation.EqvGen.refl (initial l) : Related (before C) (initial l) (initial l))
      · change Cycle S (rightChild C)
        rw [rightChild,hR]
        apply (right_cycle_cons S r rs).mpr
        constructor
        · simpa [S,anchor₀,hL,hR] using
            (Relation.EqvGen.refl (initial r) : Related (before C) (initial r) (initial r))
        · apply (walk_collapse_retain C hne (Related (before C)) _ _ rs).mpr
          simpa [anchor₁,hL,hR] using parts.2

private theorem old_step (C : DisplayedCut) (hne : C.left ++ C.right ≠ [])
    (x y : Endpoint C.edgeCount) (h : Step (before C) x y) :
    Related (split C) (oldEndpoint x) (oldEndpoint y) := by
  apply (allCycles_iff (before C) _).mp ?_ x y h
  intro w hw
  simp only [before, List.mem_append, List.mem_singleton] at hw
  rcases hw with hp | hs | ht
  · apply (cycle_retain (Related (split C)) w).mp
    apply generated_cycles (split C) (retainWord w)
    have hm : retainWord w ∈ C.prefix.map retainWord := List.mem_map.mpr ⟨w,hp,rfl⟩
    simp only [split, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inl hm
  · subst w
    exact (selected_lift C hne).1
  · apply (cycle_retain (Related (split C)) w).mp
    apply generated_cycles (split C) (retainWord w)
    have hm : retainWord w ∈ C.suffix.map retainWord := List.mem_map.mpr ⟨w,ht,rfl⟩
    simp only [split, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inr (Or.inr hm))

private theorem collapse_step (C : DisplayedCut) (hne : C.left ++ C.right ≠ [])
    (x y : Endpoint (C.edgeCount + 1)) (h : Step (split C) x y) :
    Related (before C) (collapse C hne x) (collapse C hne y) := by
  apply (allCycles_iff (split C) _).mp ?_ x y h
  intro w hw
  simp only [split, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with hp | hl | hr | ht
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hp
    apply (cycle_collapse_retain C hne (Related (before C)) v).mpr
    exact generated_cycles (before C) v (by simp [before,hv])
  · subst w
    exact (selected_collapse C hne).1
  · subst w
    exact (selected_collapse C hne).2
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ht
    apply (cycle_collapse_retain C hne (Related (before C)) v).mpr
    exact generated_cycles (before C) v (by simp [before,hv])

private theorem old_related (C : DisplayedCut) (hne : C.left ++ C.right ≠ [])
    {x y : Endpoint C.edgeCount} (h : Related (before C) x y) :
    Related (split C) (oldEndpoint x) (oldEndpoint y) := by
  induction h with
  | rel x y h => exact old_step C hne x y h
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂

private theorem collapse_related (C : DisplayedCut) (hne : C.left ++ C.right ≠ [])
    {x y : Endpoint (C.edgeCount + 1)} (h : Related (split C) x y) :
    Related (before C) (collapse C hne x) (collapse C hne y) := by
  induction h with
  | rel x y h => exact collapse_step C hne x y h
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂

/-- Includes all old endpoints and both fresh endpoints, with no distinctness premise. -/
private theorem endpoint_normalization (C : DisplayedCut) (hne : C.left ++ C.right ≠ [])
    (x : Endpoint (C.edgeCount + 1)) :
    Related (split C) x (oldEndpoint (collapse C hne x)) := by
  rcases x with ⟨e,b⟩
  refine Fin.lastCases ?_ (fun a => ?_) e
  · cases b with
    | false => simpa [collapse,p] using (selected_lift C hne).2.1
    | true => simpa [collapse,q] using (selected_lift C hne).2.2
  · simpa [collapse,oldEndpoint] using
      (Relation.EqvGen.refl (a.castSucc,b) :
        Related (split C) (a.castSucc,b) (a.castSucc,b))

def classMap (C : DisplayedCut) (hne : C.left ++ C.right ≠ []) :
    Vertices (split C) → Vertices (before C) :=
  Quotient.map (collapse C hne) (fun _ _ h => collapse_related C hne h)

def oldClassMap (C : DisplayedCut) (hne : C.left ++ C.right ≠ []) :
    Vertices (before C) → Vertices (split C) :=
  Quotient.map oldEndpoint (fun _ _ h => old_related C hne h)

/-- An explicit inverse pair on the quotients of the original literal seam relations. -/
def classesEquiv (C : DisplayedCut) (hne : C.left ++ C.right ≠ []) :
    Vertices (split C) ≃ Vertices (before C) where
  toFun := classMap C hne
  invFun := oldClassMap C hne
  left_inv := by
    intro v
    refine Quotient.inductionOn v ?_
    intro x
    exact Quotient.sound (endpoint_normalization C hne x).symm
  right_inv := by
    intro v
    refine Quotient.inductionOn v ?_
    intro x
    change Quotient.mk _ (collapse C hne (oldEndpoint x)) = Quotient.mk _ x
    rw [collapse_old]

/-- Displayed-face local P2 invariant. Hypothesis is ONLY that the selected word is
nonempty. Both one-sided-empty cuts and every monogon wrap are included. Euler is
the P1 combinatorial count, not topological genus. -/
theorem p2_generated_vertex_classes (C : DisplayedCut) (hne : C.left ++ C.right ≠ []) :
    (∀ xy : Endpoint (C.edgeCount + 1) × Endpoint (C.edgeCount + 1),
      Related (split C) xy.1 xy.2 ↔
        Related (before C) (collapse C hne xy.1) (collapse C hne xy.2)) ∧
    (∀ x : Endpoint C.edgeCount, collapse C hne (oldEndpoint x) = x) ∧
    (∀ x : Endpoint (C.edgeCount + 1),
      Related (split C) x (oldEndpoint (collapse C hne x))) ∧
    (∀ v : Vertices (before C), classesEquiv C hne (oldClassMap C hne v) = v) ∧
    Nat.card (Vertices (split C)) = Nat.card (Vertices (before C)) ∧
    (split C).edgeCount = (before C).edgeCount + 1 ∧
    (split C).faces.length = (before C).faces.length + 1 ∧
    euler (split C) = euler (before C) := by
  have hc := Nat.card_congr (classesEquiv C hne)
  have hf : (split C).faces.length = (before C).faces.length + 1 := by
    simp [split,before] <;> omega
  refine ⟨?_, collapse_old C hne, endpoint_normalization C hne,
    (classesEquiv C hne).apply_symm_apply, hc, rfl, hf, ?_⟩
  · rintro ⟨x,y⟩
    constructor
    · exact collapse_related C hne
    · intro h
      exact (endpoint_normalization C hne x).trans _ _ _
        ((old_related C hne h).trans _ _ _ (endpoint_normalization C hne y).symm)
  · unfold euler
    rw [hc,hf]
    change (Nat.card (Vertices (before C)) : ℤ) - ((C.edgeCount + 1 : ℕ) : ℤ) +
      (((before C).faces.length + 1 : ℕ) : ℤ) =
        (Nat.card (Vertices (before C)) : ℤ) - (C.edgeCount : ℤ) +
          ((before C).faces.length : ℤ)
    simp only [Nat.cast_add, Nat.cast_one]
    omega

namespace FullCut

/-- Reverse the traversal of one signed edge occurrence. -/
def flipDart {α : Type} : SignedDart α → SignedDart α
  | .pos e => .neg e
  | .neg e => .pos e

@[simp] private theorem flipDart_flipDart {α : Type} (d : SignedDart α) :
    flipDart (flipDart d) = d := by cases d <;> rfl

/-- The inverse word reverses order AND flips every sign. -/
def inverseWord {α : Type} (word : List (SignedDart α)) : List (SignedDart α) :=
  word.reverse.map flipDart

@[simp] private theorem inverseWord_inverseWord {α : Type}
    (word : List (SignedDart α)) : inverseWord (inverseWord word) = word := by
  simp [inverseWord, List.map_map, Function.comp_def]

@[simp] private theorem inverseWord_append {α : Type}
    (left right : List (SignedDart α)) :
    inverseWord (left ++ right) = inverseWord right ++ inverseWord left := by
  simp [inverseWord]

private theorem inverseWord_isRotated {α : Type}
    {left right : List (SignedDart α)} (h : left.IsRotated right) :
    (inverseWord left).IsRotated (inverseWord right) :=
  h.reverse.map flipDart

abbrev Face (P : FiniteCyclicPresentation) := Fin P.faces.length

def boundary (P : FiniteCyclicPresentation) (f : Face P) := P.faces.get f

/-- The source face is a list position together with its chosen traversal bit. -/
structure OrientedFace (P : FiniteCyclicPresentation) where
  face : Face P
  orientation : Bool

def OrientedFace.flip {P : FiniteCyclicPresentation} (f : OrientedFace P) :
    OrientedFace P := ⟨f.face, !f.orientation⟩

abbrev orientedBoundary (P : FiniteCyclicPresentation) (f : OrientedFace P) :=
  if f.orientation then inverseWord (boundary P f.face) else boundary P f.face

/-- A rotation of the actual oriented boundary, allowing either piece to be empty. -/
structure P2Cut (P : FiniteCyclicPresentation) where
  face : OrientedFace P
  left : List (SignedDart (Fin P.edgeCount))
  right : List (SignedDart (Fin P.edgeCount))
  boundary_rotated : (orientedBoundary P face).IsRotated (left ++ right)

private theorem orientedBoundary_flip (P : FiniteCyclicPresentation)
    (f : OrientedFace P) :
    orientedBoundary P f.flip = inverseWord (orientedBoundary P f) := by
  rcases f with ⟨f, b⟩
  cases b <;> simp [OrientedFace.flip, orientedBoundary]

/-- Genuine reversal of the chosen traversal also exchanges the two pieces. -/
def P2Cut.flip {P : FiniteCyclicPresentation} (cut : P2Cut P) : P2Cut P where
  face := cut.face.flip
  left := inverseWord cut.right
  right := inverseWord cut.left
  boundary_rotated := by
    rw [orientedBoundary_flip]
    simpa only [inverseWord_append] using inverseWord_isRotated cut.boundary_rotated

namespace P2

def freshEdge (P : FiniteCyclicPresentation) : Fin (P.edgeCount + 1) :=
  Fin.last P.edgeCount

/-- In a negative traversal, store the genuine inverse of the displayed child. -/
def storedWord {α : Type} (orientation : Bool) (word : List (SignedDart α)) :=
  if orientation then inverseWord word else word

def selectedOrientedBoundary (P : FiniteCyclicPresentation) (cut : P2Cut P) :=
  retainWord cut.left ++ [.pos (freshEdge P)]

def rightOrientedBoundary (P : FiniteCyclicPresentation) (cut : P2Cut P) :=
  .neg (freshEdge P) :: retainWord cut.right

def selectedBoundary (P : FiniteCyclicPresentation) (cut : P2Cut P) :=
  storedWord cut.face.orientation (selectedOrientedBoundary P cut)

def rightBoundary (P : FiniteCyclicPresentation) (cut : P2Cut P) :=
  storedWord cut.face.orientation (rightOrientedBoundary P cut)

/-- The first child occupies the selected old index; the second is at Fin.last. -/
def faceWord (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    Fin (P.faces.length + 1) → List (SignedDart (Fin (P.edgeCount + 1))) :=
  Fin.lastCases (rightBoundary P cut) fun f =>
    if f = cut.face.face then selectedBoundary P cut else retainWord (boundary P f)

abbrev split (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    FiniteCyclicPresentation where
  edgeCount := P.edgeCount + 1
  faces := List.ofFn (faceWord P cut)

end P2

/-- Display the chosen occurrence without changing the other face positions. -/
def displayed (P : FiniteCyclicPresentation) (cut : P2Cut P) : DisplayedCut where
  edgeCount := P.edgeCount
  «prefix» := P.faces.take cut.face.face.val
  suffix := P.faces.drop (cut.face.face.val + 1)
  left := cut.left
  right := cut.right

@[simp] private theorem initial_flip {n : ℕ} (d : SignedDart (Fin n)) :
    initial (flipDart d) = terminal d := by cases d <;> rfl

@[simp] private theorem terminal_flip {n : ℕ} (d : SignedDart (Fin n)) :
    terminal (flipDart d) = initial d := by cases d <;> rfl

/-- The literal cycle constraints differ only in their starting point. -/
private theorem cycle_append {n : ℕ} (R : Endpoint n → Endpoint n → Prop)
    (u v : List (SignedDart (Fin n))) : Cycle R (u ++ v) ↔ Cycle R (v ++ u) := by
  cases u with
  | nil => simp
  | cons a as =>
    cases v with
    | nil => simp
    | cons b bs =>
      simp only [List.cons_append, Cycle, walk_append_cons]
      exact and_comm

private theorem cycle_rotated {n : ℕ} (R : Endpoint n → Endpoint n → Prop)
    {u v : List (SignedDart (Fin n))} (h : u.IsRotated v) : Cycle R u ↔ Cycle R v := by
  rcases h with ⟨k, rfl⟩
  rw [List.rotate_eq_drop_append_take_mod, cycle_append]
  simp only [List.take_append_drop]

/-- Reversal reverses each seam; symmetry keeps the same endpoint identities. -/
private theorem walk_inverse {n : ℕ} (R : Endpoint n → Endpoint n → Prop)
    (hR : Symmetric R) (u : List (SignedDart (Fin n))) (p q : Endpoint n) :
    Walk R p (inverseWord u) q ↔ Walk R q u p := by
  induction u generalizing p q with
  | nil => exact ⟨fun h => hR h, fun h => hR h⟩
  | cons d ds ih =>
    have hi : inverseWord (d :: ds) = inverseWord ds ++ [flipDart d] := by
      simp [inverseWord]
    rw [hi, walk_append_cons]
    simp only [Walk, initial_flip, terminal_flip, ih]
    exact ⟨fun h => ⟨hR h.2, h.1⟩, fun h => ⟨h.2, hR h.1⟩⟩

private theorem cycle_inverse {n : ℕ} (R : Endpoint n → Endpoint n → Prop)
    (hR : Symmetric R) (u : List (SignedDart (Fin n))) :
    Cycle R (inverseWord u) ↔ Cycle R u := by
  cases u with
  | nil => rfl
  | cons d ds =>
    have hi : inverseWord (d :: ds) = inverseWord ds ++ [flipDart d] := by
      simp [inverseWord]
    rw [hi, cycle_append]
    simp only [List.singleton_append, Cycle, initial_flip, terminal_flip]
    exact walk_inverse R hR ds (initial d) (terminal d)

private theorem cycle_stored {n : ℕ} (R : Endpoint n → Endpoint n → Prop)
    (hR : Symmetric R) (b : Bool) (u : List (SignedDart (Fin n))) :
    Cycle R (P2.storedWord b u) ↔ Cycle R u := by
  cases b with
  | false => rfl
  | true => exact cycle_inverse R hR u

private theorem source_layout (P : FiniteCyclicPresentation) (f : Face P) :
    P.faces.take f.val ++ [boundary P f] ++ P.faces.drop (f.val + 1) = P.faces := by
  calc
    _ = P.faces.take f.val ++ (P.faces.get f :: P.faces.drop (f.val + 1)) := by
      simp only [boundary, List.singleton_append, List.append_assoc]
    _ = P.faces.take f.val ++ P.faces.drop f.val :=
      congrArg (fun t => P.faces.take f.val ++ t) (List.cons_get_drop_succ (l := P.faces) (n := f))
    _ = P.faces := List.take_append_drop f.val P.faces

private theorem selected_cycle (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (R : Endpoint P.edgeCount → Endpoint P.edgeCount → Prop) (hR : Symmetric R) :
    Cycle R (boundary P cut.face.face) ↔ Cycle R (cut.left ++ cut.right) := by
  have ho : Cycle R (boundary P cut.face.face) ↔ Cycle R (orientedBoundary P cut.face) := by
    cases hb : cut.face.orientation with
    | false => simp [orientedBoundary, hb]
    | true => simpa [orientedBoundary, hb] using
        (cycle_inverse R hR (boundary P cut.face.face)).symm
  exact ho.trans (cycle_rotated R cut.boundary_rotated)

private theorem before_cycles (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (R : Endpoint P.edgeCount → Endpoint P.edgeCount → Prop) (hR : Symmetric R) :
    (∀ w ∈ P.faces, Cycle R w) ↔ ∀ w ∈ (before (displayed P cut)).faces, Cycle R w := by
  change (∀ w ∈ P.faces, Cycle R w) ↔
    ∀ w ∈ P.faces.take cut.face.face.val ++ [cut.left ++ cut.right] ++
      P.faces.drop (cut.face.face.val + 1), Cycle R w
  conv_lhs => rw [← source_layout P cut.face.face]
  simp only [List.forall_mem_append, List.forall_mem_singleton]
  rw [selected_cycle P cut R hR]

/-- Pointwise equality with list replacement, rather than deletion of equal words. -/
private theorem split_faces_set (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (P2.split P cut).faces =
      (P.faces.map retainWord).set cut.face.face.val (P2.selectedBoundary P cut) ++
        [P2.rightBoundary P cut] := by
  change List.ofFn (P2.faceWord P cut) = _
  rw [List.ofFn_succ_last]
  change List.ofFn (fun f : Face P => P2.faceWord P cut f.castSucc) ++
    [P2.faceWord P cut (Fin.last P.faces.length)] = _
  have hlast : P2.faceWord P cut (Fin.last P.faces.length) = P2.rightBoundary P cut := by
    simp [P2.faceWord]
  rw [hlast]
  congr 1
  apply List.ext_getElem (by simp)
  intro i hi hj
  have hi' : i < P.faces.length := by simpa using hi
  by_cases h : i = cut.face.face.val
  · have he : (⟨i, hi'⟩ : Face P) = cut.face.face := Fin.ext h
    simp [List.getElem_ofFn, P2.faceWord, List.getElem_set, h, he]
  · have he : (⟨i, hi'⟩ : Face P) ≠ cut.face.face := fun e => h (congrArg Fin.val e)
    simp [List.getElem_ofFn, P2.faceWord, List.getElem_set, h, Ne.symm h, he,
      boundary, List.get_eq_getElem]

private theorem split_faces_layout (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (P2.split P cut).faces =
      (displayed P cut).prefix.map retainWord ++ [P2.selectedBoundary P cut] ++
        (displayed P cut).suffix.map retainWord ++ [P2.rightBoundary P cut] := by
  rw [split_faces_set, List.set_eq_take_append_cons_drop]
  have hi : cut.face.face.val < (P.faces.map retainWord).length := by
    simpa using cut.face.face.isLt
  simp [hi, displayed, List.map_take, List.map_drop, List.append_assoc]

/-- Only the second child's position moves past the suffix; multiplicities remain. -/
private theorem split_faces_perm (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (P2.split P cut).faces.Perm
      ((displayed P cut).prefix.map retainWord ++
        [P2.selectedBoundary P cut, P2.rightBoundary P cut] ++
        (displayed P cut).suffix.map retainWord) := by
  rw [split_faces_layout]
  have hm : ((displayed P cut).suffix.map retainWord ++ [P2.rightBoundary P cut]).Perm
      (P2.rightBoundary P cut :: (displayed P cut).suffix.map retainWord) := by
    simpa using (List.perm_append_comm (l₁ := (displayed P cut).suffix.map retainWord)
      (l₂ := [P2.rightBoundary P cut]))
  simpa only [List.append_assoc, List.singleton_append, List.cons_append] using
    (hm.cons (P2.selectedBoundary P cut)).append_left ((displayed P cut).prefix.map retainWord)

private theorem after_cycles (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (R : Endpoint (P.edgeCount + 1) → Endpoint (P.edgeCount + 1) → Prop)
    (hR : Symmetric R) :
    (∀ w ∈ (P2.split P cut).faces, Cycle R w) ↔
      ∀ w ∈ (split (displayed P cut)).faces, Cycle R w := by
  have hp := split_faces_perm P cut
  have hm : (∀ w ∈ (P2.split P cut).faces, Cycle R w) ↔
      ∀ w ∈ (displayed P cut).prefix.map retainWord ++
        [P2.selectedBoundary P cut, P2.rightBoundary P cut] ++
        (displayed P cut).suffix.map retainWord, Cycle R w :=
    ⟨fun h w hw => h w (hp.mem_iff.mpr hw), fun h w hw => h w (hp.mem_iff.mp hw)⟩
  rw [hm]
  change (∀ w ∈ (displayed P cut).prefix.map retainWord ++
    [P2.storedWord cut.face.orientation (leftChild (displayed P cut)),
     P2.storedWord cut.face.orientation (rightChild (displayed P cut))] ++
    (displayed P cut).suffix.map retainWord, Cycle R w) ↔ _
  simp only [split, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_nil,
    and_true, cycle_stored R hR]

private theorem before_related (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (x y : Endpoint P.edgeCount) :
    Related P x y ↔ Related (before (displayed P cut)) x y := by
  have hab : ∀ a b, Step P a b → Related (before (displayed P cut)) a b :=
    (allCycles_iff P _).mp ((before_cycles P cut _ (fun _ _ h => h.symm)).mpr
      (generated_cycles (before (displayed P cut))))
  have hba : ∀ a b, Step (before (displayed P cut)) a b → Related P a b :=
    (allCycles_iff (before (displayed P cut)) _).mp
      ((before_cycles P cut _ (fun _ _ h => h.symm)).mp (generated_cycles P))
  exact ⟨Relation.EqvGen.eqvGen_le hab, Relation.EqvGen.eqvGen_le hba⟩

private theorem after_related (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (x y : Endpoint (P.edgeCount + 1)) :
    Related (P2.split P cut) x y ↔ Related (split (displayed P cut)) x y := by
  have hab : ∀ a b, Step (P2.split P cut) a b → Related (split (displayed P cut)) a b :=
    (allCycles_iff (P2.split P cut) _).mp
      ((after_cycles P cut _ (fun _ _ h => h.symm)).mpr (generated_cycles (split (displayed P cut))))
  have hba : ∀ a b, Step (split (displayed P cut)) a b → Related (P2.split P cut) a b :=
    (allCycles_iff (split (displayed P cut)) _).mp
      ((after_cycles P cut _ (fun _ _ h => h.symm)).mp (generated_cycles (P2.split P cut)))
  exact ⟨Relation.EqvGen.eqvGen_le hab, Relation.EqvGen.eqvGen_le hba⟩

private def beforeClasses (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    Vertices (before (displayed P cut)) ≃ Vertices P where
  toFun := Quotient.map id (fun x y h => (before_related P cut x y).mpr h)
  invFun := Quotient.map id (fun x y h => (before_related P cut x y).mp h)
  left_inv v := Quotient.inductionOn v (fun _ => rfl)
  right_inv v := Quotient.inductionOn v (fun _ => rfl)

private def afterClasses (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    Vertices (P2.split P cut) ≃ Vertices (split (displayed P cut)) where
  toFun := Quotient.map id (fun x y h => (after_related P cut x y).mp h)
  invFun := Quotient.map id (fun x y h => (after_related P cut x y).mpr h)
  left_inv v := Quotient.inductionOn v (fun _ => rfl)
  right_inv v := Quotient.inductionOn v (fun _ => rfl)

/-- Collapse only the two fresh endpoints; all old edge names and bits stay fixed. -/
def fullCollapse (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (hne : cut.left ++ cut.right ≠ []) : Endpoint (P.edgeCount + 1) → Endpoint P.edgeCount :=
  collapse (displayed P cut) hne

/-- The equivalence transports endpoint representatives by identities at both interfaces. -/
def fullClassesEquiv (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (hne : cut.left ++ cut.right ≠ []) : Vertices (P2.split P cut) ≃ Vertices P :=
  (afterClasses P cut).trans
    ((classesEquiv (displayed P cut) hne).trans (beforeClasses P cut))

/-- The old class map is induced by literal castSucc, preserving the endpoint bit. -/
def fullOldClassMap (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (hne : cut.left ++ cut.right ≠ []) : Vertices P → Vertices (P2.split P cut) :=
  Quotient.map oldEndpoint (fun x y h => (after_related P cut _ _).mpr
    (old_related (displayed P cut) hne ((before_related P cut x y).mp h)))

/-- The complete oriented, rotated and position-preserving P2 endpoint statement.
The selected boundary is nonempty; either one of its two pieces may be empty. -/
theorem p2_full_generated_vertex_classes (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (hne : cut.left ++ cut.right ≠ []) :
    (∀ xy : Endpoint (P.edgeCount + 1) × Endpoint (P.edgeCount + 1),
      Related (P2.split P cut) xy.1 xy.2 ↔
        Related P (fullCollapse P cut hne xy.1) (fullCollapse P cut hne xy.2)) ∧
    (∀ x : Endpoint P.edgeCount, fullCollapse P cut hne (oldEndpoint x) = x) ∧
    (∀ x : Endpoint (P.edgeCount + 1),
      Related (P2.split P cut) x (oldEndpoint (fullCollapse P cut hne x))) ∧
    (∀ x : Endpoint P.edgeCount,
      fullClassesEquiv P cut hne (Quotient.mk _ (oldEndpoint x)) = Quotient.mk _ x) ∧
    (∀ v : Vertices P, fullClassesEquiv P cut hne (fullOldClassMap P cut hne v) = v) ∧
    Nat.card (Vertices (P2.split P cut)) = Nat.card (Vertices P) ∧
    (P2.split P cut).edgeCount = P.edgeCount + 1 ∧
    (P2.split P cut).faces.length = P.faces.length + 1 ∧
    euler (P2.split P cut) = euler P ∧
    (∀ x y : Endpoint P.edgeCount,
      Related P x y ↔ Related (before (displayed P cut)) x y) ∧
    (∀ x y : Endpoint P.edgeCount,
      Related (before (displayed P cut.flip)) x y ↔ Related P x y) := by
  have hlocal := p2_generated_vertex_classes (displayed P cut) hne
  have hcomm : ∀ x : Endpoint P.edgeCount,
      fullClassesEquiv P cut hne (Quotient.mk _ (oldEndpoint x)) = Quotient.mk _ x := by
    intro x
    change Quotient.mk _ (collapse (displayed P cut) hne (oldEndpoint x)) = Quotient.mk _ x
    rw [hlocal.2.1 x]
  have hc := Nat.card_congr (fullClassesEquiv P cut hne)
  have hf : (P2.split P cut).faces.length = P.faces.length + 1 := by
    simp [P2.split]
  refine ⟨?_, hlocal.2.1, ?_, hcomm, ?_, hc, rfl, hf, ?_, before_related P cut,
    fun x y => (before_related P cut.flip x y).symm⟩
  · intro xy
    exact (after_related P cut xy.1 xy.2).trans
      ((hlocal.1 xy).trans (before_related P cut _ _).symm)
  · intro x
    exact (after_related P cut _ _).mpr (hlocal.2.2.1 x)
  · intro v
    refine Quotient.inductionOn v ?_
    exact hcomm
  · unfold euler
    rw [hc, hf]
    change (Nat.card (Vertices P) : ℤ) - ((P.edgeCount + 1 : ℕ) : ℤ) +
      (((P.faces.length + 1 : ℕ) : ℤ)) =
        (Nat.card (Vertices P) : ℤ) - (P.edgeCount : ℤ) + (P.faces.length : ℤ)
    simp only [Nat.cast_add, Nat.cast_one]
    omega

end FullCut

end D5.S3.Geometry.Gluing.CyclicP2GeneratedVertices
