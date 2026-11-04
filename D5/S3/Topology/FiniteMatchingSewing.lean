/- GID: D5/S3/Topology/FiniteMatchingSewing
   generality: G
   mirror-B: D5/B/S3/Topology/FiniteMatchingSewing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   utility: none
   digest: Sewing partitions actual components and computes closed matching stacks. -/
import D5.S3.Topology.FiniteMatchingComposition

/-!
Sewing actual finite pairing networks.
The component inventory is constructed here, not supplied as a field.
No planarity assumption is used: these are Brauer pairings, including N=0
and differently colored parallel edges. Circle weights belong to consumers.
-/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Topology.FiniteMatchingSewing

attribute [local instance] Classical.propDecidable

open D5.S3.Topology.FiniteMatchingClosure
open D5.S3.Topology.FiniteMatchingComposition

theorem matching_ext {V : Type*} {d e : Matching V}
    (h : ∀ v, d.mate v = e.mate v) : d = e := by
  cases d with
  | mk d hd hdf =>
    cases e with
    | mk e he hef =>
      have hde : d = e := funext h
      subst e
      rfl

def componentMap {X Y : Type*} (r : X → X → Prop) (s : Y → Y → Prop)
    (f : X → Y) (hf : ∀ x y, r x y → Relation.EqvGen s (f x) (f y)) :
    Component r → Component s := Quotient.lift (fun x => component s (f x)) (by
  intro x y h
  apply Quotient.sound
  induction h with
  | rel x y h => exact hf x y h
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂)

theorem matching_component_iff {V : Type*} (d : Matching V) (a b : V) :
    component (fun x y => y = d.mate x) a =
      component (fun x y => y = d.mate x) b ↔ b = a ∨ b = d.mate a := by
  constructor
  · intro h
    have hp : Relation.EqvGen (fun x y => y = d.mate x) a b := Quotient.eq.mp h
    clear h
    induction hp with
    | rel x y h => exact Or.inr h
    | refl => exact Or.inl rfl
    | symm x y h ih =>
      rcases ih with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h, d.involutive])
    | trans x y z hxy hyz ih₁ ih₂ =>
      rcases ih₁ with rfl | h₁
      · exact ih₂
      · rcases ih₂ with h₂ | h₂
        · exact Or.inr (h₂.trans h₁)
        · exact Or.inl (by rw [h₂, h₁, d.involutive])
  · rintro (rfl | h)
    · rfl
    · exact Quotient.sound (.rel _ _ h)

/-! A generic sewing lemma. Its only endpoint input is the already proved
local partner characterization. In particular no global count is an input. -/

section Sewing
variable {X B : Type*} (r : X → X → Prop) (a : B → X)
    (d : Matching B) (t : B → B)
    (hend : ∀ b c, component r (a b) = component r (a c) ↔
      c = b ∨ c = d.mate b)

def sewStep (x y : X) : Prop := r x y ∨ ∃ b, x = a b ∧ y = a (t b)

def Unmarked := {q : Component r // ∀ b, component r (a b) ≠ q}

def sewnOpenMap : Component r → Component (sewStep r a t) :=
  componentMap r (sewStep r a t) id (fun _ _ h => .rel _ _ (Or.inl h))

def sewnBoundaryMap : Component (twoStep d.mate t) → Component (sewStep r a t) :=
  componentMap (twoStep d.mate t) (sewStep r a t) a (by
    intro b c h
    rcases h with h | h
    · have hp := Quotient.eq.mp ((hend b c).mpr (Or.inr h))
      exact Quotient.eq.mp (congrArg (sewnOpenMap r a t) (Quotient.sound hp))
    · exact .rel _ _ (Or.inr ⟨b, rfl, congrArg a h⟩))

def componentLabel (q : Component r) :
    Unmarked r a ⊕ Component (twoStep d.mate t) :=
  if h : ∃ b, component r (a b) = q then
    .inr (component (twoStep d.mate t) (Classical.choose h))
  else .inl ⟨q, fun b hb => h ⟨b, hb⟩⟩

include hend in
theorem componentLabel_boundary (b : B) :
    componentLabel r a d t (component r (a b)) =
      Sum.inr (component (twoStep d.mate t) b) := by
  unfold componentLabel
  have hh : ∃ c, component r (a c) = component r (a b) := ⟨b, rfl⟩
  rw [dif_pos hh]
  apply congrArg Sum.inr
  rcases (hend _ b).mp (Classical.choose_spec hh) with h | h
  · exact congrArg (component (twoStep d.mate t)) h.symm
  · exact Quotient.sound (.rel _ _ (Or.inl h))

theorem componentLabel_unmarked (q : Unmarked r a) :
    componentLabel r a d t q.1 = Sum.inl q := by
  unfold componentLabel
  rw [dif_neg (by rintro ⟨b, h⟩; exact q.2 b h)]
  rfl

def sewnLabel : Component (sewStep r a t) →
    Unmarked r a ⊕ Component (twoStep d.mate t) :=
  Quotient.lift (fun x => componentLabel r a d t (component r x)) (by
    intro x y hp
    induction hp with
    | rel x y h =>
      rcases h with h | ⟨b, rfl, rfl⟩
      · exact congrArg (componentLabel r a d t) (Quotient.sound (.rel _ _ h))
      · rw [componentLabel_boundary r a d t hend,
          componentLabel_boundary r a d t hend]
        exact congrArg Sum.inr (Quotient.sound (.rel _ _ (Or.inr rfl)))
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

theorem sewnLabel_open (q : Component r) :
    sewnLabel r a d t hend (sewnOpenMap r a t q) = componentLabel r a d t q := by
  induction q using Quotient.inductionOn with
  | _ x => rfl

def sewingInventory : Component (sewStep r a t) ≃
    Unmarked r a ⊕ Component (twoStep d.mate t) where
  toFun := sewnLabel r a d t hend
  invFun := Sum.elim (fun q => sewnOpenMap r a t q.1)
    (sewnBoundaryMap r a d t hend)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ x =>
      change Sum.elim _ _ (componentLabel r a d t (component r x)) = _
      unfold componentLabel
      split_ifs with h
      · change component (sewStep r a t) (a (Classical.choose h)) = _
        exact congrArg (sewnOpenMap r a t) (Classical.choose_spec h)
      · rfl
  right_inv q := by
    cases q with
    | inl q =>
      change sewnLabel r a d t hend (sewnOpenMap r a t q.1) = Sum.inl q
      exact (sewnLabel_open r a d t hend q.1).trans (componentLabel_unmarked r a d t q)
    | inr q =>
      induction q using Quotient.inductionOn with
      | _ b => exact componentLabel_boundary r a d t hend b

end Sewing

/-! Straight strands really are units for the first-return composite. -/

def rightCollapse {N : ℕ} (x : GluingVertex N) : Boundary N :=
  (if x.1 = 0 then false else true, x.2)

def leftCollapse {N : ℕ} (x : GluingVertex N) : Boundary N :=
  (if x.1 = 2 then true else false, x.2)

theorem rightCollapse_outer {N : ℕ} (a : Boundary N) : rightCollapse (outer a) = a := by
  rcases a with ⟨b, i⟩; cases b <;> rfl

theorem leftCollapse_outer {N : ℕ} (a : Boundary N) : leftCollapse (outer a) = a := by
  rcases a with ⟨b, i⟩; cases b <;> rfl

theorem rightCollapse_upper {N : ℕ} (a : Boundary N) : rightCollapse (upper a) = a := by
  rcases a with ⟨b, i⟩; cases b <;> rfl

theorem leftCollapse_lower {N : ℕ} (a : Boundary N) : leftCollapse (lower a) = a := by
  rcases a with ⟨b, i⟩; cases b <;> rfl

def rightUnitComponents {N : ℕ} (d : Matching (Boundary N)) :
    Component (gluingStep d (identityMatching N)) ≃
      Component (fun x y => y = d.mate x) := by
  apply contractionEquiv _ _ rightCollapse outer rightCollapse_outer
  · intro x y h
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl⟩
    · simpa only [rightCollapse_upper] using
        (Relation.EqvGen.rel a (d.mate a) rfl :
          Relation.EqvGen (fun x y => y = d.mate x) a (d.mate a))
    · rcases a with ⟨b, i⟩; cases b <;> exact .refl _
  · intro x y h
    subst y
    have fiber (a : Boundary N) : Relation.EqvGen (gluingStep d (identityMatching N))
        (upper a) (outer a) := by
      rcases a with ⟨b, i⟩
      cases b
      · exact .refl _
      · exact .rel _ _ (Or.inr ⟨(false, i), rfl, rfl⟩)
    exact .trans _ _ _ (.symm _ _ (fiber x))
      (.trans _ _ _ (.rel _ _ (Or.inl ⟨x, rfl, rfl⟩)) (fiber (d.mate x)))
  · intro x
    rcases x with ⟨l, i⟩
    fin_cases l
    · exact .refl _
    · exact .rel _ _ (Or.inr ⟨(false, i), rfl, rfl⟩)
    · exact .refl _

def leftUnitComponents {N : ℕ} (d : Matching (Boundary N)) :
    Component (gluingStep (identityMatching N) d) ≃
      Component (fun x y => y = d.mate x) := by
  apply contractionEquiv _ _ leftCollapse outer leftCollapse_outer
  · intro x y h
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl⟩
    · rcases a with ⟨b, i⟩; cases b <;> exact .refl _
    · simpa only [leftCollapse_lower] using
        (Relation.EqvGen.rel a (d.mate a) rfl :
          Relation.EqvGen (fun x y => y = d.mate x) a (d.mate a))
  · intro x y h
    subst y
    have fiber (a : Boundary N) : Relation.EqvGen (gluingStep (identityMatching N) d)
        (lower a) (outer a) := by
      rcases a with ⟨b, i⟩
      cases b
      · exact .symm _ _ (.rel _ _ (Or.inl ⟨(false, i), rfl, rfl⟩))
      · exact .refl _
    exact .trans _ _ _ (.symm _ _ (fiber x))
      (.trans _ _ _ (.rel _ _ (Or.inr ⟨x, rfl, rfl⟩)) (fiber (d.mate x)))
  · intro x
    rcases x with ⟨l, i⟩
    fin_cases l
    · exact .refl _
    · exact .symm _ _ (.rel _ _ (Or.inl ⟨(false, i), rfl, rfl⟩))
    · exact .refl _

theorem composite_right_identity {N : ℕ} (d : Matching (Boundary N)) :
    composite d (identityMatching N) = d := by
  apply matching_ext
  intro a
  have h := (triple_component_iff d (identityMatching N) a
    ((composite d (identityMatching N)).mate a)).mpr (Or.inr rfl)
  have hm := congrArg (rightUnitComponents d) h
  change component (fun x y => y = d.mate x) (rightCollapse (outer a)) =
    component (fun x y => y = d.mate x)
      (rightCollapse (outer ((composite d (identityMatching N)).mate a))) at hm
  rw [rightCollapse_outer, rightCollapse_outer] at hm
  rcases (matching_component_iff d _ _).mp hm with h | h
  · exact False.elim ((composite d (identityMatching N)).fixedPointFree a h)
  · exact h

theorem composite_left_identity {N : ℕ} (d : Matching (Boundary N)) :
    composite (identityMatching N) d = d := by
  apply matching_ext
  intro a
  have h := (triple_component_iff (identityMatching N) d a
    ((composite (identityMatching N) d).mate a)).mpr (Or.inr rfl)
  have hm := congrArg (leftUnitComponents d) h
  change component (fun x y => y = d.mate x) (leftCollapse (outer a)) =
    component (fun x y => y = d.mate x)
      (leftCollapse (outer ((composite (identityMatching N) d).mate a))) at hm
  rw [leftCollapse_outer, leftCollapse_outer] at hm
  rcases (matching_component_iff d _ _).mp hm with h | h
  · exact False.elim ((composite (identityMatching N) d).fixedPointFree a h)
  · exact h

theorem internalLoopCount_right_identity {N : ℕ} (d : Matching (Boundary N)) :
    internalLoopCount d (identityMatching N) = 0 := by
  rw [internalLoopCount_eq]
  letI : IsEmpty (InternalComponent d (identityMatching N)) := ⟨by
    rintro ⟨q, hq⟩
    induction q using Quotient.inductionOn with
    | _ x =>
      rcases x with ⟨l, i⟩
      fin_cases l
      · exact hq (false, i) rfl
      · exact hq (true, i) (Quotient.sound
          (.symm _ _ (.rel _ _ (Or.inr ⟨(false, i), rfl, rfl⟩))))
      · exact hq (true, i) rfl⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

theorem internalLoopCount_left_identity {N : ℕ} (d : Matching (Boundary N)) :
    internalLoopCount (identityMatching N) d = 0 := by
  rw [internalLoopCount_eq]
  letI : IsEmpty (InternalComponent (identityMatching N) d) := ⟨by
    rintro ⟨q, hq⟩
    induction q using Quotient.inductionOn with
    | _ x =>
      rcases x with ⟨l, i⟩
      fin_cases l
      · exact hq (false, i) rfl
      · exact hq (false, i) (Quotient.sound
          (.rel _ _ (Or.inl ⟨(false, i), rfl, rfl⟩)))
      · exact hq (true, i) rfl⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

/-! Closing the stack before or after composition. -/

def ClosedComponent {N : ℕ} (d : Matching (Boundary N)) :=
  Component (twoStep d.mate (identityMatching N).mate)

instance {N : ℕ} (d : Matching (Boundary N)) : Finite (ClosedComponent d) := by
  unfold ClosedComponent
  infer_instance

def closedCount {N : ℕ} (d : Matching (Boundary N)) : ℕ := Nat.card (ClosedComponent d)

def closedWire {N : ℕ} (x : Piece N) : Piece N := (!x.1, (!x.2.1, x.2.2))

def closedStackStep {N : ℕ} (d e : Matching (Boundary N)) :=
  twoStep (piecesMate d e) (@closedWire N)

def sewnStackEquiv {N : ℕ} (d e : Matching (Boundary N)) :
    Component (closedStackStep d e) ≃
      Component (sewStep (halfEdgeStep d e) outerPiece (identityMatching N).mate) := by
  apply contractionEquiv _ _ id id (fun _ => rfl)
  · intro x y h
    rcases h with h | h
    · exact .rel _ _ (Or.inl (Or.inl h))
    · subst y
      rcases x with ⟨l, b, i⟩
      cases l <;> cases b
      · exact .rel _ _ (Or.inr ⟨(false, i), rfl, rfl⟩)
      · exact .rel _ _ (Or.inl (Or.inr rfl))
      · exact .rel _ _ (Or.inl (Or.inr rfl))
      · exact .rel _ _ (Or.inr ⟨(true, i), rfl, rfl⟩)
  · intro x y h
    rcases h with (h | h) | ⟨a, rfl, rfl⟩
    · exact .rel _ _ (Or.inl h)
    · subst y
      rcases x with ⟨l, b, i⟩
      cases l <;> cases b
      · exact .refl _
      · exact .rel _ _ (Or.inr rfl)
      · exact .rel _ _ (Or.inr rfl)
      · exact .refl _
    · rcases a with ⟨b, i⟩; cases b <;> exact .rel _ _ (Or.inr rfl)
  · intro x; exact .refl _

def closedStackInventory {N : ℕ} (d e : Matching (Boundary N)) :
    Component (closedStackStep d e) ≃
      halfEdgeInternalComponent d e ⊕ ClosedComponent (composite d e) :=
  (sewnStackEquiv d e).trans
    (sewingInventory (halfEdgeStep d e) outerPiece (composite d e)
      (identityMatching N).mate (composite_component_iff d e))

theorem closedStack_card {N : ℕ} (d e : Matching (Boundary N)) :
    Nat.card (Component (closedStackStep d e)) =
      internalLoopCount d e + closedCount (composite d e) := by
  rw [Nat.card_congr (closedStackInventory d e), Nat.card_sum]
  rfl

def rotatePiece {N : ℕ} (x : Piece N) : Piece N := (!x.1, x.2)

def rotateClosedStack {N : ℕ} (d e : Matching (Boundary N)) :
    Component (closedStackStep d e) ≃ Component (closedStackStep e d) := by
  apply contractionEquiv _ _ rotatePiece rotatePiece
    (by rintro ⟨l, b, i⟩; cases l <;> rfl)
  · intro x y h
    rcases h with h | h <;> subst y
    · rcases x with ⟨l, b, i⟩; cases l <;> exact .rel _ _ (Or.inl rfl)
    · rcases x with ⟨l, b, i⟩; cases l <;> cases b <;> exact .rel _ _ (Or.inr rfl)
  · intro x y h
    rcases h with h | h <;> subst y
    · rcases x with ⟨l, b, i⟩; cases l <;> exact .rel _ _ (Or.inl rfl)
    · rcases x with ⟨l, b, i⟩; cases l <;> cases b <;> exact .rel _ _ (Or.inr rfl)
  · rintro ⟨l, b, i⟩; cases l <;> exact .refl _

theorem closed_weight_cyclic {N : ℕ} (d e : Matching (Boundary N)) :
    internalLoopCount d e + closedCount (composite d e) =
      internalLoopCount e d + closedCount (composite e d) := by
  rw [← closedStack_card, ← closedStack_card]
  exact Nat.card_congr (rotateClosedStack d e)

def identityClosureEquiv (N : ℕ) : ClosedComponent (identityMatching N) ≃ Fin N := by
  let F : ClosedComponent (identityMatching N) → Fin N :=
    Quotient.lift Prod.snd (by
      intro x y h
      induction h with
      | rel x y h => rcases h with h | h <;> subst y <;> rfl
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)
  exact {
    toFun := F
    invFun := fun i => component _ (false, i)
    left_inv := by
      intro q
      induction q using Quotient.inductionOn with
      | _ x =>
        rcases x with ⟨b, i⟩
        cases b
        · rfl
        · exact Quotient.sound (.rel _ _ (Or.inl rfl))
    right_inv := fun _ => rfl }

theorem closedCount_identity (N : ℕ) : closedCount (identityMatching N) = N := by
  unfold closedCount
  rw [Nat.card_congr (identityClosureEquiv N), Nat.card_fin]

end D5.S3.Topology.FiniteMatchingSewing
