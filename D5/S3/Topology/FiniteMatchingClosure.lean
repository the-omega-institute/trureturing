/- GID: D5/S3/Topology/FiniteMatchingClosure
   generality: G
   mirror-B: D5/B/S3/Topology/FiniteMatchingClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   utility: none
   digest: Matching networks and explicit series contraction preserve components. -/
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
Finite matching networks preserve both edge colors, including parallel edges.
Series contraction identifies the component quotients by explicit inverse maps.
The three-layer graph records the literal matching multiplication network.
-/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Topology.FiniteMatchingClosure

structure Matching (V : Type*) where
  mate : V → V
  involutive : Function.Involutive mate
  fixedPointFree : ∀ v, mate v ≠ v

abbrev Component {V : Type*} (r : V → V → Prop) :=
  Quotient (Relation.EqvGen.setoid r)

def component {V : Type*} (r : V → V → Prop) (v : V) : Component r :=
  Quotient.mk _ v

def Coloring {V : Type*} (r : V → V → Prop) (C : Type*) :=
  {f : V → C // ∀ x y, r x y → f x = f y}

theorem coloring_respects {V C : Type*} {r : V → V → Prop}
    (f : Coloring r C) {x y : V} (h : Relation.EqvGen r x y) : f.1 x = f.1 y := by
  induction h with
  | rel x y h => exact f.2 x y h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A closed network coloring is exactly one independent color per component.
No degree, planarity, nondegeneracy or distinct-edge hypothesis is needed. -/
def coloringEquiv {V : Type*} (r : V → V → Prop) (C : Type*) :
    Coloring r C ≃ (Component r → C) where
  toFun f := Quotient.lift f.1 (fun _ _ h => coloring_respects f h)
  invFun f := ⟨fun v => f (component r v), fun x y h =>
    congrArg f (Quotient.sound (Relation.EqvGen.rel x y h))⟩
  left_inv f := by
    apply Subtype.ext
    rfl
  right_inv f := by
    funext q
    induction q using Quotient.inductionOn with
    | _ v => rfl

theorem coloring_card {V C : Type*} [Finite V]
    (r : V → V → Prop) :
    Nat.card (Coloring r C) = Nat.card C ^ Nat.card (Component r) := by
  rw [Nat.card_congr (coloringEquiv r C), Nat.card_fun]

/-- Retraction/series contraction of a network. Each removed vertex is
connected to its retained representative; every edge lifts in both directions.
These are local path obligations, rather than a component-count assumption. -/
def contractionEquiv {V W : Type*} (r : V → V → Prop) (s : W → W → Prop)
    (f : V → W) (g : W → V) (hfg : ∀ y, f (g y) = y)
    (hf : ∀ x y, r x y → Relation.EqvGen s (f x) (f y))
    (hg : ∀ x y, s x y → Relation.EqvGen r (g x) (g y))
    (hfiber : ∀ x, Relation.EqvGen r x (g (f x))) :
    Component r ≃ Component s := by
  let F : Component r → Component s := Quotient.lift
    (fun x => component s (f x)) (by
      intro x y h
      apply Quotient.sound
      induction h with
      | rel x y h => exact hf x y h
      | refl => exact .refl _
      | symm _ _ _ ih => exact .symm _ _ ih
      | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂)
  let G : Component s → Component r := Quotient.lift
    (fun x => component r (g x)) (by
      intro x y h
      apply Quotient.sound
      induction h with
      | rel x y h => exact hg x y h
      | refl => exact .refl _
      | symm _ _ _ ih => exact .symm _ _ ih
      | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂)
  exact {
    toFun := F
    invFun := G
    left_inv := by
      intro q
      induction q using Quotient.inductionOn with
      | _ x => exact Quotient.sound (.symm _ _ (hfiber x))
    right_inv := by
      intro q
      induction q using Quotient.inductionOn with
      | _ x => change component s (f (g x)) = component s x; rw [hfg]
  }

def twoStep {V : Type*} (s t : V → V) (x y : V) : Prop :=
  y = s x ∨ y = t x

/-- Two matching layers before identifying their common dart labels.
The cross-layer edges are actual wires; the within-layer edges are the
two matchings. This is a degree-two colored multigraph, including bigons. -/
def overlayStep {V : Type*} (s t : V → V) : Sum V V → Sum V V → Prop
  | .inl x, .inl y => y = s x
  | .inr x, .inr y => y = t x
  | .inl x, .inr y => y = x
  | .inr x, .inl y => y = x

/-- Suppressing every external wire gives precisely the quotient generated
by the two matchings. This is a concrete gluing theorem, with no cardinality
or Jones equality among its hypotheses. Involutivity is not even needed. -/
def overlayEquiv {V : Type*} (s t : V → V) :
    Component (overlayStep s t) ≃ Component (twoStep s t) := by
  apply contractionEquiv (overlayStep s t) (twoStep s t)
    (Sum.elim id id) Sum.inl (fun _ => rfl)
  · intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact .rel _ _ (Or.inl h)
      | inr y => change y = x at h; subst y; exact .refl _
    | inr x =>
      cases y with
      | inl y => change y = x at h; subst y; exact .refl _
      | inr y => exact .rel _ _ (Or.inr h)
  · intro x y h
    rcases h with h | h
    · exact .rel _ _ h
    · exact .trans _ _ _
        (.rel _ _ (show overlayStep s t (.inl x) (.inr x) from rfl))
        (.trans _ _ _
          (.rel _ _ (show overlayStep s t (.inr x) (.inr y) from h))
          (.rel _ _ (show overlayStep s t (.inr y) (.inl y) from rfl)))
  · intro x
    cases x with
    | inl x => exact .refl _
    | inr x => exact .rel _ _ rfl

theorem overlay_component_card {V : Type*} (s t : V → V) :
    Nat.card (Component (overlayStep s t)) = Nat.card (Component (twoStep s t)) :=
  Nat.card_congr (overlayEquiv s t)

abbrev Boundary (N : ℕ) := Bool × Fin N

def identityMatching (N : ℕ) : Matching (Boundary N) where
  mate x := (!x.1, x.2)
  involutive x := by cases x with | mk b i => cases b <;> rfl
  fixedPointFree x := by cases x with | mk b i => cases b <;> simp

/-- The literal cup at the top, cap at the bottom, and all remaining vertical
strands. The printed generator index is j+1; j itself is zero based. -/
def cupcapMate {N : ℕ} (j : ℕ) (hj : j + 1 < N) (x : Boundary N) : Boundary N :=
  if x.2.val = j then (x.1, ⟨j+1,hj⟩)
  else if x.2.val = j+1 then (x.1, ⟨j,by omega⟩)
  else (!x.1,x.2)

theorem cupcapMate_involutive {N : ℕ} (j : ℕ) (hj : j+1 < N) :
    Function.Involutive (cupcapMate j hj) := by
  rintro ⟨b,i⟩
  by_cases h₀ : i.val = j
  · simp [cupcapMate, h₀, show j+1 ≠ j by omega, Prod.ext_iff, Fin.ext_iff]
  · by_cases h₁ : i.val = j+1
    · simp [cupcapMate, h₀, h₁, show j ≠ j+1 by omega, Prod.ext_iff, Fin.ext_iff]
    · cases b <;> simp [cupcapMate, h₀, h₁]

theorem cupcapMate_fixedPointFree {N : ℕ} (j : ℕ) (hj : j+1 < N)
    (x : Boundary N) : cupcapMate j hj x ≠ x := by
  rcases x with ⟨b,i⟩
  by_cases h₀ : i.val = j
  · intro h
    have := congrArg (fun z : Boundary N => z.2.val) h
    simp [cupcapMate, h₀] at this
  · by_cases h₁ : i.val = j+1
    · intro h
      have := congrArg (fun z : Boundary N => z.2.val) h
      simp [cupcapMate, h₁] at this
    · cases b <;> simp [cupcapMate, h₀, h₁]

def cupcapMatching {N : ℕ} (j : ℕ) (hj : j+1 < N) : Matching (Boundary N) :=
  ⟨cupcapMate j hj, cupcapMate_involutive j hj, cupcapMate_fixedPointFree j hj⟩

abbrev GluingVertex (N : ℕ) := Fin 3 × Fin N

def upper {N : ℕ} (x : Boundary N) : GluingVertex N :=
  (if x.1 then 1 else 0, x.2)

def lower {N : ℕ} (x : Boundary N) : GluingVertex N :=
  (if x.1 then 2 else 1, x.2)

def outer {N : ℕ} (x : Boundary N) : GluingVertex N :=
  (if x.1 then 2 else 0, x.2)

def gluingStep {N : ℕ} (d e : Matching (Boundary N))
    (x y : GluingVertex N) : Prop :=
  (∃ a, x = upper a ∧ y = upper (d.mate a)) ∨
  (∃ a, x = lower a ∧ y = lower (e.mate a))

def InternalComponent {N : ℕ} (d e : Matching (Boundary N)) :=
  {c : Component (gluingStep d e) //
    ∀ a, component (gluingStep d e) (outer a) ≠ c}

end D5.S3.Topology.FiniteMatchingClosure
