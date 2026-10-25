/- GID: D5/S3/Geometry/Gluing/CyclicP1GeneratedVertices
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/CyclicP1GeneratedVertices
   mirror-E: none(waiver:finite-cyclic-p1-generated-endpoint-classes)
   anchors: [mathlib/module/Mathlib.Logic.Relation,
     mathlib/module/Mathlib.SetTheory.Cardinal.Finite]
   utility: none
   digest: Actual P1 face expansion adds exactly one generated endpoint class. -/

/-
Selected definitions adapted from LeanPool/ClassificationOfSurfaces/{CellComplex,
FiniteCyclicPresentation,FiniteCyclicP1}.lean at
edbe5bd56f476cc2965564676b66199f281ab714.
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Authors: Ryan McCorvie, Jack McCarthy.
Released under Apache 2.0; see docs/reports/licenses/lean-pool-surface/LICENSE.txt and NOTICE.txt.
The definitions use this D5 namespace and the current Mathlib imports.
The generated endpoint relation and its proofs use the actual cyclic face seams.
-/

import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Quot
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.DeriveFintype
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
noncomputable section

namespace D5.S3.Geometry.Gluing.CyclicP1GeneratedVertices

/-- Minimal faithful port of the selected signed-word datatype. -/
inductive SignedDart (α : Type) where
  | pos : α → SignedDart α
  | neg : α → SignedDart α
  deriving DecidableEq, Repr, Fintype

def SignedDart.edge {α : Type} : SignedDart α → α
  | .pos e => e
  | .neg e => e

/-- Faces remain list positions, including equal words and empty words. -/
structure FiniteCyclicPresentation where
  edgeCount : ℕ
  faces : List (List (SignedDart (Fin edgeCount)))

/-- False is the stored initial endpoint, true the stored terminal endpoint. -/
abbrev Endpoint (n : ℕ) := Fin n × Bool

def initial {n : ℕ} : SignedDart (Fin n) → Endpoint n
  | .pos e => (e, false)
  | .neg e => (e, true)

def terminal {n : ℕ} : SignedDart (Fin n) → Endpoint n
  | .pos e => (e, true)
  | .neg e => (e, false)

/-- Read the remaining word, starting at p and closing at q. -/
def seams {n : ℕ} (p : Endpoint n) :
    List (SignedDart (Fin n)) → Endpoint n → List (Endpoint n × Endpoint n)
  | [], q => [(p, q)]
  | d :: ds, q => (p, initial d) :: seams (terminal d) ds q

/-- Exactly the cyclic terminal-to-next-initial seams. Empty faces add no seam. -/
def cyclePairs {n : ℕ} :
    List (SignedDart (Fin n)) → List (Endpoint n × Endpoint n)
  | [] => []
  | d :: ds => seams (terminal d) ds (initial d)

/-- No edge endpoint is identified except by a literal face seam and EqvGen. -/
def Step (P : FiniteCyclicPresentation) (x y : Endpoint P.edgeCount) : Prop :=
  ∃ w ∈ P.faces, (x, y) ∈ cyclePairs w

abbrev Related (P : FiniteCyclicPresentation) := Relation.EqvGen (Step P)

def vertexSetoid (P : FiniteCyclicPresentation) : Setoid (Endpoint P.edgeCount) :=
  Relation.EqvGen.setoid (Step P)

/-- The quotient is defined from the actual seams, never from a disjoint sum. -/
abbrev Vertices (P : FiniteCyclicPresentation) := Quotient (vertexSetoid P)

def Occurs (P : FiniteCyclicPresentation) (a : Fin P.edgeCount) : Prop :=
  ∃ w ∈ P.faces, ∃ d ∈ w, d.edge = a

namespace P1

def freshEdge (n : ℕ) : Fin (n + 1) := Fin.last n

def firstSubedge {n : ℕ} (a : Fin n) : Fin (n + 1) := a.castSucc

/-- Faithful selected P1 substitution, including the reversed negative order. -/
def expandDart {n : ℕ} (a : Fin n) :
    SignedDart (Fin n) → List (SignedDart (Fin (n + 1)))
  | .pos e => if e = a then
      [.pos (firstSubedge a), .pos (freshEdge n)] else [.pos e.castSucc]
  | .neg e => if e = a then
      [.neg (freshEdge n), .neg (firstSubedge a)] else [.neg e.castSucc]

def expandWord {n : ℕ} (a : Fin n) (w : List (SignedDart (Fin n))) :=
  w.flatMap (expandDart a)

def expand (P : FiniteCyclicPresentation) (a : Fin P.edgeCount) :
    FiniteCyclicPresentation where
  edgeCount := P.edgeCount + 1
  faces := P.faces.map (expandWord a)

private theorem expandWord_nil {n : ℕ} (a : Fin n) : expandWord a [] = [] := rfl

private theorem expandWord_cons {n : ℕ} (a : Fin n) (d : SignedDart (Fin n))
    (ds : List (SignedDart (Fin n))) :
    expandWord a (d :: ds) = expandDart a d ++ expandWord a ds := rfl

end P1

open P1

/-- The two endpoints that become the one new midpoint class. -/
def midpoint₀ {n : ℕ} (a : Fin n) : Endpoint (n + 1) := (a.castSucc, true)

def midpoint₁ {n : ℕ} (a : Fin n) : Endpoint (n + 1) := (Fin.last n, false)

/-- Old endpoints: only a's terminal endpoint moves to the fresh terminal tip. -/
def oldEndpoint {n : ℕ} (a : Fin n) : Endpoint n → Endpoint (n + 1)
  | (e, false) => (e.castSucc, false)
  | (e, true) => if e = a then (Fin.last n, true) else (e.castSucc, true)

/-- Explicit classification BEFORE quotienting; it does not define the new relation. -/
def collapse {n : ℕ} (a : Fin n) : Endpoint (n + 1) → Endpoint n ⊕ Unit
  | (e, b) => Fin.lastCases
      (match b with | false => .inr () | true => .inl (a, true))
      (fun c => match b with
        | false => .inl (c, false)
        | true => if c = a then .inr () else .inl (c, true)) e

private theorem collapse_old {n : ℕ} (a : Fin n) (x : Endpoint n) :
    collapse a (oldEndpoint a x) = Sum.inl x := by
  rcases x with ⟨e, b⟩
  cases b with
  | false => simp [oldEndpoint, collapse]
  | true =>
    by_cases h : e = a
    · subst e; simp [oldEndpoint, collapse]
    · simp [oldEndpoint, collapse, h]

private theorem collapse_midpoint₀ {n : ℕ} (a : Fin n) :
    collapse a (midpoint₀ a) = Sum.inr () := by
  simp [collapse, midpoint₀]

private theorem collapse_midpoint₁ {n : ℕ} (a : Fin n) :
    collapse a (midpoint₁ a) = Sum.inr () := by
  simp [collapse, midpoint₁]

/-- Recursive conjunction of the literal seam constraints; used only to prove facts
about cyclePairs, which remains the definition of Step. -/
def Walk {n : ℕ} (R : Endpoint n → Endpoint n → Prop) (p : Endpoint n) :
    List (SignedDart (Fin n)) → Endpoint n → Prop
  | [], q => R p q
  | d :: ds, q => R p (initial d) ∧ Walk R (terminal d) ds q

def Cycle {n : ℕ} (R : Endpoint n → Endpoint n → Prop) :
    List (SignedDart (Fin n)) → Prop
  | [] => True
  | d :: ds => Walk R (terminal d) ds (initial d)

private theorem walk_iff {n : ℕ} (R : Endpoint n → Endpoint n → Prop)
    (p : Endpoint n) (w : List (SignedDart (Fin n))) (q : Endpoint n) :
    Walk R p w q ↔ ∀ t ∈ seams p w q, R t.1 t.2 := by
  induction w generalizing p with
  | nil => simp [Walk, seams, List.forall_mem_singleton]
  | cons d ds ih => simp [Walk, seams, List.forall_mem_cons, ih]

private theorem cycle_iff {n : ℕ} (R : Endpoint n → Endpoint n → Prop)
    (w : List (SignedDart (Fin n))) :
    Cycle R w ↔ ∀ t ∈ cyclePairs w, R t.1 t.2 := by
  cases w with
  | nil => simp [Cycle, cyclePairs]
  | cons d ds => exact walk_iff R (terminal d) ds (initial d)

private theorem cycle_mono {n : ℕ} {R S : Endpoint n → Endpoint n → Prop}
    (h : ∀ x y, R x y → S x y) (w : List (SignedDart (Fin n)))
    (hw : Cycle R w) : Cycle S w := by
  apply (cycle_iff S w).mpr
  intro t ht
  exact h t.1 t.2 ((cycle_iff R w).mp hw t ht)

theorem allCycles_iff (P : FiniteCyclicPresentation)
    (R : Endpoint P.edgeCount → Endpoint P.edgeCount → Prop) :
    (∀ w ∈ P.faces, Cycle R w) ↔ ∀ x y, Step P x y → R x y := by
  constructor
  · rintro h x y ⟨w, hw, hxy⟩
    exact (cycle_iff R w).mp (h w hw) (x, y) hxy
  · intro h w hw
    apply (cycle_iff R w).mpr
    intro t ht
    exact h t.1 t.2 ⟨w, hw, ht⟩

theorem generated_cycles (P : FiniteCyclicPresentation) :
    ∀ w ∈ P.faces, Cycle (Related P) w :=
  (allCycles_iff P (Related P)).mpr (fun x y h => Relation.EqvGen.rel x y h)

/-- Internal seams in the actual expanded block, with the two orientations kept. -/
private def Interior {n : ℕ} (R : Endpoint (n + 1) → Endpoint (n + 1) → Prop)
    (a : Fin n) : SignedDart (Fin n) → Prop
  | .pos e => e = a → R (midpoint₀ a) (midpoint₁ a)
  | .neg e => e = a → R (midpoint₁ a) (midpoint₀ a)

/-- This is a derived equivalence of actual seam conjunctions, for arbitrary R.
It assumes neither a quotient classification nor symmetry/transitivity of R. -/
private theorem walk_expand {n : ℕ}
    (R : Endpoint (n + 1) → Endpoint (n + 1) → Prop) (a : Fin n)
    (p : Endpoint n) (w : List (SignedDart (Fin n))) (q : Endpoint n) :
    Walk R (oldEndpoint a p) (expandWord a w) (oldEndpoint a q) ↔
      Walk (fun x y => R (oldEndpoint a x) (oldEndpoint a y)) p w q ∧
        ∀ d ∈ w, Interior R a d := by
  induction w generalizing p q with
  | nil => simp [P1.expandWord_nil, Walk]
  | cons d ds ih =>
    cases d with
    | pos e =>
      have hi := ih (terminal (.pos e)) q
      by_cases h : e = a
      · subst e
        simp [terminal, oldEndpoint] at hi
        simpa [P1.expandWord_cons, expandDart, firstSubedge, freshEdge,
          Walk, initial, terminal, oldEndpoint, midpoint₀, midpoint₁, Interior,
          hi, and_assoc, and_left_comm, and_comm]
      · simp [terminal, oldEndpoint, h] at hi
        simpa [P1.expandWord_cons, expandDart, h, Walk, initial, terminal,
          oldEndpoint, Interior, hi, and_assoc, and_left_comm, and_comm]
    | neg e =>
      have hi := ih (terminal (.neg e)) q
      by_cases h : e = a
      · subst e
        simp [terminal, oldEndpoint] at hi
        simpa [P1.expandWord_cons, expandDart, firstSubedge, freshEdge,
          Walk, initial, terminal, oldEndpoint, midpoint₀, midpoint₁, Interior,
          hi, and_assoc, and_left_comm, and_comm]
      · simp [terminal, oldEndpoint, h] at hi
        simpa [P1.expandWord_cons, expandDart, h, Walk, initial, terminal,
          oldEndpoint, Interior, hi, and_assoc, and_left_comm, and_comm]

/-- Includes the closing seam, empty face, monogon and all repeated occurrences. -/
private theorem cycle_expand {n : ℕ}
    (R : Endpoint (n + 1) → Endpoint (n + 1) → Prop) (a : Fin n)
    (w : List (SignedDart (Fin n))) :
    Cycle R (expandWord a w) ↔
      Cycle (fun x y => R (oldEndpoint a x) (oldEndpoint a y)) w ∧
        ∀ d ∈ w, Interior R a d := by
  cases w with
  | nil => simp [P1.expandWord_nil, Cycle]
  | cons d ds =>
    cases d with
    | pos e =>
      have hi := walk_expand R a (terminal (.pos e)) ds (initial (.pos e))
      by_cases h : e = a
      · subst e
        simp [initial, terminal, oldEndpoint] at hi
        simpa [P1.expandWord_cons, expandDart, firstSubedge, freshEdge,
          Cycle, Walk, initial, terminal, oldEndpoint, midpoint₀, midpoint₁,
          Interior, hi, and_assoc, and_left_comm, and_comm]
      · simp [initial, terminal, oldEndpoint, h] at hi
        simpa [P1.expandWord_cons, expandDart, h, Cycle, Walk, initial, terminal,
          oldEndpoint, Interior, hi, and_assoc, and_left_comm, and_comm]
    | neg e =>
      have hi := walk_expand R a (terminal (.neg e)) ds (initial (.neg e))
      by_cases h : e = a
      · subst e
        simp [initial, terminal, oldEndpoint] at hi
        simpa [P1.expandWord_cons, expandDart, firstSubedge, freshEdge,
          Cycle, Walk, initial, terminal, oldEndpoint, midpoint₀, midpoint₁,
          Interior, hi, and_assoc, and_left_comm, and_comm]
      · simp [initial, terminal, oldEndpoint, h] at hi
        simpa [P1.expandWord_cons, expandDart, h, Cycle, Walk, initial, terminal,
          oldEndpoint, Interior, hi, and_assoc, and_left_comm, and_comm]

/-- Old face seams lift to actual new face seams; then lift the entire EqvGen. -/
private theorem oldEndpoint_related (P : FiniteCyclicPresentation)
    (a : Fin P.edgeCount) {x y : Endpoint P.edgeCount} (h : Related P x y) :
    Related (expand P a) (oldEndpoint a x) (oldEndpoint a y) := by
  have faceOK : ∀ w ∈ P.faces,
      Cycle (fun x y => Related (expand P a) (oldEndpoint a x) (oldEndpoint a y)) w := by
    intro w hw
    have he := generated_cycles (expand P a) (expandWord a w)
      (List.mem_map.mpr ⟨w, hw, rfl⟩)
    exact ((cycle_expand (Related (expand P a)) a w).mp he).1
  have stepOK := (allCycles_iff P _).mp faceOK
  induction h with
  | rel x y h => exact stepOK x y h
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂

/-- One actual occurrence supplies the internal seam; no surface-validity hypothesis. -/
private theorem midpoints_related (P : FiniteCyclicPresentation)
    (a : Fin P.edgeCount) (ha : Occurs P a) :
    Related (expand P a) (midpoint₀ a) (midpoint₁ a) := by
  obtain ⟨w, hw, d, hd, he⟩ := ha
  have hc := generated_cycles (expand P a) (expandWord a w)
    (List.mem_map.mpr ⟨w, hw, rfl⟩)
  have hi := ((cycle_expand (Related (expand P a)) a w).mp hc).2 d hd
  cases d with
  | pos e => exact hi he
  | neg e => exact (hi he).symm

/-- Collapse to either an actual old class or the midpoint tag. -/
def classify (P : FiniteCyclicPresentation) (a : Fin P.edgeCount)
    (x : Endpoint (P.edgeCount + 1)) : Vertices P ⊕ Unit :=
  match collapse a x with
  | .inl y => .inl (Quotient.mk _ y)
  | .inr _ => .inr ()

private theorem classify_old (P : FiniteCyclicPresentation) (a : Fin P.edgeCount)
    (x : Endpoint P.edgeCount) :
    classify P a (oldEndpoint a x) = Sum.inl (Quotient.mk _ x) := by
  simp [classify, collapse_old]

private theorem classify_midpoint₀ (P : FiniteCyclicPresentation) (a : Fin P.edgeCount) :
    classify P a (midpoint₀ a) = Sum.inr () := by
  simp [classify, collapse_midpoint₀]

private theorem classify_midpoint₁ (P : FiniteCyclicPresentation) (a : Fin P.edgeCount) :
    classify P a (midpoint₁ a) = Sum.inr () := by
  simp [classify, collapse_midpoint₁]

/-- Every external seam preserves the old class; every internal seam has midpoint tag. -/
private theorem classify_related (P : FiniteCyclicPresentation) (a : Fin P.edgeCount)
    {x y : Endpoint (P.edgeCount + 1)} (h : Related (expand P a) x y) :
    classify P a x = classify P a y := by
  have faceOK : ∀ w ∈ (expand P a).faces,
      Cycle (fun x y => classify P a x = classify P a y) w := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    apply (cycle_expand (fun x y => classify P a x = classify P a y) a v).mpr
    constructor
    · apply cycle_mono (R := Related P) _ v (generated_cycles P v hv)
      intro x y hxy
      rw [classify_old, classify_old]
      exact congrArg Sum.inl (Quotient.sound hxy)
    · intro d hd
      cases d with
      | pos e =>
        intro he
        exact (classify_midpoint₀ P a).trans (classify_midpoint₁ P a).symm
      | neg e =>
        intro he
        exact (classify_midpoint₁ P a).trans (classify_midpoint₀ P a).symm
  have stepOK := (allCycles_iff (expand P a) _).mp faceOK
  induction h with
  | rel x y h => exact stepOK x y h
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def classMap (P : FiniteCyclicPresentation) (a : Fin P.edgeCount) :
    Vertices (expand P a) → Vertices P ⊕ Unit :=
  Quotient.lift (classify P a) (fun _ _ h => classify_related P a h)

def oldClassMap (P : FiniteCyclicPresentation) (a : Fin P.edgeCount) :
    Vertices P → Vertices (expand P a) :=
  Quotient.map (oldEndpoint a) (fun _ _ h => oldEndpoint_related P a h)

def inverseClassMap (P : FiniteCyclicPresentation) (a : Fin P.edgeCount) :
    Vertices P ⊕ Unit → Vertices (expand P a)
  | .inl v => oldClassMap P a v
  | .inr _ => Quotient.mk _ (midpoint₀ a)

private def representative {n : ℕ} (a : Fin n) : Endpoint n ⊕ Unit → Endpoint (n + 1)
  | .inl x => oldEndpoint a x
  | .inr _ => midpoint₀ a

/-- Exhaustive endpoint classification, including both fresh endpoints. -/
private theorem endpoint_normalization (P : FiniteCyclicPresentation)
    (a : Fin P.edgeCount) (ha : Occurs P a) (x : Endpoint (P.edgeCount + 1)) :
    Related (expand P a) x (representative a (collapse a x)) := by
  rcases x with ⟨e, b⟩
  refine Fin.lastCases ?_ (fun c => ?_) e
  · cases b with
    | false =>
      simpa [collapse, representative, midpoint₀, midpoint₁] using
        (midpoints_related P a ha).symm
    | true =>
      simpa [Related, expand, collapse, representative, oldEndpoint] using
        (Relation.EqvGen.refl (Fin.last P.edgeCount, true) :
          Related (expand P a) (Fin.last P.edgeCount, true) (Fin.last P.edgeCount, true))
  · cases b with
    | false =>
      simpa [Related, expand, collapse, representative, oldEndpoint] using
        (Relation.EqvGen.refl (c.castSucc, false) :
          Related (expand P a) (c.castSucc, false) (c.castSucc, false))
    | true =>
      by_cases h : c = a
      · subst c
        simpa [Related, expand, collapse, representative, midpoint₀] using
          (Relation.EqvGen.refl (a.castSucc, true) :
            Related (expand P a) (a.castSucc, true) (a.castSucc, true))
      · simpa [Related, expand, collapse, representative, oldEndpoint, h] using
          (Relation.EqvGen.refl (c.castSucc, true) :
            Related (expand P a) (c.castSucc, true) (c.castSucc, true))

private theorem inverse_classify (P : FiniteCyclicPresentation) (a : Fin P.edgeCount)
    (x : Endpoint (P.edgeCount + 1)) :
    inverseClassMap P a (classify P a x) =
      Quotient.mk _ (representative a (collapse a x)) := by
  unfold classify
  cases collapse a x <;> rfl

/-- Explicit equivalence of the quotient of actual expanded cyclic seams.
Occurrence is used only to identify the two midpoint endpoints in the left inverse. -/
def classesEquiv (P : FiniteCyclicPresentation) (a : Fin P.edgeCount) (ha : Occurs P a) :
    Vertices (expand P a) ≃ Vertices P ⊕ Unit where
  toFun := classMap P a
  invFun := inverseClassMap P a
  left_inv := by
    intro v
    refine Quotient.inductionOn v (fun (x : Endpoint (P.edgeCount + 1)) => ?_)
    change inverseClassMap P a (classify P a x) = Quotient.mk _ x
    rw [inverse_classify P a x]
    exact Quotient.sound (s := vertexSetoid (expand P a))
      (endpoint_normalization P a ha x).symm
  right_inv := by
    intro v
    cases v with
    | inl v =>
      refine Quotient.inductionOn v ?_
      intro x
      change classify P a (oldEndpoint a x) = Sum.inl (Quotient.mk _ x)
      exact classify_old P a x
    | inr u =>
      cases u
      change classify P a (midpoint₀ a) = Sum.inr ()
      exact classify_midpoint₀ P a

/-- Combinatorial Euler count; this is not a definition of topological genus. -/
def euler (P : FiniteCyclicPresentation) : ℤ :=
  (Nat.card (Vertices P) : ℤ) - (P.edgeCount : ℤ) + (P.faces.length : ℤ)

/-- The one public theorem bundles the actual relation classification, commuting
old-class map, BOTH midpoint endpoints and its cardinal/Euler consumers.
No validity, connectedness, closedness, orientability or twice-occurrence premise. -/
theorem p1_generated_vertex_classes (P : FiniteCyclicPresentation)
    (a : Fin P.edgeCount) (ha : Occurs P a) :
    (∀ xy : Endpoint (P.edgeCount + 1) × Endpoint (P.edgeCount + 1),
      Related (expand P a) xy.1 xy.2 ↔ classify P a xy.1 = classify P a xy.2) ∧
    (∀ v : Vertices P, classesEquiv P a ha (oldClassMap P a v) = Sum.inl v) ∧
    classesEquiv P a ha (Quotient.mk _ (midpoint₀ a)) = Sum.inr () ∧
    classesEquiv P a ha (Quotient.mk _ (midpoint₁ a)) = Sum.inr () ∧
    Nat.card (Vertices (expand P a)) = Nat.card (Vertices P) + 1 ∧
    (expand P a).edgeCount = P.edgeCount + 1 ∧
    (expand P a).faces.length = P.faces.length ∧
    euler (expand P a) = euler P := by
  have hc : Nat.card (Vertices (expand P a)) = Nat.card (Vertices P) + 1 := by
    calc
      Nat.card (Vertices (expand P a)) = Nat.card (Vertices P ⊕ Unit) :=
        Nat.card_congr (classesEquiv P a ha)
      _ = Nat.card (Vertices P) + 1 := by simp
  refine ⟨?_, ?_, ?_, ?_, hc, rfl, ?_, ?_⟩
  · intro xy
    constructor
    · exact classify_related P a
    · intro h
      have he :
          (Quotient.mk (vertexSetoid (expand P a)) xy.1 : Vertices (expand P a)) =
            Quotient.mk (vertexSetoid (expand P a)) xy.2 := by
        apply (classesEquiv P a ha).injective
        exact h
      exact Quotient.exact (s := vertexSetoid (expand P a)) he
  · intro v
    refine Quotient.inductionOn v ?_
    intro x
    exact classify_old P a x
  · exact classify_midpoint₀ P a
  · exact classify_midpoint₁ P a
  · simp [expand]
  · unfold euler
    rw [hc]
    simp only [expand, List.length_map, Nat.cast_add, Nat.cast_one]
    omega

end D5.S3.Geometry.Gluing.CyclicP1GeneratedVertices
