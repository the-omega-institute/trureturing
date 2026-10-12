/- GID: D5/S3/ConceptDynamics/Coding/ResetAlternatingSquares
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResetAlternatingSquares
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Typed reset square algebra and uniform strip forgetting for every positive even carrier. -/

import D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
import D5.S3.ConceptDynamics.Coding.SameCutWholeRayBridge
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.ResetNumberedHistories

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization (History)
open D5.S3.ConceptDynamics.Coding.FixedBlockRigidity (expandedGraph groupHistory)
open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap (GroupMat Edge)
open Multiplicative

/- Typed alternating squares retain the original numbered reset edges. -/

namespace Alternating

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion

abbrev Vertex (q : ℕ) := Fin q × Sign

def zero {q : ℕ} (hq : 0 < q) : Fin q := ⟨0, hq⟩

def next {q : ℕ} (i : Fin q) (hi : i.val + 1 < q) : Fin q :=
  ⟨i.val + 1, hi⟩

def flipSign (h : Sign) : Sign := h * ofAdd true

/- These are the actual two kinds of numbered reset edge.  The equivalence
   below retains the original label, number zero and absolute source sign. -/
inductive B (q : ℕ) where
  | f (i : Fin q) (h : Sign)
  | a (i : Fin q) (h : Sign) (hi : i.val + 1 < q)
  deriving DecidableEq

/- The direct typed I+B boundary: D, F and legal A are distinct edges. -/
inductive R (q : ℕ) where
  | d (i : Fin q) (h : Sign)
  | f (i : Fin q) (h : Sign)
  | a (i : Fin q) (h : Sign) (hi : i.val + 1 < q)
  deriving DecidableEq

def sourceB {q : ℕ} : B q → Vertex q
  | .f i h => (i, h)
  | .a i h _ => (i, h)

def targetB {q : ℕ} (hq : 0 < q) : B q → Vertex q
  | .f _ h => (zero hq, flipSign h)
  | .a i h hi => (next i hi, h)

def sourceR {q : ℕ} : R q → Vertex q
  | .d i h => (i, h)
  | .f i h => (i, h)
  | .a i h _ => (i, h)

def targetR {q : ℕ} (hq : 0 < q) : R q → Vertex q
  | .d i h => (i, h)
  | .f _ h => (zero hq, flipSign h)
  | .a i h hi => (next i hi, h)

def identityR {q : ℕ} (v : Vertex q) : R q := .d v.1 v.2

private theorem matrix_coefficient (q : ℕ) (i j : Fin q) (g : Sign) :
    ((resetMatrix q) i j).coeff g =
      if (j.val = 0 ∧ g = ofAdd true) ∨ (j.val = i.val + 1 ∧ g = 1)
        then 1 else 0 := by
  have hdis : j.val = 0 → j.val ≠ i.val + 1 := by omega
  by_cases h₀ : j.val = 0 <;> by_cases h₁ : j.val = i.val + 1 <;>
    by_cases hg₀ : g = ofAdd true <;> by_cases hg₁ : g = 1 <;>
    simp_all [resetMatrix, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, eq_comm]

private theorem edge_support (q : ℕ) (e : Edge (resetMatrix q)) :
    (e.target.val = 0 ∧ e.label = ofAdd true) ∨
      (e.target.val = e.source.val + 1 ∧ e.label = 1) := by
  have hn : 0 < ((resetMatrix q) e.source e.target).coeff e.label :=
    lt_of_le_of_lt (Nat.zero_le e.number.val) e.number.isLt
  rw [matrix_coefficient] at hn
  split_ifs at hn with h
  · exact h
  · omega

theorem numbered_ext {q : ℕ} {M : GroupMat Sign q q}
    (e f : Edge M) (hs : e.source = f.source) (ht : e.target = f.target)
    (hl : e.label = f.label) (hn : e.number.val = f.number.val) : e = f := by
  rcases e with ⟨i, j, g, n⟩
  rcases f with ⟨i', j', g', n'⟩
  dsimp only at hs ht hl hn
  subst i'
  subst j'
  subst g'
  have h : n = n' := Fin.ext hn
  cases h
  rfl

def originalEdge {q : ℕ} (hq : 0 < q) : B q → Edge (resetMatrix q) × Sign
  | .f i h =>
      (⟨i, zero hq, ofAdd true,
        ⟨0, by rw [matrix_coefficient]; simp [zero]⟩⟩, h)
  | .a i h hi =>
      (⟨i, next i hi, 1,
        ⟨0, by rw [matrix_coefficient]; simp [next]⟩⟩, h)

def typedEdge {q : ℕ} (p : Edge (resetMatrix q) × Sign) : B q :=
  if h : p.1.target.val = 0 then .f p.1.source p.2
  else .a p.1.source p.2 (by
    obtain hs | hs := edge_support q p.1
    · exact False.elim (h hs.1)
    · have ht := p.1.target.isLt
      omega)

theorem typed_original {q : ℕ} (hq : 0 < q) (b : B q) :
    typedEdge (originalEdge hq b) = b := by
  cases b <;> simp [typedEdge, originalEdge, zero, next]

theorem original_typed {q : ℕ} (hq : 0 < q)
    (p : Edge (resetMatrix q) × Sign) : originalEdge hq (typedEdge p) = p := by
  apply Prod.ext
  · by_cases ht : p.1.target.val = 0
    · have hs := edge_support q p.1
      have hl : p.1.label = ofAdd true := by rcases hs with hs | hs <;> simp_all
      have hc : ((resetMatrix q) p.1.source p.1.target).coeff p.1.label = 1 := by
        rw [matrix_coefficient]
        simp [ht, hl]
      have hn : p.1.number.val = 0 := by have := p.1.number.isLt; omega
      simp only [typedEdge, dif_pos ht, originalEdge]
      apply numbered_ext
      · rfl
      · apply Fin.ext
        exact ht.symm
      · exact hl.symm
      · exact hn.symm
    · have hs := edge_support q p.1
      have ha : p.1.target.val = p.1.source.val + 1 ∧ p.1.label = 1 := by
        rcases hs with hs | hs
        · exact False.elim (ht hs.1)
        · exact hs
      have hc : ((resetMatrix q) p.1.source p.1.target).coeff p.1.label = 1 := by
        rw [matrix_coefficient]
        simp [ha.1, ha.2]
      have hn : p.1.number.val = 0 := by have := p.1.number.isLt; omega
      simp only [typedEdge, dif_neg ht, originalEdge]
      apply numbered_ext
      · rfl
      · apply Fin.ext
        exact ha.1.symm
      · exact ha.2.symm
      · exact hn.symm
  · by_cases ht : p.1.target.val = 0
    · simp only [typedEdge, dif_pos ht, originalEdge]
    · simp only [typedEdge, dif_neg ht, originalEdge]

def actualEdgeEquiv {q : ℕ} (hq : 0 < q) :
    B q ≃ Edge (resetMatrix q) × Sign where
  toFun := originalEdge hq
  invFun := typedEdge
  left_inv := typed_original hq
  right_inv := original_typed hq

theorem actual_source {q : ℕ} (hq : 0 < q) (b : B q) :
    (expandedGraph (resetMatrix q)).source (originalEdge hq b) = sourceB b := by
  cases b <;> rfl

theorem actual_target {q : ℕ} (hq : 0 < q) (b : B q) :
    (expandedGraph (resetMatrix q)).target (originalEdge hq b) = targetB hq b := by
  cases b <;> simp [expandedGraph, originalEdge, targetB, flipSign]

/- Faithful boundary decoding into identity edges plus original B edges.
   No adjacency count or quotient is used for R. -/
def originalBoundary {q : ℕ} (hq : 0 < q) :
    R q → Sum (Vertex q) (Edge (resetMatrix q) × Sign)
  | .d i h => .inl (i, h)
  | .f i h => .inr (actualEdgeEquiv hq (.f i h))
  | .a i h hi => .inr (actualEdgeEquiv hq (.a i h hi))

private def typedBoundary {q : ℕ} :
    Sum (Vertex q) (Edge (resetMatrix q) × Sign) → R q
  | .inl v => .d v.1 v.2
  | .inr p => match typedEdge p with
      | .f i h => .f i h
      | .a i h hi => .a i h hi

def actualBoundaryEquiv {q : ℕ} (hq : 0 < q) :
    R q ≃ Sum (Vertex q) (Edge (resetMatrix q) × Sign) where
  toFun := originalBoundary hq
  invFun := typedBoundary
  left_inv := by
    intro r
    cases r <;> simp [originalBoundary, typedBoundary, actualEdgeEquiv, typed_original]
  right_inv := by
    intro r
    cases r with
    | inl v => rfl
    | inr p =>
        have hp := original_typed hq p
        cases hb : typedEdge p <;> simpa [originalBoundary, typedBoundary, actualEdgeEquiv, hb] using
          congrArg (Sum.inr (α := Vertex q)) hp

/- Exactly the endpoint square specified by the research artifact.  The only
   nontrivial fiber is FD/AF.  Its swap is guarded by both parity and existence
   of A_i.  At the terminal suffix, fdFix is forced even for odd q. -/
inductive Square {q : ℕ} (hq : 0 < q) : R q → B q → B q → R q → Prop
  | fdSwap (i : Fin q) (h : Sign) (hi : i.val + 1 < q) (he : i.val % 2 = 0) :
      Square hq (.a i h hi) (.f i h) (.f (next i hi) h) (.d (zero hq) (flipSign h))
  | fdFix (i : Fin q) (h : Sign) (hn : ¬ (i.val + 1 < q ∧ i.val % 2 = 0)) :
      Square hq (.d i h) (.f i h) (.f i h) (.d (zero hq) (flipSign h))
  | afSwap (i : Fin q) (h : Sign) (hi : i.val + 1 < q) (he : i.val % 2 = 0) :
      Square hq (.d i h) (.a i h hi) (.f i h) (.f (next i hi) h)
  | afFix (i : Fin q) (h : Sign) (hi : i.val + 1 < q) (ho : i.val % 2 ≠ 0) :
      Square hq (.a i h hi) (.a i h hi) (.f (next i hi) h) (.f (next i hi) h)
  | ff (i : Fin q) (h : Sign) :
      Square hq (.f i h) (.f i h) (.f (zero hq) (flipSign h))
        (.f (zero hq) (flipSign h))
  | fa (i : Fin q) (h : Sign) (h1 : 1 < q) :
      Square hq (.f i h) (.f i h) (.a (zero hq) (flipSign h) h1)
        (.a (zero hq) (flipSign h) h1)
  | ad (i : Fin q) (h : Sign) (hi : i.val + 1 < q) :
      Square hq (.d i h) (.a i h hi) (.a i h hi) (.d (next i hi) h)
  | aa (i : Fin q) (h : Sign) (hi : i.val + 1 < q) (hii : i.val + 2 < q) :
      Square hq (.a i h hi) (.a i h hi) (.a (next i hi) h hii)
        (.a (next i hi) h hii)

theorem square_endpoints {q : ℕ} {hq : 0 < q}
    {r s : R q} {x y : B q} (hs : Square hq r x y s) :
    sourceR r = sourceB x ∧ targetR hq r = sourceB y ∧
      targetB hq x = sourceR s ∧ targetR hq s = targetB hq y := by
  cases hs <;> exact ⟨rfl, rfl, rfl, rfl⟩

private theorem left_square_exists {q : ℕ} (hq : 0 < q)
    (x : B q) (s : R q) (hc : targetB hq x = sourceR s) :
    ∃ r y, Square hq r x y s := by
  cases x with
  | f i h =>
      cases s with
      | d j g =>
          simp only [targetB, sourceR, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          by_cases hs : i.val + 1 < q ∧ i.val % 2 = 0
          · exact ⟨_, _, .fdSwap i h hs.1 hs.2⟩
          · exact ⟨_, _, .fdFix i h hs⟩
      | f j g =>
          simp only [targetB, sourceR, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact ⟨_, _, .ff i h⟩
      | a j g hj =>
          simp only [targetB, sourceR, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact ⟨_, _, .fa i h hj⟩
  | a i h hi =>
      cases s with
      | d j g =>
          simp only [targetB, sourceR, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact ⟨_, _, .ad i h hi⟩
      | f j g =>
          simp only [targetB, sourceR, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          by_cases he : i.val % 2 = 0
          · exact ⟨_, _, .afSwap i h hi he⟩
          · exact ⟨_, _, .afFix i h hi he⟩
      | a j g hj =>
          simp only [targetB, sourceR, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact ⟨_, _, .aa i h hi hj⟩

private theorem right_square_exists {q : ℕ} (hq : 0 < q)
    (r : R q) (y : B q) (hc : targetR hq r = sourceB y) :
    ∃ x s, Square hq r x y s := by
  cases r with
  | d i h =>
      cases y with
      | f j g =>
          simp only [targetR, sourceB, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          by_cases he : i.val + 1 < q ∧ i.val % 2 = 0
          · exact ⟨_, _, .afSwap i h he.1 he.2⟩
          · exact ⟨_, _, .fdFix i h he⟩
      | a j g hj =>
          simp only [targetR, sourceB, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact ⟨_, _, .ad i h hj⟩
  | f i h =>
      cases y with
      | f j g =>
          simp only [targetR, sourceB, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact ⟨_, _, .ff i h⟩
      | a j g hj =>
          simp only [targetR, sourceB, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact ⟨_, _, .fa i h hj⟩
  | a i h hi =>
      cases y with
      | f j g =>
          simp only [targetR, sourceB, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          by_cases he : i.val % 2 = 0
          · exact ⟨_, _, .fdSwap i h hi he⟩
          · exact ⟨_, _, .afFix i h hi he⟩
      | a j g hj =>
          simp only [targetR, sourceB, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact ⟨_, _, .aa i h hi hj⟩

theorem square_left_unique {q : ℕ} {hq : 0 < q}
    {r r' s s' : R q} {x x' y y' : B q}
    (hs : Square hq r x y s) (hs' : Square hq r' x' y' s')
    (hx : x = x') (ht : s = s') :
    r = r' ∧ y = y' := by
  cases hs <;> cases hs' <;> simp_all [next, zero, Fin.ext_iff] <;> omega

theorem square_right_unique {q : ℕ} {hq : 0 < q}
    {r r' s s' : R q} {x x' y y' : B q}
    (hs : Square hq r x y s) (hs' : Square hq r' x' y' s')
    (hr : r = r') (hy : y = y') :
    x = x' ∧ s = s' := by
  cases hs <;> cases hs' <;> simp_all [next, zero, Fin.ext_iff] <;> omega

private def leftSquareChoice {q : ℕ} (hq : 0 < q) (x : B q) (s : R q) : R q × B q :=
  if hc : targetB hq x = sourceR s then
    let r := Classical.choose (left_square_exists hq x s hc)
    (r, Classical.choose (Classical.choose_spec (left_square_exists hq x s hc)))
  else (identityR (sourceB x), x)

private theorem leftSquareChoice_spec {q : ℕ} (hq : 0 < q) (x : B q) (s : R q)
    (hc : targetB hq x = sourceR s) :
    Square hq (leftSquareChoice hq x s).1 x (leftSquareChoice hq x s).2 s := by
  simp only [leftSquareChoice, dif_pos hc]
  exact Classical.choose_spec (Classical.choose_spec (left_square_exists hq x s hc))

private def rightSquareChoice {q : ℕ} (hq : 0 < q) (r : R q) (y : B q) : B q × R q :=
  if hc : targetR hq r = sourceB y then
    let x := Classical.choose (right_square_exists hq r y hc)
    (x, Classical.choose (Classical.choose_spec (right_square_exists hq r y hc)))
  else (y, identityR (targetB hq y))

private theorem rightSquareChoice_spec {q : ℕ} (hq : 0 < q) (r : R q) (y : B q)
    (hc : targetR hq r = sourceB y) :
    Square hq r (rightSquareChoice hq r y).1 y (rightSquareChoice hq r y).2 := by
  simp only [rightSquareChoice, dif_pos hc]
  exact Classical.choose_spec (Classical.choose_spec (right_square_exists hq r y hc))

private def BRFiber {q : ℕ} (hq : 0 < q) (v z : Vertex q) :=
  {p : B q × R q // sourceB p.1 = v ∧ targetB hq p.1 = sourceR p.2 ∧ targetR hq p.2 = z}

private def RBFiber {q : ℕ} (hq : 0 < q) (v z : Vertex q) :=
  {p : R q × B q // sourceR p.1 = v ∧ targetR hq p.1 = sourceB p.2 ∧ targetB hq p.2 = z}

/- The genuine endpoint-preserving phi, not an adjacency equality.  Its
   forward and inverse functions are consumed by both sweep algorithms. -/
private def endpointSquare {q : ℕ} (hq : 0 < q) (v z : Vertex q) :
    BRFiber hq v z ≃ RBFiber hq v z where
  toFun p :=
    ⟨leftSquareChoice hq p.val.1 p.val.2, by
      have hs := leftSquareChoice_spec hq p.val.1 p.val.2 p.property.2.1
      have he := square_endpoints hs
      exact ⟨he.1.trans p.property.1, he.2.1, he.2.2.2.symm.trans p.property.2.2⟩⟩
  invFun p :=
    ⟨rightSquareChoice hq p.val.1 p.val.2, by
      have hs := rightSquareChoice_spec hq p.val.1 p.val.2 p.property.2.1
      have he := square_endpoints hs
      exact ⟨he.1.symm.trans p.property.1, he.2.2.1, he.2.2.2.trans p.property.2.2⟩⟩
  left_inv p := by
    apply Subtype.ext
    have hs := leftSquareChoice_spec hq p.val.1 p.val.2 p.property.2.1
    have ht := rightSquareChoice_spec hq (leftSquareChoice hq p.val.1 p.val.2).1
      (leftSquareChoice hq p.val.1 p.val.2).2 (square_endpoints hs).2.1
    have hu := square_right_unique hs ht rfl rfl
    exact (Prod.ext hu.1 hu.2).symm
  right_inv p := by
    apply Subtype.ext
    have hs := rightSquareChoice_spec hq p.val.1 p.val.2 p.property.2.1
    have ht := leftSquareChoice_spec hq (rightSquareChoice hq p.val.1 p.val.2).1
      (rightSquareChoice hq p.val.1 p.val.2).2 (square_endpoints hs).2.2.1
    have hu := square_left_unique hs ht rfl rfl
    exact (Prod.ext hu.1 hu.2).symm

def leftSquare {q : ℕ} (hq : 0 < q) (x : B q) (s : R q) : R q × B q :=
  if hc : targetB hq x = sourceR s then
    ((endpointSquare hq (sourceB x) (targetR hq s)) ⟨(x, s), rfl, hc, rfl⟩).val
  else (identityR (sourceB x), x)

theorem leftSquare_spec {q : ℕ} (hq : 0 < q) (x : B q) (s : R q)
    (hc : targetB hq x = sourceR s) :
    Square hq (leftSquare hq x s).1 x (leftSquare hq x s).2 s := by
  simp only [leftSquare, dif_pos hc]
  exact leftSquareChoice_spec hq x s hc

def rightSquare {q : ℕ} (hq : 0 < q) (r : R q) (y : B q) : B q × R q :=
  if hc : targetR hq r = sourceB y then
    ((endpointSquare hq (sourceR r) (targetB hq y)).symm ⟨(r, y), rfl, hc, rfl⟩).val
  else (y, identityR (targetB hq y))

theorem rightSquare_spec {q : ℕ} (hq : 0 < q) (r : R q) (y : B q)
    (hc : targetR hq r = sourceB y) :
    Square hq r (rightSquare hq r y).1 y (rightSquare hq r y).2 := by
  simp only [rightSquare, dif_pos hc]
  exact rightSquareChoice_spec hq r y hc

/- Ordered ranks are symmetric on their comparison fibers: leftRank on
   pairs with a common source, rightRank on pairs with a common target.
   All outgoing edges are compared, including different targets; all incoming
   edges are compared, including F edges with different origins. -/
private def leftRank {q : ℕ} (r r' : R q) : ℕ :=
  if r = r' then 0 else
    match r, r' with
    | .d i _, .a _ _ _ | .a i _ _, .d _ _ => i.val + 2
    | .d i _, .f _ _ | .f i _, .d _ _ => if i.val % 2 = 0 then i.val + 2 else 1
    | .f i _, .a _ _ _ | .a i _ _, .f _ _ => if i.val % 2 = 0 then 1 else i.val + 2
    | _, _ => 0

private def rightRank {q : ℕ} (hq : 0 < q) (r r' : R q) : ℕ :=
  if r = r' then 0 else
    if (targetR hq r).1.val = 0 then
      match r, r' with
      | .f _ _, .f _ _ => 1
      | _, _ => q
    else q - (targetR hq r).1.val

private theorem even_mod {q : ℕ} (he : Even q) : q % 2 = 0 := by
  rcases he with ⟨a, ha⟩
  omega

private theorem leftRank_positive {q : ℕ} {r r' : R q}
    (hc : sourceR r = sourceR r') (hn : r ≠ r') : 0 < leftRank r r' := by
  cases r <;> cases r' <;>
    simp_all [sourceR, leftRank, Fin.ext_iff] <;> (try split_ifs) <;> omega

private theorem rightRank_positive {q : ℕ} (hq : 0 < q) {r r' : R q}
    (hn : r ≠ r') : 0 < rightRank hq r r' := by
  have hj : (targetR hq r).1.val < q := (targetR hq r).1.isLt
  simp only [rightRank, if_neg hn]
  split_ifs <;> cases r <;> cases r' <;> simp_all <;> omega

private theorem leftRank_le {q : ℕ} (he : Even q) {r r' : R q}
    (hc : sourceR r = sourceR r') : leftRank r r' ≤ q := by
  have heq := even_mod he
  cases r <;> cases r' <;>
    simp_all [sourceR, leftRank, Fin.ext_iff] <;> (try split_ifs) <;> omega

private theorem rightRank_le {q : ℕ} (hq : 0 < q) (r r' : R q) :
    rightRank hq r r' ≤ q := by
  unfold rightRank
  split_ifs <;> cases r <;> cases r' <;> simp_all <;> omega

/- The case split is on the fixed eight endpoint fibers, not on words or q.
   The guards are retained throughout, so q=2 is included without a terminal
   A edge.  Evenness excludes the terminal even FD obstruction. -/
private theorem leftRank_step {q : ℕ} {hq : 0 < q} (he : Even q)
    {r r' s s' : R q} {x x' y y' : B q}
    (hs : Square hq r x y s) (hs' : Square hq r' x' y' s')
    (hx : x = x') (hn : r ≠ r') :
    leftRank r r' < leftRank s s' := by
  have heq := even_mod he
  cases hs <;> cases hs' <;>
    simp_all [leftRank, next, zero, Fin.ext_iff] <;> (try split_ifs) <;> (try simp_all) <;> omega

private theorem rightRank_step {q : ℕ} {hq : 0 < q} (he : Even q)
    {r r' s s' : R q} {x x' y y' : B q}
    (hs : Square hq r x y s) (hs' : Square hq r' x' y' s')
    (hy : y = y') (hn : s ≠ s') :
    rightRank hq s s' < rightRank hq r r' := by
  have heq := even_mod he
  cases hs <;> cases hs' <;>
    simp_all [rightRank, targetR, next, zero, Fin.ext_iff] <;>
    (try split_ifs) <;> (try simp_all) <;> omega

/- A strip retains every original B edge, every right B edge and both original
   R boundaries.  Internal boundaries are existential in Prop, not erased
   from the square relation. -/
inductive Strip {q : ℕ} (hq : 0 < q) :
    List (B q) → R q → R q → List (B q) → Prop
  | nil (r : R q) : Strip hq [] r r []
  | cons {xs ys : List (B q)} {r s t : R q} {x y : B q}
      (square : Square hq r x y s) (tail : Strip hq xs s t ys) :
      Strip hq (x :: xs) r t (y :: ys)

theorem strip_length {q : ℕ} {hq : 0 < q}
    {xs ys : List (B q)} {r s : R q} (hs : Strip hq xs r s ys) :
    xs.length = ys.length := by
  induction hs with
  | nil => rfl
  | cons _ _ ih => simpa using ih

private theorem strip_right_unique {q : ℕ} {hq : 0 < q}
    {xs xs' ys : List (B q)} {r s s' : R q}
    (hs : Strip hq xs r s ys) (hs' : Strip hq xs' r s' ys) : xs = xs' ∧ s = s' := by
  induction hs generalizing xs' s' with
  | nil r => cases hs'; exact ⟨rfl, rfl⟩
  | cons sq tail ih =>
      cases hs' with
      | cons sq' tail' =>
          obtain ⟨hx, rfl⟩ := square_right_unique sq sq' rfl rfl
          obtain ⟨hxs, hs⟩ := ih tail'
          exact ⟨by simp [hx, hxs], hs⟩

private theorem strip_left_rank {q : ℕ} {hq : 0 < q} (he : Even q)
    {xs ys ys' : List (B q)} {r r' s s' : R q}
    (hs : Strip hq xs r s ys) (hs' : Strip hq xs r' s' ys') (hn : r ≠ r') :
    leftRank r r' + xs.length ≤ leftRank s s' := by
  induction hs generalizing r' s' ys' with
  | nil r => cases hs'; simp
  | @cons xs ys r m s x y sq tail ih =>
      cases hs' with
      | @cons _ ys' r' m' _ _ y' sq' tail' =>
          have hd := leftRank_step he sq sq' rfl hn
          have hm : m ≠ m' := by
            intro h
            subst m'
            exact hn (square_left_unique sq sq' rfl rfl).1
          have ht := ih tail' hm
          simp only [List.length_cons]
          omega

private theorem strip_right_rank {q : ℕ} {hq : 0 < q} (he : Even q)
    {xs xs' ys : List (B q)} {r r' s s' : R q}
    (hs : Strip hq xs r s ys) (hs' : Strip hq xs' r' s' ys) (hn : s ≠ s') :
    rightRank hq s s' + ys.length ≤ rightRank hq r r' := by
  induction hs generalizing xs' r' s' with
  | nil r => cases hs'; simp
  | @cons xs ys r m s x y sq tail ih =>
      cases hs' with
      | @cons xs' _ r' m' _ x' _ sq' tail' =>
          have hm : m ≠ m' := by
            intro h
            subst m'
            exact hn (strip_right_unique tail tail').2
          have hd := rightRank_step he sq sq' rfl hm
          have ht := ih tail' hn
          simp only [List.length_cons]
          omega

/- Uniform q-step contraction on ALL legal strips.  The terminal boundaries
   on the left have independent targets; initial boundaries on the right
   have independent origins.  Those endpoints are never equated here. -/
theorem strip_left_forgets {q : ℕ} {hq : 0 < q} (he : Even q)
    {xs ys ys' : List (B q)} {r r' s s' : R q}
    (hs : Strip hq xs r s ys) (hs' : Strip hq xs r' s' ys')
    (hlen : xs.length = q) (hc : sourceR s = sourceR s') :
    originalBoundary hq r = originalBoundary hq r' := by
  have hr : r = r' := by
    by_contra hn
    have hb := leftRank_le he hc
    have hd := strip_left_rank he hs hs' hn
    have hsource : sourceR r = sourceR r' := by
      cases hs with
      | nil => simp only [List.length_nil] at hlen; omega
      | cons sq tail =>
          cases hs' with
          | cons sq' tail' => exact (square_endpoints sq).1.trans (square_endpoints sq').1.symm
    have hp := leftRank_positive hsource hn
    omega
  exact congrArg (originalBoundary hq) hr

theorem strip_right_forgets {q : ℕ} {hq : 0 < q} (he : Even q)
    {xs xs' ys : List (B q)} {r r' s s' : R q}
    (hs : Strip hq xs r s ys) (hs' : Strip hq xs' r' s' ys)
    (hlen : ys.length = q) : originalBoundary hq s = originalBoundary hq s' := by
  have ht : s = s' := by
    by_contra hn
    have hb := rightRank_le hq r r'
    have hd := strip_right_rank he hs hs' hn
    have hp := rightRank_positive hq hn
    omega
  exact congrArg (originalBoundary hq) ht

def sweepLeft {q : ℕ} (hq : 0 < q) : List (B q) → R q → R q × List (B q)
  | [], s => (s, [])
  | x :: xs, s =>
      let tail := sweepLeft hq xs s
      let sq := leftSquare hq x tail.1
      (sq.1, sq.2 :: tail.2)

def sweepRight {q : ℕ} (hq : 0 < q) : R q → List (B q) → List (B q) × R q
  | r, [] => ([], r)
  | r, y :: ys =>
      let sq := rightSquare hq r y
      let tail := sweepRight hq sq.2 ys
      (sq.1 :: tail.1, tail.2)

theorem sweepLeft_length {q : ℕ} (hq : 0 < q) (xs : List (B q)) (s : R q) :
    (sweepLeft hq xs s).2.length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sweepLeft, ih]

theorem sweepRight_length {q : ℕ} (hq : 0 < q) (ys : List (B q)) (r : R q) :
    (sweepRight hq r ys).1.length = ys.length := by
  induction ys generalizing r with
  | nil => rfl
  | cons y ys ih => simp [sweepRight, ih]

inductive ListPath {q : ℕ} (hq : 0 < q) :
    Vertex q → List (B q) → Vertex q → Prop
  | nil (v : Vertex q) : ListPath hq v [] v
  | cons {v z : Vertex q} {x : B q} {xs : List (B q)}
      (hs : sourceB x = v) (tail : ListPath hq (targetB hq x) xs z) :
      ListPath hq v (x :: xs) z

theorem sweepLeft_sound {q : ℕ} {hq : 0 < q}
    {v z : Vertex q} {xs : List (B q)} (hp : ListPath hq v xs z)
    (s : R q) (hs : sourceR s = z) :
    Strip hq xs (sweepLeft hq xs s).1 s (sweepLeft hq xs s).2 ∧
      sourceR (sweepLeft hq xs s).1 = v := by
  induction hp generalizing s with
  | nil v => exact ⟨.nil s, hs⟩
  | @cons v z x xs hx tail ih =>
      obtain ⟨ht, hb⟩ := ih s hs
      have sq := leftSquare_spec hq x (sweepLeft hq xs s).1 hb.symm
      exact ⟨.cons sq ht, (square_endpoints sq).1.trans hx⟩

theorem sweepRight_sound {q : ℕ} {hq : 0 < q}
    {v z : Vertex q} {ys : List (B q)} (hp : ListPath hq v ys z)
    (r : R q) (hr : targetR hq r = v) :
    Strip hq (sweepRight hq r ys).1 r (sweepRight hq r ys).2 ys ∧
      targetR hq (sweepRight hq r ys).2 = z := by
  induction hp generalizing r with
  | nil v => exact ⟨.nil r, hr⟩
  | @cons v z y ys hy tail ih =>
      have sq := rightSquare_spec hq r y (hr.trans hy.symm)
      obtain ⟨ht, hb⟩ := ih (rightSquare hq r y).2 (square_endpoints sq).2.2.2
      exact ⟨.cons sq ht, hb⟩

def pick {q : ℕ} (hq : 0 < q) (xs : List (B q)) (k : ℕ) : B q :=
  xs.getD k (.f (zero hq) 1)

theorem pick_eq {q : ℕ} (hq : 0 < q) (xs : List (B q)) (k : ℕ)
    (hk : k < xs.length) : pick hq xs k = xs[k] := by
  exact (List.getElem_eq_getD (B.f (zero hq) 1)).symm

theorem strip_split {q : ℕ} {hq : 0 < q}
    {xs ys : List (B q)} {r s : R q} (hs : Strip hq xs r s ys) (n : ℕ) :
    ∃ t, Strip hq (xs.take n) r t (ys.take n) ∧
      Strip hq (xs.drop n) t s (ys.drop n) := by
  induction n generalizing xs ys r with
  | zero => exact ⟨r, .nil r, by simpa using hs⟩
  | succ n ih =>
      cases hs with
      | nil => exact ⟨s, by simpa using Strip.nil (hq := hq) s,
          by simpa using Strip.nil (hq := hq) s⟩
      | cons sq tail =>
          obtain ⟨t, hp, ht⟩ := ih tail
          exact ⟨t, by simpa using Strip.cons sq hp, by simpa using ht⟩

theorem strip_window {q : ℕ} {hq : 0 < q}
    {xs ys : List (B q)} {r s : R q} (hs : Strip hq xs r s ys) (a n : ℕ) :
    ∃ u v, Strip hq ((xs.drop a).take n) u v ((ys.drop a).take n) := by
  obtain ⟨u, _, ht⟩ := strip_split hs a
  obtain ⟨v, hp, _⟩ := strip_split ht n
  exact ⟨u, v, hp⟩

private theorem strip_terminal_source {q : ℕ} {hq : 0 < q}
    {xs ys ys' : List (B q)} {r r' s s' : R q}
    (hs : Strip hq xs r s ys) (hs' : Strip hq xs r' s' ys') (hn : xs ≠ []) :
    sourceR s = sourceR s' := by
  induction hs generalizing r' s' ys' with
  | nil => exact False.elim (hn rfl)
  | @cons xs ys r m s x y sq tail ih =>
      cases hs' with
      | cons sq' tail' =>
          by_cases hx : xs = []
          · subst xs
            cases tail
            cases tail'
            exact (square_endpoints sq).2.2.1.symm.trans (square_endpoints sq').2.2.1
          · exact ih tail' hx

theorem first_output_independent {q : ℕ} {hq : 0 < q} (he : Even q)
    {xs ys ys' : List (B q)} {r r' s s' : R q}
    (hs : Strip hq xs r s ys) (hs' : Strip hq xs r' s' ys')
    (hlen : xs.length = q + 1) : pick hq ys 0 = pick hq ys' 0 := by
  have hc := strip_terminal_source hs hs' (by intro h; simp [h] at hlen)
  cases hs with
  | nil => simp at hlen
  | @cons xs ys r m s x y sq tail =>
      cases hs' with
      | @cons _ ys' r' m' _ _ y' sq' tail' =>
          have ht : xs.length = q := by simpa using hlen
          have hm := (actualBoundaryEquiv hq).injective (strip_left_forgets he tail tail' ht hc)
          have hy := (square_left_unique sq sq' rfl hm).2
          simpa [pick] using hy

private theorem drop_last {q : ℕ} (hq : 0 < q) (xs : List (B q))
    (hlen : xs.length = q + 1) : xs.drop q = [pick hq xs q] := by
  have hk : q < xs.length := by omega
  rw [List.drop_eq_getElem_cons hk, pick_eq hq xs q hk]
  have ht : xs.drop (q + 1) = [] := List.drop_eq_nil_iff.mpr (by omega)
  rw [ht]

theorem last_input_independent {q : ℕ} {hq : 0 < q} (he : Even q)
    {xs xs' ys : List (B q)} {r r' s s' : R q}
    (hs : Strip hq xs r s ys) (hs' : Strip hq xs' r' s' ys)
    (hlen : ys.length = q + 1) : pick hq xs q = pick hq xs' q := by
  have hx : xs.length = q + 1 := (strip_length hs).trans hlen
  have hx' : xs'.length = q + 1 := (strip_length hs').trans hlen
  obtain ⟨m, hp, ht⟩ := strip_split hs q
  obtain ⟨m', hp', ht'⟩ := strip_split hs' q
  have hm := (actualBoundaryEquiv hq).injective (strip_right_forgets he hp hp' (by simp [hlen]))
  rw [drop_last hq xs hx, drop_last hq ys hlen] at ht
  rw [drop_last hq xs' hx', drop_last hq ys hlen] at ht'
  cases ht with
  | cons sq tail =>
      cases ht' with
      | cons sq' tail' => exact (square_right_unique sq sq' hm rfl).1

end Alternating

end D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
