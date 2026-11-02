/- GID: D5/S3/Geometry/KingFiniteReplay/FiniteLabels
   generality: G
   mirror-B: D5/B/S3/Geometry/KingFiniteReplay/FiniteLabels
   mirror-E: none(waiver:finite-graph-singular-homology)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Maps]
   utility: none
   digest: Finite label and adjacency reductions consumed by the forty literal graph moves. -/
import D5.S3.Geometry.FiniteGraphSuspensionMoves
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Bitwise

/-!
# Exact finite labels and adjacency rows

The graph is defined by its original unordered edge list. A proved bit-row
identity evaluates the same adjacency relation. Old and fresh label maps
assemble an equivalence when their images are disjoint and jointly cover
the specified target finite set.
-/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.KingFiniteReplay

open FiniteGraphSuspensionMoves

/-- An unordered edge is represented by either order in the actual edge list.
The graph uses the list itself, not a separately postulated adjacency table. -/
def listGraph (S : Finset ℕ) (E : List (ℕ × ℕ)) : SimpleGraph ↥S where
  Adj x y := x ≠ y ∧ ((x.val, y.val) ∈ E ∨ (y.val, x.val) ∈ E)
  symm.symm := fun _ _ h => ⟨Ne.symm h.1, h.2.symm⟩
  loopless.irrefl := fun _ h => h.1 rfl

instance (priority := 100) listGraphDecidable (S : Finset ℕ) (E : List (ℕ × ℕ)) :
    DecidableRel (listGraph S E).Adj := by
  intro x y
  change Decidable (x ≠ y ∧ ((x.val, y.val) ∈ E ∨ (y.val, x.val) ∈ E))
  infer_instance

/-- A row bitset computed from the edge list by ordinary recursive definitions.
It is used only to accelerate finite decisions about `listGraph`. -/
def rowBits : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (a, b) :: E, x =>
      (if x = a then 2 ^ b else 0) |||
        ((if x = b then 2 ^ a else 0) ||| rowBits E x)

theorem rowBits_spec (E : List (ℕ × ℕ)) (x y : ℕ) :
    (rowBits E x).testBit y = true ↔ ((x, y) ∈ E ∨ (y, x) ∈ E) := by
  induction E with
  | nil => simp [rowBits]
  | cons e E ih =>
    rcases e with ⟨a, b⟩
    have ha : (if x = a then 2 ^ b else 0).testBit y = true ↔ x = a ∧ y = b := by
      by_cases hx : x = a <;> simp [hx, Nat.testBit_two_pow, eq_comm]
    have hb : (if x = b then 2 ^ a else 0).testBit y = true ↔ x = b ∧ y = a := by
      by_cases hx : x = b <;> simp [hx, Nat.testBit_two_pow, eq_comm]
    simp only [rowBits, Nat.testBit_lor, Bool.or_eq_true, ha, hb, ih,
      List.mem_cons, Prod.mk.injEq]
    tauto

/-- Every cached row has a kernel proof of equality with the row computed
from the actual edge list. The cache changes only the decision procedure. -/
def cachedAdjDecidable (S : Finset ℕ) (E : List (ℕ × ℕ))
    (rows : ℕ → ℕ) (hrows : ∀ x : S, rowBits E x.val = rows x.val) :
    DecidableRel (listGraph S E).Adj := fun x y =>
  decidable_of_iff (x ≠ y ∧ (rows x.val).testBit y.val = true) (by
    change (x ≠ y ∧ (rows x.val).testBit y.val = true) ↔
      (x ≠ y ∧ ((x.val, y.val) ∈ E ∨ (y.val, x.val) ∈ E))
    rw [← hrows x, rowBits_spec])

/-- The fresh branch is disjoint from every surviving old label. In the
Lozin case the old domain already excludes precisely the deleted vertex. -/
theorem sumLabel_injective {O N : Type} (old : O → ℕ) (fresh : N → ℕ)
    (hold : Function.Injective old) (hnew : Function.Injective fresh)
    (hdisj : ∀ o n, old o ≠ fresh n) :
    Function.Injective (Sum.elim old fresh) := by
  rintro (o | n) (p | m) h
  · exact congrArg Sum.inl (hold h)
  · exact False.elim (hdisj o m h)
  · exact False.elim (hdisj p n h.symm)
  · exact congrArg Sum.inr (hnew h)

/-- A genuine equivalence onto the actual next Nat-vertex subtype, with
membership, injectivity, freshness and coverage supplied as proved terms. -/
def sumLabels {O N : Type} (T : Finset ℕ) (old : O → ℕ) (fresh : N → ℕ)
    (hold : Function.Injective old) (hnew : Function.Injective fresh)
    (hdisj : ∀ o n, old o ≠ fresh n)
    (hin : ∀ a : O ⊕ N, Sum.elim old fresh a ∈ T)
    (honto : ∀ t : T, ∃ a : O ⊕ N, Sum.elim old fresh a = t.val) :
    (O ⊕ N) ≃ ↥T :=
  Equiv.ofBijective (fun a => ⟨Sum.elim old fresh a, hin a⟩) ⟨by
    intro a b h
    exact sumLabel_injective old fresh hold hnew hdisj (congrArg Subtype.val h), by
    intro t
    obtain ⟨a, ha⟩ := honto t
    exact ⟨a, Subtype.ext ha⟩⟩

/-- Prove a mapped-graph equality by its forward finite adjacency table.
There is no existential search over `SimpleGraph.map` in the finite check. -/
theorem map_eq_of_forward {A B : Type} (G : SimpleGraph A) (F : SimpleGraph B)
    (e : A ≃ B) (h : ∀ x y, F.Adj (e x) (e y) ↔ G.Adj x y) : G.map e = F := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  obtain ⟨x, rfl⟩ := e.surjective u
  obtain ⟨y, rfl⟩ := e.surjective v
  exact ((SimpleGraph.Iso.map e G).map_adj_iff).trans (h x y).symm

/- The literal supplier keeps its adjacency helpers private. These instances
expose their definitional decisions without modifying any supplier file. -/

variable {V : Type} [Fintype V] [DecidableEq V]

instance tripleAdjDecidable (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    DecidableRel (tripleSubdivision G a b).Adj := by
  rintro (x | i) (y | j)
  · change Decidable (G.Adj x y ∧ ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a)))
    infer_instance
  · change Decidable ((j = 0 ∧ x = a) ∨ (j = 2 ∧ x = b))
    infer_instance
  · change Decidable ((i = 0 ∧ y = a) ∨ (i = 2 ∧ y = b))
    infer_instance
  · change Decidable (i.val + 1 = j.val ∨ j.val + 1 = i.val)
    infer_instance

instance crossingAdjDecidable (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : (Bool × Bool) ↪ V) : DecidableRel (crossingSuspension G e).Adj := by
  rintro (x | p) (y | q)
  · change Decidable (G.Adj x y ∧ ¬ matchingRemoved e x y)
    unfold matchingRemoved
    infer_instance
  · cases q with
    | none => exact isFalse id
    | some q =>
      change Decidable (x = e (false, q.1) ∨ x = e (true, q.2))
      infer_instance
  · cases p with
    | none => exact isFalse id
    | some p =>
      change Decidable (y = e (false, p.1) ∨ y = e (true, p.2))
      infer_instance
  · cases p <;> cases q <;> first | exact isFalse id | exact isTrue trivial

instance lozinAdjDecidable (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (Y Z : Finset V) : DecidableRel (lozinSuspension G v Y Z).Adj := by
  rintro (x | i) (y | j)
  · change Decidable (G.Adj x.val y.val)
    infer_instance
  · change Decidable ((j = 0 ∧ x.val ∈ Y) ∨ (j = 3 ∧ x.val ∈ Z))
    infer_instance
  · change Decidable ((i = 0 ∧ y.val ∈ Y) ∨ (i = 3 ∧ y.val ∈ Z))
    infer_instance
  · change Decidable (i.val + 1 = j.val ∨ j.val + 1 = i.val)
    infer_instance

end D5.S3.Geometry.KingFiniteReplay
