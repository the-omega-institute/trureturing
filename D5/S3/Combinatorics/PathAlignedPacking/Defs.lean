/- GID: D5/S3/Combinatorics/PathAlignedPacking/Defs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PathAlignedPacking/Defs
   mirror-E: none(waiver:fixed-public-definitions-for-path-aligned-packing)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric]
   utility: none
   digest: The path-aligned cycle chain and the two packing-colouring claims of issue 14183. -/

import Mathlib.Combinatorics.SimpleGraph.Metric

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PathAlignedPacking.Defs

/-- Block number and position around its cycle, both numbered from zero. -/
abbrev Vertex (t n : ℕ) := Fin t × Fin n

/-- Arithmetic coordinates used in distance certificates. -/
abbrev Point := ℕ × ℤ

def point {t n : ℕ} (v : Vertex t n) : Point := (v.1.val, v.2.val)

/-- Consecutive positions around a cycle; the last position is joined to zero. -/
def CycleAdj (n x y : ℤ) : Prop :=
  x + 1 = y ∨ y + 1 = x ∨ (x = 0 ∧ y + 1 = n) ∨ (y = 0 ∧ x + 1 = n)

/-- The exit has coordinate `a`; `b` is the length of the other entry–exit arc. -/
def RawAdj (a b : ℤ) (u v : Point) : Prop :=
  (u.1 = v.1 ∧ CycleAdj (a + b) u.2 v.2) ∨
  (u.1 + 1 = v.1 ∧ u.2 = a ∧ v.2 = 0) ∨
  (v.1 + 1 = u.1 ∧ v.2 = a ∧ u.2 = 0)

instance (a b : ℤ) : DecidableRel (RawAdj a b) := by
  unfold RawAdj CycleAdj
  infer_instance

/-- Exactly the graph in the question, with `a = ℓ - 1`, `b = n - ℓ + 1`.
    The guard makes this a simple graph even for parameters outside the claims. -/
def graph (n ℓ t : ℕ) : SimpleGraph (Vertex t n) where
  Adj u v := u ≠ v ∧ RawAdj (ℓ - 1 : ℕ) (n - ℓ + 1 : ℕ) (point u) (point v)
  symm := ⟨by
    intro u v h
    refine ⟨Ne.symm h.1, ?_⟩
    rcases h.2 with ⟨hi, hc⟩ | h | h
    · exact Or.inl ⟨hi.symm, by
        rcases hc with h | h | ⟨hx, hy⟩ | ⟨hy, hx⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr ⟨hx, hy⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨hy, hx⟩))⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

instance (n ℓ t : ℕ) : DecidableRel (graph n ℓ t).Adj := by
  unfold graph
  infer_instance

/-- A packing colouring, using walks to express distance strictly greater than the colour.
    This also handles disconnected graphs without the junk value of `SimpleGraph.dist`. -/
def PackingColoring {V : Type*} (G : SimpleGraph V) (k : ℕ) (f : V → ℕ) : Prop :=
  (∀ v, 1 ≤ f v ∧ f v ≤ k) ∧
  ∀ u v, u ≠ v → f u = f v → ∀ p : G.Walk u v, f u < p.length

def HasPacking {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ f : V → ℕ, PackingColoring G k f

/-- Furmańczyk–Gözüpek–Özkan, arXiv:2511.12761v1, Conjecture 1,
    with the exceptional cycle `C₅` removed. -/
def claimUpperFive : Prop :=
  ∀ n t ℓ : ℕ, 3 ≤ n → n ≠ 5 → 1 ≤ t → 4 ≤ ℓ → ℓ ≤ n →
    HasPacking (graph n ℓ t) 5

/-- The exceptional family has packing chromatic number exactly six from five blocks on.
    Existence at six and nonexistence at five are the usual equivalent formulation. -/
def claimCFiveSix : Prop :=
  ∀ t : ℕ, 5 ≤ t → ¬ HasPacking (graph 5 5 t) 5 ∧ HasPacking (graph 5 5 t) 6

end D5.S3.Combinatorics.PathAlignedPacking.Defs
