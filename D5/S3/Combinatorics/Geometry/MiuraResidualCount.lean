/- GID: D5/S3/Combinatorics/Geometry/MiuraResidualCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraResidualCount
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The Miura residual count retains exact extrema and one common side. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraHeightEnvelope
public import Mathlib.Algebra.MvPolynomial.Degrees

/-! Exact split counts and the full residual polynomial assertion. -/

@[expose] public section

namespace D5.S3.Combinatorics.Geometry.MiuraResidualCount

open MiuraHeightEnvelope

/- Side and AllOnSide are adapted from Chakshu Gupta, SequelSplitEdge.lean,
blob ee108001d1d12f68c137ac033ed22ced3fae225f in source tree
8beb89d4466cb8551abc92d0405972edc2edf116. CC BY 4.0;
see docs/reports/miura-suppliers/lab-NOTICE.txt and lab-LICENSE.txt.
The source's one-indexed integer positions are used literally below.
Retire this transplant if equivalent declarations occur in this project's pinned mathlib.
-/
inductive Side where
  | top | bottom | left | right
  deriving DecidableEq, Repr

open Side

variable {ι : Type*} (p : ι → ℤ × ℤ) (S : Finset ι)

/-- All apexes indexed by `S` lie on side `sd` of the `m × n` grid. -/
def AllOnSide (m n : ℤ) (sd : Side) : Prop :=
  match sd with
  | top    => ∀ s ∈ S, (p s).1 = 1
  | bottom => ∀ s ∈ S, (p s).1 = m
  | left   => ∀ s ∈ S, (p s).2 = 1
  | right  => ∀ s ∈ S, (p s).2 = n


section Count

variable {m n : ℕ}

noncomputable def minima (h : Cell m n → ℤ) : Finset (Cell m n) := by
  classical
  exact Finset.univ.filter (IsStrictLocalMin h)

noncomputable def maxima (h : Cell m n → ℤ) : Finset (Cell m n) := by
  classical
  exact Finset.univ.filter (IsStrictLocalMax h)

/-- Exactly one common side is tested, with every existing neighbour used for extrema. -/
def Residual (a b : ℕ) (h : Cell m n → ℤ) : Prop :=
  IsCanonicalHeight h ∧ (minima h).card = a ∧ (maxima h).card = b ∧
    ¬ ∃ sd : Side, AllOnSide
      (fun v : Cell m n => ((v.1.val : ℤ) + 1, (v.2.val : ℤ) + 1))
      (minima h) (m : ℤ) (n : ℤ) sd

/-- The exact normalized residual class is finite, without a counting assumption. -/
theorem residual_finite (a b : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    {h : Cell m n → ℤ | Residual a b h}.Finite :=
  (CanonicalHeights_finite hm hn).subset fun _ h => h.1

/-- Cardinality counts actual normalized functions; finiteness is proved above. -/
noncomputable def residualCount (a b m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) : ℕ :=
  (residual_finite a b hm hn).toFinset.card

end Count

/-- The full statement of arXiv:2607.05567v3, Conjecture 8.3 and Lemma 8.2. -/
def claim : Prop :=
  ∀ d a b : ℕ, ∀ hd : 5 ≤ d, 1 ≤ a → 1 ≤ b → a + b = d → a ≤ b →
    ∃ p : MvPolynomial (Fin 2) ℚ, p.totalDegree ≤ d - 3 ∧
      ∀ m n : ℕ, ∀ hm : 2 * d - 1 ≤ m, ∀ hn : 2 * d - 1 ≤ n,
        MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (m : ℚ) else (n : ℚ)) p =
          (residualCount a b m n (by omega) (by omega) : ℚ)

end D5.S3.Combinatorics.Geometry.MiuraResidualCount
