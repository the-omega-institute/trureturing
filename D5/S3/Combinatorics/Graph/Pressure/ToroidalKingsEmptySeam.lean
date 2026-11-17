/- GID: D5/S3/Combinatorics/Graph/Pressure/ToroidalKingsEmptySeam
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Pressure/ToroidalKingsEmptySeam
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Empty seams remove additional toroidal king edges. -/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import D5.S3.Combinatorics.Graph.Pressure.RectangularCountEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Lean.Elab.Tactic.Omega

/-! # Finite king-board counts and empty seams

The coordinate and cardinality definitions retain both periodic coordinates and
all side lengths. The peak counts all cardinality fibers, including the empty set.
-/

namespace D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam

open Finset
open Filter
open scoped Topology

noncomputable section

/-- Absolute coordinate difference, represented in natural arithmetic. -/
def gap (a b : ℕ) : ℕ := (a - b) + (b - a)

def freeAdjacent (u v : ℕ × ℕ) : Prop :=
  u ≠ v ∧ gap u.1 v.1 ≤ 1 ∧ gap u.2 v.2 ≤ 1

def torusAdjacent (n : ℕ) (u v : ℕ × ℕ) : Prop :=
  u ≠ v ∧ min (gap u.1 v.1) (n - gap u.1 v.1) ≤ 1 ∧
    min (gap u.2 v.2) (n - gap u.2 v.2) ≤ 1

private theorem seam_distance {n a b : ℕ} (ha : a < n - 1) (hb : b < n - 1) :
    min (gap a b) (n - gap a b) ≤ 1 ↔ gap a b ≤ 1 := by
  unfold gap
  omega

/-- Identity on the board with the final row and column empty reflects and
preserves all king edges, including for odd side lengths. -/
theorem empty_seam_adjacency {n : ℕ} (u v : ℕ × ℕ)
    (hu : u.1 < n - 1 ∧ u.2 < n - 1)
    (hv : v.1 < n - 1 ∧ v.2 < n - 1) :
    torusAdjacent n u v ↔ freeAdjacent u v := by
  simp only [torusAdjacent, freeAdjacent,
    seam_distance hu.1 hv.1, seam_distance hu.2 hv.2]

/-- The free square board, using the literal coordinate range of the source. -/
def board (n : ℕ) : Finset (ℕ × ℕ) := (range n) ×ˢ (range n)

/-- Independent vertex subsets of a finite board for the specified adjacency. -/
def independentSets (b : Finset (ℕ × ℕ)) (adj : (ℕ × ℕ) → (ℕ × ℕ) → Prop) :
    Finset (Finset (ℕ × ℕ)) := by
  classical
  exact b.powerset.filter fun s => ∀ u ∈ s, ∀ v ∈ s, ¬ adj u v

private theorem mem_independentSets {b : Finset (ℕ × ℕ)}
    {adj : (ℕ × ℕ) → (ℕ × ℕ) → Prop} {s : Finset (ℕ × ℕ)} :
    s ∈ independentSets b adj ↔ s ⊆ b ∧ ∀ u ∈ s, ∀ v ∈ s, ¬ adj u v := by
  classical
  simp [independentSets]

/-- Total free-board and toroidal independent-set counts. -/
def freeCount (n : ℕ) : ℕ := (independentSets (board n) freeAdjacent).card

/-- Rectangles used to restrict a free configuration along a straight cut. -/
def rectangleCount (r c : ℕ) : ℕ :=
  (independentSets ((range r) ×ˢ (range c)) freeAdjacent).card

private theorem freeCount_eq_rectangle (n : ℕ) : freeCount n = rectangleCount n n := rfl

private def lowerPart (r : ℕ) (s : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  s.filter fun u => u.1 < r

private def upperPart (r : ℕ) (s : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  (s.filter fun u => r ≤ u.1).image fun u => (u.1 - r, u.2)

private theorem rectangle_cut (r t c : ℕ) :
    rectangleCount (r + t) c ≤ rectangleCount r c * rectangleCount t c := by
  classical
  let A := independentSets ((range (r + t)) ×ˢ (range c)) freeAdjacent
  let B := independentSets ((range r) ×ˢ (range c)) freeAdjacent
  let C := independentSets ((range t) ×ˢ (range c)) freeAdjacent
  have hmap : Set.MapsTo (fun s => (lowerPart r s, upperPart r s))
      (↑A : Set _) (↑(B ×ˢ C) : Set _) := by
    intro s hs
    obtain ⟨hb, hi⟩ := mem_independentSets.mp hs
    apply mem_product.mpr
    constructor
    · apply mem_independentSets.mpr
      constructor
      · intro u hu
        obtain ⟨hu, hr⟩ := mem_filter.mp hu
        have hc := (mem_product.mp (hb hu)).2
        exact mem_product.mpr ⟨mem_range.mpr hr, hc⟩
      · intro u hu v hv
        exact hi u (mem_filter.mp hu).1 v (mem_filter.mp hv).1
    · apply mem_independentSets.mpr
      constructor
      · intro u hu
        obtain ⟨v, hv, rfl⟩ := mem_image.mp hu
        obtain ⟨hv, hr⟩ := mem_filter.mp hv
        obtain ⟨hv1, hv2⟩ := mem_product.mp (hb hv)
        simp only [mem_range] at hv1 hv2
        simp only [mem_product, mem_range]
        exact ⟨by omega, hv2⟩
      · intro u hu v hv hadj
        obtain ⟨a, ha, rfl⟩ := mem_image.mp hu
        obtain ⟨b, hb', rfl⟩ := mem_image.mp hv
        obtain ⟨ha, hra⟩ := mem_filter.mp ha
        obtain ⟨hb', hrb⟩ := mem_filter.mp hb'
        apply hi a ha b hb'
        rcases hadj with ⟨hne, hx, hy⟩
        refine ⟨?_, ?_, hy⟩
        · intro heq
          exact hne (congrArg (fun u : ℕ × ℕ => (u.1 - r, u.2)) heq)
        · unfold gap at hx ⊢
          omega
  have hinj : Set.InjOn (fun s => (lowerPart r s, upperPart r s)) A := by
    intro s hs t' ht h
    have hlo := congrArg Prod.fst h
    have hhi := congrArg Prod.snd h
    dsimp at hlo hhi
    ext u
    have reconstruct (s : Finset (ℕ × ℕ)) :
        u ∈ s ↔ u ∈ lowerPart r s ∨ r ≤ u.1 ∧ (u.1 - r, u.2) ∈ upperPart r s := by
      constructor
      · intro hu
        by_cases hr : u.1 < r
        · exact Or.inl (mem_filter.mpr ⟨hu, hr⟩)
        · exact Or.inr ⟨by omega, mem_image.mpr ⟨u, mem_filter.mpr ⟨hu, by omega⟩, rfl⟩⟩
      · rintro (hu | ⟨hr, hu⟩)
        · exact (mem_filter.mp hu).1
        · obtain ⟨v, hv, heq⟩ := mem_image.mp hu
          obtain ⟨hv, hrv⟩ := mem_filter.mp hv
          have hx := congrArg Prod.fst heq
          have hy := congrArg Prod.snd heq
          have hvu : v = u := Prod.ext (by dsimp at hx; omega) hy
          simpa [hvu] using hv
    rw [reconstruct s, reconstruct t', hlo, hhi]
  simpa [A, B, C, rectangleCount, card_product] using
    card_le_card_of_injOn (fun s => (lowerPart r s, upperPart r s)) hmap hinj

private theorem rectangle_symm (r c : ℕ) : rectangleCount r c = rectangleCount c r := by
  classical
  have hle (r c : ℕ) : rectangleCount r c ≤ rectangleCount c r := by
    apply card_le_card_of_injOn (fun s : Finset (ℕ × ℕ) => s.image Prod.swap)
    · intro s hs
      obtain ⟨hb, hi⟩ := mem_independentSets.mp hs
      apply mem_independentSets.mpr
      constructor
      · intro u hu
        obtain ⟨v, hv, rfl⟩ := mem_image.mp hu
        exact mem_product.mpr ⟨(mem_product.mp (hb hv)).2, (mem_product.mp (hb hv)).1⟩
      · intro u hu v hv hadj
        obtain ⟨a, ha, rfl⟩ := mem_image.mp hu
        obtain ⟨b, hb', rfl⟩ := mem_image.mp hv
        exact hi a ha b hb' ⟨fun h => hadj.1 (congrArg Prod.swap h), hadj.2.2, hadj.2.1⟩
    · intro s hs t ht heq
      have h := congrArg (fun s : Finset (ℕ × ℕ) => s.image Prod.swap) heq
      simpa [image_image, Function.comp_def] using h
  exact le_antisymm (hle r c) (hle c r)

private theorem rectangle_pos (r c : ℕ) : 0 < rectangleCount r c := by
  apply card_pos.mpr
  exact ⟨∅, mem_independentSets.mpr ⟨empty_subset _, by simp⟩⟩

private theorem rectangle_le_binary (r c : ℕ) : rectangleCount r c ≤ 2 ^ (r * c) := by
  classical
  have h := card_le_card (filter_subset
    (fun s : Finset (ℕ × ℕ) => ∀ u ∈ s, ∀ v ∈ s, ¬ freeAdjacent u v)
    (((range r) ×ˢ (range c)).powerset))
  simpa [rectangleCount, independentSets, card_powerset, card_product] using h

def torusCount (n : ℕ) : ℕ := (independentSets (board n) (torusAdjacent n)).card

/-- Every coefficient, including zero coefficients outside the independence number. -/
def coefficient (n k : ℕ) : ℕ := by
  classical
  exact ((independentSets (board n) (torusAdjacent n)).filter fun s => s.card = k).card

/-- The maximum over all cardinalities from zero through the number of vertices. -/
def peak (n : ℕ) : ℕ := (range (n ^ 2 + 1)).sup (coefficient n)

private theorem board_mono {m n : ℕ} (h : m ≤ n) : board m ⊆ board n := by
  intro u hu
  simp only [board, mem_product, mem_range] at hu ⊢
  exact ⟨hu.1.trans_le h, hu.2.trans_le h⟩

/-- Empty final row and column give an injection valid for every side length. -/
theorem free_le_torus (n : ℕ) : freeCount (n - 1) ≤ torusCount n := by
  apply card_le_card
  intro s hs
  obtain ⟨hb, hi⟩ := mem_independentSets.mp hs
  refine mem_independentSets.mpr ⟨hb.trans (board_mono (Nat.sub_le n 1)), ?_⟩
  intro u hu v hv hadj
  have hbu := hb hu
  have hbv := hb hv
  simp only [board, mem_product, mem_range] at hbu hbv
  exact hi u hu v hv ((empty_seam_adjacency u v hbu hbv).mp hadj)

/-- Forgetting the wraparound edges is an injection into the free board. -/
theorem torus_le_free (n : ℕ) : torusCount n ≤ freeCount n := by
  apply card_le_card
  intro s hs
  obtain ⟨hb, hi⟩ := mem_independentSets.mp hs
  refine mem_independentSets.mpr ⟨hb, ?_⟩
  intro u hu v hv hfree
  exact hi u hu v hv ⟨hfree.1, (min_le_left _ _).trans hfree.2.1,
    (min_le_left _ _).trans hfree.2.2⟩

private theorem coefficient_sum (n : ℕ) :
    ∑ k ∈ range (n ^ 2 + 1), coefficient n k = torusCount n := by
  classical
  symm
  apply card_eq_sum_card_fiberwise
  intro s hs
  have h := card_le_card (mem_independentSets.mp hs).1
  simpa [board, card_product, card_range, pow_two] using Nat.lt_succ_of_le h

private theorem coefficient_le_peak (n k : ℕ) (hk : k ∈ range (n ^ 2 + 1)) :
    coefficient n k ≤ peak n := Finset.le_sup hk

/-- The modal coefficient loses at most the number of cardinality fibers. -/
theorem count_le_mul_peak (n : ℕ) : torusCount n ≤ (n ^ 2 + 1) * peak n := by
  rw [← coefficient_sum]
  calc
    ∑ k ∈ range (n ^ 2 + 1), coefficient n k ≤
        ∑ _k ∈ range (n ^ 2 + 1), peak n :=
      sum_le_sum fun k hk => coefficient_le_peak n k hk
    _ = (n ^ 2 + 1) * peak n := by simp

theorem peak_le_count (n : ℕ) : peak n ≤ torusCount n := by
  classical
  apply Finset.sup_le
  intro k hk
  exact card_le_card (filter_subset _ _)

/-- A two-by-two tile is specified by its lower-left cell. -/
def squareTile (u : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  ({u.1, u.1 + 1} : Finset ℕ) ×ˢ ({u.2, u.2 + 1} : Finset ℕ)

/-- A tiling by unit and two-by-two squares is encoded by its two-by-two
placements. Every cell outside those tiles has its unique unit tile. -/
def tilingPlacements (m : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  independentSets (board (m - 1))
    (fun u v => u ≠ v ∧ ¬ Disjoint (squareTile u) (squareTile v))

/-- The literal square-tiling count used by OEIS A063443. -/
def a063443 (m : ℕ) : ℕ := (tilingPlacements m).card

/-- The complete collection of tiles recovered from a placement encoding. -/
def tilingBlocks (m : ℕ) (s : Finset (ℕ × ℕ)) : Finset (Finset (ℕ × ℕ)) :=
  s.image squareTile ∪ (board m \ s.biUnion squareTile).image (fun u => {u})

private theorem tile_overlap (u v : ℕ × ℕ) :
    ¬ Disjoint (squareTile u) (squareTile v) ↔
      gap u.1 v.1 ≤ 1 ∧ gap u.2 v.2 ≤ 1 := by
  simp only [squareTile, disjoint_product, disjoint_insert_left, disjoint_singleton_left,
    mem_insert, mem_singleton, not_or, not_and, not_not, gap]
  omega

/-- The tiling encoding and free king-board configurations are the same finite
objects, with the source's exact side shift m minus one. -/
theorem tiling_free_identity (m : ℕ) : a063443 m = freeCount (m - 1) := by
  classical
  change (tilingPlacements m).card = (independentSets (board (m - 1)) freeAdjacent).card
  congr 1
  apply Finset.ext
  intro s
  simp only [a063443, freeCount, tilingPlacements, mem_independentSets]
  simp only [tile_overlap, freeAdjacent]

private theorem rectangle_log_subadditive (c : ℕ) :
    Subadditive (fun r => Real.log (rectangleCount r c : ℝ)) := by
  intro r t
  have hp (r : ℕ) : (0 : ℝ) < rectangleCount r c := by exact_mod_cast rectangle_pos r c
  have hle : (rectangleCount (r + t) c : ℝ) ≤
      (rectangleCount r c : ℝ) * (rectangleCount t c : ℝ) := by
    exact_mod_cast rectangle_cut r t c
  simpa only [Real.log_mul (hp r).ne' (hp t).ne'] using
    Real.log_le_log (hp (r + t)) hle

private theorem rectangle_log_bounds (r c : ℕ) :
    0 ≤ Real.log (rectangleCount r c : ℝ) ∧
      Real.log (rectangleCount r c : ℝ) ≤ (r : ℝ) * c * Real.log 2 := by
  have h1 : (1 : ℝ) ≤ rectangleCount r c := by exact_mod_cast rectangle_pos r c
  refine ⟨Real.log_nonneg h1, ?_⟩
  have hp : (0 : ℝ) < rectangleCount r c := by exact_mod_cast rectangle_pos r c
  have hle : (rectangleCount r c : ℝ) ≤ (2 : ℝ) ^ (r * c) := by
    exact_mod_cast rectangle_le_binary r c
  have h := Real.log_le_log hp hle
  simpa [Real.log_pow, Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using h

theorem free_log_limit : ∃ s : ℝ, 0 ≤ s ∧
    Tendsto (fun n : ℕ => Real.log (freeCount n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 s) := by
  simpa only [freeCount_eq_rectangle] using
    RectangularCountEntropy.square_log_limit
      (fun r c => Real.log (rectangleCount r c : ℝ)) (Real.log 2)
      (Real.log_nonneg (by norm_num))
      (fun r c => congrArg (fun n : ℕ => Real.log (n : ℝ)) (rectangle_symm r c))
      rectangle_log_subadditive rectangle_log_bounds

#print axioms empty_seam_adjacency
#print axioms free_le_torus
#print axioms torus_le_free
#print axioms count_le_mul_peak
#print axioms peak_le_count
#print axioms tiling_free_identity
#print axioms free_log_limit
end
end D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam
