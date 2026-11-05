/- GID: D5/S3/Combinatorics/Graph/Domination/MertensGridGrowth
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/MertensGridGrowth
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.CycleGraph]
   utility: none
   digest: Ordinary labelled domination counts and finite boundary repair for grid cylinders. -/

import D5.S3.Combinatorics.Graph.DominatingSetAverage
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2000

noncomputable section

namespace D5.S3.Combinatorics.Graph.Domination.MertensGridGrowth

open Finset SimpleGraph
open DominatingSetAverage

/-- Number of all ordinary dominating vertex subsets, with no symmetry quotient. -/
def count {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  (domSets G).card

/-- The actual path Cartesian product on its labelled vertex set. -/
def grid (m n : ℕ) : SimpleGraph (Fin m × Fin n) := pathGraph m □ pathGraph n

/-- The actual cycle-path Cartesian product on the same labelled vertex set. -/
def cylinder (m n : ℕ) : SimpleGraph (Fin m × Fin n) := cycleGraph m □ pathGraph n

/-- Per-vertex growth, using real powers. Only positive dimensions enter the limit. -/
def growth (a m n : ℕ) : ℝ := (a : ℝ) ^ (1 / (m * n : ℕ) : ℝ)

/-- The complete unrestricted joint-limit event. -/
def JointGrowth : Prop :=
  ∃ μ : ℝ, μ ∈ Set.Icc 1 2 ∧ ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, 3 ≤ N ∧ ∀ m n : ℕ, N ≤ m → N ≤ n →
      |growth (count (grid m n)) m n - μ| < ε ∧
      |growth (count (cylinder m n)) m n - μ| < ε

private theorem count_mono {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} (h : G ≤ H) : count G ≤ count H := by
  classical
  apply card_le_card
  intro S hS
  apply mem_domSets.mpr
  intro x
  rcases (mem_domSets.mp hS) x with hx | ⟨y, hy, hxy⟩
  · exact Or.inl hx
  · exact Or.inr ⟨y, hy, h hxy⟩

/-- Repair by filling B, retaining S ∩ B to distinguish every fibre. -/
private theorem repair_count {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (B : Finset V)
    (outside : ∀ x, x ∉ B → ∀ y, H.Adj x y → G.Adj x y) :
    count H ≤ count G * 2 ^ B.card := by
  classical
  let repair : ↥(domSets H) → ↥(domSets G) × ↥(B.powerset) := fun S =>
    (⟨S.val ∪ B, mem_domSets.mpr (by
      intro x
      by_cases hx : x ∈ B
      · exact Or.inl (mem_union_right _ hx)
      · rcases (mem_domSets.mp S.property) x with hs | ⟨y, hy, hxy⟩
        · exact Or.inl (mem_union_left _ hs)
        · exact Or.inr ⟨y, mem_union_left _ hy, outside x hx y hxy⟩)⟩,
      ⟨S.val ∩ B, mem_powerset.mpr inter_subset_right⟩)
  have hinj : Function.Injective repair := by
    intro S T h
    have hu : S.val ∪ B = T.val ∪ B := congrArg (fun p => p.1.val) h
    have hi : S.val ∩ B = T.val ∩ B := congrArg (fun p => p.2.val) h
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ B
    · have hh := congrArg (fun U : Finset V => x ∈ U) hi
      simpa [hx] using hh
    · have hh := congrArg (fun U : Finset V => x ∈ U) hu
      simpa [hx] using hh
  have hh := Fintype.card_le_of_injective repair hinj
  simpa [count, Fintype.card_prod, Fintype.card_coe, card_powerset] using hh

private theorem cycle_interior {m : ℕ} (hm : 3 ≤ m) (x y : Fin m)
    (hx : x.val ≠ 0) (hl : x.val + 1 ≠ m) (h : (cycleGraph m).Adj x y) :
    (pathGraph m).Adj x y := by
  rw [cycleGraph_adj'] at h
  rw [pathGraph_adj]
  have hh : (x - y).val = (x.val + (m - y.val)) % m := rfl
  have hh' : (y - x).val = (y.val + (m - x.val)) % m := rfl
  rcases h with h | h
  · rw [hh] at h
    have hb := y.isLt
    have hb' := x.isLt
    have he : x.val + (m - y.val) < 2 * m := by omega
    have hp : x.val + (m - y.val) < m ∨ m ≤ x.val + (m - y.val) := by omega
    rcases hp with hp | hp
    · rw [Nat.mod_eq_of_lt hp] at h
      omega
    · rw [Nat.mod_eq_sub_mod hp, Nat.mod_eq_of_lt (by omega)] at h
      omega
  · rw [hh'] at h
    have hb := y.isLt
    have hb' := x.isLt
    have he : y.val + (m - x.val) < 2 * m := by omega
    by_cases hp : y.val + (m - x.val) < m
    · rw [Nat.mod_eq_of_lt hp] at h
      omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h
      omega

/-- Both endpoint columns; m≥3 keeps these two fibres disjoint. -/
def boundary (m n : ℕ) : Finset (Fin m × Fin n) :=
  univ.filter (fun x => x.1.val = 0 ∨ x.1.val + 1 = m)

private theorem boundary_card {m n : ℕ} (hm : 3 ≤ m) : (boundary m n).card = 2 * n := by
  classical
  let a : Fin m := ⟨0, by omega⟩
  let b : Fin m := ⟨m - 1, by omega⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; dsimp [a, b] at this; omega
  have he : boundary m n = ({a, b} : Finset (Fin m)) ×ˢ (univ : Finset (Fin n)) := by
    ext x
    simp [boundary, a, b, Fin.ext_iff]
    omega
  rw [he, card_product, card_pair hab, card_univ, Fintype.card_fin]

/-- Finite seam comparison for every source dimension, including m=3 and n=1. -/
theorem finite_seam_bound {m n : ℕ} (hm : 3 ≤ m) :
    count (grid m n) ≤ count (cylinder m n) ∧
    count (cylinder m n) ≤ count (grid m n) * 4 ^ n := by
  constructor
  · apply count_mono
    intro x y h
    rcases h with h | h
    · exact Or.inl ⟨pathGraph_le_cycleGraph h.1, h.2⟩
    · exact Or.inr h
  · have hh := repair_count (grid m n) (cylinder m n) (boundary m n) (by
      intro x hx y h
      have hx' : x.1.val ≠ 0 ∧ x.1.val + 1 ≠ m := by simpa [boundary] using hx
      rcases h with h | h
      · exact Or.inl ⟨cycle_interior hm x.1 y.1 hx'.1 hx'.2 h.1, h.2⟩
      · exact Or.inr h)
    rw [boundary_card hm] at hh
    have hp : 2 ^ (2 * n) = 4 ^ n := by rw [pow_mul]; rfl
    simpa only [hp] using hh

end D5.S3.Combinatorics.Graph.Domination.MertensGridGrowth
