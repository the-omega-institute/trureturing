/- GID: D5/S3/Topology/RankedCofaceContiguity
   generality: G
   mirror-B: D5/B/S3/Topology/RankedCofaceContiguity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.Preorder.Chain]
   utility: none
   digest: A ranked coface comparison gives relative contiguity to a simplicial map that may reverse comparable pairs. -/

module

public import D5.S3.Topology.DescendingClosureContiguity
import Mathlib.Tactic
import OmegaBuild.Commands

/-! For the triangle-cone step of Mosquera-Lois–Tanaka Question 6.3, a
coface selection is simplicial on the selected region. Its comparison map can
reverse individual comparable pairs. A descending rank order suffices to
interpolate from the ordinary retraction. -/

compile_only_with_mathlib

public section

set_option autoImplicit false

namespace D5.S3.Topology.RankedCofaceContiguity

variable {P Q : Type*} [Preorder P] [Preorder Q]

/-- A pointwise enlargement of an order map gives a relative contiguity
chain when the enlarged map sends each chain to a chain. Change the
vertices in decreasing rank and keep the agreement locus fixed. -/
theorem exists_relative_contiguity_of_chain_map
    (rank : P → ℕ) (hrank : StrictMono rank)
    (bound : ℕ) (hbound : ∀ x, rank x ≤ bound)
    (f : P →o Q) (g : P → Q) (hle : ∀ x, f x ≤ g x)
    (hchain : ∀ ⦃x y⦄, x ≤ y → g x ≤ g y ∨ g y ≤ g x) :
    ∃ F : ℕ → P → Q,
      F 0 = f ∧ F (bound + 1) = g ∧
      (∀ k x, g x = f x → F k x = f x) ∧
      ∀ k (s : Set P), IsChain (· ≤ ·) s → IsChain (· ≤ ·) (F k '' s ∪ F (k + 1) '' s) := by
  let turn (x : P) := bound - rank x
  let F (k : ℕ) (x : P) := if turn x < k then g x else f x
  have hturn {x y : P} (hxy : x < y) : turn y < turn x := by
    have hlt := hrank hxy
    have hb := hbound y
    dsimp [turn]
    omega
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · funext x
    simp [F]
  · funext x
    have h : turn x < bound + 1 := Nat.lt_succ_of_le (Nat.sub_le _ _)
    simp [F, h]
  · intro k x hx
    simp [F, hx]
  intro k s hs
  have ordered {x y : P} (hx : x ∈ s) (hy : y ∈ s) : x ≤ y ∨ y ≤ x := by
    by_cases he : x = y
    · exact Or.inl he.le
    · exact hs hx hy he
  have old_new {i j : ℕ} {x y : P} (hx : x ∈ s) (hy : y ∈ s)
      (hxold : ¬ turn x < i) (hynew : turn y < j) (hji : j ≤ i + 1) :
      f x ≤ g y := by
    have hxy : x ≤ y := by
      rcases ordered hx hy with h | h
      · exact h
      · by_contra hn
        have hh := hturn (lt_of_le_not_ge h hn)
        omega
    exact (f.monotone hxy).trans (hle y)
  have compare (i j : ℕ) (hij : i ≤ j + 1) (hji : j ≤ i + 1)
      {x y : P} (hx : x ∈ s) (hy : y ∈ s) : F i x ≤ F j y ∨ F j y ≤ F i x := by
    by_cases hxi : turn x < i <;> by_cases hyj : turn y < j
    · rcases ordered hx hy with h | h
      · simpa only [F, if_pos hxi, if_pos hyj] using hchain h
      · simpa only [F, if_pos hxi, if_pos hyj] using (hchain h).symm
    · exact Or.inr (by simpa only [F, if_pos hxi, if_neg hyj] using old_new hy hx hyj hxi hij)
    · exact Or.inl (by simpa only [F, if_neg hxi, if_pos hyj] using old_new hx hy hxi hyj hji)
    · rcases ordered hx hy with h | h
      · exact Or.inl (by simpa only [F, if_neg hxi, if_neg hyj] using f.monotone h)
      · exact Or.inr (by simpa only [F, if_neg hxi, if_neg hyj] using f.monotone h)
  intro a ha b hb _
  rcases ha with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ <;>
    rcases hb with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ <;>
    exact compare _ _ (by omega) (by omega) hx hy

end D5.S3.Topology.RankedCofaceContiguity
