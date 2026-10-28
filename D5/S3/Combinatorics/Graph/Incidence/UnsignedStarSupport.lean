/- GID: D5/S3/Combinatorics/Graph/Incidence/UnsignedStarSupport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Incidence/UnsignedStarSupport
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact support of unsigned integer star representatives and indexed maximum cuts. -/

import D5.S3.Combinatorics.Graph.Incidence.UnsignedStarTorsion
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Max

/-!
Admission basis: escape-witness, fixed before compilation.
The missing inference is the odd-sign cut for every unrestricted integer
potential, followed by the converse total two-color construction. It yields
an attained exact support minimum equal to indexed edge bipartization and
the complement of a maximum cut. No connectedness, finiteness, or supplied
color certificate is assumed in the support criterion. Finiteness enters
only the simultaneous extremum theorem. Every parallel original ID counts.
Private normalization and coloring helpers are consumed by these proofs.
Utility none: symbolic unbounded mathematics, not a finite census, checker,
numerical reduction, or certified instance. No algorithm or complexity claim.
Guidance: caller-supplied unsigned-incidence proof Sections 3-4, SHA256
c514b03ad862efd9a78b7509fa1b19e606f89a7bdf278e7ecfb8eed84192be9f.
No full torsion decomposition, equivariant splitting, Good, or AM claim.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Incidence.UnsignedStarSupport

open UnsignedStarTorsion

variable {V X : Type*} (g : Edges V X)

/-- Actual integer representatives of the all-original-edge indicator class. -/
def representative (b : V → ℤ) : X → ℤ := fun i => 1 + g.starMap b i

/-- Crossing original edge IDs, with all parallel indices retained. -/
def cutEdges (c : V → Bool) : Set X := {i | c (g.left i) ≠ c (g.right i)}

/-- The integer potential associated with a total Boolean partition. -/
def colorPotential (c : V → Bool) : V → ℤ := fun v => if c v then -1 else 0

theorem color_support (c : V → Bool) :
    Function.support (representative g (colorPotential c)) = (cutEdges g c)ᶜ := by
  ext i
  cases hl : c (g.left i) <;> cases hr : c (g.right i) <;>
    simp [Function.support, representative, Edges.starMap, colorPotential, cutEdges, hl, hr]

theorem color_bounds (c : V → Bool) :
    (∀ v, colorPotential c v = 0 ∨ colorPotential c v = -1) ∧
    (∀ i, representative g (colorPotential c) i = -1 ∨
      representative g (colorPotential c) i = 0 ∨
      representative g (colorPotential c) i = 1) := by
  constructor
  · intro v
    cases h : c v <;> simp [colorPotential, h]
  · intro i
    cases hl : c (g.left i) <;> cases hr : c (g.right i) <;>
      simp [representative, Edges.starMap, colorPotential, hl, hr]

/-- The nonzero odd spin 2*b+1 provides a cut whose uncut edges lie in
support, even for unrestricted integer coefficients and infinite types.
The explicit sign witness respects equal potential values; this is consumed
by invariant support compression. -/
theorem odd_sign_cut (b : V → ℤ) :
    ∃ c : V → Bool, (∀ v w, b v = b w → c v = c w) ∧
      (cutEdges g c)ᶜ ⊆ Function.support (representative g b) := by
  classical
  let a : V → ℤ := fun v => 2 * b v + 1
  have ha (v : V) : a v ≠ 0 := by dsimp [a]; omega
  refine ⟨fun v => decide (0 < a v), ?_, ?_⟩
  · intro v w hvw
    simp only [a, hvw]
  · intro i hi hz
    have he : a (g.left i) + a (g.right i) = 0 := by
      change 1 + (b (g.left i) + b (g.right i)) = 0 at hz
      dsimp [a]
      omega
    have hl := ha (g.left i)
    have hr := ha (g.right i)
    change ¬ (decide (0 < a (g.left i)) ≠ decide (0 < a (g.right i))) at hi
    by_cases h₁ : 0 < a (g.left i) <;> by_cases h₂ : 0 < a (g.right i) <;>
      simp [h₁, h₂] at hi <;> omega

private theorem cut_of_bipartite (D : Set X)
    (hD : (g.graphAfterDeleting D).IsBipartite) :
    ∃ c : V → Bool, (cutEdges g c)ᶜ ⊆ D := by
  classical
  obtain ⟨s, t, hst⟩ := hD.exists_isBipartiteWith
  refine ⟨fun v => decide (v ∈ s), ?_⟩
  intro i hi
  by_contra hnot
  have hadj : (g.graphAfterDeleting D).Adj (g.left i) (g.right i) :=
    ⟨i, hnot, Or.inl ⟨rfl, rfl⟩⟩
  rcases hst.mem_of_adj hadj with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · have hr' : g.right i ∉ s := fun h => Set.disjoint_left.mp hst.disjoint h hr
    simpa [cutEdges, hl, hr'] using hi
  · have hl' : g.left i ∉ s := fun h => Set.disjoint_left.mp hst.disjoint h hl
    simpa [cutEdges, hl', hr] using hi

private theorem bipartite_of_cut (D : Set X) (c : V → Bool)
    (hD : (cutEdges g c)ᶜ ⊆ D) : (g.graphAfterDeleting D).IsBipartite := by
  apply SimpleGraph.IsBipartiteWith.isBipartite
    (s := {v | c v = true}) (t := {v | c v = false})
  constructor
  · exact Set.disjoint_left.mpr (fun v ht hf => by simp_all)
  · rintro u v ⟨i, hi, h | h⟩
    all_goals
      have hc : c (g.left i) ≠ c (g.right i) := by
        intro he
        exact hi (hD (by simpa [cutEdges] using he))
      rw [h.1, h.2] at hc
      cases hu : c u <;> cases hv : c v <;> simp_all

/-- Bipartiteness after deletion constructs a bounded actual integer
potential and a representative in {-1,0,1} supported on those deleted IDs. -/
theorem bounded_support_of_bipartite (D : Set X)
    (hD : (g.graphAfterDeleting D).IsBipartite) :
    ∃ b : V → ℤ, (∀ v, b v = 0 ∨ b v = -1) ∧
      (∀ i, representative g b i = -1 ∨ representative g b i = 0 ∨
        representative g b i = 1) ∧
      Function.support (representative g b) ⊆ D := by
  obtain ⟨c, hc⟩ := cut_of_bipartite g D hD
  exact ⟨colorPotential c, (color_bounds g c).1, (color_bounds g c).2,
    by rwa [color_support g c]⟩

/-- An arbitrary deletion contains the support of an integer representative
of the full indicator exactly when the remaining graph is bipartite. -/
theorem support_subset_iff_bipartite (D : Set X) :
    (∃ b : V → ℤ, Function.support (representative g b) ⊆ D) ↔
      (g.graphAfterDeleting D).IsBipartite := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨c, _, hc⟩ := odd_sign_cut g b
    exact bipartite_of_cut g D c (hc.trans hb)
  · intro hD
    obtain ⟨b, _, _, hb⟩ := bounded_support_of_bipartite g D hD
    exact ⟨b, hb⟩

/-- A maximum total Boolean cut simultaneously attains the least support
among ALL integer potentials and the least original-ID deletion making the
graph bipartite. Their common value is |X| minus that maximum cut size. -/
theorem attained_support_bipartization_maxcut [Fintype V] [Fintype X] :
    ∃ c : V → Bool,
      (∀ v, colorPotential c v = 0 ∨ colorPotential c v = -1) ∧
      (∀ i, representative g (colorPotential c) i = -1 ∨
        representative g (colorPotential c) i = 0 ∨
        representative g (colorPotential c) i = 1) ∧
      IsLeast {n : ℕ | ∃ b : V → ℤ,
        (Function.support (representative g b)).ncard = n}
        (Function.support (representative g (colorPotential c))).ncard ∧
      IsLeast {n : ℕ | ∃ D : Set X, (g.graphAfterDeleting D).IsBipartite ∧ D.ncard = n}
        (Function.support (representative g (colorPotential c))).ncard ∧
      IsGreatest {n : ℕ | ∃ d : V → Bool, (cutEdges g d).ncard = n}
        (cutEdges g c).ncard ∧
      (Function.support (representative g (colorPotential c))).ncard =
        Fintype.card X - (cutEdges g c).ncard := by
  classical
  obtain ⟨c, _, hc⟩ := Finset.exists_max_image
    (Finset.univ : Finset (V → Bool)) (fun d => (cutEdges g d).ncard) Finset.univ_nonempty
  have hmax (d : V → Bool) : (cutEdges g d).ncard ≤ (cutEdges g c).ncard :=
    hc d (Finset.mem_univ d)
  have hcomp (d : V → Bool) : (cutEdges g d)ᶜ.ncard =
      Fintype.card X - (cutEdges g d).ncard := by
    simpa only [Nat.card_eq_fintype_card] using Set.ncard_compl (cutEdges g d)
  have hmin (b : V → ℤ) :
      (Function.support (representative g (colorPotential c))).ncard ≤
        (Function.support (representative g b)).ncard := by
    obtain ⟨d, _, hd⟩ := odd_sign_cut g b
    rw [color_support g c, hcomp c]
    calc
      Fintype.card X - (cutEdges g c).ncard ≤
          Fintype.card X - (cutEdges g d).ncard := Nat.sub_le_sub_left (hmax d) _
      _ = (cutEdges g d)ᶜ.ncard := (hcomp d).symm
      _ ≤ (Function.support (representative g b)).ncard := Set.ncard_mono hd
  refine ⟨c, (color_bounds g c).1, (color_bounds g c).2,
    ⟨⟨colorPotential c, rfl⟩, ?_⟩, ⟨?_, ?_⟩, ⟨⟨c, rfl⟩, ?_⟩, ?_⟩
  · rintro n ⟨b, rfl⟩
    exact hmin b
  · refine ⟨Function.support (representative g (colorPotential c)), ?_, rfl⟩
    exact (support_subset_iff_bipartite g _).mp ⟨colorPotential c, Set.Subset.rfl⟩
  · rintro n ⟨D, hD, rfl⟩
    obtain ⟨b, _, _, hb⟩ := bounded_support_of_bipartite g D hD
    exact (hmin b).trans (Set.ncard_mono hb)
  · rintro n ⟨d, rfl⟩
    exact hmax d
  · rw [color_support g c, hcomp c]

end D5.S3.Combinatorics.Graph.Incidence.UnsignedStarSupport
