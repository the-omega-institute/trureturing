/- GID: D5/S3/Combinatorics/DihedralRamsey/NestedMetricColouring
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/NestedMetricColouring
   mirror-E: none(waiver:metric-predecessor-colourings)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: none
   digest: Metric colourings give regular short graphs and matching-avoiding complements. -/

import Mathlib.Combinatorics.SimpleGraph.Finite
import D5.S3.Combinatorics.DihedralRamsey.NestedMetric
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyCircularDegree
import D5.S3.Combinatorics.DihedralRamsey.NestedMatching

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.NestedMetricColouring

open CyclicRamseyDefs NestedRamseyDefs NestedMatching NestedMetric

/-- Even short thresholds and far gaps yield the metric predecessor colourings. -/
theorem metric_colouring {n t : ℕ} (hn : 2 * t < n) :
    ∃ G : SimpleGraph (Fin n),
      (∀ x y, G.Adj x y ↔ x ≠ y ∧
        (Nat.dist x.val y.val ≤ t ∨ n - Nat.dist x.val y.val ≤ t)) ∧
      (letI := Classical.propDecidable; ∀ x, G.degree x = 2 * t) ∧
      (t % 2 = 0 → ¬CyclicEmbeddable (nestMatching (2 * (t + 1))) G) ∧
      (∀ k, 0 < k → n < 2 * k + 2 * t →
        ¬CyclicEmbeddable (nestMatching (2 * k)) Gᶜ) := by
  classical
  let G : SimpleGraph (Fin n) := SimpleGraph.fromRel fun x y =>
    Nat.dist x.val y.val ≤ t ∨ n - Nat.dist x.val y.val ≤ t
  have hadj : ∀ x y, G.Adj x y ↔ x ≠ y ∧
      (Nat.dist x.val y.val ≤ t ∨ n - Nat.dist x.val y.val ≤ t) := by
    intro x y
    simp only [G, SimpleGraph.fromRel_adj, Nat.dist_comm y.val x.val, or_self]
  refine ⟨G, hadj, ?_, ?_, ?_⟩
  · exact short_circular_degree hn G hadj
  · intro ht hcopy
    obtain ⟨ψ, hψ, c, hc, he⟩ :=
      (cyclic_iff_reflection (by omega) (by omega) G).mp hcopy
    have h := (reflection_metric_bounds (by omega) ψ hψ c hc).1 t (by omega)
      (fun i j hij => ((hadj _ _).mp (he i j hij)).2)
    omega
  · intro k hk hnk hcopy
    obtain ⟨ψ, hψ, c, hc, he⟩ :=
      (cyclic_iff_reflection (by omega) (by omega) Gᶜ).mp hcopy
    have h := (reflection_metric_bounds hk ψ hψ c hc).2 (t + 1) (by
      intro i j hij
      have hedge := (SimpleGraph.compl_adj _ _ _).mp (he i j hij)
      have hfar : ¬(Nat.dist (ψ i).val (ψ j).val ≤ t ∨
          n - Nat.dist (ψ i).val (ψ j).val ≤ t) := by
        intro hshort
        exact hedge.2 ((hadj _ _).mpr ⟨hedge.1, hshort⟩)
      omega)
    omega

/-- The three parity cases have colourings on the predicted predecessor order. -/
theorem star_predecessor {k b : ℕ} (hk : 0 < k) (hb : 2 ≤ b) :
    ∃ G : SimpleGraph
      (Fin (if k % 2 = 0 ∧ b % 2 = 1 then 2 * k + b - 4 else 2 * k + b - 3)),
      letI := Classical.propDecidable
      ¬CyclicEmbeddable (nestMatching (2 * k)) G ∧ ∀ x, Gᶜ.degree x ≤ b - 2 := by
  classical
  by_cases hkodd : k % 2 = 1
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    have hcase : ¬((r + 1) % 2 = 0 ∧ b % 2 = 1) := by omega
    rw [if_neg hcase]
    obtain ⟨G, _, hdeg, havoid, _⟩ :=
      metric_colouring (n := 2 * (r + 1) + b - 3) (t := r) (by omega)
    refine ⟨G, havoid (by omega), ?_⟩
    intro x
    have hg : G.degree x = 2 * r := by
      convert hdeg x using 1
      unfold SimpleGraph.degree
      congr 1
    have hcomp := G.degree_compl x
    simp only [Fintype.card_fin] at hcomp
    have hh : Gᶜ.degree x ≤ b - 2 := by omega
    convert hh using 1
    unfold SimpleGraph.degree
    congr 1
    ext y
    simp
  · have hkeven : k % 2 = 0 := by omega
    by_cases hbodd : b % 2 = 1
    · rw [if_pos ⟨hkeven, hbodd⟩]
      obtain ⟨G, _, hdeg, _, havoid⟩ :=
        metric_colouring (n := 2 * k + b - 4) (t := (b - 3) / 2) (by omega)
      refine ⟨Gᶜ, havoid k hk (by omega), ?_⟩
      intro x
      rw [compl_compl]
      have hg := hdeg x
      omega
    · have hcase : ¬(k % 2 = 0 ∧ b % 2 = 1) := by omega
      rw [if_neg hcase]
      obtain ⟨G, _, hdeg, _, havoid⟩ :=
        metric_colouring (n := 2 * k + b - 3) (t := b / 2 - 1) (by omega)
      refine ⟨Gᶜ, havoid k hk (by omega), ?_⟩
      intro x
      rw [compl_compl]
      have hg := hdeg x
      omega

end D5.S3.Combinatorics.DihedralRamsey.NestedMetricColouring
