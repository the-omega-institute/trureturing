/- GID: D5/S3/Combinatorics/TotalRoman/DiameterTwoMetric
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TotalRoman/DiameterTwoMetric
   mirror-E: none(waiver:explicit-clique-expansion)
   anchors: []
   utility: none
   digest: Every clique expansion is connected and has diameter exactly two. -/

import D5.S3.Combinatorics.TotalRoman.DiameterTwoConstruction

set_option autoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Combinatorics.TotalRoman.DiameterTwoMetric

open DiameterTwoConstruction

set_option maxHeartbeats 2000000 in
-- The proof-local seed path certificate evaluates all pairs of ten base vertices.
/-- Paths through seed representatives preserve the diameter under clique expansion. -/
theorem metric {n : ℕ} (hn : 10 ≤ n) :
    (family n).Connected ∧ (family n).diam = 2 ∧
      ∃ u v, u ≠ v ∧ ¬ (family n).Adj u v := by
  classical
  let : Nonempty (Fin n) := ⟨Fin.castLE hn 0⟩
  have hc : ∀ i j : Fin 10, i = j ∨ seed.Adj i j ∨
      ∃ k : Fin 10, seed.Adj i k ∧ seed.Adj k j := by decide
  have hb : ∀ x y : Fin n, (family n).edist x y ≤ 2 := by
    intro x y
    by_cases he : x = y
    · subst y
      simp
    rcases hc (project x) (project y) with hp | hp | ⟨k, hxk, hky⟩
    · have ha : (family n).Adj x y := ⟨he, Or.inl hp⟩
      rw [SimpleGraph.edist_eq_one_iff_adj.mpr ha]
      decide
    · have ha := lift_adj hp
      rw [SimpleGraph.edist_eq_one_iff_adj.mpr ha]
      decide
    · have hx : (family n).Adj x (Fin.castLE hn k) :=
        lift_adj (by simpa only [project_rep] using hxk)
      have hy : (family n).Adj (Fin.castLE hn k) y :=
        lift_adj (by simpa only [project_rep] using hky)
      have hw := (SimpleGraph.Walk.cons hx (SimpleGraph.Walk.cons hy .nil)).edist_le
      simpa using hw
  have hd : (family n).ediam ≤ 2 := SimpleGraph.ediam_le_of_edist_le hb
  have ht : (family n).ediam ≠ ⊤ := by
    intro ht
    simp [ht] at hd
  have hconn := (family n).connected_of_ediam_ne_top ht
  have hup : (family n).diam ≤ 2 := by
    exact ENat.toNat_le_toNat hd (by simp)
  have hne : Fin.castLE hn 0 ≠ Fin.castLE hn 4 := by simp
  have hna : ¬ (family n).Adj (Fin.castLE hn 0) (Fin.castLE hn 4) := by
    change ¬ (_ ∧ (_ ∨ _))
    simp only [project_rep]
    rintro ⟨_, he | ha⟩
    · exact (by decide : (0 : Fin 10) ≠ 4) he
    · exact (by decide : ¬ seed.Adj 0 4) ha
  have hlo := hconn.one_lt_dist_of_ne_of_not_adj hne hna
  have hdist := (family n).dist_le_diam ht (u := Fin.castLE hn 0) (v := Fin.castLE hn 4)
  exact ⟨hconn, by omega, Fin.castLE hn 0, Fin.castLE hn 4, hne, hna⟩

end D5.S3.Combinatorics.TotalRoman.DiameterTwoMetric
