/- GID: D5/S3/Quantum/Fibers/BipartiteBlockade/SmallSettingRecovery
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/BipartiteBlockade/SmallSettingRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Zero and one nonlinear open neighborhoods require at most zero and one actual acceleration settings. -/

import D5.S3.Quantum.Fibers.BipartiteBlockade.TwoColorReadout

attribute [local instance] LieRing.ofAssociativeRing
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators Classical Matrix
namespace D5.S3.Quantum.Fibers.BipartiteBlockade
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Distinct open neighborhoods with at least two vertices. -/
def nonlinearNeighborhoods (G : SimpleGraph V) : Finset (Finset V) :=
  (Finset.univ.filter fun v => 2 ≤ (G.neighborFinset v).card).image
    (fun v => G.neighborFinset v)

private theorem clear_disjoint (G : SimpleGraph V) (v : V) (S : Configuration G) :
    clear G v S ↔ Disjoint (G.neighborFinset v) S.val := by
  constructor
  · intro h
    rw [Finset.disjoint_left]
    intro u hu hS
    exact h u hS (by simpa using hu)
  · intro h u hu huv
    exact Finset.disjoint_left.mp h (by simpa using huv) hu

private theorem blockade_empty (G : SimpleGraph V) (v : V)
    (h : G.neighborFinset v = ∅) : blockade G v = 1 := by
  ext S T
  simp [blockade, clear_disjoint, h, Matrix.diagonal_apply, Matrix.one_apply]

private theorem blockade_singleton (G : SimpleGraph V) (v u : V)
    (h : G.neighborFinset v = {u}) : blockade G v = 1 - number G u := by
  ext S T
  by_cases he : S = T
  · subst T
    simp only [blockade, clear_disjoint, h, Finset.disjoint_singleton_left,
      Matrix.diagonal_apply_eq, Matrix.sub_apply, Matrix.one_apply_eq, number]
    by_cases hu : u ∈ S.val <;> simp [hu]
  · simp [blockade, number, Matrix.diagonal_apply, Matrix.one_apply, he]

private theorem small_vertex_recovery (G : SimpleGraph V)
    (ρ σ : Matrix (Configuration G) (Configuration G) ℂ)
    (htrace : (Matrix.trace ρ).re = (Matrix.trace σ).re)
    (hm : ∀ v, occupationMean G ρ v = occupationMean G σ v) (v : V)
    (hsmall : (G.neighborFinset v).card ≤ 1) : blockadeMean G ρ v = blockadeMean G σ v := by
  by_cases he : G.neighborFinset v = ∅
  · simpa [blockadeMean, blockade_empty G v he] using htrace
  · obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hN : G.neighborFinset v = {u} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      exact ⟨hu, fun w hw => Finset.card_le_one.mp hsmall w hw u hu⟩
    simp only [blockadeMean, blockade_singleton G v u hN, Matrix.mul_sub,
      Matrix.mul_one, Matrix.trace_sub, Complex.sub_re]
    exact congrArg₂ (· - ·) htrace (hm u)

private def colorSign (color : V → Bool) (v : V) : ℝ := if color v then 1 else -1

private def exchangeMean (G : SimpleGraph V)
    (ρ : Matrix (Configuration G) (Configuration G) ℂ) (u v : V) : ℝ :=
  (Matrix.trace (ρ * exchange G u v)).re

private theorem exchange_symmetric (G : SimpleGraph V)
    (ρ : Matrix (Configuration G) (Configuration G) ℂ) (u v : V) :
    exchangeMean G ρ u v = exchangeMean G ρ v u := by
  have he : exchange G u v = exchange G v u := by
    ext S T
    simp only [exchange, Finset.pair_comm]
  simp only [exchangeMean, he]

private theorem acceleration_expansion (G : SimpleGraph V) (Ω : V → ℝ)
    (ρ : Matrix (Configuration G) (Configuration G) ℂ) (v : V) :
    acceleration G Ω ρ v = -(2 * Ω v ^ 2 *
      (2 * occupationMean G ρ v - blockadeMean G ρ v) +
      ∑ u, if G.Adj u v then Ω u * Ω v * exchangeMean G ρ u v else 0) := by
  unfold acceleration
  rw [general_double_commutator]
  simp only [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  congr 1
  congr 1
  · simp [← Complex.ofReal_pow, Matrix.mul_smul, Matrix.mul_sub, Matrix.trace_smul, Matrix.trace_sub,
      Complex.mul_re, occupationMean, blockadeMean]
  · rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro u _
    by_cases ha : G.Adj u v
    · simp [ha, Matrix.mul_smul, Matrix.trace_smul, Complex.mul_re, exchangeMean]
    · simp [ha]

private theorem signed_conservation (G : SimpleGraph V) (color : V → Bool)
    (proper : ∀ u v, G.Adj u v → color u ≠ color v) (Ω : V → ℝ)
    (ρ : Matrix (Configuration G) (Configuration G) ℂ) :
    (∑ v, colorSign color v * (acceleration G Ω ρ v +
      4 * Ω v ^ 2 * occupationMean G ρ v)) =
      2 * ∑ v, colorSign color v * Ω v ^ 2 * blockadeMean G ρ v := by
  let f : V → V → ℝ := fun u v => if G.Adj u v then
    colorSign color v * Ω u * Ω v * exchangeMean G ρ u v else 0
  have hanti : ∀ u v, f u v = -f v u := by
    intro u v
    by_cases ha : G.Adj u v
    · have hs : colorSign color u = -colorSign color v := by
        have hc := proper u v ha
        cases hu : color u <;> cases hv : color v <;> simp_all [colorSign]
      simp only [f, ha, ha.symm, ite_true, hs, exchange_symmetric G ρ u v]
      ring
    · have hn : ¬G.Adj v u := fun h => ha h.symm
      simp [f, ha, hn]
  have hneg : (∑ v, ∑ u, f u v) = -(∑ v, ∑ u, f u v) := by
    calc
      (∑ v, ∑ u, f u v) = ∑ u, ∑ v, f u v := Finset.sum_comm
      _ = ∑ u, ∑ v, -f v u := by
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro v _
        exact hanti u v
      _ = -(∑ v, ∑ u, f u v) := by simp only [Finset.sum_neg_distrib]
  have hz : (∑ v, ∑ u, f u v) = 0 := by linarith
  have heach : ∀ v, colorSign color v * (acceleration G Ω ρ v +
      4 * Ω v ^ 2 * occupationMean G ρ v) =
      2 * (colorSign color v * Ω v ^ 2 * blockadeMean G ρ v) - ∑ u, f u v := by
    intro v
    have hf : (∑ u, f u v) = colorSign color v *
        ∑ u, if G.Adj u v then Ω u * Ω v * exchangeMean G ρ u v else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      by_cases ha : G.Adj u v
      · simp only [f, ha, ite_true]
        ring
      · simp [f, ha]
    rw [acceleration_expansion, hf]
    ring
  simp_rw [heach, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hz, sub_zero]

private theorem blockade_same_neighborhood (G : SimpleGraph V) (u v : V)
    (h : G.neighborFinset u = G.neighborFinset v) : blockade G u = blockade G v := by
  ext S T
  simp only [blockade, clear_disjoint, h]

private theorem class_coefficient_ne_zero (G : SimpleGraph V) (color : V → Bool)
    (proper : ∀ u v, G.Adj u v → color u ≠ color v) (Ω : V → ℝ)
    (nonzero : ∀ v, Ω v ≠ 0) (base : V)
    (large : 2 ≤ (G.neighborFinset base).card)
    (one : ∀ u v, 2 ≤ (G.neighborFinset u).card → 2 ≤ (G.neighborFinset v).card →
      G.neighborFinset u = G.neighborFinset v) :
    (∑ v, if 2 ≤ (G.neighborFinset v).card then colorSign color v * Ω v ^ 2 else 0) ≠ 0 := by
  have hne : (G.neighborFinset base).Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨w, hw⟩ := hne
  have hcolor : ∀ v, 2 ≤ (G.neighborFinset v).card → color v = color base := by
    intro v hv
    have hvw : G.Adj v w := by
      have hN := one base v large hv
      have hwv : w ∈ G.neighborFinset v := by rw [← hN]; exact hw
      simpa only [SimpleGraph.mem_neighborFinset] using hwv
    have hbw : G.Adj base w := by simpa using hw
    have hc₁ := proper v w hvw
    have hc₂ := proper base w hbw
    cases hv' : color v <;> cases hb' : color base <;> cases hw' : color w <;> simp_all
  have hf : (∑ v, if 2 ≤ (G.neighborFinset v).card then colorSign color v * Ω v ^ 2 else 0) =
      colorSign color base * ∑ v, if 2 ≤ (G.neighborFinset v).card then Ω v ^ 2 else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : 2 ≤ (G.neighborFinset v).card
    · simp only [hv, ite_true]
      rw [show colorSign color v = colorSign color base by
        simp only [colorSign, hcolor v hv]]
    · simp only [hv, ite_false, mul_zero]
  rw [hf]
  apply mul_ne_zero
  · cases hb : color base <;> norm_num [colorSign, hb]
  · apply ne_of_gt
    apply Finset.sum_pos'
    · intro v _; split_ifs <;> positivity
    · exact ⟨base, Finset.mem_univ _, by
        simpa only [large, ite_true] using sq_pos_of_ne_zero (nonzero base)⟩

/-- With no nonlinear neighborhood, means alone recover every blockade. With
at most one nonlinear neighborhood, any one nonzero drive recovers them from
means and actual double-commutator accelerations. The two matrices need only
have equal real trace; density matrices have this automatically. -/
theorem small_setting_recovery (G : SimpleGraph V) (color : V → Bool)
    (proper : ∀ u v, G.Adj u v → color u ≠ color v) (Ω : V → ℝ)
    (nonzero : ∀ v, Ω v ≠ 0) :
    (nonlinearNeighborhoods G = ∅ →
      ∀ ρ σ : Matrix (Configuration G) (Configuration G) ℂ,
      (Matrix.trace ρ).re = (Matrix.trace σ).re →
      (∀ v, occupationMean G ρ v = occupationMean G σ v) →
      ∀ v, blockadeMean G ρ v = blockadeMean G σ v) ∧
    ((nonlinearNeighborhoods G).card ≤ 1 →
      ∀ ρ σ : Matrix (Configuration G) (Configuration G) ℂ,
      (Matrix.trace ρ).re = (Matrix.trace σ).re →
      (∀ v, occupationMean G ρ v = occupationMean G σ v) →
      (∀ v, acceleration G Ω ρ v = acceleration G Ω σ v) →
      ∀ v, blockadeMean G ρ v = blockadeMean G σ v) := by
  have hmem : ∀ v, 2 ≤ (G.neighborFinset v).card → G.neighborFinset v ∈ nonlinearNeighborhoods G := by
    intro v hv
    exact Finset.mem_image.mpr ⟨v,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
  constructor
  · intro hn ρ σ ht hm v
    apply small_vertex_recovery G ρ σ ht hm v
    by_contra h
    have hv : 2 ≤ (G.neighborFinset v).card := by omega
    have := hmem v hv
    simpa [hn] using this
  · intro hone ρ σ ht hm ha
    have one : ∀ u v, 2 ≤ (G.neighborFinset u).card → 2 ≤ (G.neighborFinset v).card →
        G.neighborFinset u = G.neighborFinset v := by
      intro u v hu hv
      exact Finset.card_le_one.mp hone _ (hmem u hu) _ (hmem v hv)
    have hconρ := signed_conservation G color proper Ω ρ
    have hconσ := signed_conservation G color proper Ω σ
    have hleft : (∑ v, colorSign color v * (acceleration G Ω ρ v +
        4 * Ω v ^ 2 * occupationMean G ρ v)) =
        ∑ v, colorSign color v * (acceleration G Ω σ v +
          4 * Ω v ^ 2 * occupationMean G σ v) := by simp_rw [hm, ha]
    have hdelta : (∑ v, colorSign color v * Ω v ^ 2 *
        (blockadeMean G ρ v - blockadeMean G σ v)) = 0 := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      linarith
    intro v
    by_cases hv : 2 ≤ (G.neighborFinset v).card
    · have hfactor : (∑ u, colorSign color u * Ω u ^ 2 *
          (blockadeMean G ρ u - blockadeMean G σ u)) =
          (blockadeMean G ρ v - blockadeMean G σ v) *
            ∑ u, if 2 ≤ (G.neighborFinset u).card then colorSign color u * Ω u ^ 2 else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        by_cases hu : 2 ≤ (G.neighborFinset u).card
        · have hb := blockade_same_neighborhood G u v (one u v hu hv)
          simp only [hu, ite_true, blockadeMean, hb]
          ring
        · have hs : (G.neighborFinset u).card ≤ 1 := by omega
          rw [small_vertex_recovery G ρ σ ht hm u hs]
          simp only [hu, ite_false, sub_self, mul_zero]
      have hprod := hfactor.symm.trans hdelta
      have hc := class_coefficient_ne_zero G color proper Ω nonzero v hv one
      exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hc)
    · exact small_vertex_recovery G ρ σ ht hm v (by omega)

/-- info: 'D5.S3.Quantum.Fibers.BipartiteBlockade.small_setting_recovery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms small_setting_recovery
end D5.S3.Quantum.Fibers.BipartiteBlockade
