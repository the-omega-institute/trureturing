/- GID: D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/DomiRankEntropyRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.claim; result=D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.result; claim=D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.claim
   digest: DomiRank entropy monotonicity is refuted with whole-interval clone certificates. -/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import D5.S3.Entropy.MaxEntropy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix Finset

namespace D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation

/-!
Zhang and Zhao, arXiv:2610.00107v1, Remark 4.6, explicitly pose unconditional entropy
decrease for connected nonregular graphs as an open problem. The separate star-minimum
Conjecture 4.7 is excluded. The source identifier and displayed submission date disagree;
the exact identifier and version are retained without repairing that chronology. Bounded
literature and citation checks found no settlement, with unavailable search surfaces recorded
in the source qualification; this gives no global priority guarantee.

The sole public result negates the original graph claim. General covariance, the positive
pair, every pair in the interval of radius 1/5000000, and all independent-clone certificates
are proved locally. Zero is used only for the rational normalized inverse extension: the
source clipped normalization of Gamma at zero is not this extension. The cubic C below is
a reduced coordinate denominator, not an asserted adjacency determinant.
-/

def Nonregular {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj] : Prop := ∃ u v, (∑ w, if G.Adj u w then (1 : ℕ) else 0) ≠
    ∑ w, if G.Adj v w then (1 : ℕ) else 0

def clipped {W : Type*} (p : W → ℝ) : W → ℝ := fun i => max (p i) 0

noncomputable def normalized {W : Type*} [Fintype W] (p : W → ℝ) : W → ℝ := fun i => clipped p i / ∑ j, clipped p j

noncomputable def entropyBits {W : Type*} [Fintype W] (p : W → ℝ) : ℝ := D5.S3.Entropy.MaxEntropy.shannonEntropy p / Real.log 2

noncomputable def spectralMinimum {W : Type*} [Fintype W] (G : SimpleGraph W) [DecidableRel G.Adj] : ℝ := by
  classical
  by_cases h : Nonempty W
  · letI := h
    exact Finset.univ.inf' Finset.univ_nonempty (G.isHermitian_adjMatrix ℝ).eigenvalues
  · exact 0

noncomputable def graphAdj {W : Type*} [Fintype W] (G : SimpleGraph W) [DecidableRel G.Adj] : Matrix W W ℝ := G.adjMatrix ℝ

noncomputable def graphDegrees {W : Type*} [Fintype W] (G : SimpleGraph W) [DecidableRel G.Adj] : W → ℝ := graphAdj G *ᵥ (fun _ => 1)

noncomputable def graphGamma {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj] (s : ℝ) : W → ℝ := by
  classical
  exact s • ((1 + s • graphAdj G)⁻¹ *ᵥ graphDegrees G)

noncomputable def graphEntropyBits {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj] (s : ℝ) : ℝ :=
  entropyBits (normalized (graphGamma G s))

def claim : Prop := ∀ (n : ℕ), 0 < n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.Connected → Nonregular G → ∀ σ τ : ℝ, 0 < σ → σ < -1 / spectralMinimum G →
      0 < τ → τ < -1 / spectralMinimum G → σ < τ → graphEntropyBits G τ ≤ graphEntropyBits G σ

open scoped Matrix.Norms.Operator

set_option maxHeartbeats 3000000 in
theorem result : ¬ claim := by
  classical
  let sourceGraph : SimpleGraph (Fin 6) := {
    Adj := fun u v =>
      (u = 0 ∧ v = 4) ∨ (u = 4 ∧ v = 0) ∨ (u = 0 ∧ v = 5) ∨ (u = 5 ∧ v = 0) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) ∨ (u = 1 ∧ v = 3) ∨ (u = 3 ∧ v = 1) ∨
      (u = 1 ∧ v = 4) ∨ (u = 4 ∧ v = 1) ∨ (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2) ∨ (u = 2 ∧ v = 4) ∨ (u = 4 ∧ v = 2)
    symm := by
      constructor
      aesop
    loopless := ⟨by decide⟩ }
  letI local_decidable_1 : DecidableRel sourceGraph.Adj := by
    intro u v; unfold sourceGraph; infer_instance
  let A : Matrix (Fin 6) (Fin 6) ℝ := sourceGraph.adjMatrix ℝ
  let degrees : (Fin 6) → ℝ := ![2, 3, 3, 2, 3, 1]
  let ones : (Fin 6) → ℝ := fun _ => 1
  have adjacency_formula : A = !![ 0,0,0,0,1,1; 0,0,1,1,1,0; 0,1,0,1,1,0; 0,1,1,0,0,0; 1,1,1,0,0,0; 1,0,0,0,0,0] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [A, sourceGraph, SimpleGraph.adjMatrix]
  have degree_formula : A *ᵥ ones = degrees := by
    rw [adjacency_formula]; funext i; fin_cases i <;> norm_num [Matrix.mulVec, degrees, ones, Fin.sum_univ_succ,
      Matrix.one_apply, vecHead, vecTail, cons_val_one, cons_val_two, cons_val_three, cons_val_four]
  have source_connected : sourceGraph.Connected := by
    refine (SimpleGraph.connected_iff_exists_forall_reachable sourceGraph).2 ⟨0, ?_⟩; intro w; fin_cases w
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons' (G := sourceGraph) 0 4 1 (by decide) (SimpleGraph.Walk.cons' (G := sourceGraph) 4 1 1 (by decide) SimpleGraph.Walk.nil)⟩
    · exact ⟨SimpleGraph.Walk.cons' (G := sourceGraph) 0 4 2 (by decide) (SimpleGraph.Walk.cons' (G := sourceGraph) 4 2 2 (by decide) SimpleGraph.Walk.nil)⟩
    · exact ⟨SimpleGraph.Walk.cons' (G := sourceGraph) 0 4 3 (by decide) (SimpleGraph.Walk.cons' (G := sourceGraph) 4 1 3 (by decide)
          (SimpleGraph.Walk.cons' (G := sourceGraph) 1 3 3 (by decide) SimpleGraph.Walk.nil))⟩
    · exact ⟨SimpleGraph.Walk.cons' (G := sourceGraph) 0 4 4 (by decide) SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons' (G := sourceGraph) 0 5 5 (by decide) SimpleGraph.Walk.nil⟩
  have source_nonregular : Nonregular sourceGraph := by exact ⟨0, 5, by decide⟩
  let B (s : ℝ) : Matrix (Fin 6) (Fin 6) ℝ := 1 + s • A
  have B_formula (s : ℝ) : B s = !![ 1,0,0,0,s,s; 0,1,s,s,s,0; 0,s,1,s,s,0; 0,s,s,1,0,0; s,s,s,0,1,0; s,0,0,0,0,1] := by
    dsimp only [B]; rw [adjacency_formula]; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.one_apply, vecHead, vecTail, cons_val_one, cons_val_two, cons_val_three, cons_val_four]
      <;> ring
  let C (s : ℝ) : ℝ := 1 + 2*s - 4*s^2 - 6*s^3
  let N (s : ℝ) : (Fin 6) → ℝ := fun i => match i.val with
    | 0 => 2 - 6*s^2
    | 1 => 3 - 2*s - 6*s^2
    | 2 => 3 - 2*s - 6*s^2
    | 3 => 2 - 2*s - 4*s^2
    | 4 => 3 - 2*s - 8*s^2
    | _ => 1 - 4*s^2
  let T (s : ℝ) : ℝ := 14 - 8*s - 34*s^2
  have direct_coordinate_certificate (s : ℝ) : B s *ᵥ N s = C s • degrees ∧ ∑ i, N s i = T s := by
    constructor
    · rw [B_formula]
      funext i; fin_cases i <;>
        norm_num [B, N, C, degrees, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
          Matrix.one_apply, vecHead, vecTail, cons_val_one, cons_val_two, cons_val_three, cons_val_four] <;>
        ring
    · simp [N, T, Fin.sum_univ_succ]
      ring
  have C_pos_small {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 100) : 0 < C s := by
    dsimp [C]; nlinarith [sq_nonneg s]
  have N_pos_small {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 100) : ∀ i, 0 < N s i := by
    intro i; fin_cases i <;> simp [N] <;> nlinarith [sq_nonneg s]
  have T_pos_small {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 100) : 0 < T s := by
    dsimp [T]; nlinarith [sq_nonneg s]
  let sourceGamma (s : ℝ) : (Fin 6) → ℝ := s • ((B s)⁻¹ *ᵥ degrees)
  let explicitGamma (s : ℝ) : (Fin 6) → ℝ := (s / C s) • N s
  have gamma_pair : explicitGamma (1 / 20) = (1 / 4357 : ℝ) • ![(397 : ℝ),577,577,378,576,198] ∧
      explicitGamma (1 / 6) = (1 / 129 : ℝ) • ![(33 : ℝ),45,45,28,44,16] := by
    constructor
    · ext i
      fin_cases i <;> norm_num [explicitGamma, N, C]
    · ext i
      fin_cases i <;> norm_num [explicitGamma, N, C]
  have pair_probability_certificate : normalized (explicitGamma (1 / 20)) = (1 / 2703 : ℝ) • ![(397 : ℝ),577,577,378,576,198] ∧
      normalized (explicitGamma (1 / 6)) = (1 / 211 : ℝ) • ![(33 : ℝ),45,45,28,44,16] := by
    rcases gamma_pair with ⟨h20, h6⟩
    constructor
    · rw [h20]
      have hs : ∀ i, 0 ≤ ((1 / 4357 : ℝ) • ![(397 : ℝ),577,577,378,576,198]) i := by intro i; fin_cases i <;> norm_num
      ext i; fin_cases i <;> norm_num [normalized, clipped, Fin.sum_univ_succ]
    · rw [h6]
      have hs : ∀ i, 0 ≤ ((1 / 129 : ℝ) • ![(33 : ℝ),45,45,28,44,16]) i := by intro i; fin_cases i <;> norm_num
      ext i; fin_cases i <;> norm_num [normalized, clipped, Fin.sum_univ_succ]
  have covariance_certificate :
      let d : (Fin 6) → ℝ := degrees
      let q : (Fin 6) → ℝ := A *ᵥ d
      let D : ℝ := ∑ i, d i
      let Q : ℝ := ∑ i, q i
      D = 14 ∧ q = ![(4 : ℝ),8,8,6,8,2] ∧ Q = 36 ∧ (∀ i, (Q * d i - D * q i) / D^2 = ((![ (4 : ℝ),-1,-1,-3,-1,2] : (Fin 6) → ℝ) i) / 49) := by
    dsimp
    have hq : A *ᵥ degrees = ![(4 : ℝ),8,8,6,8,2] := by
      rw [adjacency_formula]; funext i; simp [degrees]
      fin_cases i <;> norm_num [Matrix.mulVec, Fin.sum_univ_succ, vecHead, vecTail, cons_val_one, cons_val_two, cons_val_three, cons_val_four]
    refine ⟨?_, hq, ?_, ?_⟩
    · norm_num [degrees, Fin.sum_univ_succ, vecHead, vecTail, cons_val_one, cons_val_two, cons_val_three, cons_val_four]
    · rw [hq]
      norm_num [Fin.sum_univ_succ, vecHead, vecTail, cons_val_one, cons_val_two, cons_val_three, cons_val_four]
    · rw [hq]
      intro i; fin_cases i <;> norm_num [degrees, Fin.sum_univ_succ, vecHead, vecTail, cons_val_one, cons_val_two, cons_val_three, cons_val_four]
  have clone_certificate (m : ℕ) (hm : 0 < m) :
      let card := 6 * m
      card > 0 ∧ (m : ℝ) > 0 ∧ (1 / ((20 : ℝ) * m)) < 1 / ((6 : ℝ) * m) ∧ 0 < 1 / ((20 : ℝ) * m) ∧ 1 / ((6 : ℝ) * m) < 1 / ((3 : ℝ) * m) := by
    dsimp
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    refine ⟨by omega, hm', ?_, ?_, ?_⟩
    · apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
      nlinarith [hm']
    · positivity
    · apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
      nlinarith [hm']
  have stable_isUnit {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] {s : ℝ}
      (hs : 0 < s) (hstable : s < -1 / spectralMinimum G) : IsUnit (1 + s • graphAdj G) := by
    classical
    have hmin : spectralMinimum G < 0 := by
      have hp : 0 < -1 / spectralMinimum G := lt_trans hs hstable
      rcases (div_pos_iff.mp hp) with h | h
      · norm_num at h
      · exact h.2
    by_contra hn
    have hz : (0 : ℝ) ∈ spectrum ℝ (1 + s • graphAdj G) := spectrum.zero_mem ℝ hn
    have hn1 : (-1 : ℝ) ∈ spectrum ℝ (s • graphAdj G) := by
      apply (spectrum.add_mem_add_iff (s := (1 : ℝ))).mp; simpa using hz
    have he : (-1 / s : ℝ) ∈ spectrum ℝ (graphAdj G) := by
      apply (spectrum.smul_mem_smul_iff (r := Units.mk0 s hs.ne')).mp; convert hn1 using 1 <;> simp [Units.smul_def, smul_eq_mul] <;> field_simp
    rw [graphAdj, (G.isHermitian_adjMatrix ℝ).spectrum_real_eq_range_eigenvalues] at he
    obtain ⟨i, hi⟩ := he
    have hle : spectralMinimum G ≤ -1 / s := by
      rw [spectralMinimum, dif_pos (inferInstance : Nonempty W), ← hi]
      exact Finset.inf'_le (G.isHermitian_adjMatrix ℝ).eigenvalues (Finset.mem_univ i)
    have hprod : 1 + s * spectralMinimum G > 0 := by
      have := (lt_div_iff_of_neg hmin).mp hstable
      nlinarith
    have : s * spectralMinimum G ≤ -1 := by
      have := mul_le_mul_of_nonneg_left hle hs.le
      have hmul : s * (-1 / s) = -1 := by field_simp
      simpa only [hmul] using this
    linarith
  have stable_equilibrium {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] {s : ℝ}
      (hs : 0 < s) (hstable : s < -1 / spectralMinimum G) : (1 + s • graphAdj G) *ᵥ graphGamma G s = s • graphDegrees G := by
    classical
    have hu := (Matrix.isUnit_iff_isUnit_det _).mp (stable_isUnit G hs hstable)
    rw [graphGamma, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have stable_clipped_mass_pos {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] (hG : Nonregular G) {s : ℝ}
      (hs : 0 < s) (hstable : s < -1 / spectralMinimum G) : 0 < ∑ i, clipped (graphGamma G s) i := by
    classical
    have hedge : ∃ u v, G.Adj u v := by
      by_contra hn
      push Not at hn
      rcases hG with ⟨u, v, huv⟩
      simp [hn] at huv
    obtain ⟨u, v, huv⟩ := hedge
    have ha : ∀ i j, 0 ≤ graphAdj G i j := by
      intro i j; simp only [graphAdj, SimpleGraph.adjMatrix_apply]
      split_ifs <;> norm_num
    have hd : 0 < graphDegrees G u := by
      have hle := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => mul_nonneg (ha u j) (by norm_num : (0 : ℝ) ≤ 1)) (Finset.mem_univ v)
      have he : graphAdj G u v = 1 := by simp [graphAdj, huv]
      simpa [graphDegrees, Matrix.mulVec, dotProduct, he] using (lt_of_lt_of_le (by norm_num [he] : (0 : ℝ) < graphAdj G u v * 1) hle)
    have hc : ∀ i, 0 ≤ clipped (graphGamma G s) i := fun i => le_max_right _ _
    by_contra hn
    have hz : ∑ i, clipped (graphGamma G s) i = 0 := le_antisymm (le_of_not_gt hn) (Finset.sum_nonneg (fun i _ => hc i))
    have hg : ∀ i, graphGamma G s i ≤ 0 := by
      intro i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hc j)).mp hz i (Finset.mem_univ i)
      exact le_trans (le_max_left _ _) hi.le
    have hB : ∀ j, 0 ≤ (1 + s • graphAdj G) u j := by
      intro j; simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      exact add_nonneg (by simp only [Matrix.one_apply]; split_ifs <;> norm_num) (mul_nonneg hs.le (ha u j))
    have hle : ((1 + s • graphAdj G) *ᵥ graphGamma G s) u ≤ 0 := by exact Finset.sum_nonpos (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hB j) (hg j))
    rw [stable_equilibrium G hs hstable] at hle; exact (not_le_of_gt (mul_pos hs hd)) hle
  have witness_isUnit {s : ℝ} (hs : 0 ≤ s) (hslt : s < 1 / 3) : IsUnit (B s) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr; apply isUnit_iff_ne_zero.mpr; apply det_ne_zero_of_sum_row_lt_diag
    intro i; rw [B_formula]; fin_cases i <;>
      norm_num [Fin.sum_univ_succ, Real.norm_eq_abs, abs_of_nonneg hs, Finset.sum_erase,
        vecHead, vecTail, cons_val_one, cons_val_two, cons_val_three, cons_val_four] <;>
      linarith
  have inverse_coordinate_bridge {s : ℝ} (hs : 0 ≤ s) (hslt : s < 1 / 3) (hC : C s ≠ 0) : sourceGamma s = explicitGamma s := by
    have hu := witness_isUnit hs hslt
    apply (Matrix.mulVec_injective_iff_isUnit.mpr hu)
    have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hu
    dsimp only [sourceGamma]; rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    dsimp only [explicitGamma]; rw [Matrix.mulVec_smul, (direct_coordinate_certificate s).1, smul_smul, div_mul_cancel₀ s hC]
  have graph_gamma_witness (s : ℝ) : graphGamma sourceGraph s = sourceGamma s := by
    have hadj : graphAdj sourceGraph = A := rfl
    have hdeg : graphDegrees sourceGraph = degrees := by
      change A *ᵥ ones = degrees; exact degree_formula
    simp only [graphGamma, sourceGamma, B, hadj, hdeg]
  have witness_spectral_bounds : -3 ≤ spectralMinimum sourceGraph ∧ spectralMinimum sourceGraph ≤ -1 := by
    have hA : A.IsHermitian := sourceGraph.isHermitian_adjMatrix ℝ
    have hmin : spectralMinimum sourceGraph = Finset.univ.inf' Finset.univ_nonempty hA.eigenvalues := by
      simp only [spectralMinimum, dif_pos (inferInstance : Nonempty (Fin 6))]; rfl
    have hrow : ∀ k, ∑ j ∈ Finset.univ.erase k, ‖A k j‖ ≤ 3 := by
      intro k; rw [Finset.sum_erase_eq_sub (Finset.mem_univ k), adjacency_formula]; fin_cases k <;> norm_num [Fin.sum_univ_succ]
    have hlo : ∀ i, -3 ≤ hA.eigenvalues i := by
      intro i
      have he : Module.End.HasEigenvalue A.toLin' (hA.eigenvalues i) := by
        apply Module.End.HasEigenvalue.of_mem_spectrum; rw [Matrix.spectrum_toLin']; exact hA.eigenvalues_mem_spectrum_real i
      obtain ⟨k, hk⟩ := eigenvalue_mem_ball he
      have hdiag : A k k = 0 := by simp [A, SimpleGraph.adjMatrix]
      have hn : ‖hA.eigenvalues i‖ ≤ 3 := by
        rw [Metric.mem_closedBall, dist_eq_norm, hdiag, sub_zero] at hk; exact le_trans hk (hrow k)
      exact (abs_le.mp (Real.norm_eq_abs _ ▸ hn)).1
    have hneg : (-1 : ℝ) ∈ spectrum ℝ A := by
      rw [← Matrix.spectrum_toLin']; apply Module.End.HasEigenvalue.mem_spectrum
      apply Module.End.hasEigenvalue_of_hasEigenvector (x := (![0, 1, -1, 0, 0, 0] : (Fin 6) → ℝ))
      refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
      · change A *ᵥ _ = _
        rw [adjacency_formula]; ext i; fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      · intro hz
        have := congrFun hz 1
        norm_num at this
    rw [hA.spectrum_real_eq_range_eigenvalues] at hneg
    obtain ⟨i, hi⟩ := hneg
    rw [hmin]
    constructor
    · exact Finset.le_inf' _ _ (fun i _ => hlo i)
    · rw [← hi]
      exact Finset.inf'_le _ (Finset.mem_univ i)
  have witness_stable {s : ℝ} (hs : 0 < s) (hslt : s < 1 / 3) : s < -1 / spectralMinimum sourceGraph := by
    rcases witness_spectral_bounds with ⟨hlo, hhi⟩
    have hn : spectralMinimum sourceGraph < 0 := lt_of_le_of_lt hhi (by norm_num)
    apply (lt_div_iff_of_neg hn).mpr
    have := mul_le_mul_of_nonneg_left hlo hs.le
    nlinarith
  have actual_pair_certificate : graphGamma sourceGraph (1 / 20) = (1 / 4357 : ℝ) • ![(397 : ℝ), 577, 577, 378, 576, 198] ∧ graphGamma sourceGraph (1 / 6) =
          (1 / 129 : ℝ) • ![(33 : ℝ), 45, 45, 28, 44, 16] ∧
      normalized (graphGamma sourceGraph (1 / 20)) = (1 / 2703 : ℝ) • ![(397 : ℝ), 577, 577, 378, 576, 198] ∧ normalized (graphGamma sourceGraph (1 / 6)) =
          (1 / 211 : ℝ) • ![(33 : ℝ), 45, 45, 28, 44, 16] := by
    have h20 : graphGamma sourceGraph (1 / 20) = explicitGamma (1 / 20) := by
      rw [graph_gamma_witness]; exact inverse_coordinate_bridge (by norm_num) (by norm_num) (by norm_num [C])
    have h6 : graphGamma sourceGraph (1 / 6) = explicitGamma (1 / 6) := by
      rw [graph_gamma_witness]; exact inverse_coordinate_bridge (by norm_num) (by norm_num) (by norm_num [C])
    rw [h20, h6]; exact ⟨gamma_pair.1, gamma_pair.2, pair_probability_certificate.1, pair_probability_certificate.2⟩
  have scalar_normalization {W : Type} [Fintype W] (x : W → ℝ)
      {s : ℝ} (hs : 0 < s) (hx : ∀ i, 0 < x i) : normalized (s • x) = fun i => x i / ∑ j, x j := by
    classical
    have hclip : clipped (s • x) = s • x := by
      ext i; exact max_eq_left (le_of_lt (mul_pos hs (hx i)))
    ext i; simp only [normalized, hclip, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]; exact mul_div_mul_left _ _ hs.ne'
  have general_probability_derivative {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] (hd : ∀ i, 0 < graphDegrees G i) :
      let d := graphDegrees G
      let q := graphAdj G *ᵥ d
      let D := ∑ i, d i
      let Q := ∑ i, q i
      let x := fun s : ℝ => (1 + s • graphAdj G)⁻¹ *ᵥ d
      let p := fun s i => x s i / ∑ j, x s j
      (∀ i, HasDerivAt (fun s => p s i) ((Q * d i - D * q i) / D^2) 0) ∧ (∀ᶠ s in nhds (0 : ℝ), 0 < s → graphEntropyBits G s = entropyBits (p s)) := by
    classical
    dsimp only
    letI : NormedAddCommGroup (Matrix W W ℝ) := Matrix.linftyOpNormedAddCommGroup
    letI : NormedSpace ℝ (Matrix W W ℝ) := Matrix.linftyOpNormedSpace
    let d := graphDegrees G
    let q := graphAdj G *ᵥ d
    let D := ∑ i, d i
    let Q := ∑ i, q i
    let x := fun s : ℝ => (1 + s • graphAdj G)⁻¹ *ᵥ d
    have hD : 0 < D := Finset.sum_pos (fun i _ => hd i) Finset.univ_nonempty
    have hx0 : x 0 = d := by simp [x]
    have hf : HasDerivAt (fun s : ℝ => (1 : Matrix W W ℝ) + s • graphAdj G) (graphAdj G) 0 := by
      simpa only [one_smul, id_eq] using! ((hasDerivAt_id (0 : ℝ)).smul_const (graphAdj G)).const_add (1 : Matrix W W ℝ)
    have hi : HasDerivAt (fun s : ℝ => (1 + s • graphAdj G)⁻¹) (-graphAdj G) 0 := by
      have h0 := hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (Matrix W W ℝ)ˣ)
      have h := h0.comp_hasDerivAt_of_eq 0 hf (by simp)
      simpa [Matrix.nonsing_inv_eq_ringInverse, Function.comp_def, ContinuousLinearMap.mulLeftRight_apply] using h
    let entry := fun i j =>
      ({ toFun := fun M : Matrix W W ℝ => M i j
         map_add' := by intros; rfl
         map_smul' := by intros; rfl } : Matrix W W ℝ →ₗ[ℝ] ℝ).toContinuousLinearMap
    have he : ∀ i j, HasDerivAt (fun s : ℝ => ((1 + s • graphAdj G)⁻¹) i j) (-graphAdj G i j) 0 := by
      intro i j; simpa [entry, Function.comp_def] using (entry i j).hasFDerivAt.comp_hasDerivAt 0 hi
    have hx : ∀ i, HasDerivAt (fun s => x s i) (-q i) 0 := by
      intro i
      have h := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (he i j).mul_const (d j))
      simpa [x, q, Matrix.mulVec, dotProduct, Finset.sum_neg_distrib] using h
    have ht : HasDerivAt (fun s => ∑ j, x s j) (-Q) 0 := by
      simpa [Q, Finset.sum_neg_distrib] using HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hx j)
    constructor
    · intro i
      have h := (hx i).div ht (by simpa [hx0] using hD.ne')
      convert! h using 1 <;> try rfl
      rw [hx0]; dsimp [D, Q]; ring
    · have hxpos : ∀ᶠ s in nhds (0 : ℝ), ∀ i, 0 < x s i := by
        apply Filter.eventually_all.mpr; intro i; exact (hx i).continuousAt.eventually (lt_mem_nhds (by simpa [hx0] using hd i))
      filter_upwards [hxpos] with s hs hsp
      unfold graphEntropyBits graphGamma; rw [scalar_normalization (x s) hsp hs]
  have general_covariance_derivative {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] (hd : ∀ i, 0 < graphDegrees G i) :
      let d := graphDegrees G
      let q := graphAdj G *ᵥ d
      let D := ∑ i, d i
      let Q := ∑ i, q i
      let x := fun s : ℝ => (1 + s • graphAdj G)⁻¹ *ᵥ d
      let p := fun s i => x s i / ∑ j, x s j
      let w := fun i => d i / D
      let r := fun i => q i / d i
      let cov := (∑ i, w i * r i * Real.log (d i)) - (∑ i, w i * r i) * (∑ i, w i * Real.log (d i))
      HasDerivAt (fun s => entropyBits (p s)) (cov / Real.log 2) 0 := by
    classical
    dsimp only
    let d := graphDegrees G
    let q := graphAdj G *ᵥ d
    let D := ∑ i, d i
    let Q := ∑ i, q i
    let x := fun s : ℝ => (1 + s • graphAdj G)⁻¹ *ᵥ d
    let p := fun s i => x s i / ∑ j, x s j
    let v := fun i => (Q * d i - D * q i) / D^2
    have hD : 0 < D := Finset.sum_pos (fun i _ => hd i) Finset.univ_nonempty
    have hp0 : ∀ i, p 0 i = d i / D := by intro i; simp [p, x, D]
    have hp : ∀ i, HasDerivAt (fun s => p s i) (v i) 0 := (general_probability_derivative G hd).1
    have hv : ∑ i, v i = 0 := by
      change (∑ i, (Q * d i - D * q i) / D^2) = 0; rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      change (Q * D - D * Q) / D^2 = 0; ring
    have hterm : ∀ i, HasDerivAt (fun s => Real.negMulLog (p s i)) ((-Real.log (d i / D) - 1) * v i) 0 := by
      intro i
      have h0 : p 0 i ≠ 0 := by rw [hp0]; exact div_ne_zero (hd i).ne' hD.ne'
      simpa only [Function.comp_def, hp0] using (Real.hasDerivAt_negMulLog h0).comp 0 (hp i)
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hterm i)
    have hsimpl : ∑ i, (-Real.log (d i / D) - 1) * v i = (D * (∑ i, q i * Real.log (d i)) - Q * (∑ i, d i * Real.log (d i))) / D^2 := by
      have hi : ∀ i, (-Real.log (d i / D) - 1) * v i = -v i * Real.log (d i) + (Real.log D - 1) * v i := by
        intro i; rw [Real.log_div (hd i).ne' hD.ne']; ring
      have hvlog : ∑ i, v i * Real.log (d i) = (Q * (∑ i, d i * Real.log (d i)) - D * (∑ i, q i * Real.log (d i))) / D^2 := by
        change (∑ i, ((Q * d i - D * q i) / D^2) * Real.log (d i)) = _; simp_rw [div_mul_eq_mul_div]; rw [← Finset.sum_div]
        congr 1
        simp_rw [sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_add_distrib, ← Finset.mul_sum, hv, mul_zero, add_zero]; simp_rw [neg_mul]
      rw [Finset.sum_neg_distrib, hvlog]; ring
    have hr : ∀ i, (d i / D) * (q i / d i) = q i / D := by
      intro i
      have hdi : d i ≠ 0 := (hd i).ne'
      field_simp [hdi, hD.ne']
    have hcov : (∑ i, (d i / D) * (q i / d i) * Real.log (d i)) - (∑ i, (d i / D) * (q i / d i)) * (∑ i, (d i / D) * Real.log (d i)) =
        (D * (∑ i, q i * Real.log (d i)) - Q * (∑ i, d i * Real.log (d i))) / D^2 := by
      simp only [hr]; simp_rw [div_mul_eq_mul_div]; rw [← Finset.sum_div, ← Finset.sum_div, ← Finset.sum_div]
      dsimp [Q]; field_simp [hD.ne']
    have h := hsum.div_const (Real.log 2)
    rw [hsimpl] at h; rw [hcov]; simpa only [entropyBits, D5.S3.Entropy.MaxEntropy.shannonEntropy] using h
  have general_degree_square_sum {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj] :
      ∑ i, (graphAdj G *ᵥ graphDegrees G) i = ∑ i, (graphDegrees G i)^2 := by
    classical
    have hs : ∀ i j, graphAdj G i j = graphAdj G j i := by
      intro i j; exact congrFun (congrFun (G.isSymm_adjMatrix (α := ℝ)) j) i
    simp only [Matrix.mulVec, dotProduct]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl
    intro i _; simp_rw [hs, ← Finset.sum_mul]
    have hd : ∑ j, graphAdj G i j = graphDegrees G i := by simp [graphDegrees, Matrix.mulVec, dotProduct]
    rw [hd]; ring
  let logApprox (z : ℝ) : ℝ := 2 * (z + z^3 / 3 + z^5 / 5)
  have log_approximation {p : ℝ} (hp : 0 < p) (hz : |(8*p - 1) / (8*p + 1)| ≤ 27 / 100) :
      |Real.log (8*p) - logApprox ((8*p - 1) / (8*p + 1))| ≤ 1 / 4000 := by
    let z := (8*p - 1) / (8*p + 1)
    have hz' : |z| ≤ 27 / 100 := hz
    have hsq : z^2 ≤ (27 / 100 : ℝ)^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg z) hz' 2
    have hden : 0 < 1 - z^2 := by nlinarith
    have htail : |z|^7 / (1 - z^2) ≤ 1 / 8000 := by
      calc
        _ ≤ (27 / 100 : ℝ)^7 / (1 - (27 / 100 : ℝ)^2) := by gcongr
        _ ≤ _ := by norm_num
    have hr := Real.sum_range_sub_log_div_le (lt_of_le_of_lt hz' (by norm_num : (27 / 100 : ℝ) < 1)) 3
    have hid : (1 + z) / (1 - z) = 8*p := by
      dsimp [z]; field_simp; ring
    rw [hid] at hr; norm_num [Finset.sum_range_succ] at hr
    have hpoli : Real.log (8*p) - logApprox z = 2 * (1/2 * Real.log (8*p) - (z + z^3/3 + z^5/5)) := by dsimp [logApprox]; ring
    rw [hpoli, abs_mul]; norm_num
    have ht := le_trans hr htail
    nlinarith
  have entropy_shift_identity {W : Type} [Fintype W] (p : W → ℝ) (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) :
      entropyBits p = 3 - (∑ i, p i * Real.log (8*p i)) / Real.log 2 := by
    classical
    have hl : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
    have he : ∑ i, p i * Real.log (8*p i) = 3 * Real.log 2 + ∑ i, p i * Real.log (p i) := by
      simp_rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (hp _).ne', mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hs, one_mul, hl]
    rw [entropyBits, D5.S3.Entropy.MaxEntropy.shannonEntropy]; simp_rw [Real.negMulLog_def, neg_mul, Finset.sum_neg_distrib]; rw [he]
    field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']; ring
  have actual_entropy_gap : 1 / (500 * Real.log 2) < graphEntropyBits sourceGraph (1/6) - graphEntropyBits sourceGraph (1/20) := by
    let p : (Fin 6) → ℝ := (1/2703 : ℝ) • ![(397 : ℝ),577,577,378,576,198]
    let r : (Fin 6) → ℝ := (1/211 : ℝ) • ![(33 : ℝ),45,45,28,44,16]
    have hp : ∀ i, 0 < p i := by intro i; fin_cases i <;> norm_num [p]
    have hr : ∀ i, 0 < r i := by intro i; fin_cases i <;> norm_num [r]
    have hpsum : ∑ i, p i = 1 := by norm_num [p, Fin.sum_univ_succ]
    have hrsum : ∑ i, r i = 1 := by norm_num [r, Fin.sum_univ_succ]
    have hzp : ∀ i, |(8*p i - 1)/(8*p i + 1)| ≤ 27/100 := by intro i; fin_cases i <;> norm_num [p]
    have hzr : ∀ i, |(8*r i - 1)/(8*r i + 1)| ≤ 27/100 := by intro i; fin_cases i <;> norm_num [r]
    have hpl : ∀ i, p i * logApprox ((8*p i-1)/(8*p i+1)) - p i / 4000 ≤ p i * Real.log (8*p i) := by
      intro i
      have h := (abs_le.mp (log_approximation (hp i) (hzp i))).1
      nlinarith [hp i]
    have hru : ∀ i, r i * Real.log (8*r i) ≤ r i * logApprox ((8*r i-1)/(8*r i+1)) + r i / 4000 := by
      intro i
      have h := (abs_le.mp (log_approximation (hr i) (hzr i))).2
      nlinarith [hr i]
    have hpt : (342367 : ℝ)/1000000 < ∑ i, p i * logApprox ((8*p i-1)/(8*p i+1)) := by norm_num [p, logApprox, Fin.sum_univ_succ]
    have hrt : (∑ i, r i * logApprox ((8*r i-1)/(8*r i+1))) < (339667 : ℝ)/1000000 := by norm_num [r, logApprox, Fin.sum_univ_succ]
    have hlower := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpl i)
    have hupper := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hru i)
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hpsum] at hlower; rw [Finset.sum_add_distrib, ← Finset.sum_div, hrsum] at hupper
    have hdiff : 1/500 < (∑ i, p i * Real.log (8*p i)) - ∑ i, r i * Real.log (8*r i) := by linarith
    have h20 : normalized (graphGamma sourceGraph (1/20)) = p := actual_pair_certificate.2.2.1
    have h6 : normalized (graphGamma sourceGraph (1/6)) = r := actual_pair_certificate.2.2.2
    rw [graphEntropyBits, graphEntropyBits, h20, h6, entropy_shift_identity p hp hpsum, entropy_shift_identity r hr hrsum]
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h := (div_lt_div_of_pos_right hdiff hl2)
    convert! h using 1 <;> first | rfl | (field_simp <;> simp only [mul_comm] <;> ring)
  let cloneGraph (m : ℕ) : SimpleGraph ((Fin 6) × Fin m) := {
    Adj u v := sourceGraph.Adj u.1 v.1
    symm := ⟨fun _ _ h => sourceGraph.symm.symm _ _ h⟩
    loopless := ⟨fun u h => sourceGraph.loopless.irrefl u.1 h⟩ }
  letI local_decidable_2 (m : ℕ) : DecidableRel (cloneGraph m).Adj := by
    intro u v; change Decidable (sourceGraph.Adj u.1 v.1); infer_instance
  have clone_adjacency (m : ℕ) (u v : (Fin 6) × Fin m) : graphAdj (cloneGraph m) u v = A u.1 v.1 := rfl
  have clone_action (m : ℕ) (v : (Fin 6) → ℝ) : graphAdj (cloneGraph m) *ᵥ (fun i => v i.1) = fun i => (m : ℝ) * (A *ᵥ v) i.1 := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, clone_adjacency, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.mul_sum]
  have clone_degrees (m : ℕ) : graphDegrees (cloneGraph m) = fun i => (m : ℝ) * degrees i.1 := by
    change graphAdj (cloneGraph m) *ᵥ (fun i => ones i.1) = _; rw [clone_action, degree_formula]
  have clone_connected (m : ℕ) (hm : 0 < m) : (cloneGraph m).Connected := by
    let z : Fin m := ⟨0, hm⟩
    let lift : sourceGraph →g cloneGraph m :=
      { toFun := fun i => (i, z)
        map_rel' := fun h => h }
    let neighbor : (Fin 6) → (Fin 6) := ![4, 2, 1, 1, 0, 0]
    have hneighbor : ∀ i, sourceGraph.Adj (neighbor i) i := by
      intro i; fin_cases i <;> decide
    apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr; refine ⟨(0, z), ?_⟩; intro i
    exact ((source_connected 0 (neighbor i.1)).map lift).trans (SimpleGraph.Adj.reachable (G := cloneGraph m) (hneighbor i.1))
  have graph_unit_of_degree_bound {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj] {dmax s : ℝ}
      (hmax : ∀ i, graphDegrees G i ≤ dmax) (hs : 0 ≤ s) (hsmall : s*dmax < 1) : IsUnit (1 + s • graphAdj G) := by
    classical
    apply (Matrix.isUnit_iff_isUnit_det _).mpr; apply isUnit_iff_ne_zero.mpr; apply det_ne_zero_of_sum_row_lt_diag
    intro i
    have hdiag : graphAdj G i i = 0 := by simp [graphAdj, SimpleGraph.adjMatrix]
    have hsum : ∑ j ∈ Finset.univ.erase i, ‖(1 + s • graphAdj G) i j‖ = s * graphDegrees G i := by
      have he : ∀ j ∈ Finset.univ.erase i, ‖(1 + s • graphAdj G) i j‖ = s * graphAdj G i j := by
        intro j hj
        have hji := (Finset.mem_erase.mp hj).1
        simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, if_neg (Ne.symm hji), zero_add, graphAdj, SimpleGraph.adjMatrix_apply]
        split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg hs]
      rw [Finset.sum_congr rfl (fun j hj => he j hj), ← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ i), hdiag, sub_zero]
      congr 1
      simp [graphDegrees, Matrix.mulVec, dotProduct]
    rw [hsum]
    have hd : (1 + s • graphAdj G) i i = 1 := by simp [Matrix.one_apply, hdiag]
    rw [hd]; norm_num; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hmax i) hs) hsmall
  have clone_inverse_replication (m : ℕ) (hm : 0 < m) {s : ℝ} (hs : 0 < s) (hsmall : s < 1 / (3 * (m : ℝ))) :
      graphGamma (cloneGraph m) s = fun i => graphGamma sourceGraph ((m : ℝ)*s) i.1 := by
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hms : 0 ≤ (m : ℝ)*s := le_of_lt (mul_pos hm' hs)
    have hmslt : (m : ℝ)*s < 1/3 := by
      have := (lt_div_iff₀ (by positivity : 0 < 3*(m : ℝ))).mp hsmall
      nlinarith
    have hbase := stable_equilibrium sourceGraph (mul_pos hm' hs) (witness_stable (mul_pos hm' hs) hmslt)
    have hmax : ∀ i, graphDegrees (cloneGraph m) i ≤ 3*(m : ℝ) := by
      intro i; rw [clone_degrees]
      have hdall : ∀ j, degrees j ≤ 3 := by intro j; fin_cases j <;> norm_num [degrees]
      have hd := hdall i.1
      nlinarith
    have hunit := graph_unit_of_degree_bound (cloneGraph m) hmax hs.le ((lt_div_iff₀ (by positivity : 0 < 3*(m : ℝ))).mp hsmall)
    have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hunit
    apply Matrix.mulVec_injective_iff_isUnit.mpr hunit
    rw [graphGamma, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, clone_action, clone_degrees]; ext i
    have hi := congrFun hbase i.1
    have hadj : graphAdj sourceGraph = A := rfl
    have hdeg : graphDegrees sourceGraph = degrees := by
      change A *ᵥ ones = degrees; exact degree_formula
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hadj, hdeg] at hi
    change _ = graphGamma sourceGraph ((m : ℝ)*s) i.1 + s * ((m : ℝ) * (A *ᵥ graphGamma sourceGraph ((m : ℝ)*s)) i.1)
    change graphGamma sourceGraph ((m : ℝ)*s) i.1 + ((m : ℝ)*s) * (A *ᵥ graphGamma sourceGraph ((m : ℝ)*s)) i.1 = ((m : ℝ)*s) * degrees i.1 at hi
    dsimp only [Pi.smul_apply, smul_eq_mul]; nlinarith [hi]
  have normalized_sum {W : Type} [Fintype W] (p : W → ℝ) (hp : 0 < ∑ i, clipped p i) : ∑ i, normalized p i = 1 := by
    simp only [normalized]; rw [← Finset.sum_div, div_self hp.ne']
  have clone_probability_replication (m : ℕ) (p : (Fin 6) → ℝ) : normalized (fun i : (Fin 6) × Fin m => p i.1) = fun i => normalized p i.1 / (m : ℝ) := by
    classical
    ext i
    simp only [normalized, clipped, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    simp [div_div, mul_comm]
  have clone_entropy_identity (m : ℕ) (hm : 0 < m) (p : (Fin 6) → ℝ) (hp : ∑ i, p i = 1) : entropyBits (fun i : (Fin 6) × Fin m => p i.1 / (m : ℝ)) =
        entropyBits p + Real.log (m : ℝ) / Real.log 2 := by
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have he : ∀ i, (m : ℝ) * Real.negMulLog (p i / (m : ℝ)) = Real.negMulLog (p i) + p i * Real.log (m : ℝ) := by
      intro i; rw [div_eq_mul_inv, Real.negMulLog_mul]; simp only [Real.negMulLog_def, Real.log_inv]
      field_simp [hm']
    have hsum : ∑ i : (Fin 6) × Fin m, Real.negMulLog (p i.1 / (m : ℝ)) = (∑ i, Real.negMulLog (p i)) + Real.log (m : ℝ) := by
      rw [Fintype.sum_prod_type]; simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp_rw [he, Finset.sum_add_distrib, ← Finset.sum_mul, hp, one_mul]
    rw [entropyBits, D5.S3.Entropy.MaxEntropy.shannonEntropy, hsum]; exact add_div _ _ _
  have clone_actual_entropy_identity (m : ℕ) (hm : 0 < m) {s : ℝ} (hs : 0 < s) (hsmall : s < 1 / (3 * (m : ℝ))) :
      graphEntropyBits (cloneGraph m) s = graphEntropyBits sourceGraph ((m : ℝ)*s) + Real.log (m : ℝ) / Real.log 2 := by
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hms : 0 < (m : ℝ)*s := mul_pos hm' hs
    have hmslt : (m : ℝ)*s < 1/3 := by
      have := (lt_div_iff₀ (by positivity : 0 < 3*(m : ℝ))).mp hsmall
      nlinarith
    have hmass := stable_clipped_mass_pos sourceGraph source_nonregular hms (witness_stable hms hmslt)
    unfold graphEntropyBits; rw [clone_inverse_replication m hm hs hsmall, clone_probability_replication]
    exact clone_entropy_identity m hm _ (normalized_sum _ hmass)
  have clone_exact_gap (m : ℕ) (hm : 0 < m) : 1 / (500 * Real.log 2) < graphEntropyBits (cloneGraph m) (1 / (6 * (m : ℝ))) -
          graphEntropyBits (cloneGraph m) (1 / (20 * (m : ℝ))) := by
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have h20 : 0 < 1 / (20 * (m : ℝ)) := by positivity
    have h6 : 0 < 1 / (6 * (m : ℝ)) := by positivity
    have hs20 : 1 / (20 * (m : ℝ)) < 1 / (3 * (m : ℝ)) := by
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr; nlinarith
    have hs6 : 1 / (6 * (m : ℝ)) < 1 / (3 * (m : ℝ)) := by
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr; nlinarith
    have he20 : (m : ℝ) * (1 / (20 * (m : ℝ))) = 1/20 := by field_simp
    have he6 : (m : ℝ) * (1 / (6 * (m : ℝ))) = 1/6 := by field_simp
    rw [clone_actual_entropy_identity m hm h6 hs6, clone_actual_entropy_identity m hm h20 hs20, he20, he6]
    simpa only [add_sub_add_right_eq_sub] using actual_entropy_gap
  have clone_nonregular (m : ℕ) (hm : 0 < m) : Nonregular (cloneGraph m) := by
    classical
    let z : Fin m := ⟨0, hm⟩
    refine ⟨(0, z), (5, z), ?_⟩; intro he
    have hnat : ∀ i : (Fin 6) × Fin m, graphDegrees (cloneGraph m) i = ((∑ j, if (cloneGraph m).Adj i j then (1 : ℕ) else 0) : ℝ) := by
      intro i; simp [graphDegrees, graphAdj, Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix]
    have heq : graphDegrees (cloneGraph m) (0, z) = graphDegrees (cloneGraph m) (5, z) := by
      rw [hnat, hnat]
      exact_mod_cast he
    rw [clone_degrees] at heq; change (m : ℝ)*2 = (m : ℝ)*1 at heq
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    nlinarith
  have spectral_lower_degree {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] {dmax : ℝ}
      (hmax : ∀ i, graphDegrees G i ≤ dmax) : -dmax ≤ spectralMinimum G := by
    classical
    let hA := G.isHermitian_adjMatrix ℝ
    have hmin : spectralMinimum G = Finset.univ.inf' Finset.univ_nonempty hA.eigenvalues := by
      simp only [spectralMinimum, dif_pos (inferInstance : Nonempty W)]; rfl
    rw [hmin]; apply Finset.le_inf'; intro i _
    have he : Module.End.HasEigenvalue (graphAdj G).toLin' (hA.eigenvalues i) := by
      apply Module.End.HasEigenvalue.of_mem_spectrum; rw [Matrix.spectrum_toLin']; exact hA.eigenvalues_mem_spectrum_real i
    obtain ⟨k, hk⟩ := eigenvalue_mem_ball he
    have hdiag : graphAdj G k k = 0 := by simp [graphAdj, SimpleGraph.adjMatrix]
    have ha : ∀ j, ‖graphAdj G k j‖ = graphAdj G k j := by
      intro j; simp only [graphAdj, SimpleGraph.adjMatrix_apply]
      split_ifs <;> norm_num
    have hrow : ∑ j ∈ Finset.univ.erase k, ‖graphAdj G k j‖ = graphDegrees G k := by
      simp_rw [ha]; rw [Finset.sum_erase_eq_sub (Finset.mem_univ k), hdiag, sub_zero]; simp [graphDegrees, Matrix.mulVec, dotProduct]
    rw [Metric.mem_closedBall, dist_eq_norm, hdiag, sub_zero, hrow] at hk; exact (abs_le.mp (Real.norm_eq_abs _ ▸ le_trans hk (hmax k))).1
  have clone_spectral_bounds (m : ℕ) (hm : 0 < m) : -3*(m : ℝ) ≤ spectralMinimum (cloneGraph m) ∧ spectralMinimum (cloneGraph m) ≤ -(m : ℝ) := by
    letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    have hmax : ∀ i, graphDegrees (cloneGraph m) i ≤ 3*(m : ℝ) := by
      intro i; rw [clone_degrees]
      have hdall : ∀ j, degrees j ≤ 3 := by intro j; fin_cases j <;> norm_num [degrees]
      exact mul_le_mul_of_nonneg_left (hdall i.1) (Nat.cast_nonneg m) |>.trans_eq (by ring)
    refine ⟨?_, ?_⟩
    · convert spectral_lower_degree (cloneGraph m) hmax using 1 <;> ring
    · have hA := (cloneGraph m).isHermitian_adjMatrix ℝ
      let v : (Fin 6) → ℝ := ![0, 1, -1, 0, 0, 0]
      have hv : A *ᵥ v = -v := by
        rw [adjacency_formula]; ext i; fin_cases i <;> norm_num [v, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      have he : (-(m : ℝ)) ∈ spectrum ℝ (graphAdj (cloneGraph m)) := by
        rw [← Matrix.spectrum_toLin']; apply Module.End.HasEigenvalue.mem_spectrum
        apply Module.End.hasEigenvalue_of_hasEigenvector (x := fun i : (Fin 6) × Fin m => v i.1)
        refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
        · change graphAdj (cloneGraph m) *ᵥ (fun i => v i.1) = _
          rw [clone_action, hv]; ext i; simp
        · intro hz
          have hi := congrFun hz (1, (⟨0, hm⟩ : Fin m))
          norm_num [v] at hi
      rw [graphAdj, hA.spectrum_real_eq_range_eigenvalues] at he
      obtain ⟨i, hi⟩ := he
      rw [spectralMinimum, dif_pos (inferInstance : Nonempty ((Fin 6) × Fin m)), ← hi]; exact Finset.inf'_le hA.eigenvalues (Finset.mem_univ i)
  have clone_stable (m : ℕ) (hm : 0 < m) {s : ℝ} (hs : 0 < s) (hsmall : s < 1 / (3*(m : ℝ))) : s < -1 / spectralMinimum (cloneGraph m) := by
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    rcases clone_spectral_bounds m hm with ⟨hlo, hhi⟩
    have hn : spectralMinimum (cloneGraph m) < 0 := lt_of_le_of_lt hhi (by linarith)
    apply (lt_div_iff_of_neg hn).mpr
    have hs' := (lt_div_iff₀ (by positivity : 0 < 3*(m : ℝ))).mp hsmall
    have := mul_le_mul_of_nonneg_left hlo hs.le
    nlinarith
  have small_score_certificate {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1/100) : (∀ i, 0 < graphGamma sourceGraph s i ∧ graphGamma sourceGraph s i < 1) ∧
        normalized (graphGamma sourceGraph s) = fun i => N s i / T s := by
    have hC := C_pos_small hs.le hsmall
    have hT := T_pos_small hs.le hsmall
    have hN := N_pos_small hs.le hsmall
    have hCb : (1/2 : ℝ) < C s := by dsimp [C]; nlinarith [sq_nonneg s]
    have hNb : ∀ i, N s i ≤ 3 := by intro i; fin_cases i <;> simp [N] <;> nlinarith [sq_nonneg s]
    have hgamma : graphGamma sourceGraph s = explicitGamma s := by
      rw [graph_gamma_witness]; exact inverse_coordinate_bridge hs.le (by linarith) hC.ne'
    have hpos : ∀ i, 0 < N s i := hN
    constructor
    · intro i
      rw [hgamma]; change 0 < (s/C s)*N s i ∧ (s/C s)*N s i < 1
      constructor
      · exact mul_pos (div_pos hs hC) (hN i)
      · rw [div_mul_eq_mul_div, div_lt_one hC]
        have hx := mul_le_mul_of_nonneg_left (hNb i) hs.le
        nlinarith
    · rw [hgamma]
      unfold explicitGamma; rw [scalar_normalization (N s) (div_pos hs hC) hpos, (direct_coordinate_certificate s).2]
  have witness_origin_derivative :
      let x := fun s : ℝ => (1 + s • graphAdj sourceGraph)⁻¹ *ᵥ graphDegrees sourceGraph
      let p := fun s i => x s i / ∑ j, x s j
      HasDerivAt (fun s => entropyBits (p s)) (Real.log (27/2) / (49 * Real.log 2)) 0 ∧ 1 / (100 * Real.log 2) < Real.log (27/2) / (49 * Real.log 2) := by
    have hd : graphDegrees sourceGraph = degrees := by
      change A *ᵥ ones = degrees; exact degree_formula
    have ha : graphAdj sourceGraph = A := rfl
    have hpos : ∀ i, 0 < graphDegrees sourceGraph i := by rw [hd]; intro i; fin_cases i <;> norm_num [degrees]
    have hq : A *ᵥ degrees = ![(4 : ℝ),8,8,6,8,2] := covariance_certificate.2.1
    have hlog : Real.log (27/2) = 3*Real.log 3 - Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num), show (27 : ℝ) = 3^3 by norm_num, Real.log_pow]; norm_num
    constructor
    · have h := general_covariance_derivative sourceGraph hpos
      dsimp only at h ⊢; convert! h using 1 <;> try rfl
      rw [hd, ha, hq, hlog]; norm_num [degrees, Fin.sum_univ_succ, Real.log_one]; ring
    · have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hln : (25/27 : ℝ) < Real.log (27/2) := by
        have h := Real.self_sub_one_lt_mul_log (by norm_num : (0 : ℝ) ≤ 27/2) (by norm_num : (27/2 : ℝ) ≠ 1)
        nlinarith
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr; nlinarith
  -- The rational probability extension is used at zero; the source domain is positive.
  let n1 : Fin 6 → ℝ := ![0, -2, -2, -2, -2, 0]
  let n2 : Fin 6 → ℝ := ![-6, -6, -6, -4, -8, -4]
  let N1 (s : ℝ) (i : Fin 6) : ℝ := n1 i + 2 * n2 i * s
  let N2 (i : Fin 6) : ℝ := 2 * n2 i
  let T1 (s : ℝ) : ℝ := -8 - 68*s
  let P (s : ℝ) (i : Fin 6) : ℝ := N s i / T s
  let P1 (s : ℝ) (i : Fin 6) : ℝ := N1 s i / T s - N s i * T1 s / (T s)^2
  let P2 (s : ℝ) (i : Fin 6) : ℝ := N2 i / T s - 2 * N1 s i * T1 s / (T s)^2 - N s i * (-68) / (T s)^2 + 2 * N s i * (T1 s)^2 / (T s)^3
  let E (s : ℝ) : ℝ := entropyBits (P s)
  let E1 (s : ℝ) : ℝ := -(∑ i, P1 s i * (Real.log (P s i) + 1)) / Real.log 2
  let E2 (s : ℝ) : ℝ := -(∑ i, (P2 s i * (Real.log (P s i) + 1) + (P1 s i)^2 / P s i)) / Real.log 2
  have N_polynomial (s : ℝ) (i : Fin 6) : N s i = degrees i + n1 i*s + n2 i*s^2 := by fin_cases i <;> norm_num [N, degrees, n1, n2] <;> ring
  have N_derivative (s : ℝ) (i : Fin 6) : HasDerivAt (fun t => N t i) (N1 s i) s := by
    simp_rw [N_polynomial]; convert! (((hasDerivAt_const s (degrees i)).add ((hasDerivAt_id s).const_mul (n1 i))).add
      (((hasDerivAt_id s).pow 2).const_mul (n2 i))) using 1 <;> try simp only [N1, id_eq] <;> ring
  have N1_derivative (s : ℝ) (i : Fin 6) : HasDerivAt (fun t => N1 t i) (N2 i) s := by
    simpa [N1, N2] using! ((hasDerivAt_id s).const_mul (2*n2 i)).const_add (n1 i)
  have T_derivative (s : ℝ) : HasDerivAt T (T1 s) s := by
    convert! ((hasDerivAt_const s (14 : ℝ)).sub ((hasDerivAt_id s).const_mul 8)).sub
      (((hasDerivAt_id s).pow 2).const_mul 34) using 1 <;> try simp only [T, T1, id_eq] <;> ring
  have T1_derivative (s : ℝ) : HasDerivAt T1 (-68) s := by simpa [T1] using! (hasDerivAt_const s (-8 : ℝ)).sub ((hasDerivAt_id s).const_mul 68)
  have P_derivative {s : ℝ} (hT : T s ≠ 0) (i : Fin 6) : HasDerivAt (fun t => P t i) (P1 s i) s := by
    convert! (N_derivative s i).div (T_derivative s) hT using 1; dsimp [P1]; field_simp <;> ring
  have P1_derivative {s : ℝ} (hT : T s ≠ 0) (i : Fin 6) : HasDerivAt (fun t => P1 t i) (P2 s i) s := by
    have h := ((N1_derivative s i).div (T_derivative s) hT).sub (((N_derivative s i).mul (T1_derivative s)).div ((T_derivative s).pow 2) (pow_ne_zero 2 hT))
    convert! h using 1; dsimp [P2]; try simp only [Pi.pow_apply, Pi.mul_apply]
    norm_num; field_simp <;> ring
  have coordinate_bounds {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1/100) : (∀ i, 9/10 ≤ N s i ∧ N s i ≤ 3 ∧ |N1 s i| ≤ 3 ∧ |N2 i| ≤ 16) ∧
      (13 ≤ T s ∧ T s ≤ 14 ∧ |T1 s| ≤ 9) := by
    constructor
    · intro i
      fin_cases i <;> norm_num [N, N1, N2, n1, n2, abs_le, abs_of_nonneg hs0] <;> (try constructor) <;> (try constructor) <;> (try constructor) <;>
        nlinarith only [hs0, hs, sq_nonneg s]
    · dsimp [T, T1]
      rw [abs_le]
      (try constructor) <;> (try constructor) <;> (try constructor) <;>
        nlinarith only [hs0, hs, sq_nonneg s]
  have abs_sub_bound (x y : ℝ) : |x-y| ≤ |x|+|y| := by simpa only [sub_eq_add_neg, abs_neg] using (abs_add_le x (-y))
  have probability_bounds {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1/100) (i : Fin 6) : 1/30 ≤ P s i ∧ P s i ≤ 1 ∧ |P1 s i| ≤ 1 ∧ |P2 s i| ≤ 3 := by
    rcases coordinate_bounds hs0 hs with ⟨hc, hTlo, hThi, hT1⟩
    rcases hc i with ⟨hNlo, hNhi, hN1, hN2⟩
    have hT : 0 < T s := by linarith only [hTlo]
    have hN : 0 < N s i := by linarith only [hNlo]
    have hNa : |N s i| ≤ 3 := by rwa [abs_of_pos hN]
    have hp : 1/30 ≤ P s i := by dsimp [P]; apply (le_div_iff₀ hT).mpr; nlinarith only [hThi, hNlo]
    have hp1 : P s i ≤ 1 := by dsimp [P]; apply (div_le_iff₀ hT).mpr; linarith only [hNhi, hTlo]
    have hd1 : |P1 s i| ≤ (3/13 + 3*9/(13:ℝ)^2) := by
      calc
        |P1 s i| ≤ |N1 s i / T s| + |N s i * T1 s / (T s)^2| := abs_sub_bound _ _
        _ = |N1 s i| / T s + |N s i| * |T1 s| / (T s)^2 := by rw [abs_div, abs_div, abs_mul, abs_pow, abs_of_pos hT]
        _ ≤ 3/13 + 3*9/(13:ℝ)^2 := by gcongr
    have hd2 : |P2 s i| ≤ (16/13 + 2*3*9/(13:ℝ)^2 + 3*68/(13:ℝ)^2 + 2*3*9^2/(13:ℝ)^3) := by
      calc
        |P2 s i| ≤ |N2 i / T s| + |2*N1 s i*T1 s/(T s)^2| +
            |N s i*(-68)/(T s)^2| + |2*N s i*(T1 s)^2/(T s)^3| := by
          exact (abs_add_le _ _).trans (add_le_add ((abs_sub_bound _ _).trans (add_le_add (abs_sub_bound _ _) le_rfl)) le_rfl)
        _ = |N2 i| / T s + 2*|N1 s i| *|T1 s|/(T s)^2 +
            |N s i| *68/(T s)^2 + 2*|N s i| *|T1 s|^2/(T s)^3 := by
          simp only [abs_div, abs_mul, abs_pow, abs_of_pos hT]; norm_num
        _ ≤ 16/13 + 2*3*9/(13:ℝ)^2 + 3*68/(13:ℝ)^2 + 2*3*9^2/(13:ℝ)^3 := by gcongr
    exact ⟨hp, hp1, by norm_num at hd1 ⊢; linarith only [hd1], by norm_num at hd2 ⊢; linarith only [hd2]⟩
  have E_derivative {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1/100) : HasDerivAt E (E1 s) s := by
    have hT := (T_pos_small hs0 hs).ne'
    have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      (Real.hasDerivAt_negMulLog (by
        have := (probability_bounds hs0 hs i).1
        linarith only [this] : P s i ≠ 0)).comp s (P_derivative hT i))
    convert! h.div_const (Real.log 2) using 1; dsimp [E1]; rw [← Finset.sum_neg_distrib]
    congr 2
    funext i; ring
  have E1_derivative {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1/100) : HasDerivAt E1 (E2 s) s := by
    have hT := (T_pos_small hs0 hs).ne'
    have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      (P1_derivative hT i).mul (((Real.hasDerivAt_log (by
          have := (probability_bounds hs0 hs i).1
          linarith only [this] : P s i ≠ 0)).comp s (P_derivative hT i)).add_const 1))
    convert! h.neg.div_const (Real.log 2) using 1; dsimp [E2]
    congr 2
    apply Finset.sum_congr rfl; intro i _
    try simp only [Function.comp_apply]
    ring
  have E2_bound {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1/100) : ‖E2 s‖ ≤ 1000 / Real.log 2 := by
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hterm : ∀ i : Fin 6,
        |P2 s i * (Real.log (P s i) + 1) + (P1 s i)^2 / P s i| ≤ 123 := by
      intro i
      rcases probability_bounds hs0 hs i with ⟨hp, hp1, hd1, hd2⟩
      have hpos : 0 < P s i := by linarith only [hp]
      have hinv : (P s i)⁻¹ ≤ 30 := by
        have h : (1 : ℝ) / P s i ≤ 30 := (div_le_iff₀ hpos).mpr (by nlinarith only [hp])
        simpa only [one_div] using h
      have hlog : |Real.log (P s i) + 1| ≤ 31 := by
        have hlo := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
        rw [Real.log_inv] at hlo
        have hhi := Real.log_nonpos hpos.le hp1
        rw [abs_le]
        constructor <;> linarith only [hlo, hhi, hinv]
      calc
        |P2 s i * (Real.log (P s i) + 1) + (P1 s i)^2 / P s i| ≤
            |P2 s i| * |Real.log (P s i) + 1| + |P1 s i|^2 / P s i := by
          have hdiv : |(P1 s i)^2 / P s i| = |P1 s i|^2 / P s i := by rw [abs_div, abs_pow, abs_of_pos hpos]
          calc
            _ ≤ |P2 s i * (Real.log (P s i) + 1)| + |(P1 s i)^2 / P s i| := abs_add_le _ _
            _ = _ := by rw [abs_mul, hdiv]
        _ ≤ 3*31 + 1^2/(1/30 : ℝ) := by gcongr
        _ = 123 := by norm_num
    have hsum : |∑ i, (P2 s i * (Real.log (P s i) + 1) + (P1 s i)^2 / P s i)| ≤ 738 := by
      calc
        _ ≤ ∑ i, |P2 s i * (Real.log (P s i) + 1) + (P1 s i)^2 / P s i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin 6, (123 : ℝ) := Finset.sum_le_sum (fun i _ => hterm i)
        _ = 738 := by norm_num
    dsimp only [E2]; rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hl2]
    exact (div_le_div_iff_of_pos_right hl2).mpr (by linarith only [hsum])
  let X (s : ℝ) := (B s)⁻¹ *ᵥ degrees
  let F (s : ℝ) := entropyBits (fun i => X s i / ∑ j, X s j)
  have inverse_extension {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1/100) : X s = (1 / C s) • N s := by
    have hu := witness_isUnit hs0 (by linarith only [hs])
    have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hu
    apply Matrix.mulVec_injective_iff_isUnit.mpr hu; dsimp only [X]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec, Matrix.mulVec_smul, (direct_coordinate_certificate s).1, smul_smul,
      one_div_mul_cancel (C_pos_small hs0 hs).ne', one_smul]
  have rational_extension_agrees {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1/100) : E s = F s := by
    dsimp only [E, F]; rw [inverse_extension hs0 hs]
    congr 1
    funext i; dsimp only [P]; simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    rw [(direct_coordinate_certificate s).2]; exact (mul_div_mul_left (N s i) (T s) (one_div_ne_zero (C_pos_small hs0 hs).ne')).symm
  have E_origin_slope : E1 0 = Real.log (27/2) / (49 * Real.log 2) := by
    have hd : graphDegrees sourceGraph = degrees := by
      change A *ᵥ ones = degrees; exact degree_formula
    have ha : graphAdj sourceGraph = A := rfl
    have hF : HasDerivAt F (Real.log (27/2) / (49 * Real.log 2)) 0 := by simpa only [F, X, B, hd, ha] using! witness_origin_derivative.1
    have hFE : HasDerivWithinAt E (Real.log (27/2) / (49 * Real.log 2)) (Set.Icc 0 (1/100 : ℝ)) 0 := hF.hasDerivWithinAt.congr_of_mem
        (fun s hs => rational_extension_agrees hs.1 hs.2) ⟨le_rfl, by norm_num⟩
    have hu : UniqueDiffWithinAt ℝ (Set.Icc 0 (1/100 : ℝ)) 0 := uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1/100) 0 ⟨le_rfl, by norm_num⟩
    exact ((E_derivative (by norm_num) (by norm_num)).hasDerivWithinAt.derivWithin hu).symm.trans (hFE.derivWithin hu)
  have E1_positive {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 1/5000000) : 0 < E1 s := by
    have hsmall : s ≤ 1/100 := by linarith only [hs]
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hcontrol := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.Icc 0 (1/100 : ℝ)) (f := E1) (f' := E2)
      (fun t ht => (E1_derivative ht.1 ht.2).hasDerivWithinAt)
      (fun t ht => E2_bound ht.1 ht.2) (convex_Icc 0 (1/100 : ℝ))
      (show (0 : ℝ) ∈ Set.Icc 0 (1/100 : ℝ) from ⟨le_rfl, by norm_num⟩)
      (show s ∈ Set.Icc 0 (1/100 : ℝ) from ⟨hs0, hsmall⟩)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg hs0] at hcontrol
    have hlo := (abs_le.mp hcontrol).1
    have horigin : 1/(100*Real.log 2) < E1 0 := by
      rw [E_origin_slope]; exact witness_origin_derivative.2
    have hmargin : (1000 / Real.log 2)*s < 1/(100*Real.log 2) := by
      apply (mul_lt_mul_iff_of_pos_right hl2).mp; field_simp; nlinarith only [hs]
    linarith only [hlo, horigin, hmargin]
  have rational_whole_interval (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1/5000000) : E a < E b := by
    have hmono : StrictMonoOn E (Set.Ioo 0 (1/5000000 : ℝ)) := strictMonoOn_of_deriv_pos (convex_Ioo 0 (1/5000000 : ℝ))
        (fun t ht => (E_derivative ht.1.le (by linarith only [ht.2])).continuousAt.continuousWithinAt)
        (by
          intro t ht; rw [interior_Ioo] at ht; rw [(E_derivative ht.1.le (by linarith only [ht.2])).deriv]
          exact E1_positive ht.1.le ht.2)
    exact hmono ⟨ha, lt_trans hab hb⟩ ⟨lt_trans ha hab, hb⟩ hab
  have whole_base_interval (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1/5000000) : a < -1 / spectralMinimum sourceGraph ∧ b < -1 / spectralMinimum sourceGraph ∧
      (∀ i, 0 < graphGamma sourceGraph a i ∧ graphGamma sourceGraph a i < 1) ∧ (∀ i, 0 < graphGamma sourceGraph b i ∧ graphGamma sourceGraph b i < 1) ∧
      graphEntropyBits sourceGraph a < graphEntropyBits sourceGraph b := by
    have hapos : 0 < a := ha
    have hbpos : 0 < b := lt_trans ha hab
    have hal : a ≤ 1/100 := by linarith only [hab, hb]
    have hbl : b ≤ 1/100 := by linarith only [hb]
    refine ⟨witness_stable ha (by linarith only [hal]), witness_stable hbpos (by linarith only [hbl]),
      (small_score_certificate ha hal).1, (small_score_certificate hbpos hbl).1, ?_⟩
    have hea : graphEntropyBits sourceGraph a = E a := by
      unfold graphEntropyBits; rw [(small_score_certificate ha hal).2]
    have heb : graphEntropyBits sourceGraph b = E b := by
      unfold graphEntropyBits; rw [(small_score_certificate hbpos hbl).2]
    rw [hea, heb]; exact rational_whole_interval a b ha hab hb
  have clone_whole_interval (m : ℕ) (hm : 0 < m) (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < (1/5000000) / (m : ℝ)) :
      a < -1 / spectralMinimum (cloneGraph m) ∧ b < -1 / spectralMinimum (cloneGraph m) ∧
      (∀ i, 0 < graphGamma (cloneGraph m) a i ∧ graphGamma (cloneGraph m) a i < 1) ∧ (∀ i, 0 < graphGamma (cloneGraph m) b i ∧ graphGamma (cloneGraph m) b i < 1) ∧
      graphEntropyBits (cloneGraph m) a < graphEntropyBits (cloneGraph m) b := by
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hbpos := lt_trans ha hab
    have hmb : (m : ℝ)*b < 1/5000000 := by simpa only [mul_comm] using (lt_div_iff₀ hm').mp hb
    have hma : 0 < (m : ℝ)*a := mul_pos hm' ha
    have hmab : (m : ℝ)*a < (m : ℝ)*b := mul_lt_mul_of_pos_left hab hm'
    have hal : a < 1/(3*(m : ℝ)) := by
      apply (lt_div_iff₀ (by positivity : 0 < 3*(m : ℝ))).mpr; nlinarith only [hma, hmab, hmb]
    have hbl : b < 1/(3*(m : ℝ)) := by
      apply (lt_div_iff₀ (by positivity : 0 < 3*(m : ℝ))).mpr; nlinarith only [hmb]
    rcases whole_base_interval ((m : ℝ)*a) ((m : ℝ)*b) hma hmab hmb with ⟨_, _, hascores, hbscores, hinc⟩
    refine ⟨clone_stable m hm ha hal, clone_stable m hm hbpos hbl, ?_, ?_, ?_⟩
    · rw [clone_inverse_replication m hm ha hal]
      exact fun i => hascores i.1
    · rw [clone_inverse_replication m hm hbpos hbl]
      exact fun i => hbscores i.1
    · rw [clone_actual_entropy_identity m hm ha hal, clone_actual_entropy_identity m hm hbpos hbl]
      simpa only [add_comm] using add_lt_add_right hinc (Real.log (m : ℝ) / Real.log 2)
  have pair_score_bounds : (∀ i, 0 < graphGamma sourceGraph (1/20) i ∧ graphGamma sourceGraph (1/20) i < 1) ∧
      (∀ i, 0 < graphGamma sourceGraph (1/6) i ∧ graphGamma sourceGraph (1/6) i < 1) := by
    constructor
    · intro i
      rw [actual_pair_certificate.1]; fin_cases i <;> norm_num
    · intro i
      rw [actual_pair_certificate.2.1]; fin_cases i <;> norm_num
  have clone_pair_scores (m : ℕ) (hm : 0 < m) : (∀ i, 0 < graphGamma (cloneGraph m) (1/(20*(m : ℝ))) i ∧ graphGamma (cloneGraph m) (1/(20*(m : ℝ))) i < 1) ∧
      (∀ i, 0 < graphGamma (cloneGraph m) (1/(6*(m : ℝ))) i ∧ graphGamma (cloneGraph m) (1/(6*(m : ℝ))) i < 1) := by
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have h20 : 0 < 1/(20*(m : ℝ)) := by positivity
    have h6 : 0 < 1/(6*(m : ℝ)) := by positivity
    have h20lt : 1/(20*(m : ℝ)) < 1/(3*(m : ℝ)) := by
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr; nlinarith only [hm']
    have h6lt : 1/(6*(m : ℝ)) < 1/(3*(m : ℝ)) := by
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr; nlinarith only [hm']
    have he20 : (m : ℝ)*(1/(20*(m : ℝ))) = 1/20 := by field_simp
    have he6 : (m : ℝ)*(1/(6*(m : ℝ))) = 1/6 := by field_simp
    rw [clone_inverse_replication m hm h20 h20lt, clone_inverse_replication m hm h6 h6lt, he20, he6]
    exact ⟨fun i => pair_score_bounds.1 i.1, fun i => pair_score_bounds.2 i.1⟩
  have source_certificates : (∀ n : ℕ, 0 < n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], Nonregular G → ∀ s : ℝ, 0 < s → s < -1 / spectralMinimum G →
        IsUnit (1 + s • graphAdj G) ∧ (1 + s • graphAdj G) *ᵥ graphGamma G s = s • graphDegrees G ∧ 0 < ∑ i, clipped (graphGamma G s) i) ∧
    (∀ n : ℕ, 0 < n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ i, 0 < graphDegrees G i) →
      let d := graphDegrees G
      let q := graphAdj G *ᵥ d
      let D := ∑ i, d i
      let Q := ∑ i, q i
      let x := fun s : ℝ => (1 + s • graphAdj G)⁻¹ *ᵥ d
      let p := fun s i => x s i / ∑ j, x s j
      let w := fun i => d i / D
      let r := fun i => q i / d i
      let cov := (∑ i, w i * r i * Real.log (d i)) - (∑ i, w i * r i) * (∑ i, w i * Real.log (d i))
      (∀ i, HasDerivAt (fun s => p s i) ((Q * d i - D * q i) / D^2) 0) ∧ HasDerivAt (fun s => entropyBits (p s)) (cov / Real.log 2) 0 ∧ Q = ∑ i, (d i)^2 ∧
      (∀ᶠ s in nhds (0 : ℝ), 0 < s → graphEntropyBits G s = entropyBits (p s))) ∧
    (∃ (G : SimpleGraph (Fin 6)) (dec : DecidableRel G.Adj),
      letI : DecidableRel G.Adj := dec
      G.Connected ∧ Nonregular G ∧ (-3 ≤ spectralMinimum G ∧ spectralMinimum G ≤ -1) ∧ (graphGamma G (1/20) = (1/4357 : ℝ) • ![(397 : ℝ),577,577,378,576,198] ∧
       graphGamma G (1/6) = (1/129 : ℝ) • ![(33 : ℝ),45,45,28,44,16] ∧ normalized (graphGamma G (1/20)) = (1/2703 : ℝ) • ![(397 : ℝ),577,577,378,576,198] ∧
       normalized (graphGamma G (1/6)) = (1/211 : ℝ) • ![(33 : ℝ),45,45,28,44,16]) ∧
      1 / (500 * Real.log 2) < graphEntropyBits G (1/6) - graphEntropyBits G (1/20) ∧ (∀ s : ℝ, 0 < s → s ≤ 1/100 →
        (∀ i, 0 < graphGamma G s i ∧ graphGamma G s i < 1) ∧ ∑ i, normalized (graphGamma G s) i = 1) ∧
      (let x := fun s : ℝ => (1 + s • graphAdj G)⁻¹ *ᵥ graphDegrees G
       let p := fun s i => x s i / ∑ j, x s j
       HasDerivAt (fun s => entropyBits (p s)) (Real.log (27/2) / (49 * Real.log 2)) 0 ∧ 1 / (100 * Real.log 2) < Real.log (27/2) / (49 * Real.log 2)) ∧
      (∀ a b : ℝ, 0 < a → a < b → b < 1/5000000 → a < -1 / spectralMinimum G ∧ b < -1 / spectralMinimum G ∧ (∀ i, 0 < graphGamma G a i ∧ graphGamma G a i < 1) ∧
        (∀ i, 0 < graphGamma G b i ∧ graphGamma G b i < 1) ∧ graphEntropyBits G a < graphEntropyBits G b) ∧
      (∀ m : ℕ, 0 < m → ∃ (Gm : SimpleGraph (Fin 6 × Fin m)) (decm : DecidableRel Gm.Adj),
        letI : DecidableRel Gm.Adj := decm
        (∀ u v, Gm.Adj u v ↔ G.Adj u.1 v.1) ∧ Gm.Connected ∧ Nonregular Gm ∧ Fintype.card (Fin 6 × Fin m) = 6*m ∧
        (-3*(m : ℝ) ≤ spectralMinimum Gm ∧ spectralMinimum Gm ≤ -(m : ℝ)) ∧ (∀ s : ℝ, 0 < s → s < 1 / (3*(m : ℝ)) → s < -1 / spectralMinimum Gm ∧
          graphGamma Gm s = (fun i => graphGamma G ((m : ℝ)*s) i.1) ∧ normalized (graphGamma Gm s) = (fun i => normalized (graphGamma G ((m : ℝ)*s)) i.1 / (m : ℝ)) ∧
          graphEntropyBits Gm s = graphEntropyBits G ((m : ℝ)*s) + Real.log (m : ℝ) / Real.log 2) ∧
        (1 / (20*(m : ℝ))) < 1 / (6*(m : ℝ)) ∧ 0 < 1 / (20*(m : ℝ)) ∧ 1 / (6*(m : ℝ)) < 1 / (3*(m : ℝ)) ∧ 1 / (500 * Real.log 2) <
          graphEntropyBits Gm (1 / (6*(m : ℝ))) - graphEntropyBits Gm (1 / (20*(m : ℝ))) ∧
        (∀ i, 0 < graphGamma Gm (1 / (20*(m : ℝ))) i ∧ graphGamma Gm (1 / (20*(m : ℝ))) i < 1) ∧ (∀ i, 0 < graphGamma Gm (1 / (6*(m : ℝ))) i ∧
          graphGamma Gm (1 / (6*(m : ℝ))) i < 1) ∧
        (∀ a b : ℝ, 0 < a → a < b → b < (1/5000000)/(m : ℝ) → a < -1 / spectralMinimum Gm ∧ b < -1 / spectralMinimum Gm ∧
          (∀ i, 0 < graphGamma Gm a i ∧ graphGamma Gm a i < 1) ∧ (∀ i, 0 < graphGamma Gm b i ∧ graphGamma Gm b i < 1) ∧
          graphEntropyBits Gm a < graphEntropyBits Gm b))) := by
    refine ⟨?_, ?_, ?_⟩
    · intro n hn G dec hG s hs hstable
      letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      exact ⟨stable_isUnit G hs hstable, stable_equilibrium G hs hstable, stable_clipped_mass_pos G hG hs hstable⟩
    · intro n hn G dec hd
      letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      exact ⟨(general_probability_derivative G hd).1, general_covariance_derivative G hd, general_degree_square_sum G, (general_probability_derivative G hd).2⟩
    · refine ⟨sourceGraph, inferInstance, source_connected, source_nonregular, witness_spectral_bounds, actual_pair_certificate, actual_entropy_gap, ?_,
        witness_origin_derivative, whole_base_interval, ?_⟩
      · intro s hs hsmall
        refine ⟨(small_score_certificate hs hsmall).1, ?_⟩
        rw [(small_score_certificate hs hsmall).2, ← Finset.sum_div, (direct_coordinate_certificate s).2]
        exact div_self (T_pos_small hs.le hsmall).ne'
      · intro m hm
        refine ⟨cloneGraph m, inferInstance, (fun _ _ => Iff.rfl), clone_connected m hm, clone_nonregular m hm, ?_, clone_spectral_bounds m hm, ?_, ?_, ?_, ?_,
          clone_exact_gap m hm, (clone_pair_scores m hm).1, (clone_pair_scores m hm).2, clone_whole_interval m hm⟩
        · simp [Fintype.card_prod, Fintype.card_fin]
        · intro s hs hsmall
          refine ⟨clone_stable m hm hs hsmall, clone_inverse_replication m hm hs hsmall, ?_, clone_actual_entropy_identity m hm hs hsmall⟩
          rw [clone_inverse_replication m hm hs hsmall, clone_probability_replication]
        · exact (clone_certificate m hm).2.2.1
        · exact (clone_certificate m hm).2.2.2.1
        · exact (clone_certificate m hm).2.2.2.2
  intro hclaim
  rcases source_certificates with ⟨_hglobal, _hcovariance, G, dec, hconnected, hnonregular, hspectral,
      _hcoordinates, _hbasegap, _hscores, _horigin, _hbaseinterval, hfamily⟩
  letI : DecidableRel G.Adj := dec
  rcases hfamily 1 (by norm_num) with ⟨G1, dec1, _hadjacency, _hconnected1, _hnonregular1, _hcard1, _hspectral1,
      hreplication, _horder1, _hpositive1, _hstable1, hpairgap1, _hpair20, _hpair6, hwholeinterval1⟩
  letI : DecidableRel G1.Adj := dec1
  have transfer (s : ℝ) (hs : 0 < s) (hsmall : s < 1/3) : graphEntropyBits G1 s = graphEntropyBits G s := by
    simpa only [Nat.cast_one, mul_one, one_mul, Real.log_one, zero_div, add_zero]
      using (hreplication s hs (by simpa only [Nat.cast_one, mul_one] using hsmall)).2.2.2
  have stable_base {s : ℝ} (hs : 0 < s) (hsmall : s < 1/3) : s < -1 / spectralMinimum G := by
    have hn : spectralMinimum G < 0 := lt_of_le_of_lt hspectral.2 (by norm_num)
    apply (lt_div_iff_of_neg hn).mpr
    have hmul := mul_le_mul_of_nonneg_left hspectral.1 hs.le
    nlinarith only [hmul, hsmall]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have pair_increment : 0 < graphEntropyBits G (1/6) - graphEntropyBits G (1/20) := by
    norm_num only [Nat.cast_one, mul_one] at hpairgap1
    rw [transfer (1/6) (by norm_num) (by norm_num), transfer (1/20) (by norm_num) (by norm_num)] at hpairgap1
    exact lt_trans (by positivity) hpairgap1
  have interval_increment : 0 < graphEntropyBits G (1/7500000) - graphEntropyBits G (1/15000000) := by
    have h := (hwholeinterval1 (1/15000000) (1/7500000) (by norm_num) (by norm_num) (by norm_num)).2.2.2.2
    rw [transfer (1/15000000) (by norm_num) (by norm_num), transfer (1/7500000) (by norm_num) (by norm_num)] at h; exact sub_pos.mpr h
  have pair_nonpositive : graphEntropyBits G (1/6) - graphEntropyBits G (1/20) ≤ 0 := sub_nonpos.mpr (hclaim 6 (by norm_num) G hconnected hnonregular (1/20) (1/6)
      (by norm_num) (stable_base (by norm_num) (by norm_num))
      (by norm_num) (stable_base (by norm_num) (by norm_num)) (by norm_num))
  have interval_nonpositive : graphEntropyBits G (1/7500000) - graphEntropyBits G (1/15000000) ≤ 0 :=
    sub_nonpos.mpr (hclaim 6 (by norm_num) G hconnected hnonregular (1/15000000) (1/7500000) (by norm_num) (stable_base (by norm_num) (by norm_num))
      (by norm_num) (stable_base (by norm_num) (by norm_num)) (by norm_num))
  have hnonpositive := add_nonpos pair_nonpositive interval_nonpositive
  have hpositive := add_pos pair_increment interval_increment
  linarith only [hnonpositive, hpositive]
#check result
#print axioms result
end D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation
