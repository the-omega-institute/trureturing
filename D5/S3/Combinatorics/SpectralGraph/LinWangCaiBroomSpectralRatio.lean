/- GID: D5/S3/Combinatorics/SpectralGraph/LinWangCaiBroomSpectralRatio
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/LinWangCaiBroomSpectralRatio
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/SpectralGraph/LinWangCaiBroomSpectralRatio.claim; result=D5/S3/Combinatorics/SpectralGraph/LinWangCaiBroomSpectralRatio.result; claim=D5/S3/Combinatorics/SpectralGraph/LinWangCaiBroomSpectralRatio.claim
   digest: The order-19 broom with seven leaves has larger Laplacian ratio than with eight. -/

/- Judgement form.
   admission_basis: open-problem-resolution (#19460; Refuted)
   Direct frozen dependencies: D5/S3/Weil/ZetaLinear/Sylvester;
   RHLinalg.hermForm_le_of_eigenvalues_le; declaration statement_id: sha256:c7db3b66a76717eeab3df89fca20f9a9468c477ecc8b249c5b35e56fe728d5e2.
   Definitions and the named decidability instance: proof_shape: bind-only; escape_witness: none.
   rayleigh_le_top: proof_shape: bind-only; escape_witness: none; consumers: broom7_large_bound.
   eigenvector_sorted: proof_shape: bind-only; escape_witness: none; consumers: eigenvalue_lt_of_posDef, lapVec_eigen.
   eigenvalue_lt_of_posDef: proof_shape: bind-only; escape_witness: none; consumers: broom8_large_bound.
   pd_of_rat_certificate: proof_shape: bind-only; escape_witness: none; consumers: certHigh_posDef, certLow_posDef.
   eigenvalue_nonneg_of_psd: proof_shape: bind-only; escape_witness: none; consumers: lapEig_nonneg.
   rayleigh_ge_of_support: proof_shape: bind-only; escape_witness: none; consumers: lap_rayleigh_lower.
   broom_connected: proof_shape: bind-only; escape_witness: none; consumers: broom7_tree, broom8_tree.
   broom7_tree: proof_shape: bind-only; escape_witness: none; consumers: broom7_small_bound, broom_ratio_strict, result.
   broom8_tree: proof_shape: bind-only; escape_witness: none; consumers: broom8_small_bound.
   lapEig_eq_eigenvalues: proof_shape: bind-only; escape_witness: none; consumers: lapVec_eigen, lapEig_nonneg, lap_rayleigh_lower, broom8_large_bound.
   lapVec_eigen: proof_shape: bind-only; escape_witness: none; consumers: lapVec_last_constant, lapEig_pos, lap_second_gt_of_posDef.
   lapVec_ne_zero: proof_shape: bind-only; escape_witness: none; consumers: lapVec_last_entry_ne_zero, lapEig_pos, lap_second_gt_of_posDef.
   lapVec_dot: proof_shape: bind-only; escape_witness: none; consumers: lapVec_sum_zero, lap_second_gt_of_posDef.
   lapEig_nonneg: proof_shape: bind-only; escape_witness: none; consumers: lapEig_last_zero, lapEig_pos.
   lapEig_last_zero: proof_shape: bind-only; escape_witness: none; consumers: lapVec_last_constant.
   lap_kernel_constant: proof_shape: bind-only; escape_witness: none; consumers: lapVec_last_constant, lapEig_pos.
   lapVec_last_constant: proof_shape: bind-only; escape_witness: none; consumers: lapVec_last_entry_ne_zero, lapVec_sum_zero, lap_rayleigh_lower.
   lapVec_last_entry_ne_zero: proof_shape: bind-only; escape_witness: none; consumers: lapVec_sum_zero.
   lapVec_sum_zero: proof_shape: bind-only; escape_witness: none; consumers: lapEig_pos, lap_second_gt_of_posDef.
   lapEig_pos: proof_shape: bind-only; escape_witness: none; consumers: broom_ratio_strict.
   lap_rayleigh_lower: proof_shape: bind-only; escape_witness: none; consumers: broom7_small_bound.
   lap_second_gt_of_posDef: proof_shape: bind-only; escape_witness: none; consumers: broom8_small_bound.
   ratios_separated: proof_shape: bind-only; escape_witness: none; consumers: broom_ratio_strict.
   lapMatrix_rat_cast: proof_shape: bind-only; escape_witness: none; consumers: rat_quadratic_cast, certHigh_real, certLow_real.
   rat_quadratic_cast: proof_shape: bind-only; escape_witness: none; consumers: small_energy_real, large_energy_real.
   small_norm_rat: proof_shape: bind-only; escape_witness: none; consumers: small_norm_real.
   small_energy_rat: proof_shape: bind-only; escape_witness: none; consumers: small_energy_real.
   small_norm_real: proof_shape: bind-only; escape_witness: none; consumers: broom7_small_bound.
   small_energy_real: proof_shape: bind-only; escape_witness: none; consumers: broom7_small_bound.
   large_norm_rat: proof_shape: bind-only; escape_witness: none; consumers: large_norm_real.
   large_energy_rat: proof_shape: bind-only; escape_witness: none; consumers: large_energy_real.
   large_norm_real: proof_shape: bind-only; escape_witness: none; consumers: broom7_large_bound.
   large_energy_real: proof_shape: bind-only; escape_witness: none; consumers: broom7_large_bound.
   small_sum_rat: proof_shape: bind-only; escape_witness: none; consumers: small_sum_real.
   small_sum_real: proof_shape: bind-only; escape_witness: none; consumers: broom7_small_bound.
   broom7_small_bound: proof_shape: bind-only; escape_witness: none; consumers: broom_ratio_strict.
   broom7_large_bound: proof_shape: bind-only; escape_witness: none; consumers: broom_ratio_strict.
   certHigh_inv: proof_shape: bind-only; escape_witness: none; consumers: certHigh_posDef.
   certHigh_factor: proof_shape: bind-only; escape_witness: none; consumers: certHigh_posDef.
   certHigh_positive: proof_shape: bind-only; escape_witness: none; consumers: certHigh_posDef.
   certHigh_posDef: proof_shape: bind-only; escape_witness: none; consumers: broom8_large_bound.
   certLow_inv: proof_shape: bind-only; escape_witness: none; consumers: certLow_posDef.
   certLow_factor: proof_shape: bind-only; escape_witness: none; consumers: certLow_posDef.
   certLow_positive: proof_shape: bind-only; escape_witness: none; consumers: certLow_posDef.
   certLow_posDef: proof_shape: bind-only; escape_witness: none; consumers: broom8_small_bound.
   certHigh_real: proof_shape: bind-only; escape_witness: none; consumers: broom8_large_bound.
   certLow_real: proof_shape: bind-only; escape_witness: none; consumers: broom8_small_bound.
   broom8_large_bound: proof_shape: bind-only; escape_witness: none; consumers: broom_ratio_strict.
   broom8_small_bound: proof_shape: bind-only; escape_witness: none; consumers: broom_ratio_strict.
   broom_ratio_strict: proof_shape: bind-only; escape_witness: none; consumers: result.
   result: proof_shape: bind-only; escape_witness: none; consumers: settling result.
   The public result is the designated refutation result (`basis=refutes`) and is exempt from
   four-slot escape registration (CLAUDE.md §3.9).
-/

import D5.S3.Weil.ZetaLinear.Sylvester
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Star

/-! Definitions from Z. Lin, J. Wang and M. Cai, "The Laplacian spectral ratio of connected graphs",
arXiv:2302.10491v1: the Laplacian matrix `L(G) = D(G) − A(G)`, its eigenvalues `µ_1(G) ≥ ⋯ ≥ µ_n(G)`, the Laplacian
spectral ratio `R_L(G) = µ_1(G)/µ_{n−1}(G)`, the star `K_{1,n−1}`, the broom tree `B_n^t` (Figure 2), and
Conjecture 5.4. -/

namespace D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio

open Matrix

/-- `µ_{i+1}(G)`: the Laplacian eigenvalues of `G`, with multiplicity, in non-increasing order
`µ_1(G) ≥ µ_2(G) ≥ ⋯ ≥ µ_n(G)`. -/
noncomputable def lapEig {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i : Fin n) : ℝ :=
  (G.isHermitian_lapMatrix ℝ).eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i)

/-- `R_L(G) = µ_1(G)/µ_{n−1}(G)`, the Laplacian spectral radius over the algebraic connectivity (`n ≥ 2`). -/
noncomputable def spectralRatio {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℝ :=
  if h : 2 ≤ n then lapEig G ⟨0, by omega⟩ / lapEig G ⟨n - 2, by omega⟩ else 0

/-- The broom tree `B_n^t` with the labels of Figure 2: the star `K_{1,t}` has center `v_0` and pendant vertices
`v_1, …, v_t`; the path `P_{n−t−1}` is `v_{t+1} v_{t+2} ⋯ v_{n−1}`; and the pendant vertex `v_{t+1}` of the path is
joined to the center `v_0` by an edge. -/
def broom (n t : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j : Fin n =>
    (i.val = 0 ∧ 1 ≤ j.val ∧ j.val ≤ t + 1) ∨ (t + 1 ≤ i.val ∧ i.val + 1 = j.val)

private instance broomAdjDecidable (n t : ℕ) : DecidableRel (broom n t).Adj := by
  unfold broom; infer_instance

/-- The upper-bound parameter of Conjecture 5.4: `(n − 3)/2` for odd `n` and `(n − 4)/2` for even `n`. -/
def conjParam (n : ℕ) : ℕ := if n % 2 = 1 then (n - 3) / 2 else (n - 4) / 2

/-- Conjecture 5.4: for every tree `T` with `n ≥ 8` vertices, `R_L(K_{1,n−1}) ≤ R_L(T) ≤ R_L(B_n^{(n−3)/2})` (`n`
odd) or `R_L(B_n^{(n−4)/2})` (`n` even); the left (right) equality holds if and only if `T` is (isomorphic to)
`K_{1,n−1}` (that broom). -/
def claim : Prop :=
  ∀ (n : ℕ) (hn : 8 ≤ n) (T : SimpleGraph (Fin n)) [DecidableRel T.Adj], T.IsTree →
    spectralRatio (SimpleGraph.starGraph (⟨0, by omega⟩ : Fin n)) ≤ spectralRatio T ∧
    spectralRatio T ≤ spectralRatio (broom n (conjParam n)) ∧
    (spectralRatio T = spectralRatio (SimpleGraph.starGraph (⟨0, by omega⟩ : Fin n)) ↔
      Nonempty (T ≃g SimpleGraph.starGraph (⟨0, by omega⟩ : Fin n))) ∧
    (spectralRatio T = spectralRatio (broom n (conjParam n)) ↔ Nonempty (T ≃g broom n (conjParam n)))

end D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio

open Matrix Finset
open scoped InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio
variable {m : Type*} [Fintype m] [DecidableEq m] {A : Matrix m m ℝ}


private lemma rayleigh_le_top [Nonempty m] (hA : A.IsHermitian) (x : m → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ hA.eigenvalues₀ ⟨0, Fintype.card_pos⟩ * (x ⬝ᵥ x) := by
  have h := RHLinalg.hermForm_le_of_eigenvalues_le hA
    (θ := hA.eigenvalues₀ ⟨0, Fintype.card_pos⟩)
    (fun i => hA.eigenvalues₀_antitone (Fin.zero_le _)) x
  simpa only [RHLinalg.hermForm, star_trivial, RCLike.re_to_real,
    Real.norm_eq_abs, sq_abs, dotProduct, ← pow_two] using h

private lemma eigenvector_sorted (hA : A.IsHermitian) (i : Fin (Fintype.card m)) :
    A *ᵥ WithLp.ofLp (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace) i) =
      hA.eigenvalues₀ i • WithLp.ofLp (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace) i) := by
  have h := congrArg WithLp.ofLp ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).apply_eigenvectorBasis finrank_euclideanSpace i)
  simpa only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul,
    Matrix.IsHermitian.eigenvalues₀, RCLike.ofReal_real_eq_id, id_eq] using h

private lemma eigenvalue_lt_of_posDef (hA : A.IsHermitian) (d : ℝ)
    (hD : (d • (1 : Matrix m m ℝ) - A).PosDef) (i : Fin (Fintype.card m)) :
    hA.eigenvalues₀ i < d := by
  let v := WithLp.ofLp (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace) i)
  have hv : v ≠ 0 := (WithLp.ofLp_eq_zero 2).ne.mpr ((((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace)).orthonormal.ne_zero i)
  have hq := hD.dotProduct_mulVec_pos hv
  have he := eigenvector_sorted hA i
  change A *ᵥ v = hA.eigenvalues₀ i • v at he
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, he,
    star_trivial, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hq
  have hn : 0 < v ⬝ᵥ v := by simpa only [star_trivial] using (dotProduct_star_self_pos_iff.mpr hv)
  nlinarith

private lemma pd_of_rat_certificate {n : ℕ} (M U V : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ)
    (hUV : U * V = 1) (hM : M = U * diagonal d * U.transpose) (hd : ∀ i, 0 < d i) :
    (M.map (Rat.castHom ℝ)).PosDef := by
  let f := Rat.castHom ℝ
  have huv : U.map f * V.map f = 1 := by
    simpa [Matrix.map_mul] using congrArg (fun N : Matrix (Fin n) (Fin n) ℚ => N.map f) hUV
  have hinj : Function.Injective (U.map f).vecMul := by
    intro x y h
    have hh := congrArg (fun z => z ᵥ* V.map f) h
    simpa only [vecMul_vecMul, huv, vecMul_one] using hh
  have hdiag : (diagonal (fun i => (d i : ℝ))).PosDef :=
    Matrix.PosDef.diagonal (fun i => by exact_mod_cast hd i)
  have hh := hdiag.mul_mul_conjTranspose_same hinj
  have hcast : M.map f = U.map f * diagonal (fun i => (d i : ℝ)) * (U.map f)ᴴ := by
    rw [hM, Matrix.map_mul, Matrix.map_mul]
    congr 1
    · ext i j
      by_cases hij : i=j <;> simp [Matrix.map_apply, hij, f]
  rwa [← hcast] at hh
private lemma eigenvalue_nonneg_of_psd (hA : A.IsHermitian) (hP : A.PosSemidef)
    (i : Fin (Fintype.card m)) : 0 ≤ hA.eigenvalues₀ i := by
  let e : Fin (Fintype.card m) ≃ m := Fintype.equivOfCardEq (Fintype.card_fin _)
  simpa only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply] using hP.eigenvalues_nonneg (e i)

private lemma rayleigh_ge_of_support (hA : A.IsHermitian) (k : Fin (Fintype.card m)) (x : m → ℝ)
    (hz : ∀ i, k < i → (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace)).repr (WithLp.toLp 2 x) i = 0) :
    hA.eigenvalues₀ k * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  let y := WithLp.toLp 2 x
  have he :
      inner ℝ (A.toEuclideanLin y) y =
        ∑ i, hA.eigenvalues₀ i * ((((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace)).repr y i)^2 := by
    rw [← (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace)).repr.inner_map_map (A.toEuclideanLin y) y, PiLp.inner_apply]
    apply sum_congr rfl
    intro i _
    rw [RCLike.inner_apply, (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis_apply_self_apply]
    simp only [RCLike.conj_to_real, RCLike.ofReal_real_eq_id,
      id_eq, Matrix.IsHermitian.eigenvalues₀]
    ring
  have hn :
      ∑ i, ((((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace)).repr y i)^2 = inner ℝ y y := by
    rw [← (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace)).repr.inner_map_map y y, PiLp.inner_apply]
    apply sum_congr rfl
    intro i _
    simp [pow_two]
  have h : (∑ i, hA.eigenvalues₀ k * ((((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace)).repr y i)^2) ≤
      ∑ i, hA.eigenvalues₀ i * ((((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace)).repr y i)^2 := by
    apply sum_le_sum
    intro i _
    by_cases hi : i ≤ k
    · exact mul_le_mul_of_nonneg_right (hA.eigenvalues₀_antitone hi) (sq_nonneg _)
    · rw [hz i (lt_of_not_ge hi)]; simp
  rw [← mul_sum, hn, ← he] at h
  simpa only [y, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply,
    WithLp.ofLp_toLp, star_trivial, dotProduct_comm] using h
end D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio

namespace D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio
private lemma broom_connected (t : ℕ) : (broom 19 t).Connected := by
  have hreach : ∀ k : ℕ, ∀ hk : k < 19, (broom 19 t).Reachable 0 ⟨k,hk⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      by_cases hz : k = 0
      · subst k; exact SimpleGraph.Reachable.rfl
      by_cases hsmall : k ≤ t+1
      · apply SimpleGraph.Adj.reachable
        change (0 : Fin 19) ≠ ⟨k,hk⟩ ∧ _
        constructor
        · intro hh; have := congrArg Fin.val hh; simp at this; omega
        · exact Or.inl (Or.inl ⟨rfl, by change 1 ≤ k; omega, hsmall⟩)
      · have hkprev : k-1 < 19 := Nat.sub_lt_of_lt hk
        exact (ih (k-1) (by omega) hkprev).trans (SimpleGraph.Adj.reachable (by
          change (⟨k-1,hkprev⟩ : Fin 19) ≠ ⟨k,hk⟩ ∧ _
          constructor
          · intro hh; have := congrArg Fin.val hh; simp at this; omega
          · exact Or.inl (Or.inr ⟨by change t+1 ≤ k-1; omega, by change (k-1)+1=k; omega⟩)))
  exact { preconnected := fun u w => (hreach u.val u.isLt).symm.trans (hreach w.val w.isLt) }

private lemma broom7_tree : (broom 19 7).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨broom_connected 7, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

private lemma broom8_tree : (broom 19 8).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨broom_connected 8, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  decide
end D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio
namespace D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio
private lemma lapEig_eq_eigenvalues (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (i : Fin 19) :
    lapEig G i = (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i := by
  exact Real.ext_cauchy rfl

private lemma lapVec_eigen (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (i : Fin 19) :
    G.lapMatrix ℝ *ᵥ (fun (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (i : Fin 19) => WithLp.ofLp (((Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).eigenvectorBasis finrank_euclideanSpace) i)) G i = lapEig G i • (fun (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (i : Fin 19) => WithLp.ofLp (((Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).eigenvectorBasis finrank_euclideanSpace) i)) G i := by
  simpa only [lapEig_eq_eigenvalues] using eigenvector_sorted (G.isHermitian_lapMatrix ℝ) i

private lemma lapVec_ne_zero (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (i : Fin 19) : (fun (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (i : Fin 19) => WithLp.ofLp (((Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).eigenvectorBasis finrank_euclideanSpace) i)) G i ≠ 0 :=
  (WithLp.ofLp_eq_zero 2).ne.mpr ((((Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).eigenvectorBasis finrank_euclideanSpace)).orthonormal.ne_zero i)

private lemma lapVec_dot (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (i j : Fin 19) :
    (fun (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (i : Fin 19) => WithLp.ofLp (((Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).eigenvectorBasis finrank_euclideanSpace) i)) G i ⬝ᵥ (fun (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (i : Fin 19) => WithLp.ofLp (((Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).eigenvectorBasis finrank_euclideanSpace) i)) G j = if i=j then 1 else 0 := by
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
    using orthonormal_iff_ite.mp (((Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).eigenvectorBasis finrank_euclideanSpace)).orthonormal i j

private lemma lapEig_nonneg (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (i : Fin 19) : 0 ≤ lapEig G i := by
  simpa only [lapEig_eq_eigenvalues] using eigenvalue_nonneg_of_psd (G.isHermitian_lapMatrix ℝ)
    (G.posSemidef_lapMatrix ℝ) i

private lemma lapEig_last_zero (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] : lapEig G 18 = 0 := by
  have hz := G.zero_mem_spectrum_lapMatrix ℝ
  rw [(G.isHermitian_lapMatrix ℝ).spectrum_real_eq_range_eigenvalues] at hz
  obtain ⟨i, hi⟩ := hz
  have hlo : (G.isHermitian_lapMatrix ℝ).eigenvalues₀ (18 : Fin 19) ≤
      (G.isHermitian_lapMatrix ℝ).eigenvalues i := by
    apply (G.isHermitian_lapMatrix ℝ).eigenvalues₀_antitone
    exact Fin.le_last _
  have hn := lapEig_nonneg G 18
  change 0 ≤ (G.isHermitian_lapMatrix ℝ).eigenvalues₀ (18 : Fin 19) at hn
  change (G.isHermitian_lapMatrix ℝ).eigenvalues₀ (18 : Fin 19) = 0
  linarith

private lemma lap_kernel_constant (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (hG : G.Connected)
    (x : (Fin 19) → ℝ) (hx : G.lapMatrix ℝ *ᵥ x = 0) : x = fun _ => x 0 := by
  funext i
  exact (G.lapMatrix_mulVec_eq_zero_iff_forall_reachable.mp hx) i 0 (hG i 0)

private lemma lapVec_last_constant (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (hG : G.Connected) :
    (fun (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (i : Fin 19) => WithLp.ofLp (((Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).eigenvectorBasis finrank_euclideanSpace) i)) G 18 = fun _ => (fun (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (i : Fin 19) => WithLp.ofLp (((Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).eigenvectorBasis finrank_euclideanSpace) i)) G 18 0 := by
  apply lap_kernel_constant G hG
  rw [lapVec_eigen, lapEig_last_zero, zero_smul]

private lemma lapVec_last_entry_ne_zero (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (hG : G.Connected) :
    (fun (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (i : Fin 19) => WithLp.ofLp (((Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).eigenvectorBasis finrank_euclideanSpace) i)) G 18 0 ≠ 0 := by
  intro hz
  apply lapVec_ne_zero G 18
  rw [lapVec_last_constant G hG, hz]
  rfl

private lemma lapVec_sum_zero (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (hG : G.Connected)
    (i : Fin 19) (hi : i ≠ 18) : ∑ j, (fun (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (i : Fin 19) => WithLp.ofLp (((Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).eigenvectorBasis finrank_euclideanSpace) i)) G i j = 0 := by
  have ho := lapVec_dot G i 18
  rw [ite_eq_right hi, lapVec_last_constant G hG] at ho
  simp only [dotProduct, ← Finset.sum_mul] at ho
  exact (mul_eq_zero.mp ho).resolve_right (lapVec_last_entry_ne_zero G hG)

private lemma lapEig_pos (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (hG : G.Connected)
    (i : Fin 19) (hi : i ≠ 18) : 0 < lapEig G i := by
  have hn := lapEig_nonneg G i
  have hnz : lapEig G i ≠ 0 := by
    intro he
    have hker : G.lapMatrix ℝ *ᵥ (fun (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (i : Fin 19) => WithLp.ofLp (((Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).eigenvectorBasis finrank_euclideanSpace) i)) G i = 0 := by rw [lapVec_eigen, he, zero_smul]
    have hc := lap_kernel_constant G hG _ hker
    have hs := lapVec_sum_zero G hG i hi
    rw [hc] at hs
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at hs
    have hz : (fun (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (i : Fin 19) => WithLp.ofLp (((Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).eigenvectorBasis finrank_euclideanSpace) i)) G i 0 = 0 := by linarith
    apply lapVec_ne_zero G i
    rw [hc, hz]; rfl
  exact lt_of_le_of_ne hn (Ne.symm hnz)

private lemma lap_rayleigh_lower (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (hG : G.Connected)
    (x : (Fin 19) → ℝ) (hx : ∑ j, x j = 0) :
    lapEig G 17 * (x ⬝ᵥ x) ≤ x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x) := by
  rw [lapEig_eq_eigenvalues]
  apply rayleigh_ge_of_support (G.isHermitian_lapMatrix ℝ) (17 : Fin 19) x
  intro i hi
  have hi18 : i = 18 := by
    apply Fin.ext
    have hit : i.val < 19 := i.isLt
    norm_num [Fin.lt_def] at hi ⊢
    omega
  subst i
  rw [OrthonormalBasis.repr_apply_apply]
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
  change (fun (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (i : Fin 19) => WithLp.ofLp (((Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).eigenvectorBasis finrank_euclideanSpace) i)) G 18 ⬝ᵥ x = 0
  rw [lapVec_last_constant G hG]
  simp only [dotProduct, ← Finset.mul_sum, hx, mul_zero]

private lemma lap_second_gt_of_posDef (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj]
    (hG : G.Connected) (c : ℝ)
    (hP : (G.lapMatrix ℝ + Matrix.of (fun _ _ => (1 : ℝ)) - c • 1).PosDef) :
    c < lapEig G 17 := by
  let v := (fun (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (i : Fin 19) => WithLp.ofLp (((Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).eigenvectorBasis finrank_euclideanSpace) i)) G 17
  have hn : v ≠ 0 := lapVec_ne_zero G 17
  have hs : ∑ i, v i = 0 := lapVec_sum_zero G hG 17 (by decide)
  have hj : Matrix.of (fun (_ _ : (Fin 19)) => (1 : ℝ)) *ᵥ v = 0 := by
    ext i
    simpa [Matrix.mulVec, dotProduct] using hs
  have hq := hP.dotProduct_mulVec_pos hn
  have he := lapVec_eigen G 17
  change G.lapMatrix ℝ *ᵥ v = lapEig G 17 • v at he
  have hvv : v ⬝ᵥ v = 1 := by simpa [v] using lapVec_dot G 17 17
  simpa only [sub_mulVec, add_mulVec, hj, smul_mulVec, one_mulVec, he,
    star_trivial, add_zero, dotProduct_sub, dotProduct_smul, smul_eq_mul, hvv, mul_one,
    sub_pos] using hq
end D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio
namespace D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio
private lemma ratios_separated
    (hp : 0 < lapEig (broom 19 7) 17)
    (h7s : lapEig (broom 19 7) 17 < 35467/1000000)
    (h7l : 9018480/1000000 < lapEig (broom 19 7) 0)
    (h8s : 39388/1000000 < lapEig (broom 19 8) 17)
    (h8l : lapEig (broom 19 8) 0 < 10014270/1000000) :
    spectralRatio (broom 19 8) < spectralRatio (broom 19 7) := by
  have hs8 : 0 < lapEig (broom 19 8) 17 := by linarith
  have hR7 : (9018480 : ℝ)/35467 <
      lapEig (broom 19 7) 0 / lapEig (broom 19 7) 17 := by
    apply (div_lt_div_iff₀ (by norm_num) hp).mpr
    nlinarith
  have hR8 : lapEig (broom 19 8) 0 / lapEig (broom 19 8) 17 <
      (10014270 : ℝ)/39388 := by
    apply (div_lt_div_iff₀ hs8 (by norm_num)).mpr
    nlinarith
  have hm : (10014270 : ℝ)/39388 < 9018480/35467 := by norm_num
  simpa [spectralRatio] using lt_trans hR8 (lt_trans hm hR7)
end D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio
namespace D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio
private lemma lapMatrix_rat_cast (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] :
    (G.lapMatrix ℚ).map (Rat.castHom ℝ) = G.lapMatrix ℝ := by
  ext i j
  by_cases hij : i=j <;> by_cases ha : G.Adj i j <;>
    simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
      Matrix.map_apply, hij, ha]

private lemma rat_quadratic_cast (G : SimpleGraph (Fin 19)) [DecidableRel G.Adj] (v : (Fin 19) → ℚ) :
    ((v ⬝ᵥ (G.lapMatrix ℚ *ᵥ v) : ℚ) : ℝ) =
      (fun i => (v i : ℝ)) ⬝ᵥ (G.lapMatrix ℝ *ᵥ (fun i => (v i : ℝ))) := by
  have h := (Rat.castHom ℝ).map_dotProduct v (G.lapMatrix ℚ *ᵥ v)
  have hvec : (Rat.castHom ℝ) ∘ (G.lapMatrix ℚ *ᵥ v) =
      (G.lapMatrix ℚ).map (Rat.castHom ℝ) *ᵥ ((Rat.castHom ℝ) ∘ v) := by
    funext i
    exact (Rat.castHom ℝ).map_mulVec _ _ _
  rw [hvec, lapMatrix_rat_cast] at h
  exact h

private def smallVecQ : (Fin 19) → ℚ := ![-402236785,-417027449,-417027449,-417027449,-417027449,-417027449,-417027449,-417027449,-284436044,-156547234,-23106187,111154368,241472632,363226589,472098052,564225651,636341937,685889149,711110015]
private lemma small_norm_rat : smallVecQ ⬝ᵥ smallVecQ = 3609999954590155762 := by decide +kernel
private lemma small_energy_rat : smallVecQ ⬝ᵥ ((broom 19 7).lapMatrix ℚ *ᵥ smallVecQ) = 128035461083249098 := by decide +kernel
private lemma small_norm_real : (fun i => (smallVecQ i : ℝ)) ⬝ᵥ (fun i => (smallVecQ i : ℝ)) = 3609999954590155762 := by
  have h := congrArg (Rat.castHom ℝ) small_norm_rat
  simpa only [RingHom.map_dotProduct, Rat.coe_castHom, Rat.cast_ofNat, Function.comp_def] using h
private lemma small_energy_real : (fun i => (smallVecQ i : ℝ)) ⬝ᵥ ((broom 19 7).lapMatrix ℝ *ᵥ (fun i => (smallVecQ i : ℝ))) = 128035461083249098 := by
  have h := congrArg (Rat.castHom ℝ) small_energy_rat
  simp only [Rat.coe_castHom, Rat.cast_ofNat] at h
  rw [rat_quadratic_cast] at h
  simpa only [Rat.coe_castHom, Rat.cast_ofNat, Function.comp_def] using h
private def largeVecQ : (Fin 19) → ℚ := ![94051336,-11729321,-11729321,-11729321,-11729321,-11729321,-11729321,-11729321,-13684208,1991014,-289687,42149,-6133,892,-130,19,-3,0,0]
private lemma large_norm_rat : largeVecQ ⬝ᵥ largeVecQ = 10000000020090436 := by decide +kernel
private lemma large_energy_rat : largeVecQ ⬝ᵥ ((broom 19 7).lapMatrix ℚ *ᵥ largeVecQ) = 90184805886938387 := by decide +kernel
private lemma large_norm_real : (fun i => (largeVecQ i : ℝ)) ⬝ᵥ (fun i => (largeVecQ i : ℝ)) = 10000000020090436 := by
  have h := congrArg (Rat.castHom ℝ) large_norm_rat
  simpa only [RingHom.map_dotProduct, Rat.coe_castHom, Rat.cast_ofNat, Function.comp_def] using h
private lemma large_energy_real : (fun i => (largeVecQ i : ℝ)) ⬝ᵥ ((broom 19 7).lapMatrix ℝ *ᵥ (fun i => (largeVecQ i : ℝ))) = 90184805886938387 := by
  have h := congrArg (Rat.castHom ℝ) large_energy_rat
  simp only [Rat.coe_castHom, Rat.cast_ofNat] at h
  rw [rat_quadratic_cast] at h
  simpa only [Rat.coe_castHom, Rat.cast_ofNat, Function.comp_def] using h
private lemma small_sum_rat : ∑ i, smallVecQ i = 0 := by decide +kernel
private lemma small_sum_real : ∑ i, (fun i => (smallVecQ i : ℝ)) i = 0 := by
  have h := congrArg (Rat.castHom ℝ) small_sum_rat
  simpa only [map_sum, map_zero, Rat.coe_castHom] using h

private lemma broom7_small_bound : lapEig (broom 19 7) 17 < 35467/1000000 := by
  have h := lap_rayleigh_lower (broom 19 7) broom7_tree.connected (fun i => (smallVecQ i : ℝ)) small_sum_real
  rw [small_norm_real, small_energy_real] at h
  norm_num at h ⊢
  linarith

private lemma broom7_large_bound : 9018480/1000000 < lapEig (broom 19 7) 0 := by
  have h := rayleigh_le_top ((broom 19 7).isHermitian_lapMatrix ℝ) (fun i => (largeVecQ i : ℝ))
  change _ ≤ lapEig (broom 19 7) 0 * _ at h
  rw [large_norm_real, large_energy_real] at h
  norm_num at h ⊢
  linarith
end D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio

set_option maxHeartbeats 10000000
set_option maxRecDepth 16384
namespace D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio
private def certHighU : Matrix (Fin 19) (Fin 19) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
(100000/101427),1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
(100000/101427),(-10000000000/81429036329),1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
(100000/101427),(-10000000000/81429036329),(-10000000000/71429036329),1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
(100000/101427),(-10000000000/81429036329),(-10000000000/71429036329),(-10000000000/61429036329),1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
(100000/101427),(-10000000000/81429036329),(-10000000000/71429036329),(-10000000000/61429036329),(-10000000000/51429036329),1,0,0,0,0,0,0,0,0,0,0,0,0,0;
(100000/101427),(-10000000000/81429036329),(-10000000000/71429036329),(-10000000000/61429036329),(-10000000000/51429036329),(-10000000000/41429036329),1,0,0,0,0,0,0,0,0,0,0,0,0;
(100000/101427),(-10000000000/81429036329),(-10000000000/71429036329),(-10000000000/61429036329),(-10000000000/51429036329),(-10000000000/41429036329),(-10000000000/31429036329),1,0,0,0,0,0,0,0,0,0,0,0;
(100000/101427),(-10000000000/81429036329),(-10000000000/71429036329),(-10000000000/61429036329),(-10000000000/51429036329),(-10000000000/41429036329),(-10000000000/31429036329),(-10000000000/21429036329),1,0,0,0,0,0,0,0,0,0,0;
(100000/101427),(-10000000000/81429036329),(-10000000000/71429036329),(-10000000000/61429036329),(-10000000000/51429036329),(-10000000000/41429036329),(-10000000000/31429036329),(-10000000000/21429036329),(-10000000000/11429036329),1,0,0,0,0,0,0,0,0,0;
0,0,0,0,0,0,0,0,0,(1142903632900000/145268298041483),1,0,0,0,0,0,0,0,0;
0,0,0,0,0,0,0,0,0,0,(14526829804148300000/2131573004491596241),1,0,0,0,0,0,0,0;
0,0,0,0,0,0,0,0,0,0,0,(213157300449159624100000/255617177855856500635907),1,0,0,0,0,0,0;
0,0,0,0,0,0,0,0,0,0,0,0,(25561717785585650063590700000/183542777952569545325133039289),1,0,0,0,0,0;
0,0,0,0,0,0,0,0,0,0,0,0,0,(18354277795256954532513303928900000/144539966127635387994926326278265403),1,0,0,0,0;
0,0,0,0,0,0,0,0,0,0,0,0,0,0,(14453996612763538799492632627826540300000/114002803654246750641358490497321407130081),1,0,0,0;
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,(11400280365424675064135849049732140713008100000/89919525262935656746302747701014149322039425587),1,0,0;
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,(8991952526293565674630274770101414932203942558700000/70923907336356267072805587276807452577413280729912649),1,0;
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,(7092390733635626707280558727680745257741328072991264900000/55941139032224637483894335917479824803538199079661704550123),1]
private def certHighV : Matrix (Fin 19) (Fin 19) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
(-100000/101427),1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
(-90142700000/81429036329),(10000000000/81429036329),1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
(-90142700000/71429036329),(10000000000/71429036329),(10000000000/71429036329),1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
(-90142700000/61429036329),(10000000000/61429036329),(10000000000/61429036329),(10000000000/61429036329),1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
(-90142700000/51429036329),(10000000000/51429036329),(10000000000/51429036329),(10000000000/51429036329),(10000000000/51429036329),1,0,0,0,0,0,0,0,0,0,0,0,0,0;
(-90142700000/41429036329),(10000000000/41429036329),(10000000000/41429036329),(10000000000/41429036329),(10000000000/41429036329),(10000000000/41429036329),1,0,0,0,0,0,0,0,0,0,0,0,0;
(-90142700000/31429036329),(10000000000/31429036329),(10000000000/31429036329),(10000000000/31429036329),(10000000000/31429036329),(10000000000/31429036329),(10000000000/31429036329),1,0,0,0,0,0,0,0,0,0,0,0;
(-90142700000/21429036329),(10000000000/21429036329),(10000000000/21429036329),(10000000000/21429036329),(10000000000/21429036329),(10000000000/21429036329),(10000000000/21429036329),(10000000000/21429036329),1,0,0,0,0,0,0,0,0,0,0;
(-90142700000/11429036329),(10000000000/11429036329),(10000000000/11429036329),(10000000000/11429036329),(10000000000/11429036329),(10000000000/11429036329),(10000000000/11429036329),(10000000000/11429036329),(10000000000/11429036329),1,0,0,0,0,0,0,0,0,0;
(9014270000000000/145268298041483),(-1000000000000000/145268298041483),(-1000000000000000/145268298041483),(-1000000000000000/145268298041483),(-1000000000000000/145268298041483),(-1000000000000000/145268298041483),(-1000000000000000/145268298041483),(-1000000000000000/145268298041483),(-1000000000000000/145268298041483),(-1142903632900000/145268298041483),1,0,0,0,0,0,0,0,0;
(-1000000000000000/2364665141483),(100000000000000000000/2131573004491596241),(100000000000000000000/2131573004491596241),(100000000000000000000/2131573004491596241),(100000000000000000000/2131573004491596241),(100000000000000000000/2131573004491596241),(100000000000000000000/2131573004491596241),(100000000000000000000/2131573004491596241),(100000000000000000000/2131573004491596241),(114290363290000000000/2131573004491596241),(-14526829804148300000/2131573004491596241),1,0,0,0,0,0,0,0;
(90142700000000000000000000/255617177855856500635907),(-10000000000000000000000000/255617177855856500635907),(-10000000000000000000000000/255617177855856500635907),(-10000000000000000000000000/255617177855856500635907),(-10000000000000000000000000/255617177855856500635907),(-10000000000000000000000000/255617177855856500635907),(-10000000000000000000000000/255617177855856500635907),(-10000000000000000000000000/255617177855856500635907),(-10000000000000000000000000/255617177855856500635907),(-11429036329000000000000000/255617177855856500635907),(1452682980414830000000000/255617177855856500635907),(-213157300449159624100000/255617177855856500635907),1,0,0,0,0,0,0;
(-9014270000000000000000000000000/183542777952569545325133039289),(1000000000000000000000000000000/183542777952569545325133039289),(1000000000000000000000000000000/183542777952569545325133039289),(1000000000000000000000000000000/183542777952569545325133039289),(1000000000000000000000000000000/183542777952569545325133039289),(1000000000000000000000000000000/183542777952569545325133039289),(1000000000000000000000000000000/183542777952569545325133039289),(1000000000000000000000000000000/183542777952569545325133039289),(1000000000000000000000000000000/183542777952569545325133039289),(1142903632900000000000000000000/183542777952569545325133039289),(-145268298041483000000000000000/183542777952569545325133039289),(21315730044915962410000000000/183542777952569545325133039289),(-25561717785585650063590700000/183542777952569545325133039289),1,0,0,0,0,0;
(1000000000000000000000000000000/160345725308466895261542339289),(-100000000000000000000000000000000000/144539966127635387994926326278265403),(-100000000000000000000000000000000000/144539966127635387994926326278265403),(-100000000000000000000000000000000000/144539966127635387994926326278265403),(-100000000000000000000000000000000000/144539966127635387994926326278265403),(-100000000000000000000000000000000000/144539966127635387994926326278265403),(-100000000000000000000000000000000000/144539966127635387994926326278265403),(-100000000000000000000000000000000000/144539966127635387994926326278265403),(-100000000000000000000000000000000000/144539966127635387994926326278265403),(-114290363290000000000000000000000000/144539966127635387994926326278265403),(14526829804148300000000000000000000/144539966127635387994926326278265403),(-2364665141483000000000000000/160345725308466895261542339289),(2556171778558565006359070000000000/144539966127635387994926326278265403),(-18354277795256954532513303928900000/144539966127635387994926326278265403),1,0,0,0,0;
(-90142700000000000000000000000000000000000/114002803654246750641358490497321407130081),(10000000000000000000000000000000000000000/114002803654246750641358490497321407130081),(10000000000000000000000000000000000000000/114002803654246750641358490497321407130081),(10000000000000000000000000000000000000000/114002803654246750641358490497321407130081),(10000000000000000000000000000000000000000/114002803654246750641358490497321407130081),(10000000000000000000000000000000000000000/114002803654246750641358490497321407130081),(10000000000000000000000000000000000000000/114002803654246750641358490497321407130081),(10000000000000000000000000000000000000000/114002803654246750641358490497321407130081),(10000000000000000000000000000000000000000/114002803654246750641358490497321407130081),(11429036329000000000000000000000000000000/114002803654246750641358490497321407130081),(-1452682980414830000000000000000000000000/114002803654246750641358490497321407130081),(213157300449159624100000000000000000000/114002803654246750641358490497321407130081),(-255617177855856500635907000000000000000/114002803654246750641358490497321407130081),(1835427779525695453251330392890000000000/114002803654246750641358490497321407130081),(-14453996612763538799492632627826540300000/114002803654246750641358490497321407130081),1,0,0,0;
(9014270000000000000000000000000000000000000000/89919525262935656746302747701014149322039425587),(-1000000000000000000000000000000000000000000000/89919525262935656746302747701014149322039425587),(-1000000000000000000000000000000000000000000000/89919525262935656746302747701014149322039425587),(-1000000000000000000000000000000000000000000000/89919525262935656746302747701014149322039425587),(-1000000000000000000000000000000000000000000000/89919525262935656746302747701014149322039425587),(-1000000000000000000000000000000000000000000000/89919525262935656746302747701014149322039425587),(-1000000000000000000000000000000000000000000000/89919525262935656746302747701014149322039425587),(-1000000000000000000000000000000000000000000000/89919525262935656746302747701014149322039425587),(-1000000000000000000000000000000000000000000000/89919525262935656746302747701014149322039425587),(-1142903632900000000000000000000000000000000000/89919525262935656746302747701014149322039425587),(145268298041483000000000000000000000000000000/89919525262935656746302747701014149322039425587),(-687604194997289110000000000000000000000000/2900629847191472798267830571000456429743207277),(25561717785585650063590700000000000000000000/89919525262935656746302747701014149322039425587),(-183542777952569545325133039289000000000000000/89919525262935656746302747701014149322039425587),(1445399661276353879949263262782654030000000000/89919525262935656746302747701014149322039425587),(-11400280365424675064135849049732140713008100000/89919525262935656746302747701014149322039425587),1,0,0;
(-1000000000000000000000000000000000000000000000/78679590622819448577428440990571008609031325587),(100000000000000000000000000000000000000000000000000/70923907336356267072805587276807452577413280729912649),(100000000000000000000000000000000000000000000000000/70923907336356267072805587276807452577413280729912649),(100000000000000000000000000000000000000000000000000/70923907336356267072805587276807452577413280729912649),(100000000000000000000000000000000000000000000000000/70923907336356267072805587276807452577413280729912649),(100000000000000000000000000000000000000000000000000/70923907336356267072805587276807452577413280729912649),(100000000000000000000000000000000000000000000000000/70923907336356267072805587276807452577413280729912649),(100000000000000000000000000000000000000000000000000/70923907336356267072805587276807452577413280729912649),(100000000000000000000000000000000000000000000000000/70923907336356267072805587276807452577413280729912649),(114290363290000000000000000000000000000000000000000/70923907336356267072805587276807452577413280729912649),(-14526829804148300000000000000000000000000000000000/70923907336356267072805587276807452577413280729912649),(2364665141483000000000000000000000000000000/78679590622819448577428440990571008609031325587),(-2556171778558565006359070000000000000000000000000/70923907336356267072805587276807452577413280729912649),(18354277795256954532513303928900000000000000000000/70923907336356267072805587276807452577413280729912649),(-160345725308466895261542339289000000000000000/78679590622819448577428440990571008609031325587),(1140028036542467506413584904973214071300810000000000/70923907336356267072805587276807452577413280729912649),(-8991952526293565674630274770101414932203942558700000/70923907336356267072805587276807452577413280729912649),1,0;
(90142700000000000000000000000000000000000000000000000000/55941139032224637483894335917479824803538199079661704550123),(-10000000000000000000000000000000000000000000000000000000/55941139032224637483894335917479824803538199079661704550123),(-10000000000000000000000000000000000000000000000000000000/55941139032224637483894335917479824803538199079661704550123),(-10000000000000000000000000000000000000000000000000000000/55941139032224637483894335917479824803538199079661704550123),(-10000000000000000000000000000000000000000000000000000000/55941139032224637483894335917479824803538199079661704550123),(-10000000000000000000000000000000000000000000000000000000/55941139032224637483894335917479824803538199079661704550123),(-10000000000000000000000000000000000000000000000000000000/55941139032224637483894335917479824803538199079661704550123),(-10000000000000000000000000000000000000000000000000000000/55941139032224637483894335917479824803538199079661704550123),(-10000000000000000000000000000000000000000000000000000000/55941139032224637483894335917479824803538199079661704550123),(-11429036329000000000000000000000000000000000000000000000/55941139032224637483894335917479824803538199079661704550123),(1452682980414830000000000000000000000000000000000000000/55941139032224637483894335917479824803538199079661704550123),(-213157300449159624100000000000000000000000000000000000/55941139032224637483894335917479824803538199079661704550123),(255617177855856500635907000000000000000000000000000000/55941139032224637483894335917479824803538199079661704550123),(-1835427779525695453251330392890000000000000000000000000/55941139032224637483894335917479824803538199079661704550123),(14453996612763538799492632627826540300000000000000000000/55941139032224637483894335917479824803538199079661704550123),(-114002803654246750641358490497321407130081000000000000000/55941139032224637483894335917479824803538199079661704550123),(899195252629356567463027477010141493220394255870000000000/55941139032224637483894335917479824803538199079661704550123),(-7092390733635626707280558727680745257741328072991264900000/55941139032224637483894335917479824803538199079661704550123),1]
private def certHighD : Fin 19 → ℚ := ![(101427/100000),(81429036329/10142700000),(64388061930941483/8142903632900000),(55373791930941483/7142903632900000),(46359521930941483/6142903632900000),(37345251930941483/5142903632900000),(28330981930941483/4142903632900000),(19316711930941483/3142903632900000),(10302441930941483/2142903632900000),(145268298041483/1142903632900000),(2131573004491596241/14526829804148300000),(255617177855856500635907/213157300449159624100000),(183542777952569545325133039289/25561717785585650063590700000),(144539966127635387994926326278265403/18354277795256954532513303928900000),(114002803654246750641358490497321407130081/14453996612763538799492632627826540300000),(89919525262935656746302747701014149322039425587/11400280365424675064135849049732140713008100000),(70923907336356267072805587276807452577413280729912649/8991952526293565674630274770101414932203942558700000),(55941139032224637483894335917479824803538199079661704550123/7092390733635626707280558727680745257741328072991264900000),(49717614061037595622466363670318011507404895374483084857503725521/5594113903222463748389433591747982480353819907966170455012300000)]
private def certHighM : Matrix (Fin 19) (Fin 19) ℚ := (10014270/1000000 : ℚ) • (1 : Matrix (Fin 19) (Fin 19) ℚ) - (broom 19 8).lapMatrix ℚ
private lemma certHigh_inv : certHighU * certHighV = 1 := by
  decide +kernel
private lemma certHigh_factor : certHighM = certHighU * diagonal certHighD * certHighU.transpose := by
  have hc : ∀ i j : Fin 19, certHighM i j =
      ∑ k, certHighU i k * certHighD k * certHighU j k := by decide +kernel
  ext i j
  change certHighM i j = ∑ k, (certHighU * diagonal certHighD) i k * certHighU j k
  simp_rw [Matrix.mul_diagonal]
  exact hc i j
private lemma certHigh_positive : ∀ i, 0 < certHighD i := by
  decide +kernel
private lemma certHigh_posDef : (certHighM.map (Rat.castHom ℝ)).PosDef :=
  pd_of_rat_certificate _ _ _ _ certHigh_inv certHigh_factor certHigh_positive
end D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio

set_option maxHeartbeats 10000000
set_option maxRecDepth 16384
namespace D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio
private def certLowU : Matrix (Fin 19) (Fin 19) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
0,(250000/490153),1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
0,(250000/490153),(250000/740153),1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
0,(250000/490153),(250000/740153),(250000/990153),1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
0,(250000/490153),(250000/740153),(250000/990153),(250000/1240153),1,0,0,0,0,0,0,0,0,0,0,0,0,0;
0,(250000/490153),(250000/740153),(250000/990153),(250000/1240153),(250000/1490153),1,0,0,0,0,0,0,0,0,0,0,0,0;
0,(250000/490153),(250000/740153),(250000/990153),(250000/1240153),(250000/1490153),(250000/1740153),1,0,0,0,0,0,0,0,0,0,0,0;
0,(250000/490153),(250000/740153),(250000/990153),(250000/1240153),(250000/1490153),(250000/1740153),(250000/1990153),1,0,0,0,0,0,0,0,0,0,0;
0,(250000/490153),(250000/740153),(250000/990153),(250000/1240153),(250000/1490153),(250000/1740153),(250000/1990153),(250000/2240153),1,0,0,0,0,0,0,0,0,0;
(250000/2490153),(250000/490153),(250000/740153),(250000/990153),(250000/1240153),(250000/1490153),(250000/1740153),(250000/1990153),(250000/2240153),(-500000000000/1158055963409),1,0,0,0,0,0,0,0,0;
(250000/2490153),(250000/490153),(250000/740153),(250000/990153),(250000/1240153),(250000/1490153),(250000/1740153),(250000/1990153),(250000/2240153),(60038250000/1158055963409),(-682656479417562500000000/1140480640545350041151281),1,0,0,0,0,0,0,0;
(250000/2490153),(250000/490153),(250000/740153),(250000/990153),(250000/1240153),(250000/1490153),(250000/1740153),(250000/1990153),(250000/2240153),(60038250000/1158055963409),(38277653445140394250000/1140480640545350041151281),(-91900760079752411875000000000/132587922482638202794414695331),1,0,0,0,0,0,0;
(250000/2490153),(250000/490153),(250000/740153),(250000/990153),(250000/1240153),(250000/1490153),(250000/1740153),(250000/1990153),(250000/2240153),(60038250000/1158055963409),(38277653445140394250000/1140480640545350041151281),(9417879897080274662820250000/397763767447914608383244085993),(-32405697705702112956543562500000000/42754460863651897787600857493325643),1,0,0,0,0,0;
(250000/2490153),(250000/490153),(250000/740153),(250000/990153),(250000/1240153),(250000/1490153),(250000/1740153),(250000/1990153),(250000/2240153),(60038250000/1158055963409),(38277653445140394250000/1140480640545350041151281),(9417879897080274662820250000/397763767447914608383244085993),(741282914957437742060111332750000/42754460863651897787600857493325643),(-31564437007461041562374939494750000000000/39065817128106003029775801059022363930137),1,0,0,0,0;
(250000/2490153),(250000/490153),(250000/740153),(250000/990153),(250000/1240153),(250000/1490153),(250000/1740153),(250000/1990153),(250000/2240153),(60038250000/1158055963409),(38277653445140394250000/1140480640545350041151281),(9417879897080274662820250000/397763767447914608383244085993),(741282914957437742060111332750000/42754460863651897787600857493325643),(501408640277881778325703625244232250000/39065817128106003029775801059022363930137),(-3219892626440965248929514176873959937500000000/3787964871210295441038457025643066639160896987),1,0,0,0;
(250000/2490153),(250000/490153),(250000/740153),(250000/990153),(250000/1240153),(250000/1490153),(250000/1740153),(250000/1990153),(250000/2240153),(60038250000/1158055963409),(38277653445140394250000/1140480640545350041151281),(9417879897080274662820250000/397763767447914608383244085993),(741282914957437742060111332750000/42754460863651897787600857493325643),(501408640277881778325703625244232250000/39065817128106003029775801059022363930137),(106776402703605010655407734133711170034250000/11363894613630886323115371076929199917482690961),(-939991639770236361712139726233741187956625000000000/1058708766940436127626418812448561529843230387619011),1,0,0;
(250000/2490153),(250000/490153),(250000/740153),(250000/990153),(250000/1240153),(250000/1490153),(250000/1740153),(250000/1990153),(250000/2240153),(60038250000/1158055963409),(38277653445140394250000/1140480640545350041151281),(9417879897080274662820250000/397763767447914608383244085993),(741282914957437742060111332750000/42754460863651897787600857493325643),(501408640277881778325703625244232250000/39065817128106003029775801059022363930137),(106776402703605010655407734133711170034250000/11363894613630886323115371076929199917482690961),(6999578032337498547474530177025471833599246750000/1058708766940436127626418812448561529843230387619011),(-790412507860449443109156242550199397222600900937500000000/855413172243667149119969252645215197804099852324621546049),1,0;
(250000/2490153),(250000/490153),(250000/740153),(250000/990153),(250000/1240153),(250000/1490153),(250000/1740153),(250000/1990153),(250000/2240153),(60038250000/1158055963409),(38277653445140394250000/1140480640545350041151281),(9417879897080274662820250000/397763767447914608383244085993),(741282914957437742060111332750000/42754460863651897787600857493325643),(501408640277881778325703625244232250000/39065817128106003029775801059022363930137),(106776402703605010655407734133711170034250000/11363894613630886323115371076929199917482690961),(6999578032337498547474530177025471833599246750000/1058708766940436127626418812448561529843230387619011),(3619067344877652610657866786221750159821889776758250000/855413172243667149119969252645215197804099852324621546049),(-71130605741895417399190667396876375304579214369011000000000000/74047227161622786149243846474978329693636683218739203724268499),1]
private def certLowV : Matrix (Fin 19) (Fin 19) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
0,(-250000/490153),1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
0,(-250000/740153),(-250000/740153),1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
0,(-250000/990153),(-250000/990153),(-250000/990153),1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
0,(-250000/1240153),(-250000/1240153),(-250000/1240153),(-250000/1240153),1,0,0,0,0,0,0,0,0,0,0,0,0,0;
0,(-250000/1490153),(-250000/1490153),(-250000/1490153),(-250000/1490153),(-250000/1490153),1,0,0,0,0,0,0,0,0,0,0,0,0;
0,(-250000/1740153),(-250000/1740153),(-250000/1740153),(-250000/1740153),(-250000/1740153),(-250000/1740153),1,0,0,0,0,0,0,0,0,0,0,0;
0,(-250000/1990153),(-250000/1990153),(-250000/1990153),(-250000/1990153),(-250000/1990153),(-250000/1990153),(-250000/1990153),1,0,0,0,0,0,0,0,0,0,0;
0,(-250000/2240153),(-250000/2240153),(-250000/2240153),(-250000/2240153),(-250000/2240153),(-250000/2240153),(-250000/2240153),(-250000/2240153),1,0,0,0,0,0,0,0,0,0;
(-250000/2490153),(-185038250000/1158055963409),(-185038250000/1158055963409),(-185038250000/1158055963409),(-185038250000/1158055963409),(-185038250000/1158055963409),(-185038250000/1158055963409),(-185038250000/1158055963409),(-185038250000/1158055963409),(500000000000/1158055963409),1,0,0,0,0,0,0,0,0;
(-183034648871265394250000/1140480640545350041151281),(-229755789496265394250000/1140480640545350041151281),(-229755789496265394250000/1140480640545350041151281),(-229755789496265394250000/1140480640545350041151281),(-229755789496265394250000/1140480640545350041151281),(-229755789496265394250000/1140480640545350041151281),(-229755789496265394250000/1140480640545350041151281),(-229755789496265394250000/1140480640545350041151281),(-229755789496265394250000/1140480640545350041151281),(235615364466797105750000/1140480640545350041151281),(682656479417562500000000/1140480640545350041151281),1,0,0,0,0,0,0,0;
(-27613526634815782262606750000/132587922482638202794414695331),(-31832475853565782262606750000/132587922482638202794414695331),(-31832475853565782262606750000/132587922482638202794414695331),(-31832475853565782262606750000/132587922482638202794414695331),(-31832475853565782262606750000/132587922482638202794414695331),(-31832475853565782262606750000/132587922482638202794414695331),(-31832475853565782262606750000/132587922482638202794414695331),(-31832475853565782262606750000/132587922482638202794414695331),(-31832475853565782262606750000/132587922482638202794414695331),(10190840362106092737393250000/132587922482638202794414695331),(50558942198675083924893250000/132587922482638202794414695331),(91900760079752411875000000000/132587922482638202794414695331),1,0,0,0,0,0,0;
(-32204473142641899479465458998250000/128263382590955693362802572479976929),(-35612825681704399479465458998250000/128263382590955693362802572479976929),(-35612825681704399479465458998250000/128263382590955693362802572479976929),(-35612825681704399479465458998250000/128263382590955693362802572479976929),(-35612825681704399479465458998250000/128263382590955693362802572479976929),(-35612825681704399479465458998250000/128263382590955693362802572479976929),(-35612825681704399479465458998250000/128263382590955693362802572479976929),(-35612825681704399479465458998250000/128263382590955693362802572479976929),(-35612825681704399479465458998250000/128263382590955693362802572479976929),(-1663548480887993229465458998250000/128263382590955693362802572479976929),(30948534589542656411159541001750000/128263382590955693362802572479976929),(64347251340671927014364603501750000/128263382590955693362802572479976929),(32405697705702112956543562500000000/42754460863651897787600857493325643),1,0,0,0,0,0;
(-11426108967570872343819667499369232250000/39065817128106003029775801059022363930137),(-12339232258586497343819667499369232250000/39065817128106003029775801059022363930137),(-12339232258586497343819667499369232250000/39065817128106003029775801059022363930137),(-12339232258586497343819667499369232250000/39065817128106003029775801059022363930137),(-12339232258586497343819667499369232250000/39065817128106003029775801059022363930137),(-12339232258586497343819667499369232250000/39065817128106003029775801059022363930137),(-12339232258586497343819667499369232250000/39065817128106003029775801059022363930137),(-12339232258586497343819667499369232250000/39065817128106003029775801059022363930137),(-12339232258586497343819667499369232250000/39065817128106003029775801059022363930137),(-3243965448616770781319667499369232250000/39065817128106003029775801059022363930137),(5493056992241868191336582500630767750000/39065817128106003029775801059022363930137),(14440824515104504502294098125630767750000/39065817128106003029775801059022363930137),(23246902452780624632536884750193267750000/39065817128106003029775801059022363930137),(31564437007461041562374939494750000000000/39065817128106003029775801059022363930137),1,0,0,0,0;
(-1269017105024640821699550098809234098344750000/3787964871210295441038457025643066639160896987),(-450065658543369857233183366269744699448250000/1262654957070098480346152341881022213053632329),(-450065658543369857233183366269744699448250000/1262654957070098480346152341881022213053632329),(-450065658543369857233183366269744699448250000/1262654957070098480346152341881022213053632329),(-450065658543369857233183366269744699448250000/1262654957070098480346152341881022213053632329),(-450065658543369857233183366269744699448250000/1262654957070098480346152341881022213053632329),(-450065658543369857233183366269744699448250000/1262654957070098480346152341881022213053632329),(-450065658543369857233183366269744699448250000/1262654957070098480346152341881022213053632329),(-450065658543369857233183366269744699448250000/1262654957070098480346152341881022213053632329),(-180531927439610091608183366269744699448250000/1262654957070098480346152341881022213053632329),(78385409063434784368379133730255300551750000/1262654957070098480346152341881022213053632329),(10204398171804131360045721484562038630250000/37504602685250449911271851739040263754068287),(1813535501289187042087038890737640901655250000/3787964871210295441038457025643066639160896987),(2552993563030728311785633744414243589155250000/3787964871210295441038457025643066639160896987),(3219892626440965248929514176873959937500000000/3787964871210295441038457025643066639160896987),1,0,0,0;
(-1210392581160794206703019520034350547392922740250000/3176126300821308382879256437345684589529691162857033),(-425030727126840256401006506678116849130974246750000/1058708766940436127626418812448561529843230387619011),(-425030727126840256401006506678116849130974246750000/1058708766940436127626418812448561529843230387619011),(-425030727126840256401006506678116849130974246750000/1058708766940436127626418812448561529843230387619011),(-425030727126840256401006506678116849130974246750000/1058708766940436127626418812448561529843230387619011),(-425030727126840256401006506678116849130974246750000/1058708766940436127626418812448561529843230387619011),(-425030727126840256401006506678116849130974246750000/1058708766940436127626418812448561529843230387619011),(-425030727126840256401006506678116849130974246750000/1058708766940436127626418812448561529843230387619011),(-425030727126840256401006506678116849130974246750000/1058708766940436127626418812448561529843230387619011),(-210214855678903244682256506678116849130974246750000/1058708766940436127626418812448561529843230387619011),(-3860151775557575981084631678116849130974246750000/1058708766940436127626418812448561529843230387619011),(622416056737281874011122081528149452607077259750000/3176126300821308382879256437345684589529691162857033),(1246373114537979027954579448688305702607077259750000/3176126300821308382879256437345684589529691162857033),(1835714297482764874387593307668413968232077259750000/3176126300821308382879256437345684589529691162857033),(2367226635057810188390860108590965745115639759750000/3176126300821308382879256437345684589529691162857033),(939991639770236361712139726233741187956625000000000/1058708766940436127626418812448561529843230387619011),1,0,0;
(-370874650733154601893501983276665630416642634901758250000/855413172243667149119969252645215197804099852324621546049),(-388003225104492492518501983276665630416642634901758250000/855413172243667149119969252645215197804099852324621546049),(-388003225104492492518501983276665630416642634901758250000/855413172243667149119969252645215197804099852324621546049),(-388003225104492492518501983276665630416642634901758250000/855413172243667149119969252645215197804099852324621546049),(-388003225104492492518501983276665630416642634901758250000/855413172243667149119969252645215197804099852324621546049),(-388003225104492492518501983276665630416642634901758250000/855413172243667149119969252645215197804099852324621546049),(-388003225104492492518501983276665630416642634901758250000/855413172243667149119969252645215197804099852324621546049),(-388003225104492492518501983276665630416642634901758250000/855413172243667149119969252645215197804099852324621546049),(-388003225104492492518501983276665630416642634901758250000/855413172243667149119969252645215197804099852324621546049),(-217392141678451843104439483276665630416642634901758250000/855413172243667149119969252645215197804099852324621546049),(-53501087606396082789498077026665630416642634901758250000/855413172243667149119969252645215197804099852324621546049),(114343170645222546764037323363959369583357365098241750000/855413172243667149119969252645215197804099852324621546049),(279529583432389290975312065544623432083357365098241750000/855413172243667149119969252645215197804099852324621546049),(435551788328243226123332459970314560989607365098241750000/855413172243667149119969252645215197804099852324621546049),(576264382726346457410488279345393634116747990098241750000/855413172243667149119969252645215197804099852324621546049),(696124978958546494762841030256315036932447425160741750000/855413172243667149119969252645215197804099852324621546049),(790412507860449443109156242550199397222600900937500000000/855413172243667149119969252645215197804099852324621546049),1,0;
(-36749754959752732703410860868953526511183655386458837170750000/74047227161622786149243846474978329693636683218739203724268499),(-38256609017064744422160860868953526511183655386458837170750000/74047227161622786149243846474978329693636683218739203724268499),(-38256609017064744422160860868953526511183655386458837170750000/74047227161622786149243846474978329693636683218739203724268499),(-38256609017064744422160860868953526511183655386458837170750000/74047227161622786149243846474978329693636683218739203724268499),(-38256609017064744422160860868953526511183655386458837170750000/74047227161622786149243846474978329693636683218739203724268499),(-38256609017064744422160860868953526511183655386458837170750000/74047227161622786149243846474978329693636683218739203724268499),(-38256609017064744422160860868953526511183655386458837170750000/74047227161622786149243846474978329693636683218739203724268499),(-38256609017064744422160860868953526511183655386458837170750000/74047227161622786149243846474978329693636683218739203724268499),(-38256609017064744422160860868953526511183655386458837170750000/74047227161622786149243846474978329693636683218739203724268499),(-23247420411554032752238985868953526511183655386458837170750000/74047227161622786149243846474978329693636683218739203724268499),(-8829413726837176993571993681453526511183655386458837170750000/74047227161622786149243846474978329693636683218739203724268499),(5936368647100207057967740205265223488816344613541162829250000/74047227161622786149243846474978329693636683218739203724268499),(20468332074113473719358168752872645363816344613541162829250000/74047227161622786149243846474978329693636683218739203724268499),(34194091578739424443340445761735577981003844613541162829250000/74047227161622786149243846474978329693636683218739203724268499),(46573016945609852282798357305028928150453063363541162829250000/74047227161622786149243846474978329693636683218739203724268499),(57117527062374464825991335162885457395689735035416162829250000/74047227161622786149243846474978329693636683218739203724268499),(65412294764554137514068094323439912742802477605354350329250000/74047227161622786149243846474978329693636683218739203724268499),(71130605741895417399190667396876375304579214369011000000000000/74047227161622786149243846474978329693636683218739203724268499),1]
private def certLowD : Fin 19 → ℚ := ![(2490153/250000),(490153/250000),(177749963409/122538250000),(237788213409/185038250000),(99275487803/82512750000),(357864713409/310038250000),(417902963409/372538250000),(159313737803/145012750000),(537979463409/497538250000),(1158055963409/560038250000),(1140480640545350041151281/720934132862702894250000),(397763767447914608383244085993/285120160136337510287820250000),(42754460863651897787600857493325643/33146980620659550698603673832750000),(39065817128106003029775801059022363930137/32065845647738923340700643119994232250000),(11363894613630886323115371076929199917482690961/9766454282026500757443950264755590982534250000),(352902922313478709208806270816187176614410129206337/315663739267524620086538085470255553263408082250000),(855413172243667149119969252645215197804099852324621546049/794031575205327095719814109336421147382422790714258250000),(222141681484868358447731539424934989080910049656217611172805497/213853293060916787279992313161303799451024963081155386512250000),(12994408309003664172616309791609215501338186665822373877590347/18511806790405696537310961618744582423409170804684800931067124750000)]
private def certLowM : Matrix (Fin 19) (Fin 19) ℚ := (broom 19 8).lapMatrix ℚ + Matrix.of (fun _ _ => (1 : ℚ)) - (39388/1000000 : ℚ) • 1
private lemma certLow_inv : certLowU * certLowV = 1 := by
  decide +kernel
private lemma certLow_factor : certLowM = certLowU * diagonal certLowD * certLowU.transpose := by
  have hc : ∀ i j : Fin 19, certLowM i j =
      ∑ k, certLowU i k * certLowD k * certLowU j k := by decide +kernel
  ext i j
  change certLowM i j = ∑ k, (certLowU * diagonal certLowD) i k * certLowU j k
  simp_rw [Matrix.mul_diagonal]
  exact hc i j
private lemma certLow_positive : ∀ i, 0 < certLowD i := by
  decide +kernel
private lemma certLow_posDef : (certLowM.map (Rat.castHom ℝ)).PosDef :=
  pd_of_rat_certificate _ _ _ _ certLow_inv certLow_factor certLow_positive
end D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio
namespace D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio
private lemma certHigh_real : certHighM.map (Rat.castHom ℝ) =
    (10014270/1000000 : ℝ) • (1 : Matrix (Fin 19) (Fin 19) ℝ) - (broom 19 8).lapMatrix ℝ := by
  ext i j
  have he := congrFun (congrFun (lapMatrix_rat_cast (broom 19 8)) i) j
  simp only [certHighM, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, map_sub, map_mul] at he ⊢
  rw [he]
  by_cases hij : i=j <;> simp [Matrix.one_apply, hij]

private lemma certLow_real : certLowM.map (Rat.castHom ℝ) =
    (broom 19 8).lapMatrix ℝ + Matrix.of (fun (_ _ : (Fin 19)) => (1 : ℝ)) -
      (39388/1000000 : ℝ) • (1 : Matrix (Fin 19) (Fin 19) ℝ) := by
  ext i j
  have he := congrFun (congrFun (lapMatrix_rat_cast (broom 19 8)) i) j
  simp only [certLowM, Matrix.map_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, map_sub, map_add, map_mul] at he ⊢
  rw [he]
  by_cases hij : i=j <;> simp [Matrix.one_apply, hij]

private lemma broom8_large_bound : lapEig (broom 19 8) 0 < 10014270/1000000 := by
  have hp := certHigh_posDef
  rw [certHigh_real] at hp
  rw [lapEig_eq_eigenvalues]
  exact eigenvalue_lt_of_posDef ((broom 19 8).isHermitian_lapMatrix ℝ) _ hp 0

private lemma broom8_small_bound : 39388/1000000 < lapEig (broom 19 8) 17 := by
  have hp := certLow_posDef
  rw [certLow_real] at hp
  exact lap_second_gt_of_posDef (broom 19 8) broom8_tree.connected _ hp

private lemma broom_ratio_strict : spectralRatio (broom 19 8) < spectralRatio (broom 19 7) :=
  ratios_separated (lapEig_pos _ broom7_tree.connected 17 (by decide))
    broom7_small_bound broom7_large_bound broom8_small_bound broom8_large_bound

theorem result : ¬ D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio.claim := by
  intro h
  have hu := (h 19 (by decide) (broom 19 7) broom7_tree).2.1
  have hp : conjParam 19 = 8 := Nat.eight_eq_digitChar.mp rfl
  rw [hp] at hu
  exact (not_le_of_gt broom_ratio_strict) hu

end D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio
