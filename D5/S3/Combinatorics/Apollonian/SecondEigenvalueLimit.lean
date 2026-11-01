/- GID: D5/S3/Combinatorics/Apollonian/SecondEigenvalueLimit
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Apollonian/SecondEigenvalueLimit
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Spectrum]
   utility: none
   digest: The second ordinary-adjacency eigenvalue of the inner-face Apollonian stages. -/

import D5.S3.Combinatorics.Apollonian.CutoffGramLimit
import D5.S3.Combinatorics.Apollonian.CutoffOrderedSpectrum
import Mathlib.Analysis.CStarAlgebra.Basic

/-! The actual cutoff blocks and face weights determine the all-stage ordinary spectrum. -/
noncomputable section
namespace D5.S3.Combinatorics.Apollonian.SecondEigenvalueLimit
open InnerFaceStages CutoffGramLimit CutoffOrderedSpectrum Matrix Filter
open scoped BigOperators Topology Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def weight (k : ℕ) (v : Vertex k) : ℝ := (faceCount k v : ℝ) / (2:ℝ)^k

private theorem weight_old (k : ℕ) (v : Vertex k) :
    weight (k+1) (Sum.inl v) = weight k v := by
  simp only [weight, faceCount_old, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
  field_simp

private theorem weight_seed (k : ℕ) (v : Fin 4) :
    weight k (seed k v) = if v = 3 then 3 else 2 := by
  have hd := degreeCount_old k (seed k v)
  change degreeCount (k+1) (seed (k+1) v) =
    degreeCount k (seed k v) + faceCount k (seed k v) at hd
  rw [seed_degrees, seed_degrees] at hd
  have hf : faceCount k (seed k v) = 2^k * (if v = 3 then 3 else 2) := by
    split_ifs at hd ⊢ <;> simp only [pow_succ] at hd <;> omega
  simp only [weight, hf, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  split_ifs <;> push_cast <;> field_simp

private theorem weight_other_le (k : ℕ) (v : Vertex k) (hv : v ≠ seed k 3) :
    weight k v ≤ 2 := by
  induction k with
  | zero =>
    have h := weight_seed 0 v
    have hv' : v ≠ 3 := hv
    simpa only [seed, if_neg hv'] using le_of_eq h
  | succ k ih =>
    cases v with
    | inl v =>
      rw [weight_old]
      exact ih v (by simpa only [seed, ne_eq, Sum.inl.injEq] using hv)
    | inr f =>
      simp only [weight, faceCount_new, Nat.cast_ofNat]
      apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^(k+1))).mpr
      have h : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
      rw [pow_succ]
      nlinarith

private theorem diagonal_hermitian (k : ℕ) : (limitingDiagonal k).IsHermitian := by
  exact isHermitian_diagonal_iff.mpr (fun _ => by simp [IsSelfAdjoint])

/-- At every fixed cutoff, the second decreasing eigenvalue of the face-weight diagonal is two. -/
private theorem limiting_diagonal_second (k : ℕ) :
    (diagonal_hermitian k).eigenvalues₀ (secondIndex k) = 2 := by
  classical
  let c := seed k 3
  let a := seed k 0
  let s : Finset (Vertex k) := Finset.univ.erase c
  let r : Finset (Vertex k) := s.erase a
  have hac : a ≠ c := by
    exact fun h => (by decide : (0:Fin 4) ≠ 3) (seed_injective k h)
  have ha : a ∈ s := by simp [s, hac]
  have hsplit : (Finset.univ : Finset (Vertex k)).val = c ::ₘ a ::ₘ r.val := by
    calc
      _ = c ::ₘ s.val := by
        exact (Multiset.cons_erase
          (by simp : c ∈ (Finset.univ : Finset (Vertex k)).val)).symm
      _ = _ := congrArg (Multiset.cons c) (Multiset.cons_erase ha).symm
  have hwc : weight k c = 3 := by simpa [c] using weight_seed k 3
  have hwa : weight k a = 2 := by simpa [a] using weight_seed k 0
  have hrest : ∀ v ∈ r.val, weight k v ≤ 2 := by
    intro v hv
    exact weight_other_le k v (by
      have := Finset.mem_erase.mp ((Finset.mem_erase.mp hv).2)
      exact this.1)
  have hsort : ((Finset.univ.val.map (weight k)).sort (· ≥ ·))[1]? = some 2 := by
    rw [hsplit, Multiset.map_cons, Multiset.map_cons, hwc, hwa]
    rw [Multiset.sort_cons, Multiset.sort_cons]
    · rfl
    · intro b hb
      obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hb
      exact hrest v hv
    · intro b hb
      rcases Multiset.mem_cons.mp hb with h | h
      · subst b; norm_num
      · obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp h
        exact (hrest v hv).trans (by norm_num)
  have he := (diagonal_hermitian k).sort_roots_charpoly_eq_eigenvalues₀
  have hr : (limitingDiagonal k).charpoly.roots = Finset.univ.val.map (weight k) := by
    rw [limitingDiagonal, charpoly_diagonal, Polynomial.roots_prod]
    · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
      rfl
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  rw [hr] at he
  rw [Multiset.map_map] at he
  change (Finset.univ.val.map (weight k)).sort (· ≥ ·) = _ at he
  rw [he] at hsort
  have hcard : 1 < Fintype.card (Vertex k) := (secondIndex k).isLt
  simpa [secondIndex, hcard] using hsort


private theorem hermitian_complex {ι : Type*}
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) : (A.map Complex.ofReal).IsHermitian :=
  hA.map Complex.ofReal (by intro x; simp)

private theorem hermitian_norm {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]
    {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) :
    ‖A‖ = ‖fun i => (hA.eigenvalues i : 𝕜)‖ := by
  calc
    ‖A‖ = ‖Unitary.conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary
      (diagonal (RCLike.ofReal ∘ hA.eigenvalues))‖ := congrArg norm hA.spectral_theorem
    _ = _ := by
      simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
        CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, l2_opNorm_diagonal]
      rfl

private theorem norm_complex {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) : ‖A.map Complex.ofReal‖ = ‖A‖ := by
  rw [hermitian_norm (hermitian_complex hA), hermitian_norm hA]
  have he : (hermitian_complex hA).eigenvalues = hA.eigenvalues := by
    funext i
    simp only [IsHermitian.eigenvalues,
      SpectralTopology.RectangularDilation.eigenvalues_ofReal A hA (hermitian_complex hA)]
  rw [he]
  have hi : Isometry (fun f : ι → ℝ => fun i => (f i : ℂ)) :=
    (algebraMap_isometry ℝ ℂ).postcomp_pi
  exact hi.norm_map_of_map_zero (by funext i; rfl) hA.eigenvalues

private theorem real_weyl {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (j : Fin (Fintype.card ι)) :
    |hA.eigenvalues₀ j - hB.eigenvalues₀ j| ≤ ‖A-B‖ := by
  let hAC := hermitian_complex hA
  let hBC := hermitian_complex hB
  have hbound (x : EuclideanSpace ℂ ι) :
      ‖(toEuclideanLin (A.map Complex.ofReal) - toEuclideanLin (B.map Complex.ofReal)) x‖ ≤
        ‖A-B‖ * ‖x‖ := by
    have hb := (toEuclideanCLM (n := ι) (𝕜 := ℂ) ((A-B).map Complex.ofReal)).le_opNorm x
    rw [l2_opNorm_toEuclideanCLM, norm_complex (hA.sub hB)] at hb
    have he : (A-B).map Complex.ofReal = A.map Complex.ofReal - B.map Complex.ofReal := by
      ext i j; simp
    rw [he] at hb
    have heval := congrArg (fun f : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι => f x)
      (coe_toEuclideanCLM_eq_toEuclideanLin
        (A.map Complex.ofReal - B.map Complex.ofReal))
    have hb' : ‖toEuclideanLin (A.map Complex.ofReal - B.map Complex.ofReal) x‖ ≤
        ‖A-B‖ * ‖x‖ := by
      rw [← heval]
      exact hb
    simpa only [map_sub, LinearMap.sub_apply] using hb'
  have hh := SpectralTopology.HermitianEigenvaluePerturbation.abs_eigenvalue_sub_eigenvalue_le
    (isSymmetric_toEuclideanLin_iff.mpr hAC)
    (isSymmetric_toEuclideanLin_iff.mpr hBC) finrank_euclideanSpace hbound j
  change |hAC.eigenvalues₀ j - hBC.eigenvalues₀ j| ≤ ‖A-B‖ at hh
  simpa only [SpectralTopology.RectangularDilation.eigenvalues_ofReal A hA hAC,
    SpectralTopology.RectangularDilation.eigenvalues_ofReal B hB hBC] using hh

private theorem real_smul_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (c : ℝ) (hc : 0 ≤ c)
    (j : Fin (Fintype.card ι)) :
    (hA.smul (IsSelfAdjoint.all c)).eigenvalues₀ j = c * hA.eigenvalues₀ j := by
  let hAC := hermitian_complex hA
  let hSC := hermitian_complex (hA.smul (IsSelfAdjoint.all c))
  have he : (c • A).map Complex.ofReal = (c:ℂ) • A.map Complex.ofReal := by
    ext i j; simp
  have hSC' : ((c:ℂ) • A.map Complex.ofReal).IsHermitian := he ▸ hSC
  have hh := Quantum.Matrix.LinGProperty.eigenvalues_zero_smul_finite
    (A.map Complex.ofReal) hAC c hc hSC' j
  have hval := Quantum.Matrix.LinGProperty.eigenvalues_zero_eq_of_charpoly
    hSC' hSC (congrArg Matrix.charpoly he).symm j
  rw [hval,
    SpectralTopology.RectangularDilation.eigenvalues_ofReal (c • A) _ hSC,
    SpectralTopology.RectangularDilation.eigenvalues_ofReal A hA hAC] at hh
  exact hh

private theorem gram_hermitian (k t : ℕ) : (normalizedGram k t).IsHermitian := by
  simpa only [normalizedGram, conjTranspose_eq_transpose_of_trivial] using
    (isHermitian_mul_conjTranspose_self (cutoffBlock k t)).smul
      (IsSelfAdjoint.all (((2:ℝ)^(k+t))⁻¹))

/-- The actual normalized fixed-cutoff Gram spectrum has second eigenvalue tending to two. -/
private theorem normalized_gram_second_tendsto (k : ℕ) :
    Tendsto (fun t => (gram_hermitian k t).eigenvalues₀ (secondIndex k))
      atTop (nhds 2) := by
  have hn := (tendsto_iff_norm_sub_tendsto_zero.mp (normalized_gram_tendsto k))
  have hb (t : ℕ) := real_weyl (gram_hermitian k t) (diagonal_hermitian k) (secondIndex k)
  simp only [limiting_diagonal_second] at hb
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) (by simpa only [Real.norm_eq_abs] using hb) hn

private theorem scale_sq (n : ℕ) : ((2:ℝ)^((n:ℝ)/2))^2 = (2:ℝ)^n := by
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]
  convert Real.rpow_natCast 2 n using 1
  congr 1
  norm_num

/-- The actual unequal cutoff dilation has the original normalized second-eigenvalue limit. -/
private theorem cutoff_second_normalized_tendsto (k : ℕ) :
    Tendsto (fun t => cutoffSecond k t / (2:ℝ)^(((k+t:ℕ):ℝ)/2))
      atTop (nhds (Real.sqrt 2)) := by
  have hG := normalized_gram_second_tendsto k
  have hp := hG.eventually (eventually_gt_nhds (by norm_num : (0:ℝ) < 2))
  apply (Real.continuous_sqrt.tendsto 2 |>.comp hG).congr'
  filter_upwards [hp] with t ht
  have hs := real_smul_eigenvalues
    (isHermitian_mul_conjTranspose_self (cutoffBlock k t))
    (((2:ℝ)^(k+t))⁻¹) (by positivity) (secondIndex k)
  have hs' : (gram_hermitian k t).eigenvalues₀ (secondIndex k) =
      ((2:ℝ)^(k+t))⁻¹ *
      (isHermitian_mul_conjTranspose_self (cutoffBlock k t)).eigenvalues₀ (secondIndex k) := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hs
  have hpos : 0 < (isHermitian_mul_conjTranspose_self (cutoffBlock k t)).eigenvalues₀
      (secondIndex k) := by rw [hs'] at ht; exact pos_of_mul_pos_right ht (by positivity)
  simp only [Function.comp_apply]
  rw [cutoff_second_eq_sqrt_gram k t hpos, hs', Real.sqrt_mul (by positivity), Real.sqrt_inv]
  have hroot : Real.sqrt ((2:ℝ)^(k+t)) = (2:ℝ)^(((k+t:ℕ):ℝ)/2) := by
    rw [← scale_sq (k+t), Real.sqrt_sq (by positivity)]
  rw [hroot]
  ring

private theorem block_norm_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) :
    ‖fromBlocks A 0 0 B‖ ≤ ‖A‖ + ‖B‖ := by
  rw [← l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  let u : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => x (Sum.inl i))
  let v : EuclideanSpace ℝ κ := WithLp.toLp 2 (fun i => x (Sum.inr i))
  have hx : ‖x‖^2 = ‖u‖^2 + ‖v‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
    rfl
  have hu : ‖u‖ ≤ ‖x‖ := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by
    nlinarith [sq_nonneg ‖v‖])
  have hv : ‖v‖ ≤ ‖x‖ := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by
    nlinarith [sq_nonneg ‖u‖])
  have hyvec : toEuclideanCLM (n := ι ⊕ κ) (𝕜 := ℝ) (fromBlocks A 0 0 B) x =
      WithLp.toLp 2 (Sum.elim (fun i => toEuclideanLin A u i) (fun i => toEuclideanLin B v i)) := by
    ext w
    cases w with
    | inl i =>
      change (∑ j : ι ⊕ κ, fromBlocks A 0 0 B (Sum.inl i) j * x j) =
        ∑ j : ι, A i j * u j
      simp [Fintype.sum_sum_type, u]
    | inr i =>
      change (∑ j : ι ⊕ κ, fromBlocks A 0 0 B (Sum.inr i) j * x j) =
        ∑ j : κ, B i j * v j
      simp [Fintype.sum_sum_type, v]
  have hy : ‖toEuclideanCLM (n := ι ⊕ κ) (𝕜 := ℝ) (fromBlocks A 0 0 B) x‖^2 =
      ‖toEuclideanLin A u‖^2 + ‖toEuclideanLin B v‖^2 := by
    rw [hyvec]
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr]
  have hAu : ‖toEuclideanLin A u‖ ≤ ‖A‖ * ‖x‖ :=
    ((toEuclideanCLM (n := ι) (𝕜 := ℝ) A).le_opNorm u).trans
      (mul_le_mul_of_nonneg_left hu (norm_nonneg _))
  have hBv : ‖toEuclideanLin B v‖ ≤ ‖B‖ * ‖x‖ :=
    ((toEuclideanCLM (n := κ) (𝕜 := ℝ) B).le_opNorm v).trans
      (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [hy]
  have ha2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hAu
  have hb2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hBv
  nlinarith [show 0 ≤ ‖A‖ * ‖B‖ * ‖x‖^2 by positivity]

private theorem actual_cutoff_perturbation (k t : ℕ) :
    |secondEigenvalue (k+t) - cutoffSecond k t| ≤
      ‖adjacency k‖ + ‖lateAdjacency k t‖ := by
  let e := cutoffEquiv k t
  let M := (adjacency (k+t)).reindex e.symm e.symm
  have hA : (adjacency (k+t)).IsHermitian := (graph (k+t)).isHermitian_adjMatrix ℝ
  have hM : M.IsHermitian := hA.reindex e.symm
  have hD : (cutoffDilation k t).IsHermitian := by
    simpa only [cutoffDilation, conjTranspose_eq_transpose_of_trivial] using
      (isHermitian_zero.fromBlocks (B := cutoffBlock k t) rfl isHermitian_zero)
  let j : Fin (Fintype.card (Vertex k ⊕ LateVertex k t)) := ⟨1, by
    simp only [Fintype.card_sum]; have h := card_vertex_ge_four k; omega⟩
  have he : hM.eigenvalues₀ j = secondEigenvalue (k+t) := by
    have h := hM.sort_roots_charpoly_eq_eigenvalues₀
    have hcp : M.charpoly = (adjacency (k+t)).charpoly :=
      charpoly_reindex e.symm (adjacency (k+t))
    rw [hcp, hA.sort_roots_charpoly_eq_eigenvalues₀] at h
    have hh := congrArg (fun l : List ℝ => l[1]?) h
    have hN : 1 < Fintype.card (Vertex k ⊕ LateVertex k t) := j.isLt
    have hF : 1 < Fintype.card (Vertex (k+t)) := (secondIndex (k+t)).isLt
    simp only [List.getElem?_ofFn, dif_pos hN, dif_pos hF] at hh
    exact Option.some.inj hh.symm
  have hdiff : M - cutoffDilation k t = fromBlocks (adjacency k) 0 0 (lateAdjacency k t) := by
    ext u v
    have h := cutoff_adjacency k t u v
    change adjacency (k+t) (e u) (e v) - cutoffDilation k t u v = _
    rw [h]
    cases u <;> cases v <;> simp [cutoffDilation]
  have hh := real_weyl hM hD j
  rw [he, hdiff] at hh
  exact hh.trans (block_norm_le _ _)

private theorem actual_normalized_perturbation (k t : ℕ) (ht : 1 ≤ t) :
    |secondEigenvalue (k+t) / (2:ℝ)^(((k+t:ℕ):ℝ)/2) -
        cutoffSecond k t / (2:ℝ)^(((k+t:ℕ):ℝ)/2)| ≤
      ‖adjacency k‖ / (2:ℝ)^(((k+t:ℕ):ℝ)/2) +
        3 * Real.sqrt 2 / (2:ℝ)^((k:ℝ)/2) := by
  rw [← sub_div, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2^(((k+t:ℕ):ℝ)/2))]
  have hh := div_le_div_of_nonneg_right (actual_cutoff_perturbation k t)
    (by positivity : (0:ℝ) ≤ 2^(((k+t:ℕ):ℝ)/2))
  rw [add_div] at hh
  exact hh.trans (add_le_add le_rfl (CutoffSpectralBounds.late_adjacency_normalized_le k t ht))

private theorem inverse_scale_tendsto :
    Tendsto (fun n : ℕ => ((2:ℝ)^((n:ℝ)/2))⁻¹) atTop (nhds 0) := by
  have h := (Real.continuous_sqrt.tendsto 0).comp
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1))
  simp only [Real.sqrt_zero] at h
  convert h using 1
  funext n
  change ((2:ℝ)^((n:ℝ)/2))⁻¹ = Real.sqrt ((1/2:ℝ)^n)
  rw [div_pow, one_pow, one_div, Real.sqrt_inv, ← scale_sq n, Real.sqrt_sq (by positivity)]

/-- Along every natural stage, the second largest ordinary adjacency eigenvalue, with
 multiplicity, divided by the original real power 2^(n/2), tends to sqrt two. -/
theorem result : limitClaim := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hε3 : 0 < ε/3 := by positivity
  have hC : Tendsto (fun k : ℕ => 3 * Real.sqrt 2 / (2:ℝ)^((k:ℝ)/2))
      atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using inverse_scale_tendsto.const_mul (3 * Real.sqrt 2)
  obtain ⟨k, hk⟩ := Metric.tendsto_atTop.mp hC (ε/3) hε3
  have hsmall : 3 * Real.sqrt 2 / (2:ℝ)^((k:ℝ)/2) < ε/3 := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity :
      (0:ℝ) ≤ 3 * Real.sqrt 2 / (2:ℝ)^((k:ℝ)/2))] using hk k le_rfl
  obtain ⟨T, hT⟩ := Metric.tendsto_atTop.mp (cutoff_second_normalized_tendsto k) (ε/3) hε3
  have hOld : Tendsto (fun t : ℕ => ‖adjacency k‖ / (2:ℝ)^(((k+t:ℕ):ℝ)/2))
      atTop (nhds 0) := by
    have hh := inverse_scale_tendsto.comp (show Tendsto (fun t : ℕ => k+t) atTop atTop by
      simpa only [Nat.add_comm] using tendsto_add_atTop_nat k)
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using hh.const_mul ‖adjacency k‖
  obtain ⟨U, hU⟩ := Metric.tendsto_atTop.mp hOld (ε/3) hε3
  refine ⟨k + max 1 (max T U), ?_⟩
  intro n hn
  let t := n-k
  have hnt : n = k+t := by dsimp [t]; omega
  have ht1 : 1 ≤ t := by omega
  have htT : T ≤ t := by omega
  have htU : U ≤ t := by omega
  have hc := hT t htT
  have ho : ‖adjacency k‖ / (2:ℝ)^(((k+t:ℕ):ℝ)/2) < ε/3 := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity :
      (0:ℝ) ≤ ‖adjacency k‖ / (2:ℝ)^(((k+t:ℕ):ℝ)/2))] using hU t htU
  rw [hnt, Real.dist_eq]
  have hb := actual_normalized_perturbation k t ht1
  have hab := abs_sub_le (secondEigenvalue (k+t) / (2:ℝ)^(((k+t:ℕ):ℝ)/2))
    (cutoffSecond k t / (2:ℝ)^(((k+t:ℕ):ℝ)/2)) (Real.sqrt 2)
  rw [Real.dist_eq] at hc
  linarith

end D5.S3.Combinatorics.Apollonian.SecondEigenvalueLimit
