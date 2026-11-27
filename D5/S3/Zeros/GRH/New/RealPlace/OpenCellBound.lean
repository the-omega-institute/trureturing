/- GID: D5/S3/Zeros/GRH/New/RealPlace/OpenCellBound
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/RealPlace/OpenCellBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.RealPlace.OpenCellBound. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/RealPlace/OpenCellBound.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Filling.StableCells
import D5.S3.Zeros.GRH.New.RealPlace.SobolevCell
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Real-place Bessel integrals: band limits, energy and open-cell bound (see
New.Filling.FillingData).

This file: Mean-square bound for Bessel integrals on the open cell. -/

open Finset Fintype Subgroup Matrix MeasureTheory Norms.L2Operator ProbabilityTheory
  ENNReal Metric IdemSemiring Measure ComplexConjugate Fin
attribute [-instance] toMulLeftMono toCanonicallyOrderedAdd

/-- Open-cell bound. For ρ ≥ B, 𝗀(Z(γ)) > 0, Box(ρ) meeting γBox(ρ): there are compact A, random
t ∈ 𝖴⁰H and n of mass ≤ `cellMass` with 𝔼‖∫_A φ(y) W(γty)W(ty)* dy‖² ≤ ∫|φ|² dn; almost
surely A contains the y ∈ Box(ρ) with R(γty) ≤ ρ. -/
lemma BesselSystem.open_cell {𝔰 B f ρ γ y} (X : BesselSystem 𝔰 B f) (hγ : 0 < gramDiscReal
  (realFrameGram γ)) (hy : y ∈ frameBox ρ) (hz : γ⁻¹ * y ∈ frameBox ρ) (hρ : B ≤ ρ) : ∃ A n m, ∃ t :
  U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) × (𝔰.middleGram (1 : ℂ)).besselU0 → _, IsCompact A ∧ Measurable t ∧
  IsL2Contraction m (volume.restrict A) n (fun (i, j) x y ↦
  X.W .full (γ * t x * y) i * conj (X.W .full (t x * y) j)) ∧ IsProbabilityMeasure m ∧
  IsFiniteMeasure n ∧ n.real .univ ≤ cellMass γ X.deg ρ (card X.I) ∧ ∀ᵐ x ∂m, t x ∈ besselU0 ⊔
  besselH ∧ ∀ y ∈ frameBox ρ, besselSize (γ * t x * y) ≤ ρ → y ∈ A := by
  obtain ⟨hB, _⟩ := X.eight_mul_rank_le, X.deg_pos; rw [cellMass]; choose h8 m h1 using show
    8 * (𝔰.ϱ + 1) ≤ ρ ∧ 𝔰.n ≤ ρ ∧ 1 ≤ ρ by simp at hB; grind
  have hZ a c := (norm_realFrameGram_le_mul ..).trans (by grw [hy a, hz c, ← sq])
  set Z := realFrameGram γ; set M := _ / gramDiscReal _; choose hγ' r using show M⁻¹ ≤
    gramDiscReal Z ∧ ρ ≤ M by
    simp [field]
    grw [gramDiscReal_eq (mem_openCell_iff.2 hγ).1, cornerDefect, sub_le_self, norm_det_le_norm_pow,
      l2_opNorm_le_of_apply hZ, Fintype.card_fin, m, m]; ring; repeat bound
  clear_value M
  grw [r] at hZ h8 h1; have l Z a b :=
    mem_openCell_and_bounds_of_near (Z := Z) a h8 b le_rfl (mem_ball_self (by bound))
  obtain ⟨q, -, hO, z', -⟩ := le_self_pow₀ h1 (n := 9 * 𝔰.n) nofun, l _ hγ' hZ
  obtain ⟨s, u, k, v, j, e⟩ := le_self_pow₀ (h1.trans q) (n := 5) nofun,
    exists_eq_mul_gramSection_mul hO rfl
  choose A Ω hA hΩ h0 hv hs hβ3 hβ1 using exists_tube (s.trans' (by bound))
  obtain ⟨n, c, w, o, t, R⟩ := besselU0_sup_besselH_le_besselS
    (mul_mem_sup (unipotentOf_mem_besselU0 u) (toBesselH_mem k)), 𝔰.openCellConst_pos, toReal_pos h0
    hv, hA.measurableSet, le_self_pow₀ (s.trans' (by bound)) 𝔰.ϱ.succ_ne_zero,
    X.tail.isBesselFunction .full
  have V := lintegral_mul_le_of_frameMatrix_le (R.stronglyMeasurable.enorm.pow_const 2)
    (by fun_prop) (by simp +contextual
    [R.enorm_besselS_mul]) hβ1 (by simp_intro y h s _ g ..; simpa using! ((norm_apply_le_l2_opNorm
    ..).trans (norm_mul_le_of_le (hs _ g) ((U.norm_inv _).trans_le (hs _ h))))) (by bound)
  grw [X.tail.lintegral_sq_full_eq, (by bound : 2 ≤ M)] at V
  have T (x : _ × besselU0) := mul_mem
    (mul_mem_sup (unipotentOf_mem_besselU0 v) (toBesselH_mem (j * x.1⁻¹))) (mem_sup_left x.2⁻¹.2)
  refine' ⟨A, _, _, _, hA, by fun_prop, fun φ C mφ hC ↦ _, cond_isProbabilityMeasure_of_finite
    .., @smul_finite _ _ _ (isFiniteMeasure_withDensity (V.trans_lt (by finiteness)).ne) .., _,
    ae_cond_of_forall_mem (.prod .univ hΩ) fun x hx ↦ ⟨T x,
    (mul_left_surjective (x.2 * embedH x.1)).forall.2 fun z ↦ _⟩⟩
  · have i := (volume.integrableOn_of_bounded hA.measure_ne_top
      (by fun_prop) (.of_forall hC)).integrable_indicator o
    have b j := by simpa [Pi.mul_def] using i.mul_of_top_left (R.memLp_top.eval_piLp j).star
    have S {β} hi b := funext (eval_integral_piLp (R.integrable_smul (x := β) hi b).eval_piLp)
      ▸ euclidean_enorm_sq_eq_sum _
    have c g j := S ((starL' ℝ).integrable_comp_iff.2 ((R.integrable_smul i g).eval_piLp j))
    have E x g j :=
      (R.enorm_integral_besselS_mul (besselU0_sup_besselH_le_besselS (T x)) .. ▸ c ..) ▸ c g j 1
    simp_rw [← RCLike.enorm_conj (∫ _, _), ← integral_conj] at E
    simp [sum_prod_type, ← mul_assoc, ← integral_indicator o,
      Set.indicator_mul_left, -Subtype.forall] at E ⊢
    grw [(E ..).le, lintegral_congr fun x ↦ sum_comm.trans (sum_congr rfl fun j _ ↦ .trans (by
      simp [e, mul_assoc]; ac_rfl) (R.enorm_integral_besselS_mul n _ (gramSection Z *
      (x.2 * embedH x.1)⁻¹) ▸ S (b j) _).symm), ProbabilityTheory.cond, lintegral_smul_measure,
      lintegral_finsetSum, fun j ↦ (lintegral_gramSection_integral_le (by bound) (X.hasSchurBound _
      (t.trans' (by bound))) (half_pos hγ) (mem_openCell_and_bounds_of_near hγ' h8 hZ (s.trans t))
      (by fun_prop) (b j) (by simp +contextual [hs])).trans'
      (lintegral_mono_set fun u h ↦ hs _ (by simpa using hβ3 _ h.2 1 (by simp; bound))), ← mul_sum,
      ← lintegral_finsetSum', lintegral_withDensity_eq_lintegral_mul, ← smul_mul_assoc]; gcongr 1
    simp [Set.indicator, apply_ite, mul_comm, mul_pow, euclidean_enorm_sq_eq_sum,
      mul_sum]; repeat fun_prop
  iterate 4 simp [*, mul_eq_top, real_def, not_le_of_gt, half_pos hγ]
  grw [V]; simp (disch := positivity) [field]; ring; gcongr <;> simp; finiteness
  simp [e, frameBox, mul_assoc, frameVector_mul, mem_sup_left, mem_sup_right]
  -- two frames: a point with bounded frame whose image under `gramSection Z` has bounded size is
  -- bounded
  grw [r, ← mul_assoc, besselSize_besselS_mul n]; refine' fun h hy ↦ hβ3 _ hx.2 _ _
  choose w hw f using exists_norm_le_of_besselSize_le hy
  obtain ⟨b, K, this⟩ := (norm_frameVector_le · |>.trans f), congr($(submatrix_mul_besselFrame hw
    (w * (gramSection Z * z))⁻¹.1.1 id) * $(realFrameGram_eq_frameMatrix_mul (gramSection Z)
    hw)ᴴ⁻¹), congr((gramSection Z * z)⁻¹ * $((coe_gramSection hO).trans (sectionMatrix.eq_1 ..)))
  choose _ _ N _ using l (realFrameGram (w * gramSection Z)) (by
    simpa [← Filling.frameDisc_frameGram_besselU_mul hw (one_mem _), realFrameGram_gramSection hO,
      gramDiscReal]) (by grw [norm_realFrameGram_le_mul, b, sq]; simp_intro ..; grw [h])
  grw [q] at h b h8; set Q := M ^ _
  grw [norm_embedH_mul, pow_succ', ← h8,
    ← norm_le_of_mem_frameBox _ (h · |>.trans (by bound))]; simp; bound
  intro
  simp [← sectionMatrix_mul_frameCols, ← Matrix.mul_assoc, Matrix.mul_sub, mul_add,
    ← coe_gramSection hO, realFrameGram_gramSection hO, ← mul_inclMatrix,
    det_eq_one_of_unitriangular (frameMatrix_unitriangular hw)] at this K ⊢; rw [this, K]
  simp [diagLast, eq_comm, mul_apply, diagonal, inclMatrix, sum_univ_castSucc, sectionCoeff,
    ← Pi.add_def, ← sum_fn, ← Matrix.mul_inv_rev]; grw [norm_add₃_le, norm_sum_le, norm_sum_le]
  norm_num [frameVector, PiLp.norm_eq_of_L2, mul_pow, ← sum_mul, forall_fin_succ',
    ← conjTranspose_nonsing_inv, ← mul_assoc, -sum_sum_type] at h b ⊢
  grw [b.1, b.2, h.1]
  repeat grw [norm_apply_le_l2_opNorm]
  grw [N, z']; simp [field]; nlinarith
