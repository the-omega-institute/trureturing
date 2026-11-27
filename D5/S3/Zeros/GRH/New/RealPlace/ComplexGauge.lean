/- GID: D5/S3/Zeros/GRH/New/RealPlace/ComplexGauge
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/RealPlace/ComplexGauge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.RealPlace.ComplexGauge. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/RealPlace/ComplexGauge.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.RealPlace.LevelGauge
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Bruhat.ComplexFloorMeasure
import D5.S3.Zeros.GRH.New.Filling.StableCells
import D5.S3.Zeros.GRH.New.RealPlace.SobolevCell
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Tower method: pairings of kernels bounded floor by floor (see
New.RealPlace.LocalTheorem).

This file: Tower measure at C is Haar with constant bound; level and gauge at C. -/

open Fin Sum Complex ComplexOrder ENNReal EuclideanSpace Filling Fintype Level Matrix MeasureTheory
  Metric ProbabilityTheory Real Set Shape Size WithLp Fin.NatCast MeasureTheory.Measure
  Norms.L2Operator

/-- The numerical hypotheses at a real place: ρ = b^(6n+2) ≥ 8r with b ≥ 2, |κ| = s + 3n + 2 ≥
n⁷, s > 10⁹n³ and ϱ ≥ 10⁸. Here ϱ counts the hyperbolic planes of the `Shape`, n = ϱ + 1, κ
indexes the basis of the summand X₀ and r is the rank of the whole space. -/
structure RealPlaceSizes (𝔰 : Shape) ρ s (b : ℝ) where
  rho_eq : ρ = b ^ (6 * 𝔰.n + 2)
  eight_mul_r_le_rho : 8 * 𝔰.r ≤ ρ
  k_eq : 𝔰.k = s + 3 * 𝔰.n + 2
  mul_cube_lt_s : 10 ^ 9 * 𝔰.n ^ 3 < s
  pow_seven_le_k : 𝔰.n ^ 7 ≤ 𝔰.k
  ten_pow_le_varrho : 10 ^ 8 ≤ 𝔰.ϱ
  two_le_b : 2 ≤ b

variable {𝔰 ρ s b} (hF : RealPlaceSizes 𝔰 ρ s b) {L : ℝ}

/-- The level at ℂ: Haar probability measure on U(X₀), g = 1, the open Euclidean ball of radius
1/4, the box of elements of operator norm ≤ ρ, all positions. -/
@[simps toHyperbolicBasis θ measureH g 𝔅 boxSet
  positions] noncomputable def RealPlaceSizes.complexLevel :
  Level {i // i ≠ 𝔰.k₀} (𝔰.middleGram (1 : ℂ)) 0 := by
  refine ⟨complexBasis 𝔰, cellLaw 𝔰.ϱ ∗ₘ volume.map embedH, volume.map embedH, 1, toLp 2 ⁻¹'
    Metric.ball 0 4⁻¹, {x | ‖x.1.1‖ ≤ ρ}, .univ, ⟨ae_mem_mconv ?_ ?_, map_orbitPoint_cellLaw_top
    ?_⟩, ?_, ?_, ⟨isOpen_ball.preimage (by fun_prop), ?_, ((PiLp.antilipschitzWith_toLp 2
    _).isBounded_preimage isBounded_ball).isCompact_closure⟩, isCompact_U_norm_le _, .univ⟩ <;>
    simp +contextual (disch := with_unfolding_all first | fun_prop | exact measurableSet_floorGroup)
    [↓ae_map_iff, cellChart_mem, embedH_mem_floorGroup, prob_le_one, hF.k_eq]
  intro _ _ h; erw [(exists_toBesselH_eq h).choose_spec, ← map_dirac,
    ← map_mconv_monoidHom (toBesselH 𝔰 1), mconv_dirac, map_mul_right_eq_self]; fun_prop

/-- A chosen constant λ in [0, ∞] such that the measure 𝖬 of the level at ℂ is λ times the Haar
measure of G₁. -/
noncomputable def RealPlaceSizes.haarRatio :=
  (exists_eq_smul_haar volume hF.complexLevel.isMulRightInvariant_groupMeasure).choose

/-- For the level at ℂ, λ = `RealPlaceSizes.haarRatio` has 0 < λ < ∞, 𝖬 = λ·dy, ∫ f d(θ_n ∗ ⋯ ∗ θ₀)
= λ∫_{𝖴\G₁} f for measurable left 𝖴-invariant f ≥ 0, and λ·vol U(k)/vol U(r) ≤ 1, k = |κ|. -/
lemma RealPlaceSizes.haarRatio_spec : (hF.haarRatio ≠ 0 ∧ hF.haarRatio ≠ ∞) ∧
  hF.complexLevel.groupMeasure = hF.haarRatio • ℙ ∧ (∀ f, Measurable f → besselU.FixesLeft f → ∫⁻ g,
  f g ∂hF.complexLevel.upperMeasure 0 = hF.haarRatio * ∫⁻ g, f g ∂besselQuotMeasure) ∧ .ofReal
  (volU 𝔰.k / volU 𝔰.r) * hF.haarRatio ≤ 1 := by
  obtain ⟨s, e : _ = hF.haarRatio • _, _, g, _, eg, ig⟩ := isCompact_U_norm_le (J := 𝔰.J₁) 2,
    (exists_eq_smul_haar volume hF.complexLevel.isMulRightInvariant_groupMeasure).choose_spec,
    hF.k_eq, @exists_chart_ascConv_cellLaw 𝔰 𝔰.n
  have w l : l ≤ 𝔰.ϱ → descConv hF.complexLevel.floorMeasure 0 𝔰.n =
    ascConv cellLaw l ∗ₘ descConv hF.complexLevel.floorMeasure l (𝔰.ϱ - l + 1) ∗ₘ
    ascConv complexPlace.heisenbergMeasure l := l.rec (by simp [ascConv]) fun l ih h ↦ by
    rw [ih, descConv_floorMeasure_succ, ascConv, ascConv_heisenbergMeasure_succ]
    delta cellLaw cellChart cellDensity; simp [Place.weylLaw, mconv_assoc,
      ← pow_mul]; all_goals grind
  have n := by simpa [stackMeasure_zero_eq, ascConv, ascConv_heisenbergMeasure_eq_besselHaar] using
    e
  suffices _ from ⟨⟨(by simp [·, stackMeasure_ne_zero] at e), (by simp [·] at this)⟩, e,
    fun F f j ↦ by simpa using (identDistrib_orbitMeasure_of_unfold (.id _) (.comp ⟨measurable_mul,
    n⟩ (.comp (.prod ⟨by fun_prop, rfl⟩
    (.id _)) measurePreserving_swap)) f measurable_id (j _ ·.2)).lintegral_eq.symm, this⟩
  -- one test function is enough: the indicator f of a ball
  rw [← ENNReal.mul_le_mul_iff_left (measure_sublevel_ne_zero volume) s.measure_ne_top, one_mul,
    ← lintegral_indicator_one s.measurableSet, ← smul_eq_mul, mul_smul,
    ← lintegral_smul_measure, ← n, ← map_inv_eq_self besselHaar, descConv_succ, w _ le_rfl]
  set f := @indicator _ ℝ≥0∞ _ _ 1
  have : Measurable f := by measurability
  have j h k g : f (embedH h * (embedH k * g)⁻¹) = f g := by
    simp [f, indicator, ↓U.norm_inv, ↓norm_embedH_mul, -_root_.mul_inv_rev]
  refine le_lintegral_of_gramSection ‹_› fun k ↦ (lintegral_indicator_le ..).trans' ?_
  erw [← lintegral_bruhat_coords, lintegral_mconv_symm]
  simp [descConv, floorMeasure, ← mconv_assoc, ascConv_heisenbergMeasure_eq_besselHaar, besselHaar,
    ← ascConv.eq_2, ← lintegral_const_mul']
  simp (disch := with_unfolding_all fun_prop) only [ig, lintegral_mconv, lintegral_map]
  refine lintegral_le_const (.of_forall fun t ↦ lintegral_mono_ae
    ((ae_all_iff.2 (ae_eval_ne _ · 0)).mono fun c z ↦ ?_))
  by_cases! h : ‖c (last _)‖ ≤ 1; simp [cellDensity, prod_univ_castSucc, *]
  have D x h b := @(((measurePreserving_conj_bessel mem_besselU0_iff_apply
    besselS_le_normalizer_besselU0 (mem_besselS.2 ⟨_, liftUnitri_mem_besselU x, _, toBesselH_mem h,
    rfl⟩)).mul_left 𝔰.besselHaar₀ ⟨_,
    (besselS_le_normalizer_besselU0 (mem_unitriGroup_of_mem_besselU (liftUnitri_mem_besselU x)) _).1
    (unipotentOf_mem_besselU0 b)⟩).comp (measurePreserving_inv _)).lintegral_comp
  have e := by simpa using eg (.mk0 _ <| z ·)
  have Z γ (v : realFrameGram γ = realFrameGram (g c)) x y :
    realFrameGram ((liftUnitri x)⁻¹ * γ * liftUnitri y) = (unitriMatrix x)ᴴ * Matrix.diagonal
    c * unitriMatrix y := by simp [↓frameGram_inv_mul_mul, ↓frameGram_weylElem_mul,
    realFrameGram_cellChart, cellChart_mem, liftUnitri_mem_besselU, ← init_def, *]
  have B x y := congr($((frameDisc_frameGram_besselU_mul (liftUnitri_mem_besselU x)
    (liftUnitri_mem_besselU y) 1).trans (e ▸ frameDisc_weylElem_mul cellChart_mem 1)).re)
  simp only [Z, realFrameGram_cellChart h, RCLike.star_def, mul_conj'] at B; norm_cast at B
  have o x y := mem_openCell_iff.2 ((B x y).trans_gt (by simpa [-Units.coe_prod]))
  simp [lintegral_const_mul', ← mul_assoc, row, gramDiscReal, B, o]
  gcongr 1; clear * - h
  simp (disch := bound) [cellDensity, prod_univ_castSucc, ENNReal.ofReal_mul', openCellConst,
    pow_add, ← norm_prod, enorm, Finset.prod_pow]; ring; rfl
  erw [@lintegral_lintegral_swap (_ × _)]; gcongr with w
  repeat erw [lintegral_prod]
  gcongr with x; rw [lintegral_lintegral_swap, lintegral_prod]; gcongr 1 with y
  obtain ⟨q, p, b, r, e⟩ := exists_eq_mul_gramSection_mul (o x y) (Z (embedH w⁻¹ * g c * embedH t⁻¹)
    (by simp [realFrameGram_mul_invariant, Subgroup.mem_sup_right]) ..)
  rw [← D y (r * w⁻¹) b]; gcongr 1
  rw [← D x (p * k⁻¹) q]
  simp [← j (r * w⁻¹) (p * k⁻¹) (_ * a.1⁻¹), eq_inv_mul_of_mul_eq e]; group; rfl
  all_goals fun_prop (disch := exact isOpen_openCell.measurableSet)

instance :
  hF.complexLevel.groupMeasure.IsHaarMeasure := by simp [hF.haarRatio_spec, IsHaarMeasure.smul]

attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort

attribute [local simp ←] ofReal_coe_nnreal ENNReal.ofReal_mul ENNReal.ofReal_pow dotProduct_mulVec

attribute [local simp] star_mulVec MeasureTheory.volume_pi_closedBall Size.vecsOfSize inclMatrix
  pi_norm_le_iff_of_nonneg

/-- Let n = ϱ+1, |ι| = s+1+3n ≤ L, L ≥ 4, and rank C ≤ 3n. Some matrix O with orthonormal
columns has CO = 0 and, for all j, the integral of (36/|Oᴴu|²)^s over the u in ℂ^ι with all
|u_i| ≤ L^j is at most L^{198n(j+1)}. -/
lemma exists_orthonormal_ker_lintegral_le {m ι : Type} [Fintype m] [Fintype ι] (C : Matrix m ι ℂ)
  (_ : card ι = s + 1 + 3 * 𝔰.n) (h4 : 4 ≤ L) (_ : C.rank ≤ 3 * 𝔰.n) (c : card ι ≤ L) : ∃ (D :
  Finset ι) (O : Matrix ι D ℂ), C * O = 0 ∧ Oᴴ * O = 1 ∧ ∀ j, ∫⁻ u in {u | ∀ i, ‖u i‖ ≤ L ^ j},
  (.ofReal (‖star (Oᴴ *ᵥ u) ⬝ᵥ Oᴴ *ᵥ u‖ / 36))⁻¹ ^ s ≤ (.ofReal L ^ 2) ^ (99 * 𝔰.n * (j + 1)) := by
  have H := C.isHermitian_conjTranspose_mul_self; let Q := H.eigenvectorUnitary
  let ⟨D, hD, d⟩ := @Finset.exists_subset_card_eq _ {i | H.eigenvalues i = 0} s.succ (by grind
    [card_subtype_compl, card_subtype, H.rank_eq_card_non_zero_eigs, rank_conjTranspose_mul_self])
  use D, Q.1.submatrix id (↑), (conjTranspose_mul_self_mul_eq_zero ..).1 (ext fun a i ↦
    congr($(H.mulVec_eigenvectorBasis i) a).trans (by simp; grind)), ext (congr($(Q.2.1) · ·).trans
    (by simp)), fun j ↦ .trans' ?_ ((lintegral_mono_set fun u h ↦ ?_).trans_eq
    (((((@measurePreserving_normSq_sphereDensity _ _ (D.card_pos.1 ?_).coe_sort).prod (.id _)).comp
    (volume_preserving_piEquivPiSubtypeProd ..)).comp (complexPlace.measurePreserving_mulVec Q.1ᴴ
    (det_of_mem_unitary (star Q).2).1)).setLIntegral_comp_preimage (f := fun p ↦
    (.ofReal (p.1 / 36))⁻¹ ^ s) (s := Iic (L * (L * L ^ j) ^ 2) ×ˢ closedBall 0 (L * L ^ j)) ?_ ?_))
  erw [setLIntegral_prod_symm]; simp [restrict_withDensity, Iic_inter_Ioi]
  grw [lintegral_withDensity_le_lintegral_mul, setLIntegral_le_iSup_mul,
    iSup₂_le (a := .ofReal (4 * 3 ^ 144))]
  · simp (disch := positivity) [*]
    grw [pi_gt_three, pi_le_four, pi_le_four, h4, h4, h4]; ring; gcongr <;> bound
  simp; intros
  grw [← exp_one_lt_three, exp_one_pow, ← pow_div_factorial_le_exp _ _ s, pi_le_four]
  simp (disch := finiteness) [← toReal_le_toReal, field, pow_succ, div_pow, d, ← mul_pow]; bound
  any_goals measurability
  have k i : ‖(Q.1ᴴ *ᵥ u) i‖ ≤ L * L ^ j := (norm_sum_le ..).trans (by
    simp; grw [entry_norm_bound_of_unitary Q.2, h _, ← c]; simp)
  simp (disch := positivity) [k, ↓star_dot_self_eq_norm_sq, norm_sq_eq]
  grw [k, ← c, ← D.card_le_univ]; simp

lemma RealPlaceSizes.ten_le (hF : RealPlaceSizes 𝔰 ρ s b) : 4 ≤ ρ :=
  hF.eight_mul_r_le_rho.trans' (by simp; bound)

/-- For L ≥ ρ, the gauge of the level at ℂ with sizes B_j = {x : |x| ≤ L^j} and constant Λ = L². -/
noncomputable def RealPlaceSizes.gauge (hF : RealPlaceSizes 𝔰 ρ s b) (hρ : ρ ≤ L := by rfl) :
  Gauge hF.complexLevel := by
  obtain ⟨hk, _, h4⟩ := hF.k_eq, hF.eight_mul_r_le_rho, hF.ten_le.trans hρ
  refine ⟨⟨fun j ↦ {x | ‖x‖ ≤ L ^ j}, ?_, fun c k ↦ by
    rify at c; simp_all [pow_succ']; grw [norm_sum_le, k]; simp; bound, ?_, ?_, by simp [
    inv_eq_left_inv IsHermInvolution.mul_self,
    (entry_norm_bound_of_unitary IsHermInvolution.mem_unitary ..).trans, h4.trans']⟩,
    .ofReal L ^ 2, fun _ ↦ by simpa [closedBall] using isCompact_closedBall (0 : ℂ) _, ?_, ?_, by
    simp [HasMatSize, apply_ite, complexBasis]
    grind [norm_add_le, norm_one, norm_I], by simp +contextual [HasMatSize, (norm_apply_le_l2_opNorm
    ..).trans, hρ.trans'], fun u h i ↦ by simp_all; grind [PiLp.norm_apply_le (toLp 2 u) i], ?_, by
    simp (disch := positivity) [← mem_closedBall_zero_iff, -mem_closedBall]
    grw [pi_le_four, h4]; ring; bound, fun σ _ j _ h ↦ .trans_eq ?_ (mul_one _), ?_⟩
  iterate 6 simp (disch := positivity) [pow_add, ← ofReal_norm, pow_right_comm, abs_of_pos] <;>
    bound [two_le_pi, sq_nonneg (L - 1)]
  · grw [Measure.map_apply, prod_apply_symm, complexPlace_skewMeasure, lintegral_map_le,
      ← lintegral_cauchyPDF_eq_one 0 one_ne_zero, ← lintegral_const_mul]
    gcongr with r; grw [measure_mono (t := closedBall 0 (2 * L ^ j / ‖r + Complex.I‖) ×ˢ
      closedBall 0 (L ^ j)) fun p h ↦ ?_]
    · simp (disch := positivity) [norm_eq_sqrt_sq_add_sq, volume_eq_prod, cauchyPDF,
        cauchyPDFReal, field]
      ring; grw [pi_le_four, pi_le_four, h4, h4, h4]; ring; bound
    simp (disch := positivity) [Place.flatChart, neg_add_eq_sub, mul_assoc,
      inv_def (starRingEnd ℂ _), ← mul_sub] at h ⊢; nth_grw 1 [← abs_im_le_norm (_ - _),
      le_div_iff₀ (by simp [Complex.ext_iff]), norm_add_le] at *
    simp_all [entrywise, ← Finset.sum_add_distrib, mul_comm]; linarith
    all_goals measurability
  let N := (1 - 𝔰.J₁).submatrix (.map id (inl ∘ inr)) id
  set e := hF.complexLevel.orthonormalPart
  intro x _ y _ v W
  refine (exists_orthonormal_ker_lintegral_le (fromRows v (fromRows (N * x⁻¹.1.1 * e) (N * (x *
    y)⁻¹.1.1 * e))) (by simp [volumeExponent, hk]; lia) h4 (by grw [rank_le_card_height]; simp; lia)
    (by simp_all; bound)).elim fun _ ⟨O, z, o, I⟩ ↦ ⟨_, by fun_prop, fun u ↦ ?_, I⟩
  clear * - z o
  generalize hr : star _ ⬝ᵥ Oᴴ *ᵥ u = r
  by_cases r = 0; simp [*]
  have B : closedBall 0 (|√‖r‖| / 9) ⊆ (star u ⬝ᵥ ·) '' W := fun t h ↦ by
    let w := O *ᵥ (t / r) • Oᴴ *ᵥ u
    have k {g : 𝔰.G₁} (a : N * g.1.1 * e * O = 0) : ‖toLp 2 (g.1.1 *ᵥ e *ᵥ w)‖ ≤ 9⁻¹ := by
      have n := congr(‖$(U.form_mulVec_mulVec g (e *ᵥ w) (e *ᵥ w))‖)
      rw [(by clear * -; simp [mulVec_eq_sum, funext_iff, N, splitGram, middleGram]; grind : ∀ z,
        N *ᵥ z = 0 →
        𝔰.J₁ *ᵥ z = z) _ (by simp [w, ← Matrix.mul_assoc, a]), star_dot_self_eq_norm_sq] at n
      simp [show eᴴ *
        (𝔰.J₁ * e) = 1 by ext; simp [e, complexBasis, mul_apply, splitGram, middleGram]; grind] at n
      simp_all [-mulVec_smul, w, ← Matrix.mul_assoc]; grw [← sq_le_sq₀, n, h, h] <;> simp [field]
    use w, ⟨by simp [-mulVec_smul, w, show v * O = 0 from congr(toRows₁ $z)], (by simp; grind
      [norm_sub_le] : _ → _ → _) (k congr($z ∘ inr ∘ inl)) (k congr($z ∘ inr ∘ inr))⟩; simp_all [w]
  grw [← B, measure_mono (t := closedBall 0 (3 / |√‖r‖|)) fun t h ↦ ?_]
  simp (disch := positivity) [field]; bound [pi_le_four, pi_gt_three]
  obtain ⟨c, w, ⟨z, a, y, b, o⟩, e⟩ := @norm_inner_J₁_le 𝔰,
    (@B (|√‖r‖| / 9) (by simp)).imp (And.imp_left <| h ·)
  replace o := congr(‖$o‖).le
  simp [e, ← mem_ball_iff_norm', dotProduct_comm (star _), inner_toLp_toLp,
    (toLp_surjective 2).forall] at *
  grw [norm_sub_le, c, c, (norm_lt_of_mem_ball a.2).le, a.1.le, norm_lt_of_mem_ball b.2] at o
  simp [field]; bound
