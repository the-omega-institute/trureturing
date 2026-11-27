/- GID: D5/S3/Zeros/GRH/New/Filling/ThinClasses
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Filling/ThinClasses
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Filling.ThinClasses. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Filling/ThinClasses.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Filling.SchurTest
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Incoherent and degenerate pairs are negligible (see New.Filling.CrudeEnergy).

This file: Schur-test bound for total amplitude of a thin double-coset class of terms. -/

open AddSubgroup Fin DoubleCoset ENNReal Finset Fintype LinearMap MatMul Matrix MeasureTheory Metric
  Pointwise Real Norms.Elementwise

attribute [-simp] Nat.cast_mul

attribute [local simp] frameVolume_mul_left Filling.minorNorm Filling.basisScale prod_eq_zero_iff
  Subgroup.mem_sup_left realFrameGram_mul_invariant div_pow mul_pow unipotentOf_mem_besselU0

variable {E} [Field E] [CMType E] [StablyUnram E] {𝔰} {S : Filling E 𝔰} [S.IsAdmissible] {j :
  Fin (𝔰.ϱ + 2)} {c s c' γ} (hk : γ ∈ S.termsOver c s c') (h : S.HasLevel j γ)

include hk h

omit [StablyUnram E] [S.IsAdmissible] in
/-- Let γ have level j and h_c⁻¹γh_c' ∈ K. Every δ in the class of γ has level j, the same Z and
the same reduction, and the middle parts of the frame images of h_c⁻¹δh_c' and h_c⁻¹γh_c'
differ by rows in g·(Ô-span of the first ϱ rows of Z(h_c⁻¹γh_c')); Z(γ) = (h(f_j, γf_l)), f the
frame. -/
lemma Filling.terms_of_class_spec δ (m : δ ∈ doubleCoset γ (S.classUnip₀ c) (S.classUnip₀ c')) :
    S.HasLevel j δ ∧ S.frameProducts δ = S.frameProducts γ ∧ δ ∈ S.termsOver c s c' ∧ ∀ i,
  (frameMiddle (S.termPosition c c' δ) - frameMiddle (S.termPosition c c' γ))ᴴ.col
  i ∈ S.gIdele • colLattice (Ô E) (xRows ((S.latMiddle _).frameGram (S.termPosition c c' γ)))ᴴ := by
  obtain ⟨u, ⟨U, hu⟩, x, ⟨X, hx⟩, rfl⟩ := mem_doubleCoset.1 m
  refine ⟨(isStable_hasLevel j _ (inv_mem hu.1) _ hx.1 _).2 h, (frameGram_inv_mul_mul (inv_mem hu.1)
    hx.1).trans (by simp_all [mem_besselU0_iff.1]), by simpa using termsOver.mul (.mul U.2 hk) X.2,
    fun i ↦ ⟨_, ⟨_, (star_mem_Ô <| (S.principalLevel_eq_unitaryLevel.le (x :=
    termPosition ..) U.2).2 (.inr (.inl i)) <| eStar ·), rfl⟩, ?_⟩⟩
  rw [frameMiddle, show frameImage _ = frameImage (S.termPosition c c u * S.termPosition c c' γ) by
    simp [↓frameImage_termPosition, coe_termPosition,
      classCoord, ↓frameImage_mul_of_mem_besselU0 hx, ↓frameImage_mul]]
  simp [funext_iff, mul_apply, mulVec_eq_sum, frameGram, splitGram, apply_inr_of_mem_besselU
    (hu.1.termPosition_mem_besselU c), show star S.gIdele = S.gIdele by ext; simp [gIdele],
    ← Units.smul_def, mul_comm]

set_option synthInstance.maxHeartbeats 200000 in
seal Finset.univ Finset.sum Finset.prod in
/-- Under `Filling.IsAdmissible`, if γ has level j and h_c⁻¹γh_c' ∈ K, the sum of
`Filling.schurIntegral` over 𝖴⁰_c(g)γ𝖴⁰_c'(g) is at most
ν·#`Filling.BesselCoord`·τ²·(b⁴g)^(−min(ϱ,j)kf)·(i/√D)^(k+1), τ = `Filling.tailScale`, i the index
`Filling.xRowsIndex` of h_c⁻¹γh_c', D = `Filling.minorNorm` j γ, ν = `Filling.unipCovolume`,
f the number of infinite places. -/
lemma Filling.tsum_schurIntegral_le : ∑' δ : doubleCoset γ (S.classUnip₀ c) (S.classUnip₀ c'),
  S.schurIntegral c c' δ ≤ .ofReal (S.unipCovolume * (card S.BesselCoord * S.tailScale ^ 2 *
  (S.b ^ 4 * S.g)⁻¹ ^ (min 𝔰.ϱ j * 𝔰.k * numInfPlaces E) * (S.xRowsIndex j (S.termPosition c c'
  γ) / √(S.minorNorm j γ)) ^ (𝔰.k + 1))) := S.of_size_bounds fun g τ b t _ _ N ν o _ _ ↦ by
  have D v : _ = _ * Φ v (leadingMinor (S.frameProducts γ) j) :=
    det_submatrix_realFrameGram_ratToInf ..
  let e : IndexBelow j ↪ Fin j := ⟨fun i ↦ ⟨i, i.2⟩, id fun _ ↦ by grind⟩
  let R v := diagonal fun i : IndexBelow j ↦ π * S.g / (S.b * S.basisScale v (.inl i))
  let s (x : _ → Matrix _ (IndexBelow j) ℂ) v :=
    unipotentOf (inclMatrix ℂ (·.1 : IndexBelow j → _) * (x v * R v)ᴴ, 0)
  have := (by fun_prop : Continuous s).measurable
  simp (disch := fun_prop) [schurIntegral, ← lintegral_tsum]
  grw [lintegral_boxCutoff_le_of_average c volume this (by simp [s]) _ (fun u hu y ↦ by
    conv_lhs => rw [doubleCoset, ← smul_coe_set hu, smul_mul_assoc, smul_mul_assoc,
      ← Set.image_smul, tsum_image (S.schurWeight c' · _) (by simp)]
    simp [schurWeight, ratToInf_mem_besselU0 hu.2, doubleCoset]) (ball 0 1) (by
    repeat refine (Measure.pi_ball _ _ one_pos).ge.trans' (one_le_prod'' fun _ ↦ ?_)
    simpa using! one_le_two.trans two_le_pi) fun u hu y hy ↦ ?_]; rotate_right
  set X := @ball _ (_) _ 1
  choose G _ O T using terms_of_class_spec hk h
  grw [lintegral_tsum (by clear_value s; fun_prop), tsum_le_of_colouring _ ((relIndex_pointwise_smul
    S.gIdele ..).trans_gt (one_le_xRowsIndex_and_saturationIndex hk h).1).ne' T (∫⁻ x in X,
    S.schurWeight c' · (u * s x * y)) _ fun B (hB : ∀ ⦃_⦄, _) p₀ i r ↦ ?_]
  choose! l _ M using fun p h ↦ (G _ (hB i)).exists_frameImage_toRows₂_eq_add (.subtype (·.1 < ↑j))
    (by simp) (G _ (hB h)) (by simp [*])
    (Submodule.mem_sup_left <| by simpa [*, frameGram_termPosition, Pi.sub_def] using! r p h _ i ·)
  let L (l : type_of% (l p₀)) v := l.map (Φ v · * (S.b / π))
  choose K _ iK hK using fun v ↦ exists_kernel_frameVolume_le (hy v).2 e (R v) (by simp [R, o.ne'])
    ((D v).trans_ne (by simp [h.2]))
    (frameX₀Part ((u v)⁻¹ * S.ratToInf p₀ v) * inclMatrix ℂ (castLE j.is_le))
  apply (mul_le_mul_right ((lintegral_pi_prod ..).trans_le (prod_mono' iK)) _).trans'
  have := IsOpen.measurableSet (s := X) isOpen_ball
  grw [← volume_pi, ← lintegral_const_mul, ← tsum_congr fun p ↦
    (lintegral_sub_right_eq_self _ (L _)).trans (lintegral_indicator ‹_› _), ← lintegral_tsum]
  any_goals fun_prop
  gcongr
  set w := fun _ : B ↦ _
  choose q W using (w.support.pairwise_eq_iff_exists_eq (l ·)).1 fun _ hp _ h _ ↦ sub_eq_zero.1
    (ext fun a _ ↦
    col_eq_zero_of_norm_lt_one (c := c) (by simp [Matrix.map_sub, IsIntMatrix.sub, *]) a fun v ↦ by
    simp [w] at h hp
    have e := X.sub_mem_sub h.1 hp.1
    simp [X, L, pi_norm_lt_iff, norm_lt_iff, ← sub_mul,
      ← lt_div_iff₀ (by positivity : 0 < |S.b| / π)] at e ⊢
    grw [e, pi_le_four] <;> simp [field, Nonempty.intro a]; nlinarith [S.k_le_b])
  grw [tsum_classCutoff_box_le (V := (piMap fun v ↦ ((Fintype.linearCombination ℂ _).restrictScalars
    ℝ).compLeft _).range) (fun _ ↦ Subtype.ext) (fun p hp ↦ ⟨O _ (hB p.2), by simp, by
    exact (by simpa [schurWeight, boxCutoff, W p hp] using hp :).2.1.1, ?_⟩) fun p a r b ↦
    ⟨_, funext₂ fun v _ ↦ (frameVector_sub_eq_sum (by simp [M, W _ a, W _ b]) ..).symm⟩,
    pow_le_tailScale (by grw [finrank_range_le]; simp; lia)]
  swap; grw [X.indicator_le_self .., schurWeight, boxCutoff, Set.indicator_le_self .., W p hp]
  gcongr
  cases mem_besselU0_iff_unipotentOf.1 (hu v)
  grw [← hK v _ _ _ (((G p _).1.ratToInf v).besselU_mul (inv_mem (mul_mem (hu v)
    (unipotentOf_mem_besselU0 _ : s (a - L q) v ∈ _))).1)] <;> simp [mul_assoc, s, *,
    frameX₀Part_unipotentOf_inv_mul, ← ext_iff]
  simpa [↓mul_inclMatrix, ↓basisScale_besselFrame, L, W p hp, by simpa using congrFun₂ (M _ p.2),
    mul_apply, mul_sum, R, *, add_left_comm (_ * _), add_mul, add_sub, e, ← castSucc_mk, sum_mul,
    inclMatrix, frameX₀Part, diagonal_apply, add_assoc, sub_eq_iff_eq_add'] using fun _ _ ↦
    sum_congr _ _ (by have := o.ne'; simp [*, field, ← Complex.ofReal_pow])
  have := (one_le_prod_norm_Φ · h.2.1) (.det fun _ _ ↦ isIntegral_frameProducts hk ..)
  simp (disch := intros; positivity) only [abs_norm_eq_prod_norm_sq, prod_pow, pow_mul', D,
    xRowsIndex, relIndex_pointwise_smul, sqrt_sq, ← div_pow, ← ofReal_prod_of_nonneg, ← ofReal_mul,
    pow_add _ 𝔰.k, ← ofReal_natCast, ofReal_le_ofReal_iff, prod_mul_distrib]
  have C (x : ℝ) : x ^ j.1 = x ^ (j - 𝔰.ϱ) * x ^ min 𝔰.ϱ j := by simp [← pow_add, min_comm 𝔰.ϱ]
  apply le_of_le_of_eq
    (by grw [show _ ^ 𝔰.n ≤ S.tailScale / ((∏ v, ‖Φ v _‖) / (S.N ^ numInfPlaces E) ^ (j - 𝔰.ϱ)) by
    simp
    grw [t, ← one_le_abs_kappa, N_le, le_self_pow₀ this, ← N.nat_succ_le]
    simp [field, ← pow_mul, ← pow_add]; grw [j.is_le, pow_le_tailScale]
    repeat lia, C, show _ ^ (_ - _) ≤ (S.g / S.b ^ 6) ^ min 𝔰.ϱ j by
    grw [← le_g, t]; simp [field, ← pow_mul, ← pow_add]
    gcongr; grind [S.ϱ_le], two_le_pi, ← Nat.factorial_le bot_le])
  simp [R, C, Fintype.card_subtype, card_filter_val_lt, pow_right_comm _ _ 2, prod_pow_eq_pow_sum,
    e, ← sum_of_injective e e.2 _ (𝔰.ϱ - ·) (by simp [Fin.forall_iff]; lia) fun _ ↦ rfl]
  field

attribute [local instance] Side.cut

/-- Let γ have level j, lie over (c, s, c') and satisfy ∏_v|𝗀(γ)|_v ≤ N^f·`Filling.minorNorm` j γ.
Then the absolute amplitudes, for cut Bessel functions, over the double coset
𝖴⁰_c(g)γ𝖴⁰_c'(g) sum to at most ν·`Filling.classSize` j (𝗀*), 𝗀* = `Filling.classGauge` j c c' γ,
ν = `Filling.unipCovolume`. -/
lemma Filling.tsum_amplitudeAbs_class_le (k : S.termDiscNorm γ ≤ S.N ^ numInfPlaces E * S.minorNorm
  j γ) : ∑' δ : doubleCoset γ (S.classUnip₀ c) (S.classUnip₀ c'), S.amplitudeAbs c c' δ ≤
  .ofReal (S.unipCovolume * S.classSize j (S.classGauge j c c' γ)) := of_size_bounds (by
  intros; let : MeasurableSpace (S.G E) := ⊤; have := h.minorNorm_pos
  grw [classSize, classGauge, max_eq_right k, ← show S.N ^ numInfPlaces E * S.tailScale ^ 8 /
    (S.tailScale ^ 32) ^ min 𝔰.ϱ j * S.besselEnergy ≤ ite .. by
    grw [N_le, ← pow_mul, pow_le_tailScale (by lia), ← pow_succ']; split
    grw [← IsAdmissible.besselEnergy_le, div_le_self]
    any_goals gcongr
    repeat bound, ← ENNReal.pow_le_pow_left_iff, ← lintegral_count, sq_lintegral_le .of_discrete
    .of_discrete fun δ ↦ amplitudeAbs_sq_le, lintegral_count, lintegral_count,
    tsum_schurIntegral_le hk h, ← tsum_image _ (by simp),
    (tsum_schurIntegral_le (.inv hk) h.inv).trans' (tsum_mono_subtype _ (by simp [doubleCoset,
    mul_assoc, -Set.mul_singleton, -Set.singleton_mul])), show S.termPosition _ _ γ⁻¹ =
    (S.termPosition c c' γ)⁻¹ by simp [termPosition, mul_assoc], show S.minorNorm j γ⁻¹ =
    S.minorNorm j γ by simp [abs_norm_eq_prod_norm_sq, leadingMinor, ← conjTranspose_submatrix],
    ← ofReal_mul, ← ofReal_pow, mul_pow, mul_pow, sq_sqrt, ← sq_sqrt this.le, sqrt_sq, pow_mul
    _ 4 2, pow_mul _ 4 8, tailScale_pow_four, IsAdmissible.card_besselCoord_le] <;> try positivity
  congr! 1; push_cast [besselEnergy, columnDim, div_pow, inv_pow]; field)
