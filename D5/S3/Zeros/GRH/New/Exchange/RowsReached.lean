/- GID: D5/S3/Zeros/GRH/New/Exchange/RowsReached
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/RowsReached
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.RowsReached. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/RowsReached.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Exchange.SteepParameters
import D5.S3.Zeros.GRH.New.Exchange.TriangleArrows
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Every row pairs with a restriction of explicit level. Every nonzero form of level g on the
indefinite U(Y_0) pairs nontrivially with the restriction of a real translate of a form on a unitary
group of rank one more, descended from a definite group at a principal level of explicit depth, so
the construction of crude rows reaches all rows. Nonvanishing periods via Poincaré series of deep
level and restriction results of Burger–Sarnak type are known. Related work: Prasad–Schulze-Pillot,
Generalised form of a conjecture of Jacquet, 2008; Harris, Testing rationality of coherent
cohomology of Shimura varieties, 2014; Muić, Fourier coefficients of automorphic forms and
integrable discrete series, 2015.

This file: Descent chain is the transpose of the lift chain, hence onto. Form orthogonal to
restrictions of explicit deep level from rank one more vanishes. -/

open ComplexConjugate Finset Matrix MeasureTheory Space Submodule U

/-- For i ≤ m, let U be the lift of y from node (0, 0) to (0, i), each step weighted by
`Data.triangleOrder`, and ι_b = `Data.iotaPlus`. Then ∫ι_iφ·U = ∫ι₀φ·y for all φ; if i ≠ 0, U and
all ι_{i−1}φ have principal level `Data.triangleModulus`. -/
lemma Data.iotaPlus_adjoint_weightedChain {P} (D : Data P) z ϑ {i} (h : i ≤ D.m) y
    : let U := weightedChain (triangleOrder z) (D.triLift z) ϑ 0 i y; let ι := iotaPlus ϑ z
    (i ≠ 0 → (∀ φ u, (triangleModulus z ϑ).reductionK₀ u = 1 → formRep _ _ u.1 (ι (i - 1) φ) = ι _
      φ) ∧ ∀ u, (triangleModulus z ϑ).reductionK₀ u = 1 → formRep _ _ u.1 U = U) ∧ ∀ φ, ∫ g, ι i φ
      g * U g ∂(D.gridSpace ..).quotMeasure = ∫ g, ι 0 φ g * y g ∂(D.gridSpace ..).quotMeasure := by
   induction' i with i ih; tauto; have e := isEdgeFamily_grid id false (z := z) rfl bot_le
   simp only [(iotaPlus.eq_1 ..).trans (ite_eq_left h), i.succ_sub_one, ← ih (by omega)]
   refine ⟨fun _ ↦ ⟨fun _ u k ↦ ?_, fun u k ↦ ?_⟩, fun _ ↦ by erw [LinearMap.smul_apply, ← map_smul,
     e.isArrow_modDatum.1.integral_mul_formLift_swap e.isArrow_modDatum.2]; congr! 2; apply
     mul_right_comm⟩ <;> erw [LinearMap.map_smul]
     <;> [erw [e.isArrow_modDatum.2.formRep_formLift_of_eq_smul (pairWeil_modDatum_Kf _ _ _ _ _
     u 1 ..)]; erw [e.isArrow_modDatum.1.formRep_formLift_of_eq_smul (pairWeil_modDatum_Kf (k := 1)
     ..)]] <;> simp <;> erw [(gridChar_hasWeight ..).apply_det_eq_charOfTamePart _, k] <;> cases
     z <;> simp <;> first | rfl | use ((auxPair ..).tame_eq_one · <| places_levelModulus.ge.mt ·)

/-- The untwisted descent `Data.iotaPlus` from Z_{m,0} to Z_{0,0} (nodes (0, m) and (0, 0) of the
grid Z, `Data.gridSpace`) is onto on forms of principal level
`Data.gridLevelGen`. -/
lemma Data.gridLevelForms_eq_map_iotaPlus {P} (D : Data P) : D.gridLevelForms 0 = (D.gridLevelForms
  _).map (D.iotaPlus 1 _ 0) := have : Module.Finite ℂ (D.gridLevelForms D.m) := (finite_levelSpace
    (isConjKernelPair_gridKernel (by simp) _).1 ⟨_, isOpen_principalLevel Fact.out⟩)
  (sup_orthogonal_inf_of_hasOrthogonalProjection
    (K₁ := (D.gridLevelForms _).map (D.iotaPlus 1 _ 0)) (K₂ := D.gridLevelForms 0)
    (map_le_iff_le_comap.2 fun _ _ ⟨k, h⟩ ↦
    (((D.iotaPlus_adjoint_weightedChain _ 1 D.nat_le_of_hasLogBound 0).1 one_ne_zero).1 _ ⟨k,
    h.1⟩ ((Modulus.mem_principalLevel_iff gridModulus_one_ideal _).1 h)).trans
    (by simp))).symm.trans (sup_of_le_left (bot_le.trans' fun z ⟨hz, hy⟩ ↦ by
    let y : triBase .. := ⟨conjForm (isConjKernelPair_gridKernel (by simp) true).2 z,
      mem_levelSpace_formRep_iff.2 (by simp [mem_levelSpace_formRep_iff.1 hy · ·])⟩; have ⟨L, H⟩ :=
      D.iotaPlus_adjoint_weightedChain true 1 le_rfl y; rw [iotaPlus] at H; simp at H
    exact Subtype.ext (star_eq_zero.1
      congr($((exists_isTriangle ..).choose_spec.eq_zero_of_weightedChain _ 0 (by omega) y
      (inner_self_eq_zero.1 ((H (conjForm (isConjKernelPair_gridKernel (by simp) false).2 _)).trans
      (congr(integral _ $(mul_comm ..)).trans (inner_eq_zero_symm.1 (hz _ ⟨_,
      mem_levelSpace_formRep_iff.2 fun k h g ↦ congrArg (star <| · g) ((L NeZero.out).2 ⟨k,
      h.1⟩ ((Modulus.mem_principalLevel_iff gridModulus_one_ideal _).1 h)), rfl⟩)))))).1))))

open Norms.L2Operator

attribute [-simp] MulMemClass.coe_mul Subgroup.coe_mul

attribute [local simp] prod_eq_zero_iff prod_pos dsKernel abs_of_pos typeKernel mul_assoc ne_of_gt

/-- Under gap, size and matrix coefficient bounds there is a real g such that a form y of type l,
principal level `Data.chosenLevel`, on V vanishes if orthogonal to x ↦ φ((x⊕1)g) for all φ of type
l′, level K(`Data.gridLevelGen`), on V ⊕ ⟨1⟩. -/
lemma eq_zero_of_petersson_restrict_eq_zero {P : Parameters} {D : Data P} (n : Type) [Fintype n]
  [Nonempty n] {s : n → ℤˣ} {V : Space D.E n s} (A : ℕ) {L N : ℕ} (β : ℝ) {m : ℝ} {t :
  n ⊕ Unit → ℤˣ} {l : _ → HCParam s} {l' : _ → HCParam t} {e : s ⊕ᵥ 1 = t} (hg : ∀ w,
  (l w).HasLargeGap (4 * A)) (hg' : ∀ w, (l' w).HasLargeGap (2 * A)) (hl : ∀ w i, |l w i| ≤ L)
  (hA : 8 * (Fintype.card n + 1) ^ 2 < A) (hN : N < A) (hA' : 2 * D.f * (Fintype.card n + 1) + 2 ≤
  A) (hc : D.gProd * cuspConst D.E n D.cycloConductor ^ 2 ≤ β) (hβ : 2000 *
  (Fintype.card n + L + 1) ^ 6 ≤ β) (fβ : D.f ≤ β) (hm : β ^ (20 * A * (D.f + 1)) ≤ m) (hR : ∀ w,
  m ^ (3 * Fintype.card n + 2) ≤ ‖Φ w D.gridLevelGen.val‖) (H : ∀ w, ∃ ω : USign _, ‖ω.1.1‖ ^ 2 ≤ β
  ∧ volume.real {r : USign s | ‖r.1.1 - 1‖ ≤ 1} ≤ β ^ N * ‖∫ r : USign s, (l w).dsCoeff r * conj
  ((toHCParam (s ⊕ᵥ 1) (l' w)).dsCoeff (ω⁻¹ * inl s 1 r * ω).1.1)‖) : ∃ g, ∀ y ∈ levelSpace
  (V.formRep (typeKernel l s)) D.chosenLevel, (∀ φ ∈ levelSpace (((V.sum (signedSpace ..)).reindex
  (.refl _) e).formRep (typeKernel l' t)) (principalLevel _ D.gridLevelGen), V.petersson y
  (fun x ↦ φ (G.reindex (.refl _) e (.sum (x, 1)) * (g, 1))) = 0) → y.1 = 0 := by
  choose ω c H using H
  obtain ⟨rfl, b : 16 ≤ β, ke⟩ := e, hβ.trans' (mod_cast by lia), isCuspKernel_typeKernel hg
  obtain ⟨bm : β ≤ m, r : 2 ≤ β⟩ := by grw [← hm]; bound, by bound
  set v := Measure.real ..
  choose p I J using fun w ↦ And.intro (norm_dsCoeff_le_pow (hg w) (by bound))
    (integral_tail_le (hl w) (2 * A) (by lia))
  obtain ⟨_, _ : 0 < v, I : Integrable _ volume, J⟩ := b.trans bm, ENNReal.toReal_pos
    (measure_sublevel_ne_zero _) (measure_ball_ne_top_of_isProperMap _ .monoidHom_id _),
    .fintype_prod I, ((integral_fintype_prod_volume_eq_prod _).trans_le
    (prod_le_prod₀ (by delta formalDegree; positivity [·, ·]) fun w _ ↦ J w)).trans (c :=
    m / (16 * β) / (β ^ N * (2 * β) ^ (3 * A)) ^ D.f) (by
    grw [← hm, hβ, b, (by bound : 8 ≤ β), r]
    simp [field, ← pow_mul, ← pow_add, ← pow_succ', ← sq]; gcongr <;> nlinarith)
  refine ⟨ω, fun ⟨y, hy⟩ hK h0 ↦ have k a (h : _ ∣ a) :=
      (mem_levelSpace_formRep_iff.1 hK · <| D.principalLevel_le_chosenLevel h ·)
    funext (norm_le_zero_iff.1 <| le_of_halving hy.2.choose_spec le_rfl (fun S _ hS x ↦ .inl
    ((le_or_gt ..).elim (fun z ↦ ?_)
      (IsForm.norm_le_of_firstMinimum_lt hy ke P.cycloConductor_mem_different NeZero.out (k _ ⟨_,
    D.piGBar_mul_star.symm⟩) (δ := m⁻¹ ^ 2) (by bound) (by bound) · fun u h ↦ ?_))) ·)⟩
  · have F α := (norm_poincare_period_sub_le hy.1 hS Fact.out (k _ D.piGBar_dvd_gridLevelGen) hR hA'
      hA hg' (by bound) x (by
      grw [← z, hc, bm] <;> simp [field, div_pow, NeZero.pos, (one_le_cuspConst ..).trans_lt']
      ring_nf; rfl) (fβ.trans bm) (by bound) ω α).imp_right (·.trans_eq' (congrArg (‖· - _‖)
      ((exists_kernel_form _ (isCuspKernel_typeKernel hg') (G.sum (x, 1) * (α, 1))⁻¹ _).elim fun Q
      hQ ↦ by simpa [↓conj_petersson, hQ, petersson, tsum_mul_left, ↓tsum_mul_right] using!
      congrArg conj (h0 _ Q.2))))
    have T := (congrArg _ (integral_mul_realConv hy.isBoundedMeasurable (F ω).1 ke.1.2
      (x * ⟨·, 1⟩))).ge.trans (norm_integral_le_of_norm_le
      (I.mul_const (((2 * β) ^ (3 * A) * v) ^ D.f * S * 10 / m)) (.of_forall fun u ↦ ?_))
    · simp_rw [hy.realConv_translate ke, ← mul_assoc, integral_mul_const, norm_mul] at T
      nth_grw 1 [J, (congrArg _ (funext ?_)).trans (integral_fintype_prod_volume_eq_prod _)] at T
      grw [norm_prod, ← (div_le_iff₀' (by bound)).2 (H _)] at T
      simp [field, mul_pow] at T; nlinarith
      simp [field]
    obtain ⟨F, _⟩ := (F (inl .. ∘ u * ω)).2, (le_prod_opNorm u).1
    rw [realConv, ← integral_mul_left_eq_self _ u] at F
    simp [measureReal_pos_of_isLevel, realConv, Subgroup.coe_mul] at F ⊢
    grw [F, p, b, norm_mul_le]; simp [← sq]; grw [c]
    simp [field, div_pow, prod_pow, one_le_norm]; linear_combination
  have j g := hy.isBoundedMeasurable.integrable_mul_comp ke.1.2 (g * ⟨·, 1⟩)
  grw [← hy.3 ke.1.2, realConv, realConv, ← integral_mul_left_eq_self _ u⁻¹, ← integral_sub
    ((j _).comp_mul_left _) (j _), norm_integral_le_of_norm_le (((I.comp_mul_left u⁻¹).add
    I).mul_const (β / m * S)) (.of_forall fun r ↦ ?_), integral_mul_const, integral_add'
    (I.comp_mul_left _) I, (integral_mul_left_eq_self ..).trans_le J, J, div_le_self]
  field_simp; linarith; any_goals bound
  simp [← mul_sub, ← sub_mul, ← mul_add]
  grw [hS, ← mul_assoc]; gcongr
  nth_grw 1 [← sq_le_sq₀, sq, (?_ : ‖_‖ ≤ β * (β * m⁻¹ ^ 2)), norm_sub_le]
  simp; grw [p, p, ← sub_nonneg]; simp_rw [prod_pow]; ring_nf
  any_goals positivity
  apply ((ContinuousMultilinearMap.mkPiAlgebra ℂ _ ℂ).norm_image_sub_le ..).trans
  gcongr
  grw [fβ, pow_le_one₀] <;> simp [pi_norm_le_iff_of_nonempty, norm_dsCoeff_le_one]
  simp_rw [pi_norm_le_iff_of_nonempty, Pi.sub_apply, ← dsCoeff_inv, _root_.mul_inv_rev, inv_inv]
  intro
  grw [norm_dsCoeff_sub_le (hl _), ← dist_eq_norm, ← hβ, ← h, ← dist_le_pi_dist u 1 ‹_›]; bound

/-- There is a real point g of U(Z_{0,0}) such that a form y of level g₀g₁ on Y₀ vanishes if it is
orthogonal to x ↦ φ((x ⊕ 1)g) for all forms φ of principal level `Data.gridLevelGen` on
Z_{0,0} = Y₀ ⊕ ⟨1⟩.

Every row pairs with a restriction of explicit level. -/
lemma Data.eq_zero_of_orthogonal_gridLevelForms {P} (D : Data P) : ∃ g,
  ∀ y ∈ D.principalForms (D.spaceY 0), (∀ φ ∈ D.gridLevelForms 0, (spaceY ..).petersson y (fun x ↦
  φ (G.reindex (.refl _) D.gridSigns_zero.symm (.sum (x, 1)) * (g, 1))) = 0) → y.1 = 0 := by
  choose e S using D.exists_isSteep
  obtain ⟨o, a⟩ := pow_right_mono₀ (D.le_of_hasLogBound : 1 ≤ √D.gProd),
    (D.abs_gridParam_le (z := ·) · bot_le bot_le)
  have := D.hasLogLower_of_le (o (D.nat_le_of_hasLogBound : 3 ≤ ⌈D.x⌉₊))
  refine' eq_zero_of_petersson_restrict_eq_zero (D.Y 0) (D.r ^ 4) (√D.gProd ^ ⌈D.x⌉₊)
    (D.hasGap_signsY_paramW · |>.mono _) (D.hasGap_gridParam · .. |>.neg.mono _) (a false) _ _ _ _ _
    _ le_rfl (have := congr(√‖Φ · $D.piGBar_mul_star‖); _) fun w ↦ .imp (fun ω ⟨c, T, A⟩ ↦
    have b := le_trans (by grw [c]) _; ⟨b, (T.laplace_method (h := D.r ^ 7) _ ((hasGap_gridParam
      ..).mono _) ((D.gridSigns_zero ▸ hasGap_gridParam ..).neg.mono _) D.le_of_hasLogBound
    (a false w) ((abs_neg _).trans_le <| a true w ·) _ _ _ .monoidHom_id _ fun s o ↦ by
      grw [eq_add_of_sub_eq (A s), norm_add_le, norm_mul₃_le, ← b, U.norm_inv, norm_fromBlocks, o]
      simp [sq]).trans_eq congr(_ * ‖$(?_)‖)⟩) ((S _ w).exists_isTwoFactor_restriction (by grind)
    (D.gridSigns_zero ▸ S ..) (D.gridSigns_zero ▸ hasGap_gridParam ..) D.le_of_hasLogBound)
  any_goals simp [HCParam.laplaceIntegrand, gapThreshold, cuspConst, ↓card_rowIndex]
  any_goals first | exact D.le_of_hasLogBound | rfl | fun_prop | use D.nat_lt_of_hasLogBound | grw
    [(D.le_of_hasLogBound : _ + 1 ≤ √D.gProd),
    (D.le_of_hasLogBound : 6 * _ ≤ √D.gProd), ← pow_add, ← pow_mul] | simp_all [← pow_mul]
  repeat use o D.nat_le_of_hasLogBound
