/- GID: D5/S3/Zeros/GRH/New/Exchange/RealPair
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/RealPair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.RealPair. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/RealPair.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.MixedModel.RapidSections
import D5.S3.Zeros.GRH.New.Exchange.LowRankIdentity
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Exchange theorem for theta integrals of complementary rank (see
New.Exchange.ExchangeTheorem).

This file: Matched real data giving the exchange identity at the top of the tower. -/


open Matrix NumberField MeasureTheory Complex Space Filter ContDiff Norms.Elementwise Finset
  Function Splitting Measure MixedModel GeneralLinearGroup ENNReal IsHermInvolution U MatMul
variable {E n a b m} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype a] [Fintype b]
  [Fintype m] {s r} {X : Space E m r} {W₁ : Space E n s} (D : X.Splitting W₁ b) [IsBaseAdapted D]

/-- For an adapted splitting D, τ ≥ 0 smooth, compactly supported, not identically zero, and v
rapid (`IsRapidDatum`), there
are κ in ℂ and a rapid Λ with real slices τ(x_∞)κ·v at all x, whose slice at 0 for the
opposite splitting is v. -/
lemma exists_rapid_with_realSlice {t'} (V' : Space E a t') (τ : _ → ℝ) (c :
  ContDiff ℝ ∞ τ) {v} (hv : IsRapidDatum v) (k : HasCompactSupport τ) (h : 0 ≤ τ) y (o : τ y ≠ 0) :
  ∃ κ Λ, IsRapidDatum Λ ∧ realSlice D.symm V' 0 Λ = v ∧ ∀ x,
  (isAdapted_homSource D V').mixedModel.slice x Λ = (τ x • (κ : ℂ)) • realWeil 1 v := by
  peel 1 (ofReal_ne_zero.2 (c.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (μ := realMeasure _) k h o).ne').isUnit.dvd
  refine (exists_section _ (c.smul_const _) k.smul_right contDiff_const hv).imp fun _ ↦
    .imp_right fun l ↦ ⟨eq_of_integrated_zeroTerm_eq (isAdapted_homSource D.symm V') fun f ↦ ?_, l⟩
  erw [← zeroTerm_integrated, symm_homSource_zeroTerm_eq_integral,
    symm_homSource_zeroTerm_eq_integral, ← (integrated _ v).integral_comp_comm (by fun_prop),
    @isAddLeftInvariant_eq_smul _ _ _ _ _ _ _ _ volume _
    (.domSMul (μ := vacuumMeasure) (.mk (star (adaptedHomBasis b V'))))]
  simp [integral_domSMul, star, -coe_units_inv]; simp +singlePass only [mixedTerm_integrated,
    isAdapted_homSource]
  simp [(adelicSum E 1).integral_eq_integral_prod, adelicSum, realCoord.eq_unfold, l]
  repeat rw [(congrArg _ (funext (by simp; tauto))).trans (integral_prod_smul ..)]
  erw [integral_mul_const, integral_ofReal, ← this]

/-- Witt's theorem, smooth local form: for `J` Hermitian and a frame `x` with invertible Gram
matrix, elements `k y` of `U J`, smooth in `y`, carry the span of `x` to that of `y` near
`x`. -/
lemma exists_contDiff_witt {J : Matrix m m ℂ} (hJ : Jᴴ = J) {x : Matrix m b ℂ}
    (d : (xᴴ * J * x).det ≠ 0) : ∃ k : _ → U J, ContDiff ℝ ∞ (fun y ↦ (k y).1.1) ∧
      ∀ᶠ y in nhds x, ∃ c : Matrix b b ℂ, (k y).1.1 * x * c = y := by
  let w := (xᴴ * J * x)⁻¹ * xᴴ
  let L a := (a * x * w - x * w * aᴴ) * J
  let p y := 1 - (x - y) * w * J
  have ⟨_, i⟩ := (by fun_prop : ContDiff ℝ 1 L).differentiable_one 1
  open Norms.L2Operator in have hT := (HasFDerivAt.comp 1 (by simpa [L] using
    hasFDerivAt_exp_zero) i).fun_mul' ((hasFDerivAt_id 1).fun_sub i)
  have ⟨A, _, e⟩ := exists_contDiff_eventuallyEq (.to_localInverse (f' := 1) (by fun_prop)
    (hT.congr_fderiv (by simp [L]; apply sub_add_cancel)) (by simp))
  use (expU ⟨L <| A <| p ·, by simp [unitaryLie, L, w, *, conjTranspose_nonsing_inv]⟩), by fun_prop,
    .mono ((by fun_prop : Continuous p).tendsto' _ _ (by simp [L, p]) ((e.fun_comp _).trans
    (HasStrictFDerivAt.eventually_right_inverse _))) fun y e ↦ ⟨_, by
    simpa +zetaDelta [xᴴ.mul_assoc J x ▸ d] using congr($e * x)⟩

/-- For adapted splittings of X over W₁ (even rank) and of W₁ along a line, and rapid v, v₁,
some x, x' satisfy `StdExchange` for (X, V' ⊕ W₁, V') with factor `equalRankThetaRatio` of v₁,
and x' has slice v at 0 for the opposite splitting. -/
lemma exists_stdExchange_top {t t'} {W : Space E a t} (D₁ :
  W₁.Splitting W Unit) [IsBaseAdapted D₁] (V' : Space E b t') σ' (hn : 2 ∣ Fintype.card n) μ {v v₁ :
  PairFock ..} (hv : IsRapidDatum v) (r₁ : IsRapidDatum v₁) : ∃ x x', realSlice D.symm V' 0 x' = v ∧
  StdExchange X (V'.sum W₁) V' μ σ' x x' (equalRankThetaRatio W₁ · v₁) := by
  obtain ⟨⟨j, hj⟩, d⟩ := id hn, IsHermInvolution.det_ne_zero (signMatrix t')
  let M := Int.toNat ∘ μ
  let J := signMatrix (t' ⊕ᵥ s); let x₀ := @fromRows ℂ b n b 1 0
  have g₁ : x₀ᴴ * J * x₀ = signMatrix t' := by simp [x₀, J, ← signMatrix_sum]
  obtain ⟨⟨γ, _, eg⟩, k, _, N⟩ := exists_contDiff_eventuallyEq (f := (·⁻¹)) (x := signMatrix t')
    (by simp [Matrix.inv_def, funext₂ (adjugate_apply _), det_apply, updateRow_apply,
    prod_ite] at *; fun_prop), exists_contDiff_witt isHermitian (g₁ ▸ d)
  set S := (k · |>.1.1) with ← hk
  obtain ⟨σ, sσ, kσ, _, rσ, _⟩ := exists_contDiff_tsupport_subset (nhds_pi.le (eventually_pi fun _ :
    InfinitePlace E ↦ N.and ((by fun_prop : ContinuousAt (_ * _ * ·) _) (g₁ ▸ eg.and
    (ContinuousAt.eventually_ne (by fun_prop) d)))))
  let cuL {a} [Fintype a] : _ ≃L[ℝ] InfinitePlace E → Matrix a b ℂ :=
    (LinearEquiv.curry .. ≪≫ₗ .piCongrRight fun v ↦ .curry ..).toContinuousLinearEquiv
  let z (x : type_of% x₀) := x * (γ (xᴴ * J * x) * (xᴴ * J * x₀))
  let w (y x : InfinitePlace E → type_of% x₀) v := (k (y v))⁻¹.1.1 * x v
  have P x (h : σ (z ∘ x) ≠ 0) v : ∃ c, S ((z ∘ x) v) * x₀ * c = x v ∧ cᴴ * signMatrix t' * c =
    (x v)ᴴ * J * x v := have ⟨⟨_, e⟩, _⟩ := sσ (subset_closure h) v
    (Matrix.mul_assoc ..).symm.trans (congr($e * _).trans (mul_nonsing_inv_cancel_right _ _ (by
    simp_all [z, gram_mul (x v), -conjTranspose_mul]))) ▸ ⟨_, rfl, by rw [gram_mul _ J,
      U.gram_invariant, g₁]⟩
  have ⟨κ, Λ', r, e', l'⟩ := exists_rapid_with_realSlice D V' ((fun x ↦ σ (x₀ * x ·) * ‖∏ w,
    (x w).det ^ (j + M w)‖ ^ 2) ∘ cuL) (.mul (by fun_prop) (.norm_sq ℂ
    (by simp [det_apply]; fun_prop))) hv ((kσ.image_auto
    (cuL.symm ∘ (x₀ᴴ * · ·))).closure_of_subset fun x h ↦ ⟨_, subset_closure (left_ne_zero_of_mul
    h), by simp [x₀]⟩) (fun _ ↦ mul_nonneg (rσ ⟨_, rfl⟩).1 (sq_nonneg _)) (cuL.symm 1) (by simp [*])
  let τ y x := ((σ y * σ (w y x)) • ((∏ v, (w y x v).toRows₁ᴴ.det ^ (M v * 2)) * κ)) • realPairWeil
    (j - M ·) 0 (1, k ∘ y) (realBoxProd (realSigns_comp_split homSigns_sum_target) v v₁)
  have ⟨Φ, R, l⟩ : ∃ Φ, IsRapidDatum Φ ∧ ∀ x,
    (isAdapted_homSource D (V'.sum W₁)).mixedModel.slice (cuL.symm x) Φ = τ (z ∘ x) x := by
    simp [τ, realPairWeil, ← smul_assoc, -real_smul, zpow_sub₀, division_def, inv_eq_conj,
      reindex_equiv cuL]
    exact exists_section _ (by
      simp [w, ↓U.coe_inv IsHermInvolution.mul_self, congrFun hk, det_apply, -real_smul]
      fun_prop) (((kσ.prod kσ).image_auto (cuL.symm ∘ fun (p, q) v ↦
      S (p v) * q v)).closure_of_subset
      fun x h ↦ ⟨(z ∘ cuL x, _), closure_prod_eq.le (subset_closure (mul_ne_zero_iff.1
      (left_ne_zero_of_smul h))), by simp [S]⟩) (contDiff_pi' fun _ ↦ contDiff_pi' (by
      simp_intro _ [pairHomInf, blockDiagonal_apply, pairHom, congrFun hk]; split_ifs <;> fun_prop))
      fun N ↦ mul_ne_top (mul_ne_top (isRapidDatum_vacVector N) (r₁ N)) (hv N) ∘ eq_top_mono (by
      (repeat refine (weightedNorm_integral_le _).trans (lintegral_weightedNorm_smul_le fun _ ↦
        (weightedNorm_realHeisOp_le ..).trans ?_); rw
        [mul_comm]; gcongr) <;> simp [realCoordSum, enorm, pi_nnnorm_le_iff, nnnorm_le_pi_nnnorm])
  refine ⟨_, _, e', stdExchange_of_periods _ D D₁ _ _ hn (fun h ↦ (rσ ⟨z ∘ (h⁻¹ · |>.1.1 * x₀),
    rfl⟩).1) ((Continuous.tendsto (by fun_prop) 1).eventually_ne (by simp_all [comp_def, z,
    eg.eq_of_nhds])) R r (fun 𝔠 h ↦ ?_) (.inl fun x e w ↦ (P (atRealPlace x) (e <|
    (l (atRealPlace x)).trans <| by simp [τ, ·]) w).imp (by simp [↓← gram_map_real, J]))⟩
  lift μ to type_of% M using (𝔠.weight_pos · |>.le)
  generalize hy : z ∘ _ = y
  choose! c ec hc using hy ▸ P _
  choose! u hu using (exists_U_coe_eq <| hc · · |>.trans (g₁ ▸ U.gram_invariant ..))
  choose! q hq using fun o v ↦ (mem_range_sum (signMatrix_sum ..) (g := h v * k (y v) * U.sum
    (signMatrix_sum ..) (u v, 1)).2 isUnit).2 (by simpa [hu o, x₀, U.sum,
             ← fromCols_fromRows_eq_fromBlocks] using congr((h v).1.1 * $(ec o v)))
  use ((u, 1), q⁻¹, 1); intros
  let x v := (h⁻¹ v).1.1 * x₀ * (u⁻¹ v).1.1 * (‹GL b _›.map (delta% evalInf v)).1
  erw [l (atRealPlace _), l' (cuL.symm (atRealPlace _)), MonoidHom.prod_apply, show atRealPlace _ =
    x by ext; simp [x, x₀, ↓mul_apply, Prod.fst_sum, U.sum, blockGL], show τ _ x = τ y x by
    by_cases! i : ∀ y, σ (w y x) = 0; simp [τ, i]; congr 1
    simp_rw [← hy, comp_def, z,
      (by simpa only [w, U.gram_invariant] using sσ (subset_closure i.choose_spec) ·
      |>.2.1), x, gram_mul (_ * _), U.gram_invariant (J := J), g₁, eg.eq_of_nhds]
    simp [-val_map_apply]]
  by_cases o : σ y = 0; simp [τ, o]
  simp +zetaDelta [𝔠.hasWeight.baseChange_apply_inf, ideleAbs_eq_prod_of_v_eq_one, ← conj_mul',
    ← hu o, rep_apply_apply, ← norm_prod, thetaIntegral,
    ← map_mul, pow_mul, hj, pow_add, ← thetaLarge_eq_apply_one_of_even_rank D₁ 𝔠 hn r₁ ‹_›, congrFun
    ‹_ = _›, prod_pow, comp_def, -norm_pow, thetaOnRealData_boxProd_eq_mul, _root_.zpow_mul,
    div_pow, ↓← ec o, mul_pow, pow_right_comm _ 2, Pi.mul_def, mul_assoc, ← map_inv,
    ← mul_inv_eq_of_eq_mul (hq o _), ← Pi.one_def]
  field [prod_eq_zero_iff]
