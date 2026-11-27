/- GID: D5/S3/Zeros/GRH/New/RealPlace/BesselCut
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/RealPlace/BesselCut
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.RealPlace.BesselCut. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/RealPlace/BesselCut.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.DiscreteSeries.BesselExistence
import D5.S3.Zeros.GRH.New.RealPlace.OpenCellBound
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Normalise a real-place Bessel function and cut it off. A Bessel function at a real place, an
average of a discrete series coefficient that is large at one point, inherits the coefficient's
decay, and normalising it and multiplying by a scalar cut-off gives a continuous approximant, close
in L² and compactly supported modulo the unipotent group, with an explicit tail bound. Averages of
integrable discrete series coefficients over a unipotent group and their decay are known, and the
normalisation and scalar cut-off with a tail bound are standard. Related work: Muić, Fourier
coefficients of automorphic forms and integrable discrete series, 2015; Miličić, Asymptotic behavior
of matrix coefficients of the discrete series, 1977; Wallach, Real Reductive Groups II, 1992.

Part of: Real-place Bessel integrals: band limits, energy and open-cell bound (see
New.Filling.FillingData). -/
seal Finset.univ Finset.sum Finset.prod

open ENNReal Fintype Matrix MeasureTheory Set Norms.L2Operator

attribute [local simp] CStarRing.norm_mem_unitary_mul CStarRing.norm_mul_mem_unitary

variable {𝔰} {I : Type} {ε} [Fintype I] [p : Frame 𝔰 ε] {rep} {A : ℕ} {l : HCParam ε} {L : ℕ}

/-- Let F be Bessel, integrable on 𝖴\G₁, with F(y) = ∫ deg·ψ_λ(g⁻¹)F(yg) dg (unitary frame p, l
= 2λ with `HCParam.HasLargeGap`, |l_a| ≤ L, rank N). Then F has continuous iterated right
derivatives satisfying `HasSchurBound` with constant deg⁻¹‖F‖₂², for every B ≥
(N+1)⁴(L+N+1+2(ϱ+1)²). -/
lemma IsBesselFunction.hasSchurBound_of_convolve_eq (hg : l.HasLargeGap A) (hL : ∀ a, |l a| ≤ L) {F}
  (hW : IsBesselFunction (I := I) rep F) (h2 : Integrable F besselQuotMeasure) (B : ℝ) : let e :=
    (l.formalDegree * l.psiInFrame ·); convolve F e = F → (𝔰.r + 1) ^ 4 * (L +
    𝔰.r + 1 + (2 * 𝔰.n ^ 2 : ℕ)) ≤ B →
    HasSchurBound F rep B (.ofReal l.formalDegree⁻¹ * ∫⁻ y, ‖F y‖ₑ ^ 2 ∂besselQuotMeasure) := by
  intro e fx H; obtain ⟨⟨β, hβ⟩, ⟨o, u, -⟩, k⟩ := exists_smear_dsCoeffSmooth_eq hg l.dsGenerator,
    hg.isUnitaryCasimirGe_dsAction, isIdempotentKernel_psiInFrame hg
  let π := frameEquiv (ε := ε); let γ w := (bumpDeriv.adTwist p.p⁻¹).word w β
  let S := smear l.dsCoeffSmooth.1; let X w g := l.formalDegree * S (γ w) (π g)
  have c := (fx ▸ hW.continuous_convolve k.2).comp π.3
  have hb : IsBoundedMeasurable e :=
    .of ⟨_, fun _ ↦ by grw [norm_mul, HCParam.psiInFrame, norm_dsCoeff_le_one hg]⟩ k.1
  have t w : Integrable (X w) ∧ convolve e (X w) = X w ∧ convolve F (X w) = smear _ c (γ w) ∘ π :=
    have z := measurePreserving_frameEquiv.integrable_comp_of_integrable (γ w).2.integrable; by
    rw [← show convolve e (_ ∘ π) = X w by
      ext; simp [X, S, e, π, convolve, ↓← integral_comp_frameEquiv, ← map_mul,
        mul_left_comm _ (l.formalDegree : ℂ)]; tauto, ← hb.convolve_assoc k.2 z, show convolve e e =
      e by ext; simpa [k.4] using! k.integral_inv_mul_translate _ 1, ← hW.convolve_assoc k.2 z, fx]
    use integrable_convolve k.2 z, rfl, by ext; simp [π, convolve, ← integral_comp_frameEquiv]
  use fun w ↦ ⟨_, hW.continuous_convolve (t w).1⟩, by simp [X]; erw [hβ, fx], fun w ↦ ?_
  let ⟨j, ex, a⟩ := t w; dsimp
  obtain ⟨x, -, b, s⟩ : ∃ x ∈ l.dsAction.filtration ε l.dsGenerator w.length,
      ‖x‖ ≤ ((𝔰.r + 1) ^ 4 * (L + 𝔰.r + 1 + w.length)) ^ w.length ∧ S (γ w) = x.1
  · refine w.rec ⟨_, GlModule.self_mem_filtration, u.le, hβ⟩ fun q w ⟨x, m, b, s⟩ ↦ ⟨_,
      ((isKHighest_dsGenerator hg).norm_apply_le_of_mem_filtration o (abs_lowestKType_le hg hL) m
      _).imp_right (⟨·.trans ?_, rightDeriv_smear _ _ s _⟩)⟩
    simp [inv_eq_left_inv p.2.1, p.2, l2_opNorm_single, pow_succ' _ w.length]
    grw [b]; gcongr <;> simp
  use ?_, fun g Z r h ↦ a ▸ .congr_deriv (hasDerivAt_smear _ _ c ?_) (by
    erw [(bumpDeriv.adTwist p.p⁻¹).apply_eq_sum Z]; simp [t, -smear_apply]; rfl), fun hw φ i ↦ ?_
  constructor <;> simp +contextual [hW.convolve_right j, convolve, mul_assoc, hW.2, hW.3, smul_comm
    (X w _), integral_smul, ← ContinuousLinearMap.integral_comp_comm, hW.integrable_smul j.comp_inv]
  simpa [π, frameEquiv, U.conj, mul_assoc] using (h.const_mul _).mul_const _
  grw [pow_mul', ← H, ← hw, ← b, show _ ^ 2 = (∫ g, ‖X w g‖ ^ 2) / l.formalDegree by
    simpa [X, s, π, field, Complex.mul_conj', ← Complex.ofReal_pow, integral_complex_ofReal,
    mul_pow, ← integral_comp_frameEquiv] using! congr($(hg.toL2_spec.2.2 x x 1).re),
    ← hW.lintegral_sq_convolve_convolve_le rfl ?_ hW.2 h2 j k ?_ fx hb ex i] <;> simp [convolve,
    HCParam.psiInFrame]

/-- Given a peaked Bessel function (`HasPeakAt`) at x with `besselSize` x ≤ b^{5(ϱ+1)}, and
numerical bounds
on b, n, l, there are F, reproduced by convolution with deg·ψ_l, and V such that (F, V) satisfies
`IsCutPair`.

Normalise a real-place Bessel function and cut it off. -/
lemma HasPeakAt.exists_cut_isCutPair (hg : l.HasLargeGap A) {L : ℕ} (hL : ∀ a, |l a| ≤
  L) f [NeZero f] {n Y b x}
  (H : HasPeakAt (I := I) l rep Y x (b ^ n)) (hR : besselSize x ≤ b ^ (5 * 𝔰.n)) (b2 : 2000 ≤ b)
  (hM : n + 99 * 𝔰.r ^ 2 ≤ 𝔰.r ^ 3) (hb : 𝔰.r + L + 1 ≤ b ^ 4) (hf : 3 * 𝔰.r ^ 3 * f ≤ A) : ∃ F V :
  C(_, _), convolve F (l.formalDegree * l.psiInFrame ·) = F ∧ IsCutPair b f rep (·.rec F V) := by
  let M := 8 * 𝔰.r ^ 2 + 1; let B := {g : 𝔰.G₁ | ‖g.1.1 - 1‖ ≤ 1}
  obtain ⟨⟨_, b3, b8, b9, _⟩ : 1 ≤ b ∧ 2 ≤ b ∧ 8 ≤ b ∧ 16 ≤ b ∧ 0 < 𝔰.r ^ 2, _, ⟨hY, fx, h0, hS, z⟩,
    d, i, j⟩ := by bound, H.stronglyMeasurable, H, formalDegree_pos hg,
    integral_tail_le hL (M * 2) (by lia)
  have a (g : 𝔰.G₁) : ‖(frameEquiv g).1.1‖ = ‖g.1.1‖ := by simp [frameEquiv, U.conj,
    inv_eq_left_inv p.2.1, p.2]
  have k {n} (o : n ≤ A) g : ‖l.psiInFrame g‖ ≤ _ := a g ▸ norm_dsCoeff_le_pow (c :=
    M * 2 + n) hg (by delta gapThreshold; norm_cast; lia) _; let C : ℝ≥0∞ := .ofReal (16 ^ M)
  let ω c (g : 𝔰.G₁) : ℝ≥0∞ := .ofReal ((2 / ‖g.1.1‖) ^ c); let R := b ^ (6 * 𝔰.n + 2)
  let φ := ω (M * 2); let Φ y := ∫⁻ s, φ (x⁻¹ * (s.1.1 * y)) ∂𝔰.besselGraphMeasure
  have j : .ofReal l.formalDegree * (∫⁻ g, φ g) * (C * C) ≤ .ofReal b ^ (99 * 𝔰.r ^ 2) := (by
    simp_rw [φ, ω, C, ← a]; grw [lintegral_const_mul_le, (ofReal_mul d.le).ge,
    (measurePreserving_frameEquiv.lintegral_comp (by fun_prop)).trans
      (ofReal_integral_eq_lintegral_ofReal i (.of_forall
    fun _ ↦ by positivity)).symm, j, hb, b2, b8, b3, b9]
    simp (disch := positivity) only [← pow_mul, ← pow_add, ← pow_succ', ← ofReal_mul, ← ofReal_pow]
    gcongr; lia); have := fx ▸ hY.continuous_convolve (isIdempotentKernel_psiInFrame hg).2
  have r {y} (s : 𝔰.besselGraph) (h : ‖(x⁻¹ * (s.1.1 * y)).1.1‖ ≤ b * 2) : besselSize y + 1 ≤
    R := by
    grw [← besselSize_besselS_mul (besselGraph_fst_mem_besselS s), besselSize_le_norm_mul x, hR, h,
      add_one_le_two_mul, b3, b3]
    ring_nf!; repeat bound
  have hB {g} (h : g ∈ B) : ‖g.1.1‖ ≤ 16 := by grw [norm_le_insert' _ 1, h.out]; bound
  have w := @ENNReal.div_mul_cancel (volume B) C (measure_sublevel_ne_zero _)
    (measure_ball_ne_top_of_isProperMap _ .monoidHom_id 1)
  let μ := (C / volume B * (.ofReal (b ^ n) * ‖Y x‖ₑ)) • volume.withDensity (ω M)
  have m := show μ univ ≤ _ by simp [μ]; grw [show lintegral _ (ω M) ≤
    C * volume B from (lintegral_decay_le _ .monoidHom_id .refl
    1).trans_eq' (by simp [ω, M]), mul_right_comm, mul_left_comm _ C, w]
  have S y O (o : {g | besselSize (y * g) ≤ R} ⊆ O) : Φ y ≤ μ O := by
    grw [Measure.smul_apply, ← z, smul_eq_mul, mul_right_comm, ← lintegral_const_mul _ (by
      fun_prop)]; simp_rw [Φ, φ, ω, a]; gcongr with s; set t := x⁻¹ * _
    grw [← withDensity_apply_le, ← lintegral_mono_set (s := (t * ·) ⁻¹' B) fun g h ↦ o ((r s (by
      grw [← mul_assoc _ y, ← mul_assoc, hB h.out]; bound)).trans' (by simp)),
      ← setLIntegral_mono (by fun_prop) fun g h ↦ ?_, setLIntegral_const, measure_preimage_mul,
      mul_left_comm, w, ← ofReal_mul, ← mul_pow, div_mul_cancel₀, pow_mul, sq, ofReal_mul] <;>
      (try positivity); grw [div_div, ← hB h.out, ← U.norm_inv t, ← norm_mul_le] <;> simp
  have h5 := show ‖Y x‖ₑ ^ 2 ≤ _ by
    grw [← fx, convolve, enorm_integral_le_lintegral_enorm, sq_lintegral_le ?_ ?_ fun t ↦
      (?_ : _ ≤ φ t * .ofReal l.formalDegree ^ 2 * (‖Y (x * t)‖ₑ ^ 2 * φ t)),
      lintegral_unfold_besselGraphMeasure (_ * φ ·), congr(‖Y $(mul_inv_cancel_left ..)‖ₑ).le,
      (hY.enorm_besselS_mul (besselGraph_fst_mem_besselS _) _).le, (lintegral_const_mul _ ?_
    ).trans_le (mul_le_mul' le_rfl (S _ univ le_top)), m, lintegral_mul_const, lintegral_mul_const]
    <;> (try fun_prop); grw [enorm_smul, ← ofReal_norm, norm_mul, k zero_le, U.norm_inv]
    simp [abs_of_nonneg, φ, ω, d.le]; ring_nf; rfl
  have iY : Integrable Y besselQuotMeasure := ⟨by fun_prop, (lintegral_mono hS).trans_lt
    (lintegral_unfold_besselGraphMeasure (‖l.psiInFrame ·‖ₑ) (by fun_prop) ▸
    ((integrable_const_mul_iff (by simp [d.ne']) _).1 (isIdempotentKernel_psiInFrame hg).2).2)⟩
  obtain ⟨q, hq⟩ : ∃ q, _ = ofNNReal q := ⟨_, lintegral_enorm_sq iY hY.memLp_top⟩
  simp [↓hq, sq, ← mul_assoc, ENNReal.mul_le_mul_iff_left, h0] at h5
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ‖c‖ₑ ^ 2 * q = card I := ⟨(card I / q).sqrt, by
    rw [NNReal.enorm_eq]; norm_cast; simp [show q ≠ 0 from (by simp [·, h0] at h5)]⟩
  let χ t := 0 ⊔ 1 ⊓ (R - t); let F : C(_, _) := .mk (c • Y ·)
  let V : C(_, _) := .mk fun y ↦ χ (besselSize y) • F y
  have v {y} : ‖V y‖ₑ ≤ ‖F y‖ₑ ∧ ‖(χ (besselSize y) - 1) • F y‖ₑ ≤ ‖F y‖ₑ := by
    simp [V, χ, norm_smul, enorm_le_iff_norm_le, mul_le_of_le_one_left, abs_le]
  refine have nF := by simp [F, enorm_smul, mul_pow, lintegral_const_mul', *]
    have G y := by
      dsimp [F, Φ, φ, ω]; grw [enorm_smul, mul_left_comm, hS, lintegral_const_mul_le]; gcongr with s
      grw [← ofReal_norm]; split; grw [k zero_le]; simp; grw [← ofReal_mul (by bound), k hf,
      pow_add, mul_left_comm, ← mul_pow, ← mul_div_assoc, div_le_one_of_le₀ (le_of_not_ge
      (mt (r s) (‹¬_› <| by simp [inf_of_le_left, F, V, χ, le_sub_iff_add_le', ·])))] <;> simp
    have Z := by dsimp; grw [m, lintegral_const_mul, ← lintegral_unfold_besselGraphMeasure, h5,
      ← hc, ← hM, ofReal_pow,
      ofReal_pow, pow_mul', pow_add, ← j] <;> first | positivity | fun_prop | ring_nf; rfl
    ⟨F, V, by simpa [F, funext_iff, convolve, smul_comm _ c, integral_smul]
      using congr(c • $fx), ?_, iY.smul c, nF, by grw [v.1, nF], by simp +contextual [V, χ, R,
      le_of_lt], ?_, (‖c‖ₑ * Φ ·), ‖c‖ₑ • μ, by fun_prop, fun s h y ↦ congr(_ * $(.trans
      (by simp [mul_assoc]) (lintegral_mul_right_eq_self _ (𝔰.besselGraphChart (⟨s, h⟩, 1))))),
    (·.rec G (by grw [v.1, G ·])), (by simp; grw [← S · _ .rfl]), ⟨by simp; grw [m]; finiteness⟩, Z⟩
  rintro ⟨⟩ <;> use ⟨by fun_prop, hY.bounded.imp' _ fun _ k y ↦ .trans (b := ‖F y‖)
    (by simp [← enorm_le_iff_norm_le, v]) (by erw [norm_smul]; grw [k])⟩ <;> simp +contextual [F,
    V, besselSize_besselS_mul ∘ mem_unitriGroup_of_mem_besselU, besselSize_besselS_mul
    (mem_unitriGroup_of_mem_floorGroup (toBesselH_mem _)), hY.2, hY.3, smul_comm (wave _)]
  grw [← ENNReal.mul_le_mul_iff_right (a := .ofReal (b ^ (3 * 𝔰.r ^ 3 * f)) ^ 2), ← mul_assoc,
    ← mul_pow, ← ofReal_mul, ← @ofReal_pow (_ * _), ← Z.trans (mul_le_mul' ?_ le_rfl),
    lintegral_const_mul_le, ← lintegral_const_mul _ (by fun_prop), lintegral_mono fun y ↦ ?_] <;>
    try finiteness
  dsimp at *; grw [← S y univ le_top, ← sq, ← G]; split; simp [*]
  grw [← mul_pow, ← v.2, sub_smul, one_smul]; rfl
  gcongr; simp [field, ← pow_add, ← pow_mul, -card_sum]; gcongr; nlinarith [NeZero.pos f]
