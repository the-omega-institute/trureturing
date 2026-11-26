/- GID: D5/S3/Zeros/GRH/Lib/SiegelWeil/Formula/SiegelWeilFormula
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/SiegelWeil/Formula/SiegelWeilFormula
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.SiegelWeil.Formula.SiegelWeilFormula. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/SiegelWeil/Formula/SiegelWeilFormula.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.SiegelWeil.Formula.SiegelSets
import D5.S3.Zeros.GRH.Lib.Weil.MixedModel.EquivariantCoefficients
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Siegel–Weil formula in the convergent range. Here a split space of rank 2p is
paired with a hermitian space of rank above 2p, both unimodular at every finite place, over a CM
field with the 5040th roots of unity. The Eisenstein series is a sum over Lagrangians, and the proof
uses one Hecke operator at a split place against the positive Eisenstein series. Source: A. Weil,
Sur la formule de Siegel dans la théorie des groupes classiques, Acta Math. 113 (1965), n° 52 Thm 5;
method of proof after Andrianov (1979), Harris (1981), P. Garrett, The Siegel-Weil formula in the
convergent range (notes, 2005). -/

open Set Matrix MeasureTheory Filter Fintype Core Space Splitting Lagrangian Metric Subsingleton
  MatMul

/-- Siegel–Weil formula: for S split of rank 2p and rk T > 2p, the norms of the zero terms ev_L
are summable over the Lagrangians L of S, and for every f, h ↦ θ(ω(1,h)f) is integrable on
[U(T)] with mean ∑_L ev_L f.

Known result: Siegel–Weil formula in the convergent range. -/
lemma siegel_weil {E n m p} [Field E] [CMType E]
    [WeilData E] [Fintype n] [Fintype m] [Fintype p] {s t} {S : Space E n s} (T : Space E m t) (P :
  CompleteSplitting S p) (hm : 2 * card p < card m) : Summable (‖Lagrangian.zeroTerm (S :=
  S) T ·‖) ∧ ∀ f, Integrable (θ _ <| splitWeil S T ⟨1, ·⟩ f) T.quotMeasure ∧ ∫ h, θ _ (splitWeil S T
  (1, h) f) ∂T.quotMeasure = T.quotMeasure.real univ * tsum (Lagrangian.zeroTerm T · f) := by
  induction' h : card n using Nat.strongRec with _ IH generalizing n p
  obtain ⟨⟨N, mN, hN, B⟩, ⟨Ω, hΩ, H⟩, b, u, hB⟩ := theta_normalisedTorus_le T P hm,
    exists_siegel_set P, exists_summable_zeroTerm_bound T P hm
  have hs := u.of_nonneg_of_le (by simp) (normalisedTorus_zero T P ▸ hB 0)
  have i f : Integrable _ T.quotMeasure := ⟨by fun_prop, (lintegral_mono
    (normalisedTorus_zero T P ▸ B · 0 f)).trans_lt (lintegral_mul_const _ mN ▸ by finiteness)⟩
  have sm f : Summable (‖Lagrangian.zeroTerm T · f‖) := (hs.of_norm.mapL (.apply ℂ _ f)).norm
  refine let ℓ : _ →L[ℂ] ℂ := T.quotMeasure.real univ • _ - strongIntegral ..
    have hℓ f : ℓ f = _ - integral .. := congrArg₂ (_ * · - ·) (ContinuousLinearMap.map_tsum
      (.apply ℂ _ f) hs.of_norm) (strongIntegral_apply _ (θ _ ∘L splitWeil S T ⟨1, ·⟩) i f)
    ⟨hs, (⟨i ·, ?_⟩)⟩
  cases isEmpty_or_nonempty n
  simp [Lagrangian.zeroTerm, mixedValue, Splitting.zeroTerm_apply, pairWeil, eq_one (G.onHom _),
    eq_zero (_ + _), sum_subsingleton _ P.lagrangian]
  have key {C} (c : IsCompact C) ι : (atTop.comap (·.1 ι)).Tendsto (fun z : _ × C ↦ ℓ
    (normalisedTorus T P z.1 z.2.1)) (nhds 0) := by
    obtain ⟨⟨_, _, _, D₁, e⟩, ⟨R, hR⟩, Ω, hΩ, H⟩ := S.exists_splitting (.of_ne_zero (ne_of_apply_ne
      (_ ⬝ᵥ ·) (congr($P.gram_lk ι ι).trans_ne (by simp)))) congr(submatrix $P.gram_kk _ _),
      c.isBounded.exists_norm_le,
      IsCovolOneLattice.exists_compact_cover (_root_.ratVectors E (m × Unit))
    choose τ hσ using exists_lagrangian_equiv_containing T D₁
    let σ := τ.trans (.subtypeEquivRight fun _ ↦ by simp [range_mulVecLin, range_unique, e]; rfl)
    have D₂ := (σ.symm ⟨P.lagrangian, _, mulVec_single_one ..⟩).completeSplitting.1.2
    choose _ I J using IH _ (h ▸ by simp [D₁.card_eq]) D₂ (by bound [P.card_eq, D₂.card_eq,
      D₁.card_eq]) rfl
    conv in ℓ _ => erw [hℓ, ← (sm _).of_norm.tsum_subtype_add_tsum_subtype_compl,
      mul_add, add_sub_right_comm, ← σ.tsum_eq, funext (hσ · _), ← J, ← integral_sub (I _) (i _)]
    let w : C(𝔸 E × G E t, _) := ⟨_, (hΩ.prod c).continuous_sSup (f := fun a y ↦ ‖ϱ _ ((a.2⁻¹.mat
      * T.dualFrame.2).kronecker D₁.lCoordᵀ *ᵥ a.1 • y.1) y.2 - y.2‖ₑ) (by fun_prop [kronecker,
      kroneckerMap])⟩
    refine .trans' (by simp) (Tendsto.add (EMetric.tendsto_nhds.2 fun _ _ ↦
      (mem_nhds_zero_finAdele_iff.1 ((tendsto_lintegral_filter_of_dominated_convergence (F :=
      fun a h ↦ N h * w (.swap a, h)) _ (.of_forall (by fun_prop)) (.of_forall fun _ ↦
      .of_forall fun _ ↦ mul_right_mono (sSup_le (forall_mem_image.2 fun _ y ↦ by grw
      [← ofReal_norm, norm_sub_le, (heisRep _).3, hR _ y.2]))) (by
      rw [lintegral_mul_const] <;> finiteness) ((ae_lt_top mN hN).mono fun _ _ ↦ Continuous.tendsto
      (by fun_prop (disch := order)) 0)).eventually_lt_const (by simpa [w, sSup_image])).curry_nhds
      ).elim fun M ⟨hM, k⟩ ↦ .mono (tendsto_comap ((summable_geometric_two.smul_const ↑M
      ).tendsto_atTop_zero (k 1 (by simp)))) fun (x, f) v ↦ (edist_zero_right _).trans_lt
      (v.trans_le' ((enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun h ↦ ?_))))
      (.const_mul _ (tendsto_tsum_of_dominated_convergence ((u.mul_right _).subtype _) (g := 0) (fun
      ⟨L, l⟩ ↦ ?_) (.of_forall fun z L ↦ hB _ L |> (_ ∘L _).le_of_opNorm_le_of_le <| hR _ z.2.2))))
    have : D₁.lCoord * (P.levi (dyadicDiag (x ·), 1)).mat = star (twoAtInfinity E ^ x ι)⁻¹.1 •
      D₁.lCoord := by ext1; simpa [dyadicDiag, ← map_inv, lCoord, kAdelic,
      e] using! congr($(P.lCoord_mul_mat (P.levi_mul_kAdelic (dyadicDiag (x ·)) 1)) ι _)
    rw [← (by simpa using D₁.sourceTerm_levi T _ 1 1 1 h 0 _ :
      _ = splitWeil _ T _ _), θ_apply, Splitting.zeroTerm_apply, ← edist_eq_enorm_sub]
    refine (convex_closedEBall ..).integral_mem isClosed_closedEBall (.of_forall fun q ↦ (((by
      simpa : (M : E) ≠ 0).isUnit.map toAdele).smul_bijective.2 q.out).elim fun b e ↦ (H b).elim
      fun c r ↦ .trans (.trans_eq' (B h x _) (.trans ?_ congr(edist $((isContPeriodic_along_k ..).2
      _ (nsmul_mem r.1 M) _) _))) (mul_right_mono (le_sSup ⟨(_, _), ⟨r.2, f.2⟩, congr(‖ϱ _ (_ *ᵥ
      $(show _ = star (twoAtInfinity E ^ x ι)⁻¹.1 • (M • c + q.out) by ext <;> simp [← e,
      twoAtInfinity, mul_add])) _ - _‖ₑ)⟩))) (isContPeriodic_along_k ..).integrable_out
    simp [-mulVec_add, normalisedTorus, varrho_pairWeil, -θ_apply, *, ← mul_sub, ← θ_ϱ, splitWeil,
      D₁.card_eq,
      ↓mulVec_smul, kronecker_mulVec_eq_matToVec, homSource_kAdelic, edist_eq_enorm_sub]; rfl
    obtain ⟨⟨_, D'⟩, rfl⟩ := L.completeSplitting
    choose Y hY hv using (reindex_equiv toLin').2.1.1
      (((D'.lᴴ * S.J).toLin'.domRestrict _).exists_extend_of_notMem l 0)
    use (exists_zeroTerm_normalisedTorus_le T P D' (Y.map toAdele * S.x.1) ?_
      isCompact_singleton).elim fun _ h ↦
      squeeze_zero_norm (fun x ↦ .trans ?_ ((h 1 rfl x.1 (indicator {ι}ᶜ x.1) ?_ _).trans (by
      grw [hR _ x.2.2]))) ?_ <;> simp [indicator, kAdelic, dyadicDiag, ← Finset.sum_sub_distrib,
      apply_ite, ite_sub, ← ext_iff, ← Matrix.mul_assoc, ← Matrix.map_mul,
      mul_apply.trans congr($hv _), by simpa [← ext_iff_mulVec] using (congr($hY ⟨_, ·, rfl⟩))]
    apply ((tendsto_pow_atTop hm.ne_bot).comp ((tendsto_pow_atTop_atTop_of_one_lt
      (mod_cast by simp)).comp tendsto_comap)).const_div_atTop
  refine (sub_eq_zero.1 (hℓ _ ▸ eq_zero_of_le_tsum_zeroTerm P hm ?_ sm fun f ↦ ?_)).symm
  intros; simpa [hℓ, Lagrangian.zeroTerm, mixedValue_splitWeil] using! thetaIntegral_pairWeil _ 1
  have c : Continuous (splitWeil S T ⟨·, 1⟩ f) := by fun_prop
  apply ((((Finite.pi' fun ι ↦ Nat.cofinite_eq_atTop.le (eventually_comap.1 (key (hΩ.image (.smul
    (.inv₀ (by fun_prop) (norm_zeroTerm_vacElem_pos T P · |>.ne')) c)) ι (closedBall_mem_nhds 0
    one_pos)))).image _).isCompact.mul hΩ).image (ℓ.2.comp c)).isBounded.exists_pos_norm_le.imp
  rintro B hB _ ⟨g, rfl⟩
  obtain ⟨γ, x, κ, k, ⟨⟩⟩ := H g
  refine (exists_lagrangian_equiv_containing T (isometrySplitting γ)).elim fun σ o ↦
    sub_le_iff_le_add'.2 (.trans' (by_contra fun h ↦ h
    ((hB.2 _ ⟨_, mul_mem_mul ⟨x, fun _ j ↦ h ?_, rfl⟩ k, rfl⟩).trans (by simp [tsum_nonneg]))) ?_)
  grw [← hB.1.le, ← (sm _).le_tsum (σ P.lagrangian) (by simp)]
  simpa [o, zeroTerm_isometrySplitting, normalisedTorus,
    norm_zeroTerm_parabolic_mul (levi_mul_kAdelic ..), rep_apply_apply, field,
    div_le_iff₀ (norm_zeroTerm_vacElem_pos ..), mul_assoc] using j ⟨x, _, κ, k, rfl⟩ rfl
  rw [hℓ, ← (σ.trans (.subtypeUnivEquiv (by simp [isometrySplitting, colSpan]))).tsum_eq]
  simp [hℓ, o, zeroTerm_isometrySplitting, rep_apply_apply, mul_assoc, splitWeil,
    (pairThetaKer ..).theta_rat_mul _ ⟨γ, rfl⟩]
