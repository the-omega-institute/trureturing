/- GID: D5/S3/Zeros/GRH/New/Exchange/ExchangeTheorem
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/ExchangeTheorem
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.ExchangeTheorem. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/ExchangeTheorem.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.ClassField.HeckeCharacter.LevelModulus
import D5.S3.Zeros.GRH.New.Exchange.EqualRankValue
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Exchange theorem for theta integrals of complementary rank. If the ranks and negative signs of hermitian spaces V, V' over a CM field add up to those of W (few negative), with rk V − rk V' = 2e ≥ 0, then theta integrals over U(V) and U(V') agree on matched ramified data up to a nonzero constant sized by the conductor and Hecke L-values at 1,…,e, so theta lifts can be exchanged. Equal theta lifts of characters of complementary groups are known for trivial characters (Siegel–Weil) and for O(3), O(1) to Mp(2). Related work: Snitz, Theta correspondence of automorphic characters (thesis), 2003; Erez, Matchings of theta lifts of automorphic characters, arXiv 2401.13469, 2024; Gan–Qiu–Takeda, The regularized Siegel–Weil formula (second term identity), 2014. -/


open RingHom Fintype Modulus IsLinearMap
variable {E} [Field E] [CMType E] [WeilData E] {n a b} [Fintype n] [Fintype a] [Fintype b] {s t t'}
  (W : Space E n s) (V : Space E a t) (V' : Space E b t')

/-- Exchange theorem: let rk W = n = rk V + rk V′, rk V = rk V′ + 2e, q_W = q_V + q_{V′} negative
signs, n ≥ 2q_W + 2, μ ≥ n/2 − q_W, v rapid. Some C and rapid x give
∫_{[U(V)]}θ(x⊗Φ) = c∫_{[U(V′)]}θ(v⊗Ψ) for partners, c ≠ 0, |c|² = C·`lValueProd`, for each tame ν.

Exchange theorem for theta integrals of complementary rank. -/
lemma exchange_theorem σ (hs : negCount s = negCount t + negCount t') {e} (he : card a =
  card b + 2 * e) (hn : 2 * negCount s + 2 ≤ card n) {μ : _ → ℤ} (hμ : ∀ v,
  card n ≤ 2 * μ v + 2 * negCount s) {v} (hv : IsRapidDatum v) : ∃ C x, IsRapidDatum x ∧ ∀ 𝔪 ν χ,
  IsTameFor 𝔪 ν μ χ → let γ := rankTwist ν⁻¹ n; ∃ c ≠ 0, ‖c‖ ^ 2 = C * lValueProd 𝔪.places ν e
    ∧ ∀ Φ Ψ, IsPartner ⊤ σ χ Φ Ψ → ∀ g, thetaIntegral W V γ 1 (modDatum W V 𝔪 Φ x) g =
    c * ∫ h, pairTheta V' W γ γ (modDatum _ W 𝔪 Ψ v) (h, g) ∂V'.quotMeasure := by
  have ⟨_, r₀, C₀, _⟩ := exists_equalRankThetaRatio_value W μ (card n / 2 - negCount s) ?_ ?_
  have ⟨C, x, r, H⟩ := exchange_of_partners V' μ (removePlanes _ W) V σ r₀ hv ?_ ?_
  use C₀ / C, x, r, fun 𝔪 ν χ ⟨h, ψ, a₁, a₂, a₃⟩ ↦ ?_
  have o := 𝔪.places.toFinite.coe_toFinset
  let 𝔠 := SplitTameChar.mk ν ψ a₁ _ (by simpa using! h) (by simpa using! 𝔪.not_le_star) (o ▸ a₂) ?_
  obtain ⟨⟨c, hc, H⟩, l, _, m, _, ρ, _, k, k'⟩ := H 𝔠, lValueProdInt_pos 𝔠 e, o ▸ 𝔠.readsAt
  simp +arith [*, ← card_congr σ, Int.add_mul_ediv_left] at hc
  simp [lValueProdInt, lValueProd.eq_1 _ _ 0] at *
  use c, by grind [norm_zero], by grind, fun Φ Ψ P ↦ ?_
  let π := ((evalPlaces 𝔠.S).restrict _ _ evalPlaces_mem_O).liftOfRightInverse
    (⟨_, by simpa [← k', *] using m <| ρ ·⟩) (Subtype.ext <| k ·) ⟨𝔪.reduction, fun x hx ↦
    (𝔪.reduction_congr (y := 0) (congr($hx.1 ⟨·, o.ge ·⟩))).trans (map_zero _)⟩
  have e i u : modulusResidue _ (o.le i.2) (π u) = residueAt i u :=
    (modulusResidue_reduction ..).trans congr(⟦⟨$(k u) i, _⟩⟧)
  have d {n n' : Type} [Fintype n] [Fintype n'] Φ : 𝔪.liftFn (Φ ∘ @vecToMat n n' _) =
    (liftIntegralFn π Φ <| vecToMat <| evalPlaces
    _ ∘ ·) := by ext; erw [liftFn_apply, mk'_apply]; congr! <;> simp [vecToMat, m, ← k']; rfl
  simpa [modDatum, 𝔠, *] using! H _ _ (by simpa [Function.comp_def, *] using (d Ψ ▸
    isSchwartzBruhat_liftFn .. :).locally_constant.comp_continuous (f := (ρ ∘ matToVec ·)) (by
    fun_prop [matToVec])) (P.lift_of_reduction π ⟨fun u h ↦ isUnit_iff_residueAt_ne_zero.2
    (e · u ▸ (h.map _).ne_zero)⟩ (𝔪.reduction_surjective.forall.2 fun _ ↦
    ⟨_, liftOfRightInverse_comp_apply ..⟩) (by
    simp_intro .. [← finprod_comp_equiv (Set.equivOfEq o),
    a₃, charOfTamePart, ← e, 𝔠.localChar_apply_of_isUnit, finprod_eq_prod_of_fintype]; rfl))
  repeat grind [card_sum, card_congr σ, card_unit]
