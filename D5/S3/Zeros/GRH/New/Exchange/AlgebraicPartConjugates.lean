/- GID: D5/S3/Zeros/GRH/New/Exchange/AlgebraicPartConjugates
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/AlgebraicPartConjugates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.AlgebraicPartConjugates. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/AlgebraicPartConjugates.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Exchange.TriangleLevelExponent
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! This file: Galois conjugate of the lift is the lift for the conjugate Hecke character. Galois
conjugates of the lift's squared norm: factorials over periods, error bounded below. -/

open Finset G LValueData Matrix Parameters Prod Real Space

/-- Galois action on Ξ. Given n, places S with Q empty and σ ∈ Aut(ℂ/K), there are t, l ≠ 0, u with
|t| = Ω^{−1/2} such that, if |n| = 2m, X is on S and μ = σ∘X.μ at finite points, σ(per^D
Ξ(h)_i) = t^D·l·(μυ^m)(u)·(σΔ(h)/Δ(h))·Ξ′(h)_{i′}; D = ∑ dg, Ξ′ the lift for μ, places permuted by
σ; Ξ = `LValueData.trivialLift`, per = `Parameters.jetScale`, dg = `jetDeg`, σΔ/Δ =
`multiplierRatio` σ. -/
lemma LValueData.map_trivialLift {P s} n [Fintype n] (S : LevelPlaces (E P s)) (hψ :
  IsEmpty S.TwistIndex) (σ : Gal(ℂ/K P)) : ∃ t l u, ‖t‖ = (√(P.bigOmega s))⁻¹ ∧ l ≠ 0 ∧ ∀ {X :
  LValueData _ n} {e μ ψ m} is unr, X.1 = S → let Y := (mk X.1 (X.jetDeg <|
    e.symm ·) μ ψ is X.one_lt_card unr); Fintype.card n = 2 * m → placePerm s σ = e → (∀ u, u.1.1 =
    1 → μ.1 u = σ (X.μ.1 u)) → ∀ h i, σ ((P.jetScale s ^ (∑ τ, X.jetDeg τ) • X.trivialLift) h i) =
    (t ^ ∑ τ, X.jetDeg τ) * (l * Y.auxPair.b.1 u) * multiplierRatio σ (onHom (s :=
    X.auxPair.signs) (s' := 1) (1, 1, h)).2 * Y.trivialLift h (i <| e.symm ·) := by
  choose t l z L T hl h1 _ using exists_semilinear_isJetConjugate ((stdSpace _ Unit).hom
    (stdSpace _ n)) (R := S.places) (by grind [S.7.2]) σ
  exact ⟨t, l, _, by simpa using congr(√$T), hl, by
  introv a Y hm he hb; subst a; simp [↓Y.trivialLift_eq_stdClassSum_translate (scalarFin _ z⁻¹),
    trivialLift, apply_eq_evalForm, classSum, mul_sum,
    map_rat_smul, -MonoidHom.coe_range]; congr! 2 with g
  have := congr((schurJet
    _ $((he ▸ h1) _ (pairWeilFinite _ _ 1 X.auxPair.b (g.out, h) X.auxPair.auxDatum).2) *ᵥ 1) i)
  rw [(_ : L _ = (_ : ℂ) • _), (_ : ∀ F, schurJet _ (.rename _ F) =
    (schurJet Y.auxPair.κ F).submatrix (e.piCongrLeft' _) (e.piCongrLeft' _)),
    submatrix_mulVec_equiv, schurJet_jetSeries_eq_smul Y.isLiftWeight] at this
  with_unfolding_all simpa [↓← apply_eq_evalForm, kernelForm, kernelValue, entrywise, ← map_schurJet
                       X.isLiftWeight, AuxPair.κ, mul_sum, mixedWeight, Y, X.one_lt_card, boxes,
    schurJet_jetSeries_eq_smul X.isLiftWeight (jetScale ..), mul_assoc (_ ^ _), Equiv.sum_comp]
  intro; ext; apply jet_rename (Equiv.prodCongr _ 1).toEmbedding
  rw [map_schur Y.isLiftWeight.1, schur_apply_eq_prod X.isLiftWeight.1, ← e.symm.prod_comp,
    schur_apply_eq_prod Y.isLiftWeight.1]; simp; rfl
  simp_rw [pairWeilFinite_apply_apply_coe, pairWeil_apply]
  rw [show G.onHom ((_, _ * _), _) = _ by simpa using ((map_mul _ ((1, _), 1, h) _).trans
      congr(_ * $(onHom_scalarFin z⁻¹ 1))), onHom_fin, ← fst_mul_snd (_, _)]
  simp only [map_smulₛₗ, snd_mul, ← one_mk_mul_one_mk, mul_apply_eq_comp, *, omega_mem_finitePart,
    smul_smul,
    AuxPair.auxDatum, places_levelModulus, liftFn_eq_residueDatum, isSchwartzBruhat_residueDatum _
    X.apart.2, name_mem_finitePart _ _ vacElem_mem_finitePart, pairChar_apply, map_mul]
  congr 1; erw [multiplierRatio, finMultiplier_onHom_left, map_pow, ← div_pow, hm, pow_mul,
    multiplierRatio_sq, detFin, map_inv _ (1, _)]
  simp [rankTwist, *, funext_iff, mul_pow, field]
  congr with; simp [univ_eq_empty, residueDatum, AuxPair.resDetDatum, apply_ite σ]⟩

/-- For σ in Aut(ℂ/K) and fixed n, one c serves all pairs (ν, z) with |n| = 2z ≥ 4: untwisted,
log|σ(‖Ξ‖²)| = c + r + ∑_τ (log λ_τ! − λ_τ log(Ω/g)), λ_τ = c_τ − z, with r ≥ −4f, and r ≤
4f if all λ_τ = 0. -/
lemma Data.Pair.log_norm_map_norm_sq_trivialLift {P} (D : Data P) n [Fintype n] (σ : Gal(ℂ/K P)) :
    ∃ c, ∀ (p : D.Pair) (H : p.HasLiftRank n), ∃ r : ℝ, -(4 * D.f) ≤ r ∧ (p.IsFlat n →
  r ≤ 4 * D.f) ∧ log ‖σ (‖trivialLift H .one‖ ^ 2)‖ = c + r + ∑ τ, D.jetSize (p.c τ - p.z) := by
  choose t c z _ _ J using map_trivialLift n (D.levelPlaces .one) ⟨nofun⟩
  constructor; intro p H
  let X := lValueData H .one
  choose ν hν hb using X.hasWeight.exists_conj (σ := σ) placePerm_spec
  let Y := LValueData.mk X.1 _ ν _ hν X.6 (by clear * -; simp_all [X.7])
  obtain ⟨C, h⟩ := Y.inner_trivialLift_self_eq_L H.1.symm H.2
  set ℓ := ν⁻¹.L ..
  have : ℓ ≠ 0 ∧ _ :=
    abs_log_norm_eulerProd_le hν.inv.isHeckeOfType.norm_heckeCoeff_le le_rfl (mod_cast H.2)
  simp [finrank_eq_two_mul_card_infinitePlace, abs_le, -Set.Sum.elim_range] at this C
  use log (Fintype.card (WeylIndex n Y.auxPair.κ)) +
    log ‖ℓ‖, by grw [← log_natCast_nonneg]; linarith!,
    fun d ↦ by grw [Fintype.card_le_one_iff.2 fun _ _ ↦ linearIndependent_nablaBasis
    (R := ℂ).injective (by simp [nablaBasis_eq_one, Y, X, d])]; simp; linarith!
  erw [trivialLift, mul_pow, ← mul_assoc, mul_smul, norm_smul, norm_mul, norm_pow (star _),
    Complex.ofReal_mul, mul_pow, ← inner_self_eq_norm_sq_to_K (_ • X.trivialLift),
    ← Complex.ofReal_pow, mul_pow, pow_right_comm, D.norm_map_star_piG_sq 1, map_mul,
    LevelPlaces.map_inner_self_eq σ _ (J σ hν Y.7 rfl H.1 rfl hb) (J {(starRingAut * σ.toRingEquiv *
    starRingAut :) with commutes' x := by simpa using congr(star $(σ.4 (star x)))} hν _ rfl
    H.1 congr(.mulLeft (.mk $(by ext; simp [← map_star_complex, placePerm_spec])))
    (by simp [← Circle.coe_inv_eq_conj, ← hb · ·])) (by simp [multiplierRatio, div_mul_div_comm,
    finMultiplier_ne_zero, ← map_finMultiplier_mul_conj σ]), h,
    prod_coe_sort, hookNumber_eq_prod_factorial, ← Equiv.prod_comp (placePerm _ σ)]
  simp +instances [jetSize, log_mul, log_div, log_prod, *, X, Y, bigOmega_pos, NeZero.pos, log_sqrt,
    le_of_lt, prod_ne_zero_iff, ne_of_gt, ← sum_mul, -Fintype.card_pi, -H, ← sub_eq_iff_eq_add,
    twist_one_spec]
  ring; rfl
