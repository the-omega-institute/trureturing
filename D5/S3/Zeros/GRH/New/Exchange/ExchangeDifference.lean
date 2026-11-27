/- GID: D5/S3/Zeros/GRH/New/Exchange/ExchangeDifference
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/ExchangeDifference
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.ExchangeDifference. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/ExchangeDifference.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Exchange.StableSpaces
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.ThetaIntegralLaws
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Exchange theorem for theta integrals of complementary rank (see
New.Exchange.ExchangeTheorem).

This file: Difference of both theta integrals is an equivariant functional of one partner datum. -/


open RingHom Matrix Pi WeilData SemilocalField Fintype SplitTameChar GeneralLinearGroup
variable {E} [Field E] [CMType E] [WeilData E] {n a b} [Fintype n] [Fintype a] [Fintype b]
  {s t t' μ} (W : Space E n s) (V : Space E a t) (V' : Space E b t') (𝔠 : SplitTameChar E μ)

/-- The theta integral over [U(V)], characters νυ^⌊rk W/2⌋ and υ^{rk V}, of the datum with real
part v and y ↦ Ψ(yᵀ), read through conjugation at the places conjugate to 𝔠.S;
υ = `WeilData.upsilonU1`. -/
noncomputable abbrev thetaSmall v (Ψ : _ → ℂ) :=
  thetaIntegral W V (rankTwist 𝔠.ν n) (upsilonU1 ^ card a) (localDatum W V v (Ψ ·ᵀ) 𝔠.readsAt.star)

attribute [local simp] atPlaces_star atPlaces_of_mem_trivialOn nu_det_of_mem_Kf
  MulChar.inv_apply_eq_inv'

/-- For W of even rank, rapid v, v′ and c ∈ ℂ, there are a space M of data and a linear 𝒟
satisfying `IsEquivariantLift` such that for integral partners Φ, Ψ with Ψ locally constant, Ψ
∈ M and 𝒟Ψ = `thetaLarge` Φ − c·`thetaSmall` Ψ. -/
lemma exists_isEquivariantLift σ (hn : 2 ∣ card n) {v v'} (hv : IsRapidDatum v) (hv' :
  IsRapidDatum v') (c : ℂ) : ∃ M 𝒟, IsEquivariantLift
  𝔠 W (localChar _ (υ ^ card b) (card b))⁻¹ M 𝒟 ∧ ∀ {Φ Ψ}, IsLocallyConstant Ψ →
  IsPartner O σ 𝔠.χ Φ Ψ → Ψ ∈ M ∧ 𝒟 Ψ = thetaLarge W V 𝔠 v Φ - c • thetaSmall W V' 𝔠 v' Ψ := by
  obtain ⟨⟨Λ, H⟩, ⟨Λ', H'⟩, r, r'⟩ := exists_linear_thetaIntegral W V ..,
    exists_linear_thetaIntegral W V' .., 𝔠.readsAt, 𝔠.readsAt.star
  have e := matchingPairs.exists_linear_factor _ σ (𝔠.tameLocalChar (card n))
    (Λ ∘ₗ ⟨⟨(localDatum W V v · r), ?_⟩, ?_⟩) fun g Φ hΦ ↦ ?_
  let l := e.choose - c • Λ' ∘ₗ ⟨⟨fun Ψ ↦ localDatum W V' v' (Ψ ·ᵀ) r', ?_⟩, ?_⟩
  have e {p} m : l _ = _ := congr($((e.choose_spec p m).trans (H (r.isTargetBounded hv m.1.1) :)) -
    c • $(H' (r'.isTargetBounded hv' m.1.2.transpose_mem_schwartzBruhat)))
  refine ⟨.map (.snd ..) _, _, ⟨fun _ ⟨_, m, e⟩ ↦ e ▸ m.1.2, ?_, ?_, ?_⟩, fun h ⟨p, q, _⟩ ↦ (fun m ↦
    ⟨⟨_, m, rfl⟩, e m⟩) (IsPartner.mem_matchingPairs (𝔠.tameLocalChar _) ⟨p, q, by simp_all [intGL,
    localChar_apply_of_isUnit, ← val_det_apply, GeneralLinearGroup.map_det]⟩ h)⟩ <;> rintro _ ⟨p, m,
    rfl⟩ <;> erw [e m]
  simpa using (Space.Splitting.centreCoeff_sub (W₀ := W) (p :=
    n) (r.isTargetBounded hv m.1.1).isAutFunction_thetaIntegral
    (r'.isTargetBounded hv' m.1.2.transpose_mem_schwartzBruhat).isAutFunction_thetaIntegral c 1).1
  intro g hg; have q := matchingPairs.translate_mem _ σ m (atPlaces _ g⁻¹); use ⟨_, q,
    rfl⟩; erw [e q]
  any_goals simp only [sub_def, Pi.smul_apply, ← thetaIntegral_pairWeil (_, 1, 1)]
  simp +contextual [localDatum, ↓pairWeil_integrated_fin, ↓pairWeil_name_on r.1 (hΨ :=
    r.isSchwartzBruhat q.1.1), ↓pairWeil_name_on r'.1 (hΨ :=
    r'.isSchwartzBruhat q.1.2.transpose_mem_schwartzBruhat), Gf.mem_supportedOn.1 hg, ↓detOn_star,
    AutChar.spaceChar, ← Pi.smul_def,
    eq_mul_inv_of_mul_eq (spaceChar_rankTwist hn), -smul_eq_mul, ↓localChar_det, υ_star, -coe_comp]
  simp [sq, mul_pow, ← card_congr σ, field, pow_add, thetaIntegral, pairTheta]
  simp_all [↓r.pairWeil_localDatum_of_mem_Kf m.1.1, ↓r'.pairWeil_localDatum_of_mem_Kf
    m.1.2.transpose_mem_schwartzBruhat, rankTwist, -coe_comp]
  any_goals simp [localDatum, ← add_def, ← Pi.smul_def, -smul_eq_mul]
  ext x; obtain ⟨⟨k, _, rfl⟩, d, _⟩ := 𝔠.exists_atPlaces_eq g, r.isTargetBounded hv hΦ,
    r.isSchwartzBruhat hΦ
  erw [H d, ← mul_one x, ← thetaIntegral_pairWeil (1, ↑k⁻¹),
    ← H (Exists₂.imp (by simp_all [pairTheta, pairWeil, rep_apply_apply, ← map_mul]) d),
    pairWeil_integrated_fin, pairWeil_name_on] <;> simp_all [r.1, spaceChar_rankTwist]
