/- GID: D5/S3/Zeros/GRH/Lib/SiegelWeil/Formula/SiegelSets
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/SiegelWeil/Formula/SiegelSets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.SiegelWeil.Formula.SiegelSets. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/SiegelWeil/Formula/SiegelSets.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.Unramified.HeckeTransfer
import D5.S3.Zeros.GRH.Lib.SiegelWeil.Formula.ZeroTermHeight
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Siegel–Weil formula in the convergent range (known result; see
Lib.SiegelWeil.Formula.SiegelWeilFormula).

Part of: Reduction theory: Mahler-Godement compactness, finite covolume, adelic Minkowski theorems
(known result; see Lib.Adelic.Reduction.Defs).

This file: Invariant functional small against the positive Eisenstein series vanishes, by one Hecke
operator. Normal form, Siegel sets and uniform convergence of the Siegel Eisenstein series. -/

open Finset Matrix Real Fintype ComplexOrder WeilData Space Splitting AutChar HeckeChar Lagrangian G
  Complex

/-- Let S ≠ 0 be split, rk T > rk S, ∑_L|ev_L f| finite for each f (L Lagrangian). A continuous
U(T)(𝔸)-invariant functional ℓ vanishes if, for each f, |ℓ(ω(g)f)| − ∑_L|ev_L ω(g)vac| is
bounded above for g in U(S)(𝔸). -/
lemma eq_zero_of_le_tsum_zeroTerm {E n m p} [Field E] [CMType E] {s t} [WeilData E] [Fintype n]
  [Fintype m] {S : Space E n s} {T : Space E m t} [Fintype p] [Nonempty n] (D : CompleteSplitting S
  p) (hm : 2 * card p < card m) {ℓ : _ →L[ℂ] ℂ} (hℓ : ∀ h f, ℓ (splitWeil S T (1, h) f) = ℓ f) (hs :
  ∀ f, Summable (‖Lagrangian.zeroTerm (S := S) T · f‖)) (hB : ∀ f,
  BddAbove (.range fun g ↦ ‖ℓ (splitWeil S T (g, 1) f)‖ - ∑' L, ‖Lagrangian.zeroTerm T L (splitWeil
  S T (g, 1) (vacElem _))‖)) {f} : ℓ f = 0 := ext_integrated _ (projOn_empty ..) fun P z _ ↦ by
  obtain ⟨⟨k, k0, hk⟩, hs, w, hw, hf⟩ := lt_iff_exists_add.1 hm, (hs · |>.hasSum.mul_left),
    ((frequently_prime_q.mono fun _ ↦ isSplit_of_q_prime).and_eventually (.all fun i ↦
    (z i).2.and (star_injective.tendsto_cofinite.eventually (z i).2))).exists
  have K {f} hf {ℓ : _ →L[ℂ] ℂ} (hℓ : ∀ h f, ℓ (splitWeil S T (1, h) f) = ℓ f) := by
    choose h _ H using hecke_transfer_of_equivariant (f :=
      f) (by simpa [D.card_eq]) ((hasWeight_upsilonU1_pow (card n / 2)).charUnramifiedAt rfl rfl)
      (HasWeight.one.charUnramifiedAt rfl rfl) hw hf (.pi fun g ↦
      (ℓ ∘L splitWeil S T (g, 1)).1) (finRightRep ..) 1 fun x h ↦
      funext fun g ↦ .trans (by simp [splitWeil, rep_apply_apply]) (hℓ h _)
    simpa [(isSphericalWith_trivialHecke ..).2, ↓heckePolyOp_eq_sum hw h, frobValue,
      AutChar.spaceChar, ← pow_mul, atUnif, finPart,
      D.card_eq, mul_sum, ← mul_assoc, -Prod.forall, -map_inv] using (congr(‖$(H (-1)) ·‖))
  refine by_contra fun c ↦ (congr(‖$((hℓ ..).trans ((ℓ.map_smul ..).trans (div_mul_cancel₀ _
    c)))‖).trans_gt (NormedField.exists_lt_norm ..).choose_spec).not_ge (sub_nonpos.1
    (maximum_principle (hB _) _ _ ?_ (fun g ↦ (by simpa only [mul_sub, sum_sub_distrib] using id :
    _ → _) (sub_le_sub ((K (by rw [map_smul, projOn_integrated, projOn_finHeisOp, boxIndicator,
    ite_eq_left] <;> simp [mem_integralBox, idem_mul_mem_Ô, star_eq_iff_star_eq]; simpa
      using! hf) hℓ
    g).trans_le (norm_sum_le_of_le _ fun _ _ ↦ norm_mul_le ..)) (hasSum_le (fun L ↦ (K (by simp)
    (by simp [Lagrangian.zeroTerm, mixedValue_splitWeil]) g).trans_ge ?_) (hasSum_sum fun _ _ ↦
    hs ..) (hs ..)))) _))
  · have h : 1 < √w.q := by simp [lt_sqrt]
    have := q_binomial_submodule n (ResField w) ⊤ (-√w.q ^ k)
    simp [heckePolyCoeff, w.q_eq_sqrt_sq, -mul_self_sqrt, sq, pow_add, ← div_div, ← div_pow, *,
      D.card_eq, mul_assoc, ← mul_sum, card_ResField] at this ⊢
    norm_cast at *
    simp (disch := positivity) only [*, norm_of_nonneg, two_mul, add_right_comm,
      prod_range_add, ← prod_mul_distrib, mul_comm _ ((range k).prod _), mul_assoc]
    apply mul_lt_mul' (by congr!; ring) (prod_lt_prod_of_nonempty₀ _ (fun j _ ↦ by
      linear_combination _ ^ (2 * j) * mul_add_mul_lt_mul_add_mul (pow_lt_pow_right₀ h k0)
        (hk ▸ one_lt_pow₀ h hm.ne_bot)) ⟨0, by simpa using card_pos.trans_eq D.card_eq⟩)
      <;> intros <;> positivity
  simp [↓fun u ↦ (by rewrite [← Prod.mk_one_mul_mk_one, pairWeil_apply, G.onHom.map_mul,
    ← rep_apply_apply, ← projOn_vacElem (S := {w}), ← name_boxIndicator, show G.onHom (_, 1) =
    _ from onHom_fin .., ω_name_on, map_smul, map_smul, map_smul, ← mul_inv_cancel_left _ (G.onHom
    (g, _)), ← rep_apply_apply] <;> (try erw [RingHom.map_mul, ← Circle.coe_inv_eq_conj, (omega_name
    ..).2, (θ _).comp_apply, sourceTerm_zero, ← mixedTerm_zero, ← mulVec_zero (1 : GL _ _).1⁻¹ᴴ,
    ← finVec_zero, (exists_isAdapted_and_frame_eq ..).choose_spec.1.omega_name_of_isMixedLaw
    isMixedLaw_mixedTerm _ _ _ ((IsSchwartzBruhat.comp_mulVec _).comp_mulVec _),
    (name ..).pi_apply_eq_sum_univ, sum_unique, sliceDatum,
    eq_coe_norm_of_nonneg (MeasureTheory.integral_nonneg _)]) <;> simp [*, ite_nonneg, Pi.le_def] :
    L.zeroTerm T (splitWeil S T (g * (1, atSplit hw u), 1) (vacElem _)) = _), ← coe_singleton,
    detOn_eq_prod, (charUnramifiedAt_upsilon _).apply_locFullIdele, (basicCosetRep_spec _).1.2,
    mul_pow, mul_assoc, ← mul_sum, atUnif, finPart, div_pow, det_kronecker', _root_.zpow_mul]
  field_simp; simp [← sum_mul, mul_div_right_comm]; norm_cast
  gcongr; rw [mul_comm]; apply le_norm_self

attribute [-simp] Matrix.coe_units_inv

open ENNReal Set MonoidHom Int Classical Subsingleton
variable {E n m p} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype m] [Fintype p] {s t}
  {S : Space E n s} (T : Space E m t) (P : CompleteSplitting S p)

attribute [local simp] radicalElt_mul_kAdelic levi_mul_kAdelic Matrix.mul_assoc _root_.zpow_add
  dyadicDiag mul_assoc

@[local simp] lemma radicalElt_eq_conj_levi a b : P.radicalElt 0 (a.1 * (b * a.1ᴴ)) =
    MulAut.conj (P.levi (a, 1)) (P.radicalElt 0 b) := by simp [↓P.levi_conj_radicalElt]

attribute [local simp↓ ←] radicalElt_zero_mul Matrix.map_mul

lemma exists_compact_parabolic_normal_form : ∃ Ω, IsCompact Ω ∧ ∀ g γ, ∃ δ x y ν,
  (ν, P.levi (dyadicDiag x, 1) * (radicalElt P 0 ν)⁻¹ *
  S.ratEmbed δ⁻¹ * g) ∈ Ω ∧ P.ActsOnFrame (S.ratEmbed (δ⁻¹ * γ)) ((y : GL p E).map toAdele).1 := by
  obtain ⟨⟨N, hN, H⟩, M, _, hM, h⟩ := IsCovolOneLattice.exists_compact_cover (ratMatrices E p p),
    exists_isCompact_profileBases E p
  exact ⟨_, hN.prod (isCompact_maxCompact.mul (hM.image_auto (P.levi ⟨·, 1⟩) (by
    simp [↓continuous_iff, Splitting.levi]; fun_prop))).inv, fun g γ ↦
    (P.iwasawa ((S.ratEmbed γ)⁻¹ * g)).elim fun κ ⟨hκ, a, _, _, c, z, u, e⟩ ↦
    (h a).elim fun x ⟨y, hy, _⟩ ↦ let a := y⁻¹.map toAdele; (H (a * z * a.1ᴴ)).elim fun r ⟨hr, hb⟩ ↦
      (mul_mem (P.radicalElt_mem_Gamma 0 hr) (P.levi_mem_Γ y⁻¹ ⟨1,
    rfl⟩)).elim fun δ hδ ↦ ⟨γ * δ⁻¹, x, y⁻¹, _, ⟨hb, _, hκ, _, ⟨_, hy, rfl⟩, by simp [*, a, eq_zero
      c, eq_mul_inv_of_mul_eq e, ← inl_apply, eq_one u]⟩, by simp [*, ← (mat _).mul_assoc]⟩⟩

/-- Siegel-set decomposition for split S: there is a compact Ω such that every adelic g equals γ
· levi(diag(2^{x_i})) · κ with γ rational, x ∈ ℕ^p and κ ∈ Ω, where 2 is the archimedean
idele. -/
lemma exists_siegel_set : ∃ Ω, IsCompact Ω ∧ ∀ g, ∃ γ, ∃ x : p → ℕ, ∃ κ ∈ Ω,
    g = S.ratEmbed γ * P.levi (dyadicDiag (x ·), 1) * κ := by
  obtain ⟨⟨Ω, hΩ, h⟩, F, C, hF, hC, H⟩ := exists_compact_parabolic_normal_form P, exists_finite_gram
    ((toFinite {stdForm E s}).preimage Units.val_injective.injOn).isCompact
  choose! r hr using fun T (_ : T ∈ F) ↦
    @id (∃ R : Matrix n p E, HasLeftInv (diagonal T.1 * R) ∧ Rᴴ * T.2 * R = 0)
  choose c k using fun i ↦
    exists_eq_zero_of_zpow_mul_mem (hF.isCompact_biUnion fun T _ ↦ isCompact_iUnion ((hΩ.prod
    hC).image_auto fun (κ, A) ↦ (P.kCoord * κ.2.mat * A.2 * (r T).map toAdele) i ·))
  refine ⟨_, ((isCompact_closedBall_prod_integral (E := E)).matrix.prod hΩ).image_auto
    fun (a, b, κ) ↦ P.radicalElt 0 (a * b * aᴴ) * ((P.levi (dyadicDiag (-c), 1))⁻¹ * κ),
    fun g ↦ (H S.isUnit_J.unit _ (S.move g).gram_point).elim fun Y ⟨d, i, z, m⟩ ↦ ?_⟩
  set W := (star Y * _)⁻¹
  have ⟨γ, hγ⟩ := exists_isometry_orthogonal P ⟨_, congr(submatrix $Y.inv_val _ _).trans
    (submatrix_one _ (by simp))⟩ (funext₂ i)
  have u : diagonal d * (⅟W.1 * (γ.1.1 * P.k)) = _ := Matrix.ext fun i j ↦ (diagonal_mul ..).trans
    (mul_left_eq_self₀.2 (or_not.imp_right (congrFun₂ hγ ⟨i, ·⟩ j)))
  have q := hr _ m ⟨_, ⟨_, by rw [Matrix.mul_assoc _ W.1, u, Matrix.mul_invOf_cancel_left,
    U.gram_invariant, P.gram_lk]⟩, by erw [← gram_mul, W.1.mul_assoc, u,
    Matrix.mul_invOf_cancel_left, U.gram_invariant, P.gram_kk]⟩
  have ⟨a, ha⟩ := S.witt ⟨_, P.gram_lk⟩ (q.1.imp' (· * W.1⁻¹) (by simp))
    (P.gram_kk.trans ((gram_mul ..).trans q.2).symm)
  choose δ x y ν hκ hy using h g a
  choose t ht using fun i ↦ le.dest (le_neg.1 (not_lt.1 (y.det_ne_zero <| det_eq_zero_of_row_eq_zero
    i fun j ↦ k i (-x i) · (mem_biUnion m ⟨_, ⟨j, rfl⟩, (_, _), ⟨hκ, z⟩, by
    simp [move, mat.eq_1 g, radicalElt_inv] at ha hy ⊢
    erw [← ha, ← S.ratMap_mul_toAdele S, hy]; simp [← Matrix.mul_assoc]⟩))))
  exact ⟨δ, t, _, ⟨(_, _), ⟨dyadicDiag_inv_mem t, hκ⟩, rfl⟩, by
    simp [← inl_apply, ← ht, ← Pi.mul_def]⟩

/-- If rk T > 2p, there is a summable function c on the Lagrangians L of the split space S bounding,
uniformly in x, the operator norm of the zero term ev_L composed with the operator `normalisedTorus`
T P x. -/
lemma exists_summable_zeroTerm_bound (hm : 2 * card p < card m) :
    ∃ c, Summable c ∧ ∀ x L, ‖Lagrangian.zeroTerm T L ∘L normalisedTorus T P x‖ ≤ c L := by
  obtain ⟨⟨Ω, hΩ, h⟩, N, hN, H⟩ := exists_compact_parabolic_normal_form P,
    IsCovolOneLattice.exists_compact_cover (ratMatrices E p p)
  choose γ hγ using fun L : Lagrangian S ↦
    exists_isometry_orthogonal P ⟨_, gram_lk _⟩ L.completeSplitting.1.2.gram_kk
  choose δ x y ν hκ e₁ using (h 1 <| γ ·)
  choose d hd using fun j ↦ exists_eq_zero_of_zpow_mul_mem (isCompact_iUnion (hΩ.image_auto fun κ ↦
    (S.x.1 * κ.2⁻¹.mat * P.kAdelic) · j))
  choose t ht using fun L j ↦ le.dest (not_lt.1 ((congrFun₂ ((U.gram_invariant (δ L) ..).trans
    P.gram_lk) j j).trans_ne (by simp) <| sum_eq_zero fun i _ ↦ mul_eq_zero_of_right _ <|
    hd j (x L j) · ⟨_, ⟨i, rfl⟩, _, hκ L, by
    simp [← (mat _).mul_assoc, ← map_inv, mat_ratEmbed]
    simp [kAdelic, ← Matrix.mul_assoc, mul_comm]⟩))
  let K := Subtype.mk _
    ((hN.image_auto (P.radicalElt 0)).mul (hΩ.image_auto ((P.levi (dyadicDiag d, 1))⁻¹ * ·.2)))
  obtain ⟨⟨R, hR⟩, ⟨F, hF⟩, C, hC, hB⟩ := exists_zeroTerm_normalisedTorus_le T P P P.kCoord
    (by simp) K.2, (tendsto_coe_cofinite_of_isDiscrete S.ratEmbed_injective
      ⟨S.discreteTopology_Gamma⟩
    (K.2.inv.mul K.2).compl_mem_cocompact).exists_encard_eq_coe,
    encard_hermitian_le (((isCompact_closedBall_prod_integral (E := E)).matrix.prod
    (hN.prod hΩ)).image_auto fun (a, u, v, _) ↦ a * (u + uᴴ) * aᴴ - (v + vᴴ))
  simp [ratMatrices, -Subtype.forall, kAdelic, -map_inv, mat_ratEmbed, coe_units_inv, ← ht,
    inv_mul_eq_iff_eq_mul_of_invertible,
    (map_injective (@toAdele E ..).injective).eq_iff] at H e₁ hκ
  choose b hc using fun L ↦ H ((dyadicDiag (t L ·)).1 * ν L * (dyadicDiag (t L ·)).1ᴴ)
  let Q L γ :=
    P.radicalElt 0 ((b L).map toAdele) * P.levi (dyadicDiag (t L ·), 1) * S.ratEmbed γ⁻¹ ∈ K.1
  have E₁ L : Q L (δ L) :=
    ⟨_, ⟨_, hc L, rfl⟩, _, ⟨_, hκ L, rfl⟩, by simp [← inl_apply, -coe_diagGL, ← Pi.mul_def]⟩
  have k L : CompleteSplitting.lagrangian ((isometrySplitting (δ L)).comp P) = L :=
    eq_of_le fun _ ⟨x, h⟩ ↦ (L.2 _).2 (L.completeSplitting.2 ▸ forall_colSpan_dot_eq_zero_iff.2
    (by simpa [← h, Splitting.comp, isometrySplitting, e₁] using congr($(hγ L) *ᵥ (y L)⁻¹.1 *ᵥ _)))
  have hB x : (t ⁻¹' {x}).encard.toENNReal ≤ _ := (mul_le_mul_left (hB (x ·)) F).trans' (mod_cast
    hF ▸ encard_prod ▸ encard_le_encard_of_injOn (f := fun L ↦ (b L + (b L)ᴴ, epsilon (Q L) * (δ
    L)⁻¹)) (fun L l ↦ ⟨⟨by simp [add_comm], (_, _, _), ⟨dyadicDiag_inv_mem x, hc L, hκ L⟩, by
    ext <;> simp [l.symm, ← map_inv, add_sub_add_comm, mul_add, twoAtInfinity, field]⟩,
    (· ⟨_, inv_mem_inv.2 (epsilon_spec ⟨_, E₁ L⟩), _, E₁ L, by simp⟩)⟩) fun L l M m ↦
    by simp +contextual [Q, radicalElt, ← Matrix.map_add, l.trans m.symm, ← (k L).congr (k M)])
  refine ⟨_, summable_toReal (f := fun L ↦ R / ((2 ^ numInfPlaces E) ^ ∑ i, t L i) ^ card m)
    (ne_of_lt ?_), fun x L ↦ (_ ∘L _).opNorm_le_bound toReal_nonneg ?_⟩
  grw [← tsum_fiberwise _ t, tsum_congr fun z ↦ by rw [tsum_congr (by rw [·.2]), tsum_set_const],
    hB, tsum_congr (g := (C * F * R * ∏ i, (.ofReal (2 ^ (2 * card p) / 2 ^ card m)
    ^ numInfPlaces E) ^ · i)) fun t ↦ by simp [toNat_add, division_def,
             prod_pow_eq_pow_sum, ← mul_sum, ENNReal.inv_pow]; ring, ENNReal.tsum_mul_left,
    tsum_prod_le_prod_tsum]
  simp [mul_lt_top_iff, hC.lt_top, div_lt_one, pow_lt_one_iff, pow_lt_pow_right₀, *]
  simpa [norm_zeroTerm_parabolic_mul (levi_mul_kAdelic ..), norm_zeroTerm_parabolic_mul (a := 1),
    -dyadicDiag, zeroTerm_isometrySplitting, field, mul_comm, k L ▸ zeroTerm_lagrangian_eq_theta ..,
    zeroTerm_homSource_comp, ← zeroTerm_lagrangian_eq_theta, -θ_apply] using hR _ (E₁ L) x x rfl
