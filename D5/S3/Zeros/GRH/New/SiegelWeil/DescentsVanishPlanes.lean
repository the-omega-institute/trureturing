/- GID: D5/S3/Zeros/GRH/New/SiegelWeil/DescentsVanishPlanes
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/SiegelWeil/DescentsVanishPlanes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.SiegelWeil.DescentsVanishPlanes. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/SiegelWeil/DescentsVanishPlanes.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.SiegelWeil.AuxPairVanishing
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Non-lifts sharing one Hecke root have zero theta periods (see
New.Rows.MemberOrthogonality).

This file: Climbing the theta tower: bounded descents with a too small Hecke root vanish. -/

open Matrix MeasureTheory WeilData Space Splitting Finset Fintype Real G MatMul
variable {E r n m p} [Field E] [CMType E] [WeilData E] [Fintype r] [Fintype n] [Fintype m]
  [Fintype p] {s t} {W : Space E r s} {W' : Space E m t} {V : Space E n 1} {a S Y}
  (h0 : DescentsVanish W V a S Y) (D : W'.Splitting W p)

omit [WeilData E] in
/-- Let F be a bounded function on the adelic unitary group of rank m, spherical at a split
place w and killed by the Hecke polynomial at w evaluated at X. If q_w^{m+1}|X| ≤ 1, then F
= 0. -/
lemma eq_zero_of_heckePolyOp_eq_zero {F w X} (hw : w.IsSplit) (hK : F ∈ sphericalAt (finRightRep E
  t) w) (h : heckePolyOp (finRightRep ..) hw X F = 0) (hX : w.q ^ (card m + 1) * ‖X‖ ≤ 1) (b :
  BddAbove (.range (‖F ·‖))) : F = 0 := have P := q_binomial_submodule m (ResField w) ⊤ (-‖X‖); by
  let r U : G E t := (1, atSplit hw (transposeGL (basicCosetRep U)))
  refine' funext (norm_le_zero_iff.1 <|
    maximum_principle b (heckePolyCoeff X) (· / r ⊥ * r ·) (l := 2) _ (fun g
    ↦ _) ·) <;> simp [funext_iff, heckePolyCoeff, heckePolyOp_eq_sum hw hK, -Prod.forall] at *
  norm_cast at *; grw [P, card_ResField, prod_one_add_le_exp_sum _ (by bound), ← lt_log_iff_exp_lt
    two_pos, ← sum_mul, ← log_two_gt_d9, ← Nat.cast_sum, Nat.geomSum_lt w.one_lt_q fun _ ↦
    mem_range.1, pow_succ, ← Nat.mul_le_mul_left _ w.one_lt_q] at *; grind
  simpa [h, r, two_mul, le_sub_iff_add_le] using norm_sum_le (univ.erase ⊥) fun U ↦
    heckePolyCoeff X U * F (g / r ⊥ * r U)

include h0 D
attribute [local simp] sourceTerm lt_sqrt lCoord CharUnramifiedAt AutChar.frobValue
  kronecker_mulVec_eq_matToVec name_boxIndicator projOn_empty
  Splitting.zeroTerm_apply coordMatrix kAdelic

lemma DescentsVanish.integral_sourceTerm_eq_zero [IsBaseAdapted D] {f} (hf : projOn _ S f =
  f) g : ∫ h, θ _ (D.sourceTerm V 0 (pairWeil _ V (a * upsilonU1 ^ card p) 1 (g, h) f)) * Y
  h ∂V.quotMeasure = 0 := by
  choose κ hκ t _ _ c z u e using D.iwasawa g
  simp [show ∀ h : G E 1, (g, h) = (D.radicalElt c z, 1) * (D.levi (t, u),
    h) * (κ⁻¹, 1) by simp [← e], -Prod.mk_mul_mk, -sourceTerm, -sourceTerm_zero,
    sourceTerm_radicalElt, sourceTerm_levi, mul_assoc]
  exact congr($(h0 _ (projOn_pairWeil hf (κ⁻¹, 1) (by simp [mem_Kf_iff.1 hκ.2]) ▸ by
    simpa [mixedTerm_zero] using
      ((isAdapted_homSource D V).omega_projOn_of_isMixedLaw isMixedLaw_mixedTerm 0 _).symm)) _)

/-- Let W' = W ⊕ ℍ^p (adapted), V definite, r = rk W, n = rk V > 2r + 2p + 3, w split, w̄ ∈ S,
a's base change unramified at w̄, Y automorphic, spherical at w, H_w(X)Y = 0, |X| =
q_w^{(r+2−2n)/2}. Then `DescentsVanish` for W, a implies it for W', aυ^p. -/
lemma descentsVanish_add_planes [IsBaseAdapted D] (hY : V.IsAutomorphic Y) {w} (hw :
  w.IsSplit) (ha : CharUnramifiedAt a.baseChange.finPart (star w))
  (hw' : star w ∈ S) (hK : Y ∈ sphericalAt (finRightRep ..) w) {X} (hX : ‖X‖ = (√w.q ^ card r *
  w.q ^ (card n - card r - 1))⁻¹) (hP : heckePolyOp (finRightRep ..) hw X Y = 0) (h : 2 * card
  r + 2 * card p + 3 < card n) : DescentsVanish W' V (a * upsilonU1 ^ card p) S Y := by
  induction' hl : card p with l ih generalizing m p <;> intro f hf <;> ext g
  rw [card_eq_zero_iff] at hl
  simpa [univ_eq_empty, mulVec_eq_sum] using! h0.integral_sourceTerm_eq_zero D hf g
  set χ := a * _
  let Θ := (pairThetaKer W' V χ 1).swap
  obtain _ := D.card_eq, (by simpa using pow_mul √w.q 2 · |>.symm)
  refine (Θ.exists_clm_lift hY.mem_rapidFunctions).elim fun L e ↦
    e .. ▸ ext_integrated _ hf fun P y _ ↦ e .. ▸ ?_
  set f := integrated _ (polyVector _ P) _
  replace hf : projOn _ S f = f := by simp +contextual [f, finHeisOp, finVec, *]
  obtain ⟨⟨C, A, h₀⟩, ⟨c, u⟩, ⟨D', _, -⟩, K, h₅, H⟩ := Θ.moderate_growth,
    V.exists_short_basis_matrix, exists_isBaseAdapted_stage D (equivOfCardEq (α := Unit ⊕ Fin l)
    (by simp; omega)), hecke_transfer_of_equivariant (k := card n - card m) (by omega) (a :=
    χ) (by simp_all [χ, charUnramifiedAt_upsilon ..]) (b := 1) (by simp) hw.star (f := f) (hf
    ▸ by simp [← projOn_union, hw']) Θ.liftBilin (.linHom 1 (finRightRep ..))
    (rapidFunctions.toRepresentation.linHom 1) fun g h ↦ by ext y; simpa [mul_assoc] using!
    (Θ.lift_equivariant (y.2.1.comp_mul_right h⁻¹) f h ..).symm
  rw [sphericalAt, maxCompactAt,
    Gf.supportedOn_star] at *; simp at H; lift Y to V.rapidFunctions.1 using hY.mem_rapidFunctions
  have J := heckePolyOp_adjoint hw («π» := V.rapidFunctions.toRepresentation) .applyₗ
    (Subtype.ext <| hK ·) h₅ (by simp) X
  rw [Submodule.coe_eq_zero.1 ((map_heckePolyOp (Submodule.subtype _) _).trans hP), map_zero, H,
    map_smul, map_heckePolyOp _ (π' := finRightRep ..) _] at J
  refine congr($(eq_zero_of_heckePolyOp_eq_zero hw (by apply congr($(K ·) Y))
    ((IsUnit.prod_iff.2 fun i ↦ isUnit_one_sub_of_norm_lt_one ∘ ?_).smul_eq_zero.1 J.symm) ?_ ?_) g)
  any_goals simp [*, field, ← pow_add, pow_lt_pow_iff_right₀, pow_le_pow_iff_right₀]; omega
  let ℓ := θ _ - θ _ ∘L (D'.homSource V).zeroTerm
  have cov {φ B} (h : ∀ b, ‖θ _ φ - θ _ (ϱ _ ((D'.homSource V).kAdelic *ᵥ b) φ)‖ ≤ B) : ‖ℓ φ‖ ≤
    B := by simpa [ℓ, quotMean, integral_sub, by simpa using ((D'.homSource
    V).isContPeriodic_along_k φ 0).integrable_out] using! norm_quotMean_le (_root_.ratVectors ..) h
  constructor; rintro _ ⟨g, ⟨⟩⟩
  choose! ξ h1 i e using W'.exists_short_isotropic
  choose! γ hγ using fun l ↦ W'.witt (.of_ne_zero (h1 l <| ext_col fun () ↦ ·)) ⟨_,
    D'.gram_lk⟩ (D'.gram_kk ▸ i l)
  have b := ae_of_all V.quotMeasure fun h ↦ norm_mul_le_of_le (by
    simpa only [height, (V.move h).firstMinimum_le_one.antisymm one_le_firstMinimum, pow_zero,
      mul_one] using (exists_norm_name_le χ 1 disjoint_bot_left (Ψ :=
      boxIndicator _ ⊥) (finHeisOp_mem_finitePart y vacElem_mem_finitePart) 0 A (C + C)
    c).choose_spec _ (W'.ratEmbed γ * g) h ℓ _ _ (weightedNorm_polyVector_ne_top _ P)
      (one_le_height ..) (W'.height_pos g) (fun _ ↦ cov fun b ↦ by grw (transparency :=
      .default) [varrho_pairWeil, norm_sub_le, Θ.swap.theta_rat_mul, h₀, Θ.swap.theta_rat_mul,
      h₀] <;> simp [Γ, add_mul]) fun l ↦ (u h).rec fun Y u ↦ ⟨_, _, _, _, u,
      fun j ↦ by simpa [baseLattice, ↓move_vecAtPoint, ← hγ l, ← replicateCol_mulVec, col_apply', ←
      mat_mul, ← ratEmbed_mulVec_vecAtPoint, archCoords] using e l j, le_rfl, .inr D'.gram_kk,
      fun z φ ↦ congr($(by simp [← vecAtPoint_hom]) - θ _ $(by simp [← zeroTerm_rho_kAdelic
      (matToVec (V.dualFrame.1 * V.coordMatrix 1 z)) φ, ↓homSource_kAdelic,
      -transpose_mul, Space.ratMap, W'.map_J])), .inr fun φ B H ↦ cov fun b ↦ by
    simpa [ℓ, ← (Y.1.map _).mul_assoc, ← zeroTerm_rho_kAdelic b (ω _ _ φ), ↓homSource_kAdelic,
      ← mat_mul, ← h.mat.mul_assoc, ↓mat_preserves_stdForm, pairWeil, ω_ϱ,
      ← mul_sub, -transpose_mul, -θ_apply] using H (matToVec (Y⁻¹.1.map toAdele * V.x.1 *
      V.dualFrame⁻¹.1 * vecToMat b))⟩) (Y.2.2.bounded.choose_spec h)
  refine (Θ.fixesLeft_lift _ ⟨γ, rfl⟩ g).symm.trans (sub_eq_zero.1 ((integral_sub
    (Θ.integrable_theta_mul Y.2 ..) (.of_bound (hY.rec (by simp; fun_prop)) _ b)).symm.trans ?_)) ▸
    norm_integral_le_of_norm_le_const b
  simpa +zetaDelta [mul_assoc, sub_mul] using! (ih (removePlanes ..) (by simp; omega)
    (by simp)).integral_sourceTerm_eq_zero D' hf _
