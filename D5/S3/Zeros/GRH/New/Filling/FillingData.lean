/- GID: D5/S3/Zeros/GRH/New/Filling/FillingData
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Filling/FillingData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Filling.FillingData. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Filling/FillingData.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.RealPlace.BandLimits
import D5.S3.Zeros.GRH.New.RealPlace.BesselCut
import D5.S3.Zeros.GRH.New.Exchange.SteepParameters
import D5.S3.Zeros.GRH.New.Filling.ColumnCoords
import D5.S3.Zeros.GRH.New.Rows.LineCoordinates
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Band limits, energy and open-cell bound for real-place Bessel integrals. At a real place,
integrals of a Bessel function on an indefinite unitary group against its translates have bounded
energy, Fourier transforms decaying beyond a band and a mean-square bound on the open cell, and they
replace Petersson's J-Bessel kernel in showing that few translates almost span the rows. Rank one is
classical and Bessel kernels are studied for GL(n) and GSp(4). Related work: Petersson, Über die
Entwicklungskoeffizienten der automorphen Formen, 1932; NIST DLMF §10.22; Baruch, Bessel
distributions on the open cell, 2001–2004; Comtat et al., Effective Kuznetsov trace formula for
GSp(4), 2025.

This file: A polynomial identity that splits a product of determinants (used in
New.Rows.Separation). Existence of a Bessel
system with tail, Schur and band bounds for the data. Builds the filling record from the global
data, with chosen Bessel systems. -/

open Matrix MvPolynomial Finset Filling MatrixOrder MeasureTheory Norms.L2Operator

/-- The product L of the determinants det(η; x), η from `Data.detRows`, equals ∑_l P_l·Q_l, with
P_l the polynomial `letterPoly` of the l-th basis vector in the positive letters of W_j and Q_l
from `Data.linePolyCoords`; columns of W_j are renamed by f, those of L⁺ by g. -/
lemma Data.stdClassSum_carrierXi_eq_lineMultiplier {P} {D : Data P} j i {n} (f g : _ → n) :
  renameRowsCols id (f ∘ D.basisVec ∘ (↑) ⊕ᵥ g) (stackedDetProd (posEquiv j) (detRows j i)) = ∑ l,
  renameRowsCols id f (letterPoly (D.signsW j) (untwistedAuxPair j).ord 1 _ (Pi.single l 1)) *
  renameRowsCols id g ((linePolyCoords j i) l) := by
  rw [(?_ : renameRowsCols .. = (aevalTower (renameRowsCols id g) (renameRowsCols id f <|
    fockLetters _ _ 1 <| .X ·)).comp inFirstCols)]
  simpa [← toPoly_linePolyCoords, toPoly, letterPoly, entrywise, nablaBasis, tableauPoly, minor,
    smul_eq_C_mul, AlgHom.map_det, Matrix.map,
    Fintype.linearCombination_apply, sum_mul, mul_right_comm _ (rename _ _)] using! sum_comm
  ext1 ⟨τ, a, s | s⟩ <;> simp [inFirstCols, fockLetters, auxPair]
  rw [sum_eq_single] <;> grind [basisVec, D.basisNumber.eq_symm_apply, signsW]

attribute [local simp] ConjAct.units_smul_def

variable {P} (D : Data P)

lemma Data.card_X₀ : Fintype.card (D.X 0) = D.k := by grind [card_X, n]

/-- An orthonormal frame with the signs of Y₀ (`Data.signsY` 0). -/
noncomputable instance Data.unitarySignFrameY : Frame _ (D.signsY 0 ·) := Nonempty.some <|
  have ⟨_, a, b⟩ := exists_frame_gradedGram D.shape.besselIndexEquiv (.id ℂ) one_pos
    ((D.card_neg_gridSigns false 0 0).trans (by grind)); ⟨@.mk _ _
    ⟨(.mkOfMulEqOne _ _ (b rfl))⁻¹, by convert! a; simp [← ext_iff, gradedGram,
    Shape.besselIndexEquiv, splitGram, middleGram, Fin.rev]; lia⟩ ⟨b rfl, Units.inv_mul _⟩⟩

/-- For every infinite place v there is a Bessel system on G₁ with the formal degree and the
reproducing property of the parameter ς(v) (doubled: `Data.paramW` v) and the U(X₀)-type with column
numbers `Data.κ` v, in the sense of `Filling.IsBessel`.

Real-place Bessel integrals: band limits, energy and open-cell bound. -/
lemma Data.exists_besselSystem v : ∃ B : BesselSystem _ D.b D.f,
  IsBessel B (D.paramW v) (D.κ v) := by
  let w (_ : Unit) := D.κ v
  obtain ⟨ck : Fintype.card D.shape.κ = _, _, _ : D.k ≤ D.a, b1 : 1 ≤ D.b, u, h⟩ := D.card_X₀,
    @isHermInvolution_J₁ D.shape, D.nat_le_of_hasLogBound, D.le_of_hasLogBound,
    Exists.intro _ (isHCParam_hcParameter D.shape.κ w 0)
  have hL i : |D.paramW v i| ≤ ↑(3 * D.a) :=
    (D.abs_gridParam_le (z := false) v bot_le bot_le i).trans (mod_cast D.nat_le_of_hasLogBound)
  obtain ⟨hg : HCParam.HasLargeGap _ (D.r ^ 7), i, _⟩ := (D.hasGap_signsY_paramW v).mono
    D.le_of_hasLogBound, h.exists_decrPosition_eq () Fintype.card_pos
  have L j : (toHCParam 1 (u ())).lowestKType j = ite (j = i) (D.κ v 1) 0 ∧ |u () j| ≤
    ↑(3 * D.a) := by have := h.eq_hcParameter () j; rw [h.lowestKType_eq, hcParameter,
    diagramWeight_apply, sum_eq_ite 1, Pi.zero_apply] at * <;> grind [κ, (h ()).1, decrPosition]
  obtain ⟨d1, ⟨p, q⟩, ⟨_, ⟨B, rfl⟩, hG⟩, K, ⟨dq⟩, _, _, x, hR, T⟩ := _root_.formalDegree_pos hg,
    exists_equiv_decrPosition (h ()).1,
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.1 (weylGram_posDef.isStrictlyPositive
    (n := WeylIndex D.shape.κ w)), isIdempotentKernel_psiInFrame (p := D.unitarySignFrameY.1) hg,
    Orbital.harish_chandra_degree_and_orbital (hg.mono D.le_of_hasLogBound),
    D.shape.besselGraphMeasure_isMulRightInvariant, D.shape.besselGraphMeasure_finiteOnCompacts,
    ((D.exists_isSteep false).choose_spec v).exists_isTwoFactor_besselPairHom (b :=
    D.b) (.swap (.inr ()) i) (by simpa using (L · |>.1)) D.le_of_hasLogBound
    (by grw [show D.κ .. ≤ D.a by grind [κ]]; use D.le_of_hasLogBound) D.le_of_hasLogBound
  let φ := MulSemiringAction.toAlgEquiv ℂ (type_of% B.1) (ConjAct.toConjAct B)
  -- `rep` is Sym^(κ v 1) in an orthonormal basis for the Gram form
  let rep : U (1 : Matrix D.shape.κ _ ℂ) →* unitaryGroup _ ℂ := .mk' (fun h ↦ ⟨φ (schur w fun _ ↦
    h), by simpa [mem_unitaryGroup_iff', φ, hG, star, ← U.inv_val_eq_conjTranspose,
    conjTranspose_nonsing_inv, mul_assoc]
    using congr(B.1ᴴ⁻¹ * $(PolyRep.schur_conjTranspose_weylGram_schur .refl (κ := w) (fun _ ↦ h.1.1)
             fun _ ↦ h) * B⁻¹)⟩) (by simp [schur_mul_left])
  obtain ⟨Y, hS⟩ := exists_isBesselFunction (rep := rep) (by simp [rep, φ]; fun_prop) (v :=
    .toLp ..) (fun k ↦ (dotProduct_comm (_ *ᵥ B.1 *ᵥ highestVector w u) (star (_ *ᵥ _))).trans (by
    simpa [weylRep, hG, q, rep, φ, ↓star_mulVec, ↓star_highestVector, highestVector,
      dotProduct_mulVec, mul_assoc, dsCoeff_of_mem_maxCompactU (h.hasGap () 0) (k := ⟨k, _⟩) k.2,
      _root_.funext (h.lowestKType_eq _)] using! weylRep_coeff_eq_prod_weightMinors (κ := w) (e :=
      0) (fun _ ↦ p) _)) hg D.le_of_hasLogBound (T.laplace_method (β := D.b ^ 3) _ hg (h.hasGap ..)
    D.le_of_hasLogBound hL (L · |>.2) D.le_of_hasLogBound (ck ▸ D.le_of_hasLogBound) (ck ▸
    D.le_of_hasLogBound) (isProperMap_fst_besselPairHom x) (.subtype_mk (by simp; fun_prop) _) fun s
    _ ↦ (CStarRing.norm_of_mem_unitary (U_one_mem_unitaryGroup s.1.2)).trans_le D.le_of_hasLogBound)
  obtain ⟨F, V, fx, t⟩ := (pow_mul D.b .. ▸ hS).exists_cut_isCutPair hg hL D.f hR
    D.le_of_hasLogBound (ck ▸ D.nat_le_of_hasLogBound) D.le_of_hasLogBound D.nat_le_of_hasLogBound
  have s := t.isBesselFunction .full
  have k B := t.lintegral_sq_full_eq ▸ s.hasSchurBound_of_convolve_eq hg hL t.integrable B fx
  use ⟨_, _, _, d1, _, t, fun M H ↦ (scalar_of_commute_schur fun g a ↦ by
    simpa [rep] using! (H (U.of isUnit_one (g ()) (by simp [a]))).map φ.symm).imp (φ.commutes · ▸
    φ.eq_symm_apply.1 ·), (k · ∘ D.le_of_hasLogBound.trans), D.le_of_hasLogBound, _,
    (hasBandLimits_of_isCutBessel ⟨t, rfl, D.le_of_hasLogBound.trans (le_self_pow₀ b1 nofun),
    (Nat.sub_add_cancel (m := _ + 2) (ck.ge.trans' D.nat_le_of_hasLogBound)).symm,
    lt_tsub_iff_right.2 (ck.ge.trans_lt' D.nat_lt_of_hasLogBound),
    ck.ge.trans' D.nat_le_of_hasLogBound, D.nat_le_of_hasLogBound, D.le_of_hasLogBound⟩ d1 ((k _
    le_rfl).elim fun _ j ↦ by simpa [j] using (j.2 []).2.2) ?_).choose_spec⟩, dq, ⟨star B, (star
    B)⁻¹.1, by simp [s.3, rep, φ, w, ← mul_assoc, hG ▸ weylGram_mul_schur _, ← star_mul]⟩,
    fun y i ↦ by simpa [← integral_comp_frameEquiv (p := D.unitarySignFrameY.1), K.3] using!
    (eval_integral_piLp (s.integrable_smul K.2.comp_inv y).eval_piLp i).symm.trans congr($fx y i)
  rify at hL
  simp [-prod_mul_distrib, Shape.bandConst, dq, volU, ↓card_rowIndex, ck]; rw [weylDimensionPoly,
    card_rowIndex]; field_simp
  grw [le_abs_self (∏ _, _), abs_prod, (abs_prod ..).le, (abs_div ..).le, abs_sub, hL, hL, abs_two,
    (D.le_of_hasLogBound : _ / 2 ≤ D.b ^ 3), filter_subset, ← Nat.factorial_le bot_le,
    (D.nat_le_of_hasLogBound : _ * _ ≤ D.r ^ 2), k_le_r]
  simp [field, ↓card_rowIndex]
  grw [(D.le_of_hasLogBound : .pi ≤ D.b)]
  ring_nf
  repeat bound [Real.two_le_pi]

variable {P : _} (D : Data P)

instance Data.instLbHPowRealNatOfNatϱHMulLb : D.HasLogLower (ofNat(2) ^ D.ϱ) (10 * D.logB) := ⟨by
  simp [← Real.le_log_iff_exp_le]; grw [← Real.log_two_gt_d9]; norm_num; use D.le_of_hasLogBound⟩

/-- The filling data `Filling` attached to the admissible data D: its level N with π̄, primes
g₀, g₁ with chosen places, ϖ, and Bessel systems chosen from `Data.exists_besselSystem`. -/
noncomputable def Data.filling := by refine' (Filling.mk (fintypeChosen := _) _ _ D.piIdele _ _ _ _
  D.classAut_columnLevel_eq_bot (D.exists_besselSystem · |>.choose) (mod_cast D.piIdele_spec.1.symm)
  D.N_prime (by grind [D.piIdele_spec.2, D.isSplitLevel_piPlaces.q_eq]) (coe_mem_Ô _) (⟨D.g_prime ·,
  D.nat_lt_of_hasLogBound.ne⟩) (D.g_mem · |>.1) (D.g_mem · |>.2)
  (@q_eq_g _ D · · ·.2) D.isConjApart_chosen.1 (IsChosen.not_star ·.1 ·.1) (fun r ↦ by
       refine .trans ?_ (.trans (forall_congr' fun i ↦ (dvd_iff_reduceAt_eq_zero
         (Parameters.intValuation_p · (Parameters.not_dvd_N₁_mul_d_of_modEq_one (D.g_modEq_one i)))
         r).trans ?_) Sigma.forall.symm) <;> simp
       use (by grw [← ·]; simp),
         And.elim (Nat.Coprime.cast (by grind [Nat.coprime_primes, Data])).mul_dvd
       use fun h a ⟨_, k⟩ ↦ ⟨h a k, h _ (by simpa)⟩, fun h w k ↦ by_cases (h w ⟨·, k⟩ |>.1) fun n ↦
         star_star w ▸ (h _ ⟨(D.isChosen_star_iff k).2 n, by simpa⟩).2) D.card_chosenPlace P.star_ϖ
  P.different_eq_span_varpi ..) <;> and_intros <;> (try rify [Shape.k, card_X₀,
  finrank_eq_two_mul_card_infinitePlace, inv_pow, pow_mul']) <;> use D.le_of_hasLogBound

/-- The level group `Data.columnLevel` on X₀ is the preimage of the principal congruence subgroup
K(g) under the embedding of the finite adelic points of U(X₀) in those of U(Y₀). -/
lemma Data.columnLevel_zero_eq_comap : D.columnLevel 0 =
  D.filling.principalLevel.comap D.filling.inclHFin := by
  ext; simp [columnLevel, Filling.principalLevel, _root_.funext_iff,
    D.filling.reduction_inclHFin_eq_one_iff, levelOf, Sigma.forall,
    D.filling.inclHFin_mem_latStabilizer, -Subtype.forall]
  use by tauto, fun ⟨c, b⟩ ↦ ⟨⟨c.1, b⟩, c⟩
