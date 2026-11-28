/- GID: D5/S3/Zeros/GRH/New/Rows/Separation
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Rows/Separation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Rows.Separation. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/Separation.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Rows.NaturalFormNear
import D5.S3.Zeros.GRH.New.Exchange.AlgebraicPartConjugates
import D5.S3.Zeros.GRH.New.Filling.DegreeBounds
import D5.S3.Zeros.GRH.New.Rows.MonomialCoefficientVector
import D5.S3.Zeros.GRH.New.Selmer.HeckeStableSubspaces
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Products of theta forms detect all good forms. For a finite family of choices with small
integral data, a good form on U(W_j) orthogonal to all products of the twist-free theta forms with
theta kernels of the complementary block is zero, and this non-degeneracy of the comparison forms is
needed to cancel the volumes of lifts. It is known that stable-range theta kernels reach all forms,
that maxima of forms avoid the cusps and that products span for GL(2). Related work: J.-S. Li,
Non-vanishing theorems for the cohomology of certain arithmetic quotients, 1992; Poor–Yuen, Linear
dependence among Siegel modular forms, 2000; Khuri-Makdisi, Moduli interpretation of Eisenstein
series, 2012.

Part of: Twisted theta forms lie on one line (see New.Rows.LineArithmetic).

This file: The main result `Data.eq_zero_of_integral_fNatural_tableTheta`. Hodge–Tate jumps of the
data lie in low or high windows. The three character
pairs and the product of Hecke value ratios. Untwisted Hecke value is large against parallel weight,
giving negative height. One twist-free form is a multiple, possibly zero here, of each twisted theta
form, with L-value
ratio. Level and holomorphic weight of the twist-free theta form. -/
seal Finset.univ Finset.sum Finset.prod

open NumberField Multiset Data Int Fintype Real WeilData Data.Pair Additive Function Matrix Sum
variable {P} {D : Data P}

@[simp] lemma cmSign_star σ : @cmSign D.E _ _ (star σ) = -cmSign σ := by
  grind [cmSign, neg_neg, Φ_eq_or, InfinitePlace.mk_eq_iff]

/-- For 1 ≤ j ≤ m, the multisets of the r integers ⌊t/2⌋ − sgn(σ)(ς_q + w_j), 0 ≤ q < r, at the
embeddings σ satisfy the jump conditions `IsRowType` for (r, t); sgn is 1 on the CM
type, else −1. -/
lemma isRowType_auxPair {j} (hj : j ∈ D.LiftIndex) : IsRowType D D.r D.t fun σ ↦ (Multiset.range
  D.r).map fun q ↦ D.t / 2 - cmSign σ * (D.rowParameter (.mk σ) q + D.w j (.mk σ)) := by
  use ⟨D.nat_le_of_hasLogBound, .refl⟩, .refl, ⟨j, hj.2, by simpa using fun σ p _ ↦ by grind
    [rowParameter, units_natAbs, (mul_le_mul_left (by grind : p + 2 - D.k + j < D.t) D.h).trans
    (D.nat_le_of_hasLogBound (B := D.h₂ ^ 2))]⟩, fun σ ↦ (mul_le_mul' (?_ : _ ≤ D.r + 1 - D.k)
    D.k_le_r).trans (by grind), fun σ ↦ ?_ <;> induction D.r <;> simp_all [countP_cons] <;> grind
    [rowParameter, units_natAbs, !(D.nat_lt_of_hasLogBound : 2 * D.h₂ ^ 2 + D.h₂ < D.w _ _)]

/-- For a sign s, the number e_s: e₊ = m and e₋ = ⌊m/2⌋. -/
def Data.eSign {P} (D : Data P) (s : ℤˣ) := ite (s = 1) D.m (D.m / 2)

/-- The natural number 𝖾 = ⌊(k + 7m)/2⌋, the point z of the pair `Data.linePair` j none. -/
def Data.heckeCount {P} (D : Data P) := 7 * (D.m / 2) + D.k / 2

/-- Three pairs (ν, z) for 1 ≤ j ≤ m: (μ_j⁰υ^{j+⌊(t−11m−1)/2⌋}, ⌊(k+7m)/2⌋) at none, and
(υ^{−e_s}χ^{sj}, e_s) at a sign s, with e₊ = m, e₋ = ⌊m/2⌋. -/
noncomputable def Data.linePair {P : Parameters} {D : Data P} (j : D.LiftIndex) : Option ℤˣ →
  D.Pair := by
  let n := j + (D.t - 11 * D.m - 1) / 2
  refine' Option.rec (.mk _ (D.w j · - n) _ D.heckeCount (((D.mu₀_hasWeight j).mul_upsilonU1_pow
    n).of_weight_eq _) ..) fun s ↦ ⟨_ * _ ^ (s.1 * j), fun _ ↦ D.eSign s, _, D.eSign s, by
    simpa using! (WeilData.hasWeight_upsilonU1_pow _).inv.mul (D.chi_hasWeight.zpow _), _, _, _, _⟩
  any_goals refine' fun v ↦ .trans (b := (D.w j v : ℝ)) (Nat.mono_cast _) _
  all_goals grind [heckeCount, eSign, omega_eq_one_of_not_isChosen, _root_.one_zpow, Pi.pow_apply,
    w_le_two_mul_b]

/-- The product, over the three pairs (ν, z) of `Data.linePair`, of `lValueProd`((νϑ^{±1})⁻¹, z)
off the chosen places and Q; the exponent is −1 only for the sign −1. -/
noncomputable def Data.heckeValueProd {P} {D : Data P} (j : D.LiftIndex) (ϑ : D.Twist) := ∏ i,
    (lValueProd ({w | D.IsChosen w} ∪ ϑ.Q) ((linePair j i).ν * ϑ.toAutChar ^ (i.getD 1).1)⁻¹
  (linePair j i).z : ℂ)

namespace Data

variable {P : _} {D : Data P}

/-- Let n have even size 2z, 4 ≤ 2z ≤ t. A weight-0 character χ of U(1)(𝔸), tame at the chosen
places, equals ν·υ^z for a pair (ν, z) of parallel weight −z with the same tame part. -/
lemma exists_isFlat n [Fintype n] (hn : 4 ≤ Fintype.card n ∧ Fintype.card n ≤
  D.t ∧ 2 ∣ Fintype.card n := by simp; grind) (χ : AutChar.tameChars D.finite_isChosen.toFinset) :
  ∃ p : D.Pair, (rankTwist p.ν n = χ.1.1 ∧ p.ψ = χ.1.2) ∧ p.IsFlat n := ⟨⟨_, _, _, Fintype.card
  n / 2, by simpa using! χ.2.1.mul (hasWeight_upsilonU1_pow _).inv, by simp_all [χ.2.2], by
    grind -zetaDelta -abstractProof, fun _ ↦ le_rfl, fun _ ↦
  .trans (mod_cast by lia -zetaDelta -abstractProof) (D.le_of_hasLogBound : ↑D.t ≤ _)⟩, by simp [rankTwist]; lia -zetaDelta -abstractProof⟩

/-- For a pair p of rank one for j (`Data.Pair.IsRankOne`), the squared norm of the untwisted form
`Data.Pair.trivialLift`, as a constant family, has height (`HeightLe`) at most B₀ − ∑_τ st(w₀(τ)),
st = `Data.jetSize`. -/
lemma heightLe_norm_trivialLift_sq {j p} (H : @IsRankOne P D p j) :
    HeightLe (D.B₀ - ∑ τ, D.jetSize (D.w 0 τ)) fun _ ↦ ‖trivialLift H.1 .one‖ ^ 2 := by
  obtain ⟨q, -, h⟩ := D.exists_isFlat (RankOneIndex p.z) (by grind [IsRankOne]) 1
  refine ⟨q.intAlgPart h.2 .one / ‖trivialLift H.1 .one‖ ^ 2, _, 0, by simp,
    (P.exists_algEquiv_norm_eq · |>.elim fun σ e ↦
    (log_norm_map_norm_sq_trivialLift D (RankOneIndex p.z) σ).elim fun _ k ↦
    le_exp_of_log_le ?_), by simp [(isIntegralMeasure_intAlgPart ..).norm_apply_one_le], by aesop⟩
  obtain - := k, k _ h.2, k _ H.1, sum_mono fun τ ↦ D.jetSize_le_add
    (by cases j <;> grind [IsRankOne] : D.w 0 τ ≤ p.c τ - p.z + 0)
  simp [h, Pair.intAlgPart, twist_one_spec, denomBound, log_mul, log_div, NeZero.ne, jetSize] at *
  rename_i a b _; obtain ⟨⟨_, _, _, _⟩, _, _, -, _⟩ := And.intro a b; simp only [e]
  linarith [(D.le_of_hasLogBound :
    Real.log D.chosenGroupOrder + D.f * (8 * q.z * Real.log D.gProd + 8) ≤ D.B₀)]

end Data

attribute [local simp] Data.regroupEquiv Data.negIndex Data.detRows

/-- For 1 ≤ j ≤ m there are C (not shown non-zero here) and numbers c_ϑ with |c_ϑ|² = C /
`Data.heckeValueProd`(ϑ) such that
c_ϑ times `cosetKernelSum`, for w and the vectors `Data.lineMultiplier` of the choice i, equals F♮_i
(`Data.fNatural`) whenever the matrix of i is uw for some u.

Twisted theta forms lie on one line. -/
lemma Data.cosetKernelSum_eq_fNatural {P} {D : Data P} {a} [Fintype a] j : ∃ C, ∃ c : D.Twist → ℂ,
  ∀ ϑ, ‖c ϑ‖ ^ 2 = C / heckeValueProd j ϑ ∧ ∀ (u : Matrix _ a (D.untwistedModulus 2).ResRing) i g
  (w : Matrix a _ (D.untwistedModulus 2).ResRing), u * w = i.1 → fNatural j i g = c ϑ *
  cosetKernelSum (D.auxPair ϑ j) (bigChar ϑ j) w (.trans .inl .inl) (lineMultiplier ϑ j i) g := by
  have' hs : _ = blockSigns (.ofBijective (regroupEquiv j ∘ Sum.map (D.basisVec ∘ Fin.val (n :=
    D.posRank j)) inr ⊕ᵥ inr ∘ inl ∘ negIndex j) _) := _
  have e ϑ : bigChar ϑ j * WeilData.upsilonU1 ^ D.m = twistedChi ϑ j * carrierChar j := ?_
  have' := (explicit_matching _ (.refl _) · 1 (posEquiv j) _ hs _ _ (DetIndex j))
  choose _ _ _ hK using this
  choose _ _ _ hM using stdClassSum_carrierXi_eq_carrierForm D.E D.m_even
  repeat constructor
  refine fun ϑ ↦ let hν := (isTameFor_twistedChi j ϑ).mul (carrierChar_hasWeight ..); .symm ⟨fun u i
      g w H ↦ .symm (.trans ?_ (explicit_matching_of_sum _ _ hν (hM (isTameFor_twistedChi j _))
      (D.untwistedModulus 2) levelModulus_ideal_le _ fun _ _ h _ ↦ (hK _ hν
      (by simp [← card_detIndex_add_bigCharExp j]) (detRows j i.2) h (bigChar ϑ j) _ :).trans (by
    congr! <;> simp [← e, matchedPoly, pairedDetProd, letterMinor, ← mul_assoc, linePoly,
      prod_sigma, AlgHom.map_det, Matrix.map, ← Finset.prod_mul_distrib]
    congr! 4; omega; rw [← Fin.prod_const]; congr!
    repeat ext; simp [entrywise, inclMatrix, posRowIndex] <;> split <;> rfl))), ?_⟩
  simp_rw [@classSum_comm (Gf _ (BigIndex j)), ← mul_classSum]
  refine congrArg _ (.trans ?_ congr(stdClassSum _ fun _ ↦ _ * $(stdClassSum_rowStabilizer_eq hν (by
    rw [hs]; simpa [-regroupEquiv] using! realPairWeil_stackedDetProd _ _
      (funext (by simp [← card_detIndex_add_bigCharExp j])) (detRows j i.2) 1) (forgetTwist _) w
    (.trans .inl .inl) (F := fun y ↦ ∑ k : GL _ _, traceChar i.1 (y.map (forgetTwist _) * k.1))
    fun A a ↦ by simp [traceChar, Matrix.mul_assoc, trace_mul_comm (A.1.map _), ← H, a.2])))
  simp_rw [mul_classSum, @classSum_comm (Gf _ D.CarrierIndex), ← e,
    cosetKernelSum]; congr with h; clear * -
  change modKernelBilin (D.spaceW j) _ _ _ _ _ _ (columnDatum _ (forgetTwist _) _ _) (letterPoly _
    _ 1 (untwistedAuxPair j).colsPlus _) = _
  rw [pi_eq_sum_univ' (lineMultiplier ϑ j i h)]; symm
  simp [lineMultiplier, modKernelI, mul_classSum, ← classSum_sum, mul_left_comm (modKernel ..),
    mul_assoc, -mul_ite, ← Finset.mul_sum, mul_comm (modKernel (.sum ..) ..),
    ← modKernel_sum_left, -regroupEquiv]; congr!
  erw [← modKernel_reindex (regroupEquiv ..).symm ?_ (.refl _) rfl,
    ← map_sum ((modKernelBilin ..) _), modKernelBilin_apply]; congr! -closePost 1; rfl
  ext1; simp [GeneralLinearGroup.ext_iff, Space.reindex, Space.sum]
  rfl; grind [pow_sub_mul_pow, card_neg_signsW, auxPair]
  congr! 2; simp [lPlusDatum, ← ite_and]; congr
  simp [entrywise, inclMatrix, forall_and, -sum_sum_type]; tauto
  simpa [Prod.map_comp_map, ← comp_assoc, -regroupEquiv] using!
    stdClassSum_carrierXi_eq_lineMultiplier j _ inl (inr ∘ inr)
  apply G.ext_mat; simp [entrywise, Prod.ext_iff, funext_iff, U.sum]; iterate 3 aesop
  simp [← Complex.ofReal_pow, mul_pow, div_pow, heckeValueProd, places_modulus_eq_union, *,
    linePair, eSign, ← division_def,
    div_right_comm _ (_ * _), div_mul_div_comm]; with_reducible congr
  any_goals clear * -; apply_fun ofMul; simp [bigChar, liftChar, twistedChi, carrierChar, μ₀];
            match_scalars <;> grind [heckeCount]
  all_goals simp [↓card_rowIndex, ↓bijective_iff_injective_and_card, Injective, signsW, funext_iff,
    ↓Equiv.eq_comp_symm, apply_dite (padSigns j), basisVec]; grind [Equiv.injective, heckeCount]

unseal Finset.univ Finset.prod

namespace Data

variable {P : _} {D : Data P} {j : D.LiftIndex} (F : D.goodForms (D.spaceW j))

lemma goodForms_mem_rapidOfLevel {a} (d : D.piGBar ∣ a := by simp) :
  F.1.1.1 ∈ rapidOfLevel (D.spaceW j) a := ⟨F.1.1.2.mem_rapidFunctions D.isCuspKernel_paramW,
  (funext <| Space.mem_levelSpace_formRep_iff.1 F.1.2 _ <| D.principalLevel_le_chosenLevel d ·.2)⟩

/-- For a good form F on U(W_j), F·F♮_i is rapidly decreasing of level π̄² (π̄ = `Data.piGBar`), and
F♮_i = `Data.fNatural` is holomorphic of weight `conjHolWeight` − `kernelWeight`. -/
lemma mul_fNatural_mem_rapidOfLevel_and_hol i : F * fNatural j i ∈ rapidOfLevel (D.spaceW j)
  (D.piGBar ^ 2) ∧ IsAdelicHol (orderW j) (conjHolWeight j - kernelWeight j) (fNatural j i) := by
  choose _ _ _ e using cosetKernelSum_eq_fNatural (a := D.CarrierIndex) j
  simpa only [Pi.sub_def, conjHolWeight_eq_add_kernelWeight, add_sub_cancel_right, funext
    (e 1 1 i · _ i.1.one_mul), cosetKernelSum, classSum, finsum_eq_sum_of_fintype, Rat.smul_def,
    Finset.mul_sum, ← mul_assoc] using have G := D.fitsParams_auxPair ..; ⟨mul_sum_mem_rapidOfLevel
      fun _ ↦ mul_modKernel_mem_rapidOfLevel D.ideal_untwistedModulus_eq_span
    (goodForms_mem_rapidOfLevel F) _ _ _ ((auxPair ..).tame_eq_one · <|
      places_levelModulus.ge.mt ·), (.sum _ fun _ ↦ isAdelicHol_pairTheta
    (mem_holomorphicData_of_highestVector (e' := 0) (_ ∘ₗ _) (by simp [Injective, Fin.val_inj]) (by
      intros; erw [realPairWeil_fockLetters, star_mulVec]; simp [letterPoly, weylRep,
        ← mulVec_transpose, comp_def, conjTranspose_transpose])
      (letterPoly_highestVector_holomorphic isPosFirstOrder_orderW (paramW_lt_of_orderW_lt 1)
      (G.paramsCorrespond 1).2.1 (G.ord_eq 1) _ G.colsPlus_eq_zero).2) ·)⟩

end Data

open ComplexConjugate AuxPair Parameters

/-- On U(W_j), the sum over classes c of level ϖ² of the conjugate (W_j, V°) kernel at (g, c):
datum 1_inc mod ϖ², polynomial of conj ζ(c) in negative letters. -/
noncomputable def Data.tableTheta {P} {D : Data P} (j : D.LiftIndex) (ζ : D.SmallClasses → _) g :=
  ∑ c, conj (modKernelI (D.spaceW j) (untwistedAuxPair j).a (upsilonU1 ^ (D.m / 2 - j : ℤ))
  (D.untwistedModulus 2) (Pi.single (inclMatrix _ .inl) 1) (letterPoly (D.signsW j)
  (untwistedAuxPair j).ord (-1) (untwistedAuxPair j).colsMinus (star (ζ c))) g c.out)

/-- For 1 ≤ j ≤ m, a good form F on U(W_j) vanishes if ∫ conj(F·F♮_i)·θo(ζ) = 0 over [U(W_j)] for
all choices i and all ζ, where F♮ = `Data.fNatural` and θo = `Data.tableTheta`.

Products of theta forms detect all good forms. -/
lemma Data.eq_zero_of_integral_fNatural_tableTheta {P} {D : Data P} {j : D.LiftIndex} (F :
  D.goodForms (D.spaceW j)) (h : ∀ i ζ, ∫ g, conj (F.1.1 g * fNatural j i g) * tableTheta j ζ
  g ∂(D.spaceW j).quotMeasure = 0) : F = 0 := by
  obtain ⟨o, N, G, _, _, _, ε, C, M⟩ := @isPosFirstOrder_orderW _ D j, rank_bounds_card_bigIndex j,
    D.fitsParams_auxPair _ j, exists_fNatural_approx j
  have H : IsAdelicHol (orderW j) (conjHolWeight j) (star <| F.1.1 ·) := by
    obtain ⟨⟨_, e'⟩, _, J, k, _⟩ := (_ ∘ₗ _).surjective_of_injective
      ((LinearMap.self_comp_adjoint_injective_iff _).2 (D.auxLift_injective .one)) F.1,
      G.exists_isJointHarmonic
    erw [← e', (exists_theta_to_principalForms ..).choose_spec j.2]
    simpa [θ, AuxPair.conjKernel, classSum, Rat.smul_def] using! (.sum _ fun _ ↦
      isAdelicHol_pairTheta (mem_holomorphicData_of_highestVector (_ ∘ₗ _) (J · |>.gap.1)
      (realPairWeil_harmonicPoly _) (congr(polyVector _
      $k).substr (prod_mem_holomorphicData o paramW_lt_of_orderW_lt (J · |>.2) rfl).2)) ·)
  choose w6 w3 w2 w5 w4 using conjHolWeight_kernelWeight_bounds j
  choose lG hG using mul_fNatural_mem_rapidOfLevel_and_hol F
  repeat apply Subtype.ext
  refine star_eq_zero.1 (by_contra (exists_near_max _ _ o (by grind only [HasHolGap, nStar_bounds])
    w6 D.le_of_hasLogBound D.le_of_hasLogBound (by simp [star_sqrtNegDInE]) (by simpa [NeZero.pos]
    using D.le_of_hasLogBound) (star_mem_rapidOfLevel (goodForms_mem_rapidOfLevel F (.mul_right ⟨_,
    D.piGBar_mul_star.symm⟩ (sqrtNegDInE ..)))) H · |> fun ⟨g, g0, g2, hl⟩ ↦
    ε.not_ge (isolation (by bound) D.le_of_hasLogBound D.le_of_hasLogBound o w2
    w3 w4 w5 w6 F.1.1.2.continuous.star H g0 g2 C fun I z a ↦ ⟨_, .sum _ (hG · _), (M _ (hl _
    a)).choose_spec, ((reproducing_formula_modKernel o D.ideal_untwistedModulus_eq_span
    nonempty_modulus_places _ (hasWeight_upsilonU1_pow _) (hasWeight_upsilonU1_zpow _) w2 I
    (by simp [N]; omega) .inl (letterPoly_highestVector_holomorphic o (paramW_lt_of_orderW_lt 1)
    (G.paramsCorrespond 1).2.1 (G.ord_eq 1) _ G.colsMinus_eq_zero) (fun _ ↦ fockLetters (D.signsW j)
    (untwistedAuxPair j).ord (-1) ∘ nablaBasis ℂ _ (untwistedAuxPair j).colsMinus)
    (by intros; erw [realPairWeil_fockLetters]; clear * -; aesop (add safe sum_mem,
    simp [toPoly, linearCombination_apply])) z).choose_spec _ (star_star F.1.1.1 ▸
    mul_sum_mem_rapidOfLevel lG :)).trans (Fintype.sum_eq_zero _ fun c ↦ ?_)⟩)))
  simp [mul_assoc, Finset.sum_mul]
  refine .inr ((integral_mul_sum_const_mul fun i ↦ (mul_assoc ..).subst
    (mul_modKernel_mem_rapidOfLevel D.ideal_untwistedModulus_eq_span (lG i) ..)).trans
    (Fintype.sum_eq_zero _ fun i ↦ mul_eq_zero_of_right _ ?_))
  let ⟨v, e'⟩ := range_toPoly.ge (prod_tableauPoly_mem_nabla : nablaBasis ℂ _ _ c.2 ∈ _)
  simpa [tableTheta, ← integral_conj, ← modKernelBilin_apply, apply_ite, letterPoly, e', mul_assoc,
    nablaBasis] using! congr(conj $(h i (Pi.single c.1 (star v))))
