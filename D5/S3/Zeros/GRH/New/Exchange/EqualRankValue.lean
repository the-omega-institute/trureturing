/- GID: D5/S3/Zeros/GRH/New/Exchange/EqualRankValue
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/EqualRankValue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.EqualRankValue. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/EqualRankValue.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.Flip
import D5.S3.Zeros.GRH.New.Exchange.SquareLawFourier
import D5.S3.Zeros.GRH.New.Exchange.RealPair
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Exchange theorem for theta integrals of complementary rank (see
New.Exchange.ExchangeTheorem).

This file: Removing hyperbolic planes from both sides preserves the exchange identity. Exchange
identity for all partners, constant known up to the equal-rank constant lambda. Modulus of the
equal-rank theta constant is a nonzero multiple of Hecke L-values. -/

section

open Matrix Fintype Space Splitting MeasureTheory MatMul MixedModel
variable {E} [Field E] [CMType E] [WeilData E] {n n' r r' p b} [Fintype n] [Fintype n'] [Fintype r]
  [Fintype r'] [Fintype p] [Fintype b] {s s' t t' u} {W : Space E n s} {W' : Space E n' s'} (U :
  Space E b u) (V' : Space E r' t') (A : W'.Splitting W p) (B : W.Splitting V' r) [IsBaseAdapted A]

attribute [-simp] θ_apply Matrix.smul_apply card_unique card_punit

variable (p W) in
/-- If t is a sign vector of length rk W + 2|p| with |p| more negative signs than W, then some
space W′ of signs t has an adapted splitting over W with |p| hyperbolic planes. -/
lemma exists_isBaseAdapted t (h : card r = card n + 2 * card p) (h' : negCount t =
  card p + negCount s) : ∃ (W' : Space E r t) (A : W'.Splitting W p), IsBaseAdapted A :=
  (exists_equiv_of_card_neg (by simpa +arith) (by simpa)).rec fun ε hε ↦ ⟨(hypSum p W).reindex
  ε.symm hε, splittingOfGram (submatrix 1 ε id) (by simp) h, ⟨.of_eq_submatrix_mul .one ε.symm
  (IsBaseAdapted.isOrthoIntegral (D := removePlanes p W)) (by simp [entrywise, lAdelic, kAdelic,
  iAdelic, Space.ratMap, removePlanes, splittingOfGram, Space.reindex, reindex_equiv ε.symm])⟩⟩

lemma slice_zero_congr {B : W'.Splitting W r} {e} (k : B.k = A.k.submatrix id e ∧ B.i =
  A.i) [IsBaseAdapted B] : realSlice A U 0 = realSlice B U 0 := by simp [realSlice, ← Pi.zero_def,
  IsAdapted.mixedModel, A.zeroTerm_homSource_congr U (k.1 ▸ congr(submatrix $A.gram_kk e _)) k.2]

lemma slice_zero_comp [IsBaseAdapted B] y : realSlice (A.comp B) U 0 y = realSlice B U 0
  (realSlice A U 0 y) := eq_of_integrated_zeroTerm_eq (isAdapted_homSource ..) fun _ ↦
  (zeroTerm_integrated ..).symm.trans (by rw [zeroTerm_homSource_comp, zeroTerm_homSource_comp,
  zeroTerm_integrated, zeroTerm_integrated,
  ← (by simpa [slice_vac] using zeroTerm_integrated (isAdapted_homSource A U) vacVector :)]; rfl)

/-- Descent: let W′ split adaptedly over W of even rank with |p| ≥ 1 planes, and V′ have |p|
more signs of each kind than V. Some map f carries `StdExchange` for (x, y) to (f x, zero
term of y) and, for matching weights and ranks, every determinant vector is f of one. -/
lemma exists_stdExchange_removing_planes [Nonempty p] μ {ℓ} k j (V : Space E r t) σ σ'
  (hs : negCount t' = card p + negCount t) (hn : 2 ∣ card n) : ∃ f : _ → _,
  (∀ x y, StdExchange W' V' U μ σ' x y ℓ → StdExchange W V U μ σ (f x) (realSlice A U 0 y) ℓ) ∧
  (card n = 2 * (k + negCount s) → card n' = 2 * (k + negCount s') → μ = ((k : ℤ) + j ·) →
  (detVectors k j).SurjOn f (detVectors k j)) := by
  induction' hd : card p using Nat.strongRec with d ih generalizing p n n' r r'
  obtain ⟨e, e', l, _ | _ | d⟩ := card_congr σ, card_congr σ', A.card_eq, d
  simp at hd
  obtain ⟨⟨A, _, hk⟩, V₁, X, _⟩ := exists_isBaseAdapted_reindex A (equivOfCardEq (hd ▸ card_unit)),
    exists_isBaseAdapted Unit V t' (by grind [card_unit, card_sum]) (by bound [card_unit])
  obtain ⟨β, z, h, C, H⟩ := exists_constant_term_thetaLarge A X σ' σ hn μ
  refine ⟨_, fun _ y ⟨_, k, D, R⟩ ↦ ⟨by simp [integrable_coneIntegrand, *],
    isRapidDatum_slice _ _ k, D * C / ‖(vacuumFactor (isAdapted_homSource A U)).1‖ ^ 2, fun 𝔠 ↦ ?_⟩,
    fun _ m a ↦ a ▸ surjOn_cone_integral_detVectors A X β z h m⟩
  obtain ⟨⟨γ, o, _, H⟩, ⟨a, M⟩, c, hc, R⟩ := H 𝔠, thetaLarge_move W' W' V₁ V' 1 1 (by simp) 𝔠, R 𝔠
  use c * vacuumFactor (isAdapted_homSource A U) * a / γ, by simp [field]; grind [card_sum],
    fun z hz ↦ funext fun g ↦ mul_left_cancel₀ o ?_
  have i := hz.mul (adaptedFrame 𝔠.readsAt A).blocks_spec.2.1
  rw [← H (u := 1)] <;> simp [thetaSmall, rankTwist_eq_mul_of_splitting A, field,
    slice_zero_congr _ _ hk, *]
  clear * - hz k i
  obtain ⟨r, m', m⟩ := 𝔠.readsAt.star,
    (stdColDatum_mem_schwartzBruhat 𝔠.χ i).transpose_mem_schwartzBruhat,
    (stdColDatum_mem_schwartzBruhat 𝔠.χ hz).transpose_mem_schwartzBruhat
  have K x := r.sourceTerm_localDatum A U (G :=
    (invOnUnits _ <| det <| z * ·.toCols₂ᵀ)) m' ((WeilData.scaleIdele E)⁻¹ • x) y
    fun _ _ ↦ if_congr forall_comm (by simp [adaptedFrame, iCoord, stdForm]; congr; aesop) rfl
  erw [integral_thetaIntegral_lineRadical A _ _ (r.isTargetBounded k m'), ← integral_const_mul,
    ← integral_const_mul]
  congr with h; erw [tsum_eq_single 0 fun x o ↦ by_contra fun H ↦ ?_, constTermAt_zero]
  swap; obtain ⟨_, _, _, X, _⟩ := exists_splitting U (.of_ne_zero o) (ite_ne_right_iff.1 H).1
  rcases (constTermAt_smul_k A X one_ne_zero (f := ·)), (name_eq_zero_of_invariant r.1 (hΨ :=
    r.isSchwartzBruhat m) (h⁻¹.mat * X.kAdelic) 1 (ℓ := θ _ ∘L (X.homTarget W).zeroTerm ∘L pairWeil
    _ _ · · (g, h)) (fun z f ↦ by simp [← zeroTerm_rho_kAdelic (matToVec (vecToMat z *
    stdForm E s * g⁻¹.mat * W.dualFrame.2)) (pairWeil _ _ _ _ _ f), varrho_pairWeil,
    homTarget_kAdelic, kronecker_mulVec_eq_matToVec, G.mat])
    fun _ ↦ (U.coordMatrix_mul_ne_zero (by aesop) 1 <| m.2.2 ·))
  iterate 2 simp_all [lineTerm, integrated_name, stdColDatum, IsIntMatrix, @forall_comm n,
    mem_O_locProd, A.sourceTerm_levi, pairTheta, field]
  choose B _ k using exists_isBaseAdapted_stage A (finSumFinEquiv.trans (equivFinOfCardEq hd).symm)
  refine' let Y := hypSum (Fin 1) V; (card_eq.1 _).elim fun τ ↦ (ih _ _ V' B Y τ σ' _ _ rfl).elim
    fun f a ↦ (ih _ _ Y (removePlanes _ W) V σ τ _ _ rfl).elim fun g c ↦
      ⟨_, _, fun _ _ _ ↦ .comp (c.2
    ..) (a.2 ..)⟩ <;> simp +contextual [slice_zero_congr U A k, slice_zero_comp, *] at e ⊢ <;> omega

end

open Matrix MeasureTheory Fintype Std Weil ExistsContDiffBumpBase

/-- Exchange with implicit constant: let rk W = rk U + rk V be even, W₁ = ℍ ⊕ X be W plus
adapted planes, signs add, z, y rapid. For some real C and rapid v, each tame ν has c with I
= cI′ on partners (Ψ locally constant) and C|c|² = Π(rk V − rk W/2)·`equalRankThetaRatio`(W₁, z);
I, I′ are the theta integrals over [U(V)], [U(U)], and Π = `lValueProdInt`. -/
lemma exchange_of_partners {E} [Field E] [CMType E] [WeilData E] {n m r p b} [Fintype n] [Fintype m]
    [Fintype r] [Fintype p] [Fintype b] {s s' t u} {W : Space E n s} {X : Space E m s'} (U : Space E
    b u) μ [Nonempty p] (A : (hypSum Unit X).Splitting W p) [IsBaseAdapted A] (V : Space E r t) (σ :
  b ⊕ r ≃ n) {z y} (r₁ : IsRapidDatum z) (hy : IsRapidDatum y) (hs : 1 + negCount s' = card p +
  negCount t + negCount u := by simp) (hn : 2 ∣ card n := by simp) : ∃ C v, IsRapidDatum v ∧ ∀ 𝔠 :
  SplitTameChar E μ, let γ := rankTwist 𝔠.ν⁻¹ n; ∃ c, C * ‖c‖ ^ 2 = lValueProdInt 𝔠 (card r - card
    n / 2) * equalRankThetaRatio (hypSum Unit X) 𝔠 z ∧ ∀ Φ Ψ, IsLocallyConstant Ψ → IsPartner
    SemilocalField.O σ 𝔠.χ Φ Ψ → ∀ g, thetaIntegral W V γ 1 (localDatum W V v Φ 𝔠.readsAt) g =
    c * ∫ h, pairTheta U W γ γ (localDatum U W y Ψ 𝔠.readsAt) (h, g) ∂U.quotMeasure := by
  let f := flipCoords (E := E) (s := s) star_normNegOne_mul_self (t := u) rfl
  have : IsRapidDatum
    (f.realMap y) := by simpa [IsRapidDatum, weightedNorm, enorm, fun x ↦ (eq_of_forall_ge_iff (by
    simp [f, flipCoords, starCoordEquiv, ↓pi_nnnorm_le_iff, nnnorm]; tauto) : ‖f.realEquiv
    x‖₊ = ‖x‖₊), ← (Heisenberg.IsVacuum.measurePreserving_equiv (realHeis 1) (realHeis 1)
    f.vac_realEquiv).lintegral_comp_emb f.realEquiv.measurableEmbedding] using! hy
  obtain ⟨_, w, a, e, -⟩ := exists_rapid_with_realSlice A.symm _ _ (u_smooth _) this
    (u_compact_support _) u_nonneg 0 ((u_support _).ge (by simp))
  obtain ⟨⟨x, u, rfl, H⟩, _, k⟩ := exists_stdExchange_top (removePlanes ..) (removePlanes _ X)
    (flipSpace U) (.symm (.sumAssoc ..)) (by grind [A.card_eq]) μ a r₁, id hn
  choose rv _ C c _ K using e ▸ slice_zero_comp _ _ (removePlanes ..).symm A u ▸
    (exists_stdExchange_removing_planes _ _ _ μ 0 0 V σ _
    (by simp; grind [negCount_neg_add]) hn).choose_spec.1 _ _ H
  refine ⟨C, _, rv, fun 𝔠 ↦ ?_⟩
  let t := normNegOne.map ((evalPlaces 𝔠.S).restrict _ _ evalPlaces_mem_O).1
  obtain ⟨⟨d, _, H⟩, r, _, 𝒟, h, R⟩ := exists_pairTheta_flip star_normNegOne_mul_self rfl U W
    (flipSpace U) 1 (by simp [flipSpace, ← ext_iff]) _, 𝔠.readsAt,
    exists_isEquivariantLift W V (flipSpace U) 𝔠 σ hn rv this (c 𝔠)
  use c 𝔠 * 𝔠.χ t ^ card b * d, by simp [*, TameLocalChar.norm_eq_one, isIntegralUnit_iff_isUnit.2],
    fun Φ Ψ m P g ↦ ?_
  rw [mul_assoc, ← integral_const_mul, ← funext fun l ↦ H _ _ l _ l.neg (by simp)]
  have : localDatum W (flipSpace U) (f.realMap y) (Ψ ·ᵀ) r.star =
    𝔠.χ t ^ card b • f.map (localDatum U W y Ψ r) := by
    rw [map_integrated, map_name _ _ _ r.1 r.star.1 (hΨ :=
      r.isSchwartzBruhat (h.le_schwartzBruhat (R m P).1)), ← map_smul, Space.smul_name]
    congr!; dsimp; rw [← P.right_mul _ ⟨.scalar _ t, rfl⟩, mul_comm]; congr
    all_goals (try unfold f flipCoords starCoordEquiv); simp [vecToMat, funext_iff, mul_left_comm,
      star_idem, starRingEnd_apply, Set.conjClosure, ← ext_iff, field, t]
  convert congr((rankTwist 𝔠.ν⁻¹ n).1 g.det * $(sub_eq_zero.1
    ((R m P).2.symm.trans ((isPrimitiveMatrix_firstCols σ (one_mem _)).rec fun j ⟨s, i, e⟩ ↦
    (partner_mem_of_stdColDatum h.comp_mul_mem_ker (inf_le_left.trans h.le_schwartzBruhat) m P ((R
    (stdColDatum_mem_schwartzBruhat _ i).1 (isPartner_stdRowDatum_stdColDatum σ i)).imp_right
    (by simp [*])) j i e 1 (by simp) _).2)))
    g) using 1 <;> simp [thetaIntegral, isForm_neg_iff_and_integral_neg U (flipSpace U), pairTheta,
    pairWeil, rankTwist, ↓this, *, ← integral_const_mul]
  repeat congr with <;> field

open Space Equiv Subsingleton ENNReal MixedModel Heisenberg Sum OrthogonalSum IsIntMatrix Finset
variable {E n} [Field E] [CMType E] [WeilData E] [Fintype n] {s} (W : Space E n s) (μ : _ → ℤ)

lemma name_vacElem_of_isEmpty [IsEmpty n] (𝔠 : SplitTameChar E μ) Φ : W.name 𝔠.S Φ W.vacElem =
  Φ 0 • W.vacElem := by
  nth_rw 1 [(funext (by simp [eq_zero ·]) : Φ = Φ 0 • boxIndicator _ 𝔠.S)]
  simp [name_boxIndicator 𝔠.readsAt.1]

attribute [local simp] name_vacElem_of_isEmpty localDatum stdColDatum pairTheta pairWeil_apply
  funext_iff vacElem_apply_eq_prod_lineTheta measureReal_univ_ne_zero
  IsIntMatrix.one lValueProdInt_pos invOnUnits thetaIntegral dvd_add

attribute [-simp] measure_univ_of_isAddLeftInvariant probReal_univ

/-- Let W have rank n = 2k + 2q, q negative signs, and weights μ ≥ k. Some rapid v and C ≠ 0 give
|λ(v)|² = CΠ(n/2+1) on ℍ ⊕ W for all tame characters of weight μ (`equalRankThetaRatio`,
`lValueProdInt`). -/
lemma exists_equalRankThetaRatio_value k (hk : card n = 2 * k + 2 * negCount s) (hm : ∀ v, k ≤
  μ v) : ∃ v, IsRapidDatum v ∧
  ∃ C ≠ 0, ∀ 𝔠 : SplitTameChar E μ, equalRankThetaRatio (hypSum Unit W) 𝔠 v = C := by
  let J := stdSpace E (Fin (2 * k))
  obtain ⟨X, A, _⟩ := exists_isBaseAdapted (Fin _) J s (by simpa) (by simp)
  let Y := hypSum Unit X
  let P := removePlanes Unit X
  let Q := P.comp A
  let Z := stdSpace E Empty
  obtain ⟨o, h₀ | ⟨_, v₁, r₁, h⟩⟩ := (J.isAutomorphic_const 1).mem_rapidFunctions,
    em' (∃ 𝔠 v, IsRapidDatum v ∧ equalRankThetaRatio Y 𝔠 v ≠ 0)
  simp [equalRankThetaRatio, ne_of_gt, -thetaIntegral] at h₀
  refine (exists_stdExchange_removing_planes J.neg _ ((removePlanes _ Y).symm.comp Q) μ k
    (μ · - k |>.toNat) Z (sumEmpty ..) (sumAssoc ..).symm ?_ ?_).rec fun f ⟨K, a⟩ ↦
    (a ?_ ?_ ?_ ⟨isRapidDatum_vacVector, 1, 0, ?_⟩).rec fun v ⟨⟨r, _⟩, a⟩ ↦ (a ▸ K _ 0 <|
    stdExchange_of_periods _ (removePlanes _ Y) P _ 0 ?q zero_le_one ?_ r ?_ (fun 𝔠 _ ↦ ⟨1, by
    simp_intro .. [realSlice]; exact And.elim (fun i R ↦ .trans (by
      congr with
      rw [IsVacuum.map_eq_integral]
      convert! (θ _ ∘L (pairWeil ..) _ ∘L (integrated _).flip _).integral_comp_comm i
      rw [map_smul, map_smul]
      convert! congrArg _ (thetaOnRealData_boxProd_eq_mul ..)
      erw [← heisOp_tmul, tmul_vacElem]) ((thetaLarge_eq_apply_one_of_even_rank P _ ?q R _).trans
      (h₀ _ _ R))) (isRapidDatum_integral (by fun_prop) fun _ ↦ (eq_top_mono
      (lintegral_weightedNorm_smul_le fun y ↦ by grw [weightedNorm_smul, weightedNorm_realHeisOp_le,
      ← ofReal_norm, (thetaOnRealData ..).le_opNorm, Heisenberg.Rep.norm_map,
      (enorm_le_iff_norm_le.2 (pi_norm_comp_le y _) : ‖Prod.snd _‖ₑ ≤ _), mul_comm, mul_rotate])).mt
      (by simp [mul_eq_top, isRapidDatum_vacVector _, realPairWeil, weightedNorm_smul,
      isRapidDatum_slice _ _ r _, (eq_top_mono (weightedNorm_realWeil_le ..)).mt]))⟩) ?_).2.2.rec
    fun _ K ↦ ⟨_, isRapidDatum_vacVector, 1, ?_,
    fun 𝔠 ↦ by simpa [↓isIntegralUnit_iff_v_eq_one, univ_eq_empty, @eq_one (G ..),
    (id rfl : stdRowDatum (sumEmpty ..) _ 1 _ = stdColDatum _ 1 1)] using
    (K 𝔠).choose_spec.2 _ .one⟩ <;> simp +arith [IsRapidDatum, weightedNorm, detVectorFn, *]
  choose B y r b hb K using exchange_of_partners Z μ Q J (emptySum ..) r₁ isRapidDatum_vacVector
  choose C x _ c hc H using exchange_of_partners J μ Q Z (sumEmpty ..) r₁ r
  refine have F 𝔠 : equalRankThetaRatio Y 𝔠 v₁ ^ 2 =
      B * C * ‖integrated _ x (J.hom Z).vacElem 0‖ ^ 2 := ?_
    ⟨_, r₁, _, h, fun 𝔠 ↦ by rw [← sq_eq_sq₀, F, ← F 𝔠, equalRankThetaRatio,
      (thetaLarge_move _ _ _ Y _ _ (exists_eq_move
      ..).choose_spec.choose_spec.2.1 𝔠).choose_spec, thetaLarge_eq_apply_one_of_even_rank P] <;>
      simp [Y, *, equalRankThetaRatio, div_nonneg, _root_.le_of_lt, -thetaIntegral]⟩
  have T α φ := (pairThetaKer _ _ α α).integral_lift_eq_integral_descent (φ := φ) o o
  specialize K 𝔠 (stdColDatum _ 1) _ (.of_discrete _)
    (isPartner_stdRowDatum_stdColDatum _ (s := 0) nofun)
  have := congr(‖∫ g, $(H 𝔠 (fun _ ↦ stdColDatum _ 1 1) _ (stdColDatum_mem_schwartzBruhat _ .one).1
    (isPartner_stdRowDatum_stdColDatum _ IsIntMatrix.one) g) ∂J.quotMeasure‖)
  simp [↓isIntegralUnit_iff_v_eq_one, ↓IsIntMatrix.one, IsIntMatrix, lift, field, univ_eq_empty,
    @eq_one (G ..), mul_right_comm _ _⁻¹] at T K this
  simp [*, field] at *
  rw [this]; clear * - hc hb; grind [lValueProdInt, lValueProdInt_pos]
