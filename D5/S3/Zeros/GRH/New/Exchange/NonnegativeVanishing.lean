/- GID: D5/S3/Zeros/GRH/New/Exchange/NonnegativeVanishing
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/NonnegativeVanishing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.NonnegativeVanishing. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/NonnegativeVanishing.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.MixedModel.EquivariantCoefficients
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Exchange theorem for theta integrals of complementary rank (see
New.Exchange.ExchangeTheorem).

This file: Theta integral coefficient vanishes at forms not negative definite, by circle weights. -/

attribute [-simp] map_zero map_neg
open Matrix MatMul MeasureTheory Measure Space Pointwise Pi Fintype MulAction ComplexConjugate
  ComplexOrder MatrixOrder Heisenberg.IsVacuum Finset CStarAlgebra Kronecker
attribute [local simp] neg_eq_iff_eq_neg vecMulVec_mulVec card_subtype_le vecMulVec_apply
  blockDiagonal pairSign sum_prod_type mul_vecMulVec vecMulVec_mul neg_mulVec commute_iff_eq
  star_mulVec rep_apply_apply mulVec Matrix.single_apply negCount RCLike.mul_conj mul_assoc add_mul
  ite_and vecMul mem_blockDiagAlg_iff_commute pairHomInf pairHom holCoord_eq
attribute [local simp ←] dotProduct_mulVec replicateCol_mulVec

/-- Let X split over Z along b lines, Y have a positive sign and b more negative signs than Z,
and weights of ν be below the number of positive signs of Z. For integrable terms, the theta
integral with characters νυ^b has coefficient 0 at invertible T with ȷ⁻¹T not totally
negative. -/
lemma centreCoeff_eq_zero_of_not_negative {E} [Field E] [CMType E] [H : WeilData E] {a b m n}
  [Fintype a] [Fintype b] [Fintype m] [Fintype n] {r ν} {X : Space E m r} {s} {Y : Space E n s} {t}
  {Z : Space E a t} {D : X.Splitting Z b} {μ ψ δ f g T} [AutChar.HasWeight ν μ ψ] i (hγ : ∀ τ,
  μ τ < negCount (-t)) (ht' : s i = 1) (ht : card b + negCount t = negCount s) (d : δ =
  ν * H.upsilonU1 ^ card b) (h₀ : IsUnit T) (hR : ¬RepresentedBy (-1) (T.map toAdele)) (hi :
  D.HasIntegrableTerms Y δ δ f g) : D.centreCoeff (H.j • T) (thetaIntegral X Y δ δ f) g = 0 := by
  obtain ⟨⟨τ, hβ⟩, e | ⟨x, rfl⟩⟩ := not_forall.1 hR,
    isEmpty_or_nonempty {x : Matrix n b E | xᴴ * Y.J * x = T}
  simpa [tsum_empty] using! D.centreCoeff_integral_eq_tsum hi T
  let x' := Y.x⁻¹.1 * x.map toAdele
  rw [← gram_at_point_eq_map, ← gram_map_real] at hβ
  set w := atRealPlace x' τ with ← e
  obtain ⟨h, M, hM⟩ := isHermitian_conjTranspose_mul_mul w posProj_mul_self.2.2, (hγ τ).dest
  obtain ⟨v, -, hv⟩ := herm_represents_one h ⊤ fun _ ↦ hβ (by simpa [eq_comm] using! (
    nonneg_iff_eq_star_mul_self.1 (posSemidef_iff_dotProduct_mulVec.2 ⟨h.neg, by simp_all⟩).nonneg))
  have ⟨u, hu⟩ := witt ⟨.I, by simp⟩ (posProj_mul_self (ε := s)).2.2 IsHermInvolution.isUnit
    (.of_ne_zero (x := w *ᵥ v) (by simp [← mulVec_mulVec, ·] at hv))
    (.of_ne_zero ((basisFun ℂ _).ne_zero i)) (by ext; simp_all [← replicateRow_vecMul, signMatrix])
  -- no invariant functional on the Fock space: enough negative lines can be rotated
  have K (l : PairFock E t s →L[ℂ] ℂ) (k : ∀ c ∈ maxCompactU s, c.1.1 * (u.1.1 * w) = u.1.1 * w →
    ∀ v, l (realPairWeil μ 0 (1, mulSingle τ c) v) = l v) : l = 0 := hom_ext fun y ↦ by
    let f := ((u.1.1 * w).vecMulLinear.prod (of fun i (j : {j // t j = -1}) ↦ y (τ, i,
      j)).vecMulLinear).prod (.funLeft ℂ ℂ (@Subtype.val _ (s · ≠ -1)))
    have : Nonempty {k // s k ≠ -1} := ⟨⟨i, by simp [ht']⟩⟩
    obtain ⟨r, hr, h1⟩ := herm_represents_one isHermitian_one f.ker fun n ↦ have ⟨r, h⟩ :=
      (f.linearEquivOfInjective (.of_ker f (by simpa [
        (dotProduct_star_self_nonneg _).ge_iff_eq'] using n)) (by simp_all)).surjective (0, 1)
      by simpa [f, by simpa using hu] using congr($h.1.1 ⬝ᵥ v - $h.2 ⟨i, by simp [*]⟩)
    simp [f, funext_iff, dotProduct_comm] at hr h1
    let z := .single τ τ 1 ⊗ₖ (vecMulVec (star r) r ⊗ₖ diagonal 1) *ᵥ y
    let F (η : ℂ) : PairFock E t s := η ^ M.succ • realHeisOp (y + (conj η - 1) • z) vacVector
    have e (L : _ →L[ℂ] _) {f} (h : ∀ η, η * conj η = 1 → L (F η) = f η) d := (L.integral_comp_comm
      integrable_of_compactSpace).symm.trans (congr(∫ θ, $(h _ (by simp))).trans (@integral_toCircle
      f d))
    refine (e l (fun η h0 ↦ ?_) (differentiableOn_const _)).symm.trans (.trans (congrArg l (ext
      fun w ↦ (e (modelEval w) (fun η h0 ↦ by rw [map_smul, valueAt_apply, heisOp_apply,
      Heisenberg.IsVacuum.vacElem_apply, beta_mul_realVac,
      (by simp [realVac, z, *]; clear * - h0; grind : realVac (y + _) = realVac y), map_add,
      (show Function.IsFixedPt (holCoord _) (_ • z) by
           funext p; by_cases s p.2.1 = -1 <;> simp [*, z, dotProduct, ← mul_sum]
           clear * - hr; grind [dotProduct])]) (by simp; fun_prop)).trans (by simp))) l.map_zero)
    have : posProj s *ᵥ star r = 0 ∧
      r ᵥ* posProj s = 0 := by simp +contextual [funext_iff, posProj, *]
    convert k (U.of IsHermInvolution.isUnit (1 + (conj η - 1) • vecMulVec (star r) r) ?_)
      (ext ?_) ?_ _
    any_goals simp [← Matrix.ext_iff, signMatrix_eq_posProj_sub, *] <;> clear * - h0 <;> grind
    rw [realPairWeil_apply_apply, weilRep_heisOp, ← map_smul, ← realPairWeil_apply_apply,
      ← vacVector, ← polyVector_one, realPairWeil_polyVector,
      Fintype.prod_eq_single τ, map_smul]; congr! 3
    · simp [principalMinor_eq_det, ← posProj.eq_1, *, eq_inv_of_mul_eq_one_right h0,
        eq_sub_of_add_eq hM]
      rw [← smul_vecMulVec, vecMulVec_eq Unit, det_one_add_mul_comm]
      simp +contextual [*, ite_eq_left_iff.2, ← zpow_natCast]
    all_goals simp [funext_iff] <;> intro w <;> by_cases τ = w <;> simp [*, z,
      dotProduct, mul_sum, signMatrix_eq_posProj_sub]
  let H := stabilizer (G E s) x'
  obtain ⟨h : IsClosed H.carrier, I, -, J⟩ := isClosed_singleton.preimage (f := (G.mat · * x'))
    (by fun_prop), D.centreCoeff_eq_integral_stabilizer hi h₀ fun _ ↦ (stabilizer ..).mem_map
  let U : G .. := (mulSingle τ u⁻¹, 1)
  let C := (ConjAct.toConjAct U • maxCompact ..).subgroupOf H
  have c : @IsCompact H _ C := (isCompact_maxCompact.smul _).preimage_val
  obtain ⟨⟨_, A, B⟩, _, _⟩ := exists_compact_superset c, c.compactSpace, c.isClosed
  have law (k : H) h := by simpa [← d, x', -coe_units_inv, (id k⁻¹.2 : k.1⁻¹.mat *
    x' = _)] using D.sourceTerm_levi _ ν δ 1 1 k x' (pairWeil _ _ δ δ (g, h) f)
  let κ := (haar (@.univ C))⁻¹ • haar (G := C)
  have : MeasurableConstSMul Cᵐᵒᵖ C := ⟨fun c ↦ measurable_mul_const c.unop⟩
  have : (haar (G := C)).IsMulRightInvariant := inferInstance
  have : κ.IsMulRightInvariant := isMulRightInvariant_smul _
  -- `C` keeps the Haar measure of `H`, which is read on a compact neighbourhood stable under `C`
  simpa using! J.trans (integral_quotMeasure_eq_zero_of_mean _ I (by fun_prop [Splitting.thetaTerm])
    (fun _ ⟨_, _, e⟩ ↦ e ▸ (ratMap_mul_toAdele ..).trans (by congr)) κ (fun _ ↦ (↑)) 1 (fun _ k ↦
    (one_smul ..).substr (((haarMeasure_unique ..).congr (haarMeasure_unique _ ⟨⟨_, A.mul c⟩, _,
    subset_interior_mul_left ⟨_, B k.2, k, k.2, rfl⟩⟩)).2 congr($(by simp [Set.preimage,
    (measurableEmbedding_mulRight _).map_apply, ← QuotientGroup.preimage_image_mk_eq_mul]) • _)))
    zero_ne_one fun k _ ↦ let T (c : C) := θ _ ∘L pairWeil Z Y ν δ (1, k * (c * U))
    have e := strongIntegral_apply κ T fun _ ↦ integrable_of_compactSpace (by simp [T]; fun_prop)
    by simpa [↓law, e, T, Splitting.thetaTerm] using ext_integrated _ (projOn_empty _ (pairWeil _ _
      ν δ (1, U⁻¹) _)) fun _ _ _ ↦ DFunLike.congr_fun (K (strongIntegral κ T ∘L (integrated _).flip
      _) fun c _ _ v ↦ let p := U * (mulSingle τ c, 1) * U⁻¹
      by simpa [← pairWeil_integrated_right ν δ, e, T, p] using integral_mul_right_eq_self (T
        · _) ⟨⟨p, matrix_ext_𝔸 (fun w ↦ Matrix.map_mul.trans (show (p.1 w).1.1 * atRealPlace x' w =
        atRealPlace _ w by by_cases w = τ <;> simp [p, U, *])) (Matrix.map_mul.trans (by
          simp [p, U]; apply Matrix.one_mul))⟩, _, ⟨by simpa, by simp⟩, rfl⟩) _)
