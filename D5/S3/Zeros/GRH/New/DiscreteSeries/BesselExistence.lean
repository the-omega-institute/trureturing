/- GID: D5/S3/Zeros/GRH/New/DiscreteSeries/BesselExistence
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/DiscreteSeries/BesselExistence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.DiscreteSeries.BesselExistence. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/DiscreteSeries/BesselExistence.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Algebra.ZerosCostDegree
import D5.S3.Zeros.GRH.New.RealPlace.BesselOrthonormal
import D5.S3.Zeros.GRH.New.DiscreteSeries.TwoFactorSetup
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Discrete series coefficients near 1 and explicitly large Bessel functions (see
New.DiscreteSeries.RestrictionLemma).

This file: Record tying a Bessel system to its weight, degree and discrete series projector. Point
of controlled size, from Lagrange weights, where the Bessel phases cancel. A discrete series Bessel
function explicitly large at a point where phases cancel. -/

open Matrix

/-- A fixed unitary matrix p with pᴴJ₁p the diagonal matrix of the signs ε, where J₁ =
`Shape.J₁`. -/
class Frame (𝔰 : Shape) (ε :
  outParam _) extends SignFrame 𝔰.J₁ ε where mem_unitary : p.1 ∈ unitary _

/-- B has type (l, kw): degree given by Weyl's dimension formula for l, full function transforming
under U(κ) by weight kw and fixed by right integration against `dsKernel` ε l. -/
structure Filling.IsBessel {𝔰 ε b f} [Frame 𝔰 ε] (B : BesselSystem 𝔰 b f) (l : HCParam ε) kw where
  deg_eq : B.deg = weylDimensionPoly l
  equiv_schur : letI V := WeylIndex 𝔰.κ fun _ : Unit ↦
      kw; ∃ (A : Matrix V ..) (A' : Matrix B.I V ℂ), A * A' = 1 ∧ A' * A = 1 ∧ ∀ g y,
      A *ᵥ B.W .full (toBesselH 𝔰 1 g * y) = (schur _ fun _ ↦ gᵀ)ᵀ *ᵥ A *ᵥ B.W .full y
  kernel_fix y i : ∫ x, l.dsKernel x * B.W .full (y * frameEquiv.symm x) i = B.W .full y i

open Fin Subgroup Complex ComplexConjugate Filling Finset IsHermInvolution MatMul MeasureTheory
  Norms.L2Operator
variable (𝔰 : Shape)

/-- The group S = H𝖴 as a graph: the pairs (g, h) in G₁ × U(κ) with h⁻¹g in the unipotent group
𝖴, h embedded in G₁ by `embedH`. -/
noncomputable def Shape.besselGraph : Subgroup (𝔰.G₁ × U (1 : Matrix 𝔰.κ _ ℂ)) := .ofDiv
    {s | (embedH s.2)⁻¹ * s.1 ∈ besselU} ⟨1, by simp⟩ fun _ a t b ↦ by
  simpa [mul_assoc] using (besselS_le_normalizer_besselU
    (mem_unitriGroup_of_mem_floorGroup (toBesselH_mem t.2)) _).1 (mul_mem a (inv_mem b))

instance : IsClosed (SetLike.coe 𝔰.besselGraph) :=
  (isClosed_of_entries_eq_one mem_besselU).preimage_of_continuous

attribute [simp] ofDiv

/-- The homeomorphism 𝖴 × U(κ) → S (S = `Shape.besselGraph`) sending (u, h) to the pair (hu, h). -/
@[simps!] noncomputable def Shape.besselGraphChart :=
  (.mk ⟨fun q ↦ ⟨(embedH q.2 * q.1.1, q.2), by simp [besselGraph]⟩,
  fun s ↦ (⟨_, s.2⟩, s.1.2), by simp_intro _, by simp_intro _⟩ : besselU × _ ≃ₜ 𝔰.besselGraph)

/-- The measure on S = `Shape.besselGraph` that is the image, under (u, h) ↦ (hu, h), of the
product of `Shape.besselHaar` on 𝖴 and the compact dual measure on U(κ). -/
noncomputable def Shape.besselGraphMeasure := (𝔰.besselHaar.prod volume).map 𝔰.besselGraphChart

instance : 𝔰.besselGraphMeasure.IsOpenPosMeasure :=
  𝔰.besselGraphChart.2.isOpenPosMeasure_map 𝔰.besselGraphChart.surjective

instance Shape.besselGraphMeasure_finiteOnCompacts :
  IsFiniteMeasureOnCompacts 𝔰.besselGraphMeasure := Measure.IsFiniteMeasureOnCompacts.map ..

instance Shape.besselGraphMeasure_isMulRightInvariant : 𝔰.besselGraphMeasure.IsMulRightInvariant :=
  ⟨(reindex_equiv 𝔰.besselGraphChart).1.2 fun t ↦ ((𝔰.besselGraphChart.measurable.measurePreserving
  _).of_semiconj (((measurePreserving_conj_bessel mem_besselU besselS_le_normalizer_besselU
  (mem_unitriGroup_of_mem_floorGroup (toBesselH_mem t.2⁻¹))).mul_right _ t.1).prod
  (measurePreserving_mul_right _ t.2)) (by intro; ext1; simp; group) (by fun_prop)).2⟩

variable {𝔰} (s : 𝔰.besselGraph) {x : 𝔰.G₁} {ε} [p : Frame 𝔰 ε]

@[simp] lemma besselGraph_fst_mem_besselS : s.1.1 ∈ besselS := mem_besselS.2 ⟨_, inv_mem s⁻¹.2,
  embedH s.1.2, by simp⟩

/-- Unfolding: for x in G₁ and measurable f ≥ 0 on G₁, ∫f(g)dg = ∫∫f(xsy) dν_S(s) dν(y), with s
in S = `Shape.besselGraph` read in G₁, ν_S = `Shape.besselGraphMeasure`, and ν = `besselQuotMeasure`
the measure for integrating over G₁ modulo 𝖴. -/
lemma lintegral_unfold_besselGraphMeasure f (m : Measurable f) : ∫⁻ g, f g = ∫⁻ y, ∫⁻ s,
  f (x * (s.1.1 * y)) ∂𝔰.besselGraphMeasure ∂besselQuotMeasure := by
  simp (disch := fun_prop) [lintegral_map, lintegral_prod, Shape.besselGraphMeasure, mul_assoc]
  erw [lintegral_orbitMeasure_lintegral (f := fun g ↦ ∫⁻ k, f (x * (embedH k * g))),
    lintegral_lintegral_swap] <;> simp [← mul_assoc, lintegral_mul_left_eq_self] <;> fun_prop

attribute [local simp] FI.level forall_fin_succ' BlockTriangular inclMatrix val_toBesselH_apply_coe

/-- Let s = (g, h) lie in `Shape.besselGraph`, that is g ∈ h𝖴 with h in U(κ) embedded in G₁. Then
tr(Mg) = tr(Mh) for every M that is block upper triangular for the levels `FI.level`. -/
lemma besselGraph_trace_mul_sub_eq_zero {M : Matrix _ _ ℂ} (h : M.BlockTriangular FI.level) :
    trace (M * (s.1.1.1.1 - (embedH s.1.2).1.1)) = 0 := by
  erw [← mul_inv_cancel_left _ s.1.1, ← mul_sub_one, ← mul_assoc]
  exact sum_eq_zero fun i _ ↦ sum_eq_zero fun j _ ↦ mul_eq_zero.2 ((lt_or_ge ..).imp (h.mul (by
    simp; lia) ·) (sub_eq_zero.2 ∘ mem_besselU.1 s.2 j i))

/-- For x in `Shape.G₁`, the homomorphism (g, k) ↦ (p⁻¹x⁻¹gxp, k) from `Shape.besselGraph` to U(diag
ε) × U(κ), where p is a basis with Gram matrix diag ε. -/
noncomputable def besselPairHom (x : 𝔰.G₁) : 𝔰.besselGraph →* USign ε × @USign 𝔰.κ _ 1 :=
  .domRestrict (.prodMap (.comp (frameEquiv (ε := ε)) (MulAut.conj x⁻¹).toMonoidHom)
  (inclusion (by simp [USign]))) _

/-- W is a Bessel function for rep with W∗(deg_λ ψ) = W, W(x) ≠ 0, and for all y: ‖W(y)‖ ≤ ∫_S
|ψ(x⁻¹sy)| dν, ∫_S (2/‖p⁻¹x⁻¹syp‖)^{8r²+1} dν ≤ P‖W(x)‖, ψ = `HCParam.psiInFrame`,
ν = `Shape.besselGraphMeasure`. -/
structure HasPeakAt {I} [Fintype I] (l : HCParam ε) rep W x P extends IsBesselFunction (I :=
  I) rep W where
  (convolve_eq : convolve W (l.formalDegree * l.psiInFrame ·) = W) (apply_ne_zero : W x ≠ 0)
  enorm_le y : ‖W y‖ₑ ≤ ∫⁻ s, ‖l.psiInFrame (x⁻¹ * (s.1.1 * y))‖ₑ ∂𝔰.besselGraphMeasure
  lintegral_le y : ∫⁻ s, .ofReal ((2 / ‖(frameEquiv (x⁻¹ * (s.1.1 * y))).1.1‖) ^
    (8 * 𝔰.r ^ 2 + 1)) ∂𝔰.besselGraphMeasure ≤ .ofReal P * ‖W x‖ₑ

/-- Assume `IsSteep`, p unitary, `lowestKType` 1 u = (0,…,0,a), B ≥ 1, 3B+a ≤ 2b², b ≥ 8(ϱ+1).
For some x with `besselSize` x ≤ b^{5(ϱ+1)}, the map `besselPairHom` x satisfies `IsTwoFactor`, with
phase σ − σ̄, σ(s) = `simpleRootSum` of s. -/
lemma IsSteep.exists_isTwoFactor_besselPairHom {X} [Fintype X] {B} {l : HCParam ε} {e :
  X ⊕ Fin (2 * 𝔰.ϱ + 2) ≃ 𝔰.BesselIndex} (H : IsSteep l B e) (τ : X ⊕ Unit ≃ 𝔰.κ) {u : HCParam 1}
  {a : ℕ} (ha : ∀ i, u.lowestKType i = ite (i = τ (.inr ())) a 0) {b} (hB : 1 ≤ B) (hb : 3 * B + a ≤
  b ^ 2 * 2) (b1 : 8 * (𝔰.ϱ + 1) ≤ b) : ∃ x, besselSize x ≤ b ^ (5 * 𝔰.n) ∧ IsTwoFactor l u
  (besselPairHom x) (τ ∘ .inl) B e fun s ↦ simpleRootSum s.1.1 - conj (simpleRootSum s.1.1) := by
  let t i := l.lowestKType (e (.inr i)) - a
  have : 1 ≤ b := by bound
  have tb i : t i ^ 2 ≤ b ^ 5 := by simp [t]; nlinarith [(H.weight_mem i).symm, sq_nonneg (b ^ 2)]
  have ⟨c, c1, hc⟩ := exists_lagrange_weights (.vecCons (f :=
    t) (H.weight_strictAnti.add_const _) (sub_neg.2 (by rify; linarith [(H.weight_mem 0).2])))
  let C := (fromBlocks (l := X) 1 0 0
    (of fun i n ↦ (c 0 ^ 0 ^ n * t i ^ n / c i.succ : ℂ))).submatrix e.symm id
  let V := p.p.1 * C
  have hC : ∀ {a b}, a.elim 0 .pred + b.elim 0 .pred ≤ 2 * 𝔰.ϱ → (Vᴴ * 𝔰.J₁ * V) a b = fromBlocks
      1 0 0 (of fun j k ↦ ite (j + k = 0) 1 (ite (j + k = 2 * 𝔰.ϱ + 2) (-1) 0)) a b := by
    simp [V, ↓gram_mul, p.gram_eq, ↓mul_apply (N := C), signMatrix, reindex_equiv e, C, H.sign_inl,
      H.sign_inr, @eq_comm X]
    intro a b h; linear_combination (norm := skip) c 0 ^ 0 ^ a * c 0 ^ 0 ^ b * congr(ofReal
      $((hc (.X ^ (a + b)) (by simp; norm_cast; lia)).trans (sum_univ_succ _)))
    simp [mul_add, mul_sum, pow_succ, zero_pow_eq]; grind [ofReal_eq_zero, ofReal_one]
  let f := @Sum.map X _ Unit ℕ id 0 ⊕ᵥ .inr ∘ .succ ∘ @val 𝔰.n
  let Y := inclMatrix ℂ (.inr ∘ .inl ∘ .inl ∘ τ ⊕ᵥ 𝔰.besselFrame)
  have ⟨g, z⟩ : ∃ g : 𝔰.G₁, (g.1 * p.p).1 * C.submatrix id f = Y := by
    simp [-Subtype.exists]; refine witt ⟨I, by simp⟩ isHermitian isUnit ⟨_,
      (Matrix.mul_assoc ..).trans (nonsing_inv_mul _
      (det_eq_one_of_unitriangular (lev := 0 ⊕ᵥ Fin.val) (Z := diagonal (1 ⊕ᵥ -1) * (Vᴴ *
      𝔰.J₁).submatrix (f ∘ .inl ⊕ᵥ (.inr <| 2 * 𝔰.ϱ + 1 - Fin.val ·)) id * _) (fun a b h ↦ ?_) ▸
      isUnit_one))⟩ ⟨_, inclMatrix_gram_eq_one (by simp)⟩ (ext fun a b ↦ (hC ?_).trans ?_)
    on_goal 3 => erw [Matrix.mul_assoc, diagonal_mul, hC]
    all_goals revert a b; simp [mul_apply, Y, splitGram, middleGram, f]; grind
  use g, pow_succ' b _ ▸ ge_trans (by gcongr) (besselSize_le_of_dual g (by bound) (.toLp 2 <| Vᵀ <|
    .inr ·.succ) (fun k ↦ by ext; simpa [frameVector, Y, ↓mul_inclMatrix] using! (congr((g⁻¹.1.1 *
    $z) _ (.inr k)).symm)) (fun k h ↦ (l2_opNorm_mulVec _ (.toLp 2 _)).trans (le_of_sq_le_sq (by
    simp [CStarRing.norm_of_mem_unitary p.2, PiLp.norm_sq_eq_of_L2, reindex_equiv e, div_pow,
      pow_right_comm _ _ 2]; grw [← (c1 _).1, tb]; simp [← pow_mul]
    grw [(by bound : _ + 2 ≤ b), ← pow_succ']; gcongr; lia) (by bound))) fun a b h ↦ .trans
    (dotProduct_comm ..) (by simpa +arith using! @hC (.inr a.succ) (.inr b.succ) h))
  have hq := gram_mul_of_gram_eq g.2 p.gram_eq; set q := _ * p.p
  have J s : subOnePair (besselPairHom g) s = (q⁻¹.1 * (s.1.1 - 1) * q,
    s.1.2.1.1 - 1) := by simp [q, besselPairHom, frameEquiv, U.conj]
  refine ⟨H, fun s ↦ ?_, fun s ↦ ?_, by simp [simpleRootSum_mul]; intros; ring, by simp, by
    simp [ha], by simp [ha, ite_nonneg], fun v hw ↦
    (exists_unitary_sub_one_eq_inclMatrix τ (by simp) hw.1).rec fun (⟨k, _⟩ : USign 1) hk ↦
    ⟨𝔰.besselGraphChart (1, ⟨k, by rwa [← signMatrix_one]⟩), (J _).trans (Prod.ext ?_ hk)⟩⟩
  rw [HCParam.phase, J, trace_mul_comm, mul_assoc, trace_mul_cycle]
  set D := _ * q⁻¹.1
  have d i := by simpa [↓mul_inclMatrix, Y, f, @eq_comm 𝔰.BesselIndex i] using (z ▸ by
    simp [D, q.1.mul_apply, f, C, t, reindex_equiv e, H.weight_eq_zero, sum_mul, ← sum_add_distrib]
    constructor <;> congr! 1 <;> ring : ∀ j, let m := Sum.map id castSucc j
    (D * Y) i m = (f m).elim (fun _ ↦ 0) (Y i m * a + Y i (.inr (j.elim 0 succ)) * c 0 ^ 0 ^ ·))
  have o : ∀ c x, 𝔰.besselFrame c = .inr x ↔ c = 𝔰.top ∧ .inl (.inr ()) = x := by simp
  rw [← sub_eq_zero, ← besselGraph_trace_mul_sub_eq_zero s (M := D - besselCharMatrix
    (𝔰.middleGram 1)) (by simp [besselCharMatrix, *, splitGram, ↓Sum.forall, ↓fun b
    j ↦ by simpa [mul_apply, splitGram, d, add_mul] using (congrFun₂ (show 𝔰.J₁ * D =
    Dᴴ * 𝔰.J₁ by simp [D, signMatrix, ← gram_inv_of_gram_eq hq, mul_comm,
    conjTranspose_nonsing_inv, ← mul_assoc (diagonal _)]) (.inl b) j)]; lia)]
  simp [↓trace_besselCharMatrix_mul, simpleRootSum_inv,
    simpleRootSum_eq_zero_of_mem_besselH, -val_toBesselH_apply_coe]
  simp [trace, mul_apply, diagonal, reindex_equiv τ, *]; ring
  rw [J, trace_mul_cycle, ← sub_eq_zero,
    ← besselGraph_trace_mul_sub_eq_zero s blockTriangular_one]; simp [trace]; ring
  have m i x := by simpa [f, C, mul_apply, reindex_equiv e, Y] using congrFun₂ z i (.inl (.inl x))
  erw [mul_assoc, Units.inv_mul_eq_iff_eq_mul]; simp_rw [← Matrix.mul_assoc, mul_inclMatrix]
  ext i; revert i; simp [mul_apply, m, (eq_add_of_sub_eq hk : k.1 = _), reindex_equiv τ,
    fun x j ↦ by simpa [mul_apply, m, splitGram, middleGram, signMatrix, diagonal,
    H.sign_inl] using congrFun₂ hq (e (.inl x)) j]

open ContinuousLinearMap ENNReal HCParam InnerProductSpace

lemma isProperMap_fst_besselPairHom {𝔰 ε} [Frame 𝔰 ε] (x : 𝔰.G₁) : IsProperMap
  ((MonoidHom.fst ..).comp (besselPairHom x)) := ((Homeomorph.smul (x⁻¹ : ConjAct _)).trans
  frameEquiv.toHomeomorph).isProperMap.comp (isProperMap_fst_of_compactSpace.restrict inferInstance)

/-- For continuous rep with ⟨v, rep(·)v⟩ = ψ_u, l `HCParam.HasLargeGap`, b ≥ 16, phase σ − σ̄ at x,
ν right Haar on `Shape.besselGraph`, ν(‖p⁻¹x⁻¹sxp − 1‖ ≤ 1) ≤ bⁿ|∫θ dν|: some Bessel W = W∗(deg·ψ)
has W(x) ≠ 0, ‖W(y)‖ ≤ ∫|ψ(x⁻¹sy)|dν, ∫(2/‖p⁻¹x⁻¹syp‖)^N dν ≤ b^{N+n}‖W(x)‖ for all y, N =
8·rank²+1; θ = `HCParam.laplaceIntegrand`, σ = `simpleRootSum`. -/
lemma exists_isBesselFunction {𝔰 I ε} [Fintype I] [Frame 𝔰 ε] {x v A b l u n} {rep :
  _ →* unitaryGroup I ℂ} (c : Continuous rep) (hc : ∀ k, ⟪v, (besselValueRep rep k).1 v⟫_ℂ =
  u.dsCoeff k) (hG : l.HasLargeGap A) (b0 : 16 ≤ b)
  (La : 𝔰.besselGraphMeasure.real {s | ‖(subOnePair (besselPairHom x) s).1‖ ≤ 1} ≤ b ^ n * ‖∫ s,
  l.laplaceIntegrand u (besselPairHom x) (fun s ↦ simpleRootSum s.1.1 - conj (simpleRootSum s.1.1))
  s ∂𝔰.besselGraphMeasure‖) : ∃ W, HasPeakAt l rep W x (b ^ (8 * 𝔰.r ^ 2 + 1 + n)) := by
  have hj := isProperMap_fst_besselPairHom x
  let f y (s : 𝔰.besselGraph) := l.psiInFrame (x⁻¹ * (s.1.1 * y)) • wave (-simpleRootSum s.1.1) •
    (besselValueRep rep s.1.2⁻¹).1 v
  obtain ⟨C0, mf : Continuous f.uncurry, v1 : ‖v‖ = 1⟩ :=
    measure_ball_ne_top_of_isProperMap 𝔰.besselGraphMeasure hj 1, show Continuous fun _ ↦ _ • _ •
    WithLp.toLp 2 (_ *ᵥ _) by fun_prop [simpleRootSum, wave], by simpa using congr(√‖$(hc 1)‖)
  have nf y s := show ‖f y s‖ₑ = ‖(_ : ℂ)‖ₑ by
    simp [f, ← ofReal_norm, norm_smul, v1, Unitary.norm_map]; rfl
  have hd y := (lintegral_decay_le 𝔰.besselGraphMeasure hj .refl (frameEquiv (x⁻¹ * y))).trans_eq'
    (by simp [besselPairHom, ← map_mul, mul_assoc, -Fintype.card_sum]; rfl)
  have hb y := (hd y).trans' (lintegral_mono fun _ ↦ by grw [← norm_dsCoeff_le_pow hG
    (by simp [gapThreshold]; norm_cast; lia), ofReal_norm, ← psiInFrame, ← nf])
  have iF y : Integrable _ _ := ⟨by fun_prop, (hb y).trans_lt (by finiteness)⟩
  have E s y := (integral_mul_right_eq_self (f (s.1.1 * y)) s⁻¹).symm.trans (.trans
    (by simp [f, wave, simpleRootSum_mul, Filling.simpleRootSum_inv, mul_assoc, smul_smul,
    ← exp_add]; congr! 5; ring) ((wave _ • (besselValueRep rep s.1.2).1).integral_comp_comm (iF y)))
  erw [← le_ofReal_iff_toReal_le C0 (by bound), (congrArg _ (by simp [← hc, besselPairHom,
    laplaceIntegrand, f, wave, inner_smul_right, ← Unitary.star_eq_inv, star, adjoint_inner_right,
    neg_add_eq_sub, mul_assoc, mul_comm (cexp _), psiInFrame])).trans (integral_inner (iF x) v),
    ofReal_mul' (norm_nonneg _)] at La
  grw [norm_inner_le_norm, v1, one_mul, ofReal_norm] at La
  exact ⟨_, ⟨⟨mf.stronglyMeasurable.integral_prod_right, _, (toReal_mono (by finiteness) <|
    (enorm_integral_le_lintegral_enorm _).trans <| hb ·)⟩,
    (by simpa using E <| 𝔰.besselGraphChart ⟨⟨·, ·⟩, 1⟩), (by
    simpa [simpleRootSum_eq_zero_of_mem_besselH, wave] using! E <| 𝔰.besselGraphChart ⟨1, ·⟩)⟩, by
    ext1; simp [convolve, ← integral_smul]
    rw [integral_integral_swap ⟨⟨_, by fun_prop, .rfl⟩, (lintegral_prod_le _).trans_lt _⟩]
    simp [f, smul_smul, ← mul_assoc, integral_smul_const, (by
      simpa [psiInFrame.eq_1 l 1, ne_of_gt, ← mul_assoc, mul_right_comm _ (ofReal _)] using
        (isIdempotentKernel_psiInFrame hG).integral_inv_mul_translate · 1)]
    simp [enorm_smul, lintegral_const_mul', -enorm_mul]
    grw [hb, lintegral_mul_const'] <;> finiteness [(isIdempotentKernel_psiInFrame hG).2.comp_inv.2],
    measure_sublevel_ne_zero _ ∘
    _root_.le_zero_iff.1 ∘ (La.trans_eq <| by simp [·]), by simp [enorm_integral_le_lintegral_enorm,
    ← nf], fun y ↦ by grw [hd, La, pow_add, ENNReal.ofReal_mul (by bound), b0, mul_assoc]⟩
