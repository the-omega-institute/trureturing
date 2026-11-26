/- GID: D5/S3/Zeros/GRH/New/Filling/StandardLevel
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Filling/StandardLevel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Filling.StandardLevel. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Filling/StandardLevel.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Filling.EichlerFlag
import D5.S3.Zeros.GRH.New.RealPlace.WeightPlancherel
import D5.S3.Zeros.GRH.Lib.Adelic.Adeles.FinitePlaceDensity
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

Set-up for this proof: general results applied to the objects of this proof.

Part of: Phase sums are sharply dominated by local Bessel kernels (see New.Filling.Moments).

This file: Finite place carries a level and gauges for the tower method; masses of K. -/

open Filter Fintype Level MatMul Matrix MeasureTheory NNReal Place Pointwise SemilocalField Sum
  Topology MeasureTheory.Measure

attribute [local simp] HyperbolicBasis.floorBasis Finset.mul_sum IsIntMatrix mul_mem
  IntegralPlace.data_mem flatChart IsStarStable.star_mem Size.HasMatSize Size.vecsOfSize
  ascConv funext_iff inclMatrix intVectors ite_mem mul_add mul_assoc sub_mem sum_mem

/-- The vector x − (ππ̄)⁻¹t z of X₀ ⊕ Az, for x in A^κ and t in A, written in the lattice basis. -/
noncomputable def tailVector {A : Type} {𝔰} [CommRing A] [StarRing A] (π : Aˣ) t x :=
  (besselLatticeBasis 𝔰 π)⁻¹.1 *ᵥ (0 ⊕ᵥ ((x ⊕ᵥ fun _ ↦ -(π * star π)⁻¹ * t) ⊕ᵥ 0))

variable {A ι : Type} {𝔰 : Shape} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A]
  [Fintype ι] {m : ℕ} {π : Aˣ} {N : A} [P : Place A] {t : A} {x : 𝔰.κ → A}

omit [TopologicalSpace A] [MeasureSpace A] [Place A] in
lemma form_tailVector (hN : π * star ↑π = N) : let J :=
    (latMiddleGram 𝔰 N).splitGram; let e := tailVector π t x; star e ⬝ᵥ
      J *ᵥ e = star x ⬝ᵥ x - (π * star π)⁻¹.1 * t * star t ∧ (J *ᵥ e) 𝔰.z = t := by
  simp [← gram_besselLatticeBasis π N hN, ← mulVec_mulVec, ← star_mulVec_dotProduct, tailVector]
  simp [besselLatticeBasis, splitGram, middleGram, entrywise]; grind [π.mul_inv, star_mul, star_one]

@[fun_prop] lemma continuous_tailVector : Continuous fun z : A × (𝔰.κ → A) ↦
  tailVector π z.1 z.2 := by simp [tailVector, mulVec_eq_sum]; fun_prop

/-- Slabs near the quadric h(e, e) = −N, N = ππ̄: for Φ ≥ 0 continuous of compact support and c
> ∫Φ dδ_{−N}, all small measurable S have ∬_{y*y − ττ̄/N + N ∈ S} Φ(y − τz/N) dy dτ ≤
md(π)·ν(δS)·c, ν on skew elements. -/
lemma HyperbolicBasis.eventually_mass_near_quadric_le [IsHermUnit (latMiddleGram 𝔰 N).splitGram]
  (F : HyperbolicBasis ι (latMiddleGram 𝔰 N) m) (hN : π * star ↑π = N) {Φ : _ → ℝ≥0} (hΦ :
  Continuous Φ) (cΦ : HasCompactSupport Φ) {c} (hc : ∫⁻ e, Φ e ∂F.floorQuadric 𝔰.top < c) : ∀ᶠ S in
  (𝓝 0).smallSets, MeasurableSet S → ∫⁻ τ, ∫⁻ y in {y | star y ⬝ᵥ y - ((π * star π)⁻¹ * τ * star τ -
  N) ∈ S}, Φ (tailVector π τ y) ≤ P.md π * P.skewMeasure {Γ | P.skewUnit⁻¹.1 * Γ ∈ S} * c := by
  filter_upwards [eventually_smallSets_forall.2
    (((continuous_sub_right N).const_mul skewUnit.1).tendsto' 0 _ (by simp [splitGram,
    latMiddleGram]) (eventually_comap.1 ((nhds_subtype ..).ge (((F.isDisintegration_floorVolume _
    rfl).continuousOn_lintegral hΦ cΦ).1.upperSemicontinuous _ _ hc))))] with S k mS
  grw [mul_right_comm, mul_assoc, ← measure_preimage_add_right _ (P.skewUnitMul _
    (star_mul_star π.1 π)), ← lintegral_indicator_const_le, ← lintegral_mono fun Γ ↦ ?_,
    ← (F.isDisintegration_floorVolume 𝔰.top (map_inclMatrix_eq_floorVolume (inr ∘
    inl))).lintegral_eq fun p ↦ S.indicator 1 (p.1 + N) * Φ p.2, lintegral_map,
    lintegral_eq_mul_lintegral_map ((P.map_mulVec_volume _ ((middleBaseChange 𝔰
    π).fromCols (fromRows 0 (-(π * star π)⁻¹.1 • 1))) _).trans _), lintegral_map,
    ENNReal.mul_inv_cancel_left, ← measurePreserving_sumElim.lintegral_comp, volume_eq_prod,
    lintegral_prod_symm, ← (volume_preserving_funUnique ..).symm.lintegral_comp] <;> try fun_prop
  simp (disch := measurability) only [← lintegral_indicator]
  gcongr with τ y; rw [(?_ : _ *ᵥ _ *ᵥ _ = tailVector π τ y)]
  any_goals simp +contextual [↓form_tailVector, tailVector, besselLatticeBasis, middleBaseChange,
    entrywise, apply_ite, ← mul_assoc, ENNReal.mul_inv_cancel, Set.indicator, sub_add, *]
  grind [skewUnit.mul_inv]

attribute [-simp] splitGram_eq_ite_oppositeIndex

variable {A : Type} [SemilocalField A] [StarRing A] [P : IntegralPlace A] {T :
  𝔰.Form A} [IsHermUnit T.splitGram] (F : Level ι T m)

/-- The principal congruence subgroup K(g) of the level: integral isometries congruent to 1
modulo the unit g of F. -/
noncomputable abbrev Level.congGroup := unitaryLevel O F.g T.splitGram

/-- F is the level of the lattice R^r: unimodular form, integral basis and g, box K, ball R^r,
positions y⁻¹uy·K(g) with u in 𝖴, μH(K) = 1, θ(K) ≥ vol R^×, and an isotropic u with h(u, ·)
the z-coordinate. -/
structure IntegralPlace.IsLatticeLevel where
  integral_data : IsUnimodular R T.splitGram ∧ IsIntMatrix R F.basisMatrix ∧ F.g.1 ∈ R ∧
    star F.g.1 = F.g
  box_eq : volume P.intUnits ≤ F.θ F.boxSet ∧ F.boxSet = unitaryLevel R 1 T.splitGram ∧
    F.measureH F.boxSet = 1 ∧ F.𝔅 = intVectors P.R 𝔰.BesselIndex ∧ F.positions =
    {y⁻¹ * u * y | (y) (u ∈ T.besselU)} * F.congGroup
  exists_isotropic : ∃ u, star u ᵥ* T.splitGram = Pi.single (𝔰.besselFrame 𝔰.top) 1 ∧
    u (𝔰.besselFrame 𝔰.top) = 0

/-- A lattice level with m+1 further hyperbolic pairs, ζ_R(m)^(ϱ+1) ≤ 1 + 2^(−ϱ−1), m < 9(ϱ+1)
and 13(ϱ+1) ≤ |ι|, in a unimodular unitary group. -/
class IntegralPlace.IsStdLevel (F : Level ι T (m + 1)) extends P.IsLatticeLevel F where
  zeta_rank : idealZeta P.R m ^ 𝔰.n ≤ .ofReal (1 + 2⁻¹ ^ 𝔰.n) ∧ m < 9 * 𝔰.n ∧ 13 * 𝔰.n ≤ card ι
  unimodular : ∃ ν : Measure T.G, ν.IsHaarMeasure ∧ ν.IsMulRightInvariant

variable {g : Aˣ} {F : Level ι T (m + 1)} [h : P.IsStdLevel F]

/-- At a finite place, for self-conjugate N in R and a self-conjugate unit g of A lying in R,
and |κ| = |ι| + 2m + 1, the form in the lattice basis has a lattice level
`IntegralPlace.IsLatticeLevel` of modulus g. -/
lemma IntegralPlace.exists_isLatticeLevel {N} [IsHermUnit (latMiddleGram 𝔰 N).splitGram] (hN :
  N ∈ R ∧ star N = N) (hg : g.1 ∈ R ∧ star g.1 = g) (hm : 𝔰.k = card ι + 2 * m + 1) : ∃ F :
  Level ι (latMiddleGram 𝔰 N) m, P.IsLatticeLevel F ∧ F.g = g := by
  obtain ⟨⟨c, hc, e⟩, u, f⟩ := P.isAdelic.exists_norm_neg_one, isUnimodular_latMiddleGram 𝔰 hN,
    (equivOfCardEq (by simp +arith [hm]) : SplitIndex m ι ≃ {i // 𝔰.k₀ ≠ i})
  let E := inclMatrix A (![inl 𝔰.k₀, inr ()] ⊕ᵥ (inl <| f ·)) * @fromBlocks _ (SplitIndex m ι) _
    (SplitIndex m ι) A !![-1, -N * P.τ; 0, 1] 0 0 (fromBlocks 1 (fromCols 0 (P.τ • 1))
    (fromRows 0 (c • 1)) (fromBlocks 1 0 0 ((-star P.τ * c) • 1)))
  have hE : IsIntMatrix R E := .mul (by simp) (by simp [*])
  let F : HyperbolicBasis ι (latMiddleGram 𝔰 N) m := ⟨E, by
    rw [gram_mul, gram_inclMatrix]
    simp [entrywise, latMiddleGram, diagonal, (f _).2.symm, Subtype.val_inj]
    grind, by lia, by grind [md_det_eq_one, u.2]⟩
  let l := 𝔰.besselFrame 𝔰.top; let x : 𝔰.BesselIndex → A := Pi.single (𝔰.indexX₀ 𝔰.k₀) (-1)
  let J := (latMiddleGram 𝔰 N).splitGram; let φ p :=
    F.floorBasis 𝔰.top *ᵥ flatChart (hyperbolicGram _ 1) (P.skewUnitMul (J l l)) p
  obtain ⟨t, hx⟩ : (∀ p, φ p 𝔰.z = p.1.1) ∧ star x ᵥ* J = Pi.single l 1 ∧ x l = 0 :=
    by simp +zetaDelta [entrywise, splitGram, latMiddleGram, diagonal]
  have M := measurable_unitary_of_coe (f := fun p ↦
    U.of IsHermUnit.isUnit _ (exists_eichler_orbitPoint_eq (e := φ p) hx).1) (by fun_prop)
  have C := isClosed_of_entries_eq_one (J := J) (mem_floorGroup (l := 𝔰.n))
  have w := MeasurableEmbedding.subtype_coe C.measurableSet
  let ν : Measure besselH := .inv (haarMeasure ⟨⟨_, unitaryLevel_open_compact.2.inv.preimage_val
    C⟩, 1, by simp [unitaryLevel_open_compact.1.preimage_val.interior_eq]⟩)
  have n := (w.map_apply ν (unitaryLevel R 1 J)).trans ((inv_apply ..).trans haarMeasure_self)
  refine ⟨.mk F _ _ g _ _ _ (neZero_measureH := ⟨(by simp [·] at n)⟩) ⟨(ae_map_iff M.aemeasurable
    measurableSet_floorGroup).2 (.of_forall fun _ ↦ (exists_eichler_orbitPoint_eq hx).2.1 fun i
    k ↦ by simp [φ, ← mulVec_mulVec]; exact Finset.sum_eq_zero (by simp; grind [floorOf])),
    (Measure.map_map (by fun_prop) M).trans (.trans (Measure.map_congr
    ((quasiMeasurePreserving_fst.ae (quasiMeasurePreserving_fst.ae ae_isUnit)).mono fun p k ↦
    (exists_eichler_orbitPoint_eq hx).2.2 ?_ (by simpa [t])))
    (Measure.map_map (g := mulVec _) (by fun_prop) (by fun_prop)).symm)⟩ ⟨w.ae_map_iff.2 (by simp),
    fun s k ↦ (mconv_dirac ..).trans ((w.2.measurePreserving _).of_semiconj
    (measurePreserving_mul_right ν ⟨s, k⟩) (by tauto) (by fun_prop)).2, fun y ↦ by
    simp_rw [← n, w.map_apply]; exact measure_le_of_div_mem fun x ⟨v, b, c⟩ ↦ ⟨x, fun k ⟨w, e, f⟩ ↦
      mem_unitaryLevel_of_besselU_mul (mul_mem e ((besselS_le_normalizer_besselU
      (mem_unitriGroup_of_mem_floorGroup (k / x).2) _).1 (inv_mem b))) (k / x).2 (by
      simpa [div_eq_mul_inv] using div_mem f c)⟩⟩ hg.2 ⟨intVectors_open_compact_vol.1, by simp,
    intVectors_open_compact_vol.2.1.closure⟩ ⟨unitaryLevel_open_compact.2,
    unitaryLevel_open_compact.1.mul_left.measurableSet⟩, ⟨⟨u.splitGram, hE, hg⟩, ⟨.trans (by
    simp [intVectors_open_compact_vol, -intVectors]) ((measure_mono (s := (intUnits ×ˢ intVectors R
    _) ×ˢ {b | b.1 ∈ R}) ?_).trans (le_map_apply M.aemeasurable _)), by tauto⟩, x, hx⟩, rfl⟩
  · dsimp; erw [star_mulVec_dotProduct, mulVec_mulVec, mulVec_mulVec, F.gram_floorBasis,
      form_flatChart] <;> simp +zetaDelta [k]
  rintro ⟨⟨_, w⟩, b⟩ ⟨⟨⟨d, v, r, rfl⟩, y⟩, a⟩
  refine (fun c : ∀ i, φ ((v, w), b) i ∈ R ↦ u.splitGram.mem_unitaryLevel ?_ ?_) (IsIntMatrix.mulVec
    ?_ ?_) <;> simp (maxDischargeDepth := 19) [-sum_sum_type, entrywise, vecMulVec_apply, add_mem,
    vecMul, x, u.splitGram.isIntMatrix _, F, hE _, J, y _, a.out, *]

namespace IntegralPlace.IsStdLevel

/-- The gauge of depth α, for a self-conjugate unit α of A lying in R: x has size j if α^j x ∈
R, and Λ = 2/md(α). -/
@[simp] noncomputable def gauge (α : Aˣ := 1) (hα : α.1 ∈ R := by simp)
    (sα : star α.1 = α := by simp [*] <;> ring) : Gauge F := by
  have l := by simpa using ENNReal.div_le_div_left (md_le_one α hα) 2
  obtain ⟨J, c, _, G, o⟩ := h.integral_data.1.isIntMatrix, le_two_of_pow_le_ofReal h.zeta_rank.1,
    h.zeta_rank, h.integral_data.2, one_le_two.trans l
  have L j : (md (α ^ j).1)⁻¹ ≤ (2 / P.md α) ^ j := by grw [← one_le_two]; simp [ENNReal.inv_pow]
  have Z {j n k} (e : j * n + 1 ≤ k) := (mul_le_mul' (c.trans l) (pow_le_pow_left' (L j) n)).trans
    ((pow_le_pow_right' o e).trans_eq' (by ring))
  refine' { ofSize j := {x | α ^ j * x ∈ R}, Λ := 2 / P.md α, .. }
  rotate_right
  simp_rw -zeta [closePairs, h.box_eq]
  rintro x hx _ ⟨_, ⟨y, u, hu, rfl⟩, k, hk, rfl⟩ v W
  have σ : SplitIndex 𝔰.ϱ (Fin 𝔰.ϱ) ⊕ Fin (F.volumeExponent + (m + 5)) ≃ ι :=
    equivOfCardEq (by simp; lia)
  let N := (y * x⁻¹).1.1 * F.orthonormalPart
  obtain ⟨V, hV, z⟩ := valPair.exists_mul_clear_cols (v.fromRows
    (N ∘ inr ∘ inr ⊕ᵥ ((u⁻¹.1.1 - 1) * N) ∘ inl)) (.trans .inl σ.toEmbedding)
  let Y := V.1.submatrix id (σ ∘ inr)
  have w t (a : t ∈ intVectors R _) : Y *ᵥ t ∈ W := by
    have z a j := z a (σ (inr j)) (by simp)
    have r := hx.1.isIntMatrix_inv.mul (N :=
      F.orthonormalPart * Y) (by simp [mul_apply, G.1 _, Y, hV.isIntMatrix _])
    have : (u⁻¹.1.1 - 1) * N * Y = 0 := Matrix.ext (Sum.rec (z <| inr <| inr ·) fun i j ↦ by
      rw [Matrix.mul_assoc, mul_apply]
      simp [apply_inr_of_mem_besselU (inv_mem hu), -Subgroup.coe_inv, -InvMemClass.coe_inv,
        fun a ↦ show (N * Y) (eStar a) j = 0 from z (inr (inl a)) j])
    simp [N] at this
    simpa [*, W, ← smul_neg, (Matrix.ext (z <| inl ·) : v * Y = 0), -fromRows_mulVec] using!
      And.intro (r.mulVec a) (((inv_mem hk).2.mul r).neg.mulVec a)
  refine ⟨P.contentIndex 0 ∘ Yᴴ.mulVec, by fun_prop, fun u ↦ ⟨le_iInf (exists_content · |>.elim
    fun t ⟨r, a, b, f⟩ ↦ .trans_eq (ENNReal.inv_le_inv.2 (md_le_volume (u := star t) fun x k ↦
    ⟨_, w (x • star r) (by simp [k, a _]), by simp [← b, ← star_dotProduct_star, dotProduct_mulVec,
    star_vecMul, mul_comm]⟩)) (by simp [f])), le_iInf fun _ ↦ measure_mono fun c a i ↦ ?_⟩, fun j ↦
    (lintegral_contentIndex_pow_le c σ 0 _ hV ⟨rfl, card_fin _, by lia⟩).trans
    (Z (by simp; nlinarith))⟩
  have H {v w} (a : v ∈ intVectors R _) b : star v ⬝ᵥ T.splitGram *ᵥ w ∈ R :=
    sum_mem fun i _ ↦ mul_mem (isAdelic.1.1 (a i)) (J.mulVec b i)
  obtain ⟨_, ⟨a, b⟩, _, ⟨c, d⟩, e⟩ := a _ (w _ (single_mem_intVectors i))
  simpa [entrywise, mul_comm] using isAdelic.1.1
    ((e.trans (by simp [mulVec_sub, ← inverse_star_unit, G]; grind)).symm.subst
    (sub_mem (add_mem (H a d) (H b c)) (mul_mem G.2.1 (H b d))))
  exacts [(by grind [R.mul_mem · ·]), by simp_all [pow_succ'], ⟨by simp, by constructor
    <;> exact (by simpa [*] using isAdelic.1.1 ·)⟩, by simp [pow_mem hα], by simp_all
    [h.integral_data.1.isUnit_det_and_isIntMatrix_inv.2 _], (isCompact_O.preimage_smul <|
    α ^ ·), by lia, by simp [ENNReal.div_eq_top], by simp [*, G.1 _], by
    simp_all [h.box_eq, unitaryLevel, mem_intGL, -Sum.forall], by simp_all [h.box_eq], fun j u k ↦
    (L j).trans' (by simpa [mul_comm] using md_le_one (α ^ j * u) k),
    (L · |>.trans (by bound) |> (volume_setOf_mul_mem _).trans_le),
    fun σ _ j k n ↦ (quadricMeasure_cone_le c k _).trans (Z (by nlinarith))]

/-- For a standard level, a self-conjugate unit g in R, a < ϱ and a subgroup S of 𝒩_{<a}, the
set S·K(g) has η_a-mass md(g)^(k + 1 + 2(ϱ − a − 1) + 1/2), the number `Level.floorModulus`. -/
lemma heisenbergMeasure_eq_floorModulus (hg : g.1 ∈ R ∧ star g.1 = g) (a : Fin 𝔰.ϱ) {S} (hS : S ≤
  unipotentBelow a) : heisenbergMeasure a {y | ∃ u ∈ S,
  u * (y * 1) ∈ unitaryLevel R g T.splitGram} = F.floorModulus a g := by
  rw [heisenbergMeasure, dite_eq_left a.2, map_apply (by fun_prop)
    measurableSet_exists_mul_mem_level,
    (Set.ext fun p ↦ ?_ : _ ⁻¹' _ = Set.univ.pi (fun _ ↦ {x | g⁻¹.1 * x ∈ R}) ×ˢ _), prod_prod,
    skewMeasure_setOf_mul_mem g⁻¹ (by simp [← inverse_star_unit, *])]
  simp [volume_pi_pi, floorModulus, ↓card_succ_le_floorOf, ENNReal.inv_rpow]
  obtain ⟨w, e⟩ := MulAction.surjective g (inclMatrix A Subtype.val *ᵥ p.1)
  rw [Set.mem_prod, show p.1 ∈ _ ↔
    g⁻¹.1 • g • w ∈ intVectors R _ by simp [e, inclMatrix_val_mulVec, dite_mem, -inclMatrix]]
  refine ⟨fun ⟨u, b, k⟩ ↦ (h.gauge.mem_vecsOfSize_of_heisenbergElem (i := 0) ⟨u, hS b,
    (by simpa using! k.2 · _)⟩).elim ?_,
    (⟨1, S.one_mem, h.integral_data.1.mem_unitaryLevel hg.1 <| ·.elim ?_⟩)⟩ <;> simp +contextual
    (maxDischargeDepth := 19) [-Sum.forall, -sum_sum_type, TraceOne.heisenbergElem, eichlerMap,
    vecMulVec, Units.smul_def, ← mul_assoc, ↓← e, hg, mul_right_comm _ _ g.1, sub_eq_add_neg,
    add_mem_cancel_right, vecMul, mulVec, dotProduct, add_assoc, h.integral_data.1.isIntMatrix _]

lemma ascConv_unitaryLevel (hg : g.1 ∈ R ∧ star g.1 = g) j : j ≤ 𝔰.ϱ →
  ascConv heisenbergMeasure j (SetLike.coe (unitaryLevel R g T.splitGram)) = ∏ l ∈ .range j,
  F.floorModulus l g := j.rec (by simp) fun j i a ↦ by rw [Finset.prod_range_succ, ← i (by lia),
  ← heisenbergMeasure_eq_floorModulus hg ⟨j, a⟩ le_rfl, ← ascConv_mconv_unfolding]; simp

lemma unfold_besselU {c} {θ : Measure T.G} [SFinite θ] (hg : g.1 ∈ R ∧ star g.1 = g) :
    (ascConv heisenbergMeasure (𝔰.ϱ + 2) ∗ₘ θ) {y | y * c ∈ unitaryLevel R g _} =
  (∏ l ∈ .range 𝔰.ϱ, F.floorModulus l g) * θ {y | ∃ u ∈ T.besselU, u * (y * c) ∈ unitaryLevel R g
  _} := by simp [↓ascConv_mconv_unfolding, unipotentBelow_eq_besselU, h.ascConv_unitaryLevel hg]

/-- For a standard level F at a finite place, the group K of integral isometries has measure
M(K) at most 1 + 2^(−(ϱ+1)). -/
lemma groupMeasure_boxSet_le : F.groupMeasure F.boxSet ≤ .ofReal (1 + 2⁻¹ ^ 𝔰.n) :=
  h.zeta_rank.1.trans' (.trans (by simpa [h.box_eq, floorModulus, IsNear, stackMeasure_zero_eq]
  using (h.unfold_besselU (g := 1) (c := 1) (by simp)).le) (F.upperMeasure_isNear_le
  (h.gauge.floorMassLe_one · (Gauge.hasFibreBound_floorQuadric_of_le
  (quadricMeasure_cone_le (le_two_of_pow_le_ofReal h.zeta_rank.1) (by simp) (1 ^ _))) ·
  |>.trans_eq (by simp [volume_O])) 0 1))

/-- For a standard level at a finite place with integers R and l + i = ϱ, the measure
`Level.stackMeasure` l (i+2) of U(V_l) gives the group K of integral isometries mass at least
vol(R^×)^(i+1). -/
lemma le_stackMeasure_boxSet i l (c : l + i = 𝔰.ϱ) : volume P.intUnits ^ (i + 1) ≤
  F.stackMeasure l (i + 2) F.boxSet := h.box_eq.elim fun v ⟨B, n, _⟩ ↦ by
  have k σ θ [SFinite θ] : σ F.boxSet * θ F.boxSet ≤ (σ ∗ₘ θ) F.boxSet := (prod_prod ..).ge.trans
    ((measure_mono fun _ ↦ by simp_all).trans (le_map_apply (by fun_prop) _))
  induction' i with i ih generalizing l
  simpa [descConv, floorMeasure, ← c] using (mul_le_mul' n.ge v).trans (k ..)
  have := by simpa [floorModulus, ← B] using
    h.heisenbergMeasure_eq_floorModulus (g := 1) (by simp) ⟨l, by lia⟩ bot_le
  grw [pow_succ, stackMeasure, descConv, ← k, ← ih _ (by lia), ← k, floorMeasure,
    ite_eq_left (by lia), ← k, this, one_mul, mul_one, ← le_map_apply (by fun_prop), B,
    ← withDensity_apply_le, ← meas_le_lintegral₀ (by fun_prop), restrict_eq_self] <;> rintro _ ⟨d,
      c, b, rfl⟩
  exacts [inv_mem (h.integral_data.1.mem_unitaryLevel R.one_mem (by simp [floorWeyl, weylOn, *])),
    one_le_pow₀ (by simpa using md_le_one _ b)]

instance isHaarMeasure_groupMeasure : F.groupMeasure.IsHaarMeasure := h.unimodular.elim fun ν ⟨_,
  _⟩ ↦ (exists_eq_smul_haar ν F.isMulRightInvariant_groupMeasure).elim fun d e ↦ e ▸ .smul _ (by
  simp [·, stackMeasure_ne_zero] at e) (by simpa [e, ·, h.box_eq,
  unitaryLevel_open_compact.1.measure_ne_zero ν] using h.groupMeasure_boxSet_le)
