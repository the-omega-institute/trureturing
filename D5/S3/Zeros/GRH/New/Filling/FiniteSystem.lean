/- GID: D5/S3/Zeros/GRH/New/Filling/FiniteSystem
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Filling/FiniteSystem
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Filling.FiniteSystem. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Filling/FiniteSystem.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Filling.FixedLines
import D5.S3.Zeros.GRH.Lib.SiegelWeil.OneVector.OneVector
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Phase sums are sharply dominated by local Bessel kernels (see New.Filling.Moments).

This file: One-sided Siegel formula at T; top kernel dominates phase sums nearly sharply. Finite
places carry a local system with sharp bottom value and frequency bounds. -/
seal Finset.univ Finset.sum Finset.prod

open Complex ENNReal Filter Finset Matrix MeasureTheory NNReal OpenAddSubgroup IntegralPlace
  Topology IsStdLevel

/-- At a finite place, let H ≤ GL_n(R) and f ≥ c_z on the H-orbits of all vectors near p_z, z in
a finite set s. Then some compactly supported Φ ≤ f, invariant under H and small
translations, has Φ(p_z) ≥ c_z on s. -/
lemma Filling.exists_step_function {A n : Type} [SemilocalField A] [StarRing A] [P : IntegralPlace
  A] [Fintype n] {G H ι} {p : ι → _} {f : _ → ℝ≥0∞} {s : Finset ι} {c : ι → ℝ≥0} (hf : ∀ z ∈ s, ∀ᶠ
  x in 𝓝 (p z), ∀ k ∈ H, ∀ y, k.1.1 *ᵥ y = x → c z ≤ f y) (i : H ≤ (intGL n P.R).subgroupOf G) :
  ∃ Φ : _ → ℝ≥0, HasCompactSupport Φ ∧ (∀ᶠ v in 𝓝 0, ∀ x, Φ (x + v) = Φ x) ∧
  (∀ k ∈ H, ∀ x, Φ (k.1.1 *ᵥ x) = Φ x) ∧ (∀ x, Φ x ≤ f x) ∧ ∀ z ∈ s, c z ≤ Φ (p z) := by
  obtain ⟨_, e, u, rfl⟩ := mem_closure_iff_nhds.1 (Measure.dense_of_ae P.ae_isUnit 0) _
    (s.eventually_all.2 fun z k ↦ P.intVectors_open_compact_vol.2.1.eventually_forall_mem (fun b r ↦
    (_ + b • r, b • (p z + b • r))) _ fun _ _ ↦
    prod_mem_nhds (by simpa using! hf z k) (P.intVectors_open_compact_vol.1.mem_nhds (by simp)))
  replace e z k x := e z k (u⁻¹ • (x - p z))
  have M (k : H) (b : Aˣ) x := k.1.1.1.mulVec_smul b x ▸ mulVec_mem_intVectors_iff (i k.2)
  simp [← Units.smul_def] at e M
  use fun x ↦ {z ∈ s | ∃ k : H, u⁻¹ • (k.1.1.1 *ᵥ x - p z) ∈ intVectors R n}.sup c, .intro
    (P.intVectors_open_compact_vol.2.1.smul u⁻¹) ?_,
    ((P.intVectors_open_compact_vol.1.preimage (continuous_const_smul u⁻¹)).eventually_mem ?_).mono
    (by simp +contextual [add_sub_right_comm, add_mem_cancel_right, M]), fun k l x ↦ sup_congr
    (s.filter_congr fun z _ ↦ (Equiv.mulRight ⟨k, l⟩).exists_congr ?_) ?_, ?_, fun z k ↦ le_sup
    (s.mem_filter.2 ⟨k, 1, ?_⟩) <;> simp_all [Set.mem_inv_smul_set_iff] <;> grind

namespace Filling.IsFillingLevel

variable {E 𝔰} [Field E] [CMType E] [WeilData E] {S : Filling E 𝔰} [ok : S.IsAdmissible] {T :
  Finset _} [T.StarStable] [Fact (↑S.gIdele⁻¹ ∈ integralOff T)] (hT :
  S.latBasis ∈ intGL _ (integralOff T) ∧ (↑S.N)⁻¹ ∈ ratIntegralOff T) [P :
  IntegralPlace (LocProd T)] {F} (hF : S.IsFillingLevel T F) {π : Side} {Z : F.IntermediateGroup}
include hT hF

/-- Siegel's formula at T. Let |t|_v > N for all v, and let finitely many (class, y), Ny*y = tt̄ −
N², h⁻¹y integral off T, have weights c bounding f below on H∩K(g)-orbits near their points. For
small compact open L: ∑c·vol L ≤ (1+b⁻⁶)·#Cl·`Filling.siegelConst`·∏_v(|t|_v² −
N²)^(|κ|−1)·∫_{h(z,e)∈t+L} f. -/
lemma siegel_sum_le_lintegral_quadric {f s} {t : E} (ht : ∀ v, S.N ^ 2 < ‖Φ v t‖ ^ 2) {c :
  _ → ℝ≥0} : let x (z : S.Classes × _) := z.1.out⁻¹.1.1 *ᵥ (↑) ∘ z.2
  (∀ z ∈ s, (S.N * star z.2 ⬝ᵥ z.2 = t * star t - S.N ^ 2 ∧ ∀ i, x z i ∈ integralOff T) ∧ ∀ᶠ e in 𝓝
    (evalPlaces T ∘ tailVector S.piBar t (x z)), ∀ k ∈ besselH ⊓ F.congGroup, ∀ y, k *ᵥ y = e →
    ↑(c z) ≤ f y) → ∀ᶠ L in (𝓝 0).smallSets, IsClopen L → (∑ z ∈ s, ↑(c z)) * volume L ≤ .ofReal
    ((1 + S.b⁻¹ ^ 6) * Fintype.card S.Classes * S.siegelConst * (∏ v,
    (‖Φ v t‖ ^ 2 - S.N ^ 2)) ^ (𝔰.k - 1)) * ∫⁻ e,
    {e | ((S.latMiddle _).splitGram *ᵥ e) (𝔰.besselFrame 𝔰.top) - ratToPlaces T t ∈ L}.indicator f e
    ∂F.floorQuadric 𝔰.top := fun hs ↦ if y0 : ∑ z ∈ s, (c z : ℝ≥0∞) = 0 then by simp [y0] else by
  obtain ⟨N0, ⟨_, d⟩⟩ := S.N_prime.pos, S.ϱ_le_k.dest
  set β := (t * star t - S.N ^ 2) / S.N
  set t' := evalPlaces T t
  let π : (LocProd T)ˣ := S.piBar.map (evalPlaces T)
  have sβ : star β = β := by simp [β, field]
  obtain ⟨u, hN : π * star π.1 = _⟩ := P.md_evalPlaces_rpow_half (x := .mk0 _ (by simp)) ⟨by simp,
    hT.2⟩, by simpa using! congr(evalPlaces T $S.piBar_mul_star)
  have p v : 0 < (Φ v β).re := by simpa [β, mul_conj', sq, N0] using ht v
  obtain ⟨Ψ, cf, uf, hk, h2, hy⟩ := exists_step_function (hs · · |>.2) fun _ ↦ (·.2.1)
  let n := LocallyConstant.indicator ⟨(Ψ <| tailVector π t' <| evalPlaces T ∘ ·),
    .comp_continuous (isLocallyConstant_of_eventually_add uf) (by fun_prop)⟩ (isClopen
    ⟨(intVectors ..).toAddSubgroup, isOpen_intVectors (isOpen_integralOff T)⟩)
  have cs : HasCompactSupport n := .of_support_subset_isCompact ((cf.image (f := fun e i ↦
    adeleOfLocal T (((besselLatticeBasis 𝔰 π).1 *ᵥ e) (𝔰.indexX₀ i))) (by fun_prop)).add
    stdLattice.isCompact_stdLattice)
    (Set.support_indicator.trans_le fun x ⟨a, h⟩ ↦ ⟨_, ⟨_, subset_closure h, rfl⟩, _,
    (by simpa [tailVector, sub_adeleOfLocal_mem_iff] using a ·), add_sub_cancel ..⟩)
  obtain ⟨sm, key⟩ := classSum_norm_eq (by lia) S.columnLevel n (fun k l x ↦
    if_congr (mulVec_mem_intVectors_iff (by clear * - l; grind [mem_intGL,
    mem_Ô_iff T, show k.1 ∈ intGL _ _ from S.hasFiniteType_columnLevel.1 l])) (.trans
    (congrArg Ψ (by rw [tailVector_evalPlaces,
    tailVector_evalPlaces]; ext1; erw [← RingHom.map_mulVec]; simp [tailVector, inclHFin,
    toLatBasis, ← mulVec_mulVec, mulVec_mulVec _ (besselLatticeBasis ..).1, toBesselH,
    fromBlocks_mulVec])) (hk (S.toPlaces T _) ⟨(inclHFin_mem_besselH k).map_mem_unitriangularOn _,
    (hF.mem_principalLevel_iff.1 (ok.columnLevel_eq.le l)).2⟩ _)) rfl) cs sβ p
  generalize eC : ofReal (_ * _) = C at key
  let r := ENNReal.ofReal ((1 + S.b⁻¹ ^ 6) / (1 + 2⁻¹ ^ 𝔰.n))
  replace hy := (ENNReal.mul_lt_mul_left y0 (by simp) (by
    grw [one_lt_ofReal, one_lt_div (by positivity), ← pow_six_le, pow_succ]
    bound)).trans_le (mul_le_mul_right (congr(‖$key‖ₑ).le.trans' (by
    simp_rw [classSum_eq_sum, ← NNReal.coe_sum, enorm_eq_nnnorm, nnnorm_real, nnnorm_eq,
      coe_finsetSum, ENNReal.coe_tsum (sm _)]
    grw [← ENNReal.tsum_prod.trans (tsum_fintype _), ← ENNReal.sum_le_tsum s]
    gcongr with z k
    grw [ite_eq_left (by simp [β, ← (hs z k).1.1]), hy z k, ← tailVector_evalPlaces]
    exact (ite_eq_left (hs z k).1.2).ge)) r)
  obtain ⟨nz, K0 : r * ‖C‖ₑ * (.ofReal (1 + 2⁻¹ ^ 𝔰.n) * volÔ E ^ 𝔰.k) * P.md π ≠ ∞⟩ := by
    simpa using hy.ne_zero, by simp [r, mul_eq_top]
  have iF := Integrable.of_integral_ne_zero nz.2.2
  let b τ := (π * star π)⁻¹.1 * τ * star τ - S.N - ratToPlaces T β
  obtain ⟨_, _, ha, _, hb, h⟩ := (isLocallyConstant_of_eventually_add uf).continuous,
    eventually_prod_iff.1
    (nhds_prod_eq.ge ((ENNReal.Tendsto.const_mul ((tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝 (0, t')) _ (.of_forall fun p ↦ (iF.1.mul (Continuous.aestronglyMeasurable (.subtype_val
    (f := fun z : selfAdjoint _ ↦ ψf E ((2⁻¹ : E) * (z.1 * -adeleOfLocal T (b p.2)))) (by fun_prop))
    )).indicator (isOpen_codifferent E p.1).measurableSet) (by simp [(norm_indicator_le_norm_self ..
    ).trans_eq]) iF.norm (.of_forall fun z ↦ .congr' (((isOpen_Ô.preimage (by fun_prop)
    ).eventually_mem (by simp)).mono fun p l ↦ .symm (ite_eq_left fun _ ↦ ψf_of_mem ∘ mul_mem l))
    (Continuous.tendsto' (.const_mul (.subtype_val (by fun_prop)) _) _ _ (by simp [show b t' = 0 by
      rw [sub_eq_zero, sub_eq_iff_eq_add, mul_assoc, Units.inv_mul_eq_iff_eq_mul]
      simpa [t', hN] using congrArg (ratToPlaces T) (by field :
      t * star t = S.N * (β + S.N))])))).const_mul _).enorm (by simp [r])).eventually_const_lt hy))
  simp only [integral_indicator (isOpen_codifferent ..).measurableSet, Pi.mul_apply,
    ← integral_mul_const, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← mul_add,
    sub_add, sub_neg_eq_add, one_mul] at h
  filter_upwards [eventually_smallSets_forall.2 (.and ((map_add_left_nhds_zero t').le hb) ((by
    fun_prop : Continuous (tailVector π · 0)).tendsto' 0 0 (by simp [tailVector, ← Pi.zero_def])
    uf))] with L hL oL
  refine (le_mul_of_forall_lt (by simp [add_pos, nz]) (.inl K0) fun a k c hc ↦
    ?_).trans (mul_le_mul' (ofReal_toReal K0 ▸ ofReal_le_ofReal (le_of_eq ?_)) (lintegral_mono
    fun e ↦ (ENNReal.coe_indicator ..).trans_le (Set.indicator_le_indicator (h2 e))))
  · obtain ⟨V, hV, d⟩ := eventually_smallSets.1 (F.eventually_mass_near_quadric_le hN ((oL.preimage
      (by fun_prop)).continuous_indicator ‹_›) (cf.mono (by simp)) hc)
    choose M M0 ha hV using
      mem_nhds_zero_finAdele_iff.1 (ha.and ((continuous_evalPlaces T).tendsto 0 hV))
    obtain ⟨⟨u, i⟩, o, z⟩ := (isUnit_natCast_finAdele (E := E) M0).exists_right_inv,
      Fact.mk ((isCompact_codifferent E (isUnit_natCast_finAdele M0)).measure_lt_top (μ := volume)),
      idealZeta_intAdeles_pow_le 𝔰.ϱ.succ (S.degree_le.trans' (Nat.mul_le_mul_right _ 𝔰.ϱ.succ_pos))
    obtain ⟨v, _, hv, sp⟩ := P.mass_near_quadric_off_places_le i (sβ ▸ star_algebraMap_finAdele β :)
      (le_two_of_pow_le_ofReal z) (by omega : _ ≤ 𝔰.k)
    grw [← k.le, ← setLIntegral_const, setLIntegral_mono' oL.2.measurableSet fun τ l ↦ ?_,
      setLIntegral_le_lintegral, lintegral_const_mul', (lintegral_add_left_eq_self _ t').trans_le
      (d _ (fun a l ↦ by simpa [↓adeleOfLocal_evalPlaces_mul, ← mul_assoc, i] using hV (adeleOfLocal
      T (evalPlaces T u * a)) (by simpa [↓mem_Ô_iff T, ↓adeleOfLocal_mem_integralOff]))
      (measurable_const_mul (evalPlaces T u) SemilocalField.isCompact_O.measurableSet))]
    rotate_right
    grw [(h (ha 1 (by simp)) (hL _ l).1).le, enorm_mul, mul_one]
    erw [enorm_integral_codifferent i ?_
      (by simpa using isFiniteMeasure_withDensity_ofReal ((n.2.comp
      toReal).continuous.integrable_of_hasCompactSupport (cs.comp_left rfl)).2),
      withDensity_apply', funext (ENNReal.coe_indicator _ _), sp _ (Ψ <| tailVector π t' ·) (by
      fun_prop), add_sub_cancel, lintegral_congr fun y ↦ ?_]
    · simp_rw [← mul_assoc]; rfl
    · rw [← (hL _ l).2, Set.indicator_of_mem (by simpa [t', form_tailVector hN]), tailVector,
        tailVector, ← mulVec_add]; congr; simp [funext_iff, mul_add]
    simp [b, sβ, ← adeleOfLocal_star, -Units.val_inv_eq_inv_val, ← Units.coe_star_inv]; ring_nf
    grw [← z, pow_one, ← hv]; simp; ring_nf; rfl
    simp [r, mul_eq_top, o.1.ne, *]
  simp [← hN, ← sq, ← ENNReal.rpow_natCast_mul] at u
  clear * - p eC d N0 u
  simp (disch := positivity) [r, u, ← eC, classSum_eq_sum, abs_of_nonneg, abs_of_pos (p _)]
  simp [siegelConst, β, mul_conj', sq, div_pow, ← d, mul_add, prod_pow]
  field

/-- Take distinct (c, c', n̄, γ), γ fixing all e_a, e*_a, h(z,γz) = t, |t|_v > N at every v,
n_T ∈ Z, integral off T, with common Gram matrix R of the ρ_p·besselCorrelation(w_pγ),
ρ_p·headDensity = r√G, G = ∏_v(|t|_v² − N²)^(k−1). For small compact open L ∋ 0: ∑‖r∑_p
cosetAmplitude(w_pγ)‖² ≤ (1+b⁻⁶)·packetConst·Re ∑R_pq·topKernel(p,q)/(vol L·massRatio).

Phase sums are sharply dominated by local Bessel kernels. -/
lemma sum_blocks_le_topKernel {T₀ : Finset _} {j} [Fintype j] {c c' : j → _} {γ : j → S.G E} {n :
  j → _} {t : Eˣ} (h : (fun i ↦ (c i, c' i, S.reduction (n i), γ i)).Injective) (hu : ∀ i, γ i ∈ GT
  𝔰.ϱ) (hs : ∀ i, S.frameProducts (γ i) 𝔰.top 𝔰.top = t) (ht : ∀ v, S.N ^ 2 < ‖Φ v t.1‖ ^ 2) (hn :
  ∀ i, S.toPlaces T (n i) ∈ Z.1) (ho : ∀ i, S.IsIntegralOff T (S.termPosition (c i) (c' i) (γ i)))
  (i : j) {R : Matrix _ _ ℂ} {ρ : _ → ℝ} {r} : let a (p : Fin 𝔰.ϱ → T₀) := padTuple (p · |>.1) t
  let ω p := Units.map (ratToPlaces T) ∘ a p
  let y i := r ^ 2 * ‖∑ p,
    S.cosetAmplitude T (c i) (S.reduction (n i)) (c' i) (weylElem 𝔰.ϱ (a p) * γ i)‖ ^ 2
  let G := (∏ v, (‖Φ v t.1‖ ^ 2 - S.N ^ 2)) ^ (𝔰.k - 1)
  (∀ i, R = .gram ℂ fun p ↦ ρ p • besselCorrelation volume (.toLp 2 <| S.besselFn ·) (S.ratToInf
    (weylElem 𝔰.ϱ (a p) * γ i))) → (∀ p, ρ p * (F.headDensity 𝔰.ϱ (ω p) 1).toReal = r * √G) →
    (∀ i p, S.IsIntegralOff T (S.termPosition (c i) (c' i) (weylElem 𝔰.ϱ (a p) * γ i))) → ∀ᶠ L in
    (𝓝 0).smallSets, IsOpen L ∧ IsCompact L ∧ 0 ∈ L → ∑ i, y i ≤ (1 + S.b⁻¹ ^ 6) * S.packetConst *
    (∑ p, ∑ q, R p q * (F.topKernel L Z (ω p) (ω q) / volume.real L / Z.massRatio.toReal)).re := by
  intro a ω y G hR w hw
  choose A hA using fun i (b : Z.Cosets) ↦ Z.exists_coset (mul_mem (inv_mem (hn i)) b.out.2)
  choose hL hv hN _ using fun i ↦ hs i ▸ termPosition_floorGroup_spec (hu i) (c i) (c' i)
  obtain ⟨D, _, eD, f⟩ : ∃ D > 0, S.packetConst = D * _ * _ ∧ Z.massRatio ≤
    F.measureH F.congGroup * (F.groupMeasure F.congGroup ^ 2 * Fintype.card Z.Cosets) * .ofReal D :=
    ⟨_, S.of_size_bounds (by intros; positivity), rfl, div_le_of_le_mul (by
    grw [measure_mono (t := ⋃ c : Z.Cosets, (· * c.out.1⁻¹) ⁻¹' F.congGroup) fun _ h ↦
      (Z.exists_coset h).elim (by simp +contextual), measure_iUnion_fintype_le,
      ← mul_one (F.groupMeasure _), one_le_pow₀ hF.g_pow_mul_unipotentMass.ge,
      ← mul_one (_ * _ ^ 2), hF.box_eq.2.2.1.ge, hF.box_eq.2.1, ← hF.card_reducedImage_mul (B :=
      besselH ..) (F.measureH_spec.1.mono fun z a ↦ (exists_toPlaces_eq z).imp
      (by clear * - a; grind)) fun _ h ↦ F.measureH_spec.2.1 _ (h.map_mem_unitriangularOn _)]
    simp [-Nat.cast_mul, ↓card_reducedImage_besselS]; push_cast; ring_nf; rfl)⟩
  have : 0 < G := by simp [G, *, prod_pos]
  let g i := (c i, fun j ↦ (γ i).1.1 (𝔰.indexX₀ j) 𝔰.z)
  refine (hF.siegel_sum_le_lintegral_quadric hT ht (s := univ.image g) (c := fun z ↦
    (.ofReal G * (Z.massRatio / .ofReal D) * ∑ k with g k = z, .ofReal (y k)).toNNReal)
    (forall_mem_image.2 fun k₀ _ ↦ ⟨⟨hN _, ((mulVec_mem_intVectors_iff (inv_mem hT.1)).1
    (Set.mem_of_eq_of_mem (hv _).symm (by simpa [orbitPoint] using (ho k₀).isIntMatrix · _)) <|
    𝔰.indexX₀ ·)⟩, ?_⟩)).mono fun L k ⟨p, q, z⟩ ↦ by
    obtain ⟨⟨⟨o⟩, l⟩⟩ := lintegral_energy_le_topKernel Z ω p (hR i ▸ posSemidef_gram ..)
      (fun _ ↦ by simp [ω, a, padTuple]; rfl), (massRatio_ne_zero_and_ne_top Z).elim toReal_pos,
      toReal_pos (p.measure_ne_zero volume ⟨_, z⟩) q.measure_ne_top
    replace k := toReal_mono (by finiteness) ((k ⟨q.isClosed, p⟩).trans (mul_le_mul_right l _))
    simp (disch := finiteness) only [toReal_sum, toReal_mul, coe_toReal, coe_toNNReal_eq_toReal,
      toReal_ofReal, toReal_div, siegelConst, ← mul_sum] at k
    rw [sum_fiberwise_of_maps_to (by simp), mul_right_comm, ← siegelConst] at k
    exact le_of_mul_le_mul_left
      (k.trans_eq (by simp [← mul_div_assoc, ← Finset.sum_div, eD, Measure.real]; field))
        (by positivity)
  refine eventually_sum_packets_le_energy Z ω Units.isOpen (NormedRing.inverse_continuousAt 1) ⟨⟨k₀,
    rfl⟩, ⟦1⟧⟩ (n := fun (i, b) ↦ (b, A i b)) (fun θ : {k // g k = g k₀} × Z.Cosets ↦
    ⟨inv_mem (x := S.toPlaces T _) (.map_mem_unitriangularOn _ (hL θ.1)), ?_⟩) ?_ |> fun z ↦ by
    peel z
    grw [← this, coe_toNNReal_le_self, div_le_of_le_mul f, sum_subtype _
      mem_filter_univ, Fintype.sum_prod_type, mul_sum, mul_sum]
    congr! 1 with k
    simp only [ω, hR k, star_dotProduct_gram_mulVec, @smul_comm ℂ ℝ,
      hF.correlation_smul_eq_cosetAmplitude
      (hu k) (hw ..) ((hA ..).2 rfl), y, smul_smul (ρ _), w, ← smul_sum]
    simp (disch := positivity) [norm_smul, ← Complex.ofReal_pow, mul_pow, Measure.real,
      ofReal_toReal (hF.groupMeasure_ne_top unitaryLevel_le_unitaryLevel_one)]; ring
  · simp_rw [← θ.1.2, g, ← hv]; simp [orbitPoint]; rfl
  rintro ⟨⟨i, q⟩, b⟩ ⟨⟨k, q'⟩⟩ l e
  obtain ⟨⟨rfl, f⟩, q, e⟩ := by simpa [g, funext_iff] using And.intro e (q.trans q'.symm)
  have x := unitriGroup_inf_floorGroup_last.le (inv_mul_mem_of_orbitPoint_eq (hu i) (hu k)
    (by simpa [funext_iff, Unique.forall_iff, orbitPoint, floorGroup_apply (hu
    _), e, frameGram, splitGram, mul_apply, middleGram] using (hs k ▸ hs i :)))
  obtain ⟨z, ⟨m⟩⟩ := eq_and_mem_classUnip_of_besselS (mem_unitriGroup_of_mem_floorGroup x)
    (by simpa [termPosition, q, mul_assoc] using
    (hF.mem_principalLevel_iff (x := _⁻¹ * _).2 ⟨mul_mem (inv_mem (ho i)) (ho k), by simpa⟩))
  simpa using h congr(($q, $z, $((hF.reduction_eq_iff ..).2
    (by simpa using div_mem ((hA i b _).2 rfl) ((hA k b _).2 f))), $(inv_mul_eq_one.1
    (eq_one_of_mem_floorGroup_inf ⟨x, (unipotentBelow_eq_besselU le_rfl).ge m⟩ (by simp)))))

end Filling.IsFillingLevel

open ComplexOrder Level

/-- Let 1/g be integral off T. Some K(g) ≤ Z ≤ K contains k_T whenever k ∈ K reduces into
`Filling.fixingSet` Sg d, and for every compact open subgroup L the normalised forms
`Level.floorForm`, `Level.topKernel` of Z form a `SieveSystem` with bottom bound
(1 + b⁻⁶)/b^(6|κ||Sg|).

Phase sums are sharply dominated by local Bessel kernels. -/
lemma Filling.IsFillingLevel.exists_finite_sieveSystem {E 𝔰} [Field E] [CMType E] [WeilData E] {S :
  Filling E 𝔰} [S.IsAdmissible] {T : Finset _} [T.StarStable] {P : IntegralPlace (LocProd T)} {F}
  (hF : S.IsFillingLevel T F) Sg d [Fact (↑S.gIdele⁻¹ ∈ integralOff T)] : ∃ Z, (∀
  k, S.reduction k ∈ S.fixingSet Sg d → S.toPlaces T k ∈ Z.1) ∧ ∀ L : OpenAddSubgroup (LocProd T),
  IsCompact L.carrier → SieveSystem unitOrOne (ratToPlaces T S.g⁻¹ * ·⁻¹.1) 𝔰.ϱ (fun j p q ↦ (if j ≤
  𝔰.ϱ then F.floorForm j p q Z.besselVector 1 else F.topKernel L Z p q / volume.real L.carrier) /
  Z.massRatio.toReal) (S.charOnPlaces T) ((1 + S.b⁻¹ ^ 6) / (S.b ^ (6 * 𝔰.k)) ^ #Sg) (finHeadWeight
  (𝔰.n ^ 6)) (S.frequencyGain T) := (hF.exists_intermediateGroup_lines Sg d).imp fun Z ⟨hm, hk⟩ ↦ by
  obtain ⟨n, _, _, Γ, C⟩ := S.pow_chain, S.k_le_f, S.one_le_b, hF.gauge, isCut_besselVector Z
  have N {x : ℂ} {D} d h : ‖x / Z.massRatio.toReal‖ ≤ _ :=
    (toReal_mono d (@ENNReal.div_le_of_le_mul' ‖x‖ₑ Z.massRatio D h)).trans' (by simp)
  have Er {j p q ξ ω} hj (k : IsUnit ξ) H : ‖F.floorForm j p q _ ω / _‖ ≤ S.frequencyGain T ξ * _ :=
    .trans' (by
    simp (disch := positivity) [-Nat.cast_mul, md_g, frequencyGain, finHeadWeight, -map_prod]
    gcongr _ * ?_ * _
    grw [g_le_b_pow, (by linarith [S.thousand_le_b] : 2 ≤ S.b), pow_add _ 6 3, mul_assoc, pow_mul',
      ← pow_mul, ← pow_mul, ← pow_succ']
    gcongr; grw [Shape.n, ← S.ϱ_le]; omega) (N (by simp [denomIndex_ne_zero, mul_eq_top,
    div_eq_top]) (IsStdLevel.enorm_floorForm_le (ξ := k.unit) Z _ hj (by omega) n.1 H))
  refine hF.psi_eq ▸ ⟨hm, fun L hl ↦ ⟨by simp, fun j p q ξ a ↦ ?_, by
    simp [div_eq_inv_mul, ← mul_assoc]
    exact fun a t e ↦ .smul (α := ℂ) ⟨.ext (by simp [topKernel, ← integral_conj, e]),
      fun x ↦ by simpa [x.sum_fintype, mul_right_comm] using!
      (lintegral_energy_le_topKernel Z _ L.2 (Matrix.posSemidef_vecMulVec_star_self
      x) e).1⟩ (by positivity), by simpa [div_div] using! (continuous_topKernel ..).div_const _,
    fun p q ↦ (N ofReal_ne_top ?_).trans_eq (toReal_ofReal (by positivity)), fun j p q a ↦
    (ite_eq_left a ▸ Er a · (.inr ⟨j, rfl, rfl, hF.g_eq ▸ (mul_sub ..).symm⟩))⟩⟩
  split_ifs with b <;> [simp_rw [div_eq_inv_mul] at *; simp_rw [← mul_div_assoc, integral_div]]
  exact (Γ.integral_floorForm_succ C ⟨j, b⟩ _ ξ (hF.lintegral_formMajorant_ne_top Z 0 a
    (by omega))).rec fun i s ↦ s.symm ▸ ⟨i, (by simp [·, Pi.one_def]), (Er a · (.inl rfl))⟩
  -- the top floor is the integral of the top kernel, up to the mean of ψ over L
  obtain ⟨rfl, ⟨i, e⟩, o⟩ := a.eq_of_not_lt' b, hF.1.floorForm_top_eq_integral Z p q ξ,
    L.2.measurableSet
  have ⟨I, s⟩ := integral_skew_product (volume.map_sub_left_eq_self <|
    (S.latMiddle _).frameGram ·⁻¹.1 𝔰.top 𝔰.top) (i.mul_prod (((by fun_prop : ContinuousOn
    (P.ψ <| -ξ * ·) L).integrableOn_compact hl).integrable_indicator o)) (by fun_prop [frameGram])
  refine (fun k ↦ ⟨((I.congr k).div_const _).div_const _, .symm ⟨fun u ↦ ?_, ?_⟩⟩)
    (P.ae_isUnit.mono fun | _, ⟨t, rfl⟩ => ?_)
  any_goals simp_rw [← integral_congr_ae k, s, integral_const_mul, integral_mul_const, ← e]
  grw [div_right_comm, mul_div_right_comm, norm_div, norm_mul, norm_integral_le_integral_norm,
    Er a u (by left; rfl)]
  iterate 2 simp +contextual [norm_indicator_eq_indicator_norm, o, Pi.one_def, finHeadWeight,
    Measure.real, toReal_eq_zero_iff, hl.measure_ne_top, L.2.measure_ne_zero _ ⟨0, L.zero_mem⟩]
  erw [topKernel, ← integral_indicator (o.preimage (by fun_prop [frameGram]))]
  simp [← integral_const_mul, Set.indicator, mul_sub, mul_right_comm _ _ (P.ψ _),
    ← P.ψ.map_add_eq_mul, correlation, Level.headDensity, prod_range, ne_of_lt]
  grw [ite_eq_left zero_le, ofReal_div_of_pos (by bound), IntermediateGroup.massRatio,
    ← ENNReal.mul_div_mul_comm, ENNReal.le_div_iff_mul_le (by simp; left; bound),
    ← ENNReal.mul_le_mul_iff_left (P.unitaryLevel_open_compact.1.measure_ne_zero _ ?_)
    (hF.groupMeasure_ne_top le_rfl), ← mul_assoc, Level.enorm_floorForm_le, Level.headDensity,
    prod_range_zero, one_mul, lintegral_mul_const_le, (?_ : lintegral .. ≤ F.floorZeroForm
    Z), mul_right_comm, ENNReal.ofReal_pow (by bound), ← hk.ge, floorZeroForm_le_main_term ⟨_,
    P.unitaryLevel_le_unitaryLevel_one, le_rfl⟩ 0 (by omega), sdiff_le, SemilocalField.volume_O,
    ← hF.box_eq.2.1, add_le_add_left hF.groupMeasure_boxSet_le, ← pow_six_le]
  any_goals simp [ENNReal.ofReal_add, pow_succ, add_assoc, ← mul_add, inv_two_add_inv_two, -inv_pow,
    mul_eq_top]
  ring; rfl
  simp [Level.floorZeroForm, enorm_integral_phase_eq_upperPairing, formModulus, descConv.eq_1,
    weylRatio, ← formIntegrandOne_eq Γ C, formIntegrandOne, ← sq, mul_pow]
