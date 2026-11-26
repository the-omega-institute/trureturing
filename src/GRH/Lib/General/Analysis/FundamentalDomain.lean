import GRH.Lib.Adelic.QuotientMeasure.PeriodicMean
import GRH.Lib.Adelic.QuotientMeasure.Unimodular
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of real and complex analysis (textbook or folklore).

This file: Fourier inversion and uniqueness on a compact abelian quotient, via Stone-Weierstrass.
Mean over compact quotient equals fundamental-domain average; unfolding of sums over a lattice.
Bounded fundamental domain for a number field in adeles, with its volume. -/

open ContinuousMap Set Complex IsDualFamily MeasureTheory NumberField QuotientAddGroup Submodule
  ZSpan nonZeroDivisors MeasureTheory.ContinuousMap MeasureTheory.Measure mixedEmbedding

variable {B} {I : outParam _} [AddCommGroup B] [TopologicalSpace B]
  [AddCommGroup I] {B₀ : AddSubgroup B} {F : B → ℂ}
  {χ : outParam (I → B → ℂ)}

/-- The property that i ↦ χ_i is an injective homomorphism from I to continuous unitary
characters of B trivial on B₀, whose common kernel lies in B₀. -/
class IsDualFamily (B₀ : AddSubgroup B) (χ : outParam (I → B → ℂ)) where
  periodic i : IsContPeriodic B₀ (χ i)
  add_left i j x : χ (i + j) x = χ i x * χ j x
  add_right i x y : χ i (x + y) = χ i x * χ i y
  norm_eq_one i x : ‖χ i x‖ = 1
  mem_of_forall_eq_one x : (∀ i, χ i x = 1) → x ∈ B₀
  eq_zero_of_forall_eq_one i : (∀ x, χ i x = 1) → i = 0

/-- Stone–Weierstrass for monoids: a conjugation-closed submonoid of `C(K, ℂ)` that separates
the points of the compact space `K` spans a dense subspace. -/
lemma stone_weierstrass_span {K} [TopologicalSpace K] [CompactSpace K] (M : Submonoid C(K, ℂ))
    (hs : ∀ f ∈ M, star f ∈ M) (h : ∀ x y, (∀ f ∈ M, f x = f y) → x = y) :
    Dense (span ℂ (M : Set C(K, ℂ)) : Set C(K, ℂ)) := fun _ ↦ by
  grw [← M.closure_le.2 (union_subset le_rfl (star_subset.2 hs)), ← StarAlgebra.adjoin_eq_span]
  exact (starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ fun _ _ ↦
    not_imp_comm.1 (by aesop)).ge ⟨⟩

lemma IsDualFamily.zero_apply [hχ : IsDualFamily B₀ χ] x :
    χ 0 x = 1 := by simpa [← norm_pos_iff, hχ.4] using hχ.2 0 0 x

lemma IsDualFamily.conj_apply [hχ : IsDualFamily B₀ χ] i x : starRingEnd _ (χ i x) = χ (-i) x := by
  simp [← inv_eq_conj, hχ.4, inv_eq_of_mul_eq_one_right (b := χ (-i) x), ← hχ.2, hχ.zero_apply]

variable [IsTopologicalAddGroup B] [CompactSpace (B ⧸ B₀)] [hχ : IsDualFamily B₀ χ]

lemma IsDualFamily.quotMean_eq_ite i : quotMean B₀ (χ i) = ite (i = 0) 1 0 := by
  have := quotMean_translate (hχ.1 i)
  split <;> simp_all [hχ.3, quotMean, hχ.zero_apply]; grind [hχ.6 i]

/-- Let χ satisfy `IsDualFamily` for B₀, with B/B₀ compact. For countable ι, ξ : ι → I with zero
set S, and c : ι → ℂ summable, the mean over B/B₀ of x ↦ ∑_i χ_{ξ(i)}(x) c_i is ∑_{i∈S} c_i. -/
lemma IsDualFamily.tsum_coeff_eq_quotMean {ι c} [Countable ι] (ξ : ι → I) {S : Set ι} (h : ∀ i,
  ξ i = 0 ↔ i ∈ S) (s : Summable c) : ∑' i : S, c i = quotMean B₀ (∑' i, χ (ξ i) · * c i) := by
  rw [tsum_subtype, quotMean, ← integral_tsum_of_summable_integral_norm] <;> simp [*,
    ← quotMean.eq_1, quotMean_eq_ite, indicator, hχ.4, s.norm, (hχ.1 _).integrable_out.mul_const]

omit [IsTopologicalAddGroup B] [CompactSpace (B ⧸ B₀)] in
lemma IsDualFamily.isContPeriodic_mul (hF : IsContPeriodic B₀ F) i : IsContPeriodic B₀ fun x ↦
  χ i x * F x := ⟨(hχ.1 i).1.mul hF.1, by grind [IsContPeriodic, IsDualFamily]⟩

lemma IsDualFamily.mul_quotMean_translate (hF : IsContPeriodic B₀ F) i a :
  χ i a * quotMean B₀ (fun x ↦ χ i x * F (x + a)) = quotMean B₀ fun x ↦ χ i x * F x := by grind
  [quotMean_translate (isContPeriodic_mul hF i) a, quotMean_const_mul, IsDualFamily]

/-- Fourier inversion for a dual family χ of characters of B modulo B₀: if F is continuous and
B₀-periodic and its coefficients a_i = mean(χ_i F) are summable, then F(x) = Σ_i χ_{−i}(x)
a_i for every x. -/
lemma IsDualFamily.fourier_inversion (hF : IsContPeriodic B₀ F) {a} (h : Summable a)
    (e : ∀ i, a i = quotMean B₀ fun y ↦ χ i y * F y) x : HasSum (fun i ↦ χ (-i) x * a i) (F x) := by
  let c : AddChar I C(_, ℂ) := by
    use (star ⟨_, hχ.1 · |>.continuous_out⟩) <;> simp [DFunLike.ext_iff, hχ.2, hχ.zero_apply]
  simpa [c, hχ.conj_apply, (hχ.1 _).apply_out_mk, ← hF.apply_out_mk x, mul_comm] using! hasSum_apply
    (hasSum_of_hasSum_Lp (g := a • ⇑c) (.of_norm (by simp [c, hχ.4, norm_eq_iSup_norm, h.norm])) (by
    simpa [HilbertBasis.repr_apply_apply, inner_toLp, c, funext e, mul_comm] using! (HilbertBasis.mk
    (by simp [c, inner_toLp, hχ.conj_apply, ← hχ.2, orthonormal_iff_ite, ← quotMean.eq_1,
      hχ.quotMean_eq_ite]; grind : Orthonormal ℂ (toLp 2 (.addHaarMeasure ⊤) ℂ ∘ c)) fun _ _ ↦ by
    erw [range_comp, span_image]
    apply (toLp_denseRange _ _ _ (by simp)).dense_image (by fun_prop) (stone_weierstrass_span
      (MonoidHom.mrange c.toMonoidHom) (by aesop (add simp hχ.conj_apply)) fun p q _ ↦
      p.out_equiv_out.1
      (leftRel_apply.2 (hχ.5 _ (by simp_all [add_neg_cancel_left p.out q.out ▸ hχ.3 .., c, hχ.4,
      ← norm_pos_iff, ← inv_eq_conj]))))).hasSum_repr (toLp 2 _ ℂ ⟨_, hF.continuous_out⟩))) x

/-- Let the χ_i form a dual family of characters of B modulo B₀, and F be continuous and
B₀-periodic. If χ_iF has mean zero for every i such that χ_i(a) = c whenever cF(x+a) = F(x)
for all x, then F = 0. -/
lemma IsDualFamily.eq_zero_of_coeff (hF : IsContPeriodic B₀ F) (h : ∀ i,
  (∀ a c, (∀ x, c * F (x + a) = F x) → χ i a = c) → quotMean B₀ (fun x ↦ χ i x * F x) = 0) x :
  F x = 0 := by simp [← (fourier_inversion hF summable_zero _
  x).tsum_eq, (by_cases id fun n ↦ h · fun a c e ↦ mul_right_cancel₀ n (by
     simpa [← quotMean_const_mul, mul_left_comm c, e] using congr(c * $(mul_quotMean_translate hF _
       a))))]

variable (B₀) [MeasurableSpace B] [BorelSpace B] [PolishSpace B] [LocallyCompactSpace B]
  (μ : Measure B) [DiscreteTopology B₀] [μ.IsAddHaarMeasure] [IsFiniteMeasure (B₀.qms μ)]

/-- For B₀ discrete and cocompact in B, μ a Haar measure with `qms` B₀ μ finite, and F
continuous and B₀-periodic, the average of F against `qms` B₀ μ is the mean of F over B
modulo B₀. -/
lemma average_quotMeasure_eq_quotMean (hF : IsContPeriodic B₀ F) : ⨍ x, F x ∂B₀.qms μ =
  quotMean B₀ F := by
  have m := continuous_mk (N := B₀).measurable
  have := IsAddLeftInvariant.mk (forall_mk.2 fun a ↦ .trans (map_map (by fun_prop) m)
    (identDistrib_addOrbitMeasure_comp (.id (@count B₀ _)) (measurePreserving_add_left μ a)
    (add_left_comm a ·) (by simp) m).map_eq)
  rw [average_eq, ← funext hF.apply_out_mk, ← integral_map (by fun_prop)
    hF.continuous_out.aestronglyMeasurable, addHaarMeasure_unique (Measure.map ..) ⊤]
  simp [quotMean, ← real_def, m, measureReal_univ_ne_zero, -withDensity_apply]

/-- Unfolding: if F is integrable on B and G(x) = ∑_{γ∈B₀} F(γ + x) converges everywhere and is
continuous, then the mean of G over B modulo B₀ is ∫_B F dμ divided by the covolume of B₀
(the mass of `qms`). -/
lemma quotMean_tsum_eq_integral {G} (i : Integrable F μ) (h : IsContPeriodic B₀ G) (e : ∀ x,
  HasSum (F <| · +ᵥ x : B₀ → ℂ) (G x)) : quotMean B₀ G = ((B₀.qms μ).real .univ)⁻¹ • ∫ x,
  F x ∂μ := by simp [← average_quotMeasure_eq_quotMean _ μ h,
  measurePreserving_addOrbitMeasure.fubini i, average_eq, ← integral_count_eq_tsum, ← (e _).tsum_eq]

/-- Let j = (j₁, j₂): I → V×W be additive on the number field I, j₁ the Minkowski embedding up
to a measure-preserving isomorphism, j₂⁻¹(O) = J, W = j₂(I) + O. Then F×O is a strict
fundamental domain for some bounded measurable F of volume N(J)2^(−r₂)√|disc I|. -/
lemma exists_fundDomain_prod {I V W} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasureSpace V]
    [BorelSpace V] [AddCommGroup W] [Field I] [NumberField I] (j : I →+ V × W) (O : AddSubgroup W)
    (J : (FractionalIdeal (𝓞 I)⁰ I)ˣ) (hO : ∀ a, (j a).2 ∈ O ↔ a ∈ J.1) (hs : ∀ w, ∃ a, w - (j a).2
    ∈ O) : (∃ e : _ ≃ₗ[ℝ] V, MeasurePreserving e ∧ ∀ a, e (mixedEmbedding I a) = (j a).1) → ∃ F,
    MeasurableSet F ∧ Bornology.IsBounded F ∧ volume F = .ofReal J.1.absNorm *
    (2⁻¹ ^ InfinitePlace.nrComplexPlaces I * ‖discr I‖₊.sqrt) ∧ ∀ x, ∃! a, j a + x ∈ F ×ˢ O
  | ⟨e, he, hT⟩ => let b := (fractionalIdealLatticeBasis I J).map e
  ⟨_, by measurability, fundamentalDomain_isBounded b, by
    erw [← he.measure_preimage (by measurability), ← map_fundamentalDomain, e.preimage_image,
      volume_fundamentalDomain_fractionalIdealLatticeBasis, volume_fundamentalDomain_latticeBasis],
    fun x ↦ (hs x.2).rec fun a ha ↦ (Equiv.subRight a).existsUnique_congr_right.1 (by
    simpa [ExistsUnique, add_comm_sub, add_mem_cancel_right ha, b, ← ZSpan.map, hO, ← hT, and_assoc,
      @imp.swap (∀ _, _), mem_span_fractionalIdealLatticeBasis, (mixedEmbedding_injective I).eq_iff,
      vadd_def] using exist_unique_vadd_mem_fundamentalDomain b (x - j a).1)⟩
