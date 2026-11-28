/- GID: D5/S3/Zeros/GRH/New/Seesaw/IntegralAsCosetSum
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Seesaw/IntegralAsCosetSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Seesaw.IntegralAsCosetSum. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Seesaw/IntegralAsCosetSum.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.Periods.UnfoldingStep
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Unfolded periods as finite sums with controlled denominators (see
New.Seesaw.SeesawTheorem).

This file: Finite coset cut with multiplicities dividing powers of q; period as weighted finite
sum. -/

open MeasureTheory Measure Subgroup QuotientGroup MulAction Set Pointwise ProbabilityTheory


variable {H} [Group H] {S A J : Subgroup H} (T : Finset (H ⧸ J)) {E ι X} [Field E] [CMType E]
  [Fintype ι] [Fintype X] {s ε N} {V : Space E ι ε} {Y : Grading V N X s}

variable (S A) in
/-- The number of cosets r(S ∩ A) in S with t in the translate rT, counted as zero if infinite. -/
noncomputable def coverMultiplicity t := (mk (s := A.subgroupOf S) '' {r | r⁻¹ • t ∈ T}).ncard

lemma coverMultiplicity_smul (p : S) t : coverMultiplicity S A T (p • t) =
  coverMultiplicity S A T t := by rw [coverMultiplicity, ← ncard_smul_set p⁻¹,
  ← image_smul_comm] <;> simp [coverMultiplicity, ← preimage_smul, mul_smul]

/-- Let J ≤ A be levels, A ≤ B, D ⊆ B compact, W ⊆ SD; each x ∈ D has n with (xux⁻¹)^{qⁿ} ∈ A
for all u ∈ J. Some finite (S ∩ A)-stable T ⊆ B/J has `coverMultiplicity` dividing a power of
q on T and on W. -/
lemma exists_cut_coverMultiplicity_dvd {S A J : Subgroup (Gf E ι)} [k : IsLevel A] [o : IsLevel J]
  (l : J ≤ A) {D q B} (cD : IsCompact D) {W : _ → _} (b : A ≤ B) (hD : ∀ x ∈ D, x ∈ B ∧ ∃ n,
  ∀ u ∈ J, (x * u * x⁻¹) ^ q ^ n ∈ A) (hW : ∀ x, W x → ∃ r ∈ S, r * x ∈ D) : ∃ T : Finset (_ ⧸ J),
  (∀ p : S, ↑p ∈ A → ∀ t, t ∈ T ↔ p • t ∈ T) ∧ (∀ ⦃x⦄, ↑x ∈ T → x ∈ B) ∧ ∀ x, ↑x ∈ T ∨ W x → ∃ j,
  coverMultiplicity S A T x ∣ q ^ j := ((mk '' D).exists_subset_bijOn (orbit S)).elim fun C ⟨hC, _,
  i, u⟩ ↦ (Finite.exists_finset (s := {t | ∃ p : S, ↑p ∈ A ∧ p⁻¹ • t ∈ C})
  ((finite_quotient_image_of_isCompact o.2 (k.isCompact.mul cD)).subset fun t ⟨p, h,
  a⟩ ↦ (hC a).elim fun d e ↦ ⟨_, ⟨p, h, d, e.1, rfl⟩, eq_inv_smul_iff.1 e.2⟩)).imp fun T m ↦ by
  simp_rw [m]
  use fun p _ _ ↦ (toPerm p).exists_congr (by simp_all [mul_mem_cancel_left, mul_smul]), fun x
    ⟨r, hr, h⟩ ↦ (hC h).elim fun d ⟨h, e⟩ ↦ by
    simpa [mul_mem_cancel_left, b hr, *] using b (l (QuotientGroup.eq.1 e)), fun y h ↦ ?_
  let ⟨_, ht, e⟩ := h.elim (fun ⟨r, h⟩ ↦ ⟨_, h.2, by simp⟩)
    (hW y · |>.elim fun r h ↦ u ⟨_, ⟨_, h.2, rfl⟩, orbit_smul (⟨r, h.1⟩ : S) (mk y)⟩)
  obtain ⟨⟨r, e⟩, x, hx, rfl⟩ := orbit_eq_iff.1 e.symm, hC ht
  have := FiniteIndex.mk (relIndex_comap_ne_zero S.subtype ((k.isCompact.smul (ConjAct.toConjAct
    x)).relIndex_ne_zero (K := MulAut.conj x • A) k.2) ∘ relIndex_eq_zero_of_le_right
    (K := stabilizer S (mk x)) fun r h ↦ ⟨_, l (QuotientGroup.eq.1 h.symm), by simp⟩)
  erw [← e, coverMultiplicity_smul, coverMultiplicity,
    (image_subset_iff.2 fun r h ↦ ?_).antisymm (b := orbit (stabilizer S
    (mk x)) (mk 1)) fun _ ⟨r, e⟩ ↦ ⟨_, (r * 1)⁻¹.2.symm.subst ((m _).2 ⟨1, by simpa⟩), e⟩,
    ← index_stabilizer, congr(($(stabilizer_quotient (A.comap _)).subgroupOf _).index)]
  exacts [.imp (fun _ ↦ (index_dvd_of_le (normalCore_le _)).trans) (isPGroup_iff_card_dvd_pow.1
    (Quot.ind fun b ↦ (hD x hx).2.imp fun n h ↦ (eq_one_iff _).2 fun c ↦ by
    simpa using! h _ (QuotientGroup.eq.1 (c * b * c⁻¹).2.symm))), ((m _).1 h).elim fun p ⟨_, e⟩ ↦
      ⟨⟨_, i (by rwa [mul_smul]) ht (by simp)⟩⁻¹, QuotientGroup.eq.2 (by simpa)⟩]

/-- For a measurable subgroup J and a left invariant measure μ, the union of a finite non-empty
set s of left cosets of J has measure |s|·μ(J). -/
lemma measure_union_cosets [MeasurableSpace H] [MeasurableMul H] {μ} [IsMulLeftInvariant μ]
    (h : @MeasurableSet H _ J) {s} (f : ncard s ≠ 0) : μ (mk (s := J) ⁻¹' s) = s.ncard * μ J := by
  lift s to Finset (H ⧸ J) using finite_of_ncard_ne_zero f
  rw [← sum_measure_preimage_singleton, Finset.sum_eq_card_nsmul (b := μ J)] <;>
    simp [forall_mk, preimage, eq_class_eq_leftCoset, h.const_smul, -measurableSet_setOfPred]

/-- For a level A and a on G_∞, one κ gives ∫_{B(E⁺)∖G} f = κ∑_{t∈T} b(t)/mult(t),
B = `Grading.besselGroup`, for all integrable f = Py (`Grading.IsGeneric` P, y automorphic), levels
J and finite (A ∩ B_f)-stable T ⊆ G_f/J, if mult ≠ 0 where f ≠ 0 and ∫_{[B]}
f(ρt)dρ = [K₀:J]a(t_∞)b(t_f) for t_f ∈ T.

Unfolded periods as finite sums with controlled denominators. -/
lemma Grading.exists_integral_eq_sum_over_cut [WeilData E]
    A [k : IsLevel A] (a : _ → ℂ) : ∃ κ, ∀ {P y J T}
  [IsLevel J] (b : _ ⧸ J → ℂ), Y.IsGeneric P → V.IsAutomorphic y → let f :=
    P * y; Integrable f Y.ratBessel.qms → (∀ p : Y.besselFin, ↑p ∈ A → ∀ t, t ∈ T ↔ p • t ∈ T) →
    (∀ g, f g ≠ 0 → coverMultiplicity Y.besselFin A T g.2 ≠ 0) →
    (∀ t, t.2 ∈ T → ∫ r, f (r * t) ∂Y.besselMeasure = stdLevelIndex J * (a t.1 * b t.2)) →
    Y.ratBessel.qms[f] = κ * ∑ t ∈ T, (↑(coverMultiplicity Y.besselFin A T t))⁻¹ * b t := by
  let η := haarMeasure (G := Y.besselFin) ⟨⟨_, k.isCompact.preimage_val⟩, 1,
    k.2.preimage_val.interior_eq.ge A.one_mem⟩
  let ⟨β, _, hβ'⟩ := hasCutoff_of_proper (ν := @haar Y.besselGroup ..) (X := G E ε)
  let α g := ∫⁻ s, β (g, s) ∂η
  use (withDensity ℙ α)[a], @fun P y J T o b p z hI hT hs hb ↦ ?_
  obtain ⟨⟨⟩, ⟨⟩⟩ := z, p, discreteTopology o.2
  let ψ := indicator T (coverMultiplicity Y.besselFin A T · : _ → NNReal)⁻¹
  have hφ := (by fun_prop : Continuous (ψ ∘ QuotientGroup.mk)).measurable
  erw [← setIntegral_eq_integral_of_forall_compl_eq_zero (not_imp_comm.1 <| hs ·),
    restrict_withDensity',
    (integral_quotMeasure_stages _ _ id ?_ (((congrArg _ (funext fun t ↦ ?_)).trans
    (withDensity_indicator_one (isOpen_ne_fun ..).measurableSet)).subst (measurePreserving_smul_prod
    (ν := haar) (β := fun g ↦ α g.1 * ψ g.2) _)) (map_subgroupOf_eq_of_le inf_le_right) _ (by
    simp +contextual [*]) ((restrict_withDensity' ..).subst hI.restrict)).2, integral_congr_ae
    ((ae_withDensity_iff _).2 (.of_forall (hb · ∘ by simp +contextual [ψ]))), integral_const_mul,
    ← prod_withDensity _ hφ.coe_nnreal_ennreal, integral_prod_mul _ (b ∘ _),
    integral_withDensity_eq_integral_smul hφ, ← integral_map (f := fun t ↦ ψ t • b t) _
    (Continuous.aestronglyMeasurable _), ← indicator_smul_left, integral_indicator T.measurableSet,
    setIntegral_finset _ (.mono_set _ (biUnion_of_singleton _).ge)]
  any_goals fun_prop
  iterate 3 simp [real_def, map_apply measurable_coe, measure_union_cosets o.2.measurableSet, field,
    -enorm_mul, ← T.mul_sum, NNReal.smul_def, zero_lt_iff,
    inter_eq_left.2 o.1 ▸ measure_inter_eq_inv_relIndex isCompact_Kf o.2]
  simp [smul_def, α, ← lintegral_mul_const', Prod.mul_def] at hβ' ⊢
  rw [lintegral_lintegral_swap, ← lintegral_congr (lintegral_mul_left_eq_self _ ⟨_, ·⁻¹.2⟩),
    lintegral_lintegral_swap, ← lintegral_congr (lintegral_mul_left_eq_self _
    ⟨_, Y.snd_mem_besselFin ·.2⟩), lintegral_lintegral_swap] <;> try fun_prop
  simp [lintegral_mul_const', indicator, *]
  let := Classical.dec; show ∫⁻ u, ψ (u⁻¹ • t.2) ∂η = _
  split_ifs with m <;> simp [ψ, indicator, coverMultiplicity_smul, apply_ite, m]
  erw [lintegral_indicator_const (measurable_inv.smul_const t.2 T.measurableSet), (congrArg _
    ((subset_preimage_image ..).antisymm fun r ⟨s, h, e⟩ ↦ (hT (s⁻¹ * r) (QuotientGroup.eq.1 e :)
    _).2 (by simpa [mul_smul]))).trans (measure_union_cosets k.2.preimage_val.measurableSet m),
    ENNReal.inv_mul_cancel_left, haarMeasure_self] <;> simp [*]
