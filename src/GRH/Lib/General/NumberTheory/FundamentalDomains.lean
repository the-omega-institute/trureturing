import GRH.Lib.Shimura.Uniformisation.PeriodLattice
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of algebraic number theory (textbook or folklore).

Part of: Adeles of a number field: base change, discreteness and compact quotient, modulus (known
result; see Lib.Adelic.Adeles.IdeleHilbert90).

This file: Fundamental domains and covolumes of adelic lattices; box domain for filtered discrete
subgroups. -/


open NumberField MeasureTheory Matrix Finset ZSpan MeasurableEquiv mixedEmbedding
variable {E n} [Field E] [CMType E] [Fintype n]

/-- Let t ∈ (E ⊗ ℝ)ⁿ and the finite adelic matrix m be invertible. The group of vectors
(t_{j,v}Φ_v(x_j)), x ∈ Eⁿ with mx integral, has a measurable strict fundamental domain of
volume |(∏_j t_j, det m)|_𝔸 divided by the n-th power of `volÔ`. -/
lemma exists_fundamental_domain_classLattice (t : RealVectors E n) (ht :
  IsUnit t) (m : GL n (𝔸f E)) : ∃ F, MeasurableSet F ∧ volume.real F =
  (∏ w, ‖∏ j, t j w‖ ^ 2) / genIndex m.1.det / volÔ E ^ Fintype.card n ∧ ∀ x, ∃! l :
  classLattice m⁻¹ ⊥ (.smulLeft ht.unit), l.1 + x ∈ F := .imp (fun F (And.intro f u) ↦ ⟨f, by
  have T z : ∀ w, ∃! y, t * toRealVectors y + z ∈ F ∧ frameTorsionClass m⁻¹ y = w :=
    frameTorsionClass_surjective (g := m⁻¹).forall.2 (Equiv.addRight · |>.existsUnique_congr_right.1
    (by simpa [ExistsUnique, mul_add, ht.mul_right_inj, add_assoc, mem_classLattice,
    toRealVectors_injective.eq_iff, and_assoc, @imp.swap (_ ∈ F)] using u _))
  erw [genIndex_eq_inv_finIdeleAbs m.det]
  simpa [field, ideleAbs_det_mkAdelicGL] using!
    (by simpa [field, volume_pi_pi, Measure.volume_eq_prod,
    (volume_measurePreserving_arrowProdEquivProdArrow ..).measure_preimage_equiv] using
    (congr($((lintegral_encard_rat_points (mkAdelicGL (((diagGL (ht.apply · |>.unit)).map <|
    Pi.evalRingHom _ ·), m))⁻¹ ((arrowProdEquivProdArrow ..).measurable (f.prod (.univ_pi fun _ ↦
    isOpen_Ô.measurableSet)))).trans (lintegral_congr fun _ ↦ congrArg _ (Set.encard_eq_one.2 (by
    simpa [diagonal, Set.singleton_iff_unique_mem, mulVec_eq_sum, frameTorsionClass, mul_add,
      torsionClass_eq_iff, ← prod_mk_sum, -map_neg, arrowProdEquivProdArrow] using!
      T _ (torsionClass (-_)))))).toReal)) :), u⟩) ⟨_, fundamentalDomain_measurableSet _, by
    rw [← (Module.finBasis ..).ofZLatticeBasis_span ℝ (classLattice ..)]
    apply exist_unique_vadd_mem_fundamentalDomain⟩

/-- Injective graded coordinates c on G: suppose each γ ∈ Γ vanishing below deg i shifts c_i by
c(γ)_i ∈ L_i, and all of L_i arises with the other coordinates of degree ≤ deg i zero. For
fundamental domains F_i of L_i, each x has a unique γ ∈ Γ with c(xγ) ∈ ∏F_i. -/
lemma Filling.existsUnique_mul_mem_box {G ι} [Group G] [Fintype ι] {V : ι → AddGrpCat} (deg : ι → ℕ)
    (c : G → ∀ i, V i) (inj : c.Injective) (Γ : Subgroup G) (L : ∀ _, AddSubmonoid _) F (hF : ∀ i
  v, ∃! l : L i, l.1 + v ∈ F i) (hL' : ∀ i, ∀ l ∈ L i, ∃ γ : Γ, c γ i = l ∧ ∀ j ≠ i, deg j ≤ deg i →
  c γ j = c 1 j) (hL : ∀ (γ : Γ) i, (∀ j, deg j < deg i → c γ j = c 1 j) → c γ i ∈ L i ∧ ∀ x, c
  (x * γ) i = c γ i + c x i) x : ∃! γ : Γ, c (x * γ) ∈ Set.univ.pi F := have := by simpa using hL 1
  .imp (fun γ h ↦ ⟨h, (mul_left_surjective γ).forall.2 fun δ _ ↦ by simpa using @inj δ 1 (funext
    ((measure deg).2.fix fun i ih ↦ have := @(hF _ (c (x * γ) _)).unique _ _ ⟨_, (hL _ _ ih).1⟩ 0
    by simp_all [← (hL _ _ ih).2, mul_assoc]))⟩) (@coe_univ .. ▸ univ.induction_on_max_value deg
    (by simp) fun a _ _ _ ⟨γ, h⟩ ↦ (hF a (c (x * γ) a)).rec fun l _ ↦ (hL' a _ l.2).imp' (γ * ·)
    fun δ o i _ ↦ by erw [← mul_assoc, (hL ..).2] <;> grind [eq_or_ne i a])

/-- For E stably unramified and nonzero reals t_v, the group of vectors (t_v Im Φ_v(s))_v, s an
integer of E with s̄ = −s, has a measurable fundamental domain in ℝ^(infinite places) of
volume ∏|t_v|·√|disc E⁺|. -/
lemma Filling.exists_fundamental_domain_im_skew [StablyUnram E] (t : _ → ℝ) (ht : ∀ v, t v ≠ 0) :
  ∃ F, MeasurableSet F ∧
  volume.real F = (∏ v, |t v|) * √√|NumberField.discr E| ∧ ∀ x, ∃! l : (skewAdjoint (𝓞 E)).map
  (.mk' (fun s v ↦ t v * (Φ v s.val).im) (by simp [funext_iff, mul_add])), l.1 + x ∈ F := by
  obtain ⟨⟨ι, _, h⟩, f, hf, _⟩ := ‹StablyUnram E›.exists_i_c₀,
    exists_mixedEquiv_maximalReal (E := E)
  have {v} : (Φ v ι.val).re = 0 ∧ |(Φ v ι).im| = 1 := by
    cases mul_self_eq_mul_self_iff.1 (by simp [h, ← map_mul] : Φ v ι * _ = _ * .I) <;> aesop
  have k := isUnit_of_mul_isUnit_left (h.1 ▸ isUnit_neg_one)
  refine ⟨_, ?_, ?_, ((Equiv.subtypeEquivRight fun l ↦ .trans ?_ k.unit.mulLeft.exists_congr_right
    ).existsUnique_congr_right.1 <| exist_unique_vadd_mem_fundamentalDomain (((latticeBasis _).map
    f).map ((diagonal fun v ↦ t v * (Φ v ι).im).toLin'.equivOfDetNeZero
    (by simp_all [prod_eq_zero_iff, ← abs_pos]))) ·)⟩
  repeat (try erw [← map_fundamentalDomain, Measure.real, volume.addHaar_image_linearMap, ←
    hf.measure_preimage, ← map_fundamentalDomain, f.preimage_image]) <;> simp [← Int.cast_abs,
    abs_discr_eq_discr_sq, Real.sqrt_sq_eq_abs, norm, k.ne_zero, *, abs_prod, prod_nonneg,
    fundamentalDomain_measurableSet, volume_fundamentalDomain_latticeBasis, ← ZSpan.map,
    mem_span_latticeBasis, funext_iff, mul_assoc, skewAdjoint.mem_iff]
  simp [star, IsCMField.ringOfIntegersComplexConj_eq_self_iff, ← funext_iff]; rfl
