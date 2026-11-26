import OmegaMath.NumberTheory.GRH.Lib.DiscreteSeries.Bruhat.ComplexPlace
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Isotropic flags in unitary groups: Heisenberg radicals, big Bruhat cell, Haar measure
(known result; see Lib.DiscreteSeries.Bruhat.ComplexPlace).

This file: Product of Heisenberg floor measures equals coordinate Haar measure on the unipotent
group. -/
seal Finset.univ Finset.sum Finset.prod


open Matrix MeasureTheory Measure Fintype Real Finset
variable {𝔰 : Shape}
attribute [-instance] MeasurableSingletonClass.toDiscreteMeasurableSpace

/-- The Gaussian exp(−π Σ_{b<l}(Σ_i |g_{i,e*_b}|² + (Im g_{e_b,e*_b})²)) on G₁, the inner sum
over the basis indices i of floor (`floorOf`) greater than b. -/
noncomputable abbrev freeGaussian l (g : 𝔰.G₁) := ‖rexp (-π * ∑ b with b.1 < l,
  let w :=
    g.1.1 *ᵥ Pi.single (eStar b) 1; ∑ i with b < floorOf i, ‖w i‖ ^ 2 + (w (.inl b)).im ^ 2)‖ₑ

lemma lintegral_freeGaussian_ascConv {l} (hl : l ≤ 𝔰.ϱ) : ∫⁻ ν : 𝔰.G₁,
  freeGaussian l ν ∂ascConv Place.heisenbergMeasure l = 1 := by
  induction' l with a ih; simp [ascConv, freeGaussian]
  erw [lintegral_mconv_symm, Place.heisenbergMeasure, dite_eq_left, ← volume.map_id, map_prod_map,
    lintegral_map, lintegral_map, lintegral_congr fun x ↦
    lintegral_congr_of_ae_imp ae_ascConv_mem_unipotentBelow fun ν h ↦ ?_, lintegral_lintegral_mul,
    lintegral_gaussian_eq_one, ih (by lia), one_mul]; any_goals fun_prop
  push_cast [freeGaussian, ← mulVec_mulVec, heisenbergElem_mulVec]
  rw [← add_sum_erase (a := ⟨a, hl⟩), mul_add, exp_add, enorm_mul, ← sum_subtype_eq_sum_filter]
  congr! <;> try rw [unipotentBelow_mulVec_apply h]
  all_goals simp_all [Complex.conj_eq_iff_im.1 (star_form IsHermUnit.conjTranspose_eq ..), ne_of_gt,
    inclMatrix_val_mulVec, -mulVec_mulVec, Fin.ext_iff, Nat.lt_of_succ_le] <;> grind [floorOf]

/-- The measure `Shape.besselHaar` on 𝖴, viewed on G₁, equals the convolution η₀∗⋯∗η_{ϱ−1} of the
measures of the floors.

Known result: Isotropic flags in unitary groups: Heisenberg radicals, big Bruhat cell, Haar
measure. -/
lemma ascConv_heisenbergMeasure_eq_besselHaar : ascConv Place.heisenbergMeasure 𝔰.ϱ =
  𝔰.besselHaar.map .val := ext_of_lintegral _ fun f hf ↦ by
  trans ∫⁻ y, ∫⁻ x,
    freeGaussian 𝔰.ϱ (y⁻¹.1 * x) * f y ∂ascConv complexPlace.heisenbergMeasure 𝔰.ϱ ∂𝔰.besselHaar
  rw [eq_comm, lintegral_lintegral_swap, lintegral_congr_of_ae_imp ae_ascConv_mem_unipotentBelow
    (lintegral_mul_left_eq_self _ ⟨·, unipotentBelow_le_besselU ·⟩ |>.symm.trans (by aesop)),
    lintegral_lintegral_swap, lintegral_congr fun y ↦ ?_, lintegral_mul_const,
    measurePreserving_freeEntries_besselHaar.lintegral_comp, lintegral_gaussian_eq_one, one_mul]
  all_goals first | fun_prop | simp (disch := first | fun_prop | simp [unipotentBelow_eq_besselU]) [
    lintegral_mul_const, ← lintegral_mconv_dirac, ← lintegral_dirac_mconv, lintegral_map,
    ascConv_heisenbergMeasure_invariant, lintegral_freeGaussian_ascConv]
  erw [freeGaussian, U.coe_inv IsHermInvolution.mul_self,
    ← sum_toFinset_eq_subtype _ (‖y.1.1.1.toRows₁ · ·‖ ^ 2).uncurry]
  simp [sum_filter, sum_prod_type, splitGram, middleGram, mul_apply]; ring

lemma exists_chart_ascConv_cellLaw j : ∃ g : (Fin j → ℂ) → 𝔰.G₁, Measurable g ∧ (∀ p : ℕ → ℂˣ, j ≤
  𝔰.n → g (p ·) = if j ≤ 𝔰.ϱ then weylElem j p else weylElem 𝔰.ϱ p * cellChart 𝔰 𝔰.ϱ (p 𝔰.ϱ)) ∧ ∀ X,
  Measurable X → ∫⁻ x, X x ∂ascConv cellLaw j = ∫⁻ z, (∏ a : Fin j, cellDensity 𝔰 a (z a)) * X
  (g z)⁻¹ := j.rec ⟨1, by simp! [measurable_one, univ_eq_empty, volume_pi]⟩ fun j ⟨g, m, e⟩ ↦
  ⟨fun z ↦ cellChart 𝔰 j (z (.last j)) * g (z ·.castSucc), by fun_prop,
  by simp! +contextual (disch := with_unfolding_all fun_prop) [lintegral_mconv, *, mul_assoc,
  (measurePreserving_piFinSuccAbove _ (.last j)).symm.lintegral_map_equiv, lintegral_prod_symm,
  volume_pi, lintegral_map, lintegral_withDensity_eq_lintegral_mul,
  Fin.prod_univ_castSucc]; grind [cellChart, weylElem_succ, (commute_weylElem cellChart_mem).eq]⟩
