import GRH.Lib.DiscreteSeries.Bessel.RealMeasures
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Isotropic flags in unitary groups (Heisenberg radicals, big Bruhat cell, Haar
measure). For the unitary group of a frame over an abstract place and at C, the open cell is
obtained from non-zero leading minors, with uniqueness. At C, Haar measure of the unipotent radical
is exactly the product of the Heisenberg floors, and the top floor carries the invariant measure of
the hyperboloid. Source: Knapp, Lie Groups Beyond an Introduction; Helgason, Groups and Geometric
Analysis, Ch. I §5.

This file: The place C, boosts, cell densities, top floor carries Leray measure on hyperboloid. -/

noncomputable section


open MeasureTheory Measure Matrix Real Fintype Set Complex ComplexConjugate Sum
  GaussianFourier ComplexOrder Function
variable {κ : Type} [Fintype κ] (𝔰 : Shape) (l : ℕ) (c : ℂ)

lemma exists_unitary_mulVec_eq ω {v : κ → ℂ} (h : star ω ⬝ᵥ ω = star v ⬝ᵥ v) : ∃ u : U 1,
  u.1.1 *ᵥ ω = v := if o : _ then ⟨1, by have := h.symm; aesop⟩ else (witt ⟨I, by simp⟩ (by simp)
  isUnit_one (.of_ne_zero o) (.of_ne_zero (by aesop)) (by aesop)).imp fun _ ↦ replicateCol_inj.1

attribute [local simp] wave skewAdjoint.mem_iff LeftInverse Matrix.mul_apply inclMatrix frameGram
  dotProduct conj_mul' mem_floorGroup val_toBesselH_apply_coe mul_pow orbitPoint le_of_lt funext_iff
  neg_add_eq_sub

/-- The place ℂ. -/
@[simps] instance complexPlace :
  Place ℂ := have e := HasGaussianIntegral.integral_exp_eq (V := ℂ) one_pos
  have J := Integrable.of_integral_ne_zero (e.trans_ne (by simp))
  have h z := integral_cexp_neg_mul_sq_norm_add (b := 1) one_pos (2 * I) (z / I)
  have := ofReal_integral_norm_eq_lintegral_enorm (J.const_mul π)
  by refine .mk (haar := AddEquiv.isAddHaarMeasure_map _ ⟨⟨_, (·.1.im), ?_, by simp_all
    [RightInverse, Complex.ext_iff, self_eq_neg]⟩, ?_⟩ ?_ ?_) (toTraceOne := ⟨2⁻¹, ?_⟩) (.mk0
    (I / 2) ?_) (volume.map fun r : ℝ ↦ ⟨r * I, by simp⟩) ⟨⟨(‖·‖ₑ ^ 2), ?_⟩, ?_⟩ ⟨wave, ?_, by
    simp [← Complex.exp_add, sub_add_sub_comm]⟩ (.ofReal (π ^ 2)) ?_ ?_ ?_ ⟨?_, by
    rw [map_prod_map, Measure.map_map, ← volume_preserving_equiv_real_prod.symm.2] <;> try fun_prop
    congr 1; simp [Complex.ext_iff]⟩ ?_ ?_ ?_ ⟨(‖·‖⁻¹),
    locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) ?_ ?_ ?_ ?_, ?_⟩ ?_ ⟨_, ?_, J, ?_, ?_, by
    simp_all [← Complex.exp_add, ↓sub_conj, mul_right_comm _ _ I, ← sub_eq_add_neg, sq,
      ← ofReal_norm, abs_of_pos pi_pos]; grind⟩ <;> norm_num +contextual [map_mulVec_haar,
    Pi.le_def, exp_pos, add_mul, ae_ne, neg_div, rpow_neg_one, ENNReal.inv_pow] <;> fun_prop [wave]

/-- The basis of V_ϱ = X₀ ⊕ ℂz made of the hyperbolic pair (1+i)/2·(x_{k₀} ± z) and the
orthonormal vectors x_i, i ≠ k₀. -/
def complexBasis : HyperbolicBasis {i // i ≠ 𝔰.k₀} (𝔰.middleGram (1 : ℂ)) 0 :=
  ⟨of fun i ↦ (fun a ↦ (1 + I) / 2 * (Pi.single 𝔰.k₀ 1 ⊕ᵥ ![1, -1] a) i) ⊕ᵥ
  (0 ⊕ᵥ (inclMatrix ℂ (inl ·.1) i ⊕ᵥ 0)), by simp [← ext_iff, middleGram, map_ofNat]; grind [I_sq],
    by simp; grind [card_pos_iff.2 ⟨𝔰.k₀⟩], by simp [middleGram]⟩

/-- For nonempty κ, k = |κ|, the map ω ↦ |ω|² carries Lebesgue measure on ℂ^κ to the measure π^k
r^{k−1}/(k−1)! dr on r > 0. -/
lemma measurePreserving_normSq_sphereDensity [Nonempty κ] :
  MeasurePreserving (fun ω : κ → ℂ ↦ ‖star ω ⬝ᵥ ω‖) volume
  ((volume.restrict (Ioi 0)).withDensity fun r ↦ .ofReal (sphereDensity (card κ) r / 2)) := by
  refine have k a := Eq.trans ?_ (Complex.volume_sum_rpow_lt κ one_le_two √a); ⟨by fun_prop,
    FiniteSpanningSetsIn.ext (borel_eq_generateFrom_Iio ℝ) isPiSystem_Iio ⟨(Iio ·), by simp, (k ·
    |>.trans_lt (by tauto)), iUnion_eq_univ_iff.2 exists_nat_gt⟩ fun _ ⟨a, e⟩ ↦ e ▸ (k a).trans ?_⟩
  simp (disch := first | positivity | measurability)
    [preimage, ↓← sqrt_eq_rpow, ↓star_dot_self_eq_norm_sq, EuclideanSpace.norm_sq_eq]
  rw [withDensity_apply, restrict_restrict, (by grind : _ ∩ _ = Ioo 0 (√a ^ 2)),
    restrict_Ioo_eq_restrict_Ioc, ← ofReal_integral_eq_lintegral_ofReal (Continuous.integrableOn_Ioc
    (by fun_prop)) (ae_restrict_of_forall_mem ..), ← intervalIntegral.integral_of_le, pow_mul] <;>
    norm_num [← ENNReal.ofReal_pow, sq_nonneg, ← ENNReal.ofReal_mul, Real.Gamma_nat_eq_factorial,
    ← Nat.mul_factorial_pred card_ne_zero, card_pos]
  grind [card_pos]
  bound

lemma lintegral_eq_polar k {g} (m : Measurable g) : ∫⁻ ω : κ → ℂ, g ω = ∫⁻ r in Ioi 0,
    .ofReal (sphereDensity (card κ) r / 2) * ∫⁻ h : U 1, g (h.1.1 *ᵥ √r • Pi.single k 1) := by
  erw [← lintegral_withDensity_eq_lintegral_mul,
    ← (@measurePreserving_normSq_sphereDensity _ _ ⟨k⟩).lintegral_comp, ← lintegral_eq_const
    (ae_of_all volume fun h : U 1 ↦ (complexPlace.measurePreserving_mulVec _ (U.det (by simp) h).2.1
    ).lintegral_comp m), lintegral_lintegral_swap] <;> try fun_prop
  refine lintegral_congr fun ω ↦ (exists_unitary_mulVec_eq ω ?_).elim fun u e ↦
    (lintegral_mul_right_eq_self _ u).symm.trans (by simp [-mulVec_smul, ← mulVec_mulVec, e]; rfl)
  simp (disch := positivity) [← ofReal_mul, norm_of_nonneg']

/-- For l = ϱ and c ≠ 0, the boost in the plane of x_{k₀}, z with h(z, wz) = a = c/min(1, |c|);
otherwise the Weyl element `floorWeyl` of floor l with entry c. -/
def cellChart : 𝔰.G₁ := let a := c / min 1 ‖c‖
  let s := √(‖a‖ ^ 2 - 1) • Pi.single 𝔰.k₀ 1
  dite (l = 𝔰.ϱ ∧ 1 ≤ ‖a‖) (fun h ↦ U.of IsHermUnit.isUnit (fromBlocks 1 0 0 (((diagonal (update 1
    𝔰.k₀ (conj a))).fromBlocks (replicateCol _ s) (-replicateRow _ s) (of fun _ _ ↦ -a)).fromBlocks
    0 0 1)) (by simp [s, splitGram, middleGram, ← ext_iff, diagonal_apply, update_apply,
    apply_ite conj, ← ofReal_mul, RCLike.star_def, *]; grind [conj_mul'])) fun _ ↦ floorWeyl l c

/-- The density of floor l at c: |c|^{2(k−1)+4(ϱ−l)} for l < ϱ, and 2π^k max(|c|²−1,
0)^{k−1}/(k−1)! otherwise, where k = |κ|. -/
def cellDensity := ite (l < 𝔰.ϱ) (‖c‖ₑ ^ (2 * (𝔰.k - 1) + 4 * (𝔰.ϱ - l)))
  (.ofReal (sphereDensity 𝔰.k (‖c‖ ^ 2 - 1)⁺))

variable {𝔰 l c}

/-- The measure on G₁ that is the image of the density `cellDensity` of floor l times dc on ℂ
under c ↦ w_l(c)⁻¹ (`cellChart`). -/
abbrev cellLaw l := (volume.withDensity (cellDensity 𝔰 l)).map fun c ↦ (cellChart 𝔰 l c)⁻¹

lemma cellChart_mem : cellChart 𝔰 l c ∈ GT l :=
  dite_mem.2 (by simp +contextual [↓floorWeyl_mem_floorGroup])

lemma embedH_mem_floorGroup k : @embedH 𝔰 k ∈ GT 𝔰.ϱ := by simp

@[fun_prop] lemma measurable_cellChart : Measurable (cellChart 𝔰 l) := measurable_unitary_of_coe (by
  simp -iota [cellChart, apply_dite]; apply Measurable.ite <;> measurability)

@[fun_prop] lemma measurable_cellDensity :
  Measurable (cellDensity 𝔰 l) := by delta cellDensity; measurability

attribute [local simp] splitGram middleGram cellChart mulVec Nat.sub_eq_zero_iff_le min_eq_left

lemma realFrameGram_cellChart (h : 1 < ‖c‖) : realFrameGram (cellChart 𝔰 𝔰.ϱ c) 𝔰.top 𝔰.top =
  c := by simp [*, U.of]

/-- Cartan decomposition of H_ϱ = U(V_ϱ): if σ ∈ H_ϱ has Z(σ)_{nn} = c, n = ϱ+1, with |c| > 1,
then σ = h w_ϱ(c) h' for some h, h' in U(X₀), w_ϱ(c) the boost `cellChart`. -/
lemma cartan_decomposition {σ} (h : σ ∈ GT 𝔰.ϱ) (e : realFrameGram σ 𝔰.top 𝔰.top =
  c) (hc : 1 < ‖c‖) : ∃ k k', σ = embedH k * cellChart 𝔰 𝔰.ϱ c * embedH k' := by
  have d := congr(diag $(σ.2) 𝔰.z)
  simp [floorGroup_apply h, neg_eq_iff_eq_neg, add_neg_eq_iff_eq_add] at d e
  refine (exists_unitary_mulVec_eq (√(‖c‖ ^ 2 - 1) • Pi.single 𝔰.k₀ 1) ?_).imp fun u f ↦
    (exists_toBesselH_eq (unitriGroup_inf_floorGroup_last.le
    (inv_mul_mem_of_orbitPoint_eq (mul_mem (embedH_mem_floorGroup u) cellChart_mem) h
    (by simpa [e, -splitGram, -middleGram, hc, floorGroup_apply h]
    using f)))).imp fun _ ↦ eq_mul_of_inv_mul_eq
  simp [← ofReal_mul, *]

/-- Polar coordinates on the hyperboloid h(v, v) = −1 of V_ϱ, for k = |κ| > 1: σ ↦ σ⁻¹z carries
the law of w_ϱ(c)⁻¹h, under `cellDensity`(c) dc and Haar probability on U(X₀), to the quadric
measure δ^(ϱ). -/
lemma map_orbitPoint_cellLaw_top (_ : 1 < 𝔰.k) : (cellLaw 𝔰.ϱ ∗ₘ volume.map embedH).map
  (orbitPoint 𝔰.top) = (complexBasis 𝔰).floorQuadric 𝔰.top := ext_of_lintegral _ fun f hf ↦ by
  let χ Γ (p : ℂ × U 1) := open Calc in update
    (𝔰.definiteCols *ᵥ (√(Γ + ‖p.1‖ ^ 2) * p.2.1.1 · 𝔰.k₀)) 𝔰.z p.1
  erw [(HyperbolicBasis.isDisintegration_floorVolume _ _
    (map_inclMatrix_eq_floorVolume (inr ∘ inl))).unique (l' :=
    ((fun Γ ↦ map (χ Γ) (volume.withDensity fun p ↦ .ofReal (sphereDensity 𝔰.k (Γ + ‖p.1‖ ^ 2)⁺)))
    <| 2 * im ·.1)) ⟨fun a s ↦ ?_, fun f m ↦ ?_⟩] <;> simp (disch := with_unfolding_all fun_prop)
    only [lintegral_map, lintegral_mconv, lintegral_withDensity_eq_lintegral_mul, Pi.mul_apply]
  any_goals exact continuous_lintegral_and_lt_top ((s.image_auto (· 𝔰.z)).prod isCompact_univ) (by
    fun_prop) fun _ _ h ↦ ⟨⟨_, subset_closure (right_ne_zero_of_mul h), rfl⟩, ⟨⟩⟩
  all_goals simp (disch := fun_prop) only [volume_eq_prod, lintegral_prod, lintegral_const_mul]
  · rw [← lintegral_neg_eq_self, (by simp : 2 * im _ = -1)]; congr with c
    rw [← lintegral_inv_eq_self]; by_cases 1 < ‖c‖; congr!
    all_goals simp_all [cellDensity, χ, -middleGram, -splitGram]
  erw [lintegral_lintegral_swap, ← measurePreserving_sumElim.lintegral_comp, lintegral_prod_symm,
    ← (volume_preserving_funUnique ..).symm.lintegral_comp] <;> try fun_prop
  congr with c; erw [lintegral_eq_polar 𝔰.k₀, ← lintegral_indicator (by simp),
    ← lintegral_add_right_eq_self
    _ (‖c‖ ^ 2), ← smul_map_volume_mul_left two_ne_zero, lintegral_smul_measure, lintegral_map,
    lintegral_map, smul_eq_mul, ← lintegral_const_mul] <;> try fun_prop (disch := simp)
  congr with Γ; fun_cases indicator <;> simp_all [-mulVec_smul, ← mul_div, mul_assoc]
  congr! 5 with u
  simp [-mulVec_smul, χ, apply_ite conj, mul_left_comm I, -map_mul, ← Finset.sum_mul,
    by simpa using congr(diag $(u.2) 𝔰.k₀)]; norm_cast; grind

instance : IsProbabilityMeasure (volume.map (@embedH 𝔰)) :=
  (isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance
