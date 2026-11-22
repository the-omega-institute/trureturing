/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/DampedPrefixSampling
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/DampedPrefixSampling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Spectral bin control for a signed prefix with exponential damping. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder.SpectralSampling

/-! Exponential weighting of local spectral integrals. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
open Set MeasureTheory Filter
open scoped Function
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder

private def negativeUnitCell (n : ℕ) : Set ℝ := Ioc (-((n : ℝ) + 1)) (- (n : ℝ))

private theorem iUnion_negativeUnitCell : ⋃ n, negativeUnitCell n = Iic 0 := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Iic, negativeUnitCell, Set.mem_Ioc]
  constructor
  · rintro ⟨n, -, hx⟩
    exact hx.trans (neg_nonpos.mpr (Nat.cast_nonneg n))
  · intro hx
    refine ⟨⌊-x⌋₊, ?_, ?_⟩
    · linarith [Nat.lt_floor_add_one (-x)]
    · linarith [Nat.floor_le (show 0 ≤ -x from neg_nonneg.mpr hx)]

private theorem negativeUnitCell_disjoint : Pairwise (Disjoint on negativeUnitCell) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro v hi hj
  change -((i : ℝ) + 1) < v ∧ v ≤ -(i : ℝ) at hi
  change -((j : ℝ) + 1) < v ∧ v ≤ -(j : ℝ) at hj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have h : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt hij
    linarith [hi.1, hj.2]
  · have h : (j : ℝ) + 1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt hji
    linarith [hi.2, hj.1]

private theorem finiteModes_norm_le (T : Finset ℕ) (γ : ℕ → ℝ) (a : ℕ → ℂ) (v : ℝ) :
    ‖finiteModes T γ a v‖ ≤ ∑ i ∈ T, ‖a i‖ := by
  unfold finiteModes
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [norm_mul, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-- The integral of the finite spectral sum against the exponential on the negative
half-line is bounded by the square mass of the frequency bins. -/
theorem exists_damped_mode_integral_le_square_mass :
    ∃ G : ℝ, 0 < G ∧ ∀ (b : ℤ → ℝ), (Summable fun k => b k ^ 2) →
      ∀ (T : Finset ℕ) (γ : ℕ → ℝ) (a : ℕ → ℂ) (C : ℝ), 0 < C →
      (∀ k, binMass T γ a k ≤ C * b k) →
      (∫ v in Iic (0 : ℝ), Real.exp (v / 2) * ‖finiteModes T γ a v‖) ≤
        (G * Real.sqrt (∑' k : ℤ, b k ^ 2)) * C := by
  obtain ⟨G, hG, hlocal⟩ := exists_local_mode_integral_le_square_mass
  let r := Real.exp (-(1 / 2 : ℝ))
  have hr₀ : 0 ≤ r := (Real.exp_pos _).le
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  refine ⟨G / (1 - r), div_pos hG (sub_pos.mpr hr₁), ?_⟩
  intro b hb T γ a C hC hbin
  let f (v : ℝ) := Real.exp (v / 2) * ‖finiteModes T γ a v‖
  have hmodes : Continuous (finiteModes T γ a) := by
    unfold finiteModes
    fun_prop
  have hfmeas : Continuous f := by unfold f; fun_prop
  have hf (v : ℝ) : 0 ≤ f v := by unfold f; positivity
  have hexp : IntegrableOn (fun v : ℝ => Real.exp (v / 2)) (Iic 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using
      (integrableOn_exp_mul_Iic (a := (1 / 2 : ℝ)) (by norm_num) 0)
  have hfi : IntegrableOn f (Iic 0) := by
    refine (hexp.mul_const (∑ i ∈ T, ‖a i‖)).mono' hfmeas.aestronglyMeasurable ?_
    filter_upwards with v
    rw [Real.norm_of_nonneg (hf v)]
    exact mul_le_mul_of_nonneg_left (finiteModes_norm_le T γ a v) (Real.exp_nonneg _)
  let L := (G * Real.sqrt (∑' k : ℤ, b k ^ 2)) * C
  have hbelt (n : ℕ) :
      (∫ v in negativeUnitCell n, f v) ≤ L * r ^ n := by
    let c : ℝ := -(n : ℝ)
    have hc : negativeUnitCell n ⊆ Icc (c-1) (c+1) := by
      intro v hv
      change -((n : ℝ)+1) < v ∧ v ≤ -(n : ℝ) at hv
      constructor <;> dsimp [c] <;> linarith [hv.1, hv.2]
    have hcont : IntegrableOn (fun v => ‖finiteModes T γ a v‖) (Icc (c-1) (c+1)) :=
      hmodes.norm.integrableOn_Icc
    have hrestrict : negativeUnitCell n ⊆ Iic (0 : ℝ) := by
      intro v hv
      exact (show v ≤ -(n : ℝ) from hv.2).trans (neg_nonpos.mpr (Nat.cast_nonneg n))
    have hcell : MeasurableSet (negativeUnitCell n) := measurableSet_Ioc
    have hpow : Real.exp (c / 2) = r ^ n := by
      dsimp [c, r]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    calc
      _ ≤ ∫ v in negativeUnitCell n, Real.exp (c / 2) * ‖finiteModes T γ a v‖ := by
        refine setIntegral_mono_on (hfi.mono_set hrestrict)
          ((hcont.mono_set hc).const_mul _) hcell fun v hv => ?_
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply Real.exp_le_exp.mpr
        exact div_le_div_of_nonneg_right (show v ≤ c from hv.2) (by norm_num)
      _ = Real.exp (c / 2) * ∫ v in negativeUnitCell n, ‖finiteModes T γ a v‖ :=
        integral_const_mul _ _
      _ ≤ Real.exp (c / 2) * ∫ v in Icc (c-1) (c+1), ‖finiteModes T γ a v‖ := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        exact setIntegral_mono_set hcont (ae_of_all _ fun v => norm_nonneg _) (Eventually.of_forall hc)
      _ ≤ Real.exp (c / 2) * L :=
        mul_le_mul_of_nonneg_left (hlocal b hb T γ a C hC hbin c) (Real.exp_nonneg _)
      _ = L * r ^ n := by rw [hpow, mul_comm]
  have hfi' : IntegrableOn f (⋃ n, negativeUnitCell n) := iUnion_negativeUnitCell ▸ hfi
  have hsum : HasSum (fun n => ∫ v in negativeUnitCell n, f v)
      (∫ v in Iic 0, f v) := by
    have h := hasSum_integral_iUnion (s := negativeUnitCell) (fun n => measurableSet_Ioc)
      negativeUnitCell_disjoint hfi'
    rwa [iUnion_negativeUnitCell] at h
  have hgeom := (hasSum_geometric_of_lt_one hr₀ hr₁).mul_left L
  calc
    _ = ∑' n, ∫ v in negativeUnitCell n, f v := hsum.tsum_eq.symm
    _ ≤ ∑' n : ℕ, L * r ^ n :=
      hsum.summable.tsum_le_tsum hbelt hgeom.summable
    _ = _ := by
      rw [hgeom.tsum_eq]
      dsimp [L]
      ring

private theorem integral_reflected_prefix_exp (J : Finset ℕ)
    (v : ℕ → ℝ) (a : ℕ → ℂ) (hv : ∀ n ∈ J, v n ≤ 0)
    {z : ℂ} (hz : 0 < z.re) :
    (∫ t in Iic (0 : ℝ), (∑ n ∈ J, if t ≤ v n then a n else 0) *
      Complex.exp (z * (t : ℂ))) =
      ∑ n ∈ J, a n * (Complex.exp (z * (v n : ℂ)) / z) := by
  let f (n : ℕ) (t : ℝ) := (Iic (v n)).indicator (fun t => a n * Complex.exp (z * t)) t
  have hpoint (t : ℝ) :
      (∑ n ∈ J, if t ≤ v n then a n else 0) * Complex.exp (z * (t : ℂ)) =
        ∑ n ∈ J, f n t := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : t ≤ v n <;> simp [f, h]
  have hfi (n : ℕ) : Integrable (f n) :=
    (integrable_indicator_iff measurableSet_Iic).mpr
      ((integrableOn_exp_mul_complex_Iic hz (v n)).const_mul (a n))
  simp_rw [hpoint]
  rw [integral_finsetSum J (fun n hn => (hfi n).integrableOn)]
  apply Finset.sum_congr rfl
  intro n hn
  have hcut : Iic (0 : ℝ) ∩ Iic (v n) = Iic (v n) :=
    inter_eq_right.mpr (Iic_subset_Iic.mpr (hv n hn))
  rw [show (fun t => f n t) = (Iic (v n)).indicator
    (fun t => a n * Complex.exp (z * (t : ℂ))) by rfl,
    setIntegral_indicator measurableSet_Iic, hcut, integral_const_mul,
    integral_exp_mul_complex_Iic hz]

/-- A uniform prefix bound controls the damped reciprocal spectral sum. The
square bin masses aggregate counts with the same frequency, including repetitions. -/
theorem exists_damped_reciprocal_sum_le_square_mass :
    ∃ K : ℝ, 0 < K ∧ ∀ (J T : Finset ℕ) (v γ : ℕ → ℝ) (a c : ℕ → ℂ)
      (P : ℝ) (b : ℤ → ℝ),
      (∀ n ∈ J, v n ≤ 0) →
      (∀ t ≤ (0 : ℝ), ‖∑ n ∈ J, if t ≤ v n then a n else 0‖ ≤ P) →
      (Summable fun k => b k ^ 2) → (∀ k, binMass T γ c k ≤ b k) →
      ‖∑ i ∈ T, c i * (∑ n ∈ J, a n *
        (Complex.exp ((1 / 2 + Complex.I * (γ i : ℂ)) * (v n : ℂ)) /
          (1 / 2 + Complex.I * (γ i : ℂ))))‖ ≤
        K * P * Real.sqrt (∑' k : ℤ, b k ^ 2) := by
  obtain ⟨K, hK, hbound⟩ := exists_damped_mode_integral_le_square_mass
  refine ⟨K, hK, ?_⟩
  intro J T v γ a c P b hv hpref hb hbin
  have hP : 0 ≤ P := (norm_nonneg _).trans (hpref 0 le_rfl)
  let A (t : ℝ) : ℂ := ∑ n ∈ J, if t ≤ v n then a n else 0
  let z (i : ℕ) : ℂ := 1 / 2 + Complex.I * (γ i : ℂ)
  have hz (i : ℕ) : (z i).re = 1 / 2 := by
    simp [z, Complex.add_re, Complex.mul_re, Complex.div_re]
  have hzpos (i : ℕ) : 0 < (z i).re := by rw [hz]; norm_num
  have hA : Measurable A := by
    apply Finset.measurable_sum
    intro n hn
    exact measurable_const.piecewise (s := Iic (v n)) measurableSet_Iic measurable_const
  let f (i : ℕ) (t : ℝ) : ℂ := c i * (A t * Complex.exp (z i * (t : ℂ)))
  let w (t : ℝ) : ℝ := Real.exp (t / 2)
  have hw : IntegrableOn w (Iic 0) := by
    simpa only [w, div_eq_mul_inv, one_mul, mul_comm] using
      (integrableOn_exp_mul_Iic (a := (1 / 2 : ℝ)) (by norm_num) 0)
  have hfmem (i : ℕ) : Measurable (f i) :=
    measurable_const.mul (hA.mul ((continuous_const.mul Complex.continuous_ofReal).cexp.measurable))
  have hnorm (i : ℕ) (t : ℝ) : ‖f i t‖ = ‖c i‖ * ‖A t‖ * w t := by
    dsimp only [f, w]
    rw [norm_mul, norm_mul, ← mul_assoc, Complex.norm_exp, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hz]
    congr 2
    ring
  have hfi (i : ℕ) : IntegrableOn (f i) (Iic 0) := by
    refine (hw.const_mul (‖c i‖ * P)).mono' (hfmem i).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    rw [hnorm]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hpref t ht) (norm_nonneg _)) (Real.exp_nonneg _)
  have hpoint (t : ℝ) :
      ∑ i ∈ T, f i t = A t * (w t : ℂ) * finiteModes T γ c t := by
    unfold finiteModes
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [f, w, z]
    rw [add_mul, Complex.exp_add, Complex.ofReal_exp]
    rw [show (1 / 2 : ℂ) * (t : ℂ) = ((t / 2 : ℝ) : ℂ) by push_cast; ring]
    ring
  let g (t : ℝ) := ∑ i ∈ T, f i t
  have hg : IntegrableOn g (Iic 0) := integrable_finsetSum T (fun i hi => hfi i)
  have heq :
      (∫ t in Iic (0 : ℝ), g t) =
        ∑ i ∈ T, c i * (∑ n ∈ J, a n * (Complex.exp (z i * (v n : ℂ)) / z i)) := by
    unfold g
    rw [integral_finsetSum T (fun i hi => hfi i)]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [f, integral_const_mul]
    rw [integral_reflected_prefix_exp J v a hv (hzpos i)]
  have hgdom : IntegrableOn (fun t => P * w t * ‖finiteModes T γ c t‖) (Iic 0) := by
    have hcont : Continuous (fun t => P * w t * ‖finiteModes T γ c t‖) := by
      unfold w finiteModes
      fun_prop
    refine (hw.mul_const (P * ∑ i ∈ T, ‖c i‖)).mono' hcont.aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_of_nonneg (by unfold w; positivity)]
    calc
      _ ≤ P * w t * (∑ i ∈ T, ‖c i‖) :=
        mul_le_mul_of_nonneg_left (finiteModes_norm_le T γ c t) (by unfold w; positivity)
      _ = _ := by ring
  change ‖∑ i ∈ T, c i * (∑ n ∈ J, a n * (Complex.exp (z i * (v n : ℂ)) / z i))‖ ≤ _
  rw [← heq]
  calc
    _ ≤ ∫ t in Iic (0 : ℝ), ‖g t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Iic (0 : ℝ), P * w t * ‖finiteModes T γ c t‖ := by
      refine setIntegral_mono_on hg.norm hgdom measurableSet_Iic fun t ht => ?_
      rw [show g t = A t * (w t : ℂ) * finiteModes T γ c t from hpoint t,
        norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hpref t ht) (Real.exp_nonneg _)) (norm_nonneg _)
    _ = P * ∫ t in Iic (0 : ℝ), w t * ‖finiteModes T γ c t‖ := by
      simp only [mul_assoc, integral_const_mul]
    _ ≤ P * ((K * Real.sqrt (∑' k : ℤ, b k ^ 2)) * 1) :=
      mul_le_mul_of_nonneg_left (hbound b hb T γ c 1 zero_lt_one (by simpa using hbin)) hP
    _ = _ := by ring

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
