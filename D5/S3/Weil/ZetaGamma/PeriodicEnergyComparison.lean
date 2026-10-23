/- GID: D5/S3/Weil/ZetaGamma/PeriodicEnergyComparison
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/PeriodicEnergyComparison
   mirror-E: none(waiver:analytic-periodic-Gamma-energy)
   anchors: []
   utility: none
   digest: Compare full extended actual Gamma energies using original-zero-extension AE evenness and nonnegative rate Tonelli. -/

import D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport

noncomputable section
open MeasureTheory Set Filter
open MeasureTheory.Measure
open scoped ComplexConjugate ENNReal Topology
open D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport

namespace D5.S3.Weil.ZetaGamma.PeriodicEnergyComparison

private def laplaceWeight (b s : ℝ) : ℝ := Real.exp (-b * |s|)

private theorem laplaceWeight_nonneg (b s : ℝ) : 0 ≤ laplaceWeight b s :=
  (Real.exp_pos _).le

private theorem laplaceWeight_neg (b s : ℝ) :
    laplaceWeight b (-s) = laplaceWeight b s := by
  simp only [laplaceWeight, abs_neg]

private theorem laplaceWeight_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (laplaceWeight b) volume := by
  have hp : IntegrableOn (laplaceWeight b) (Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (a := -b) (by linarith) 0).congr_fun
      (fun s hs => ?_) measurableSet_Ioi
    simp only [laplaceWeight, abs_of_pos (mem_Ioi.mp hs)]
  have hn : IntegrableOn (laplaceWeight b) (Iic 0) := by
    refine (integrableOn_exp_mul_Iic (a := b) hb 0).congr_fun
      (fun s hs => ?_) measurableSet_Iic
    simp only [laplaceWeight, abs_of_nonpos (mem_Iic.mp hs)]
    congr 1
    ring
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hn.union hp

/-- Reflection of the *real* correlation is the required symmetry. Complex
correlation itself need not be even. The split is at zero, with no endpoint
value condition and no loss of physical Lebesgue mass. -/
private theorem laplace_even_integral_eq_twice_positive
    (b : ℝ) (R : ℝ → ℝ) (hR : ∀ s, R (-s) = R s)
    (hInt : Integrable (fun s => laplaceWeight b s * R s) volume) :
    (∫ s : ℝ, laplaceWeight b s * R s) =
      2 * ∫ s in Ioi (0 : ℝ), laplaceWeight b s * R s := by
  let H : ℝ → ℝ := fun s => laplaceWeight b s * R s
  have hH (s : ℝ) : H (-s) = H s := by
    simp only [H, laplaceWeight_neg, hR]
  have href : (∫ s in Iic (0 : ℝ), H s) = ∫ s in Ioi (0 : ℝ), H s := by
    calc
      _ = ∫ s in Ioi (0 : ℝ), H (-s) := by
        simpa only [neg_zero] using (integral_comp_neg_Ioi 0 H).symm
      _ = _ := integral_congr_ae (Eventually.of_forall hH)
  have hsplit := integral_add_compl (μ := (volume : Measure ℝ))
    (s := Ioi (0 : ℝ)) measurableSet_Ioi hInt
  change (∫ s in Ioi (0 : ℝ), H s) + (∫ s in (Ioi (0 : ℝ))ᶜ, H s) =
    ∫ s : ℝ, H s at hsplit
  rw [compl_Ioi, href] at hsplit
  change (∫ s : ℝ, H s) = 2 * ∫ s in Ioi (0 : ℝ), H s
  linarith

private def weightedPeriodicJoint (d t : ℝ) [Fact (0 < d)]
    (w : ℝ → ℝ) (u : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (w p.2 : ℂ) * conj (u p.1) * periodicExtension d t u (p.1 - p.2)

private def weightedZeroJoint (d t : ℝ) (w : ℝ → ℝ)
    (u : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (w p.2 : ℂ) * conj (u p.1) * zeroExtension d t u (p.1 - p.2)

/-- Absolute Fubini payment for arbitrary integrable real weights, hence for
Laplace. The bound uses the actual circle shift and original physical mass. -/
private theorem weightedPeriodicJoint_integrable
    (d t : ℝ) [Fact (0 < d)] (w : ℝ → ℝ) (hw : Integrable w volume)
    (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure d t)) :
    Integrable (weightedPeriodicJoint d t w u) ((windowMeasure d t).prod volume) := by
  let F : ℝ × ℝ → ℂ := fun p => weightedPeriodicJoint d t w u p.swap
  let N : ℝ → ℝ := fun s => ∫ x, ‖F (s, x)‖ ∂windowMeasure d t
  have hwc : AEStronglyMeasurable (fun s => (w s : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hw.aestronglyMeasurable
  have huc : AEStronglyMeasurable (fun p : ℝ × ℝ => conj (u p.2))
      (volume.prod (windowMeasure d t)) :=
    Complex.continuous_conj.comp_aestronglyMeasurable hu.aestronglyMeasurable.comp_snd
  have hFm : AEStronglyMeasurable F (volume.prod (windowMeasure d t)) :=
    (hwc.comp_fst.mul huc).mul (periodic_shift_joint_aestronglyMeasurable d t u hu)
  have hSlice (s : ℝ) : Integrable (fun x => F (s, x)) (windowMeasure d t) := by
    have h := (l2_complex_correlation_integrable hu
      (periodic_shift_memLp d t u hu s)).const_mul (w s : ℂ)
    simpa only [F, weightedPeriodicJoint, Prod.swap_prod_mk, mul_assoc] using h
  have hnorm (s x : ℝ) : ‖F (s, x)‖ =
      ‖w s‖ * (‖u x‖ * ‖periodicExtension d t u (x - s)‖) := by
    simp only [F, weightedPeriodicJoint, Prod.swap_prod_mk, norm_mul,
      Complex.norm_conj, Complex.norm_real, mul_assoc]
  have hNle (s : ℝ) : N s ≤ windowEnergy d t u * ‖w s‖ := by
    dsimp only [N]
    simp_rw [hnorm s]
    rw [integral_const_mul, mul_comm (windowEnergy d t u)]
    exact mul_le_mul_of_nonneg_left
      (periodic_correlation_integrable_le d t u hu s).2 (norm_nonneg _)
  have hNint : Integrable N volume := by
    apply (hw.norm.const_mul (windowEnergy d t u)).mono' hFm.norm.integral_prod_right'
    exact Eventually.of_forall fun s => by
      rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg (F (s, x)))]
      exact hNle s
  have hFint : Integrable F (volume.prod (windowMeasure d t)) :=
    (integrable_prod_iff hFm).mpr ⟨Eventually.of_forall hSlice, hNint⟩
  simpa only [Function.comp_def, F, Prod.swap_swap] using hFint.swap

/-- The noncentral joint integrand is dominated by the periodic joint
integrand by the unique-copy norm inequality, with factor one. -/
private theorem weightedDifferenceCorrelation_integrable
    (d t : ℝ) [Fact (0 < d)] (w : ℝ → ℝ) (hw : Integrable w volume)
    (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure d t)) :
    Integrable (weightedDifferenceCorrelation d t w u)
      ((windowMeasure d t).prod volume) := by
  have hp := weightedPeriodicJoint_integrable d t w hw u hu
  have hwc : AEStronglyMeasurable (fun s => (w s : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hw.aestronglyMeasurable
  have huc : AEStronglyMeasurable (fun p : ℝ × ℝ => conj (u p.2))
      (volume.prod (windowMeasure d t)) :=
    Complex.continuous_conj.comp_aestronglyMeasurable hu.aestronglyMeasurable.comp_snd
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => weightedDifferenceCorrelation d t w u p.swap)
      (volume.prod (windowMeasure d t)) :=
    (hwc.comp_fst.mul huc).mul
      ((periodic_shift_joint_aestronglyMeasurable d t u hu).sub
        (zero_shift_joint_aestronglyMeasurable d t u hu))
  apply hp.norm.mono' (by simpa only [Function.comp_def, Prod.swap_swap] using hm.prod_swap)
  exact Eventually.of_forall fun p => by
    change ‖weightedDifferenceCorrelation d t w u p‖ ≤
      ‖weightedPeriodicJoint d t w u p‖
    simp only [weightedDifferenceCorrelation, weightedPeriodicJoint, norm_mul]
    exact mul_le_mul_of_nonneg_left
      (periodic_minus_zero_norm_le d t u (p.1 - p.2))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))

private theorem weightedZeroJoint_integrable
    (d t : ℝ) [Fact (0 < d)] (w : ℝ → ℝ) (hw : Integrable w volume)
    (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure d t)) :
    Integrable (weightedZeroJoint d t w u) ((windowMeasure d t).prod volume) := by
  apply ((weightedPeriodicJoint_integrable d t w hw u hu).sub
    (weightedDifferenceCorrelation_integrable d t w hw u hu)).congr
  exact Eventually.of_forall fun p => by
    simp only [Pi.sub_apply, weightedPeriodicJoint, weightedDifferenceCorrelation,
      weightedZeroJoint]
    ring

private theorem weightedPeriodicJoint_slice
    (d t : ℝ) [Fact (0 < d)] (w : ℝ → ℝ) (u : ℝ → ℂ) (s : ℝ) :
    (∫ x, weightedPeriodicJoint d t w u (x, s) ∂windowMeasure d t) =
      (w s : ℂ) * periodicCorrelation d t u s := by
  simp only [weightedPeriodicJoint, periodicCorrelation, mul_assoc, integral_const_mul]

private theorem weightedZeroJoint_slice
    (d t : ℝ) (w : ℝ → ℝ) (u : ℝ → ℂ) (s : ℝ) :
    (∫ x, weightedZeroJoint d t w u (x, s) ∂windowMeasure d t) =
      (w s : ℂ) * zeroCorrelation d t u s := by
  rw [zeroCorrelation_eq_window]
  simp only [weightedZeroJoint, mul_assoc, integral_const_mul]

private theorem weightedDifferenceCorrelation_slice
    (d t : ℝ) [Fact (0 < d)] (w : ℝ → ℝ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) (s : ℝ) :
    (∫ x, weightedDifferenceCorrelation d t w u (x, s) ∂windowMeasure d t) =
      (w s : ℂ) * (periodicCorrelation d t u s - zeroCorrelation d t u s) := by
  simp only [weightedDifferenceCorrelation, mul_assoc]
  rw [integral_const_mul, correlation_difference_slice d t u hu s]

/-- The central copy is transported by the same measure-preserving reflection.
This lemma pays both its integrability and its complex integral identity. -/
private theorem weighted_central_image_integrable_and_identity
    (d t : ℝ) [Fact (0 < d)] (w : ℝ → ℝ) (hw : Integrable w volume)
    (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure d t)) :
    Integrable (fun p : ℝ × ℝ =>
      (w (p.1 - p.2) : ℂ) * conj (u p.1) * u p.2)
      ((windowMeasure d t).prod (windowMeasure d t)) ∧
    (∫ s : ℝ, (w s : ℂ) * zeroCorrelation d t u s) =
      ∫ p : ℝ × ℝ, (w (p.1 - p.2) : ℂ) * conj (u p.1) * u p.2
        ∂((windowMeasure d t).prod (windowMeasure d t)) := by
  let A := weightedZeroJoint d t w u
  let B : ℝ × ℝ → ℂ := fun p => (w (p.1 - p.2) : ℂ) * conj (u p.1) * u p.2
  have hA : Integrable A ((windowMeasure d t).prod volume) :=
    weightedZeroJoint_integrable d t w hw u hu
  have hEq : A ∘ copyReflection d 0 =
      (univ ×ˢ Ioc t (t + d)).indicator B := by
    classical
    funext p
    change (w (p.1 + (0 : ℤ) • d - p.2) : ℂ) * conj (u p.1) *
      zeroExtension d t u (p.1 - (p.1 + (0 : ℤ) • d - p.2)) = _
    simp only [zero_zsmul, add_zero]
    have hy : p.1 - (p.1 - p.2) = p.2 := by ring
    rw [hy]
    by_cases hp : p.2 ∈ Ioc t (t + d)
    · have hpp : p ∈ univ ×ˢ Ioc t (t + d) := ⟨mem_univ _, hp⟩
      simp only [zeroExtension, Set.indicator_of_mem hp, Set.indicator_of_mem hpp, B]
    · have hpp : p ∉ univ ×ˢ Ioc t (t + d) := fun h => hp h.2
      simp only [zeroExtension, Set.indicator_of_notMem hp, mul_zero,
        Set.indicator_of_notMem hpp]
  have hMP := copyReflection_measurePreserving d t 0
  have hcomp := hMP.integrable_comp_of_integrable hA
  rw [hEq] at hcomp
  have hset : MeasurableSet (univ ×ˢ Ioc t (t + d) : Set (ℝ × ℝ)) :=
    MeasurableSet.prod MeasurableSet.univ measurableSet_Ioc
  have hB : Integrable B ((windowMeasure d t).prod (windowMeasure d t)) := by
    rw [windowMeasure_prod_windowMeasure]
    exact (integrable_indicator_iff hset).mp hcomp
  refine ⟨hB, ?_⟩
  calc
    _ = ∫ s : ℝ, ∫ x, A (x, s) ∂windowMeasure d t := by
      simp only [A, weightedZeroJoint_slice]
    _ = ∫ p, A p ∂((windowMeasure d t).prod volume) :=
      (integral_prod_symm A hA).symm
    _ = ∫ p, A (copyReflection d 0 p) ∂((windowMeasure d t).prod volume) :=
      (hMP.integral_comp' A).symm
    _ = ∫ p, (univ ×ˢ Ioc t (t + d)).indicator B p
        ∂((windowMeasure d t).prod volume) := congrArg
          (fun f => ∫ p, f p ∂((windowMeasure d t).prod volume)) hEq
    _ = _ := by rw [integral_indicator hset, ← windowMeasure_prod_windowMeasure]

/-- Summability of the actual Laplace lattice on every real displacement.
The triangle inequality pays the finite prefactor; neither a replacement
kernel nor a target-pairing integrability supplier is introduced. -/
private theorem laplace_lattice_summable
    (d : ℝ) (hd : 0 < d) (b : ℝ) (hb : 0 < b) (h : ℝ) :
    Summable (fun m : ℤ => laplaceWeight b (h + m • d)) := by
  have hbound (z : ℝ) : laplaceWeight b (h + z) ≤
      Real.exp (b * |h|) * Real.exp (-b * |z|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hz : |z| ≤ |h + z| + |h| := by
      calc
        |z| = |(h + z) + (-h)| := by congr 1; ring
        _ ≤ |h + z| + |-h| := abs_add_le _ _
        _ = |h + z| + |h| := by rw [abs_neg]
    change -b * |h + z| ≤ b * |h| + -b * |z|
    nlinarith
  have hg : Summable (fun n : ℕ => Real.exp (b * |h|) *
      Real.exp ((n : ℝ) * (-b * d))) :=
    (Real.summable_exp_nat_mul_iff.mpr (by nlinarith : -b * d < 0)).mul_left _
  have hp : Summable (fun n : ℕ => laplaceWeight b (h + (n : ℤ) • d)) := by
    apply hg.of_nonneg_of_le (fun n => laplaceWeight_nonneg _ _)
    intro n
    have hn : 0 ≤ (n : ℝ) * d := mul_nonneg (Nat.cast_nonneg _) hd.le
    calc
      _ = laplaceWeight b (h + (n : ℝ) * d) := by simp only [zsmul_eq_mul, Int.cast_natCast]
      _ ≤ Real.exp (b * |h|) * Real.exp (-b * |(n : ℝ) * d|) := hbound _
      _ = _ := by
        rw [abs_of_nonneg hn,
          show -b * ((n : ℝ) * d) = (n : ℝ) * (-b * d) by ring]
  have hn : Summable (fun n : ℕ => laplaceWeight b (h + (-((n : ℤ) + 1)) • d)) := by
    apply ((summable_nat_add_iff 1).mpr hg).of_nonneg_of_le (fun n => laplaceWeight_nonneg _ _)
    intro n
    have hn : 0 ≤ ((n : ℝ) + 1) * d := by positivity
    calc
      _ = laplaceWeight b (h + -(((n : ℝ) + 1) * d)) := by
        simp only [zsmul_eq_mul, Int.cast_neg, Int.cast_add, Int.cast_natCast,
          Int.cast_one, neg_mul]
      _ ≤ Real.exp (b * |h|) * Real.exp (-b * |-(((n : ℝ) + 1) * d)|) := hbound _
      _ = _ := by
        rw [abs_neg, abs_of_nonneg hn]
        simp only [Nat.cast_add, Nat.cast_one]
        rw [show -b * (((n : ℝ) + 1) * d) = ((n : ℝ) + 1) * (-b * d) by ring]
  exact hp.of_nat_of_neg_add_one hn

private def laplacePeriodicKernel (d b x y : ℝ) : ℝ :=
  ∑' m : ℤ, laplaceWeight b (x - y + m • d)

private theorem laplacePeriodicKernel_eq_central_add_image
    (d : ℝ) (hd : 0 < d) (b : ℝ) (hb : 0 < b) (x y : ℝ) :
    laplacePeriodicKernel d b x y = laplaceWeight b (x - y) +
      weightedImageKernel d (laplaceWeight b) x y := by
  classical
  have h := (laplace_lattice_summable d hd b hb (x - y)).tsum_eq_add_tsum_ite 0
  simpa only [laplacePeriodicKernel, weightedImageKernel, zero_zsmul, add_zero] using h

/-- Original complex L2 periodic correlation unfolded against the entire
integer Laplace lattice, including its central copy. Fubini, absolute lattice
summation, and both image integrabilities are conclusions of this theorem. -/
private theorem laplace_periodic_correlation_unfolding
    (d t b : ℝ) [hd : Fact (0 < d)] (hb : 0 < b)
    (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure d t)) :
    Integrable (fun s : ℝ => (laplaceWeight b s : ℂ) * periodicCorrelation d t u s) ∧
    Integrable (fun p : ℝ × ℝ =>
      (laplacePeriodicKernel d b p.1 p.2 : ℂ) * conj (u p.1) * u p.2)
      ((windowMeasure d t).prod (windowMeasure d t)) ∧
    (∫ s : ℝ, (laplaceWeight b s : ℂ) * periodicCorrelation d t u s) =
      ∫ p : ℝ × ℝ,
        (laplacePeriodicKernel d b p.1 p.2 : ℂ) * conj (u p.1) * u p.2
          ∂((windowMeasure d t).prod (windowMeasure d t)) := by
  have hw := laplaceWeight_integrable hb
  have hp := weightedPeriodicJoint_integrable d t (laplaceWeight b) hw u hu
  have hD := weightedDifferenceCorrelation_integrable d t (laplaceWeight b) hw u hu
  obtain ⟨hB, hDB⟩ := weightedLattice_image_integrable_and_identity
    d t (laplaceWeight b) u hD
  obtain ⟨hC, h0C⟩ := weighted_central_image_integrable_and_identity
    d t (laplaceWeight b) hw u hu
  have hs : Integrable (fun s : ℝ =>
      (laplaceWeight b s : ℂ) * periodicCorrelation d t u s) := by
    simpa only [weightedPeriodicJoint_slice] using hp.integral_prod_right
  have hsum (p : ℝ × ℝ) :
      (laplacePeriodicKernel d b p.1 p.2 : ℂ) * conj (u p.1) * u p.2 =
      (laplaceWeight b (p.1 - p.2) : ℂ) * conj (u p.1) * u p.2 +
        conj (u p.1) * (weightedImageKernel d (laplaceWeight b) p.1 p.2 : ℂ) * u p.2 := by
    rw [laplacePeriodicKernel_eq_central_add_image d hd.out b hb,
      Complex.ofReal_add]
    ring
  have hK : Integrable (fun p : ℝ × ℝ =>
      (laplacePeriodicKernel d b p.1 p.2 : ℂ) * conj (u p.1) * u p.2)
      ((windowMeasure d t).prod (windowMeasure d t)) := by
    exact (hC.add hB).congr (Eventually.of_forall fun p => (hsum p).symm)
  refine ⟨hs, hK, ?_⟩
  have hZ := weightedZeroJoint_integrable d t (laplaceWeight b) hw u hu
  have hsplit : weightedPeriodicJoint d t (laplaceWeight b) u =
      fun p => weightedZeroJoint d t (laplaceWeight b) u p +
        weightedDifferenceCorrelation d t (laplaceWeight b) u p := by
    funext p
    simp only [weightedPeriodicJoint, weightedZeroJoint, weightedDifferenceCorrelation]
    ring
  calc
    _ = ∫ p, weightedPeriodicJoint d t (laplaceWeight b) u p
        ∂((windowMeasure d t).prod volume) := by
      rw [integral_prod_symm _ hp]
      simp only [weightedPeriodicJoint_slice]
    _ = (∫ p, weightedZeroJoint d t (laplaceWeight b) u p
        ∂((windowMeasure d t).prod volume)) +
        ∫ p, weightedDifferenceCorrelation d t (laplaceWeight b) u p
          ∂((windowMeasure d t).prod volume) := by
      rw [hsplit, integral_add hZ hD]
    _ = (∫ p : ℝ × ℝ,
          (laplaceWeight b (p.1 - p.2) : ℂ) * conj (u p.1) * u p.2
          ∂((windowMeasure d t).prod (windowMeasure d t))) +
        ∫ p : ℝ × ℝ,
          conj (u p.1) * (weightedImageKernel d (laplaceWeight b) p.1 p.2 : ℂ) * u p.2
          ∂((windowMeasure d t).prod (windowMeasure d t)) := by
      rw [integral_prod_symm _ hZ]
      simp only [weightedZeroJoint_slice]
      rw [h0C, hDB]
    _ = _ := by
      rw [← integral_add hC hB]
      exact integral_congr_ae (Eventually.of_forall fun p => (hsum p).symm)

private def zeroLaplaceEnergy (d t b : ℝ) (u : ℝ → ℂ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), laplaceWeight b s * zeroTranslationEnergy d t u s

private def periodicLaplaceEnergy (d t b : ℝ) [Fact (0 < d)] (u : ℝ → ℂ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), laplaceWeight b s * periodicTranslationEnergy d t u s

private theorem laplace_energy_integrable_of_bound
    (b : ℝ) (hb : 0 < b) (E : ℝ → ℝ) (C : ℝ)
    (hEm : AEStronglyMeasurable E volume) (hE : ∀ s, 0 ≤ E s ∧ E s ≤ C) :
    IntegrableOn (fun s => laplaceWeight b s * E s) (Ioi (0 : ℝ)) := by
  have hw := (laplaceWeight_integrable hb).restrict (s := Ioi (0 : ℝ))
  apply (hw.mul_const C).mono' (hw.aestronglyMeasurable.mul hEm.restrict)
  exact Eventually.of_forall fun s => by
    dsimp only [Pi.mul_apply]
    rw [Real.norm_of_nonneg (mul_nonneg (laplaceWeight_nonneg b s) (hE s).1)]
    exact mul_le_mul_of_nonneg_left (hE s).2 (laplaceWeight_nonneg b s)

/-- Actual single-rate energy difference. The image integral has coefficient
ONE. All integrability is derived from original L2 plus b>0. This theorem
consumes the generalized lattice owner; it does not assume an image supplier. -/
private theorem actual_single_rate_integrable_and_identity
    (d t b : ℝ) [Fact (0 < d)] (hb : 0 < b)
    (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure d t)) :
    IntegrableOn (fun s => laplaceWeight b s * zeroTranslationEnergy d t u s) (Ioi 0) ∧
    IntegrableOn (fun s => laplaceWeight b s * periodicTranslationEnergy d t u s) (Ioi 0) ∧
    Integrable (fun p : ℝ × ℝ => conj (u p.1) *
      (weightedImageKernel d (laplaceWeight b) p.1 p.2 : ℂ) * u p.2)
      ((windowMeasure d t).prod (windowMeasure d t)) ∧
    zeroLaplaceEnergy d t b u = periodicLaplaceEnergy d t b u +
      (∫ p : ℝ × ℝ, conj (u p.1) *
        (weightedImageKernel d (laplaceWeight b) p.1 p.2 : ℂ) * u p.2
        ∂((windowMeasure d t).prod (windowMeasure d t))).re := by
  have hE0 := laplace_energy_integrable_of_bound b hb _ _
    (zeroTranslationEnergy_aestronglyMeasurable d t u hu)
    (zeroTranslationEnergy_nonneg_le d t u hu)
  have hEP := laplace_energy_integrable_of_bound b hb _ _
    (periodicTranslationEnergy_aestronglyMeasurable d t u hu)
    (periodicTranslationEnergy_nonneg_le d t u hu)
  have hF := weightedDifferenceCorrelation_integrable d t (laplaceWeight b)
    (laplaceWeight_integrable hb) u hu
  have hB := (weightedLattice_image_integrable_and_identity
    d t (laplaceWeight b) u hF).1
  -- The full correlation unfolding is a live input to this energy consumer.
  obtain ⟨hpInt, hKInt, hpK⟩ := laplace_periodic_correlation_unfolding d t b hb u hu
  obtain ⟨hCInt, hzC⟩ := weighted_central_image_integrable_and_identity
    d t (laplaceWeight b) (laplaceWeight_integrable hb) u hu
  have hZ := weightedZeroJoint_integrable d t (laplaceWeight b)
    (laplaceWeight_integrable hb) u hu
  have hzInt : Integrable (fun s : ℝ =>
      (laplaceWeight b s : ℂ) * zeroCorrelation d t u s) := by
    simpa only [weightedZeroJoint_slice] using hZ.integral_prod_right
  have hkernel (p : ℝ × ℝ) :
      (laplacePeriodicKernel d b p.1 p.2 : ℂ) * conj (u p.1) * u p.2 =
      (laplaceWeight b (p.1 - p.2) : ℂ) * conj (u p.1) * u p.2 +
        conj (u p.1) * (weightedImageKernel d (laplaceWeight b) p.1 p.2 : ℂ) * u p.2 := by
    rw [laplacePeriodicKernel_eq_central_add_image d (Fact.out : 0 < d) b hb,
      Complex.ofReal_add]
    ring
  have hFB : (∫ p, weightedDifferenceCorrelation d t (laplaceWeight b) u p
      ∂((windowMeasure d t).prod volume)) =
      ∫ p : ℝ × ℝ, conj (u p.1) *
        (weightedImageKernel d (laplaceWeight b) p.1 p.2 : ℂ) * u p.2
        ∂((windowMeasure d t).prod (windowMeasure d t)) := by
    calc
      _ = ∫ s : ℝ, (laplaceWeight b s : ℂ) *
          (periodicCorrelation d t u s - zeroCorrelation d t u s) := by
        rw [integral_prod_symm _ hF]
        simp only [weightedDifferenceCorrelation_slice d t (laplaceWeight b) u hu]
      _ = (∫ s : ℝ, (laplaceWeight b s : ℂ) * periodicCorrelation d t u s) -
          ∫ s : ℝ, (laplaceWeight b s : ℂ) * zeroCorrelation d t u s := by
        simp_rw [mul_sub]
        exact integral_sub hpInt hzInt
      _ = (∫ p : ℝ × ℝ,
          (laplacePeriodicKernel d b p.1 p.2 : ℂ) * conj (u p.1) * u p.2
          ∂((windowMeasure d t).prod (windowMeasure d t))) -
          ∫ p : ℝ × ℝ, (laplaceWeight b (p.1 - p.2) : ℂ) * conj (u p.1) * u p.2
          ∂((windowMeasure d t).prod (windowMeasure d t)) := by rw [hpK, hzC]
      _ = _ := by
        have hadd : (∫ p : ℝ × ℝ,
            (laplacePeriodicKernel d b p.1 p.2 : ℂ) * conj (u p.1) * u p.2
            ∂((windowMeasure d t).prod (windowMeasure d t))) =
            (∫ p : ℝ × ℝ, (laplaceWeight b (p.1 - p.2) : ℂ) * conj (u p.1) * u p.2
            ∂((windowMeasure d t).prod (windowMeasure d t))) +
            ∫ p : ℝ × ℝ, conj (u p.1) *
              (weightedImageKernel d (laplaceWeight b) p.1 p.2 : ℂ) * u p.2
              ∂((windowMeasure d t).prod (windowMeasure d t)) := by
          simp_rw [hkernel]
          exact integral_add hCInt hB
        rw [hadd]
        ring
  let R : ℝ → ℝ := fun s => (periodicCorrelation d t u s - zeroCorrelation d t u s).re
  have hRneg (s : ℝ) : R (-s) = R s := by
    simp only [R, periodicCorrelation_neg, zeroCorrelation_neg, map_sub,
      Complex.sub_re, Complex.conj_re]
  have hSlice := hF.integral_prod_right
  have hSliceRe (s : ℝ) :
      (∫ x, weightedDifferenceCorrelation d t (laplaceWeight b) u (x, s)
        ∂windowMeasure d t).re = laplaceWeight b s * R s := by
    rw [weightedDifferenceCorrelation_slice d t (laplaceWeight b) u hu s]
    simp only [R, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  have hRint : Integrable (fun s => laplaceWeight b s * R s) := by
    convert hSlice.re using 1
    funext s
    exact (hSliceRe s).symm
  have hBreal : (∫ p : ℝ × ℝ, conj (u p.1) *
      (weightedImageKernel d (laplaceWeight b) p.1 p.2 : ℂ) * u p.2
      ∂((windowMeasure d t).prod (windowMeasure d t))).re =
        2 * ∫ s in Ioi (0 : ℝ), laplaceWeight b s * R s := by
    calc
      _ = (∫ p, weightedDifferenceCorrelation d t (laplaceWeight b) u p
          ∂((windowMeasure d t).prod volume)).re := congrArg Complex.re hFB.symm
      _ = (∫ s, ∫ x, weightedDifferenceCorrelation d t (laplaceWeight b) u (x, s)
          ∂windowMeasure d t).re := congrArg Complex.re
            (integral_prod_symm _ hF)
      _ = ∫ s, (∫ x, weightedDifferenceCorrelation d t (laplaceWeight b) u (x, s)
          ∂windowMeasure d t).re := (integral_re hSlice).symm
      _ = ∫ s : ℝ, laplaceWeight b s * R s := by simp_rw [hSliceRe]
      _ = _ := laplace_even_integral_eq_twice_positive b R hRneg hRint
  have hEnergyDifference : zeroLaplaceEnergy d t b u - periodicLaplaceEnergy d t b u =
      2 * ∫ s in Ioi (0 : ℝ), laplaceWeight b s * R s := by
    unfold zeroLaplaceEnergy periodicLaplaceEnergy
    rw [← integral_sub hE0 hEP]
    calc
      _ = ∫ s in Ioi (0 : ℝ), 2 * (laplaceWeight b s * R s) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun s => by
          dsimp only
          rw [zeroTranslationEnergy_expansion d t u hu s,
            periodicTranslationEnergy_expansion d t u hu s]
          simp only [R, Complex.sub_re]
          ring
      _ = _ := integral_const_mul 2 _
  exact ⟨hE0, hEP, hB, by linarith [hBreal, hEnergyDifference]⟩

/-- The noncentral lattice is evaluated only on the physical displacement
window. In particular the denominator is the periodic exp(b*d)-1. -/
private theorem laplace_imageKernel_eq_cosh
    (d b : ℝ) (hd : 0 < d) (hb : 0 < b) (x y : ℝ)
    (hlo : -d ≤ x - y) (hhi : x - y ≤ d) :
    weightedImageKernel d (laplaceWeight b) x y =
      2 * Real.cosh (b * (x - y)) / (Real.exp (b * d) - 1) := by
  classical
  let h : ℝ := x - y
  let r : ℝ := Real.exp (-b * d)
  let F : ℤ → ℝ := fun m => if m = 0 then 0 else laplaceWeight b (h + m • d)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hg : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr1
  have hpos (n : ℕ) : F ((n + 1 : ℕ) : ℤ) = Real.exp (-b * h) * r ^ (n + 1) := by
    have hn : ((n + 1 : ℕ) : ℤ) ≠ 0 := by omega
    have ha : 0 ≤ h + ((n + 1 : ℕ) : ℝ) * d := by
      have hnd : 0 ≤ (n : ℝ) * d := mul_nonneg (Nat.cast_nonneg _) hd.le
      dsimp only [h]
      push_cast
      nlinarith
    simp only [F, if_neg hn, laplaceWeight, zsmul_eq_mul, Int.cast_natCast,
      abs_of_nonneg ha, r, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hneg (n : ℕ) : F (-((n : ℤ) + 1)) = Real.exp (b * h) * r ^ (n + 1) := by
    have hn : -((n : ℤ) + 1) ≠ 0 := by omega
    have ha : h + (-((n : ℤ) + 1) : ℤ) • d ≤ 0 := by
      simp only [zsmul_eq_mul, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one]
      have hnd : 0 ≤ (n : ℝ) * d := mul_nonneg (Nat.cast_nonneg _) hd.le
      dsimp only [h]
      nlinarith
    simp only [F, if_neg hn, laplaceWeight]
    rw [abs_of_nonpos ha]
    simp only [zsmul_eq_mul, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      r, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hP : Summable (fun n : ℕ => F (n : ℤ)) := by
    apply Summable.comp_nat_add (k := 1)
    exact (((summable_nat_add_iff 1).mpr hg).mul_left (Real.exp (-b * h))).congr
      (fun n => (hpos n).symm)
  have hN : Summable (fun n : ℕ => F (-((n : ℤ) + 1))) :=
    (((summable_nat_add_iff 1).mpr hg).mul_left (Real.exp (b * h))).congr
      (fun n => (hneg n).symm)
  have htail : (∑' n : ℕ, r ^ (n + 1)) = r / (1 - r) := by
    simp_rw [pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1]
    ring
  have hPSum : (∑' n : ℕ, F (n : ℤ)) = Real.exp (-b * h) * (r / (1 - r)) := by
    rw [hP.tsum_eq_zero_add]
    have hzero : F 0 = 0 := by simp only [F, if_pos rfl]
    simp only [Nat.cast_zero, hzero, zero_add]
    have heq : (fun n : ℕ => F ((n + 1 : ℕ) : ℤ)) =
        fun n : ℕ => Real.exp (-b * h) * r ^ (n + 1) := funext hpos
    rw [heq, tsum_mul_left, htail]
  have hNSum : (∑' n : ℕ, F (-((n : ℤ) + 1))) = Real.exp (b * h) * (r / (1 - r)) := by
    simp_rw [hneg]
    rw [tsum_mul_left, htail]
  have hden : 0 < Real.exp (b * d) - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hb hd))
  have hrden : r / (1 - r) = 1 / (Real.exp (b * d) - 1) := by
    have he : Real.exp (b * d) ≠ 0 := (Real.exp_pos _).ne'
    have hr : r = (Real.exp (b * d))⁻¹ := by
      dsimp only [r]
      rw [show -b * d = -(b * d) by ring, Real.exp_neg]
    have hq : 1 - (Real.exp (b * d))⁻¹ ≠ 0 := by
      rw [← hr]
      exact (sub_pos.mpr hr1).ne'
    rw [hr]
    field_simp [he, hq, hden.ne']
    <;> ring
  change (∑' m : ℤ, F m) = _
  rw [tsum_of_nat_of_neg_add_one hP hN, hPSum, hNSum, hrden,
    Real.cosh_eq]
  dsimp only [h]
  rw [show -b * (x - y) = -(b * (x - y)) by ring]
  ring

private theorem window_displacement_bounds (d t : ℝ) (hd : 0 < d)
    {x y : ℝ} (hx : x ∈ Ioc t (t + d)) (hy : y ∈ Ioc t (t + d)) :
    -d ≤ x - y ∧ x - y ≤ d := by
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

private theorem continuous_window_multiplier_integrable
    (d t : ℝ) (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure d t))
    (g : ℝ → ℂ) (hg : Continuous g) :
    Integrable (fun x => g x * u x) (windowMeasure d t) := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Icc t (t + d))).bddAbove_image hg.norm.continuousOn
  apply (hu.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).bdd_mul
    hg.aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
  exact hC (mem_image_of_mem (fun x => ‖g x‖) ⟨hx.1.le, hx.2⟩)

private def laplaceExpMoment (d t b : ℝ) (u : ℝ → ℂ) : ℂ :=
  ∫ x, (Real.exp (b * x) : ℂ) * u x ∂windowMeasure d t

/-- Complex conjugation is preserved before taking the real part. This is
an exponential-moment version of the cosh/sinh normSq correction. -/
private theorem laplace_image_integral_eq_exp_moments
    (d t b : ℝ) [hd : Fact (0 < d)] (hb : 0 < b)
    (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure d t)) :
    (∫ p : ℝ × ℝ, conj (u p.1) *
      (weightedImageKernel d (laplaceWeight b) p.1 p.2 : ℂ) * u p.2
      ∂((windowMeasure d t).prod (windowMeasure d t))) =
      ((1 / (Real.exp (b * d) - 1) : ℝ) : ℂ) *
        (conj (laplaceExpMoment d t (-b) u) * laplaceExpMoment d t b u +
          conj (laplaceExpMoment d t b u) * laplaceExpMoment d t (-b) u) := by
  let f : ℝ → ℂ := fun x => (Real.exp (b * x) : ℂ) * u x
  let g : ℝ → ℂ := fun x => (Real.exp (-b * x) : ℂ) * u x
  have hf : Integrable f (windowMeasure d t) :=
    continuous_window_multiplier_integrable d t u hu _ (by fun_prop)
  have hg : Integrable g (windowMeasure d t) :=
    continuous_window_multiplier_integrable d t u hu _ (by fun_prop)
  have hfc : Integrable (fun x => conj (f x)) (windowMeasure d t) := by
    apply hf.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    exact Eventually.of_forall fun x => (Complex.norm_conj (f x)).le
  have hgc : Integrable (fun x => conj (g x)) (windowMeasure d t) := by
    apply hg.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable)
    exact Eventually.of_forall fun x => (Complex.norm_conj (g x)).le
  have hprod1 := hgc.mul_prod hf
  have hprod2 := hfc.mul_prod hg
  let c : ℂ := ((1 / (Real.exp (b * d) - 1) : ℝ) : ℂ)
  have hpoint : ∀ᵐ p ∂(windowMeasure d t).prod (windowMeasure d t),
      conj (u p.1) * (weightedImageKernel d (laplaceWeight b) p.1 p.2 : ℂ) * u p.2 =
        c * (conj (g p.1) * f p.2 + conj (f p.1) * g p.2) := by
    have hmem : ∀ᵐ p : ℝ × ℝ ∂(windowMeasure d t).prod (windowMeasure d t),
        p.1 ∈ Ioc t (t + d) ∧ p.2 ∈ Ioc t (t + d) :=
      (Measure.quasiMeasurePreserving_fst.ae (self_mem_ae_restrict measurableSet_Ioc)).and
        (Measure.quasiMeasurePreserving_snd.ae (self_mem_ae_restrict measurableSet_Ioc))
    filter_upwards [hmem] with p hp
    obtain ⟨hlo, hhi⟩ := window_displacement_bounds d t hd.out hp.1 hp.2
    rw [laplace_imageKernel_eq_cosh d b hd.out hb _ _ hlo hhi, Real.cosh_eq]
    have hminus : Real.exp (-(b * (p.1 - p.2))) =
        Real.exp (-b * p.1) * Real.exp (b * p.2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hplus : Real.exp (b * (p.1 - p.2)) =
        Real.exp (b * p.1) * Real.exp (-b * p.2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hminus, hplus]
    simp only [f, g, c, map_mul, Complex.conj_ofReal]
    push_cast
    ring
  calc
    _ = ∫ p : ℝ × ℝ, c * (conj (g p.1) * f p.2 + conj (f p.1) * g p.2)
        ∂((windowMeasure d t).prod (windowMeasure d t)) := integral_congr_ae hpoint
    _ = c * ((∫ x, conj (g x) ∂windowMeasure d t) * (∫ y, f y ∂windowMeasure d t) +
        (∫ x, conj (f x) ∂windowMeasure d t) * (∫ y, g y ∂windowMeasure d t)) := by
      rw [integral_const_mul, integral_add hprod1 hprod2,
        integral_prod_mul (fun x => conj (g x)) f,
        integral_prod_mul (fun x => conj (f x)) g]
    _ = _ := by
      rw [integral_conj, integral_conj]
      rfl

private theorem laplaceExpMoment_eq_zero_extension (d t b : ℝ) (u : ℝ → ℂ) :
    laplaceExpMoment d t b u =
      ∫ x : ℝ, (Real.exp (b * x) : ℂ) * zeroExtension d t u x := by
  have hfun : (fun x : ℝ => (Real.exp (b * x) : ℂ) * zeroExtension d t u x) =
      (Ioc t (t + d)).indicator (fun x => (Real.exp (b * x) : ℂ) * u x) := by
    funext x
    by_cases hx : x ∈ Ioc t (t + d) <;> simp only [zeroExtension,
      Set.indicator, hx, ↓reduceIte, mul_zero]
  rw [hfun, integral_indicator measurableSet_Ioc]
  rfl

/-- Reflection acts on the original zero extension on the whole line.
Consequently no equality of endpoint traces or representative choices enters. -/
private theorem laplaceExpMoment_neg_eq_of_ae_even
    (d t b : ℝ) (u : ℝ → ℂ)
    (heven : ∀ᵐ x : ℝ, zeroExtension d t u (-x) = zeroExtension d t u x) :
    laplaceExpMoment d t (-b) u = laplaceExpMoment d t b u := by
  rw [laplaceExpMoment_eq_zero_extension, laplaceExpMoment_eq_zero_extension]
  calc
    _ = ∫ x : ℝ, (Real.exp (-b * (-x)) : ℂ) * zeroExtension d t u (-x) :=
      (integral_neg_eq_self
        (fun x : ℝ => (Real.exp (-b * x) : ℂ) * zeroExtension d t u x) volume).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [heven] with x hx
      rw [hx, show -b * (-x) = b * x by ring]

private theorem laplace_image_integral_nonneg_of_ae_even
    (d t b : ℝ) [hd : Fact (0 < d)] (hb : 0 < b)
    (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure d t))
    (heven : ∀ᵐ x : ℝ, zeroExtension d t u (-x) = zeroExtension d t u x) :
    0 ≤ (∫ p : ℝ × ℝ, conj (u p.1) *
      (weightedImageKernel d (laplaceWeight b) p.1 p.2 : ℂ) * u p.2
      ∂((windowMeasure d t).prod (windowMeasure d t))).re := by
  rw [laplace_image_integral_eq_exp_moments d t b hb u hu]
  have hden : 0 < Real.exp (b * d) - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hb hd.out))
  simp only [laplaceExpMoment_neg_eq_of_ae_even d t b u heven,
    ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_add,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (one_div_nonneg.mpr hden.le)
    (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))

private theorem actual_single_rate_order_of_ae_even
    (d t b : ℝ) [Fact (0 < d)] (hb : 0 < b)
    (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure d t))
    (heven : ∀ᵐ x : ℝ, zeroExtension d t u (-x) = zeroExtension d t u x) :
    periodicLaplaceEnergy d t b u ≤ zeroLaplaceEnergy d t b u := by
  have h := (actual_single_rate_integrable_and_identity d t b hb u hu).2.2.2
  have hnonneg := laplace_image_integral_nonneg_of_ae_even d t b hb u hu heven
  linarith

private def actualLaplaceRate (r : ℕ) : ℝ := 2 * (r : ℝ) + 1 / 2

private theorem actualLaplaceRate_pos (r : ℕ) : 0 < actualLaplaceRate r := by
  unfold actualLaplaceRate
  positivity

/-- The summability here is pointwise in a strictly positive shift. It is
NOT a summability assertion about the rate-energy majorants 4*M/b_r. -/
private theorem actual_rate_weight_summable {s : ℝ} (hs : 0 < s) :
    Summable (fun r : ℕ => laplaceWeight (actualLaplaceRate r) s) := by
  have hr0 : 0 ≤ Real.exp (-2 * s) := (Real.exp_pos _).le
  have hr1 : Real.exp (-2 * s) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  apply ((summable_geometric_of_lt_one hr0 hr1).mul_left (Real.exp (-s / 2))).congr
  intro r
  simp only [laplaceWeight, actualLaplaceRate, abs_of_pos hs,
    ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

private theorem actual_density_ofReal_eq_rate_tsum {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal (ArchimedeanJumpDecomposition.archimedeanJumpDensity s) =
      ∑' r : ℕ, ENNReal.ofReal (laplaceWeight (actualLaplaceRate r) s) := by
  have hd := D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.jump_density_eq_tsum hs
  have hseries : ArchimedeanJumpDecomposition.archimedeanJumpDensity s = ∑' r : ℕ, laplaceWeight (actualLaplaceRate r) s := by
    simpa only [ArchimedeanJumpDecomposition.archimedeanJumpDensity, laplaceWeight, actualLaplaceRate, abs_of_pos hs] using hd
  rw [hseries]
  exact ENNReal.ofReal_tsum_of_nonneg (fun r => laplaceWeight_nonneg _ _)
    (actual_rate_weight_summable hs)

/-- Nonnegative Tonelli at the actual rates. The left side and the sum may
both be infinity. No signed subtraction and no sum of finite-rate bounds is
used. The abstract helper is consumed below with each original actual energy. -/
private theorem actual_gamma_lintegral_eq_rate_tsum
    (E : ℝ → ℝ) (C : ℝ) (hEm : AEStronglyMeasurable E volume)
    (hE : ∀ s, 0 ≤ E s ∧ E s ≤ C) :
    (∫⁻ s : ℝ in Ioi 0, ENNReal.ofReal (ArchimedeanJumpDecomposition.archimedeanJumpDensity s) * ENNReal.ofReal (E s)) =
      ∑' r : ℕ, ENNReal.ofReal
        (∫ s in Ioi (0 : ℝ), laplaceWeight (actualLaplaceRate r) s * E s) := by
  have hmeas (r : ℕ) : AEMeasurable
      (fun s => ENNReal.ofReal (laplaceWeight (actualLaplaceRate r) s) *
        ENNReal.ofReal (E s)) (volume.restrict (Ioi (0 : ℝ))) := by
    have hw := (laplaceWeight_integrable (actualLaplaceRate_pos r)).aestronglyMeasurable
    exact (hw.aemeasurable.ennreal_ofReal.mul hEm.aemeasurable.ennreal_ofReal).restrict
  calc
    _ = ∫⁻ s : ℝ in Ioi 0, ∑' r : ℕ,
        ENNReal.ofReal (laplaceWeight (actualLaplaceRate r) s) * ENNReal.ofReal (E s) := by
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
      rw [actual_density_ofReal_eq_rate_tsum hs, ENNReal.tsum_mul_right]
    _ = ∑' r : ℕ, ∫⁻ s : ℝ in Ioi 0,
        ENNReal.ofReal (laplaceWeight (actualLaplaceRate r) s) * ENNReal.ofReal (E s) :=
      lintegral_tsum hmeas
    _ = _ := by
      apply tsum_congr
      intro r
      have hi := laplace_energy_integrable_of_bound (actualLaplaceRate r)
        (actualLaplaceRate_pos r) E C hEm hE
      have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
          (fun s => laplaceWeight (actualLaplaceRate r) s * E s) :=
        Eventually.of_forall fun s => mul_nonneg (laplaceWeight_nonneg _ _) (hE s).1
      rw [ofReal_integral_eq_lintegral_ofReal hi hnn]
      exact lintegral_congr_ae (Eventually.of_forall fun s =>
        (ENNReal.ofReal_mul (laplaceWeight_nonneg _ _)).symm)

/-- Full extended actual-Gamma order on the original carriers.
Only original Ioc L2 and global AE evenness of its ORIGINAL zero extension
are assumed. Infinity is allowed on either side. No finite-Gamma premise. -/
theorem actual_gamma_order_of_zero_extension_ae_even
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t))
    (heven : ∀ᵐ x : ℝ, zeroExtension d t u (-x) = zeroExtension d t u x) :
    (∫⁻ s : ℝ in Ioi 0, ENNReal.ofReal (ArchimedeanJumpDecomposition.archimedeanJumpDensity s) *
      ENNReal.ofReal (periodicTranslationEnergy d t u s)) ≤
    ∫⁻ s : ℝ in Ioi 0, ENNReal.ofReal (ArchimedeanJumpDecomposition.archimedeanJumpDensity s) *
      ENNReal.ofReal (zeroTranslationEnergy d t u s) := by
  rw [actual_gamma_lintegral_eq_rate_tsum _ _
      (periodicTranslationEnergy_aestronglyMeasurable d t u hu)
      (periodicTranslationEnergy_nonneg_le d t u hu),
    actual_gamma_lintegral_eq_rate_tsum _ _
      (zeroTranslationEnergy_aestronglyMeasurable d t u hu)
      (zeroTranslationEnergy_nonneg_le d t u hu)]
  exact ENNReal.tsum_le_tsum fun r => ENNReal.ofReal_le_ofReal
    (actual_single_rate_order_of_ae_even d t (actualLaplaceRate r)
      (actualLaplaceRate_pos r) u hu heven)

end D5.S3.Weil.ZetaGamma.PeriodicEnergyComparison
