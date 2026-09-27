/- GID: D5/S3/Fourier/Asymptotics/L2ContinuousPrimitive
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/L2ContinuousPrimitive
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An L2 primitive has a measurable continuous integral modification. -/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace

namespace D5.S3.Fourier.Asymptotics.L2ContinuousPrimitive

/-- On a finite measure space, continuity of the L2 derivative supplies compact
product integrability. Its representative integral is jointly measurable,
continuous on one common full-measure set, and a fixed-time modification. -/
theorem result {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f u : ℝ → Lp ℝ 2 P) (g : ℝ → Ω → ℝ)
    (hu : Continuous u)
    (hg : Measurable (Function.uncurry g))
    (heq : ∀ t, g t =ᵐ[P] (fun z => u t z))
    (hf : ∀ t, f t = f 0 + ∫ s in 0..t, u s) :
    let X := fun t z => f 0 z + ∫ s in 0..t, g s z
    Measurable (Function.uncurry X) ∧
      (∀ᵐ z ∂P, Continuous (fun t => X t z)) ∧
      ∀ t, X t =ᵐ[P] (fun z => f t z) := by
  classical
  intro X
  have hgm (t : ℝ) : MemLp (g t) 2 P := (Lp.memLp (u t)).ae_eq (heq t).symm
  have hint (a b : ℝ) : Integrable (Function.uncurry g)
      ((volume.restrict (uIoc a b)).prod P) := by
    apply (integrable_prod_iff hg.aestronglyMeasurable).mpr
    refine ⟨.of_forall (fun t => (hgm t).integrable (by norm_num)), ?_⟩
    have hB : Integrable (fun t => P.real univ + ‖u t‖ ^ 2)
        (volume.restrict (uIoc a b)) :=
      ((continuous_const.add (hu.norm.pow 2)).intervalIntegrable a b).def'
    apply hB.mono' (hg.stronglyMeasurable.norm.integral_prod_right.aestronglyMeasurable)
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    have hs : ∫ z, g t z ^ 2 ∂P = ‖u t‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [heq t] with z hz
      simp only [hz, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    calc
      (∫ z, ‖g t z‖ ∂P) ≤ ∫ z, (1 + g t z ^ 2) ∂P := by
        apply integral_mono ((hgm t).integrable (by norm_num)).norm
          ((integrable_const 1).add (hgm t).integrable_sq)
        intro z
        change ‖g t z‖ ≤ 1 + g t z ^ 2
        rw [Real.norm_eq_abs]
        have H := sq_nonneg (|g t z| - 1)
        have H' := sq_abs (g t z)
        nlinarith [abs_nonneg (g t z)]
      _ = P.real univ + ‖u t‖ ^ 2 := by
        rw [integral_add (integrable_const 1) (hgm t).integrable_sq, hs, integral_const]
        simp
  have heval (a b : ℝ) :
      (fun z => (∫ t in a..b, u t) z) =ᵐ[P] (fun z => ∫ t in a..b, g t z) := by
    have hgi : Integrable (fun z => ∫ t in a..b, g t z) P := by
      rw [show (fun z => ∫ t in a..b, g t z) =
        (fun z => (if a ≤ b then 1 else -1 : ℝ) * ∫ t in uIoc a b, g t z) by
          funext z; rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]; rfl]
      exact (hint a b).integral_prod_right.const_mul _
    apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
      ((Lp.memLp _).integrable (by norm_num)) hgi
    intro s hs hPs
    let I : Lp ℝ 2 P := indicatorConstLp 2 hs hPs.ne (1 : ℝ)
    calc
      (∫ z in s, (∫ t in a..b, u t) z ∂P) =
          (innerSL ℝ I) (∫ t in a..b, u t) :=
        (L2.inner_indicatorConstLp_one hs hPs.ne _).symm
      _ = ∫ t in a..b, (innerSL ℝ I) (u t) :=
        ((innerSL ℝ I).intervalIntegral_comp_comm (hu.intervalIntegrable a b)).symm
      _ = ∫ t in a..b, ∫ z in s, g t z ∂P := by
        apply intervalIntegral.integral_congr
        intro t _
        change ⟪I, u t⟫ = _
        rw [L2.inner_indicatorConstLp_one]
        exact integral_congr_ae (ae_restrict_of_ae (heq t).symm)
      _ = ∫ z in s, (∫ t in a..b, g t z) ∂P := by
        apply intervalIntegral_integral_swap
        exact (hint a b).mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hcommon : ∀ᵐ z ∂P, ∀ a b, IntervalIntegrable (fun t => g t z) volume a b := by
    have H : ∀ᵐ z ∂P, ∀ n : ℕ,
        Integrable (fun t => g t z) (volume.restrict (uIoc (-(n : ℝ)) n)) :=
      ae_all_iff.mpr (fun n => (hint (-(n : ℝ)) n).prod_left_ae)
    filter_upwards [H] with z hz a b
    obtain ⟨n, hn⟩ := exists_nat_gt (max |a| |b|)
    apply intervalIntegrable_iff.mpr
    apply (hz n).mono_measure
    apply Measure.restrict_mono
    · intro t ht
      change min a b < t ∧ t ≤ max a b at ht
      change min (-(n : ℝ)) n < t ∧ t ≤ max (-(n : ℝ)) n
      have ha : |a| < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
      have hb : |b| < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
      have hna : -(n : ℝ) < a := (abs_lt.mp ha).1
      have hnb : -(n : ℝ) < b := (abs_lt.mp hb).1
      have han : a < (n : ℝ) := (abs_lt.mp ha).2
      have hbn : b < (n : ℝ) := (abs_lt.mp hb).2
      constructor
      · exact (min_le_left _ _).trans_lt ((lt_min hna hnb).trans ht.1)
      · exact (ht.2.trans (max_le han.le hbn.le)).trans (le_max_right _ _)
    · exact le_rfl
  refine ⟨?_, hcommon.mono
    (fun z hz => continuous_const.add (intervalIntegral.continuous_primitive hz 0)), ?_⟩
  · have hleft : Measurable (fun p : (ℝ × Ω) × ℝ =>
        if 0 < p.2 ∧ p.2 ≤ p.1.1 then g p.2 p.1.2 else 0) := by
      apply Measurable.ite
      · exact (measurableSet_lt measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd (measurable_fst.fst))
      · exact hg.comp (measurable_snd.prodMk (measurable_fst.snd))
      · exact measurable_const
    have hright : Measurable (fun p : (ℝ × Ω) × ℝ =>
        if p.1.1 < p.2 ∧ p.2 ≤ 0 then g p.2 p.1.2 else 0) := by
      apply Measurable.ite
      · exact (measurableSet_lt (measurable_fst.fst) measurable_snd).inter
          (measurableSet_le measurable_snd measurable_const)
      · exact hg.comp (measurable_snd.prodMk (measurable_fst.snd))
      · exact measurable_const
    have hL := (hleft.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
    have hR := (hright.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
    have H := ((Lp.stronglyMeasurable (f 0)).measurable.comp measurable_snd).add (hL.sub hR)
    convert H using 1
    funext p
    dsimp only [Function.uncurry, X]
    rw [intervalIntegral]
    congr 2 <;> rw [← integral_indicator measurableSet_Ioc] <;>
      simp only [Set.indicator_apply, Set.mem_Ioc]
  · intro t
    filter_upwards [heval 0 t, Lp.coeFn_add (f 0) (∫ s in 0..t, u s)] with z hi ha
    dsimp only [X]
    rw [hf t, ha, Pi.add_apply, hi]


#print axioms result

end D5.S3.Fourier.Asymptotics.L2ContinuousPrimitive
