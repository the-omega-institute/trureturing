/- GID: D5/S3/Arith/Robin/ForwardKernel/MellinResidue
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MellinResidue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original forward Mellin response has a holomorphic extended remainder. -/

import D5.S3.Arith.Robin.ForwardKernel.FiniteMellin
import D5.S3.Arith.Robin.ForwardKernel.PrincipalTerm
import D5.S3.Arith.Robin.ForwardKernel.SignedRemainder
import D5.S3.Arith.Robin.ForwardKernel.InverseTransport
import D5.S3.Arith.Robin.ForwardKernel.Fubini

/-! Mellin continuation under an eventual power bound for the complete Chebyshev error. -/

namespace D5.S3.Arith.Robin.ForwardKernel.MellinResidue

open Set MeasureTheory Filter
open scoped Topology
open ForwardKernel.Adjoint ForwardKernel.Asymptotic ForwardKernel.FiniteMellin
open ForwardKernel.MellinConvergence (forwardMellin)
open ActualVonMangoldtBandCompensation (discrepancy)
open OriginalMovingWindowMoment (endpoint)

noncomputable section

private lemma signed_split {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    {q p r : ℝ → ℂ} (hq : IntegrableOn q (Ioi (1 : ℝ)))
    (hp : IntegrableOn p (Ioi (1 : ℝ)))
    (heq : ∀ t : ℝ, a ≤ t → q t - p t = r t) :
    ((∑ n ∈ Finset.Icc 0 ⌊b⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * q n) -
        ∫ t in (1 : ℝ)..b, q t) =
      ((∑ n ∈ Finset.Icc 0 ⌊b⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * p n) -
        ∫ t in (1 : ℝ)..b, p t) +
      ((∑ n ∈ Finset.Icc 0 ⌊a⌋₊,
          (ArithmeticFunction.vonMangoldt n : ℂ) * (q n - p n)) -
        ((∫ t in (1 : ℝ)..a, q t) - ∫ t in (1 : ℝ)..a, p t)) +
      ((∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
          (ArithmeticFunction.vonMangoldt n : ℂ) * r n) -
        ∫ t in a..b, r t) := by
  have hfloor : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hab
  have hset : Finset.Icc 0 ⌊b⌋₊ = Finset.Icc 0 ⌊a⌋₊ ∪ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 0 ⌊a⌋₊) (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    exact (Finset.mem_Ioc.mp hn').1.not_ge (Finset.mem_Icc.mp hn).2
  have hs : (∑ n ∈ Finset.Icc 0 ⌊b⌋₊,
      (ArithmeticFunction.vonMangoldt n : ℂ) * (q n - p n)) =
      (∑ n ∈ Finset.Icc 0 ⌊a⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * (q n - p n)) +
      ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * r n := by
    rw [hset, Finset.sum_union hdisj]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [heq n (Nat.lt_of_floor_lt (Finset.mem_Ioc.mp hn).1).le]
  have hqi {c d : ℝ} (hc : 1 ≤ c) (hcd : c ≤ d) :
      IntervalIntegrable q volume c d :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hcd).2
      (hq.mono_set fun t ht => hc.trans_lt ht.1)
  have hpi {c d : ℝ} (hc : 1 ≤ c) (hcd : c ≤ d) :
      IntervalIntegrable p volume c d :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hcd).2
      (hp.mono_set fun t ht => hc.trans_lt ht.1)
  have hi : ((∫ t in (1 : ℝ)..b, q t) - ∫ t in (1 : ℝ)..b, p t) =
      ((∫ t in (1 : ℝ)..a, q t) - ∫ t in (1 : ℝ)..a, p t) +
        ∫ t in a..b, r t := by
    rw [← intervalIntegral.integral_sub (hqi le_rfl (ha.trans hab))
      (hpi le_rfl (ha.trans hab)),
      ← intervalIntegral.integral_sub (hqi le_rfl ha) (hpi le_rfl ha),
      ← intervalIntegral.integral_add_adjacent_intervals
        ((hqi le_rfl ha).sub (hpi le_rfl ha)) ((hqi ha hab).sub (hpi ha hab))]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact heq t ht.1
  simp_rw [mul_sub, Finset.sum_sub_distrib] at hs ⊢
  linear_combination hs - hi

private lemma actual_adjoint_remainder {x0 t : ℝ} (hx0 : 4 ≤ x0) (ht : 8 < t)
    (hcut : endpoint x0 ≤ t) (s : ℂ) :
    adjointKernel x0 s t - (1 / 2 : ℂ) * (t : ℂ) ^ (-s - 1 / 2) =
      adjointRemainder t s := by
  rw [ForwardKernel.InverseTransport.adjointKernel_eq_inverseAdjoint hx0 ht.le hcut,
    (inverseAdjoint_C1_remainder_estimate ht s).1]
  ring

private theorem forward_kernel_mellin_residue_four
    {α : ℝ} (hα : 0 ≤ α)
    (hE : ∃ C t0 : ℝ, ∀ t : ℝ, t0 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ α)
    {x0 : ℝ} (hx0 : 4 ≤ x0) :
    ∃ R : ℂ → ℂ, DifferentiableOn ℂ R {s : ℂ | (α - 7 / 10) < s.re} ∧
      ∀ s : ℂ, max (1 / 2) (α - 3 / 10) < s.re →
        forwardMellin x0 s = -(1 / 2 : ℂ) *
          (deriv riemannZeta (s + 1 / 2) / riemannZeta (s + 1 / 2)) -
            1 / (2 * (s - 1 / 2)) + R s := by
  let a : ℝ := max 9 (endpoint x0)
  have ha : 8 < a := lt_of_lt_of_le (by norm_num : (8 : ℝ) < 9) (le_max_left _ _)
  have ha3 : 3 ≤ a := by linarith
  have hxa : x0 ≤ a :=
    (le_add_of_nonneg_right (Real.rpow_nonneg (by linarith : 0 ≤ x0) _)).trans
      (le_max_right _ _)
  let R : ℂ → ℂ := fun s => finiteCorrection x0 a s -
    (discrepancy a : ℂ) * adjointRemainder a s -
      ∫ t in Ioi a, (discrepancy t : ℂ) * deriv (fun y => adjointRemainder y s) t
  have hR : DifferentiableOn ℂ R {s : ℂ | (α - 7 / 10) < s.re} :=
    ((finiteCorrection_entire hx0 hxa).differentiableOn.sub
      ((ForwardKernel.Analytic.adjointRemainder_entire ha).const_mul
        (discrepancy a : ℂ)).differentiableOn).sub
      (ForwardKernel.Analytic.adjointRemainder_tail_holomorphic hα hE ha)
  refine ⟨R, hR, ?_⟩
  intro s hs
  have hsα : α - 3 / 10 < s.re := lt_of_le_of_lt (le_max_right _ _) hs
  have hshalf : 1 / 2 < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hq := ForwardKernel.Fubini.forwardMellin_adjoint_tendsto hα hE hx0 hs
  obtain ⟨C, hC, hbound⟩ := inverseAdjoint_uniform_C1_remainder {s} isCompact_singleton
  have hr : ∀ t : ℝ, a ≤ t →
      ‖adjointRemainder t s‖ ≤ C * t ^ (-s.re - 7 / 10) := by
    intro t ht
    have hb := (hbound s (mem_singleton s) t (ha.trans_le ht)).1
    convert hb using 1
    rw [mul_assoc, ← Real.rpow_add (by linarith : 0 < t)]
    congr 2
    ring
  have hdr : ∀ t : ℝ, a ≤ t →
      ‖deriv (fun y => adjointRemainder y s) t‖ ≤ C * t ^ (-s.re - 17 / 10) := by
    intro t ht
    have hb := (hbound s (mem_singleton s) t (ha.trans_le ht)).2
    convert hb using 1
    rw [mul_assoc, ← Real.rpow_add (by linarith : 0 < t)]
    congr 2
    ring
  have htail := ForwardKernel.SignedRemainder.signed_remainder_tendsto hα hE ha3
    (show (α - 7 / 10) < s.re by linarith) hC.le
    (fun t ht => (inverseAdjoint_C1_remainder_estimate (ha.trans_le ht) s).2.1.hasDerivAt)
    (aestronglyMeasurable_deriv (fun t => adjointRemainder t s) _) hr hdr
  have hp : IntegrableOn (fun t : ℝ => (1 / 2 : ℂ) * (t : ℂ) ^ (-s - 1 / 2))
      (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_cpow_of_lt (by norm_num; linarith) zero_lt_one).const_mul _
  have hlim := ((ForwardKernel.PrincipalTerm.principal_signed_tendsto hshalf).add_const
    (finiteCorrection x0 a s)).add htail
  have hcombined : Tendsto (fun b : ℝ =>
      (∑ n ∈ Finset.Icc 0 ⌊b⌋₊,
        (ArithmeticFunction.vonMangoldt n : ℂ) * adjointKernel x0 s n) -
        ∫ t in (1 : ℝ)..b, adjointKernel x0 s t) atTop
      (𝓝 (-(1 / 2 : ℂ) *
        (deriv riemannZeta (s + 1 / 2) / riemannZeta (s + 1 / 2)) -
          1 / (2 * (s - 1 / 2)) + finiteCorrection x0 a s +
            (-(discrepancy a : ℂ) * adjointRemainder a s -
              ∫ t in Ioi a, (discrepancy t : ℂ) * deriv (fun y => adjointRemainder y s) t))) := by
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop a] with b hb
    have he := signed_split (by linarith : (1 : ℝ) ≤ a) hb hq.1 hp
      (fun t ht => actual_adjoint_remainder hx0 (ha.trans_le ht)
        ((le_max_right _ _).trans ht) s)
    have hfinite :
        ((∑ n ∈ Finset.Icc 0 ⌊a⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) *
          (adjointKernel x0 s n - (1 / 2 : ℂ) * (n : ℂ) ^ (-s - 1 / 2))) -
          ((∫ t in (1 : ℝ)..a, adjointKernel x0 s t) -
            ∫ t in (1 : ℝ)..a, (1 / 2 : ℂ) * (t : ℂ) ^ (-s - 1 / 2))) =
        finiteCorrection x0 a s := by
      unfold finiteCorrection
      rw [intervalIntegral.integral_of_le (by linarith : (1 : ℝ) ≤ a),
        intervalIntegral.integral_of_le (by linarith : (1 : ℝ) ≤ a),
        integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
    simp only [Complex.ofReal_natCast] at he
    rw [hfinite] at he
    exact he.symm
  have h := tendsto_nhds_unique hq.2 hcombined
  change forwardMellin x0 s = _ +
    (finiteCorrection x0 a s - (discrepancy a : ℂ) * adjointRemainder a s - _)
  linear_combination h

/-- The actual complete forward response has the logarithmic-derivative principal
term and a holomorphic remainder on Re(s)>alpha-7/10 under an eventual
power bound for the complete Chebyshev error. -/
theorem forward_kernel_mellin_residue
    {α : ℝ} (hα : 0 ≤ α)
    (hE : ∃ C t0 : ℝ, ∀ t : ℝ, t0 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ α)
    {x0 : ℝ} (hx0 : 3 ≤ x0) :
    ∃ R : ℂ → ℂ, DifferentiableOn ℂ R {s : ℂ | (α - 7 / 10) < s.re} ∧
      ∀ s : ℂ, max (1 / 2) (α - 3 / 10) < s.re →
        forwardMellin x0 s = -(1 / 2 : ℂ) *
          (deriv riemannZeta (s + 1 / 2) / riemannZeta (s + 1 / 2)) -
            1 / (2 * (s - 1 / 2)) + R s := by
  let y : ℝ := max 4 x0
  have hy : 4 ≤ y := le_max_left _ _
  have hxy : x0 ≤ y := le_max_right _ _
  obtain ⟨C, hCp, hC⟩ := ForwardKernel.MellinConvergence.error_power_bound hα hE
  have hi : IntegrableOn
      (fun x : ℝ => (ForwardKernel.Transport.forwardResponse x : ℂ)) (Icc x0 y) := by
    have hm : IntegrableOn (fun x : ℝ => (2 * C * (2 : ℝ) ^ α) *
        x ^ (α - 3 / 10)) (Icc x0 y) := by
      apply ContinuousOn.integrableOn_Icc
      apply ContinuousOn.const_mul
      apply continuousOn_id.rpow_const
      intro t ht
      exact Or.inl (by linarith [ht.1] : t ≠ 0)
    apply hm.mono' (Complex.measurable_ofReal.comp
      ForwardKernel.MellinConvergence.response_measurable).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    change ‖(ForwardKernel.Transport.forwardResponse x : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact ForwardKernel.MellinConvergence.forwardResponse_power_bound hCp hα hC (hx0.trans hx.1)
  let G : ℂ → ℂ := fun s => ∫ x in Icc x0 y,
    (ForwardKernel.Transport.forwardResponse x : ℂ) * (x : ℂ) ^ (-s - 1)
  have hG : Differentiable ℂ G := compact_mellin_entire (by linarith) hi
  obtain ⟨R, hR, hidentity⟩ := forward_kernel_mellin_residue_four hα hE hy
  refine ⟨fun s => G s + R s, hG.differentiableOn.add hR, ?_⟩
  intro s hs
  have hsα : α - 3 / 10 < s.re := lt_of_le_of_lt (le_max_right _ _) hs
  have hi0 := ForwardKernel.MellinConvergence.forwardMellin_integrable hα hE hx0
    (s := s) (by linarith)
  have hiy := ForwardKernel.MellinConvergence.forwardMellin_integrable hα hE
    (show 3 ≤ y by linarith) (s := s) (by linarith)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi0 hiy
  have hfinite : (∫ x in x0..y,
      (ForwardKernel.Transport.forwardResponse x : ℂ) * (x : ℂ) ^ (-s - 1)) = G s := by
    rw [intervalIntegral.integral_of_le hxy]
    exact integral_Icc_eq_integral_Ioc.symm
  rw [hfinite] at hsplit
  change G s + forwardMellin y s = forwardMellin x0 s at hsplit
  rw [hidentity s hs] at hsplit
  linear_combination -hsplit

#print axioms forward_kernel_mellin_residue

end
end D5.S3.Arith.Robin.ForwardKernel.MellinResidue
