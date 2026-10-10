/- GID: D5/S3/Arith/Robin/ActualFactorialRobinHighWeight
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ActualFactorialRobinHighWeight
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The actual high weight pays ordinary odd Mobius convergence. -/
import D5.S3.Arith.Robin.ActualFactorialCumulativePositivity
import D5.S3.Arith.Robin.ActualOddHarmonicMobiusTail
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace D5.S3.Arith.Robin.ActualFactorialRobinHighWeight
open ActualFactorialRobinHighDerivative (highRemainder highRemainderDerivative)
open ActualFactorialCumulativePositivity (cumulative tailKernel)
open ActualOddHarmonicMobiusTail (weightedOddTail oddHarmonicPrefix)

/-- The actual dyadic difference of the complete factorial high remainder. -/
def q (r : ℝ) : ℝ := highRemainder r - highRemainder (r + Real.log 2) / 2

def qDerivative (r : ℝ) : ℝ :=
  highRemainderDerivative r - highRemainderDerivative (r + Real.log 2) / 2

private def K2 (t : ℝ) : ℝ := t⁻¹ ^ 2 + 2 * t⁻¹ ^ 3
private def K3 (t : ℝ) : ℝ := 2 * t⁻¹ ^ 3 + 6 * t⁻¹ ^ 4
private def Q2 (t : ℝ) : ℝ := K2 t - K2 (t + Real.log 2) / 2
private def Q3 (t : ℝ) : ℝ := K3 t - K3 (t + Real.log 2) / 2
private def g (r y : ℝ) : ℝ := cumulative y * (Q2 (r + Real.log y) / y)
private def gDerivative (r y : ℝ) : ℝ := -cumulative y * (Q3 (r + Real.log y) / y)

private lemma c_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)

private lemma K2_pos {t : ℝ} (ht : 0 < t) : 0 < K2 t := by unfold K2; positivity
private lemma K3_pos {t : ℝ} (ht : 0 < t) : 0 < K3 t := by unfold K3; positivity

private lemma K2_anti {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : K2 t ≤ K2 s := by
  have ht := hs.trans_le hst
  have hi := inv_anti₀ hs hst
  dsimp [K2]
  gcongr

private lemma K3_anti {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : K3 t ≤ K3 s := by
  have ht := hs.trans_le hst
  have hi := inv_anti₀ hs hst
  dsimp [K3]
  gcongr

private lemma Q2_pos {t : ℝ} (ht : 0 < t) : 0 < Q2 t := by
  have hm := K2_anti ht (show t ≤ t + Real.log 2 by linarith [c_pos])
  have hp := K2_pos ht
  dsimp [Q2]
  linarith

private lemma Q3_pos {t : ℝ} (ht : 0 < t) : 0 < Q3 t := by
  have hm := K3_anti ht (show t ≤ t + Real.log 2 by linarith [c_pos])
  have hp := K3_pos ht
  dsimp [Q3]
  linarith

private lemma Q3_le {t : ℝ} (ht : 0 < t) : Q3 t ≤ K3 t := by
  have hp := K3_pos (show 0 < t + Real.log 2 by linarith [c_pos])
  dsimp [Q3]
  linarith

private lemma K2_hasDerivAt {t : ℝ} (ht : 0 < t) : HasDerivAt K2 (-K3 t) t := by
  have hi := (hasDerivAt_id t).inv ht.ne'
  apply ((hi.pow 2).add ((hi.pow 3).const_mul 2)).congr_deriv
  dsimp [K2, K3]
  field_simp
  ring

private lemma Q2_hasDerivAt {t : ℝ} (ht : 0 < t) : HasDerivAt Q2 (-Q3 t) t := by
  have hshift := (K2_hasDerivAt (show 0 < t + Real.log 2 by linarith [c_pos])).comp t
    ((hasDerivAt_id t).add_const (Real.log 2))
  apply ((K2_hasDerivAt ht).sub (hshift.div_const 2)).congr_deriv
  dsimp [Q3]
  ring

private lemma g_integrable {r : ℝ} (hr : 0 < r) : IntegrableOn (g r) (Ioi (1 : ℝ)) := by
  have h0 := (ActualFactorialCumulativePositivity.result.2.2.2.2.2.2 r hr).1
  have h1 := (ActualFactorialCumulativePositivity.result.2.2.2.2.2.2
    (r + Real.log 2) (by linarith [c_pos])).1
  apply (h0.sub (h1.div_const 2)).congr
  filter_upwards with y
  dsimp [g, Q2, K2, tailKernel]
  rw [show r + Real.log y + Real.log 2 = r + Real.log 2 + Real.log y by ring]
  ring

private lemma q_representation {r : ℝ} (hr : 0 < r) :
    q r = ∫ y in Ioi (1 : ℝ), g r y := by
  have h0 := (ActualFactorialCumulativePositivity.result.2.2.2.2.2.2 r hr).1
  have h1 := (ActualFactorialCumulativePositivity.result.2.2.2.2.2.2
    (r + Real.log 2) (by linarith [c_pos])).1
  rw [q, ActualFactorialCumulativePositivity.positive_representation_y hr,
    ActualFactorialCumulativePositivity.positive_representation_y (by linarith [c_pos]),
    ← integral_div,
    ← integral_sub h0 (h1.div_const 2)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  dsimp [g, Q2, K2, tailKernel]
  rw [show r + Real.log y + Real.log 2 = r + Real.log 2 + Real.log y by ring]
  ring

private lemma g_pos {r y : ℝ} (hr : 0 < r) (hy : 1 < y) : 0 < g r y := by
  exact mul_pos (ActualFactorialCumulativePositivity.result.2.2.2.1 y hy)
    (div_pos (Q2_pos (by linarith [Real.log_pos hy])) (zero_lt_one.trans hy))

private lemma positive_integral {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi (1 : ℝ)))
    (hp : ∀ y ∈ Ioi (1 : ℝ), 0 < f y) : 0 < ∫ y in Ioi (1 : ℝ), f y := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun y hy => (hp y hy).le)) hf).mpr
  have hsub : Ioo (1 : ℝ) 2 ⊆ Function.support f ∩ Ioi 1 :=
    fun y hy => ⟨(hp y hy.1).ne', hy.1⟩
  exact (show 0 < volume (Ioo (1 : ℝ) 2) by norm_num [Real.volume_Ioo]).trans_le
    (measure_mono hsub)

private lemma q_pos {r : ℝ} (hr : 0 < r) : 0 < q r := by
  rw [q_representation hr]
  exact positive_integral (g_integrable hr) (fun y hy => g_pos hr hy)

private lemma signed_derivative {r : ℝ} (hr : 0 < r) : HasDerivAt q (qDerivative r) r := by
  have h0 := (ActualFactorialRobinHighDerivative.result.2.2 r hr).2.2.1
  have h1 := (ActualFactorialRobinHighDerivative.result.2.2 (r + Real.log 2)
    (by linarith [c_pos])).2.2.1
  apply (h0.sub ((h1.comp r ((hasDerivAt_id r).add_const (Real.log 2))).div_const 2)).congr_deriv
  dsimp [qDerivative]
  ring

private lemma g_hasDerivAt {r y : ℝ} (hr : 0 < r) (hy : 1 < y) :
    HasDerivAt (fun s => g s y) (gDerivative r y) r := by
  have hd := (Q2_hasDerivAt (show 0 < r + Real.log y by linarith [Real.log_pos hy])).comp r
    ((hasDerivAt_id r).add_const (Real.log y))
  apply ((hd.div_const y).const_mul (cumulative y)).congr_deriv
  dsimp [gDerivative]
  ring

private lemma derivative_measurable {r a : ℝ} (ha : 0 < a) :
    AEStronglyMeasurable (gDerivative r) (volume.restrict (Ioi (1 : ℝ))) := by
  have hbase := (ActualFactorialCumulativePositivity.result.2.2.2.2.2.2 a ha).1
  let ratio : ℝ → ℝ := fun y => -Q3 (r + Real.log y) / K2 (a + Real.log y)
  have hm : Measurable ratio := by dsimp [ratio, Q3, K2, K3]; fun_prop
  apply (hbase.aestronglyMeasurable.mul hm.aestronglyMeasurable).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hypos : 0 < y := zero_lt_one.trans (show 1 < y from hy)
  have hk := K2_pos (show 0 < a + Real.log y by linarith [Real.log_pos hy])
  change (cumulative y * (K2 (a + Real.log y) / y)) *
    (-Q3 (r + Real.log y) / K2 (a + Real.log y)) =
    -cumulative y * (Q3 (r + Real.log y) / y)
  field_simp [hypos.ne', hk.ne']

private lemma K3_bound {a s t : ℝ} (ha : 0 < a) (has : a ≤ s) (hst : s ≤ t) :
    K3 t ≤ (2 * a⁻¹ + 6 * a⁻¹ ^ 2) * K2 s := by
  have hs := ha.trans_le has
  have ht := hs.trans_le hst
  have hts := inv_anti₀ hs hst
  have hta := inv_anti₀ ha (has.trans hst)
  calc
    K3 t = t⁻¹ ^ 2 * (2 * t⁻¹ + 6 * t⁻¹ ^ 2) := by dsimp [K3]; ring
    _ ≤ s⁻¹ ^ 2 * (2 * a⁻¹ + 6 * a⁻¹ ^ 2) := by gcongr
    _ ≤ K2 s * (2 * a⁻¹ + 6 * a⁻¹ ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      dsimp [K2]
      have hp : 0 ≤ 2 * s⁻¹ ^ 3 := by positivity
      linarith
    _ = _ := mul_comm _ _

private lemma derivative_bound {a r y : ℝ} (ha : 0 < a) (har : a ≤ r) (hy : 1 < y) :
    ‖gDerivative r y‖ ≤ (2 * a⁻¹ + 6 * a⁻¹ ^ 2) * (cumulative y * tailKernel a y) := by
  have hC := ActualFactorialCumulativePositivity.result.2.2.2.1 y hy
  have hypos : 0 < y := zero_lt_one.trans (show 1 < y from hy)
  have hlog := (Real.log_pos hy).le
  have hden : 0 < r + Real.log y := by linarith
  have hb := (Q3_le hden).trans (K3_bound ha (by linarith : a ≤ a + Real.log y)
    (by linarith : a + Real.log y ≤ r + Real.log y))
  rw [gDerivative, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hC,
    abs_div, abs_of_pos hypos, abs_of_pos (Q3_pos hden)]
  calc
    _ ≤ cumulative y * ((2 * a⁻¹ + 6 * a⁻¹ ^ 2) * K2 (a + Real.log y) / y) := by gcongr
    _ = _ := by dsimp [tailKernel, K2]; ring

private lemma cumulative_derivative {r : ℝ} (hr : 0 < r) :
    IntegrableOn (gDerivative r) (Ioi (1 : ℝ)) ∧
    HasDerivAt q (∫ y in Ioi (1 : ℝ), gDerivative r y) r := by
  let a : ℝ := r / 2
  let U : Set ℝ := Ioo a (3 * r / 2)
  let B : ℝ → ℝ := fun y => (2 * a⁻¹ + 6 * a⁻¹ ^ 2) * (cumulative y * tailKernel a y)
  have ha : 0 < a := by dsimp [a]; linarith
  have hU : U ∈ 𝓝 r := Ioo_mem_nhds (by dsimp [a]; linarith) (by linarith)
  have hmeas : ∀ᶠ s in 𝓝 r, AEStronglyMeasurable (g s)
      (volume.restrict (Ioi (1 : ℝ))) := by
    filter_upwards [show Ioi (0 : ℝ) ∈ 𝓝 r from Ioi_mem_nhds hr] with s hs
    exact (g_integrable hs).aestronglyMeasurable
  have hbound : ∀ᵐ y ∂(volume.restrict (Ioi (1 : ℝ))), ∀ s ∈ U, ‖gDerivative s y‖ ≤ B y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    intro s hs
    exact derivative_bound ha hs.1.le hy
  have hdiff : ∀ᵐ y ∂(volume.restrict (Ioi (1 : ℝ))),
      ∀ s ∈ U, HasDerivAt (fun z => g z y) (gDerivative s y) s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    intro s hs
    exact g_hasDerivAt (ha.trans hs.1) hy
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (1 : ℝ))) (F := g) (F' := gDerivative) (bound := B)
    hU hmeas (g_integrable hr) (derivative_measurable ha) hbound
    (((ActualFactorialCumulativePositivity.result.2.2.2.2.2.2 a ha).1).const_mul _) hdiff
  refine ⟨h.1, h.2.congr_of_eventuallyEq ?_⟩
  filter_upwards [show Ioi (0 : ℝ) ∈ 𝓝 r from Ioi_mem_nhds hr] with s hs
  exact q_representation hs

private lemma q_derivative_neg {r : ℝ} (hr : 0 < r) : qDerivative r < 0 := by
  have hd := cumulative_derivative hr
  have he := (signed_derivative hr).unique hd.2
  rw [he]
  have hp : 0 < ∫ y in Ioi (1 : ℝ), -gDerivative r y := by
    apply positive_integral hd.1.neg
    intro y hy
    have hC := ActualFactorialCumulativePositivity.result.2.2.2.1 y hy
    have hk := Q3_pos (show 0 < r + Real.log y by linarith [Real.log_pos hy])
    have hypos : 0 < y := zero_lt_one.trans (show 1 < y from hy)
    change 0 < -(-cumulative y * (Q3 (r + Real.log y) / y))
    rw [neg_mul, neg_neg]
    exact mul_pos hC (div_pos hk hypos)
  rw [integral_neg] at hp
  linarith

private lemma q_strictAnti : StrictAntiOn q (Ioi (0 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro r hr
    exact (signed_derivative hr).continuousAt.continuousWithinAt
  · intro r hr
    rw [interior_Ioi] at hr
    rw [(signed_derivative hr).deriv]
    exact q_derivative_neg hr

private lemma high_pos {r : ℝ} (hr : 0 < r) : 0 < highRemainder r := by
  have h := (ActualFactorialCumulativePositivity.result.2.2.2.2.2.2 r hr).2.2.1
  have hk := ActualFactorialCumulativePositivity.result.2.2.2.2.2.1
  have hc : 0 < r + Real.log 2 := by linarith [c_pos]
  exact (show 0 < ActualFactorialCumulativePositivity.kappa *
    ((r + Real.log 2)⁻¹ + (r + Real.log 2)⁻¹ ^ 2) by positivity).trans h

private lemma q_upper {r : ℝ} (hr : 0 < r) : q r ≤ 2 * (r⁻¹ + r⁻¹ ^ 2) := by
  have h0 := (ActualFactorialCumulativePositivity.result.2.2.2.2.2.2 r hr).2.2.2
  have h1 := high_pos (show 0 < r + Real.log 2 by linarith [c_pos])
  dsimp [q]
  linarith

private lemma q_decay : Tendsto q atTop (𝓝 0) := by
  have hu : Tendsto (fun r : ℝ => 2 * (r⁻¹ + r⁻¹ ^ 2)) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.add (tendsto_inv_atTop_zero.pow 2)).const_mul (2 : ℝ)
  apply squeeze_zero' _ _ hu
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact (q_pos hr).le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact q_upper hr

private lemma finite_tail {D M : ℕ} (hD : 2 ≤ D) (hDM : D < M) :
    |weightedOddTail D M (fun m => q (Real.log m))| ≤ 4 * q (Real.log ((D+1 : ℕ) : ℝ)) := by
  apply (ActualOddHarmonicMobiusTail.result.2.2.2 D M hDM (fun m => q (Real.log m)) ?_ ?_).2.2
  · intro m hm
    have hm1 : 1 < m := by simp only [Finset.mem_Icc] at hm; omega
    exact (q_pos (Real.log_pos (by exact_mod_cast hm1))).le
  · intro m hm n hn hmn
    have hm' := Set.mem_Icc.mp hm
    have hn' := Set.mem_Icc.mp hn
    have hm1 : 1 < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
    have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    exact q_strictAnti.antitoneOn (Real.log_pos hm1) (Real.log_pos hn1)
      (Real.log_le_log (by linarith) (by exact_mod_cast hmn))

/-- Ordinary natural prefixes, retaining precisely the odd indices at least three. -/
def naturalPrefix (N : ℕ) : ℝ :=
  ∑ m ∈ (Finset.range N).filter (fun m => Odd m ∧ 3 ≤ m),
    (ArithmeticFunction.moebius m : ℝ) / (m : ℝ) * q (Real.log m)

private lemma prefix_tail {D M : ℕ} (hD : 2 ≤ D) (hDM : D ≤ M) :
    naturalPrefix (M+1) - naturalPrefix (D+1) = weightedOddTail D M (fun m => q (Real.log m)) := by
  classical
  simp only [naturalPrefix, Finset.sum_filter]
  rw [← Finset.sum_Ico_eq_sub _ (by omega : D+1 ≤ M+1)]
  rw [weightedOddTail, Finset.sum_filter,
    show Finset.Ioc D M = Finset.Ico (D+1) (M+1) by
      ext m; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega]
  apply Finset.sum_congr rfl
  intro m hm
  have h3 : 3 ≤ m := by simp only [Finset.mem_Ico] at hm; omega
  simp [h3]

private lemma sampled_decay :
    Tendsto (fun n : ℕ => 4 * q (Real.log ((n+1 : ℕ) : ℝ))) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n+1 : ℕ)) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hc : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ht
  simpa using (q_decay.comp (Real.tendsto_log_atTop.comp hc)).const_mul (4 : ℝ)

private lemma prefix_cauchy : CauchySeq naturalPrefix := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hev := sampled_decay.eventually (gt_mem_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨max (N+1) 3, ?_⟩
  intro m hm n hn
  have hm3 : 3 ≤ m := (le_max_right _ _).trans hm
  have hn3 : 3 ≤ n := (le_max_right _ _).trans hn
  have hmN : N+1 ≤ m := (le_max_left _ _).trans hm
  have hnN : N+1 ≤ n := (le_max_left _ _).trans hn
  by_cases hmn : m ≤ n
  · by_cases heq : m = n
    · subst n; simpa using hε
    have hb := finite_tail (by omega : 2 ≤ m-1) (by omega : m-1 < n-1)
    have hid := prefix_tail (by omega : 2 ≤ m-1) (by omega : m-1 ≤ n-1)
    simp only [Nat.sub_add_cancel (by omega : 1 ≤ m),
      Nat.sub_add_cancel (by omega : 1 ≤ n)] at hb hid
    rw [Real.dist_eq, abs_sub_comm, hid]
    apply hb.trans_lt
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ m)] using hN (m-1) (by omega)
  · have hb := finite_tail (by omega : 2 ≤ n-1) (by omega : n-1 < m-1)
    have hid := prefix_tail (by omega : 2 ≤ n-1) (by omega : n-1 ≤ m-1)
    simp only [Nat.sub_add_cancel (by omega : 1 ≤ m),
      Nat.sub_add_cancel (by omega : 1 ≤ n)] at hb hid
    rw [Real.dist_eq, hid]
    apply hb.trans_lt
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hN (n-1) (by omega)

/-- The actual high dyadic weight has a strictly negative signed derivative; its
positive decreasing decay pays the complete anchored tail and ordinary natural-prefix
convergence. No unconditional or absolute summability is asserted. -/
theorem result :
    (∀ r : ℝ, 0 < r → 0 < q r ∧ HasDerivAt q (qDerivative r) r ∧ qDerivative r < 0) ∧
    StrictAntiOn q (Ioi (0 : ℝ)) ∧ Tendsto q atTop (𝓝 0) ∧
    (∀ D M : ℕ, 2 ≤ D → D < M →
      |weightedOddTail D M (fun m => q (Real.log m))| ≤ 4 * q (Real.log ((D+1 : ℕ) : ℝ))) ∧
    CauchySeq (fun N : ℕ =>
      ∑ m ∈ (Finset.range N).filter (fun m => Odd m ∧ 3 ≤ m),
        (ArithmeticFunction.moebius m : ℝ) / (m : ℝ) * q (Real.log m)) ∧
    ∃ Q : ℝ, Tendsto (fun N : ℕ =>
      ∑ m ∈ (Finset.range N).filter (fun m => Odd m ∧ 3 ≤ m),
        (ArithmeticFunction.moebius m : ℝ) / (m : ℝ) * q (Real.log m)) atTop (𝓝 Q) := by
  exact ⟨fun r hr => ⟨q_pos hr, signed_derivative hr, q_derivative_neg hr⟩,
    q_strictAnti, q_decay, fun D M hD hDM => finite_tail hD hDM,
    prefix_cauchy, cauchySeq_tendsto_of_complete prefix_cauchy⟩

end D5.S3.Arith.Robin.ActualFactorialRobinHighWeight
#print axioms D5.S3.Arith.Robin.ActualFactorialRobinHighWeight.result
