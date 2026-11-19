/- GID: D5/S3/StatisticalMechanics/DelayedCooling/HistorySolution
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/DelayedCooling/HistorySolution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The concrete kernel representation of raw integrated cooling solutions. -/

module

public import D5.S3.StatisticalMechanics.DelayedCooling.Volterra
public import D5.S3.StatisticalMechanics.DelayedCooling.ShiftOrder
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Finite-Lebesgue history representation

The raw integrated equation is the input. Its bath and sample are functions
on real time, with their own finite equilibrium past. The response kernel is
the actual shifted quasi-exponential of the source Appendix. The integral
convention here is Lebesgue; inclusion of every proper-Riemann or other
source-admissible convention is a separate obligation.
-/

public section

namespace D5.S3.StatisticalMechanics.DelayedCooling.HistorySolution

open Set MeasureTheory Filter
open Kernel ShiftOrder Volterra
open scoped Topology

noncomputable section

/-- The finite-Lebesgue interpretation of the source Appendix (5). The integral
at zero is required to be defined. The theorem derives the remaining finite
integrability and the bath's own integrability from this weighted integral. -/
structure AppendixSolution (τ a q c : ℝ) (b T : ℝ → ℝ) : Prop where
  past : ∀ t ≤ a, T t = q
  preparation_integrable :
    IntervalIntegrable (fun s => (b s - c) * responseKernel τ (-s)) volume a 0
  equation : ∀ t, a ≤ t → T t = c + (q - c) * relaxation τ (t - a) +
    ∫ s in a..min 0 t, (b s - c) * responseKernel τ (t - s)

private theorem relaxation_lipschitz {τ : ℝ} (hτ : 0 < τ)
    (hsmall : τ ≤ Real.exp (-1)) : LipschitzWith 1 (relaxation τ) := by
  have hp : LipschitzOnWith 1 (relaxation τ) (Ioi 0) := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun x hx => (hasDerivAt_relaxation hτ hx).differentiableAt) _ (convex_Ioi 0)
    intro x hx
    rw [(hasDerivAt_relaxation hτ hx).deriv]
    apply NNReal.coe_le_coe.mp
    simp only [coe_nnnorm, norm_neg, Real.norm_eq_abs, NNReal.coe_one]
    rw [abs_of_pos (relaxation_pos hτ hsmall _)]
    have hm := antitone_relaxation hτ hsmall (show (0 : ℝ) ≤ max 0 (x - τ) from le_max_left _ _)
    by_cases he : x - τ ≤ 0
    · rw [relaxation_of_nonpos hτ he]
    · simpa [max_eq_right (le_of_not_ge he), relaxation_of_nonpos hτ le_rfl] using hm
  have hpc : LipschitzOnWith 1 (relaxation τ) (Ici 0) := by
    simpa only [closure_Ioi] using
      hp.closure (continuous_relaxation hτ).continuousOn
  have he (x : ℝ) : relaxation τ (max x 0) = relaxation τ x := by
    by_cases hx : x ≤ 0
    · rw [max_eq_right hx, relaxation_of_nonpos hτ le_rfl, relaxation_of_nonpos hτ hx]
    · rw [max_eq_left (le_of_not_ge hx)]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [← he x, ← he y]
  calc
    dist (relaxation τ (max x 0)) (relaxation τ (max y 0)) ≤
        1 * dist (max x 0) (max y 0) := hpc.dist_le_mul
          (max x 0) (le_max_right _ _) (max y 0) (le_max_right _ _)
    _ ≤ 1 * dist x y := by
      simpa using (LipschitzWith.id.max_const (0 : ℝ)).dist_le_mul x y

private theorem reflected_kernel_ac {τ : ℝ} (hτ : 0 < τ)
    (hsmall : τ ≤ Real.exp (-1)) (t a z : ℝ) :
    AbsolutelyContinuousOnInterval (fun s => responseKernel τ (t - s)) a z := by
  have hl : LipschitzWith 1 (fun s : ℝ => t - s - τ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul, Real.dist_eq]
    rw [show t - x - τ - (t - y - τ) = -(x - y) by ring, abs_neg]
  simpa only [one_mul, Function.comp_def, responseKernel] using
    ((relaxation_lipschitz hτ hsmall).comp hl).lipschitzOnWith.absolutelyContinuousOnInterval
      (a := a) (b := z)

private theorem reflected_kernel_deriv_early {τ t s : ℝ} (hτ : 0 < τ)
    (hs : s < t - τ) :
    HasDerivAt (fun u => responseKernel τ (t - u))
      (responseKernel τ (t - s - τ)) s := by
  have hd := (hasDerivAt_relaxation hτ (by linarith : 0 < t - s - τ)).comp s
    (((hasDerivAt_const s t).sub (hasDerivAt_id s)).sub_const τ)
  simpa [responseKernel, Function.comp_def] using! hd

private theorem reflected_kernel_deriv_late {τ t s : ℝ} (hτ : 0 < τ)
    (hs : t - τ < s) :
    HasDerivAt (fun u => responseKernel τ (t - u)) 0 s := by
  apply (hasDerivAt_const s (1 : ℝ)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs] with u hu
  simp only [mem_Ioi] at hu
  exact relaxation_of_nonpos hτ (by linarith : t - u - τ ≤ 0)

private theorem solution_deriv_ae {τ a q z : ℝ} {b T : ℝ → ℝ}
    (hT : IntegratedSolution τ a q b T) (haz : a ≤ z) :
    ∀ᵐ s : ℝ, s ∈ uIcc a z → deriv T s = b s - T (s - τ) := by
  filter_upwards [(hT.forcing_integrable z haz).ae_hasDerivAt_integral,
    (show ∀ᵐ s : ℝ ∂volume, s ≠ a from by simp [ae_iff])] with s hs hsa hsz
  have hsz' : s ∈ Icc a z := by simpa only [uIcc_of_le haz] using hsz
  have has : a < s := lt_of_le_of_ne hsz'.1 (Ne.symm hsa)
  have hd := (hs hsz a left_mem_uIcc).const_add q
  have he : HasDerivAt T (b s - T (s - τ)) s := hd.congr_of_eventuallyEq (by
    filter_upwards [Ioi_mem_nhds has] with u hu
    exact hT.equation u hu.le)
  exact he.deriv

private theorem kernel_interval_mass {τ x y : ℝ} (hτ : 0 < τ)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    (∫ s in x..y, responseKernel τ s) = relaxation τ x - relaxation τ y := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxy
    (continuous_relaxation hτ).continuousOn
    (fun s hs => hasDerivAt_relaxation hτ (by linarith [hs.1]))
    (((continuous_relaxation hτ).comp
      (continuous_id.sub continuous_const)).neg.intervalIntegrable x y)
  rw [intervalIntegral.integral_neg] at he
  change -(∫ s in x..y, responseKernel τ s) = _ at he
  linarith

/-- Every finite-Lebesgue integrated solution has the actual shifted-kernel
Duhamel representation, pointwise at every time after its own preparation
start, including every quench endpoint. -/
private theorem duhamel_representation {τ a q : ℝ} {b T : ℝ → ℝ}
    (hτ : 0 < τ) (hsmall : τ ≤ Real.exp (-1))
    (hT : IntegratedSolution τ a q b T) {t : ℝ} (ht : a ≤ t) :
    T t = q * relaxation τ (t - a) +
      ∫ s in a..t, b s * responseKernel τ (t - s) := by
  have bridge := integrated_solution_bridge hτ hT
  have hc := bridge.1
  have hdelay : Continuous (fun s => T (s - τ)) :=
    hc.comp (continuous_id.sub continuous_const)
  have hb := bridge.2.2.1
  have hk : Continuous (fun s => responseKernel τ (t - s)) :=
    (continuous_relaxation hτ).comp ((continuous_const.sub continuous_id).sub continuous_const)
  have hi (x y : ℝ) : IntervalIntegrable
      (fun s => T s * responseKernel τ (t - s - τ)) volume x y :=
    (hc.mul ((continuous_relaxation hτ).comp
      (((continuous_const.sub continuous_id).sub continuous_const).sub
        continuous_const))).intervalIntegrable x y
  by_cases hearly : t ≤ a + τ
  · have hdelay : (∫ s in a..t, b s - T (s - τ)) = ∫ s in a..t, b s - q := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le ht]
      intro s hs
      dsimp
      rw [hT.past (s - τ) (by linarith [hs.2])]
    have hkernel : (∫ s in a..t, b s * responseKernel τ (t - s)) = ∫ s in a..t, b s := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le ht]
      intro s hs
      dsimp [responseKernel]
      rw [relaxation_of_nonpos hτ (by linarith [hs.1])]
      exact mul_one _
    rw [hT.equation t ht, hdelay, intervalIntegral.integral_sub (hb t ht) intervalIntegrable_const,
      intervalIntegral.integral_const, hkernel,
      relaxation_initial_segment hτ (by linarith) (by linarith)]
    simp only [smul_eq_mul]
    ring
  · have har : a ≤ t - τ := by linarith
    have hrt : t - τ ≤ t := by linarith
    let g : ℝ → ℝ := fun s => responseKernel τ (t - s)
    have hg := reflected_kernel_ac hτ hsmall t a t
    have hTac := bridge.2.1 t ht
    have hI := hTac.integral_deriv_mul_eq_sub hg
    have hfirst : (∫ s in a..t, deriv T s * g s) =
        (∫ s in a..t, b s * g s) - ∫ s in a..t, T (s - τ) * g s := by
      have hib : IntervalIntegrable (fun s => b s * g s) volume a t :=
        (hb t ht).mul_continuousOn hk.continuousOn
      have hid : IntervalIntegrable (fun s => T (s - τ) * g s) volume a t :=
        (hdelay.mul hk).intervalIntegrable a t
      rw [← intervalIntegral.integral_sub hib hid]
      apply intervalIntegral.integral_congr_ae
      filter_upwards [solution_deriv_ae hT ht] with s hs hsz
      rw [hs (uIoc_subset_uIcc hsz)]
      ring
    have hsecond : (∫ s in a..t, T s * deriv g s) =
        ∫ s in a..(t - τ), T s * responseKernel τ (t - s - τ) := by
      have hdint := hg.intervalIntegrable_deriv.continuousOn_mul hc.continuousOn
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hdint.mono_set (by rw [uIcc_of_le har, uIcc_of_le ht]; exact Icc_subset_Icc le_rfl hrt))
        (hdint.mono_set (by rw [uIcc_of_le hrt, uIcc_of_le ht]; exact Icc_subset_Icc har le_rfl))]
      have hleft : (∫ s in a..(t - τ), T s * deriv g s) =
          ∫ s in a..(t - τ), T s * responseKernel τ (t - s - τ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le har
        intro s hs
        dsimp [g]
        rw [(reflected_kernel_deriv_early hτ hs.2).deriv]
      have hright : (∫ s in (t - τ)..t, T s * deriv g s) = 0 := by
        rw [← intervalIntegral.integral_zero (a := t - τ) (b := t)]
        apply intervalIntegral.integral_congr_Ioo_of_le hrt
        intro s hs
        dsimp [g]
        rw [(reflected_kernel_deriv_late hτ hs.1).deriv, mul_zero]
      rw [hleft, hright, add_zero]
    have hsum := intervalIntegral.integral_add
      (hTac.intervalIntegrable_deriv.mul_continuousOn hg.continuousOn)
      (hg.intervalIntegrable_deriv.continuousOn_mul hc.continuousOn)
    rw [hsum, hfirst, hsecond] at hI
    have hshift : (∫ s in a..t, T (s - τ) * g s) =
        ∫ u in (a - τ)..(t - τ), T u * responseKernel τ (t - u - τ) := by
      convert intervalIntegral.integral_comp_sub_right
        (fun u => T u * responseKernel τ (t - u - τ)) τ using 1
      congr 1
      funext s
      dsimp [g]
      congr 2
      ring
    have hpast : (∫ s in (a - τ)..a, T s * responseKernel τ (t - s - τ)) =
        q * (relaxation τ (t - a - τ) - relaxation τ (t - a)) := by
      calc
        _ = q * ∫ s in (a - τ)..a, responseKernel τ (t - s - τ) := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          rw [uIcc_of_le (by linarith : a - τ ≤ a)]
          intro s hs
          dsimp
          rw [hT.past s hs.2]
        _ = q * ∫ u in (t - a - τ)..(t - a), responseKernel τ u := by
          congr 1
          convert intervalIntegral.integral_comp_sub_left
            (a := a - τ) (b := a) (responseKernel τ) (t - τ) using 1
          · congr 1
            funext s
            congr 1
            ring
          · congr 1 <;> ring
        _ = _ := by rw [kernel_interval_mass hτ (by linarith) (by linarith)]
    have hcancel := intervalIntegral.integral_add_adjacent_intervals
      (hi (a - τ) a) (hi a (t - τ))
    rw [hshift] at hI
    rw [← hcancel, hpast] at hI
    have hgt : g t = 1 := by
      dsimp [g, responseKernel]
      apply relaxation_of_nonpos hτ
      linarith
    have hga : g a = relaxation τ (t - a - τ) := rfl
    change _ = T t * g t - T a * g a at hI
    rw [hT.past a le_rfl, hgt, hga] at hI
    dsimp [g] at hI
    nlinarith

private theorem appendix5_finite {τ a q c : ℝ} {b T : ℝ → ℝ}
    (hτ : 0 < τ) (hsmall : τ ≤ Real.exp (-1))
    (hT : IntegratedSolution τ a q b T) (ha : a ≤ 0)
    (hpost : ∀ s, 0 < s → b s = c) {t : ℝ} (ht : a ≤ t) :
    T t = c + (q - c) * relaxation τ (t - a) +
      ∫ s in a..min 0 t, (b s - c) * responseKernel τ (t - s) := by
  have hb := (integrated_solution_bridge hτ hT).2.2.1
  have hk : Continuous (fun s => responseKernel τ (t - s)) :=
    (continuous_relaxation hτ).comp ((continuous_const.sub continuous_id).sub continuous_const)
  have hdev : IntervalIntegrable (fun s => (b s - c) * responseKernel τ (t - s)) volume a t :=
    ((hb t ht).sub intervalIntegrable_const).mul_continuousOn hk.continuousOn
  have hmass : (∫ s in a..t, responseKernel τ (t - s)) = 1 - relaxation τ (t - a) := by
    rw [intervalIntegral.integral_comp_sub_left]
    simpa only [sub_self, relaxation_of_nonpos hτ le_rfl] using
      kernel_interval_mass hτ (x := 0) le_rfl (sub_nonneg.mpr ht)
  have hsplit : (∫ s in a..t, b s * responseKernel τ (t - s)) =
      (∫ s in a..t, (b s - c) * responseKernel τ (t - s)) +
        c * (1 - relaxation τ (t - a)) := by
    rw [← hmass, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hdev ((hk.intervalIntegrable a t).const_mul c)]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp
    ring
  have htrunc : (∫ s in a..t, (b s - c) * responseKernel τ (t - s)) =
      ∫ s in a..min 0 t, (b s - c) * responseKernel τ (t - s) := by
    by_cases ht0 : t ≤ 0
    · rw [min_eq_right ht0]
    · have h0t : 0 ≤ t := (lt_of_not_ge ht0).le
      rw [min_eq_left h0t, ← intervalIntegral.integral_add_adjacent_intervals
        (hdev.mono_set (by rw [uIcc_of_le ha, uIcc_of_le ht]; exact Icc_subset_Icc le_rfl h0t))
        (hdev.mono_set (by rw [uIcc_of_le h0t, uIcc_of_le ht]; exact Icc_subset_Icc ha le_rfl))]
      have hz : (∫ s in (0 : ℝ)..t, (b s - c) * responseKernel τ (t - s)) = 0 := by
        calc
          _ = ∫ _ in (0 : ℝ)..t, (0 : ℝ) := by
            apply intervalIntegral.integral_congr_Ioo_of_le h0t
            intro s hs
            dsimp
            rw [hpost s hs.1, sub_self, zero_mul]
          _ = 0 := intervalIntegral.integral_zero
      rw [hz, add_zero]
  rw [duhamel_representation hτ hsmall hT ht, hsplit, htrunc]
  ring

/-- Appendix (5) and the exact postzero history convolution for the original
raw bath representative. Each sample has its own real start `a` and equilibrium
`q`. The infinite weighted history is integrable as a consequence, including
the equilibrium tail; it is not an input field. -/
theorem raw_history_solution_bridge {τ a q c : ℝ} {b T : ℝ → ℝ}
    (hτ : 0 < τ) (hsmall : τ ≤ Real.exp (-1))
    (hT : IntegratedSolution τ a q b T) (ha : a ≤ 0)
    (hpast : ∀ s, s < a → b s = q) (hpost : ∀ s, 0 < s → b s = c) :
    (∀ t, a ≤ t → T t = c + (q - c) * relaxation τ (t - a) +
      ∫ s in a..min 0 t, (b s - c) * responseKernel τ (t - s)) ∧
    (∀ t, 0 ≤ t →
      IntegrableOn (fun u => responseKernel τ (t + u) * (b (-u) - c)) (Ioi 0) ∧
      T t = c + ∫ u in Ioi 0, responseKernel τ (t + u) * (b (-u) - c)) := by
  refine ⟨(fun t ht => appendix5_finite hτ hsmall hT ha hpost ht), ?_⟩
  intro t ht
  let f : ℝ → ℝ := fun u => responseKernel τ (t + u) * (b (-u) - c)
  have hk : Continuous (fun s => responseKernel τ (t - s)) :=
    (continuous_relaxation hτ).comp ((continuous_const.sub continuous_id).sub continuous_const)
  have hfin : IntervalIntegrable (fun s => (b s - c) * responseKernel τ (t - s)) volume a 0 :=
    (((integrated_solution_bridge hτ hT).2.2.1 0 ha).sub
      intervalIntegrable_const).mul_continuousOn hk.continuousOn
  have hreflect : (fun u => (b (-u) - c) * responseKernel τ (t - -u)) = f := by
    funext u
    dsimp [f]
    rw [sub_neg_eq_add, mul_comm]
  have hfi : IntervalIntegrable f volume 0 (-a) := by
    have hh := (IntervalIntegrable.iff_comp_neg (by finiteness)).mp hfin
    simpa only [neg_zero, hreflect] using hh.symm
  have hfeq : (∫ u in (0 : ℝ)..(-a), f u) =
      ∫ s in a..0, (b s - c) * responseKernel τ (t - s) := by
    rw [← hreflect]
    simpa only [neg_zero, neg_neg] using intervalIntegral.integral_comp_neg
      (a := (0 : ℝ)) (b := -a)
      (fun s => (b s - c) * responseKernel τ (t - s))
  have htail := kernel_tail_mass hτ hsmall (t := t) (L := -a) (by linarith)
  have htailEq : EqOn f (fun u => (q - c) * responseKernel τ (t + u)) (Ioi (-a)) := by
    intro u hu
    dsimp [f]
    rw [hpast (-u) (by have := hu; simp only [mem_Ioi] at this; linarith), mul_comm]
  have hti : IntegrableOn f (Ioi (-a)) :=
    IntegrableOn.congr_fun (htail.1.const_mul (q - c)) htailEq.symm measurableSet_Ioi
  have hteq : (∫ u in Ioi (-a), f u) = (q - c) * relaxation τ (t - a) := by
    rw [setIntegral_congr_fun measurableSet_Ioi htailEq, integral_const_mul, htail.2]
    simp only [sub_eq_add_neg]
  have h0a : (0 : ℝ) ≤ -a := by linarith
  have hunion : Ioc (0 : ℝ) (-a) ∪ Ioi (-a) = Ioi 0 := Ioc_union_Ioi_eq_Ioi h0a
  have hdisj : Disjoint (Ioc (0 : ℝ) (-a)) (Ioi (-a)) := by
    apply disjoint_left.mpr
    intro u hu hv
    exact (not_lt_of_ge hu.2) hv
  have hfinite : IntegrableOn f (Ioc 0 (-a)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h0a).mp hfi
  have hall : IntegrableOn f (Ioi 0) := by
    rw [← hunion]
    exact hfinite.union hti
  have hsum := setIntegral_union hdisj measurableSet_Ioi hfinite hti
  rw [hunion, ← intervalIntegral.integral_of_le h0a, hfeq, hteq] at hsum
  refine ⟨hall, ?_⟩
  have he := appendix5_finite hτ hsmall hT ha hpost (ha.trans ht)
  rw [min_eq_left ht] at he
  change T t = c + ∫ u in Ioi 0, f u
  rw [hsum]
  linarith

/-- For raw baths with their own finite equilibrium past and final constant
bath, the finite-Lebesgue Appendix formula is equivalent to the integrated
DDE. In the reverse direction, bath integrability is recovered from the
defined weighted integral, and existence is supplied by finite method of
steps. No convolution or optimizer is an input field. -/
theorem appendix5_iff_integrated {τ a q c : ℝ} {b T : ℝ → ℝ}
    (hτ : 0 < τ) (hsmall : τ ≤ Real.exp (-1)) (ha : a ≤ 0)
    (hpast : ∀ s, s < a → b s = q) (hpost : ∀ s, 0 < s → b s = c) :
    AppendixSolution τ a q c b T ↔ IntegratedSolution τ a q b T := by
  constructor
  · intro hA
    have hk : Continuous (fun s => responseKernel τ (-s)) :=
      (continuous_relaxation hτ).comp (continuous_neg.sub continuous_const)
    have hn (s : ℝ) : responseKernel τ (-s) ≠ 0 :=
      (relaxation_pos hτ hsmall (-s - τ)).ne'
    have hprep : IntervalIntegrable b volume a 0 := by
      have hi := hA.preparation_integrable.mul_continuousOn
        (hk.inv₀ (fun s => hn s)).continuousOn
      have hd : IntervalIntegrable (fun s => b s - c) volume a 0 := by
        apply hi.congr
        intro s _
        dsimp
        field_simp [hn s]
      simpa only [sub_add_cancel] using hd.add
        (intervalIntegrable_const (c := c))
    have hb : ∀ t, a ≤ t → IntervalIntegrable b volume a t := by
      intro t ht
      by_cases ht0 : t ≤ 0
      · exact hprep.mono_set (by
          rw [uIcc_of_le ht, uIcc_of_le ha]
          exact Icc_subset_Icc le_rfl ht0)
      · have h0t : 0 ≤ t := (lt_of_not_ge ht0).le
        have hi : IntervalIntegrable b volume 0 t := by
          apply (intervalIntegrable_const (c := c)).congr
          rw [uIoc_of_le h0t]
          intro s hs
          exact (hpost s hs.1).symm
        exact hprep.trans hi
    obtain ⟨S, hS, _⟩ := exists_unique_integrated_solution hτ b hb
    have hrep := (raw_history_solution_bridge hτ hsmall hS ha hpast hpost).1
    have heq : T = S := by
      funext t
      by_cases ht : t ≤ a
      · rw [hA.past t ht, hS.past t ht]
      · rw [hA.equation t (lt_of_not_ge ht).le, hrep t (lt_of_not_ge ht).le]
    exact heq ▸ hS
  · intro hT
    have hb := (integrated_solution_bridge hτ hT).2.2.1
    have hk : Continuous (fun s => responseKernel τ (-s)) :=
      (continuous_relaxation hτ).comp (continuous_neg.sub continuous_const)
    exact ⟨hT.past, ((hb 0 ha).sub intervalIntegrable_const).mul_continuousOn hk.continuousOn,
      (raw_history_solution_bridge hτ hsmall hT ha hpast hpost).1⟩

end

end D5.S3.StatisticalMechanics.DelayedCooling.HistorySolution
