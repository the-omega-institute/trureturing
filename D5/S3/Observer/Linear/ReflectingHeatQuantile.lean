/- GID: D5/S3/Observer/Linear/ReflectingHeatQuantile
   generality: I
   mirror-B: D5/B/S3/Observer/Linear/ReflectingHeatQuantile
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Observer.Linear.ReflectingHeatInterpolation]
   utility: none
   digest: Signed quadrature bounds for the equal-mass endpoints of the heat multiplier. -/

import D5.S3.Observer.Linear.ReflectingHeatInterpolation
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Signed right-endpoint quadrature for the reflecting heat multiplier. -/

open Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

namespace D5.S3.Observer.Linear.ReflectingHeatInterpolation

/-- The endpoints include the start of the density at index zero. The density
already includes the factor counting the cells. -/
structure EqualMassBins (β : ℝ) (density : ℝ → ℝ) where
  endpoint : ℕ → ℝ
  start : endpoint 0 = β
  increasing : StrictMono endpoint
  unbounded : Tendsto endpoint atTop atTop
  continuous_density : ContinuousOn density (Ici β)
  nonnegative : ∀ x ∈ Ici β, 0 ≤ density x
  mass : ∀ k, (∫ x in endpoint k..endpoint (k + 1), density x) = 1

namespace EqualMassBins

variable {β : ℝ} {density : ℝ → ℝ} (bins : EqualMassBins β density)

theorem start_le (k : ℕ) : β ≤ bins.endpoint k := by
  simpa only [bins.start] using bins.increasing.monotone (Nat.zero_le k)

private theorem on_interval {u v : ℝ} (hu : β ≤ u) :
    Icc u v ⊆ Ici β :=
  fun _ hx => hu.trans hx.1

private theorem integral_constant (k : ℕ) (c : ℝ) :
    (∫ x in bins.endpoint k..bins.endpoint (k + 1), c * density x) = c := by
  rw [intervalIntegral.integral_const_mul, bins.mass, mul_one]

private theorem compare_bin {f : ℝ → ℝ} (hf : ContinuousOn f (Ici β))
    (k : ℕ) {c : ℝ} (h : ∀ x ∈ Icc (bins.endpoint k) (bins.endpoint (k + 1)), c ≤ f x) :
    c ≤ ∫ x in bins.endpoint k..bins.endpoint (k + 1), f x * density x := by
  have hle := bins.increasing.monotone (Nat.le_succ k)
  have hsub := on_interval (v := bins.endpoint (k + 1)) (bins.start_le k)
  rw [← bins.integral_constant k c]
  exact intervalIntegral.integral_mono_on hle
    ((continuousOn_const.mul bins.continuous_density).mono hsub |>.intervalIntegrable_of_Icc hle)
    ((hf.mul bins.continuous_density).mono hsub |>.intervalIntegrable_of_Icc hle)
    (fun x hx => mul_le_mul_of_nonneg_right (h x hx) (bins.nonnegative x (hsub hx)))

private theorem compare_bin_upper {f : ℝ → ℝ} (hf : ContinuousOn f (Ici β))
    (k : ℕ) {c : ℝ} (h : ∀ x ∈ Icc (bins.endpoint k) (bins.endpoint (k + 1)), f x ≤ c) :
    (∫ x in bins.endpoint k..bins.endpoint (k + 1), f x * density x) ≤ c := by
  have hneg := bins.compare_bin hf.neg k (c := -c) fun x hx => neg_le_neg (h x hx)
  simp only [Pi.neg_apply, neg_mul, intervalIntegral.integral_neg] at hneg
  linarith

private theorem discrepancy_prefix {f : ℝ → ℝ} (hf : ContinuousOn f (Ici β)) (N : ℕ) :
    (∑ k ∈ Finset.range N, f (bins.endpoint (k + 1))) -
        (∫ x in β..bins.endpoint N, f x * density x) =
      ∑ k ∈ Finset.range N, (f (bins.endpoint (k + 1)) -
        ∫ x in bins.endpoint k..bins.endpoint (k + 1), f x * density x) := by
  have he := intervalIntegral.sum_integral_adjacent_intervals (a := bins.endpoint)
    (n := N) (f := fun x => f x * density x) (μ := volume) (by
      intro k _
      have hle := bins.increasing.monotone (Nat.le_succ k)
      exact ((hf.mul bins.continuous_density).mono (on_interval (bins.start_le k)))
        |>.intervalIntegrable_of_Icc hle)
  rw [Finset.sum_sub_distrib, he, bins.start]

/-- The finite signed discrepancy is bounded by the increase after the
minimum. The same formula covers prefixes ending before the minimum. -/
theorem prefix_discrepancy_le {f : ℝ → ℝ} {s : ℝ} (hs : β ≤ s)
    (hf : ContinuousOn f (Ici β)) (hleft : AntitoneOn f (Icc β s))
    (hright : MonotoneOn f (Ici s)) (N : ℕ) :
    (∑ k ∈ Finset.range N, f (bins.endpoint (k + 1))) -
        (∫ x in β..bins.endpoint N, f x * density x) ≤
      f (max s (bins.endpoint N)) - f s := by
  rw [bins.discrepancy_prefix hf]
  have hlocal (k : ℕ) :
      f (bins.endpoint (k + 1)) -
          (∫ x in bins.endpoint k..bins.endpoint (k + 1), f x * density x) ≤
        f (max s (bins.endpoint (k + 1))) - f (max s (bins.endpoint k)) := by
    by_cases hb : bins.endpoint (k + 1) ≤ s
    · have ha : bins.endpoint k ≤ s := (bins.increasing.monotone (Nat.le_succ k)).trans hb
      rw [max_eq_left hb, max_eq_left ha, sub_self, sub_nonpos]
      exact bins.compare_bin hf k fun x hx =>
        hleft ⟨(bins.start_le _).trans hx.1, hx.2.trans hb⟩ ⟨bins.start_le _, hb⟩ hx.2
    · rw [max_eq_right (le_of_lt (not_le.mp hb))]
      apply sub_le_sub_left
      apply bins.compare_bin hf k
      intro x hx
      by_cases hx' : s ≤ x
      · exact hright (mem_Ici.mpr (le_max_left _ _)) (mem_Ici.mpr hx') (max_le hx' hx.1)
      · have ha : bins.endpoint k ≤ s := hx.1.trans (le_of_lt (not_le.mp hx'))
        rw [max_eq_left ha]
        exact hleft ⟨(bins.start_le _).trans hx.1, (lt_of_not_ge hx').le⟩ ⟨hs, le_rfl⟩
          (lt_of_not_ge hx').le
  calc
    _ ≤ ∑ k ∈ Finset.range N,
        (f (max s (bins.endpoint (k + 1))) - f (max s (bins.endpoint k))) :=
      Finset.sum_le_sum fun k _ => hlocal k
    _ = _ := by
      simpa only [bins.start, max_eq_left hs] using
        Finset.sum_range_sub (fun k => f (max s (bins.endpoint k))) N

/-- For a decreasing kernel the finite signed discrepancy is between the
net decrease across the covered interval and zero. -/
theorem prefix_discrepancy_antitone {f : ℝ → ℝ} (hf : ContinuousOn f (Ici β))
    (hanti : AntitoneOn f (Ici β)) (N : ℕ) :
    f (bins.endpoint N) - f β ≤
        (∑ k ∈ Finset.range N, f (bins.endpoint (k + 1))) -
          (∫ x in β..bins.endpoint N, f x * density x) ∧
      (∑ k ∈ Finset.range N, f (bins.endpoint (k + 1))) -
          (∫ x in β..bins.endpoint N, f x * density x) ≤ 0 := by
  rw [bins.discrepancy_prefix hf]
  constructor
  · calc
      f (bins.endpoint N) - f β =
          ∑ k ∈ Finset.range N, (f (bins.endpoint (k + 1)) - f (bins.endpoint k)) := by
        simpa only [bins.start] using (Finset.sum_range_sub (fun k => f (bins.endpoint k)) N).symm
      _ ≤ _ := Finset.sum_le_sum fun k _ => sub_le_sub_left
        (bins.compare_bin_upper hf k fun x hx =>
          hanti (mem_Ici.mpr (bins.start_le _)) (mem_Ici.mpr ((bins.start_le k).trans hx.1)) hx.1) _
  · exact Finset.sum_nonpos fun k _ => sub_nonpos.mpr <|
      bins.compare_bin hf k fun x hx =>
        hanti (mem_Ici.mpr ((bins.start_le k).trans hx.1)) (mem_Ici.mpr (bins.start_le _)) hx.2

private theorem tendsto_discrepancy {f : ℝ → ℝ}
    (hsum : Summable fun k => f (bins.endpoint (k + 1)))
    (hint : IntegrableOn (fun x => f x * density x) (Ioi β)) :
    Tendsto (fun N => (∑ k ∈ Finset.range N, f (bins.endpoint (k + 1))) -
        (∫ x in β..bins.endpoint N, f x * density x)) atTop
      (𝓝 ((∑' k, f (bins.endpoint (k + 1))) - ∫ x in Ioi β, f x * density x)) :=
  hsum.hasSum.tendsto_sum_nat.sub
    (intervalIntegral_tendsto_integral_Ioi β hint bins.unbounded)

/-- The infinite signed discrepancy for a kernel decreasing to its minimum
and then increasing to zero. -/
theorem discrepancy_le {f : ℝ → ℝ} {s : ℝ} (hs : β ≤ s)
    (hf : ContinuousOn f (Ici β)) (hleft : AntitoneOn f (Icc β s))
    (hright : MonotoneOn f (Ici s)) (hzero : Tendsto f atTop (𝓝 0))
    (hsum : Summable fun k => f (bins.endpoint (k + 1)))
    (hint : IntegrableOn (fun x => f x * density x) (Ioi β)) :
    (∑' k, f (bins.endpoint (k + 1))) - (∫ x in Ioi β, f x * density x) ≤ -f s := by
  have ht : Tendsto (fun N => f (max s (bins.endpoint N))) atTop (𝓝 0) := by
    apply (hzero.comp bins.unbounded).congr'
    filter_upwards [bins.unbounded.eventually (eventually_ge_atTop s)] with N hN
    simp only [Function.comp_apply, max_eq_right hN]
  simpa only [zero_sub] using le_of_tendsto_of_tendsto'
    (bins.tendsto_discrepancy hsum hint) (ht.sub_const (f s))
    (bins.prefix_discrepancy_le hs hf hleft hright)

/-- The infinite signed discrepancy for a decreasing kernel which tends to
zero. The left-endpoint value bounds the loss. -/
theorem discrepancy_antitone {f : ℝ → ℝ} (hf : ContinuousOn f (Ici β))
    (hanti : AntitoneOn f (Ici β)) (hzero : Tendsto f atTop (𝓝 0))
    (hsum : Summable fun k => f (bins.endpoint (k + 1)))
    (hint : IntegrableOn (fun x => f x * density x) (Ioi β)) :
    -f β ≤ (∑' k, f (bins.endpoint (k + 1))) - (∫ x in Ioi β, f x * density x) ∧
      (∑' k, f (bins.endpoint (k + 1))) - (∫ x in Ioi β, f x * density x) ≤ 0 := by
  have hd := bins.tendsto_discrepancy hsum hint
  constructor
  · simpa only [zero_sub] using le_of_tendsto_of_tendsto'
      ((hzero.comp bins.unbounded).sub_const (f β)) hd
      (fun N => (bins.prefix_discrepancy_antitone hf hanti N).1)
  · exact le_of_tendsto' hd fun N => (bins.prefix_discrepancy_antitone hf hanti N).2

/-- Construct the right endpoints by inverting the cumulative density at the
natural numbers, starting with the zero-mass endpoint. -/
def ofDensity (hc : ContinuousOn density (Ici β)) (hn : ∀ x ∈ Ici β, 0 ≤ density x)
    (hp : ∀ x > β, 0 < density x)
    (hu : Tendsto (fun u => ∫ x in β..u, density x) atTop atTop) :
    EqualMassBins β density := by
  let mass (u : ℝ) := ∫ x in β..u, density x
  have hint {u v : ℝ} (hb : β ≤ u) (hle : u ≤ v) :
      IntervalIntegrable density volume u v :=
    (hc.mono (on_interval hb)).intervalIntegrable_of_Icc hle
  have hs : StrictMonoOn mass (Ici β) := by
    intro u hbu v hbv huv
    have hpos : 0 < ∫ x in u..v, density x :=
      intervalIntegral.integral_pos huv (hc.mono (on_interval hbu))
        (fun x hx => hn x (mem_Ici.mpr (hbu.trans hx.1.le)))
        ⟨v, right_mem_Icc.mpr huv.le, hp v (hbu.trans_lt huv)⟩
    have he := intervalIntegral.integral_add_adjacent_intervals (hint le_rfl hbu) (hint hbu huv.le)
    dsimp [mass]
    linarith
  have hex (k : ℕ) : ∃ u ∈ Ici β, mass u = k := by
    obtain ⟨v, hb, hv⟩ := ((eventually_ge_atTop β).and (hu.eventually_ge_atTop (k : ℝ))).exists
    have hc' : ContinuousOn mass (Icc β v) := by
      simpa only [uIcc_of_le hb] using
        intervalIntegral.continuousOn_primitive_interval' (hint le_rfl hb) (left_mem_uIcc (a := β) (b := v))
    have hk : (k : ℝ) ∈ Icc (mass β) (mass v) :=
      ⟨by simp [mass], hv⟩
    obtain ⟨u, hu, hu'⟩ := intermediate_value_Icc hb hc' hk
    exact ⟨u, mem_Ici.mpr hu.1, hu'⟩
  let t (k : ℕ) := (hex k).choose
  have ht (k : ℕ) : t k ∈ Ici β := (hex k).choose_spec.1
  have he (k : ℕ) : mass (t k) = k := (hex k).choose_spec.2
  have hmono : StrictMono t := by
    intro i j hij
    by_contra! hji
    have h := hs.monotoneOn (ht j) (ht i) hji
    rw [he, he] at h
    exact (not_le_of_gt hij) (by exact_mod_cast h)
  refine ⟨t, ?_, hmono, ?_, hc, hn, ?_⟩
  · apply hs.injOn (ht 0) (mem_Ici.mpr le_rfl)
    rw [he, Nat.cast_zero]
    simp [mass]
  · apply hmono.monotone.tendsto_atTop_atTop
    intro R
    obtain ⟨k, hk⟩ := exists_nat_gt (mass (max R β))
    refine ⟨k, (le_max_left R β).trans ?_⟩
    by_contra! h
    exact (not_le_of_gt hk) (he k ▸
      hs.monotoneOn (ht k) (mem_Ici.mpr (le_max_right R β)) h.le)
  · intro k
    have h := intervalIntegral.integral_add_adjacent_intervals
      (hint le_rfl (ht k)) (hint (ht k) (hmono.monotone (Nat.le_succ k)))
    change mass (t k) + _ = mass (t (k + 1)) at h
    rw [he, he, Nat.cast_add, Nat.cast_one] at h
    linarith

end EqualMassBins
end D5.S3.Observer.Linear.ReflectingHeatInterpolation
