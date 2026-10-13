/- GID: D5/S3/Analytic/Monotonicity/FiniteExceptionalValuesMonotonicity
   generality: G
   mirror-B: D5/B/S3/Analytic/Monotonicity/FiniteExceptionalValuesMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuity and nonnegative derivatives outside finitely many values imply interval monotonicity. -/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Set.Finite.Basic

open Set

namespace D5.S3.Analytic.Monotonicity.FiniteExceptionalValuesMonotonicity

/-- A finite set of real values leaves a nonempty open gap inside any open interval.
Only the open gap is needed: its endpoints will be endpoints of a mean-value interval. -/
private theorem exists_value_gap {S : Set ℝ} (hS : S.Finite) :
    ∀ {l r : ℝ}, l < r →
      ∃ u v : ℝ, l < u ∧ u < v ∧ v < r ∧ ∀ z ∈ Ioo u v, z ∉ S := by
  classical
  refine Set.Finite.induction_on
    (motive := fun S _ => ∀ {l r : ℝ}, l < r →
      ∃ u v : ℝ, l < u ∧ u < v ∧ v < r ∧ ∀ z ∈ Ioo u v, z ∉ S)
    S hS ?_ ?_
  · intro l r hlr
    obtain ⟨u, hlu, hur⟩ := exists_between hlr
    obtain ⟨v, huv, hvr⟩ := exists_between hur
    exact ⟨u, v, hlu, huv, hvr, by simp⟩
  · intro s S _hnot _hfinite ih l r hlr
    obtain ⟨u, v, hlu, huv, hvr, hgap⟩ := ih hlr
    obtain ⟨m, hum, hmv⟩ := exists_between huv
    by_cases hsm : s ≤ m
    · refine ⟨m, v, hlu.trans hum, hmv, hvr, ?_⟩
      intro z hz hzS
      rcases Set.mem_insert_iff.mp hzS with hzs | hzS
      · have : s < z := hsm.trans_lt hz.1
        exact (ne_of_gt this) hzs
      · exact hgap z ⟨hum.trans hz.1, hz.2⟩ hzS
    · have hms : m < s := lt_of_not_ge hsm
      refine ⟨u, m, hlu, hum, hmv.trans hvr, ?_⟩
      intro z hz hzS
      rcases Set.mem_insert_iff.mp hzS with hzs | hzS
      · have : z < s := hz.2.trans hms
        exact (ne_of_lt this) hzs
      · exact hgap z ⟨hz.1, hz.2.trans hmv⟩ hzS

/-- A downward traversal of two levels contains a closed subinterval whose endpoints
have precisely these levels and whose interior values lie strictly between them.

The right endpoint is the first crossing of the lower level. The left endpoint is
the last crossing of the upper level before that first crossing. Compact closed
level sets provide both extrema. -/
private theorem exists_downcrossing_interval {f : ℝ → ℝ} {a b u v : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hbu : f b < u) (huv : u < v) (hva : v < f a) :
    ∃ d c : ℝ, a ≤ d ∧ d < c ∧ c ≤ b ∧ f d = v ∧ f c = u ∧
      ∀ t ∈ Ioo d c, f t ∈ Ioo u v := by
  let U : Set ℝ := {t ∈ Icc a b | f t = u}
  have hUclosed : IsClosed U :=
    isClosed_Icc.isClosed_eq hf continuousOn_const
  have hUcompact : IsCompact U :=
    isCompact_Icc.of_isClosed_subset hUclosed (fun _ ht => ht.1)
  have hUne : U.Nonempty := by
    obtain ⟨t, ht, hft⟩ :=
      intermediate_value_Icc' hab hf ⟨hbu.le, (huv.trans hva).le⟩
    exact ⟨t, ht, hft⟩
  obtain ⟨c, hc, hcmin⟩ :=
    hUcompact.exists_isMinOn hUne (continuous_id.continuousOn)
  have hca : a ≤ c := hc.1.1
  have hcb : c ≤ b := hc.1.2
  have hfc : f c = u := hc.2
  have hcontac : ContinuousOn f (Icc a c) :=
    hf.mono (fun _ ht => ⟨ht.1, ht.2.trans hcb⟩)
  let V : Set ℝ := {t ∈ Icc a c | f t = v}
  have hVclosed : IsClosed V :=
    isClosed_Icc.isClosed_eq hcontac continuousOn_const
  have hVcompact : IsCompact V :=
    isCompact_Icc.of_isClosed_subset hVclosed (fun _ ht => ht.1)
  have hVne : V.Nonempty := by
    obtain ⟨t, ht, hft⟩ :=
      intermediate_value_Icc' hca hcontac ⟨by rw [hfc]; exact huv.le, hva.le⟩
    exact ⟨t, ht, hft⟩
  obtain ⟨d, hd, hdmax⟩ :=
    hVcompact.exists_isMaxOn hVne (continuous_id.continuousOn)
  have had : a ≤ d := hd.1.1
  have hdc : d ≤ c := hd.1.2
  have hfd : f d = v := hd.2
  have hdclt : d < c := lt_of_le_of_ne hdc (by
    intro heq
    have : v = u := hfd.symm.trans ((congrArg f heq).trans hfc)
    exact (ne_of_lt huv) this.symm)
  refine ⟨d, c, had, hdclt, hcb, hfd, hfc, ?_⟩
  intro t ht
  have hat : a ≤ t := had.trans ht.1.le
  have htb : t ≤ b := ht.2.le.trans hcb
  constructor
  · by_contra hnot
    have htu : f t ≤ u := le_of_not_gt hnot
    have hcontat : ContinuousOn f (Icc a t) :=
      hf.mono (fun _ hz => ⟨hz.1, hz.2.trans htb⟩)
    obtain ⟨z, hz, hfz⟩ :=
      intermediate_value_Icc' hat hcontat ⟨htu, (huv.trans hva).le⟩
    have hzU : z ∈ U := ⟨⟨hz.1, hz.2.trans htb⟩, hfz⟩
    have hcz : c ≤ z := hcmin hzU
    exact (not_le_of_gt ht.2) (hcz.trans hz.2)
  · by_contra hnot
    have hvt : v ≤ f t := le_of_not_gt hnot
    have hconttc : ContinuousOn f (Icc t c) :=
      hf.mono (fun _ hz => ⟨hat.trans hz.1, hz.2.trans hcb⟩)
    obtain ⟨z, hz, hfz⟩ :=
      intermediate_value_Icc' ht.2.le hconttc ⟨by rw [hfc]; exact huv.le, hvt⟩
    have hzV : z ∈ V := ⟨⟨hat.trans hz.1, hz.2⟩, hfz⟩
    have hzd : z ≤ d := hdmax hzV
    exact (not_le_of_gt ht.1) (hz.1.trans hzd)

/-- A continuous real function on a closed interval is monotone if it is differentiable
with nonnegative derivative at every interior point whose value avoids a finite set.
No derivative is assumed at any point whose value belongs to that set, and the set of
such points can be infinite. No ordering or positivity assumption on the endpoints is needed. -/
private theorem monotoneOn_Icc_of_deriv_nonneg_off_finite_values
    {f : ℝ → ℝ} {a b : ℝ} {S : Set ℝ} (hS : S.Finite)
    (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, f t ∉ S →
      DifferentiableAt ℝ f t ∧ 0 ≤ deriv f t) :
    MonotoneOn f (Icc a b) := by
  intro x hx y hy hxy
  by_contra hnot
  have hfyx : f y < f x := lt_of_not_ge hnot
  obtain ⟨u, v, hyu, huv, hvx, hgap⟩ := exists_value_gap hS hfyx
  have hcontxy : ContinuousOn f (Icc x y) :=
    hf.mono (fun _ ht => ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩)
  obtain ⟨d, c, hxd, hdc, hcy, hfd, hfc, hbetween⟩ :=
    exists_downcrossing_interval hxy hcontxy hyu huv hvx
  have hsub : Icc d c ⊆ Icc a b := by
    intro t ht
    exact ⟨hx.1.trans (hxd.trans ht.1), (ht.2.trans hcy).trans hy.2⟩
  have hgood : ∀ t ∈ Ioo d c,
      DifferentiableAt ℝ f t ∧ 0 ≤ deriv f t := by
    intro t ht
    have ht' : t ∈ Ioo a b :=
      ⟨(hx.1.trans hxd).trans_lt ht.1, ht.2.trans_le (hcy.trans hy.2)⟩
    exact hderiv t ht' (hgap (f t) (hbetween t ht))
  have hmono : MonotoneOn f (Icc d c) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc d c) (hf.mono hsub)
    · intro t ht
      have ht' : t ∈ Ioo d c := by simpa only [interior_Icc] using ht
      exact (hgood t ht').1.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Ioo d c := by simpa only [interior_Icc] using ht
      exact (hgood t ht').2
  have hle : f d ≤ f c :=
    hmono (left_mem_Icc.mpr hdc.le) (right_mem_Icc.mpr hdc.le) hdc.le
  rw [hfd, hfc] at hle
  exact (not_le_of_gt huv) hle

/-- A continuous real function on a closed interval is monotone if every interior
point whose value avoids a finite set admits a nonnegative derivative. The interval
endpoints are arbitrary, and the exceptional values may have an infinite preimage. -/
theorem monotoneOn_Icc_of_hasDerivAt_nonneg_off_finite_values
    {f : ℝ → ℝ} {a b : ℝ} {S : Set ℝ} (hS : S.Finite)
    (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, f t ∉ S →
      ∃ r : ℝ, HasDerivAt f r t ∧ 0 ≤ r) :
    MonotoneOn f (Icc a b) := by
  apply monotoneOn_Icc_of_deriv_nonneg_off_finite_values hS hf
  intro t ht hnot
  obtain ⟨r, hr, hrnonneg⟩ := hderiv t ht hnot
  exact ⟨hr.differentiableAt, by rw [hr.deriv]; exact hrnonneg⟩

end D5.S3.Analytic.Monotonicity.FiniteExceptionalValuesMonotonicity
