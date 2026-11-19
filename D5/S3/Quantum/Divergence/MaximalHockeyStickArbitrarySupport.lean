/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickArbitrarySupport
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickArbitrarySupport
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Arbitrary curvature support equality for the original whole-L1 maximal divergence. -/

import D5.S3.Quantum.Divergence.MaximalHockeyStickLoewnerSlopes
import Mathlib.Topology.MetricSpace.UniformConvergence



universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Filter Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology ENNReal
open D5.S3.Analytic.Convexity.CurvatureHingeRepresentation
open D5.S3.Quantum.Divergence.MaximalHockeyStickOverlap
open D5.S3.Quantum.Divergence.MaximalHockeyStickProfile
open D5.S3.Quantum.Divergence.MaximalHockeyStickQuadratic
open D5.S3.Quantum.Divergence.MaximalHockeyStickReverseTest
open D5.S3.Quantum.Divergence.MaximalHockeyStickApproximate
open D5.S3.Quantum.Divergence.MaximalHockeyStickConvex
open D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex

open D5.S3.Quantum.Divergence.MaximalHockeyStickLoewnerSlopes

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickArbitrarySupport

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! Pointwise tail control for the sufficiency route. The witness may have
zero p or zero q labels: its finite cost is used later only for integrability,
not to exclude those labels. Thus this avoids prematurely assuming finite
endpoint values or a general-f optimizer. -/

private theorem prepared_trace_mono {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (s t : ℝ) (hst : s ≤ t) :
    (R.preparedOverlap s).trace.re ≤ (R.preparedOverlap t).trace.re := by
  rw [trace_prepared, trace_prepared]
  exact Finset.sum_le_sum (fun i _ => min_le_min_left (R.p i)
    (mul_le_mul_of_nonneg_right hst (R.q_nonneg i)))

private theorem prepared_trace_scaled_lower {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (r t : ℝ) (hr : 0 < r) (ht : 0 ≤ t) (htr : t ≤ r) :
    (t / r) * (R.preparedOverlap r).trace.re ≤ (R.preparedOverlap t).trace.re := by
  rw [trace_prepared, trace_prepared, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hα : 0 ≤ t / r := div_nonneg ht hr.le
  have hα1 : t / r ≤ 1 := (div_le_one hr).2 htr
  apply le_min
  · calc
      _ ≤ 1 * min (R.p i) (r * R.q i) :=
        mul_le_mul_of_nonneg_right hα1
          (le_min (R.p_nonneg i) (mul_nonneg hr.le (R.q_nonneg i)))
      _ ≤ R.p i := by rw [one_mul]; exact min_le_left _ _
  · calc
      _ ≤ (t / r) * (r * R.q i) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hα
      _ = t * R.q i := by field_simp

/-- A finite witness is linear below an anchor below all its positive p/q
ratios. Labels p=0 are retained. -/
theorem prepared_trace_lower_tail_linear {A B : Matrix n n ℂ} {k : ℕ}
    (W : ReverseTest A B k) (r t : ℝ) (hr : 0 < r) (ht : 0 ≤ t) (htr : t ≤ r)
    (hratio : ∀ i, W.p i = 0 ∨ r * W.q i ≤ W.p i) :
    (W.preparedOverlap t).trace.re = (t / r) * (W.preparedOverlap r).trace.re := by
  rw [trace_prepared, trace_prepared, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rcases hratio i with hp | hp
  · rw [hp, min_eq_left (mul_nonneg ht (W.q_nonneg i)),
      min_eq_left (mul_nonneg hr.le (W.q_nonneg i)), mul_zero]
  · have htp : t * W.q i ≤ W.p i :=
      (mul_le_mul_of_nonneg_right htr (W.q_nonneg i)).trans hp
    rw [min_eq_right htp, min_eq_right hp]
    field_simp

/-- A finite witness is constant above an anchor above all its finite p/q
ratios. Labels q=0 are retained. -/
theorem prepared_trace_upper_tail_constant {A B : Matrix n n ℂ} {k : ℕ}
    (W : ReverseTest A B k) (r t : ℝ) (hrt : r ≤ t)
    (hratio : ∀ i, W.q i = 0 ∨ W.p i ≤ r * W.q i) :
    (W.preparedOverlap t).trace.re = (W.preparedOverlap r).trace.re := by
  rw [trace_prepared, trace_prepared]
  apply Finset.sum_congr rfl
  intro i _
  rcases hratio i with hq | hp
  · simp only [hq, mul_zero]
  · rw [min_eq_left hp,
      min_eq_left (hp.trans (mul_le_mul_of_nonneg_right hrt (W.q_nonneg i)))]

/-- Matching a lower-tail optimal trace makes the entire negative hinge
tail no larger than that of a fixed witness. This is pointwise, so it also
covers infinite endpoint values before any integration is performed. -/
theorem lower_hinge_tail_dominated {A B : Matrix n n ℂ} {k l : ℕ}
    (W : ReverseTest A B k) (R : ReverseTest A B l)
    (r t : ℝ) (hr : 0 < r) (ht : 0 ≤ t) (htr : t ≤ r)
    (hratio : ∀ i, W.p i = 0 ∨ r * W.q i ≤ W.p i)
    (hanchor : (W.preparedOverlap r).trace.re ≤ (R.preparedOverlap r).trace.re) :
    t * B.trace.re - (R.preparedOverlap t).trace.re ≤
      t * B.trace.re - (W.preparedOverlap t).trace.re := by
  apply sub_le_sub_left
  calc
    _ = (t / r) * (W.preparedOverlap r).trace.re :=
      prepared_trace_lower_tail_linear W r t hr ht htr hratio
    _ ≤ (t / r) * (R.preparedOverlap r).trace.re :=
      mul_le_mul_of_nonneg_left hanchor (div_nonneg ht hr.le)
    _ ≤ (R.preparedOverlap t).trace.re := prepared_trace_scaled_lower R r t hr ht htr

/-- The analogous control of the positive hinge tail, keeping q=0 labels. -/
theorem upper_hinge_tail_dominated {A B : Matrix n n ℂ} {k l : ℕ}
    (W : ReverseTest A B k) (R : ReverseTest A B l)
    (r t : ℝ) (hrt : r ≤ t)
    (hratio : ∀ i, W.q i = 0 ∨ W.p i ≤ r * W.q i)
    (hanchor : (W.preparedOverlap r).trace.re ≤ (R.preparedOverlap r).trace.re) :
    A.trace.re - (R.preparedOverlap t).trace.re ≤
      A.trace.re - (W.preparedOverlap t).trace.re := by
  apply sub_le_sub_left
  calc
    _ = (W.preparedOverlap r).trace.re := prepared_trace_upper_tail_constant W r t hrt hratio
    _ ≤ (R.preparedOverlap r).trace.re := hanchor
    _ ≤ (R.preparedOverlap t).trace.re := prepared_trace_mono R r t hrt

/-! Sufficiency. The next scalar facts unfold the *existing* test kernel;
the cost representation itself is reused, not redefined. In particular all
measurability statements use the negative branch at t = 1. -/

private theorem actual_test_kernel_nonneg {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (t : PositiveThreshold) : 0 ≤ testKernel R t := by
  apply Finset.sum_nonneg
  intro i _
  unfold hinge
  split_ifs <;> exact le_max_right _ _

private theorem actual_test_kernel_measurable {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) : Measurable (testKernel R) := by
  change Measurable (fun t : PositiveThreshold => ∑ i,
    if (t : ℝ) ≤ 1 then max ((t : ℝ) * R.q i - R.p i) 0
      else max (R.p i - (t : ℝ) * R.q i) 0)
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_le measurable_subtype_coe measurable_const)
    (((measurable_subtype_coe.mul_const (R.q i)).sub_const (R.p i)).max measurable_const)
    ((measurable_const.sub (measurable_subtype_coe.mul_const (R.q i))).max measurable_const)

private theorem actual_test_kernel_trace {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (t : PositiveThreshold) :
    testKernel R t = if (t : ℝ) ≤ 1 then
      (t : ℝ) * B.trace.re - (R.preparedOverlap t).trace.re
      else A.trace.re - (R.preparedOverlap t).trace.re := by
  change (∑ i, if (t : ℝ) ≤ 1 then max ((t : ℝ) * R.q i - R.p i) 0
      else max (R.p i - (t : ℝ) * R.q i) 0) = _
  split_ifs with ht
  · rw [trace_prepared, right_mass R, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rcases le_total (R.p i) ((t : ℝ) * R.q i) with h | h
    · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]
    · rw [min_eq_right h, sub_self, max_eq_right (sub_nonpos.mpr h)]
  · exact hockey_eq_trace_sub R t

private theorem actual_kernel_gap {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (t : PositiveThreshold) :
    testKernel R t = maximalKernel A B t + gap R t := by
  rw [actual_test_kernel_trace, gap_eq_overlap_trace]
  change (if (t : ℝ) ≤ 1 then
      (t : ℝ) * B.trace.re - (R.preparedOverlap t).trace.re
      else A.trace.re - (R.preparedOverlap t).trace.re) =
    (if (t : ℝ) ≤ 1 then
      (t : ℝ) * B.trace.re - overlapValue A ((t : ℝ) • B)
      else A.trace.re - overlapValue A ((t : ℝ) • B)) +
    (overlapValue A ((t : ℝ) • B) - (R.preparedOverlap t).trace.re)
  split_ifs <;> ring

private theorem actual_maximal_kernel_nonneg
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (t : PositiveThreshold) : 0 ≤ maximalKernel A B t := by
  have hX := optimalOverlap_spec A B hA hB t t.2.le
  have htr := (Complex.nonneg_iff.mp
    (sub_nonneg.mpr hX.1.2.2).posSemidef.trace_nonneg).1
  rw [Matrix.trace_sub, Complex.sub_re, Matrix.trace_smul,
    Complex.real_smul] at htr
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, hX.2] at htr
  unfold maximalKernel
  split_ifs
  · exact htr
  · exact maximal_hockey_nonneg hA hB t.2.le

private theorem actual_hockey_le_maximal
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    hockeyValue hf A B ≤ maximalValue hf A B := by
  apply le_sInf
  rintro _ ⟨k, R, rfl⟩
  rw [finite_cost_decomposition, hockeyValue]
  apply add_le_add le_rfl
  apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr
  apply lintegral_mono
  intro t
  apply ENNReal.ofReal_le_ofReal
  rw [actual_kernel_gap R t]
  exact le_add_of_nonneg_right ((actual_gap_profile_data R hA hB).1 t).1

/-- The actual hockey value is finite because its nonnegative curvature
part lies between a real affine base and the real finite actual infimum. -/
private theorem actual_hockey_real
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (c : ℝ) (hc : maximalValue hf A B = (c : EReal)) :
    ∃ H : ℝ, hockeyValue hf A B = (H : EReal) := by
  have hupper : hockeyValue hf A B ≤ (c : EReal) :=
    (actual_hockey_le_maximal hf A B hA hB).trans_eq hc
  have hlower : (affineMass f A B : EReal) ≤ hockeyValue hf A B := by
    unfold hockeyValue
    apply le_add_of_nonneg_right
    positivity
  have htop : hockeyValue hf A B ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top c) hupper
  have hbot : hockeyValue hf A B ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot (affineMass f A B)) hlower
  exact ⟨(hockeyValue hf A B).toReal, (EReal.coe_toReal htop hbot).symm⟩

/-- The original finite closed-perspective representation gives both
directions of this finiteness bridge. The reverse implication is used
BEFORE any invocation of finite_cost_gap on the interpolants. -/
private theorem integrable_test_kernel_iff_finite_cost
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    {A B : Matrix n n ℂ} {k : ℕ} (R : ReverseTest A B k) :
    Integrable (testKernel R) (curvature hf) ↔ finiteCost hf R ≠ ⊤ := by
  have hn : 0 ≤ᵐ[curvature hf] testKernel R :=
    ae_of_all _ (actual_test_kernel_nonneg R)
  constructor
  · intro hi
    have he : finiteCost hf R =
        ((affineMass f A B + ∫ t, testKernel R t ∂curvature hf : ℝ) : EReal) := by
      rw [finite_cost_decomposition,
        ← ofReal_integral_eq_lintegral_ofReal hi hn, EReal.coe_ennreal_ofReal,
        max_eq_left (integral_nonneg_of_ae hn), ← EReal.coe_add]
    rw [he]
    exact EReal.coe_ne_top _
  · intro hfin
    have hlin : (∫⁻ t, ENNReal.ofReal (testKernel R t) ∂curvature hf) ≠ ⊤ := by
      intro h
      apply hfin
      rw [finite_cost_decomposition, h, EReal.coe_ennreal_top, EReal.coe_add_top]
    exact ⟨(actual_test_kernel_measurable R).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hn).2 (lt_top_iff_ne_top.mpr hlin)⟩

/-- Finite ratios, with both axes retained. Empty alphabets make the sums
zero, hence give the same positive lower and finite upper cutoffs. -/
private theorem witness_ratio_cutoffs {A B : Matrix n n ℂ} {k : ℕ}
    (W : ReverseTest A B k) :
    ∃ l u : ℝ, 0 < l ∧ l < 1 ∧ 1 < u ∧
      (∀ i, W.p i = 0 ∨ l * W.q i ≤ W.p i) ∧
      (∀ i, W.q i = 0 ∨ W.p i ≤ u * W.q i) := by
  classical
  let S : ℝ := ∑ i, W.q i / W.p i
  let T : ℝ := ∑ i, W.p i / W.q i
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => div_nonneg (W.q_nonneg i) (W.p_nonneg i))
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i _ => div_nonneg (W.p_nonneg i) (W.q_nonneg i))
  let l : ℝ := (S + 2)⁻¹
  let u : ℝ := T + 2
  have hl : 0 < l := inv_pos.mpr (by linarith)
  have hlmul : l * (S + 2) = 1 := inv_mul_cancel₀ (by linarith)
  have hlS : 0 ≤ l * S := mul_nonneg hl.le hS
  have hl1 : l < 1 := by nlinarith
  refine ⟨l, u, hl, hl1, by dsimp [u]; linarith, ?_, ?_⟩
  · intro i
    by_cases hp : W.p i = 0
    · exact Or.inl hp
    · right
      have hp0 : 0 < W.p i := lt_of_le_of_ne (W.p_nonneg i) (Ne.symm hp)
      have hterm : W.q i / W.p i ≤ S :=
        Finset.single_le_sum (fun j _ => div_nonneg (W.q_nonneg j) (W.p_nonneg j))
          (Finset.mem_univ i)
      have hprod : l * (W.q i / W.p i) ≤ 1 := by
        have := mul_le_mul_of_nonneg_left hterm hl.le
        nlinarith
      apply (div_le_one hp0).1
      convert hprod using 1 <;> ring
  · intro i
    by_cases hq : W.q i = 0
    · exact Or.inl hq
    · right
      have hq0 : 0 < W.q i := lt_of_le_of_ne (W.q_nonneg i) (Ne.symm hq)
      have hterm : W.p i / W.q i ≤ T :=
        Finset.single_le_sum (fun j _ => div_nonneg (W.p_nonneg j) (W.q_nonneg j))
          (Finset.mem_univ i)
      apply (div_le_iff₀ hq0).1
      exact hterm.trans (by dsimp [u]; linarith)

/-- Each effective endpoint is either an actual support anchor or the
corresponding open tail contains no support. No positive anchor is invented
when that part of the support is empty. -/
private theorem witness_support_endpoints {A B : Matrix n n ℂ} {k : ℕ}
    (W : ReverseTest A B k) (K : Set PositiveThreshold) :
    ∃ a b : PositiveThreshold, (a : ℝ) < 1 ∧ 1 < (b : ℝ) ∧
      (∀ i, W.p i = 0 ∨ (a : ℝ) * W.q i ≤ W.p i) ∧
      (∀ i, W.q i = 0 ∨ W.p i ≤ (b : ℝ) * W.q i) ∧
      (a ∈ K ∨ ∀ t ∈ K, a ≤ t) ∧ (b ∈ K ∨ ∀ t ∈ K, t ≤ b) := by
  classical
  obtain ⟨l, u, hl0, hl1, hu1, hlratio, huratio⟩ := witness_ratio_cutoffs W
  have hleft : ∃ a : PositiveThreshold, (a : ℝ) < 1 ∧
      (∀ i, W.p i = 0 ∨ (a : ℝ) * W.q i ≤ W.p i) ∧
      (a ∈ K ∨ ∀ t ∈ K, a ≤ t) := by
    by_cases h : ∃ t : PositiveThreshold, t ∈ K ∧ (t : ℝ) < l
    · obtain ⟨a, haK, hal⟩ := h
      refine ⟨a, hal.trans hl1, ?_, Or.inl haK⟩
      intro i
      exact (hlratio i).imp_right (fun hi =>
        (mul_le_mul_of_nonneg_right hal.le (W.q_nonneg i)).trans hi)
    · refine ⟨⟨l, hl0⟩, hl1, hlratio, Or.inr ?_⟩
      intro t ht
      exact le_of_not_gt (fun htl => h ⟨t, ht, htl⟩)
  have hright : ∃ b : PositiveThreshold, 1 < (b : ℝ) ∧
      (∀ i, W.q i = 0 ∨ W.p i ≤ (b : ℝ) * W.q i) ∧
      (b ∈ K ∨ ∀ t ∈ K, t ≤ b) := by
    by_cases h : ∃ t : PositiveThreshold, t ∈ K ∧ u < (t : ℝ)
    · obtain ⟨b, hbK, hub⟩ := h
      refine ⟨b, hu1.trans hub, ?_, Or.inl hbK⟩
      intro i
      exact (huratio i).imp_right (fun hi =>
        hi.trans (mul_le_mul_of_nonneg_right hub.le (W.q_nonneg i)))
    · refine ⟨⟨u, lt_trans (by norm_num) hu1⟩, hu1, huratio, Or.inr ?_⟩
      intro t ht
      exact le_of_not_gt (fun hut => h ⟨t, ht, hut⟩)
  obtain ⟨a, ha1, haratio, haK⟩ := hleft
  obtain ⟨b, hb1, hbratio, hbK⟩ := hright
  exact ⟨a, b, ha1, hb1, haratio, hbratio, haK, hbK⟩

/-- Sort the distinct real knots after inserting virtual zero. This also
works for S = empty: the tuple then has length one and no secants. -/
private theorem realizes_finite_set
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (K : Set PositiveThreshold) (hC : FiniteLoewnerSlopes A B hA hB K)
    (S : Finset PositiveThreshold) (hSK : ∀ t ∈ S, t ∈ K) :
    ∃ k : ℕ, ∃ R : ReverseTest A B k,
      ∀ t ∈ S, R.preparedOverlap t = optimalOverlap A B hA hB t := by
  classical
  let P : Finset ℝ := S.image Subtype.val
  let T : Finset ℝ := insert 0 P
  have hzero : (0 : ℝ) ∉ P := by
    rintro hz
    change (0 : ℝ) ∈ S.image Subtype.val at hz
    obtain ⟨x, hx, hx0⟩ : ∃ x : PositiveThreshold, x ∈ S ∧ (x : ℝ) = 0 :=
      Finset.mem_image.1 hz
    exact (ne_of_gt x.2) hx0
  have hcard : T.card = P.card + 1 := Finset.card_insert_of_notMem hzero
  let t : Fin (P.card + 1) ↪o ℝ := T.orderEmbOfFin hcard
  have htmem (i : Fin (P.card + 1)) : t i ∈ T := T.orderEmbOfFin_mem hcard i
  have htrange : Set.range t = (T : Set ℝ) := T.range_orderEmbOfFin hcard
  have hnonneg (i : Fin (P.card + 1)) : 0 ≤ t i := by
    have hiT : t i ∈ insert 0 (S.image Subtype.val) := by
      simpa [T, P] using htmem i
    rcases Finset.mem_insert.1 hiT with hi | hi
    · rw [hi]
    · obtain ⟨s, hs, hsi⟩ : ∃ s : PositiveThreshold, s ∈ S ∧ (s : ℝ) = t i :=
        Finset.mem_image.1 hi
      exact hsi ▸ s.2.le
  have ht0 : t 0 = 0 := by
    have hz : (0 : ℝ) ∈ Set.range t := by rw [htrange]; exact Finset.mem_insert_self _ _
    obtain ⟨i, hi⟩ := hz
    exact le_antisymm (by simpa only [hi] using t.monotone (Fin.zero_le i)) (hnonneg 0)
  have htK (i : Fin (P.card + 1)) (hi : 0 < t i) :
      (⟨t i, hi⟩ : PositiveThreshold) ∈ K := by
    have hiT : t i ∈ insert 0 (S.image Subtype.val) := by
      simpa [T, P] using htmem i
    rcases Finset.mem_insert.1 hiT with hz | hp
    · exact False.elim ((ne_of_gt hi) hz)
    · obtain ⟨s, hs, hsi⟩ : ∃ s : PositiveThreshold, s ∈ S ∧ (s : ℝ) = t i :=
        Finset.mem_image.1 hp
      have he : (⟨t i, hi⟩ : PositiveThreshold) = s := Subtype.ext hsi.symm
      rw [he]
      exact hSK s hs
  obtain ⟨k, R, hR⟩ := finiteLoewnerSlopes_realizes_knots A B hA hB K hC
    P.card t ht0 t.strictMono htK
  refine ⟨k, R, ?_⟩
  intro s hs
  have hsrange : (s : ℝ) ∈ Set.range t := by
    rw [htrange]
    apply Finset.mem_insert_of_mem
    have hmem : (s : ℝ) ∈ S.image Subtype.val :=
      Finset.mem_image.2 ⟨s, hs, rfl⟩
    simpa [P] using hmem
  obtain ⟨i, hi⟩ := hsrange
  simpa only [hi] using hR i

/-- Every fixed support anchor occurs at every stage, and every dense knot
occurs permanently from its own index onwards. Alphabets may vary with j. -/
private theorem finite_knot_exhaustion
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (K : Set PositiveThreshold) (hC : FiniteLoewnerSlopes A B hA hB K)
    (F : Finset PositiveThreshold) (hFK : ∀ t ∈ F, t ∈ K)
    (q : ℕ → PositiveThreshold) (hqK : ∀ i, q i ∈ K) :
    ∃ tests : ∀ j : ℕ, Σ k : ℕ, ReverseTest A B k,
      (∀ j t, t ∈ F → (tests j).2.preparedOverlap t = optimalOverlap A B hA hB t) ∧
      (∀ i j, i ≤ j → (tests j).2.preparedOverlap (q i) =
        optimalOverlap A B hA hB (q i)) := by
  classical
  let S (j : ℕ) : Finset PositiveThreshold := F ∪ (Finset.range (j + 1)).image q
  have hSK (j : ℕ) : ∀ t ∈ S j, t ∈ K := by
    intro t ht
    rcases Finset.mem_union.1 ht with ht | ht
    · exact hFK t ht
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ht
      exact hqK i
  have hex (j : ℕ) := realizes_finite_set A B hA hB K hC (S j) (hSK j)
  choose k R hR using hex
  refine ⟨fun j => ⟨k j, R j⟩, ?_, ?_⟩
  · intro j t ht
    exact hR j t (Finset.mem_union_left _ ht)
  · intro i j hij
    apply hR j (q i)
    exact Finset.mem_union_right _
      (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)

private theorem prepared_trace_nonneg {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (t : PositiveThreshold) :
    0 ≤ (R.preparedOverlap t).trace.re := by
  rw [trace_prepared]
  exact Finset.sum_nonneg (fun i _ =>
    le_min (R.p_nonneg i) (mul_nonneg t.2.le (R.q_nonneg i)))

private theorem test_kernel_middle_bound {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (b t : PositiveThreshold) (htb : t ≤ b) :
    testKernel R t ≤ A.trace.re + (b : ℝ) * B.trace.re := by
  have hAtr := (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have hBtr := (Complex.nonneg_iff.mp hB.trace_nonneg).1
  have htr := prepared_trace_nonneg R t
  rw [actual_test_kernel_trace]
  split_ifs
  · have htb' : (t : ℝ) ≤ (b : ℝ) := htb
    have hmul := mul_le_mul_of_nonneg_right htb' hBtr
    linarith
  · have hmul := mul_nonneg b.2.le hBtr
    linarith

private theorem anchor_trace_dominates {A B : Matrix n n ℂ} {k l : ℕ}
    (W : ReverseTest A B k) (R : ReverseTest A B l)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (t : PositiveThreshold)
    (hRt : R.preparedOverlap t = optimalOverlap A B hA hB t) :
    (W.preparedOverlap t).trace.re ≤ (R.preparedOverlap t).trace.re := by
  rw [hRt, (optimalOverlap_spec A B hA hB t t.2.le).2]
  exact feasible_le_value (W.overlap_feasible t t.2.le)

/-- Compactness is inside the positive threshold space. In particular the
lower endpoint remains strictly positive even when K accumulates at zero. -/
private theorem compact_threshold_interval (a b : PositiveThreshold) :
    IsCompact (Icc a b : Set PositiveThreshold) := by
  rw [Subtype.isCompact_iff]
  have he : (Subtype.val '' (Icc a b : Set PositiveThreshold) : Set ℝ) =
      Icc (a : ℝ) (b : ℝ) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hx
      exact ⟨⟨x, lt_of_lt_of_le a.2 hx.1⟩, hx, rfl⟩
  rw [he]
  exact isCompact_Icc

/-- One explicit integrable envelope for the *test kernels*, not just the
gaps. Thus it also proves the finite actual costs needed by the gap formula.
Outside [a,b] the witness dominates at every point of the actual support;
absent-anchor tails are discarded only via conull support. -/
private theorem witness_dominated_kernels
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    {k : ℕ} (W : ReverseTest A B k) (hW : Integrable (testKernel W) (curvature hf))
    (a b : PositiveThreshold) (ha1 : (a : ℝ) < 1) (hb1 : 1 < (b : ℝ))
    (haratio : ∀ i, W.p i = 0 ∨ (a : ℝ) * W.q i ≤ W.p i)
    (hbratio : ∀ i, W.q i = 0 ∨ W.p i ≤ (b : ℝ) * W.q i)
    (haleft : a ∈ (curvature hf).support ∨ ∀ t ∈ (curvature hf).support, a ≤ t)
    (hbright : b ∈ (curvature hf).support ∨ ∀ t ∈ (curvature hf).support, t ≤ b)
    (tests : ∀ j : ℕ, Σ l : ℕ, ReverseTest A B l)
    (hRa : a ∈ (curvature hf).support → ∀ j,
      (tests j).2.preparedOverlap a = optimalOverlap A B hA hB a)
    (hRb : b ∈ (curvature hf).support → ∀ j,
      (tests j).2.preparedOverlap b = optimalOverlap A B hA hB b) :
    ∃ E : PositiveThreshold → ℝ, Integrable E (curvature hf) ∧
      (∀ t, 0 ≤ E t) ∧
      (∀ j, ∀ᵐ t ∂curvature hf, ‖testKernel (tests j).2 t‖ ≤ E t) ∧
      (∀ j, ∀ᵐ t ∂curvature hf, ‖gap (tests j).2 t‖ ≤ E t) := by
  classical
  letI : IsLocallyFiniteMeasure (curvature hf : Measure PositiveThreshold) :=
    curvature_locallyFinite hf
  let C : ℝ := A.trace.re + (b : ℝ) * B.trace.re
  have hC : 0 ≤ C := add_nonneg
    (Complex.nonneg_iff.mp hA.trace_nonneg).1
    (mul_nonneg b.2.le (Complex.nonneg_iff.mp hB.trace_nonneg).1)
  let middle : PositiveThreshold → ℝ := (Icc a b).indicator (fun _ => C)
  let E : PositiveThreshold → ℝ := fun t => testKernel W t + middle t
  have hmiddle : Integrable middle (curvature hf) := by
    apply (integrable_indicator_iff measurableSet_Icc).2
    exact integrableOn_const (compact_threshold_interval a b).measure_ne_top
  have hE : Integrable E (curvature hf) := hW.add hmiddle
  have hmiddle0 (t : PositiveThreshold) : 0 ≤ middle t := by
    dsimp [middle]
    exact Set.indicator_nonneg (fun _ _ => hC) t
  have hE0 (t : PositiveThreshold) : 0 ≤ E t :=
    add_nonneg (actual_test_kernel_nonneg W t) (hmiddle0 t)
  have hbound (j : ℕ) : ∀ᵐ t ∂curvature hf, testKernel (tests j).2 t ≤ E t := by
    filter_upwards [Measure.support_mem_ae (μ := curvature hf)] with t htK
    by_cases hta : t < a
    · have haK : a ∈ (curvature hf).support := by
        rcases haleft with h | h
        · exact h
        · exact False.elim (not_lt_of_ge (h t htK) hta)
      have ht1 : (t : ℝ) ≤ 1 := (show (t : ℝ) < (a : ℝ) from hta).le.trans ha1.le
      have htail := lower_hinge_tail_dominated W (tests j).2 a t a.2 t.2.le hta.le
        haratio (anchor_trace_dominates W (tests j).2 hA hB a (hRa haK j))
      have hk : testKernel (tests j).2 t ≤ testKernel W t := by
        simpa only [actual_test_kernel_trace, if_pos ht1] using htail
      exact hk.trans (le_add_of_nonneg_right (hmiddle0 t))
    · by_cases hbt : b < t
      · have hbK : b ∈ (curvature hf).support := by
          rcases hbright with h | h
          · exact h
          · exact False.elim (not_lt_of_ge (h t htK) hbt)
        have ht1 : ¬(t : ℝ) ≤ 1 := not_le.mpr
          (hb1.trans (show (b : ℝ) < (t : ℝ) from hbt))
        have htail := upper_hinge_tail_dominated W (tests j).2 b t hbt.le hbratio
          (anchor_trace_dominates W (tests j).2 hA hB b (hRb hbK j))
        have hk : testKernel (tests j).2 t ≤ testKernel W t := by
          simpa only [actual_test_kernel_trace, if_neg ht1] using htail
        exact hk.trans (le_add_of_nonneg_right (hmiddle0 t))
      · have htm : t ∈ Icc a b := ⟨le_of_not_gt hta, le_of_not_gt hbt⟩
        have hm : middle t = C := Set.indicator_of_mem htm _
        dsimp only [E]
        rw [hm]
        exact (test_kernel_middle_bound (tests j).2 hA hB b t htm.2).trans
          (le_add_of_nonneg_left (actual_test_kernel_nonneg W t))
  refine ⟨E, hE, hE0, ?_, ?_⟩
  · intro j
    filter_upwards [hbound j] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (actual_test_kernel_nonneg (tests j).2 t)]
      using ht
  · intro j
    filter_upwards [hbound j] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg ((actual_gap_profile_data (tests j).2 hA hB).1 t).1]
    apply le_trans _ ht
    rw [actual_kernel_gap]
    exact le_add_of_nonneg_left (actual_maximal_kernel_nonneg A B hA hB t)

/-- C -> E for the actual finite infimum. This is approximation by finite
knots, not an assertion that one finite test realizes the whole support. -/
private theorem finiteLoewnerSlopes_implies_integrated_eq
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (c : ℝ) (hc : maximalValue hf A B = (c : EReal))
    (hC : FiniteLoewnerSlopes A B hA hB (curvature hf).support) :
    maximalValue hf A B = hockeyValue hf A B := by
  classical
  have hHM := actual_hockey_le_maximal hf A B hA hB
  obtain ⟨H, hH⟩ := actual_hockey_real hf A B hA hB c hc
  obtain ⟨near, hnear⟩ := approximate_finite_tests hf A B c hc
  let W : ReverseTest A B (near 0).1 := (near 0).2
  have hWfin : finiteCost hf W ≠ ⊤ := ne_top_of_lt (hnear 0)
  have hW : Integrable (testKernel W) (curvature hf) :=
    (integrable_test_kernel_iff_finite_cost hf W).2 hWfin
  by_cases hKempty : (curvature hf).support = ∅
  · have hμ : curvature hf = 0 := Measure.support_eq_empty_iff.1 hKempty
    have hg := finite_cost_gap hf W hA hB hWfin
    have hcost : finiteCost hf W = hockeyValue hf A B := by
      calc
        finiteCost hf W = hockeyValue hf A B +
            (∫ t, gap W t ∂curvature hf : ℝ) := hg.2
        _ = hockeyValue hf A B := by
          rw [hμ, integral_zero_measure, EReal.coe_zero, add_zero]
    have hMW : maximalValue hf A B ≤ finiteCost hf W := sInf_le ⟨(near 0).1, W, rfl⟩
    exact le_antisymm (hMW.trans_eq hcost) hHM
  · have hKne : (curvature hf).support.Nonempty := Set.nonempty_iff_ne_empty.2 hKempty
    letI : Nonempty (curvature hf).support := hKne.to_subtype
    obtain ⟨qK, hqK⟩ := TopologicalSpace.exists_dense_seq (curvature hf).support
    let q : ℕ → PositiveThreshold := fun i => (qK i).1
    have hqmem (i : ℕ) : q i ∈ (curvature hf).support := (qK i).2
    have hqclosure (t : PositiveThreshold) (ht : t ∈ (curvature hf).support) :
        t ∈ closure (Set.range q) := by
      have hd : (⟨t, ht⟩ : (curvature hf).support) ∈ closure (Set.range qK) := hqK _
      have hd' := closure_subtype.1 hd
      have himage : (Subtype.val '' Set.range qK : Set PositiveThreshold) = Set.range q := by
        ext x
        constructor
        · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, by simp [q]⟩
        · rintro ⟨i, rfl⟩
          exact ⟨qK i, ⟨i, rfl⟩, by simp [q]⟩
      rwa [himage] at hd'
    obtain ⟨a, b, ha1, hb1, haratio, hbratio, haleft, hbright⟩ :=
      witness_support_endpoints W (curvature hf).support
    let F : Finset PositiveThreshold :=
      Finset.filter (fun t : PositiveThreshold => t ∈ (curvature hf).support)
        ({a, b} : Finset PositiveThreshold)
    have hFK : ∀ t ∈ F, t ∈ (curvature hf).support := by
      intro t ht
      change t ∈ ({a, b} : Finset PositiveThreshold).filter
        (fun t => t ∈ (curvature hf).support) at ht
      exact (Finset.mem_filter.1 ht).2
    obtain ⟨tests, hRF, hRq⟩ := finite_knot_exhaustion A B hA hB
      (curvature hf).support hC F hFK q hqmem
    have hRa (haK : a ∈ (curvature hf).support) (j : ℕ) :
        (tests j).2.preparedOverlap a = optimalOverlap A B hA hB a := by
      apply hRF j a
      change a ∈ ({a, b} : Finset PositiveThreshold).filter
        (fun t => t ∈ (curvature hf).support)
      exact Finset.mem_filter.2 ⟨by simp, haK⟩
    have hRb (hbK : b ∈ (curvature hf).support) (j : ℕ) :
        (tests j).2.preparedOverlap b = optimalOverlap A B hA hB b := by
      apply hRF j b
      change b ∈ ({a, b} : Finset PositiveThreshold).filter
        (fun t => t ∈ (curvature hf).support)
      exact Finset.mem_filter.2 ⟨by simp, hbK⟩
    obtain ⟨E, hE, hE0, hEkernel, hEgap⟩ := witness_dominated_kernels hf A B hA hB
      W hW a b ha1 hb1 haratio hbratio haleft hbright tests hRa hRb
    have hcostfin (j : ℕ) : finiteCost hf (tests j).2 ≠ ⊤ := by
      apply (integrable_test_kernel_iff_finite_cost hf (tests j).2).1
      exact hE.mono' (actual_test_kernel_measurable (tests j).2).aestronglyMeasurable (hEkernel j)
    have hg (j : ℕ) := finite_cost_gap hf (tests j).2 hA hB (hcostfin j)
    have hzero (i : ℕ) : ∀ᶠ j in atTop, gap (tests j).2 (q i) = 0 := by
      filter_upwards [eventually_ge_atTop i] with j hij
      rw [gap_eq_overlap_trace, hRq i j hij,
        (optimalOverlap_spec A B hA hB (q i) (q i).2.le).2, sub_self]
    have hpoint (t : PositiveThreshold) (ht : t ∈ (curvature hf).support) :
        Tendsto (fun j => gap (tests j).2 t) atTop (𝓝 0) := by
      have hequi := (LipschitzWith.uniformEquicontinuous
        (fun j t => gap (tests j).2 t) (Real.toNNReal (2 * B.trace.re))
        (fun j => (actual_gap_profile_data (tests j).2 hA hB).2)).equicontinuous
      apply (hequi t).tendsto_of_mem_closure
        (f := fun _ => (0 : ℝ)) tendsto_const_nhds _ (hqclosure t ht)
      rintro _ ⟨i, rfl⟩
      exact tendsto_const_nhds.congr' ((hzero i).mono (fun _ hi => hi.symm))
    have hgaplim : Tendsto (fun j => ∫ t, gap (tests j).2 t ∂curvature hf)
        atTop (𝓝 0) := by
      have hae : ∀ᵐ t ∂curvature hf,
          Tendsto (fun j => gap (tests j).2 t) atTop (𝓝 ((fun _ => (0 : ℝ)) t)) := by
        filter_upwards [Measure.support_mem_ae (μ := curvature hf)] with t ht
        exact hpoint t ht
      change Tendsto (fun j => ∫ t : PositiveThreshold, gap (tests j).2 t ∂curvature hf)
        atTop (𝓝 0)
      simpa only [integral_zero] using tendsto_integral_of_dominated_convergence E
        (fun j => (hg j).1.aestronglyMeasurable) hE hEgap hae
    have hineq (j : ℕ) : c ≤ H + ∫ t, gap (tests j).2 t ∂curvature hf := by
      have hMtest : maximalValue hf A B ≤ finiteCost hf (tests j).2 :=
        sInf_le ⟨(tests j).1, (tests j).2, rfl⟩
      rw [hc, (hg j).2, hH, ← EReal.coe_add, EReal.coe_le_coe_iff] at hMtest
      exact hMtest
    have hlimit : Tendsto (fun j => H + ∫ t, gap (tests j).2 t ∂curvature hf)
        atTop (𝓝 H) := by
      simpa only [add_zero] using (tendsto_const_nhds.add hgaplim)
    have hcH : c ≤ H := le_of_tendsto_of_tendsto tendsto_const_nhds hlimit
      (Eventually.of_forall hineq)
    apply le_antisymm _ hHM
    rw [hc, hH, EReal.coe_le_coe_iff]
    exact hcH

/-- Sufficiency for the entire original complex-L1 sigma-finite source
class in the independent universe u. Both values are the existing actual
ones, identified by the proved source-class and operational equalities. -/
theorem finiteLoewnerSlopes_implies_original_eq
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (c : ℝ) (hc : originalL1Value.{u} hf A B = (c : EReal))
    (hC : FiniteLoewnerSlopes A B hA hB (curvature hf).support) :
    originalL1Value.{u} hf A B = originalHockeyValue.{u} hf A B := by
  have hbridge : originalL1Value.{u} hf A B = maximalValue hf A B :=
    (originalL1Value_eq_allL1Value hf A B).trans (allL1Value_eq_maximalValue hf A B)
  have hM : maximalValue hf A B = (c : EReal) := hbridge.symm.trans hc
  exact hbridge.trans ((finiteLoewnerSlopes_implies_integrated_eq hf A B hA hB c hM hC).trans
    (hockeyValue_eq_original_operational hf A B hA hB).1)

/-- Arbitrary-support criterion for equality of the ACTUAL original-L1
infimum and ACTUAL hockey curvature value, at every finite matrix size.
The tuple condition includes virtual zero and all positive nodes lie in
the actual Stieltjes support. No endpoint finiteness or f-optimizer premise. -/
theorem original_eq_iff_finiteLoewnerSlopes
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (c : ℝ) (hc : originalL1Value.{u} hf A B = (c : EReal)) :
    (originalL1Value.{u} hf A B = originalHockeyValue.{u} hf A B) ↔
      FiniteLoewnerSlopes A B hA hB (curvature hf).support := by
  exact ⟨original_eq_implies_finiteLoewnerSlopes hf A B hA hB c hc,
    finiteLoewnerSlopes_implies_original_eq hf A B hA hB c hc⟩

end D5.S3.Quantum.Divergence.MaximalHockeyStickArbitrarySupport
