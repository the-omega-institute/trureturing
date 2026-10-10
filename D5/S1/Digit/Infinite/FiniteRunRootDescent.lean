/- GID: D5/S1/Digit/Infinite/FiniteRunRootDescent
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/FiniteRunRootDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite high-run roots descend to the cap root, and logarithmic rates ascend to the cap rate. -/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

open Filter Finset Set
open scoped Topology BigOperators

namespace D5.S1.Digit.Infinite.FiniteRunRootDescent

private theorem geometric_crossing (a h : ℝ) (ha : 0 < a) (hh : 0 ≤ h)
    (hcross : 1 < a + h) :
    ∀ᶠ n : ℕ in atTop, 1 < a * ∑ j ∈ range n, h ^ j := by
  by_cases hlt : h < 1
  · have hs := (hasSum_geometric_of_lt_one hh hlt).tendsto_sum_nat
    have ht := hs.const_mul a
    have hc : 1 < a * (1 - h)⁻¹ := by
      rw [← div_eq_mul_inv, lt_div_iff₀ (sub_pos.mpr hlt)]
      linarith
    exact ht.eventually (lt_mem_nhds hc)
  · have hge : 1 ≤ h := le_of_not_gt hlt
    have ht : Tendsto (fun n : ℕ => a * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop ha
    filter_upwards [ht.eventually_gt_atTop 1] with n hn
    apply hn.trans_le
    apply mul_le_mul_of_nonneg_left _ ha.le
    calc
      (n : ℝ) = ∑ _j ∈ range n, (1 : ℝ) := by simp
      _ ≤ ∑ j ∈ range n, h ^ j := sum_le_sum fun j _ => one_le_pow₀ hge

#print axioms geometric_crossing

noncomputable def numerator (k : ℕ) (x : ℝ) : ℝ :=
  ∑ r ∈ range k, x ^ (26 + 20 * r)
noncomputable def cap (k : ℕ) (x : ℝ) : ℝ := numerator k x / (1 - x ^ 6)
noncomputable def high (k : ℕ) (x : ℝ) : ℝ := x ^ (6 + 20 * k) / (1 - x ^ 6)
noncomputable def truncated (k n : ℕ) (x : ℝ) : ℝ :=
  cap (k - 1) x * ∑ j ∈ range (n + 2), high k x ^ j

private lemma numerator_nonneg (k : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ numerator k x :=
  sum_nonneg fun _ _ => pow_nonneg hx _

private lemma numerator_pos {k : ℕ} (hk : 0 < k) {x : ℝ} (hx : 0 < x) :
    0 < numerator k x := by
  apply sum_pos' (fun _ _ => pow_nonneg hx.le _)
  exact ⟨0, mem_range.mpr hk, pow_pos hx _⟩

private lemma numerator_mono (k : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    numerator k x ≤ numerator k y :=
  sum_le_sum fun _ _ => pow_le_pow_left₀ hx hxy _

private lemma numerator_strict {k : ℕ} (hk : 0 < k) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x < y) : numerator k x < numerator k y := by
  apply sum_lt_sum (fun _ _ => pow_le_pow_left₀ hx hxy.le _)
  exact ⟨0, mem_range.mpr hk, pow_lt_pow_left₀ hxy hx (by omega)⟩

private lemma denominator_pos {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) : 0 < 1 - x ^ 6 :=
  sub_pos.mpr (pow_lt_one₀ hx.1 hx.2 (by norm_num))

private lemma cap_nonneg (k : ℕ) {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) : 0 ≤ cap k x :=
  div_nonneg (numerator_nonneg k hx.1) (denominator_pos hx).le

private lemma cap_pos {k : ℕ} (hk : 0 < k) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < cap k x := div_pos (numerator_pos hk hx.1) (denominator_pos ⟨hx.1.le,hx.2⟩)

private lemma cap_strict {k : ℕ} (hk : 0 < k) : StrictMonoOn (cap k) (Ico (0 : ℝ) 1) := by
  intro x hx y hy hxy
  exact div_lt_div₀ (numerator_strict hk hx.1 hxy)
    (sub_le_sub_left (pow_le_pow_left₀ hx.1 hxy.le 6) 1)
    (numerator_nonneg k hy.1) (denominator_pos hy)

private lemma high_nonneg (k : ℕ) {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) : 0 ≤ high k x :=
  div_nonneg (pow_nonneg hx.1 _) (denominator_pos hx).le

private lemma high_pos (k : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < high k x :=
  div_pos (pow_pos hx.1 _) (denominator_pos ⟨hx.1.le,hx.2⟩)

private lemma high_mono (k : ℕ) : MonotoneOn (high k) (Ico (0 : ℝ) 1) := by
  intro x hx y hy hxy
  exact div_le_div₀ (pow_nonneg hy.1 _) (pow_le_pow_left₀ hx.1 hxy _)
    (denominator_pos hy) (sub_le_sub_left (pow_le_pow_left₀ hx.1 hxy 6) 1)

private lemma cap_continuous (k : ℕ) : ContinuousOn (cap k) (Ico (0 : ℝ) 1) := by
  apply ContinuousOn.div
  · unfold numerator
    fun_prop
  · fun_prop
  · intro x hx
    exact (denominator_pos hx).ne'

private lemma high_continuous (k : ℕ) : ContinuousOn (high k) (Ico (0 : ℝ) 1) := by
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro x hx
    exact (denominator_pos hx).ne'

private lemma truncated_continuous (k n : ℕ) :
    ContinuousOn (truncated k n) (Ico (0 : ℝ) 1) := by
  unfold truncated
  exact (cap_continuous (k-1)).mul (continuousOn_finsetSum _ fun j _ =>
    (high_continuous k).pow j)

private lemma truncated_strict {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    StrictMonoOn (truncated k n) (Ico (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hs : (∑ j ∈ range (n+2), high k x ^ j) ≤
      ∑ j ∈ range (n+2), high k y ^ j :=
    sum_le_sum fun j _ => pow_le_pow_left₀ (high_nonneg k hx) (high_mono k hx hy hxy.le) j
  exact mul_lt_mul ((cap_strict (by omega : 0 < k-1)) hx hy hxy) hs
    (geom_sum_pos (high_nonneg k hx) (by omega)) (cap_nonneg (k-1) hy)

private lemma cap_successor {k : ℕ} (hk : 1 ≤ k) (x : ℝ) :
    cap k x = cap (k-1) x + high k x := by
  have hn : k = (k-1)+1 := by omega
  unfold cap numerator high
  conv_lhs => rw [hn, sum_range_succ]
  have he : 26+20*(k-1) = 6+20*k := by omega
  rw [he, add_div]

private lemma cap_root_exists {k : ℕ} (hk : 0 < k) :
    ∃ x ∈ Ioo (0 : ℝ) 1, cap k x = 1 := by
  let p : ℝ → ℝ := fun x => x^6 + numerator k x
  have hp : Continuous p := by unfold p numerator; fun_prop
  have hp0 : p 0 = 0 := by simp [p, numerator]
  have hp1 : p 1 = 1 + (k : ℝ) := by simp [p, numerator]
  have hbr : 1 ∈ Ioo (p 0) (p 1) := by
    rw [hp0, hp1]
    constructor
    · norm_num
    · have : 0 < (k : ℝ) := by exact_mod_cast hk
      linarith
  obtain ⟨x, hx, hpx⟩ := intermediate_value_Ioo (by norm_num : (0:ℝ) ≤ 1) hp.continuousOn hbr
  refine ⟨x, hx, ?_⟩
  unfold cap
  rw [div_eq_one_iff_eq (denominator_pos ⟨hx.1.le,hx.2⟩).ne']
  dsimp [p] at hpx
  linarith

private lemma cap_root_unique {k : ℕ} (hk : 0 < k) {x y : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1)
    (hex : cap k x = 1) (hey : cap k y = 1) : x = y :=
  (cap_strict hk).injOn ⟨hx.1.le,hx.2⟩ ⟨hy.1.le,hy.2⟩ (hex.trans hey.symm)

private lemma truncated_root_exists {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    ∃ x ∈ Ioo (0 : ℝ) 1, truncated k n x = 1 := by
  obtain ⟨b,hb,he⟩ := cap_root_exists (by omega : 0 < k-1)
  have hb0 : truncated k n 0 = 0 := by simp [truncated, cap, numerator]
  have hsb : 1 < ∑ j ∈ range (n+2), high k b ^ j := by
    have hbase : (1 : ℝ) + high k b ≤ ∑ j ∈ range (n+2), high k b ^ j := by
      calc
        1 + high k b = ∑ j ∈ range 2, high k b ^ j := by simp [sum_range_succ]
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
          (fun j _ _ => pow_nonneg (high_pos k hb).le j)
    linarith [high_pos k hb]
  have hsb' : 1 < truncated k n b := by simpa only [truncated, he, one_mul] using hsb
  have hc : ContinuousOn (truncated k n) (Icc (0 : ℝ) b) :=
    (truncated_continuous k n).mono fun x hx => ⟨hx.1,hx.2.trans_lt hb.2⟩
  obtain ⟨x,hx,hex⟩ := intermediate_value_Ioo hb.1.le hc
    (show 1 ∈ Ioo (truncated k n 0) (truncated k n b) from
      ⟨by rw [hb0]; norm_num,hsb'⟩)
  exact ⟨x,⟨hx.1,hx.2.trans hb.2⟩,hex⟩

private lemma truncated_at_cap_root {k : ℕ} (hk : 2 ≤ k) {z : ℝ}
    (hz : z ∈ Ioo (0 : ℝ) 1) (he : cap k z = 1) (n : ℕ) :
    truncated k n z = 1 - high k z ^ (n + 2) := by
  have hs := cap_successor (by omega : 1 ≤ k) z
  have hg := geom_sum_mul_neg (high k z) (n+2)
  unfold truncated
  rw [he] at hs
  have ha : cap (k-1) z = 1 - high k z := by linarith
  rw [ha, mul_comm]
  exact hg

private lemma root_above_cap {k : ℕ} (hk : 2 ≤ k) {z x : ℝ}
    (hz : z ∈ Ioo (0 : ℝ) 1) (he : cap k z = 1)
    (n : ℕ) (hx : x ∈ Ioo (0 : ℝ) 1) (hex : truncated k n x = 1) : z < x := by
  apply ((truncated_strict hk n).lt_iff_lt ⟨hz.1.le,hz.2⟩ ⟨hx.1.le,hx.2⟩).mp
  rw [hex, truncated_at_cap_root hk hz he n]
  linarith [pow_pos (high_pos k hz) (n+2)]

private lemma truncated_succ_gt {k : ℕ} (hk : 2 ≤ k) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (n : ℕ) : truncated k n x < truncated k (n+1) x := by
  unfold truncated
  have hsum : (∑ j ∈ range (n+1+2), high k x ^ j) =
      (∑ j ∈ range (n+2), high k x ^ j) + high k x ^ (n+2) := by
    simpa only [Nat.add_assoc] using sum_range_succ (fun j => high k x ^ j) (n+2)
  rw [hsum, mul_add]
  exact lt_add_of_pos_right _
    (mul_pos (cap_pos (by omega : 0 < k-1) hx) (pow_pos (high_pos k hx) (n+2)))

private lemma roots_strictAnti {k : ℕ} (hk : 2 ≤ k) (ζ : ℕ → ℝ)
    (hz : ∀ n, ζ n ∈ Ioo (0 : ℝ) 1)
    (he : ∀ n, truncated k n (ζ n) = 1) : StrictAnti ζ := by
  apply strictAnti_nat_of_succ_lt
  intro n
  apply ((truncated_strict hk (n+1)).lt_iff_lt
    ⟨(hz (n+1)).1.le,(hz (n+1)).2⟩ ⟨(hz n).1.le,(hz n).2⟩).mp
  rw [he (n+1), ← he n]
  exact truncated_succ_gt hk (hz n) n

private lemma roots_tendsto {k : ℕ} (hk : 2 ≤ k) {z : ℝ}
    (hz : z ∈ Ioo (0 : ℝ) 1) (hze : cap k z = 1)
    (ζ : ℕ → ℝ) (hζ : ∀ n, ζ n ∈ Ioo (0 : ℝ) 1)
    (hζe : ∀ n, truncated k n (ζ n) = 1) : Tendsto ζ atTop (𝓝 z) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans (root_above_cap hk hz hze n (hζ n) (hζe n))
  · intro b hb
    obtain ⟨x,hzx,hxb⟩ := exists_between (lt_min hb hz.2)
    have hx : x ∈ Ioo (0 : ℝ) 1 := ⟨hz.1.trans hzx, hxb.trans_le (min_le_right _ _)⟩
    have hcap : 1 < cap k x := by
      rw [← hze]
      exact cap_strict (by omega) ⟨hz.1.le,hz.2⟩ ⟨hx.1.le,hx.2⟩ hzx
    have hcross : 1 < cap (k-1) x + high k x := by
      rw [← cap_successor (by omega : 1 ≤ k)]
      exact hcap
    have hc := geometric_crossing (cap (k-1) x) (high k x)
      (cap_pos (by omega) hx) (high_pos k hx).le hcross
    have hc' : ∀ᶠ n : ℕ in atTop, 1 < truncated k n x := by
      exact (tendsto_add_atTop_nat 2).eventually hc
    filter_upwards [hc'] with n hn
    have hroot : ζ n < x := by
      apply ((truncated_strict hk n).lt_iff_lt
        ⟨(hζ n).1.le,(hζ n).2⟩ ⟨hx.1.le,hx.2⟩).mp
      rw [hζe n]
      exact hn
    exact hroot.trans (hxb.trans_le (min_le_left _ _))

noncomputable def rate (x : ℝ) : ℝ := -Real.log x / Real.log 2

private lemma rates_strictMono (ζ : ℕ → ℝ) (hp : ∀ n, 0 < ζ n) (ha : StrictAnti ζ) :
    StrictMono (fun n => rate (ζ n)) := by
  intro m n hmn
  unfold rate
  exact (div_lt_div_iff_of_pos_right (Real.log_pos (by norm_num : (1:ℝ) < 2))).mpr
    (neg_lt_neg (Real.log_lt_log (hp n) (ha hmn)))

private lemma rates_tendsto {ζ : ℕ → ℝ} {z : ℝ} (hz : 0 < z)
    (ht : Tendsto ζ atTop (𝓝 z)) :
    Tendsto (fun n => rate (ζ n)) atTop (𝓝 (rate z)) := by
  exact ((Real.continuousAt_log hz.ne').tendsto.comp ht).neg.div_const (Real.log 2)

def root_rate_property (k : ℕ) (z : ℝ) : Prop :=
  z ∈ Ioo (0 : ℝ) 1 ∧ cap k z = 1 ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, cap k x = 1 → x = z) ∧
    ∃ ζ : ℕ → ℝ,
      (∀ n, ζ n ∈ Ioo (0 : ℝ) 1 ∧ truncated k n (ζ n) = 1 ∧ z < ζ n ∧
        ∀ x ∈ Ioo (0 : ℝ) 1, truncated k n x = 1 → x = ζ n) ∧
      StrictAnti ζ ∧ Tendsto ζ atTop (𝓝 z) ∧
      StrictMono (fun n => rate (ζ n)) ∧
      Tendsto (fun n => rate (ζ n)) atTop (𝓝 (rate z))

/- A full quantified result: all roots are constructed, and no root-existence,
   positivity, monotonicity or convergence premise is left to the caller. -/
theorem root_rate_chain (k : ℕ) (hk : 2 ≤ k) :
    ∃ z, root_rate_property k z := by
  obtain ⟨z,hz,he⟩ := cap_root_exists (by omega : 0 < k)
  choose ζ hζ hζe using fun n => truncated_root_exists hk n
  refine ⟨z, ?_⟩
  unfold root_rate_property
  refine ⟨hz,he,?_,ζ,?_,?_,?_,?_,?_⟩
  · intro x hx hex
    exact cap_root_unique (by omega) hx hz hex he
  · intro n
    refine ⟨hζ n,hζe n,root_above_cap hk hz he n (hζ n) (hζe n),?_⟩
    intro x hx hex
    exact (truncated_strict hk n).injOn ⟨hx.1.le,hx.2⟩
      ⟨(hζ n).1.le,(hζ n).2⟩ (hex.trans (hζe n).symm)
  · exact roots_strictAnti hk ζ hζ hζe
  · exact roots_tendsto hk hz he ζ hζ hζe
  · exact rates_strictMono ζ (fun n => (hζ n).1) (roots_strictAnti hk ζ hζ hζe)
  · exact rates_tendsto hz.1 (roots_tendsto hk hz he ζ hζ hζe)

end D5.S1.Digit.Infinite.FiniteRunRootDescent
