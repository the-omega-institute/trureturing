/- GID: D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitOrdinarySmoothing
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/Polylogarithm/FiniteSlitOrdinarySmoothing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed-prefix Abel margins and exact ordinary binomial smoothing. -/

import D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitOrdinaryEndpoint
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Data.Nat.Choose.Sum

/-! Exact smoothing and preservation of signed prefixes under Abel margins. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set Topology
open scoped BigOperators

namespace D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitOrdinarySmoothing

/-- The original ordinary product with the inverse of `(1-X)^j`. -/
def smooth (p : PowerSeries ℝ) (j n : ℕ) : ℝ :=
  PowerSeries.coeff n ((PowerSeries.invOneSubPow ℝ j).val * p)

private theorem smooth_succ (p : PowerSeries ℝ) (j n : ℕ) :
    smooth p (j + 1) n = ∑ m ∈ Finset.range (n + 1), smooth p j m := by
  have heq : (PowerSeries.invOneSubPow ℝ (j + 1)).val * p =
      ((PowerSeries.invOneSubPow ℝ j).val * p) *
        (PowerSeries.invOneSubPow ℝ 1).val := by
    rw [PowerSeries.invOneSubPow_add, Units.val_mul]
    ring
  rw [smooth, heq, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
    PowerSeries.coeff_mk, Nat.zero_add, Nat.choose_zero_right, Nat.cast_one, mul_one]
  rfl

private theorem shifted_divergence (e : ℕ → ℝ)
    (hpos : ∀ᶠ n : ℕ in atTop, 0 ≤ e n) (hns : ¬ Summable e) :
    Tendsto (fun n ↦ ∑ i ∈ Finset.range (n + 1), e i) atTop atTop := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hpos
  have hp (n : ℕ) : 0 ≤ e (n + N) := hN _ (by omega)
  have hn : ¬ Summable (fun n ↦ e (n + N)) := by
    intro h
    exact hns ((summable_nat_add_iff N).mp h)
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg hp).mp hn
  have ht' : Tendsto (fun n ↦ ∑ i ∈ Finset.range (n + N), e i) atTop atTop := by
    have h := (tendsto_const_nhds (x := ∑ i ∈ Finset.range N, e i)).add_atTop ht
    convert h using 1
    funext n
    rw [Nat.add_comm n N, Finset.sum_range_add]
    simp only [Nat.add_comm N]
  apply (tendsto_add_atTop_iff_nat N).mp
  simpa only [Function.comp_def, Nat.add_assoc, Nat.add_comm N 1] using ht'.comp (tendsto_add_atTop_nat 1)

private theorem abel_margin (e : ℕ → ℝ) (H : ℝ → ℝ)
    (hpos : ∀ᶠ n : ℕ in atTop, 0 ≤ e n)
    (hs : ∀ r : ℝ, 0 < r → r < 1 → HasSum (fun n ↦ e n * r ^ n) (H r))
    (hm : ∃ c : ℝ, 0 < c ∧ ∀ᶠ r : ℝ in 𝓝[<] 1, c ≤ H r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      δ ≤ ∑ i ∈ Finset.range (n + 1), e i := by
  obtain ⟨c, hc, hmargin⟩ := hm
  by_cases he : Summable e
  · have hAbel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt he.hasSum.tendsto_sum_nat
    have hEq : (fun r : ℝ ↦ ∑' n, e n * r ^ n) =ᶠ[𝓝[<] 1] H := by
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
      exact (hs r hr.1 hr.2).tsum_eq
    have hcT : c ≤ ∑' n, e n := le_of_tendsto_of_tendsto tendsto_const_nhds (hAbel.congr' hEq) hmargin
    refine ⟨c / 2, by positivity, ?_⟩
    have ht := he.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    exact ((tendsto_order.mp ht).1 (c / 2) (by linarith)).mono (fun _ h ↦ h.le)
  · exact ⟨1, by norm_num, (shifted_divergence e hpos he).eventually_ge_atTop 1⟩

private theorem prefix_margin (e : ℕ → ℝ)
    (hm : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, δ ≤ e n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      δ ≤ ∑ i ∈ Finset.range (n + 1), e i := by
  obtain ⟨δ, hδ, he⟩ := hm
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  have hbound (n : ℕ) : (n : ℝ) * δ ≤ ∑ i ∈ Finset.range n, e (i + N) := by
    calc
      (n : ℝ) * δ = ∑ _i ∈ Finset.range n, δ := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ ↦ hN _ (by omega))
  have ht : Tendsto (fun n : ℕ ↦ ∑ i ∈ Finset.range n, e (i + N)) atTop atTop :=
    tendsto_atTop_mono hbound (tendsto_natCast_atTop_atTop.atTop_mul_const hδ)
  have hfull : Tendsto (fun n ↦ ∑ i ∈ Finset.range (n + 1), e i) atTop atTop := by
    have ht' : Tendsto (fun n ↦ ∑ i ∈ Finset.range (n + N), e i) atTop atTop := by
      have h := (tendsto_const_nhds (x := ∑ i ∈ Finset.range N, e i)).add_atTop ht
      convert h using 1
      funext n
      rw [Nat.add_comm n N, Finset.sum_range_add]
      simp only [Nat.add_comm N]
    apply (tendsto_add_atTop_iff_nat N).mp
    simpa only [Function.comp_def, Nat.add_assoc, Nat.add_comm N 1] using ht'.comp (tendsto_add_atTop_nat 1)
  exact ⟨1, by norm_num, hfull.eventually_ge_atTop 1⟩

/-- A positive radial margin for the first excess controls every signed prefix
and yields the exact strict binomial baseline at every fixed positive smoothing order. -/
theorem result (p : PowerSeries ℝ) (L : ℝ) (H : ℝ → ℝ)
    (hpos : ∀ᶠ n : ℕ in atTop, 0 < smooth (p - PowerSeries.C L) 1 n)
    (hs : ∀ r : ℝ, 0 < r → r < 1 →
      HasSum (fun n ↦ smooth (p - PowerSeries.C L) 1 n * r ^ n) (H r))
    (hm : ∃ c : ℝ, 0 < c ∧ ∀ᶠ r : ℝ in 𝓝[<] 1, c ≤ H r) :
    ∀ j : ℕ, 1 ≤ j → ∀ᶠ n : ℕ in atTop,
      L * (Nat.choose (n + j - 1) n : ℝ) < smooth p j n := by
  let q := p - PowerSeries.C L
  have htwo : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, δ ≤ smooth q 2 n := by
    simpa only [smooth_succ] using abel_margin (smooth q 1) H
      (hpos.mono (fun _ h ↦ h.le)) hs hm
  have hmargin (k : ℕ) : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      δ ≤ smooth q (k + 2) n := by
    induction k with
    | zero => exact htwo
    | succ k ih =>
      simpa only [smooth_succ, Nat.succ_eq_add_one, Nat.add_assoc] using
        prefix_margin (smooth q (k + 2)) ih
  have heq (j n : ℕ) (hj : 1 ≤ j) :
      smooth q j n = smooth p j n - L * (Nat.choose (n + j - 1) n : ℝ) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hj
    have hjk : j = k + 1 := by omega
    subst j
    simp only [Nat.add_comm 1 k]
    simp only [q, smooth, mul_sub, map_sub, PowerSeries.coeff_mul_C,
      PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, PowerSeries.coeff_mk]
    congr 1
    rw [mul_comm]
    congr 2
    have hn : n + (k + 1) - 1 = k + n := by omega
    rw [hn, Nat.choose_symm_add]
  intro j hj
  have hpj : ∀ᶠ n : ℕ in atTop, 0 < smooth q j n := by
    by_cases h1 : j = 1
    · simpa only [h1] using hpos
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show 2 ≤ j by omega)
      obtain ⟨δ, hδ, hd⟩ := hmargin k
      filter_upwards [hd] with n hn
      have hjk : j = k + 2 := by omega
      rw [hjk]
      exact hδ.trans_le hn
  filter_upwards [hpj] with n hn
  rw [heq j n hj] at hn
  linarith

end D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitOrdinarySmoothing
