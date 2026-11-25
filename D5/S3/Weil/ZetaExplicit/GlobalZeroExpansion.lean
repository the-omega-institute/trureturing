/- GID: D5/S3/Weil/ZetaExplicit/GlobalZeroExpansion
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaExplicit/GlobalZeroExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scaling and dyadic zero counts give a centered logarithmic derivative expansion. -/

import D5.S3.Weil.ZetaExplicit.CenteredDiskLogDeriv
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Centered logarithmic derivatives and quadratic summability of the actual zeros. -/

noncomputable section

namespace Zeta23.WeilEF

open Filter Metric Set Topology Asymptotics

/-- For the original entire function, the centered logarithmic derivative has a quadratic
radius denominator and uses every zero in the closed cutoff disk with its analytic multiplicity. -/
theorem logDeriv_partial_fraction_disk_centered {f : ℂ → ℂ} {R B : ℝ}
    (hR : 0 < R) (hfa : ∀ z : ℂ, AnalyticAt ℂ f z) (hf0 : f 0 ≠ 0)
    (hB2 : 2 ≤ B) (hfB : ∀ w : ℂ, ‖w‖ ≤ 24 / 25 * R → ‖f w‖ ≤ B * ‖f 0‖) :
    ∃ Z : Finset ℂ, (↑Z : Set ℂ) = SetOfZeros (22 / 25 * R) f ∧
      ∀ s : ℂ, ‖s‖ ≤ R / 4 → f s ≠ 0 →
        ‖(logDeriv f s - logDeriv f 0) -
          ((∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)) -
            ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (0 - ρ))‖ ≤
          179180000 * ‖s‖ * Real.log B / R ^ 2 := by
  classical
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  let φ : ℂ → ℂ := fun w => (R : ℂ) * w
  let c : ℂ := (f 0)⁻¹
  let g : ℂ → ℂ := fun w => c * f (φ w)
  have hcne : c ≠ 0 := inv_ne_zero hf0
  have hφa (w : ℂ) : AnalyticAt ℂ φ w := analyticAt_const.mul analyticAt_id
  have hφd (w : ℂ) : deriv φ w = (R : ℂ) := by simp [φ]
  have hφinj : Function.Injective φ := fun _ _ h => mul_left_cancel₀ hRC h
  have hφdiv (s : ℂ) : φ (s / (R : ℂ)) = s := mul_div_cancel₀ s hRC
  have hφnorm (w : ℂ) : ‖φ w‖ = R * ‖w‖ := by
    simp only [φ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hgzero (w : ℂ) : g w = 0 ↔ f (φ w) = 0 := mul_eq_zero_iff_left hcne
  have hga : AnalyticOnNhd ℂ g (closedBall 0 1) :=
    fun w _ => analyticAt_const.mul ((hfa (φ w)).comp (hφa w))
  have hg0 : g 0 = 1 := by simpa only [g, c, φ, mul_zero] using inv_mul_cancel₀ hf0
  have hgB (w : ℂ) (hw : ‖w‖ ≤ 24 / 25) : ‖g w‖ ≤ B := by
    rw [show g w = (f 0)⁻¹ * f (φ w) by rfl, norm_mul, norm_inv,
      inv_mul_le_iff₀ (norm_pos_iff.mpr hf0), mul_comm ‖f 0‖ B]
    apply hfB
    rw [hφnorm, mul_comm R]
    exact mul_le_mul_of_nonneg_right hw hR.le
  obtain ⟨Zg, hZg, hunit⟩ := logDeriv_partial_fraction_unit_centered hga hg0 hB2 hgB
  have hZgmem (w : ℂ) : w ∈ Zg ↔ ‖w‖ ≤ 22 / 25 ∧ f (φ w) = 0 := by
    rw [← Finset.mem_coe, hZg]
    change (‖w‖ ≤ 22 / 25 ∧ g w = 0) ↔ _
    rw [hgzero]
  have hord (w : ℂ) : analyticOrderNatAt g w = analyticOrderNatAt f (φ w) := by
    have hcomp : analyticOrderAt (f ∘ φ) w = analyticOrderAt f (φ w) :=
      analyticOrderAt_comp_of_deriv_ne_zero (hφa w) (by rw [hφd]; exact hRC)
    have hsmul : analyticOrderAt g w = analyticOrderAt (f ∘ φ) w := by
      have heq : g = (fun _ : ℂ => c) • (f ∘ φ) := by
        funext z
        simp [g, smul_eq_mul]
      rw [heq, analyticOrderAt_smul analyticAt_const ((hfa (φ w)).comp (hφa w)),
        (analyticAt_const (v := c)).analyticOrderAt_eq_zero.mpr hcne, zero_add]
    rw [analyticOrderNatAt, analyticOrderNatAt, hsmul, hcomp]
  refine ⟨Zg.image φ, ?_, ?_⟩
  · ext ρ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, SetOfZeros, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨hwn, hwz⟩ := (hZgmem w).mp hw
      rw [hφnorm, mul_comm R]
      exact ⟨mul_le_mul_of_nonneg_right hwn hR.le, hwz⟩
    · rintro ⟨hρ, hρz⟩
      refine ⟨ρ / (R : ℂ), (hZgmem _).mpr ⟨?_, ?_⟩, hφdiv ρ⟩
      · rwa [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_le_iff₀ hR]
      · simpa only [hφdiv] using hρz
  · intro s hs hfs
    have hwn : ‖s / (R : ℂ)‖ ≤ 1 / 4 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_le_iff₀ hR]
      linarith
    have hgw : g (s / (R : ℂ)) ≠ 0 := by simpa only [ne_eq, hgzero, hφdiv] using hfs
    have hld (t : ℂ) : logDeriv g (t / (R : ℂ)) = (R : ℂ) * logDeriv f t := by
      have hstep : logDeriv g (t / (R : ℂ)) = logDeriv (f ∘ φ) (t / (R : ℂ)) :=
        logDeriv_const_mul (t / (R : ℂ)) c hcne
      have hdf : DifferentiableAt ℂ f (φ (t / (R : ℂ))) := (hfa _).differentiableAt
      rw [hstep, logDeriv_comp hdf (hφa _).differentiableAt, hφdiv, hφd, mul_comm]
    have hsum (t : ℂ) : ∑ ρ ∈ Zg.image φ, (analyticOrderNatAt f ρ : ℂ) / (t - ρ) =
        (R : ℂ)⁻¹ * ∑ w ∈ Zg, (analyticOrderNatAt g w : ℂ) / (t / (R : ℂ) - w) := by
      rw [Finset.sum_image (fun a _ b _ hab => hφinj hab), Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      have hsub : t - φ w = (R : ℂ) * (t / (R : ℂ) - w) := by
        rw [mul_sub]
        change t - φ w = φ (t / (R : ℂ)) - φ w
        rw [hφdiv]
      rw [hord, hsub, div_mul_eq_div_div_swap, div_eq_inv_mul]
    have hinv (t : ℂ) : logDeriv f t = (R : ℂ)⁻¹ * logDeriv g (t / (R : ℂ)) := by
      rw [hld, ← mul_assoc, inv_mul_cancel₀ hRC, one_mul]
    have h := hunit (s / (R : ℂ)) hwn hgw
    simp only [hinv s, hinv 0, hsum s, hsum 0, zero_div, ← mul_sub,
      norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    calc
      _ ≤ R⁻¹ * (179180000 * ‖s / (R : ℂ)‖ * Real.log B) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hR.le)
      _ = 179180000 * ‖s‖ * Real.log B / R ^ 2 := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
        field_simp [hR.ne']

private theorem finite_centered_zeros {f : ℂ → ℂ} {B : ℝ → ℝ}
    (hfa : ∀ z : ℂ, AnalyticAt ℂ f z) (hf0 : f 0 ≠ 0)
    (hB : ∀ᶠ R in atTop, 2 ≤ B R ∧
      ∀ w : ℂ, ‖w‖ ≤ 24 / 25 * R → ‖f w‖ ≤ B R * ‖f 0‖)
    (r : ℝ) : (SetOfZeros r f).Finite := by
  obtain ⟨R, hR, ⟨hB2, hfB⟩, hr⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and
      (hB.and (eventually_ge_atTop (r / (22 / 25))))).exists
  obtain ⟨Z, hZ, _⟩ := logDeriv_partial_fraction_disk_centered hR hfa hf0 hB2 hfB
  refine Z.finite_toSet.subset ?_
  rw [hZ]
  intro ρ hρ
  have hr' : r ≤ 22 / 25 * R := by
    have := (div_le_iff₀ (by norm_num : (0 : ℝ) < 22 / 25)).mp hr
    linarith
  exact ⟨hρ.1.trans hr', hρ.2⟩

/-- The centered expansion over the subtype of all actual zeros. The growth hypothesis sends the
disk remainder to zero. The reciprocal-square input gives absolute convergence and uses the
analytic multiplicity at each zero.
-/
theorem logDeriv_global_zero_expansion {f : ℂ → ℂ} {B : ℝ → ℝ}
    (hfa : ∀ z : ℂ, AnalyticAt ℂ f z) (hf0 : f 0 ≠ 0)
    (hB : ∀ᶠ R in atTop, 2 ≤ B R ∧
      ∀ w : ℂ, ‖w‖ ≤ 24 / 25 * R → ‖f w‖ ≤ B R * ‖f 0‖)
    (hgrowth : (fun R : ℝ => Real.log (B R)) =o[atTop] (fun R : ℝ => R ^ 2))
    (hweight : Summable (fun ρ : {ρ : ℂ // f ρ = 0} =>
      (analyticOrderNatAt f (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2))
    (s : ℂ) (hfs : f s ≠ 0) :
    let k : ℂ → ℂ := fun ρ => (analyticOrderNatAt f ρ : ℂ) * ((s - ρ)⁻¹ + ρ⁻¹)
    Summable (fun ρ : {ρ : ℂ // f ρ = 0} => ‖k ρ‖) ∧
      logDeriv f s - logDeriv f 0 = ∑' ρ : {ρ : ℂ // f ρ = 0}, k ρ := by
  classical
  let k : ℂ → ℂ := fun ρ => (analyticOrderNatAt f ρ : ℂ) * ((s - ρ)⁻¹ + ρ⁻¹)
  change Summable (fun ρ : {ρ : ℂ // f ρ = 0} => ‖k ρ‖) ∧
    logDeriv f s - logDeriv f 0 = ∑' ρ : {ρ : ℂ // f ρ = 0}, k ρ
  have hfinite := finite_centered_zeros hfa hf0 hB
  have hcofinite : ∀ᶠ ρ : {ρ : ℂ // f ρ = 0} in cofinite, 2 * ‖s‖ < ‖(ρ : ℂ)‖ := by
    rw [Filter.eventually_cofinite]
    refine (Set.Finite.preimage Subtype.val_injective.injOn (hfinite (2 * ‖s‖))).subset ?_
    intro ρ hρ
    exact ⟨le_of_not_gt hρ, ρ.property⟩
  have hknorm : Summable (fun ρ : {ρ : ℂ // f ρ = 0} => ‖k ρ‖) := by
    apply (hweight.mul_left (2 * ‖s‖)).of_norm_bounded_eventually
    filter_upwards [hcofinite] with ρ hρlarge
    have hρ0 : (ρ : ℂ) ≠ 0 := by
      intro he
      exact hf0 (by simpa only [he] using ρ.property)
    have hsρ : s - (ρ : ℂ) ≠ 0 := by
      intro he
      exact hfs (by simpa only [(sub_eq_zero.mp he).symm] using ρ.property)
    have hrewrite : (s - (ρ : ℂ))⁻¹ + (ρ : ℂ)⁻¹ = s / ((s - (ρ : ℂ)) * (ρ : ℂ)) := by
      field_simp [hρ0, hsρ]
      ring
    have htriangle : ‖(ρ : ℂ)‖ ≤ ‖s‖ + ‖s - (ρ : ℂ)‖ := by
      simpa only [sub_sub_cancel] using (norm_sub_le s (s - (ρ : ℂ)))
    have hhalf : ‖(ρ : ℂ)‖ / 2 ≤ ‖s - (ρ : ℂ)‖ := by linarith
    have hρpos : 0 < ‖(ρ : ℂ)‖ := norm_pos_iff.mpr hρ0
    have hden : ‖(ρ : ℂ)‖ ^ 2 / 2 ≤ ‖s - (ρ : ℂ)‖ * ‖(ρ : ℂ)‖ := by
      simpa only [pow_two, div_mul_eq_mul_div] using mul_le_mul_of_nonneg_right hhalf hρpos.le
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    simp only [k, hrewrite, norm_mul, Complex.norm_natCast, norm_div]
    calc
      _ ≤ (analyticOrderNatAt f (ρ : ℂ) : ℝ) * (‖s‖ / (‖(ρ : ℂ)‖ ^ 2 / 2)) := by
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hden) (Nat.cast_nonneg _)
      _ = _ := by field_simp [hρpos.ne']
  refine ⟨hknorm, ?_⟩
  let Z (R : ℝ) : Finset ℂ := (hfinite (22 / 25 * R)).toFinset
  let Z₀ (R : ℝ) : Finset {ρ : ℂ // f ρ = 0} := (Z R).subtype (fun ρ : ℂ => f ρ = 0)
  have hZmem (R : ℝ) (ρ : ℂ) : ρ ∈ Z R ↔ ‖ρ‖ ≤ 22 / 25 * R ∧ f ρ = 0 := by
    change ρ ∈ (hfinite (22 / 25 * R)).toFinset ↔ ρ ∈ SetOfZeros (22 / 25 * R) f
    exact (hfinite (22 / 25 * R)).mem_toFinset
  have hZtend : Tendsto Z₀ atTop atTop := by
    refine tendsto_atTop.2 fun S => ?_
    let M : ℝ := ∑ ρ ∈ S, ‖(ρ : ℂ)‖
    filter_upwards [eventually_ge_atTop (M / (22 / 25))] with R hR
    intro ρ hρ
    change ρ ∈ (Z R).subtype (fun ρ : ℂ => f ρ = 0)
    rw [Finset.mem_subtype, hZmem]
    have hρM : ‖(ρ : ℂ)‖ ≤ M := Finset.single_le_sum (fun _ _ => norm_nonneg _) hρ
    have hM := (div_le_iff₀ (by norm_num : (0 : ℝ) < 22 / 25)).mp hR
    exact ⟨hρM.trans (by simpa only [mul_comm R] using hM), ρ.property⟩
  have htrunc : Tendsto (fun R : ℝ => ∑ ρ ∈ Z R, k ρ) atTop
      (𝓝 (∑' ρ : {ρ : ℂ // f ρ = 0}, k ρ)) := by
    have hsum : HasSum (fun ρ : {ρ : ℂ // f ρ = 0} => k ρ)
        (∑' ρ : {ρ : ℂ // f ρ = 0}, k ρ) := hknorm.of_norm.hasSum
    have ht : Tendsto (fun S : Finset {ρ : ℂ // f ρ = 0} => ∑ ρ ∈ S, k ρ)
        atTop (𝓝 (∑' ρ : {ρ : ℂ // f ρ = 0}, k ρ)) := hsum
    refine (ht.comp hZtend).congr fun R => ?_
    change (∑ ρ ∈ (Z R).subtype (fun ρ : ℂ => f ρ = 0), k ρ) = ∑ ρ ∈ Z R, k ρ
    rw [Finset.sum_subtype_eq_sum_filter]
    rw [Finset.filter_true_of_mem (fun ρ hρ => ((hZmem R ρ).mp hρ).2)]
  have herror : ∀ᶠ R : ℝ in atTop,
      ‖(logDeriv f s - logDeriv f 0) - ∑ ρ ∈ Z R, k ρ‖ ≤
        179180000 * ‖s‖ * Real.log (B R) / R ^ 2 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hB,
      eventually_ge_atTop (4 * ‖s‖)] with R hR hBR hsR
    obtain ⟨T, hT, hbound⟩ :=
      logDeriv_partial_fraction_disk_centered hR hfa hf0 hBR.1 hBR.2
    have heq : T = Z R := by
      apply Finset.coe_injective
      exact hT.trans (hfinite (22 / 25 * R)).coe_toFinset.symm
    subst T
    simpa only [← Finset.sum_sub_distrib, k, zero_sub, div_neg, inv_neg, mul_neg,
      sub_neg_eq_add, div_eq_mul_inv, mul_add] using hbound s (by linarith) hfs
  have hrem : Tendsto (fun R : ℝ => (logDeriv f s - logDeriv f 0) - ∑ ρ ∈ Z R, k ρ)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' herror
    simpa only [mul_zero, mul_div_assoc] using
      hgrowth.tendsto_div_nhds_zero.const_mul (179180000 * ‖s‖)
  have hconst : Tendsto (fun _ : ℝ => logDeriv f s - logDeriv f 0) atTop
      (𝓝 (∑' ρ : {ρ : ℂ // f ρ = 0}, k ρ)) := by
    simpa only [sub_add_cancel, zero_add] using hrem.add htrunc
  exact tendsto_nhds_unique tendsto_const_nhds hconst

-- The partition argument follows `heightShell_partition` in `RightStripInverseHeight.lean`.
private def zeroShell (f : ℂ → ℂ) : ℕ → Set {ρ : ℂ // f ρ = 0}
  | 0 => {ρ | ‖(ρ : ℂ)‖ ≤ 2}
  | n + 1 => {ρ | (2 : ℝ) ^ (n + 1) < ‖(ρ : ℂ)‖ ∧ ‖(ρ : ℂ)‖ ≤ (2 : ℝ) ^ (n + 2)}

private theorem zeroShell_upper {f : ℂ → ℂ} {n : ℕ} {ρ : {ρ : ℂ // f ρ = 0}}
    (hρ : ρ ∈ zeroShell f n) : ‖(ρ : ℂ)‖ ≤ (2 : ℝ) ^ (n + 1) := by
  cases n with
  | zero => simpa [zeroShell] using hρ
  | succ _ => exact hρ.2

private theorem zeroShell_partition (f : ℂ → ℂ) (ρ : {ρ : ℂ // f ρ = 0}) :
    ∃! n, ρ ∈ zeroShell f n := by
  classical
  have hex : ∃ n : ℕ, ‖(ρ : ℂ)‖ ≤ (2 : ℝ) ^ (n + 1) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖(ρ : ℂ)‖ (show (1 : ℝ) < 2 by norm_num)
    exact ⟨n, hn.le.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n))⟩
  refine ⟨Nat.find hex, ?_, fun n hn => ?_⟩
  · have hu := Nat.find_spec hex
    cases hk : Nat.find hex with
    | zero => simpa [zeroShell, hk] using hu
    | succ k =>
      rw [hk] at hu
      have hmin := Nat.find_min hex (show k < Nat.find hex by rw [hk]; exact Nat.lt_succ_self k)
      exact ⟨lt_of_not_ge hmin, hu⟩
  · apply le_antisymm _ (Nat.find_min' hex (zeroShell_upper hn))
    by_contra! hlt
    cases n with
    | zero => omega
    | succ n =>
      have hs : Nat.find hex + 1 ≤ n + 1 := hlt
      exact hn.1.not_ge ((Nat.find_spec hex).trans (pow_le_pow_right₀ (by norm_num) hs))

/-- A summable dyadic growth envelope gives reciprocal-square summability with the actual zero
multiplicities. For the beta growth `O(R log (2 + R))`, the dyadic terms are `O((n + 1) / 2 ^ n)`.
-/
theorem summable_zero_multiplicity_div_norm_sq {f : ℂ → ℂ} {B : ℝ → ℝ}
    (hfa : ∀ z : ℂ, AnalyticAt ℂ f z) (hf0 : f 0 ≠ 0)
    (hB : ∀ᶠ R in atTop, 2 ≤ B R ∧
      ∀ w : ℂ, ‖w‖ ≤ 24 / 25 * R → ‖f w‖ ≤ B R * ‖f 0‖)
    (hdyadic : Summable (fun n : ℕ =>
      Real.log (B ((2 : ℝ) ^ (n + 2) / (22 / 25))) / ((2 : ℝ) ^ (n + 1)) ^ 2)) :
    Summable (fun ρ : {ρ : ℂ // f ρ = 0} =>
      (analyticOrderNatAt f (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2) := by
  classical
  let weight : {ρ : ℂ // f ρ = 0} → ℝ := fun ρ =>
    (analyticOrderNatAt f (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2
  have hweight : 0 ≤ weight := fun ρ => div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  change Summable weight
  rw [summable_partition hweight (zeroShell_partition f)]
  have hfinite := finite_centered_zeros hfa hf0 hB
  have hshell (n : ℕ) : (zeroShell f n).Finite := by
    refine ((hfinite ((2 : ℝ) ^ (n + 1))).preimage Subtype.val_injective.injOn).subset ?_
    intro ρ hρ
    exact ⟨zeroShell_upper hρ, ρ.property⟩
  constructor
  · intro n
    let _ : Fintype (zeroShell f n) := (hshell n).fintype
    exact Summable.of_finite
  · apply (summable_nat_add_iff 1).mp
    let C : ℝ := 1 / Real.log ((24 / 25) / (22 / 25))
    let R (n : ℕ) : ℝ := (2 : ℝ) ^ (n + 2) / (22 / 25)
    have hRtend : Tendsto R atTop atTop := by
      have ht := (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)).comp
        (tendsto_add_atTop_nat 2)
      exact ht.atTop_div_const (by norm_num : (0 : ℝ) < 22 / 25)
    apply (hdyadic.mul_left C).of_norm_bounded_eventually_nat
    filter_upwards [hRtend.eventually hB] with n hBR
    have hRn : 0 < R n := by dsimp [R]; positivity
    have hfaR : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) (R n)) := fun z _ => hfa z
    obtain ⟨Z, hZ, hcount, _⟩ := logDeriv_partial_fraction_disk (s₀ := 0) hRn hfaR hf0 hBR.1
      (fun w hw => hBR.2 w (mem_closedBall_zero_iff.mp hw))
    let e : zeroShell f (n + 1) ↪ ℂ :=
      ⟨fun ρ => ρ.val.val, Subtype.val_injective.comp Subtype.val_injective⟩
    let _ : Fintype (zeroShell f (n + 1)) := (hshell (n + 1)).fintype
    have hZmem (ρ : zeroShell f (n + 1)) : e ρ ∈ Z := by
      rw [← Finset.mem_coe, hZ, Set.mem_ofPred_eq, mem_closedBall_zero_iff]
      refine ⟨?_, ρ.val.property⟩
      rw [show 22 / 25 * R n = (2 : ℝ) ^ (n + 2) by dsimp [R]; ring]
      exact zeroShell_upper ρ.property
    have hsum : (∑ ρ : zeroShell f (n + 1), (analyticOrderNatAt f (e ρ) : ℝ)) ≤
        ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ) := by
      rw [← Finset.sum_map Finset.univ e (fun ρ : ℂ => (analyticOrderNatAt f ρ : ℝ))]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ρ hρ
        obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hρ
        exact hZmem p
      · exact fun _ _ _ => Nat.cast_nonneg _
    let L : ℝ := (2 : ℝ) ^ (n + 1)
    have hL : 0 < L := by dsimp [L]; positivity
    rw [Real.norm_eq_abs,
      abs_of_nonneg (tsum_nonneg fun ρ : zeroShell f (n + 1) => hweight ρ.val)]
    calc
      (∑' ρ : zeroShell f (n + 1), weight ρ.val) =
          ∑ ρ : zeroShell f (n + 1), weight ρ.val :=
        tsum_fintype (fun ρ : zeroShell f (n + 1) => weight ρ.val)
      _ ≤
          ∑ ρ : zeroShell f (n + 1), (analyticOrderNatAt f (e ρ) : ℝ) / L ^ 2 := by
        apply Finset.sum_le_sum
        intro ρ _
        have hlow : L < ‖e ρ‖ := ρ.property.1
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (sq_pos_of_pos hL)
          (pow_le_pow_left₀ hL.le hlow.le 2)
      _ = (∑ ρ : zeroShell f (n + 1), (analyticOrderNatAt f (e ρ) : ℝ)) / L ^ 2 := by
        rw [Finset.sum_div]
      _ ≤ C * Real.log (B (R n)) / L ^ 2 :=
        div_le_div_of_nonneg_right (hsum.trans hcount) (sq_nonneg _)
      _ = _ := by dsimp [L, R]; rw [mul_div_assoc]

end Zeta23.WeilEF
