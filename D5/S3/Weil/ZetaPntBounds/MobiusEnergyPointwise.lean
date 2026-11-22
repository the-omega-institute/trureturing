/- GID: D5/S3/Weil/ZetaPntBounds/MobiusEnergyPointwise
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaPntBounds/MobiusEnergyPointwise
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted Möbius energy bounds unweighted prefixes through local persistence and partial summation. -/

import D5.S3.Weil.ZetaPntBounds.MobiusDyadicEnergyUpper
import Mathlib.Analysis.SumIntegralComparisons

/-! Weighted reciprocal prefixes persist to the right of each integer cutoff. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence

open Finset Set MeasureTheory ArithmeticFunction
open scoped ArithmeticFunction.Moebius

private theorem weighted_prefix_change_le {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : (N : ℝ) ≤ x) :
    |mobiusPartialSum x - mobiusPartialSum (N : ℝ)| ≤ (x - N) / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hx0 : 0 ≤ x := hN0.le.trans hx
  have hfloor : N ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr hx
  have hset : Finset.Icc 1 ⌊x⌋₊ = Finset.Icc 1 N ∪ Finset.Ioc N ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hd : Disjoint (Finset.Icc 1 N) (Finset.Ioc N ⌊x⌋₊) := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    exact (Finset.mem_Ioc.mp hn').1.not_ge (Finset.mem_Icc.mp hn).2
  rw [mobiusPartialSum, mobiusPartialSum, Nat.floor_natCast, hset, Finset.sum_union hd,
    add_sub_cancel_left]
  calc
    _ ≤ ∑ n ∈ Finset.Ioc N ⌊x⌋₊, |(μ n : ℝ) / (n : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ Finset.Ioc N ⌊x⌋₊, 1 / (N : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hNn : (N : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1.le
      have hnabs : |(n : ℝ)| = n := abs_of_nonneg (by positivity)
      rw [abs_div, hnabs]
      exact div_le_div_of_nonneg_left (by norm_num) hN0 hNn |>.trans'
        (div_le_div_of_nonneg_right (by exact_mod_cast abs_moebius_le_one (n := n))
          (Nat.cast_nonneg n))
    _ = ((⌊x⌋₊ : ℝ) - N) / N := by
      rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc, Nat.cast_sub hfloor, mul_one_div]
    _ ≤ _ := div_le_div_of_nonneg_right (sub_le_sub_right (Nat.floor_le hx0) _) hN0.le

/-- A reciprocal prefix at an integer cutoff persists over a short interval to its right. -/
private theorem weighted_prefix_cubic_energy {α : ℝ}
    (hα : 0 ≤ α) (hα' : α ≤ 1)
    (henergy : IntegrableOn (fun x : ℝ => mobiusPartialSum x ^ 2 * x ^ (-α)) (Ioi 1))
    {N : ℕ} (hN : 2 ≤ N) :
    |mobiusPartialSum (N : ℝ)|^3 * (N : ℝ)^(1-α) ≤
      16 * ∫ x in Ioi (1 : ℝ), mobiusPartialSum x ^ 2 * x ^ (-α) := by
  let H := |mobiusPartialSum (N : ℝ)|
  let b := (N : ℝ) + H * (N : ℝ) / 2
  let e (x : ℝ) := mobiusPartialSum x ^ 2 * x ^ (-α)
  let c := (H/2)^2 * (N : ℝ)^(-α) / 2
  have hH : 0 ≤ H := abs_nonneg _
  have hH₁ : H ≤ 1 := by
    simpa only [H, Complex.norm_real, Real.norm_eq_abs] using norm_mobiusPartialSum_le_one (N : ℝ)
  have hN₂ : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN₀ : (0 : ℝ) < N := by linarith
  have hNb : (N : ℝ) ≤ b := by
    dsimp [b]
    linarith [mul_nonneg hH hN₀.le]
  have hsubset : Ioc (N : ℝ) b ⊆ Ioi (1 : ℝ) := by
    intro x hx
    exact (show (1 : ℝ) ≤ N by linarith).trans_lt hx.1
  have hlocal : ∀ x ∈ Ioc (N : ℝ) b, c ≤ e x := by
    intro x hx
    have hchange := weighted_prefix_change_le (by omega : 1 ≤ N) hx.1.le
    have hchange' : (x-(N : ℝ))/(N : ℝ) ≤ H/2 := by
      apply (div_le_iff₀ hN₀).2
      have hb := hx.2
      dsimp [b] at hb
      linarith
    have hvalue : H/2 ≤ |mobiusPartialSum x| := by
      have h := abs_sub_abs_le_abs_sub (mobiusPartialSum (N : ℝ)) (mobiusPartialSum x)
      rw [abs_sub_comm (mobiusPartialSum (N : ℝ)) (mobiusPartialSum x)] at h
      dsimp [H]
      linarith only [h, hchange.trans hchange']
    have hx₀ : 0 < x := hN₀.trans hx.1
    have h2 : x ≤ 2*(N : ℝ) := by
      have hb := hx.2
      dsimp [b] at hb
      nlinarith only [hb, mul_le_mul_of_nonneg_right hH₁ hN₀.le]
    have hpow : (N : ℝ)^(-α)/2 ≤ x^(-α) := by
      have h := Real.rpow_le_rpow_of_nonpos hx₀ h2 (neg_nonpos.mpr hα)
      rw [Real.mul_rpow (by norm_num) hN₀.le] at h
      rw [div_eq_inv_mul]
      refine (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hN₀.le _)).trans h
      have ht := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (show (-1 : ℝ) ≤ -α by linarith)
      simpa [Real.rpow_neg_one, one_div] using ht
    have hsq : (H/2)^2 ≤ mobiusPartialSum x ^ 2 := by
      rw [← sq_abs (mobiusPartialSum x)]
      exact pow_le_pow_left₀ (by positivity) hvalue 2
    dsimp [c, e]
    rw [mul_div_assoc]
    exact mul_le_mul hsq hpow (by positivity) (sq_nonneg _)
  have hconst : IntegrableOn (fun _ : ℝ => c) (Ioc (N : ℝ) b) :=
    integrableOn_const (by simp [Real.volume_Ioc])
  have hmono := setIntegral_mono_on hconst (henergy.mono_set hsubset) measurableSet_Ioc hlocal
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] e := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (1 : ℝ)))] with x hx
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (show 0 ≤ x by linarith [hx.out]) _)
  have htot := setIntegral_mono_set henergy hnonneg (Filter.Eventually.of_forall hsubset)
  have hcb : (∫ x in Ioc (N : ℝ) b, c) = H^3 * (N : ℝ)^(1-α)/16 := by
    rw [setIntegral_const, Real.volume_real_Ioc_of_le hNb, smul_eq_mul]
    dsimp [b, c]
    rw [Real.rpow_sub hN₀, Real.rpow_one, Real.rpow_neg hN₀.le, div_eq_mul_inv]
    ring
  have hh : H^3 * (N : ℝ)^(1-α)/16 ≤ ∫ x in Ioi (1 : ℝ), e x := by
    rw [← hcb]
    exact hmono.trans htot
  exact ((div_le_iff₀ (by norm_num : (0 : ℝ) < 16)).mp hh).trans_eq (by ring)

private theorem weighted_prefix_decay_of_energy {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1)
    (henergy : IntegrableOn (fun x : ℝ => mobiusPartialSum x ^ 2 * x ^ (-α)) (Ioi 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      |mobiusPartialSum (N : ℝ)| ≤ C * (N : ℝ)^(-(1-α)/3) := by
  let E := ∫ x in Ioi (1 : ℝ), mobiusPartialSum x ^ 2 * x ^ (-α)
  let δ := (1-α)/3
  let C := (16*|E|+1)^(1/3 : ℝ)
  have hC₁ : 1 ≤ C := Real.one_le_rpow (by linarith [abs_nonneg E]) (by norm_num)
  have hC : 0 < C := zero_lt_one.trans_le hC₁
  refine ⟨C, hC, ?_⟩
  intro N hN
  by_cases hn : N = 1
  · subst N
    simpa only [Nat.cast_one, Real.one_rpow, mul_one] using
      (by simpa only [Complex.norm_real, Real.norm_eq_abs] using norm_mobiusPartialSum_le_one 1 :
        |mobiusPartialSum 1| ≤ 1).trans hC₁
  have hN₂ : 2 ≤ N := by omega
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp : 0 < (N : ℝ)^δ := Real.rpow_pos_of_pos hN₀ _
  have h := weighted_prefix_cubic_energy hα hα'.le henergy hN₂
  have hpow : ((N : ℝ)^δ)^3 = (N : ℝ)^(1-α) := by
    rw [← Real.rpow_mul_natCast hN₀.le]
    congr 1
    dsimp [δ]
    norm_num
  have hCp : C^3 = 16*|E|+1 := by
    dsimp [C]
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ 16*|E|+1)]
    norm_num
  have hcub : (|mobiusPartialSum (N : ℝ)| * (N : ℝ)^δ)^3 ≤ C^3 := by
    rw [mul_pow, hpow, hCp]
    have hE := le_abs_self E
    linarith only [h, hE]
  have hbound : |mobiusPartialSum (N : ℝ)| * (N : ℝ)^δ ≤ C :=
    le_of_not_gt fun hh =>
      (not_lt_of_ge hcub) (pow_lt_pow_left₀ hh hC.le (by norm_num : (3 : ℕ) ≠ 0))
  rw [show -(1-α)/3 = -δ by dsimp [δ]; ring, Real.rpow_neg hN₀.le, ← div_eq_mul_inv]
  exact (le_div_iff₀ hp).2 hbound

private theorem unweighted_prefix_eq {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, (μ n : ℝ)) =
      (N : ℝ) * mobiusPartialSum (N : ℝ) -
        ∑ n ∈ Finset.range (N-1), mobiusPartialSum ((n+1 : ℕ) : ℝ) := by
  let g (i : ℕ) := (μ (i+1) : ℝ)/((i+1 : ℕ) : ℝ)
  have hsum (k : ℕ) :
      (∑ i ∈ Finset.range k, g i) = mobiusPartialSum (k : ℝ) := by
    rw [mobiusPartialSum, Nat.floor_natCast]
    apply Finset.sum_bij (fun i _ => i+1)
    · intro i hi
      simp only [Finset.mem_Icc, Finset.mem_range] at *
      omega
    · intro i hi j hj hij
      omega
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      refine ⟨n-1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro i hi
      rfl
  have hsum' :
      (∑ i ∈ Finset.range N, (μ (i+1) : ℝ)) =
        ∑ n ∈ Finset.Icc 1 N, (μ n : ℝ) := by
    apply Finset.sum_bij (fun i _ => i+1)
    · intro i hi
      simp only [Finset.mem_Icc, Finset.mem_range] at *
      omega
    · intro i hi j hj hij
      omega
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      refine ⟨n-1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro i hi
      rfl
  have hparts := Finset.sum_range_by_parts (fun i => ((i+1 : ℕ) : ℝ)) g N
  simp only [smul_eq_mul, hsum, Nat.sub_add_cancel hN] at hparts
  have he (i : ℕ) : (((i+1 : ℕ) : ℝ)) * g i = (μ (i+1) : ℝ) := by
    dsimp [g]
    field_simp [show (((i+1 : ℕ) : ℝ)) ≠ 0 by positivity]
  have hone (i : ℕ) : (((i+1+1 : ℕ) : ℝ) - ((i+1 : ℕ) : ℝ)) = 1 := by
    push_cast
    ring
  simpa only [he, hsum', hone, one_mul] using hparts

private theorem prefix_power_sum_le {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ < 1)
    {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.range (N-1), (((n+1 : ℕ) : ℝ))^(-δ)) ≤
      (1+(1-δ)⁻¹) * (N : ℝ)^(1-δ) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : 0 < 1-δ := sub_pos.mpr hδ'
  have hpow : 1 ≤ (N : ℝ)^(1-δ) := Real.one_le_rpow hN' hpos.le
  rcases Nat.eq_zero_or_pos (N-1) with hzero | hsucc
  · rw [hzero]
    simpa using (show 0 ≤ (1+(1-δ)⁻¹) * (N : ℝ)^(1-δ) by positivity)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hsucc.ne'
  have hm : (1+(k : ℝ)) ≤ (N : ℝ) := by
    have h : k+1 ≤ N := by omega
    exact_mod_cast (show 1+k ≤ N by omega)
  let f (x : ℝ) := x^(-δ)
  have hanti : AntitoneOn f (Icc (1 : ℝ) (1+(k : ℝ))) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx.1) hxy (neg_nonpos.mpr hδ)
  have hsum := hanti.sum_le_integral (a := k)
  have hInt : (∫ x in (1 : ℝ)..1+(k : ℝ), f x) ≤ (N : ℝ)^(1-δ)/(1-δ) := by
    change (∫ x in (1 : ℝ)..1+(k : ℝ), x^(-δ)) ≤ _
    rw [integral_rpow (Or.inl (by linarith))]
    rw [show -δ+1=1-δ by ring, Real.one_rpow]
    apply div_le_div_of_nonneg_right _ hpos.le
    exact (sub_le_self _ zero_le_one).trans
      (Real.rpow_le_rpow (by positivity) hm hpos.le)
  rw [hk, Finset.sum_range_succ']
  simp only [zero_add, Nat.cast_one]
  change (∑ n ∈ Finset.range k, f (((n+1+1 : ℕ) : ℝ))) + (1 : ℝ)^(-δ) ≤ _
  simp only [Nat.cast_add, Nat.cast_one, Real.one_rpow] at *
  have hsum' : (∑ n ∈ Finset.range k, f ((n : ℝ)+1+1)) ≤ (N : ℝ)^(1-δ)/(1-δ) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_comm (1 : ℝ)] using hsum.trans hInt
  calc
    _ ≤ (N : ℝ)^(1-δ)/(1-δ)+1 := add_le_add hsum' le_rfl
    _ ≤ _ := by
      rw [add_mul, one_mul, div_eq_inv_mul]
      linarith only [hpow]

/-- A zero-free half-plane gives an ordinary Möbius prefix bound through the weighted energy. -/
theorem unweighted_mobius_prefix_power_bound {θ α : ℝ}
    (hθ_half : 1/2 ≤ θ) (hθ_lt_one : θ < 1)
    (hzero : ∀ z : ℂ, θ < z.re → z ≠ 1 → riemannZeta z ≠ 0)
    (hα_lo : 2*θ-1 < α) (hα_hi : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, (μ n : ℝ)| ≤ C * (N : ℝ)^((2+α)/3) := by
  have hα : 0 ≤ α := by linarith
  let δ := (1-α)/3
  have hδ : 0 ≤ δ := by dsimp [δ]; linarith
  have hδ' : δ < 1 := by dsimp [δ]; linarith
  have hD : 0 < 1-δ := sub_pos.mpr hδ'
  have henergy := mobiusPartialSum_weightedEnergy_integrable_of_zero_free
    hθ_half hθ_lt_one hzero hα_lo hα_hi
  obtain ⟨C, hC, hbound⟩ := weighted_prefix_decay_of_energy hα hα_hi henergy
  refine ⟨C*(2+(1-δ)⁻¹), by positivity, fun N hN => ?_⟩
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [unweighted_prefix_eq hN]
  have hmain : |(N : ℝ)*mobiusPartialSum (N : ℝ)| ≤ C * (N : ℝ)^(1-δ) := by
    rw [abs_mul, abs_of_pos hN₀]
    have hb : |mobiusPartialSum (N : ℝ)| ≤ C * (N : ℝ)^(-δ) := by
      simpa only [show -(1-α)/3 = -δ by dsimp [δ]; ring] using hbound N hN
    refine (mul_le_mul_of_nonneg_left hb hN₀.le).trans_eq ?_
    have hprod : (N : ℝ) * (N : ℝ)^(-δ) = (N : ℝ)^(1-δ) := by
      rw [show 1-δ = 1+(-δ) by ring, Real.rpow_add hN₀, Real.rpow_one]
    rw [show (N : ℝ)*(C*(N : ℝ)^(-δ)) = C * ((N : ℝ)*(N : ℝ)^(-δ)) by ring, hprod]
  have hsum : |∑ n ∈ Finset.range (N-1), mobiusPartialSum ((n+1 : ℕ) : ℝ)| ≤
      C * ((1+(1-δ)⁻¹) * (N : ℝ)^(1-δ)) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ n ∈ Finset.range (N-1), C * (((n+1 : ℕ) : ℝ))^(-δ) := by
        apply Finset.sum_le_sum
        intro n _
        simpa only [show -(1-α)/3 = -δ by dsimp [δ]; ring] using
          hbound (n+1) (by omega)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (prefix_power_sum_le hδ hδ' hN) hC.le
  refine ((abs_sub _ _).trans (add_le_add hmain hsum)).trans_eq ?_
  rw [show (2+α)/3 = 1-δ by dsimp [δ]; ring]
  ring

end D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence
