/- GID: D5/S3/CharacterSums/DirichletFiniteZeroFree
   generality: G
   mirror-B: D5/B/S3/CharacterSums/DirichletFiniteZeroFree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite arithmetic moments exclude actual primitive Dirichlet L-function zeros. -/

import D5.S3.CharacterSums.DirichletZeroBounds
import D5.S3.CharacterSums.DirichletZeroPowerSums
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.NumberTheory.WellApproximable
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic


/-! # Finite arithmetic moment exclusion for actual Dirichlet L-functions

All zeros are repeated according to their analytic order, including the parity lattice.
One arithmetic cutoff suffices for every order and every grid point.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators Topology
open Complex Set Filter Real MeasureTheory
namespace D5.S3.CharacterSums.DirichletFiniteZeroFree
open D5.S3.CharacterSums.DirichletZeroBounds
open D5.S3.CharacterSums.DirichletZeroPowerSums

private theorem power_real_part (z : ℂ) (n : ℕ) :
    (z ^ n).re = ‖z‖ ^ n * Real.cos (n * z.arg) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
  rw [mul_pow, ← Complex.exp_nat_mul]
  have he : (n : ℂ) * ((z.arg : ℂ) * I) = ((n * z.arg : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [he]
  rw [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]

/-- A bounded common exponent is a direct application of Dirichlet approximation
on the finite product of unit circles. Zero entries and zero initial exponent are allowed. -/
private theorem simultaneous_positive_powers {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (M : ℕ) :
    ∃ u : ℕ, 1 ≤ u ∧ u ≤ 6 ^ Fintype.card ι ∧
      ∀ j, (1 / 2 : ℝ) * ‖z j‖ ^ (M * u) ≤ (z j ^ (M * u)).re := by
  classical
  let θ : ι → ℝ := fun j => M * (z j).arg / (2 * π)
  let ξ : ι → UnitAddCircle := fun j => (θ j : UnitAddCircle)
  let n := 6 ^ Fintype.card ι
  have hn : 0 < n := by dsimp [n]; positivity
  have hv : volume (Metric.closedBall (0 : ι → UnitAddCircle) ((1 / 6 : ℝ) / 2)) =
      (1 / 6 : ENNReal) ^ Fintype.card ι := by
    rw [MeasureTheory.volume_pi_closedBall (0 : ι → UnitAddCircle)
      (by norm_num : (0 : ℝ) ≤ (1 / 6 : ℝ) / 2)]
    simp only [Pi.zero_apply, AddCircle.volume_closedBall]
    norm_num
    simp
  have huniv : volume (Set.univ : Set (ι → UnitAddCircle)) = 1 := by
    simp [volume_pi, Measure.pi_univ]
  have hm : (n : ENNReal) * (1 / 6 : ENNReal) ^ Fintype.card ι = 1 := by
    dsimp [n]
    rw [Nat.cast_pow, ← mul_pow]
    norm_num only [Nat.cast_ofNat, one_div]
    rw [ENNReal.mul_inv_cancel (by norm_num : (6 : ENNReal) ≠ 0)
      (by norm_num : (6 : ENNReal) ≠ ⊤), one_pow]
  have hδ : volume (Set.univ : Set (ι → UnitAddCircle)) ≤
      (n + 1) • volume (Metric.closedBall (0 : ι → UnitAddCircle) ((1 / 6 : ℝ) / 2)) := by
    rw [huniv, hv, nsmul_eq_mul]
    calc
      _ = (n : ENNReal) * (1 / 6 : ENNReal) ^ Fintype.card ι := hm.symm
      _ ≤ (n + 1 : ENNReal) * (1 / 6 : ENNReal) ^ Fintype.card ι := by gcongr; simp
      _ = _ := by norm_cast
  obtain ⟨u, hu, hnorm⟩ := NormedAddCommGroup.exists_norm_nsmul_le
    (μ := volume) ξ hn (1 / 6) hδ
  refine ⟨u, hu.1, hu.2, ?_⟩
  intro j
  have hj : ‖(((u : ℝ) * θ j : ℝ) : UnitAddCircle)‖ ≤ 1 / 6 := by
    have hh := (norm_le_pi_norm (u • ξ) j).trans hnorm
    simpa only [Pi.smul_apply, ξ, ← AddCircle.coe_nsmul, nsmul_eq_mul] using hh
  rw [AddCircle.norm_eq] at hj
  norm_num only [inv_one, one_mul, mul_one] at hj
  let d := (u : ℝ) * θ j - (round ((u : ℝ) * θ j) : ℝ)
  have hd : |2 * π * d| ≤ π / 3 := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * π)]
    dsimp [d]
    nlinarith [Real.pi_pos]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (2 * π * d))
    (by linarith [Real.pi_pos] : π / 3 ≤ π) hd
  rw [Real.cos_pi_div_three, Real.cos_abs] at hc
  have he : ((M * u : ℕ) : ℝ) * (z j).arg =
      2 * π * d + (round ((u : ℝ) * θ j) : ℝ) * (2 * π) := by
    dsimp [d, θ]
    push_cast
    field_simp
    ring
  rw [← Real.cos_add_int_mul_two_pi (2 * π * d) (round ((u : ℝ) * θ j)), ← he] at hc
  rw [power_real_part]
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_left hc (pow_nonneg (norm_nonneg (z j)) _)


private theorem near_finite {ι : Type*} {z : ι → ℂ}
    (hs : Summable (fun i => ‖z i‖ ^ 2)) : {i | 1 / 2 < ‖z i‖}.Finite := by
  have he := hs.tendsto_cofinite_zero.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  apply (Filter.mem_cofinite.mp he).subset
  intro i hi
  change 1 / 2 < ‖z i‖ at hi
  change ¬ ‖z i‖ ^ 2 < 1 / 4
  nlinarith [hi]

private theorem power_summable {ι : Type*} {z : ι → ℂ}
    (hs : Summable (fun i => ‖z i‖ ^ 2)) {n : ℕ} (hn : 2 ≤ n) :
    Summable (fun i => ‖z i ^ n‖) := by
  classical
  apply hs.of_norm_bounded_eventually
  filter_upwards [(near_finite hs).eventually_cofinite_notMem] with i hi
  have hz : ‖z i‖ ≤ 1 := by simp only [not_lt] at hi; linarith
  rw [norm_norm, norm_pow]
  calc
    ‖z i‖ ^ n = ‖z i‖ ^ 2 * ‖z i‖ ^ (n - 2) := by
      rw [← pow_add, Nat.add_sub_cancel' hn]
    _ ≤ ‖z i‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ (norm_nonneg _) hz) (sq_nonneg _)
    _ = _ := mul_one _

private theorem far_bound {ι : Type*} {z : ι → ℂ}
    (hs : Summable (fun i => ‖z i‖ ^ 2)) {B : ℝ}
    (hB : (∑' i, ‖z i‖ ^ 2) ≤ B) {S : Finset ι}
    (hS : ∀ i, i ∉ S → ‖z i‖ ≤ 1 / 2) {n : ℕ} (hn : 2 ≤ n) :
    ‖∑' i : {i // i ∉ S}, z i ^ n‖ ≤ B * (1 / 2) ^ (n - 2) := by
  have hp := power_summable hs hn
  have hsub := hs.subtype (fun i => i ∉ S)
  have hsum : (∑' i : {i // i ∉ S}, ‖z i‖ ^ 2) ≤ B := by
    have he := hs.sum_add_tsum_compl (s := S)
    change (∑ i ∈ S, ‖z i‖ ^ 2) +
      (∑' i : {i // i ∉ S}, ‖z i‖ ^ 2) = (∑' i, ‖z i‖ ^ 2) at he
    have hn0 : 0 ≤ ∑ i ∈ S, ‖z i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  calc
    _ ≤ ∑' i : {i // i ∉ S}, ‖z i ^ n‖ := norm_tsum_le_tsum_norm (hp.subtype _)
    _ ≤ ∑' i : {i // i ∉ S}, ‖z i‖ ^ 2 * (1 / 2) ^ (n - 2) := by
      apply (hp.subtype _).tsum_le_tsum _ (hsub.mul_right _)
      intro i
      change ‖z i ^ n‖ ≤ ‖z i‖ ^ 2 * (1 / 2) ^ (n - 2)
      rw [norm_pow]
      calc
        _ = ‖z i‖ ^ 2 * ‖z i‖ ^ (n - 2) := by rw [← pow_add, Nat.add_sub_cancel' hn]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hS i i.2) _) (sq_nonneg _)
    _ = (∑' i : {i // i ∉ S}, ‖z i‖ ^ 2) * (1 / 2) ^ (n - 2) :=
      tsum_mul_right
    _ ≤ _ := mul_le_mul_of_nonneg_right hsum (by positivity)

/-- Finite one-sided moments detect every spectral value outside the target disk.
The index type can be infinite; repetitions encode arbitrary multiplicities. -/
private theorem spectrum_detection {ι : Type*} (z : ι → ℂ) (B D r R : ℝ)
    (M N : ℕ) (hs : Summable (fun i => ‖z i‖ ^ 2))
    (hB : (∑' i, ‖z i‖ ^ 2) ≤ B) (hN : 4 * B ≤ N)
    (hr : 0 < r) (hrR : r < R) (hR : R ≤ 2) (hM : 2 ≤ M)
    (hfar : 16 * B * (R / 2) ^ M ≤ 1)
    (hgain : 4 * D ≤ (R / r) ^ M)
    (hmom : ∀ n : ℕ, M ≤ n → n ≤ M * 6 ^ N → M ∣ n →
      R ^ n * (∑' i, z i ^ n).re ≤ D) :
    ∀ i, ‖z i‖ < 1 / r := by
  classical
  have hRp : 0 < R := hr.trans hrR
  have hB0 : 0 ≤ B := (tsum_nonneg fun i => sq_nonneg ‖z i‖).trans hB
  let S := (near_finite hs).toFinset
  have hS (i : ι) : i ∈ S ↔ 1 / 2 < ‖z i‖ := by simp [S]
  have hcard : S.card ≤ N := by
    have hc : (S.card : ℝ) / 4 ≤ ∑ i ∈ S, ‖z i‖ ^ 2 := by
      calc
        _ = ∑ _i ∈ S, (1 / 4 : ℝ) := by simp; ring
        _ ≤ _ := Finset.sum_le_sum fun i hi => by nlinarith [(hS i).mp hi]
    have hb := hs.sum_le_tsum S (fun _ _ => sq_nonneg _)
    exact_mod_cast (show (S.card : ℝ) ≤ (N : ℝ) by linarith)
  obtain ⟨u, hu, huN, hphase⟩ :=
    simultaneous_positive_powers (fun i : S => z i) M
  let n := M * u
  have hnM : M ≤ n := by dsimp [n]; exact Nat.le_mul_of_pos_right M hu
  have hn2 : 2 ≤ n := hM.trans hnM
  have hnN : n ≤ M * 6 ^ N := by
    apply Nat.mul_le_mul_left M
    exact huN.trans (by simpa using pow_le_pow_right₀ (by norm_num : 1 ≤ (6 : ℕ)) hcard)
  have hsmall : 4 * B * (R / 2) ^ n ≤ 1 / 4 := by
    have hp : (R / 2) ^ n ≤ (R / 2) ^ M :=
      pow_le_pow_of_le_one (by positivity) (by linarith) hnM
    nlinarith [mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 16 * B)]
  have hgrowth : 4 * D ≤ (R / r) ^ n := hgain.trans
    (pow_le_pow_right₀ (by rw [one_le_div hr]; exact hrR.le) hnM)
  intro i
  by_contra! hi
  have hiS : i ∈ S := (hS i).mpr (by
    have := (one_div_lt_one_div_of_lt hr (hrR.trans_le hR))
    change 1 / 2 < 1 / r at this
    linarith)
  have hpos (j : ι) (hj : j ∈ S) : 0 ≤ (z j ^ n).re := by
    exact (by positivity : (0 : ℝ) ≤ 1 / 2 * ‖z j‖ ^ n).trans
      (hphase ⟨j, hj⟩)
  have hhead : 1 / 2 * ‖z i‖ ^ n ≤ (∑ j ∈ S, z j ^ n).re := by
    exact (hphase ⟨i, hiS⟩).trans (by
      rw [Complex.re_sum]
      exact Finset.single_le_sum hpos hiS)
  have htail := far_bound hs hB (S := S) (fun j hj => le_of_not_gt fun h =>
    hj ((hS j).mpr h)) hn2
  have hsplit := (power_summable hs hn2).of_norm.sum_add_tsum_compl (s := S)
  have hreal : 1 / 2 * ‖z i‖ ^ n ≤
      (∑' j, z j ^ n).re + B * (1 / 2) ^ (n - 2) := by
    have ht := Complex.re_le_norm (-(∑' j : {j // j ∉ S}, z j ^ n))
    rw [Complex.neg_re, norm_neg] at ht
    have ht' := ht.trans htail
    have he := congrArg Complex.re hsplit
    rw [Complex.add_re] at he
    change (∑ j ∈ S, z j ^ n).re +
      (∑' j : {j // j ∉ S}, z j ^ n).re = (∑' j, z j ^ n).re at he
    linarith
  have hid : R ^ n * (1 / 2) ^ (n - 2) = 4 * (R / 2) ^ n := by
    have he : (1 / 2 : ℝ) ^ n = (1 / 2) ^ (n - 2) * (1 / 2) ^ 2 := by
      rw [← pow_add, Nat.sub_add_cancel hn2]
    calc
      _ = 4 * (R ^ n * (1 / 2 : ℝ) ^ n) := by
        rw [he]
        ring
      _ = _ := by rw [← mul_pow]; congr 2; ring
  have hscaled : 1 / 2 * (R * ‖z i‖) ^ n ≤ D + 1 / 4 := by
    have hh := mul_le_mul_of_nonneg_left hreal (pow_nonneg hRp.le n)
    rw [mul_add] at hh
    have hm := hmom n hnM hnN ⟨u, rfl⟩
    have he : R ^ n * (B * (1 / 2) ^ (n - 2)) = 4 * B * (R / 2) ^ n := by
      nlinarith [hid]
    rw [he] at hh
    rw [mul_pow]
    nlinarith
  have hbad : (R / r) ^ n ≤ (R * ‖z i‖) ^ n := by
    apply pow_le_pow_left₀ (by positivity)
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hi hRp.le
  have hone : 1 < (R / r) ^ n := one_lt_pow₀
    ((one_lt_div hr).mpr hrR) (by omega)
  nlinarith

/-- The starting exponent in the finite one-sided criterion. -/
def momentStart (B C r : ℝ) : ℕ :=
  2 + ⌈max (Real.log (16 * B) / Real.log (4 / 3))
    (Real.log (6 * (C + 2)) / Real.log ((3 / 2) / r))⌉₊

/-- The last normalized moment needed by the detector. -/
def momentOrder (B C r : ℝ) : ℕ := momentStart B C r * 6 ^ ⌈4 * B⌉₊ - 1

private theorem start_bounds {B C r : ℝ} (hB : 0 ≤ B)
    (hr : 0 < r) (hrR : r < 3 / 2) :
    16 * B * ((3 / 2 : ℝ) / 2) ^ momentStart B C r ≤ 1 ∧
      4 * ((C + 1) * (3 / 2)) ≤ ((3 / 2) / r) ^ momentStart B C r := by
  let M := momentStart B C r
  have hM : max (Real.log (16 * B) / Real.log (4 / 3))
      (Real.log (6 * (C + 2)) / Real.log ((3 / 2) / r)) ≤ (M : ℝ) := by
    exact (Nat.le_ceil _).trans (by dsimp [M, momentStart]; push_cast; linarith)
  have hl : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have hratio : 1 < (3 / 2 : ℝ) / r := (one_lt_div hr).mpr hrR
  have hlr : 0 < Real.log ((3 / 2 : ℝ) / r) := Real.log_pos hratio
  constructor
  · rcases hB.eq_or_lt with hB | hB
    · rw [← hB]; simp
    have ha := (le_max_left _ _).trans hM
    have he : 16 * B ≤ (4 / 3 : ℝ) ^ M := by
      apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
      rw [Real.log_pow]
      exact (div_le_iff₀ hl).mp ha
    have hh := mul_le_mul_of_nonneg_right he
      (show 0 ≤ ((3 / 2 : ℝ) / 2) ^ M by positivity)
    have hid : (4 / 3 : ℝ) ^ M * ((3 / 2 : ℝ) / 2) ^ M = 1 := by
      rw [← mul_pow]; norm_num
    rwa [hid] at hh
  · by_cases hC : C + 1 ≤ 0
    · exact (show 4 * ((C + 1) * (3 / 2)) ≤ 0 by nlinarith).trans
        (pow_nonneg (by positivity) _)
    have hCp : 0 < C + 2 := by linarith
    have ha := (le_max_right _ _).trans hM
    have he : 6 * (C + 2) ≤ ((3 / 2 : ℝ) / r) ^ M := by
      apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
      rw [Real.log_pow]
      exact (div_le_iff₀ hlr).mp ha
    linarith

/-- The explicit finite-order detector with radius three halves. This is a
spectral criterion; a Dirichlet application must supply the power-sum identity
and the square-sum estimate for its actual multiplicity-weighted zeros. -/
private theorem finite_moment_exclusion {ι : Type*} (z : ι → ℂ) (B C r : ℝ)
    (hs : Summable (fun i => ‖z i‖ ^ 2))
    (hB : (∑' i, ‖z i‖ ^ 2) ≤ B)
    (hr : 0 < r) (hrR : r < 3 / 2)
    (hmom : ∀ k : ℕ, momentStart B C r - 1 ≤ k → k ≤ momentOrder B C r →
      momentStart B C r ∣ k + 1 →
      (∑' i, z i ^ (k + 1)).re ≤ (C + 1) * (2 / 3 : ℝ) ^ k) :
    ∀ i, ‖z i‖ < 1 / r := by
  have hB0 : 0 ≤ B := (tsum_nonneg fun i => sq_nonneg ‖z i‖).trans hB
  obtain ⟨hfar, hgain⟩ := start_bounds hB0 hr hrR
  apply spectrum_detection z B ((C + 1) * (3 / 2)) r (3 / 2)
    (momentStart B C r) ⌈4 * B⌉₊ hs hB (Nat.le_ceil _) hr hrR (by norm_num)
    (by unfold momentStart; omega) hfar hgain
  intro n hn hnN hdiv
  have hn2 : 2 ≤ n := by dsimp [momentStart] at hn; omega
  have hk : n - 1 ≤ momentOrder B C r := by unfold momentOrder; omega
  have hu := hmom (n - 1) (by omega) hk
    (by simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hdiv)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hu
  have he : (3 / 2 : ℝ) ^ n * (2 / 3 : ℝ) ^ (n - 1) = 3 / 2 := by
    have hp : (3 / 2 : ℝ) ^ (n - 1) * (2 / 3 : ℝ) ^ (n - 1) = 1 := by
      rw [← mul_pow]; norm_num
    calc
      _ = ((3 / 2 : ℝ) ^ (n - 1) * (3 / 2)) * (2 / 3 : ℝ) ^ (n - 1) := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
      _ = (3 / 2) * ((3 / 2 : ℝ) ^ (n - 1) * (2 / 3 : ℝ) ^ (n - 1)) := by ring
      _ = _ := by rw [hp]; ring
  calc
    _ ≤ (3 / 2 : ℝ) ^ n * ((C + 1) * (2 / 3 : ℝ) ^ (n - 1)) :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    _ = (C + 1) * ((3 / 2 : ℝ) ^ n * (2 / 3 : ℝ) ^ (n - 1)) := by ring
    _ = _ := by rw [he]

/-- Number of equal subintervals in the height grid. -/
def gridSize (T ε : ℝ) : ℕ := max 1 ⌈2 * T / ε⌉₊

/-- The height grid includes both endpoints. -/
def gridPoint (T ε : ℝ) (j : ℕ) : ℝ := -T + 2 * T * j / gridSize T ε

private theorem grid_near {T ε γ : ℝ} (hT : 0 ≤ T) (hε : 0 < ε)
    (hγ : |γ| ≤ T) :
    ∃ j : ℕ, j ≤ gridSize T ε ∧ |γ - gridPoint T ε j| ≤ ε := by
  rcases hT.eq_or_lt with hT | hT
  · have hg : γ = 0 := by rw [← hT] at hγ; exact abs_nonpos_iff.mp hγ
    exact ⟨0, Nat.zero_le _, by simp [← hT, hg, gridPoint, hε.le]⟩
  let J := gridSize T ε
  have hJ : 1 ≤ J := le_max_left _ _
  have hJp : (0 : ℝ) < J := by exact_mod_cast hJ
  have hcut : 2 * T ≤ (J : ℝ) * ε := by
    have hc : 2 * T / ε ≤ (J : ℝ) := (Nat.le_ceil _).trans
      (by exact_mod_cast (le_max_right 1 ⌈2 * T / ε⌉₊))
    exact (div_le_iff₀ hε).mp hc
  let x := (γ + T) * J / (2 * T)
  have hx : 0 ≤ x := div_nonneg (mul_nonneg (by linarith [(abs_le.mp hγ).1])
    (Nat.cast_nonneg _)) (by positivity)
  have hxJ : x ≤ J := by
    dsimp [x]
    rw [div_le_iff₀ (by positivity : 0 < 2 * T)]
    nlinarith [(abs_le.mp hγ).2]
  let j := ⌊x⌋₊
  have hj : (j : ℝ) ≤ x := Nat.floor_le hx
  have hjJ : j ≤ J := by exact_mod_cast hj.trans hxJ
  have hju : x < (j : ℝ) + 1 := Nat.lt_floor_add_one x
  have he : γ - gridPoint T ε j = (2 * T / J) * (x - j) := by
    change γ - (-T + 2 * T * j / (J : ℝ)) = (2 * T / J) * (x - j)
    dsimp [x]
    field_simp [hJp.ne', hT.ne']
    <;> ring
  refine ⟨j, hjJ, ?_⟩
  rw [he, abs_of_nonneg (mul_nonneg (by positivity) (by linarith))]
  calc
    _ ≤ 2 * T / J := by nlinarith [div_pos (by positivity : 0 < 2 * T) hJp]
    _ ≤ ε := (div_le_iff₀ hJp).mpr (by nlinarith [hcut])

/-- Only zeros in the tested rectangle need the upper real-part bound. -/
private theorem finite_grid_exclusion {ι : Type*} (ρ : ι → ℂ) (B C T ε : ℝ)
    (hε : 0 < ε)
    (hstrip : ∀ i, 1 / 2 + ε ≤ (ρ i).re → |(ρ i).im| ≤ T → (ρ i).re ≤ 1)
    (hs : ∀ j : ℕ, j ≤ gridSize T ε →
      Summable (fun i => ‖(2 + gridPoint T ε j * Complex.I - ρ i)⁻¹‖ ^ 2))
    (hB : ∀ j : ℕ, j ≤ gridSize T ε →
      (∑' i, ‖(2 + gridPoint T ε j * Complex.I - ρ i)⁻¹‖ ^ 2) ≤ B)
    (hmom : ∀ j : ℕ, j ≤ gridSize T ε → ∀ k : ℕ,
      momentStart B C (3 / 2 - ε / 2) - 1 ≤ k →
      k ≤ momentOrder B C (3 / 2 - ε / 2) →
      momentStart B C (3 / 2 - ε / 2) ∣ k + 1 →
      (∑' i, (2 + gridPoint T ε j * Complex.I - ρ i)⁻¹ ^ (k + 1)).re ≤
        (C + 1) * (2 / 3 : ℝ) ^ k) :
    ∀ i, 1 / 2 + ε ≤ (ρ i).re → T < |(ρ i).im| := by
  by_cases hT : 0 ≤ T
  swap
  · intro i _
    exact (lt_of_not_ge hT).trans_le (abs_nonneg _)
  intro i hi
  by_contra! hheight
  have hlocal := hstrip i hi hheight
  have hεh : ε ≤ 1 / 2 := by linarith
  obtain ⟨j, hj, hnear⟩ := grid_near hT hε hheight
  let w : ℂ := 2 + gridPoint T ε j * Complex.I - ρ i
  let r : ℝ := 3 / 2 - ε / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hnorm : ‖w‖ < r := by
    have hdx : 1 ≤ 2 - (ρ i).re := by linarith [hlocal]
    have hdx' : 2 - (ρ i).re ≤ 3 / 2 - ε := by linarith
    have hdy : |gridPoint T ε j - (ρ i).im| ≤ ε := by
      rwa [abs_sub_comm] at hnear
    have hsquare : ‖w‖ ^ 2 = (2 - (ρ i).re) ^ 2 +
        (gridPoint T ε j - (ρ i).im) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp [w, Complex.normSq_apply]
      ring
    have hdxsq : (2 - (ρ i).re) ^ 2 ≤ (3 / 2 - ε) ^ 2 := by nlinarith
    have hdysq : (gridPoint T ε j - (ρ i).im) ^ 2 ≤ ε ^ 2 := by
      nlinarith [(abs_le.mp hdy).1, (abs_le.mp hdy).2]
    dsimp [r] at *
    nlinarith [norm_nonneg w, mul_pos hε
      (show 0 < 3 / 2 - 7 * ε / 4 by linarith)]
  have hw : 0 < ‖w‖ := by
    apply norm_pos_iff.mpr
    intro hz
    have hzre := congrArg Complex.re hz
    simp [w] at hzre
    linarith [hlocal]
  have hdet := finite_moment_exclusion
    (fun i => (2 + gridPoint T ε j * Complex.I - ρ i)⁻¹) B C r
    (hs j hj) (hB j hj) hr (by dsimp [r]; linarith) (hmom j hj) i
  change ‖w⁻¹‖ < 1 / r at hdet
  rw [norm_inv, ← one_div] at hdet
  exact (not_lt_of_ge ((one_div_lt_one_div hw hr).mp hdet).le) hnorm


/-- The full-zero inverse-square budget at height T. -/
def zeroBudget (q : ℕ) (T : ℝ) : ℝ := Real.log ((q : ℝ) * (T + 3)) + 4

/-- The largest moment order tested by the finite arithmetic criterion. -/
def zeroOrder (q : ℕ) (C T ε : ℝ) : ℕ :=
  momentOrder (zeroBudget q T) C (3 / 2 - ε / 2)

private abbrev ZeroCopy {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :=
  Σ ρ : {z : ℂ // χ.LFunction z = 0}, Fin (analyticOrderNatAt χ.LFunction ρ.1)

private theorem grid_height {T ε : ℝ} (hT : 0 ≤ T)
    {j : ℕ} (hj : j ≤ gridSize T ε) : |gridPoint T ε j| ≤ T := by
  have hJ : (0 : ℝ) < gridSize T ε := by
    exact_mod_cast (show 0 < gridSize T ε from
      lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
  have hj' : (j : ℝ) ≤ gridSize T ε := by exact_mod_cast hj
  rw [abs_le]
  unfold gridPoint
  constructor
  · have : 0 ≤ 2 * T * j / (gridSize T ε : ℝ) := by positivity
    linarith
  · have hh : 2 * T * j / (gridSize T ε : ℝ) ≤ 2 * T := by
      apply (div_le_iff₀ hJ).mpr
      nlinarith
    linarith

private theorem zero_order_positive {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1)
    (ρ : {z : ℂ // χ.LFunction z = 0}) : 0 < analyticOrderNatAt χ.LFunction ρ.1 := by
  have hF := DirichletCharacter.differentiable_LFunction hne
  have h2 : χ.LFunction 2 ≠ 0 :=
    χ.LFunction_ne_zero_of_one_le_re (.inl hne) (by norm_num)
  have hA : AnalyticOnNhd ℂ χ.LFunction univ := fun z _ => hF.analyticAt z
  have hn := hA.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ (2 : ℂ)) (mem_univ ρ.1)
    (by rw [(hF.analyticAt 2).analyticOrderAt_eq_zero.mpr h2]; simp)
  exact ENat.toNat_pos ((hF.analyticAt ρ.1).analyticOrderAt_ne_zero.mpr ρ.2) hn

private theorem copies_square {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (T t : ℝ) (ht : |t| ≤ T) :
    Summable (fun i : ZeroCopy χ => ‖(2 + t * I - i.1.1)⁻¹‖ ^ 2) ∧
    (∑' i : ZeroCopy χ, ‖(2 + t * I - i.1.1)⁻¹‖ ^ 2) ≤ zeroBudget q T := by
  have hb := zero_square_bound hχ hne T t ht
  have hs : Summable (fun i : ZeroCopy χ => ‖(2 + t * I - i.1.1)⁻¹‖ ^ 2) := by
    apply (summable_sigma_of_nonneg (fun _ => sq_nonneg _)).mpr
    refine ⟨fun _ => Summable.of_finite, ?_⟩
    simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using hb.2.1
  refine ⟨hs, ?_⟩
  rw [hs.tsum_sigma]
  simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, zeroBudget] using hb.2.2.2.1

private theorem copies_moment {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (k : ℕ) (hk : 1 ≤ k) (t : ℝ) :
    (∑' i : ZeroCopy χ, (2 + t * I - i.1.1)⁻¹ ^ (k + 1)).re = moment χ k t := by
  have hp := moment_zero_power_hasSum hχ hne k hk t
  have hn : Summable (fun i : ZeroCopy χ =>
      ‖(2 + t * I - i.1.1)⁻¹ ^ (k + 1)‖) := by
    apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr
    refine ⟨fun _ => Summable.of_finite, ?_⟩
    simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, norm_mul, Complex.norm_natCast] using hp.2.1
  have hs : Summable (fun i : ZeroCopy χ =>
      (2 + t * I - i.1.1)⁻¹ ^ (k + 1)) := hn.of_norm
  rw [hs.tsum_sigma]
  simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] using hp.2.2.symm

/-- Finite arithmetic tests exclude the closed rectangle and the closed grid disks. -/
theorem finite_moment_zero_free {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (C T ε : ℝ) (X : ℕ) (hε : 0 < ε)
    (hX : Real.exp (4 * (zeroOrder q C T ε + 1 : ℝ)) ≤ (X : ℝ))
    (hmom : ∀ j : ℕ, j ≤ gridSize T ε → ∀ k : ℕ,
      momentStart (zeroBudget q T) C (3 / 2 - ε / 2) - 1 ≤ k →
      k ≤ zeroOrder q C T ε →
      momentStart (zeroBudget q T) C (3 / 2 - ε / 2) ∣ k + 1 →
      finiteMoment χ k X (gridPoint T ε j) ≤ (C + 1 / 3) * (2 / 3 : ℝ) ^ k) :
    (∀ s : ℂ, 1 / 2 + ε ≤ s.re → |s.im| ≤ T → χ.LFunction s ≠ 0) ∧
    (0 ≤ T → ∀ j : ℕ, j ≤ gridSize T ε → ∀ s : ℂ,
      ‖s - (2 + gridPoint T ε j * I)‖ ≤ 3 / 2 - ε / 2 → χ.LFunction s ≠ 0) := by
  by_cases hT : 0 ≤ T
  swap
  · constructor
    · intro s _ hs
      exact ((not_le_of_gt (lt_of_not_ge hT)) ((abs_nonneg s.im).trans hs)).elim
    · exact fun h => (hT h).elim
  let ρ : ZeroCopy χ → ℂ := fun i => i.1.1
  have hstrip : ∀ i, (ρ i).re ≤ 1 := by
    intro i
    exact ((zero_square_bound hχ hne T 0 (by simpa using hT)).1 i.1).le
  have hsquare (j : ℕ) (hj : j ≤ gridSize T ε) :=
    copies_square hχ hne T (gridPoint T ε j) (grid_height hT hj)
  have hpowers (j : ℕ) (hj : j ≤ gridSize T ε) (k : ℕ)
      (hkM : momentStart (zeroBudget q T) C (3 / 2 - ε / 2) - 1 ≤ k)
      (hkK : k ≤ momentOrder (zeroBudget q T) C (3 / 2 - ε / 2))
      (hkdiv : momentStart (zeroBudget q T) C (3 / 2 - ε / 2) ∣ k + 1) :
      (∑' i : ZeroCopy χ, (2 + gridPoint T ε j * I - ρ i)⁻¹ ^ (k + 1)).re ≤
        (C + 1) * (2 / 3 : ℝ) ^ k := by
    have hk : 1 ≤ k := by unfold momentStart at hkM; omega
    rw [show (∑' i : ZeroCopy χ,
      (2 + gridPoint T ε j * I - ρ i)⁻¹ ^ (k + 1)).re =
        moment χ k (gridPoint T ε j) from copies_moment hχ hne k hk _]
    have hcut : Real.exp (4 * (k + 1 : ℝ)) ≤ (X : ℝ) := by
      apply (Real.exp_le_exp.mpr ?_).trans hX
      have hk' : (k : ℝ) ≤ zeroOrder q C T ε := by exact_mod_cast hkK
      linarith
    have he := ((finite_moment_error χ k X (gridPoint T ε j)).2.2 hcut).2
    have hm := hmom j hj k hkM hkK hkdiv
    rw [pow_succ] at he
    have hd := (abs_le.mp he).2
    nlinarith
  have hex := finite_grid_exclusion ρ (zeroBudget q T) C T ε hε (fun i _ _ => hstrip i)
    (fun j hj => (hsquare j hj).1) (fun j hj => (hsquare j hj).2) hpowers
  constructor
  · intro s hre him hz
    let z : {z : ℂ // χ.LFunction z = 0} := ⟨s, hz⟩
    let i : ZeroCopy χ := ⟨z, ⟨0, zero_order_positive hne z⟩⟩
    have hi : ρ i = s := rfl
    have hr : 1 / 2 + ε ≤ (ρ i).re := by simpa only [hi] using hre
    have ht : |(ρ i).im| ≤ T := by simpa only [hi] using him
    exact (not_lt_of_ge ht) (hex i hr)
  · intro _ j hj s hdist
    by_cases hε3 : ε < 3
    swap
    · have hn : ‖s - (2 + gridPoint T ε j * I)‖ = 0 := by
        nlinarith [norm_nonneg (s - (2 + gridPoint T ε j * I))]
      have he : s = 2 + gridPoint T ε j * I := sub_eq_zero.mp (norm_eq_zero.mp hn)
      rw [he]
      exact χ.LFunction_ne_zero_of_one_le_re
        (.inl hne) (by norm_num)
    intro hz
    let z : {z : ℂ // χ.LFunction z = 0} := ⟨s, hz⟩
    let i : ZeroCopy χ := ⟨z, ⟨0, zero_order_positive hne z⟩⟩
    let w : ℂ := 2 + gridPoint T ε j * I - ρ i
    have hr : 0 < 3 / 2 - ε / 2 := by linarith
    have hw : 0 < ‖w‖ := by
      apply norm_pos_iff.mpr
      intro hw
      have hre := congrArg Complex.re hw
      simp [w] at hre
      have hs := hstrip i
      change s.re ≤ 1 at hs
      change 2 - s.re = 0 at hre
      linarith
    have hdet := finite_moment_exclusion
      (fun i => (2 + gridPoint T ε j * I - ρ i)⁻¹) (zeroBudget q T) C
      (3 / 2 - ε / 2) (hsquare j hj).1 (hsquare j hj).2 hr
      (by linarith) (hpowers j hj) i
    change ‖w⁻¹‖ < 1 / (3 / 2 - ε / 2) at hdet
    rw [norm_inv, ← one_div] at hdet
    have hlarge := (one_div_lt_one_div hw hr).mp hdet
    have hsmall : ‖w‖ ≤ 3 / 2 - ε / 2 := by
      simpa only [w, ρ, i, z, norm_sub_rev] using hdist
    exact (not_lt_of_ge hsmall) hlarge

end D5.S3.CharacterSums.DirichletFiniteZeroFree
