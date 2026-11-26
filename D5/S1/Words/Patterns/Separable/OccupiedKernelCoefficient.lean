/- GID: D5/S1/Words/Patterns/Separable/OccupiedKernelCoefficient
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/OccupiedKernelCoefficient
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Schroder]
   utility: none
   digest: Explicit strict remainder for the actual critical occupation kernel. -/

import Mathlib.Data.Nat.Choose.Central
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import D5.S1.Words.Patterns.Separable.ActualCountRatios

/-! The critical occupation kernel has a strictly positive leading term on the scale
`m ^ (-3 / 2)`, with an explicit smaller-order bound away from the singleton. The proof
uses the actual Schröder generating series and a geometrically damped convolution. -/

namespace D5.S1.Words.Patterns.Separable.OccupiedKernelCoefficient

open D5.S1.Words.Patterns.Separable.OccupiedComparison
open D5.S1.Words.Patterns.Separable.ActualCardinality
open D5.S1.Words.Patterns.Separable.CutFactorization (Avoider)
open PowerSeries Filter Topology
open scoped BigOperators

noncomputable section

private def scaledBinom (n : ℕ) : ℝ := (Nat.centralBinom n : ℝ) / 4 ^ n

private def squaredProfile (n : ℕ) : ℝ := (n : ℝ) * scaledBinom n ^ 2

private def centralProfile (n : ℕ) : ℝ := Real.sqrt n * scaledBinom n

private theorem scaledBinom_succ (n : ℕ) :
    scaledBinom (n+1) = scaledBinom n * ((2*(n : ℝ)+1)/(2*((n : ℝ)+1))) := by
  have h : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ) =
      2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  unfold scaledBinom
  rw [pow_succ]
  field_simp [show (n : ℝ) + 1 ≠ 0 by positivity]
  nlinarith only [h]

private theorem centralProfile_nonneg (n : ℕ) : 0 ≤ centralProfile n := by
  unfold centralProfile scaledBinom
  positivity

private theorem centralProfile_sq (n : ℕ) : centralProfile n ^ 2 = squaredProfile n := by
  rw [centralProfile, mul_pow, Real.sq_sqrt (by positivity)]
  rfl

private theorem sq_step (n : ℕ) (hn : 1 ≤ n) :
    squaredProfile (n+1) =
      squaredProfile n + (1/(4*(n : ℝ)*((n : ℝ)+1))) * squaredProfile n := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  unfold squaredProfile
  rw [scaledBinom_succ, Nat.cast_succ]
  field_simp [ne_of_gt hn', show (n : ℝ) + 1 ≠ 0 by positivity]
  ring

private theorem sq_one : squaredProfile 1 = 1/4 := by
  norm_num [squaredProfile, scaledBinom, Nat.centralBinom, Nat.choose]

private theorem square_cap_shifted (n : ℕ) :
    squaredProfile (n+1) + 1/(4*((n+1 : ℕ) : ℝ)) ≤ 1/2 := by
  induction n with
  | zero =>
    norm_num [sq_one]
  | succ n ih =>
    have H : 1 ≤ n+1 := by omega
    have hn : 0 < ((n+1 : ℕ) : ℝ) := by positivity
    have hc : squaredProfile (n+1) ≤ 1 := by
      have hpos : 0 ≤ 1/(4*((n+1 : ℕ) : ℝ)) := by positivity
      linarith
    have hadd :=
      mul_le_mul_of_nonneg_left hc
        (show 0 ≤ 1/(4*((n+1 : ℕ) : ℝ)*(((n+1 : ℕ) : ℝ)+1)) by positivity)
    let x := ((n+1 : ℕ) : ℝ)
    have hrec : 1/(4*x) - 1/(4*(x+1)) = 1/(4*x*(x+1)) := by
      field_simp [show x ≠ 0 from ne_of_gt hn, show x+1 ≠ 0 by positivity]
      ring
    change squaredProfile (n+1) + 1/(4*x) ≤ 1/2 at ih
    change 1/(4*x*(x+1)) * squaredProfile (n+1) ≤ _ at hadd
    rw [show n.succ+1 = (n+1)+1 by omega, sq_step (n+1) H]
    change squaredProfile (n+1) + 1/(4*x*(x+1)) * squaredProfile (n+1) +
      1/(4*(((n+1 : ℕ)+1 : ℕ) : ℝ)) ≤ 1/2
    rw [Nat.cast_succ]
    change squaredProfile (n+1) + 1/(4*x*(x+1)) * squaredProfile (n+1) +
      1/(4*(x+1)) ≤ 1/2
    linarith only [hadd, hrec, ih]

private theorem square_half (n : ℕ) (hn : 1 ≤ n) : squaredProfile n ≤ 1/2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hp : 0 ≤ 1/(4*((m+1 : ℕ) : ℝ)) := by positivity
  linarith [square_cap_shifted m]

private theorem squares_mono : Monotone (fun j : ℕ => squaredProfile (j+1)) := by
  apply monotone_nat_of_le_succ
  intro j
  change squaredProfile (j+1) ≤ squaredProfile (j+1+1)
  rw [sq_step (j+1) (by omega)]
  have hn : 0 ≤ squaredProfile (j+1) := by unfold squaredProfile; positivity
  have hpos : 0 ≤ (1/(4*((j+1 : ℕ) : ℝ)*(((j+1 : ℕ) : ℝ)+1))) * squaredProfile (j+1) :=
    mul_nonneg (by positivity) hn
  linarith only [hpos]

private theorem squares_plus_error_anti :
    Antitone (fun j : ℕ => squaredProfile (j+1) + 1/(8*((j+1 : ℕ) : ℝ))) := by
  apply antitone_nat_of_succ_le
  intro j
  let x := ((j+1 : ℕ) : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  have hrec : 1/(8*x) - 1/(8*(x+1)) = 1/(8*x*(x+1)) := by
    field_simp [show x ≠ 0 from hx.ne', show x+1 ≠ 0 by positivity]
    ring
  have hmul : 1/(4*x*(x+1)) * squaredProfile (j+1) ≤ 1/(8*x*(x+1)) := by
    have h := mul_le_mul_of_nonneg_left (square_half (j+1) (by omega))
      (show 0 ≤ 1/(4*x*(x+1)) by positivity)
    convert h using 1
    field_simp [show x ≠ 0 from hx.ne', show x+1 ≠ 0 by positivity]
    ring
  change squaredProfile (j+1+1) + 1/(8*((j+1+1 : ℕ) : ℝ)) ≤
    squaredProfile (j+1) + 1/(8*x)
  rw [sq_step (j+1) (by omega)]
  simp only [x, Nat.cast_add, Nat.cast_one] at hmul hrec ⊢
  linarith only [hmul, hrec]

private theorem centralProfile_limit_with_remainder :
    ∃ U : ℝ, 1/2 ≤ U ∧ U^2 ≤ 1/2 ∧ Tendsto centralProfile atTop (𝓝 U) ∧
      ∀ n : ℕ, 1 ≤ n → 0 ≤ U - centralProfile n ∧ U - centralProfile n ≤ 1/(8*(n : ℝ)) := by
  let V := ⨆ j : ℕ, squaredProfile (j+1)
  have hbdd : BddAbove (Set.range fun j : ℕ => squaredProfile (j+1)) :=
    ⟨1/2, by rintro x ⟨j, rfl⟩; exact square_half (j+1) (by omega)⟩
  have hv := tendsto_atTop_ciSup squares_mono hbdd
  have hvlo (j : ℕ) : squaredProfile (j+1) ≤ V := le_ciSup hbdd j
  have hvhi (j : ℕ) : V ≤ squaredProfile (j+1) + 1/(8*((j+1 : ℕ) : ℝ)) := by
    apply le_of_tendsto hv
    filter_upwards [eventually_ge_atTop j] with m hm
    have hh := squares_plus_error_anti hm
    have hpos : 0 ≤ 1/(8*((m+1 : ℕ) : ℝ)) := by positivity
    exact (le_add_of_nonneg_right hpos).trans hh
  have hv_min : 1/4 ≤ V := by simpa only [zero_add, sq_one] using hvlo 0
  have hv_max : V ≤ 1/2 := ciSup_le (fun j => square_half (j+1) (by omega))
  let U := Real.sqrt V
  have hu_sq : U^2 = V := Real.sq_sqrt (by linarith)
  have hu_pos : 0 ≤ U := Real.sqrt_nonneg _
  have hu_min : 1/2 ≤ U := by nlinarith only [hu_sq, hv_min, hu_pos]
  have ht : Tendsto centralProfile atTop (𝓝 U) := by
    apply (tendsto_add_atTop_iff_nat 1).1
    have hbase : Tendsto (fun j : ℕ => Real.sqrt (squaredProfile (j+1))) atTop (𝓝 U) :=
      (Real.continuous_sqrt.continuousAt : ContinuousAt Real.sqrt V).tendsto.comp hv
    convert hbase using 1
    funext j
    rw [← centralProfile_sq, Real.sqrt_sq (centralProfile_nonneg _)]
  refine ⟨U, hu_min, hu_sq ▸ hv_max, ht, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hmlo := hvlo m
  have hmhi := hvhi m
  have hm0 : 1/4 ≤ squaredProfile (m+1) := by
    have h := squares_mono (show 0 ≤ m by omega)
    simpa only [zero_add, sq_one] using h
  have hsq := centralProfile_sq (m+1)
  have hpos := centralProfile_nonneg (m+1)
  have hm : 1/2 ≤ centralProfile (m+1) := by nlinarith only [hm0, hsq, hpos]
  have hu : centralProfile (m+1) ≤ U := by nlinarith only [hmlo, hu_sq, hsq, hu_pos, hpos]
  refine ⟨sub_nonneg.mpr hu, ?_⟩
  have hup := mul_nonneg (sub_nonneg.mpr hu)
    (show 0 ≤ U + centralProfile (m+1) - 1 by linarith only [hu_min, hm])
  nlinarith only [hmhi, hu_sq, hsq, hup]

private theorem cast_le_cube (j : ℕ) : (j : ℝ) ≤ (j : ℝ)^3 := by
  by_cases h : j = 0
  · simp [h]
  have hn : 1 ≤ j := by omega
  have hcast : 1 ≤ (j : ℝ) := by exact_mod_cast hn
  have hx : 0 ≤ (j : ℝ) := by positivity
  calc
    (j : ℝ) ≤ (j : ℝ)*(j : ℝ) := by
      nlinarith only [mul_nonneg hx (sub_nonneg.mpr hcast)]
    _ ≤ (j : ℝ)^3 := by
      nlinarith only [mul_nonneg (sq_nonneg (j : ℝ)) (sub_nonneg.mpr hcast)]

/-- A cubic weighted error controls both the near diagonal and the far terms,
including the missing coefficients beyond the finite convolution. -/
private theorem pointwise_truncated_convolution_remainder
    (a : ℕ → ℝ) (m : ℕ) (D : ℝ) (hD : 0 < D) (hDcube : D ≤ (m : ℝ) ^ 3)
    (ha : ∀ n, |a n| ≤ 1)
    (hnear : ∀ j : ℕ, 2*j ≤ m → |a (m-j)-a m| ≤ 9*(j : ℝ)/D)
    (j : ℕ) :
    |(if j ≤ m then a (m-j) else 0) - a m| ≤ 16*(j : ℝ)^3/D := by
  by_cases near : 2*j ≤ m
  · have hlow : j ≤ m := by omega
    rw [ite_eq_left hlow]
    apply (hnear j near).trans
    apply div_le_div_of_nonneg_right _ hD.le
    have hj : 0 ≤ (j : ℝ) := by positivity
    linarith only [cast_le_cube j, hj]
  · have hfar : m < 2*j := by omega
    have hcast : (m : ℝ) < 2*(j : ℝ) := by exact_mod_cast hfar
    have hpow : (m : ℝ)^3 ≤ (2*(j : ℝ))^3 :=
      pow_le_pow_left₀ (by positivity) hcast.le 3
    have htwice : 2*D ≤ 16*(j : ℝ)^3 := by nlinarith only [hpow, hDcube]
    apply le_trans _ ((le_div_iff₀ hD).2 htwice)
    refine (show |(if j ≤ m then a (m-j) else 0) - a m| ≤
      |if j ≤ m then a (m-j) else (0 : ℝ)| + |a m| by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (if j ≤ m then a (m-j) else 0) 0 (a m))).trans ?_
    have htrunc : |if j ≤ m then a (m-j) else (0 : ℝ)| ≤ 1 := by
      split_ifs
      · exact ha _
      · simp
    linarith only [htrunc, ha m]

/-- A finite bound uniform in the truncation length N. The application to
the actual kernel takes limits only after establishing absolute summability. -/
private theorem finite_weighted_convolution_remainder
    (a b : ℕ → ℝ) (m N : ℕ) (D : ℝ) (hD : 0 < D) (hDcube : D ≤ (m : ℝ) ^ 3)
    (ha : ∀ n, |a n| ≤ 1)
    (hnear : ∀ j : ℕ, 2*j ≤ m → |a (m-j)-a m| ≤ 9*(j : ℝ)/D) :
    |∑ j ∈ Finset.range N, ((if j ≤ m then a (m-j) else 0) - a m) * b j| ≤
      (16/D) * ∑ j ∈ Finset.range N, (j : ℝ)^3 * |b j| := by
  calc
    _ ≤ ∑ j ∈ Finset.range N, |((if j ≤ m then a (m-j) else 0) - a m) * b j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N, (16/D) * ((j : ℝ)^3 * |b j|) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      have h := mul_le_mul_of_nonneg_right
        (pointwise_truncated_convolution_remainder a m D hD hDcube ha hnear j)
        (abs_nonneg (b j))
      convert h using 1
      ring
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Telescoping any j consecutive coefficients, with the exact Nat subtraction
indices used by the canonical convolution. -/
private theorem abs_sub_le_mul_of_adjacent (a : ℕ → ℝ) (m j : ℕ) (hj : j ≤ m) (K : ℝ)
    (h : ∀ i : ℕ, m-j ≤ i → i < m → |a i - a (i+1)| ≤ K) :
    |a (m-j) - a m| ≤ (j : ℝ) * K := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hj' : j ≤ m := by omega
    have hs : m-(j+1)+1 = m-j := by omega
    have ha := h (m-(j+1)) le_rfl (by omega)
    rw [hs] at ha
    have hb := ih hj' (fun i hi hi' => h i (by omega) hi')
    have ht := abs_sub_le (a (m-(j+1))) (a (m-j)) (a m)
    push_cast
    linarith only [ha, hb, ht]

private theorem shifted_cube_le_eight_pow (j : ℕ) :
    ((j : ℝ)+1)^3 ≤ (8 : ℝ)^j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [Nat.cast_succ, pow_succ (8 : ℝ) j]
    have hn : 0 ≤ (j : ℝ) + 1 := by positivity
    calc
      ((j : ℝ)+1+1)^3 ≤ (2*((j : ℝ)+1))^3 :=
        pow_le_pow_left₀ (by positivity) (by linarith only [show 0 ≤ (j : ℝ) by positivity]) _
      _ = 8*((j : ℝ)+1)^3 := by ring
      _ ≤ (8 : ℝ)^j * 8 := by linarith only [ih]

private theorem geometric_sum_barrier (r : ℝ) (hr : 0 ≤ r) (hr₁ : r ≤ 1 / 16) (N : ℕ) :
    (∑ j ∈ Finset.range N, r*(8*r)^j) + (8*r)^N/8 ≤ 1/8 := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    have hm : (8*r)^N * (2*r) ≤ (8*r)^N * (1/8) :=
      mul_le_mul_of_nonneg_left (by linarith only [hr₁]) (by positivity)
    rw [Finset.sum_range_succ, pow_succ (8*r) N]
    nlinarith only [hm, ih]

/-- The shifted finite cubic moments for r^j |a_j| are bounded by 1/8
uniformly in N. The omitted index j=0 contributes exactly zero. -/
private theorem finite_cubic_moment_cap (a : ℕ → ℝ) (ha : ∀ j, |a j| ≤ 1)
    (r : ℝ) (hr : 0 ≤ r) (hr₁ : r ≤ 1 / 16) (N : ℕ) :
    (∑ j ∈ Finset.range N, ((j : ℝ)+1)^3 * (|a (j+1)| * r^(j+1))) ≤ 1/8 := by
  have hsum : (∑ j ∈ Finset.range N, r*(8*r)^j) ≤ 1/8 := by
    have hn : 0 ≤ (8*r)^N/8 := by positivity
    linarith only [geometric_sum_barrier r hr hr₁ N, hn]
  apply le_trans _ hsum
  apply Finset.sum_le_sum
  intro j _
  calc
    _ ≤ ((j : ℝ)+1)^3 * (1 * r^(j+1)) := by
      gcongr
      exact ha _
    _ ≤ (8 : ℝ)^j * (1 * r^(j+1)) :=
      mul_le_mul_of_nonneg_right (shifted_cube_le_eight_pow j) (by positivity)
    _ = r * (8*r)^j := by rw [mul_pow, pow_succ r]; ring

/-- With exponential tilting at r≤1/16, the strict convolution error has no
hidden asymptotic factor. Truncation past degree m is controlled too. -/
private theorem exponential_convolution_remainder
    (a : ℕ → ℝ) (m : ℕ) (D : ℝ) (hD : 0 < D) (hDcube : D ≤ (m : ℝ) ^ 3)
    (ha : ∀ n, |a n| ≤ 1)
    (hnear : ∀ j : ℕ, 2*j ≤ m → |a (m-j)-a m| ≤ 9*(j : ℝ)/D)
    (r : ℝ) (hr : 0 ≤ r) (hr₁ : r ≤ 1 / 16) :
    |(∑ j ∈ Finset.range (m+1), a (m-j) * (a j * r ^ j)) -
      a m * (∑' j, a j * r ^ j)| ≤ 2/D := by
  let b (j : ℕ) := a j * r^j
  let F (j : ℕ) := if j ≤ m then a (m-j) else 0
  let K := ∑ j ∈ Finset.range (m+1), a (m-j)*b j
  have hb : Summable b := by
    apply (summable_geometric_of_lt_one hr (show r < 1 by linarith only [hr₁])).of_norm_bounded
    intro j
    change ‖a j * r^j‖ ≤ r^j
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hr _)]
    exact (mul_le_mul_of_nonneg_right (ha j) (pow_nonneg hr _)).trans_eq (one_mul _)
  have hcap (N : ℕ) : (∑ j ∈ Finset.range N, (j : ℝ)^3 * |b j|) ≤ 1/8 := by
    cases N with
    | zero => norm_num
    | succ N =>
      rw [Finset.sum_range_succ']
      simpa only [b, abs_mul, abs_of_nonneg (pow_nonneg hr _), Nat.cast_succ,
        Nat.cast_zero, zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, add_zero] using
        finite_cubic_moment_cap a ha r hr hr₁ N
  have hfinite (N : ℕ) :
      |∑ j ∈ Finset.range N, (F j - a m)*b j| ≤ 2/D := by
    apply (finite_weighted_convolution_remainder a b m N D hD hDcube ha hnear).trans
    calc
      _ ≤ (16/D) * (1/8) :=
        mul_le_mul_of_nonneg_left (hcap N) (by positivity)
      _ = 2/D := by ring
  have hz :
      (fun N : ℕ => ∑ j ∈ Finset.range N, (F j-a m)*b j) =ᶠ[atTop]
        (fun N : ℕ => K-a m*(∑ j ∈ Finset.range N, b j)) := by
    filter_upwards [eventually_ge_atTop (m+1)] with N hN
    have hsum : (∑ j ∈ Finset.range N, F j*b j) = K := by
      rw [← Finset.sum_subset (Finset.range_mono hN)
        (fun j _ hj => show F j * b j = 0 by
          have ht : ¬j ≤ m := by exact fun h => hj (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
          simp [F, ht])]
      apply Finset.sum_congr rfl
      intro j hj
      have ht := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      simp only [F, ite_eq_left ht]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, hsum, ← Finset.mul_sum]
  have hlim : Tendsto
      (fun N : ℕ => ∑ j ∈ Finset.range N, (F j-a m)*b j) atTop
      (𝓝 (K-a m*(∑' j, b j))) :=
    (tendsto_const_nhds.sub (tendsto_const_nhds.mul hb.hasSum.tendsto_sum_nat)).congr' hz.symm
  exact le_of_tendsto hlim.abs (Eventually.of_forall hfinite)

private noncomputable def kernelDenom (n : ℕ) : ℝ := (n:ℝ)^2 * Real.sqrt n

private theorem kernelDenom_pos {n : ℕ} (hn : 1 ≤ n) : 0 < kernelDenom n := by
  have hp : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  unfold kernelDenom
  positivity

private theorem kernelDenom_le_cube {n : ℕ} (hn : 1 ≤ n) : kernelDenom n ≤ (n:ℝ)^3 := by
  have hp : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hs : Real.sqrt n ≤ (n : ℝ) := (Real.sqrt_le_left (by positivity)).2 (by
    nlinarith only [hp, mul_nonneg (show 0 ≤ (n : ℝ) by positivity) (sub_nonneg.mpr hp)])
  unfold kernelDenom
  exact (mul_le_mul_of_nonneg_left hs (sq_nonneg _)).trans_eq (by ring)

private theorem kernelDenom_le_six {m l : ℕ} (h : m ≤ 2 * l) :
    kernelDenom m ≤ 6*kernelDenom l := by
  have hm : (m:ℝ) ≤ 2*(l:ℝ) := by exact_mod_cast h
  have hs : Real.sqrt m ≤ (3/2:ℝ)*Real.sqrt l :=
    (Real.sqrt_le_left (by positivity)).2 (by
      have hl : 0 ≤ (l : ℝ) := by positivity
      nlinarith only [hm, Real.sq_sqrt hl, hl])
  have hp : (m:ℝ)^2 ≤ (2*(l:ℝ))^2 := pow_le_pow_left₀ (by positivity) hm _
  unfold kernelDenom
  exact (mul_le_mul hp hs (Real.sqrt_nonneg _) (by positivity)).trans_eq (by ring)

private theorem near_of_signed_step
    (a : ℕ → ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hcoeff : ∀ n : ℕ, 1 ≤ n → 0 ≤ -a n ∧ -a n ≤ 1/((n:ℝ)*Real.sqrt n))
    (hstep : ∀ n : ℕ, 1 ≤ n → a (n+1)-a n = (3/(2*((n:ℝ)+1)))*(-a n))
    (j : ℕ) (hj : 2*j ≤ m) :
    |a (m-j)-a m| ≤ 9*(j:ℝ)/kernelDenom m := by
  have hmpos : 1 ≤ m := by omega
  have H : |a (m-j)-a m| ≤ (j:ℝ)*(9/kernelDenom m) := by
    apply abs_sub_le_mul_of_adjacent a m j (by omega)
    intro l hl hlm
    have hl₁ : 1 ≤ l := by omega
    have hmpl : m ≤ 2*l := by omega
    have hlp : 0 < (l:ℝ) := by exact_mod_cast (show 0 < l by omega)
    have hls : 0 < Real.sqrt l := by positivity
    have hden := kernelDenom_le_six hmpl
    rw [abs_sub_comm, hstep l hl₁, abs_of_nonneg (mul_nonneg (by positivity) (hcoeff l hl₁).1)]
    calc
      _ ≤ (3/(2*((l:ℝ)+1)))*(1/((l:ℝ)*Real.sqrt l)) :=
        mul_le_mul_of_nonneg_left (hcoeff l hl₁).2 (by positivity)
      _ ≤ ((3/2)/(l:ℝ)) * (1/((l:ℝ)*Real.sqrt l)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply (div_le_div_iff₀ (by positivity : 0 < (2*((l:ℝ)+1))) hlp).2
        linarith
      _ = (3/2)/kernelDenom l := by unfold kernelDenom; ring
      _ ≤ 9/kernelDenom m := (div_le_div_iff₀
        (kernelDenom_pos hl₁) (kernelDenom_pos hmpos)).2 (by linarith only [hden])
  convert H using 1
  ring

/-- Complete remainder once the exact normalized-root coefficient and its
central-profile error are supplied. In particular this is not a fit to a
numeric kernel. The first jump is intentionally outside the theorem. -/
private theorem strict_kernel_remainder_of_root_data
    (a κ : ℕ → ℝ) (r U A : ℝ)
    (hr : 0 ≤ r) (hr₁ : r ≤ 1 / 16) (hA : 0 ≤ A ∧ A ≤ 1)
    (hAeq : A = ∑' j, a j * r ^ j)
    (ha : ∀ n, |a n| ≤ 1)
    (hcoeff : ∀ n : ℕ, 1 ≤ n → 0 ≤ -a n ∧ -a n ≤ 1/((n:ℝ)*Real.sqrt n))
    (hstep : ∀ n : ℕ, 1 ≤ n → a (n+1)-a n = (3/(2*((n:ℝ)+1)))*(-a n))
    (hprofile : ∀ n : ℕ, 1 ≤ n →
      |(-a n)*(n:ℝ)*Real.sqrt n-U/2| ≤ 5/(8*(n:ℝ)))
    (hexact : ∀ n : ℕ, 2 ≤ n → κ n = -(1/2:ℝ) *
      ∑ j ∈ Finset.range (n+1), a (n-j)*(a j * r ^ j))
    (m : ℕ) (hm : 2 ≤ m) :
    |κ m-(A*U/4)/((m:ℝ)*Real.sqrt m)| ≤ (21/16)/((m:ℝ)^2*Real.sqrt m) := by
  have hm₁ : 1 ≤ m := by omega
  have hp : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hs : 0 < Real.sqrt m := by positivity
  let D := kernelDenom m
  have hD : 0 < D := kernelDenom_pos hm₁
  have hz := exponential_convolution_remainder a m D hD (kernelDenom_le_cube hm₁)
    ha (near_of_signed_step a m hm hcoeff hstep) r hr hr₁
  rw [← hAeq] at hz
  have hkernel : |κ m - (A/2)*(-a m)| ≤ 1/D := by
    rw [hexact m hm, show -(1/2:ℝ) * (∑ j ∈ Finset.range (m+1), a (m-j)*(a j * r ^ j)) -
      A/2*(-a m) = -(1/2:ℝ) * ((∑ j ∈ Finset.range (m+1), a (m-j)*(a j * r ^ j))-a m*A)
      by ring, abs_mul]
    rw [abs_of_nonpos (show -(1/2:ℝ) ≤ 0 by norm_num), neg_neg]
    exact (mul_le_mul_of_nonneg_left hz (show 0 ≤ (1/2:ℝ) by norm_num)).trans_eq (by ring)
  have hmid : |(A/2)*(-a m) - (A*U/4)/((m:ℝ)*Real.sqrt m)| ≤ (5/16)/D := by
    have heq : (A/2)*(-a m) - (A*U/4)/((m:ℝ)*Real.sqrt m) =
        (A/2)*(((-a m)*(m:ℝ)*Real.sqrt m-U/2)/((m:ℝ)*Real.sqrt m)) := by
      field_simp [hp.ne', hs.ne']
      ring
    rw [heq, abs_mul, abs_of_nonneg (by linarith only [hA.1]), abs_div,
      abs_of_pos (mul_pos hp hs)]
    have hv := div_le_div_of_nonneg_right (hprofile m hm₁) (mul_pos hp hs).le
    calc
      _ ≤ (A/2)*((5/(8*(m:ℝ)))/((m:ℝ)*Real.sqrt m)) :=
        mul_le_mul_of_nonneg_left hv (by linarith only [hA.1])
      _ ≤ (1/2:ℝ)*((5/(8*(m:ℝ)))/((m:ℝ)*Real.sqrt m)) :=
        mul_le_mul_of_nonneg_right (by linarith only [hA.2]) (by positivity)
      _ = (5/16)/D := by
        unfold D kernelDenom
        field_simp [hp.ne', hs.ne']
        ring
  have ht := (abs_sub_le (κ m) ((A/2)*(-a m)) ((A*U/4)/((m:ℝ)*Real.sqrt m))).trans
    (add_le_add hkernel hmid)
  calc
    _ ≤ 1/D+(5/16)/D := ht
    _ = _ := by unfold D kernelDenom; ring

/-- Turn the exact central-profile formula into the signed decrement bound
and into the explicit normalized 5/(8n) error. -/
private theorem central_root_data
    (a u : ℕ → ℝ) (U : ℝ) (hU : 0 ≤ U ∧ U ≤ 1) (ha₀ : a 0 = 1)
    (hu : ∀ n : ℕ, 1 ≤ n → 0 ≤ u n ∧ u n ≤ U ∧ U-u n ≤ 1/(8*(n:ℝ)))
    (hformula : ∀ n : ℕ, 1 ≤ n →
      -a n = u n/(Real.sqrt n*(2*(n:ℝ)-1))) :
    (∀ n, |a n| ≤ 1) ∧
    (∀ n : ℕ, 1 ≤ n → 0 ≤ -a n ∧ -a n ≤ 1/((n:ℝ)*Real.sqrt n)) ∧
    ∀ n : ℕ, 1 ≤ n → |(-a n)*(n:ℝ)*Real.sqrt n-U/2| ≤ 5/(8*(n:ℝ)) := by
  have hcoeff (n : ℕ) (hn : 1 ≤ n) :
      0 ≤ -a n ∧ -a n ≤ 1/((n:ℝ)*Real.sqrt n) := by
    have hnp : 1 ≤ (n:ℝ) := by exact_mod_cast hn
    have hn₂ : 0 < 2*(n:ℝ)-1 := by linarith only [hnp]
    have hs : 0 < Real.sqrt n := by positivity
    have hup := (hu n hn).2.1.trans hU.2
    rw [hformula n hn]
    refine ⟨div_nonneg (hu n hn).1 (by positivity), ?_⟩
    calc
      _ ≤ 1/(Real.sqrt n*(2*(n:ℝ)-1)) :=
        div_le_div_of_nonneg_right hup (by positivity)
      _ ≤ 1/((n:ℝ)*Real.sqrt n) := by
        apply one_div_le_one_div_of_le (by positivity)
        rw [mul_comm (n:ℝ)]
        exact mul_le_mul_of_nonneg_left (by linarith only [hnp]) hs.le
  refine ⟨?_, hcoeff, ?_⟩
  · intro n
    by_cases hn : n = 0
    · simp [hn, ha₀]
    · have hn₁ : 1 ≤ n := by omega
      have hx : 1 ≤ (n:ℝ) := by exact_mod_cast hn₁
      have hs : 1 ≤ Real.sqrt n := by simpa using Real.sqrt_le_sqrt hx
      have hd : 1 ≤ (n:ℝ)*Real.sqrt n := by
        have h : 1*1 ≤ (n:ℝ)*Real.sqrt n := mul_le_mul hx hs (by norm_num) (by positivity)
        simpa using h
      have hb := hcoeff n hn₁
      rw [abs_of_nonpos (by linarith only [hb.1])]
      exact hb.2.trans ((div_le_iff₀ (by positivity : 0 < (n:ℝ)*Real.sqrt n)).2 (by simpa using hd))
  · intro n hn
    let x := (n:ℝ)
    have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast hn
    have hxpos : 0 < x := by linarith only [hx]
    have hden : 0 < 2*x-1 := by linarith only [hx]
    have hs : 0 < Real.sqrt n := by positivity
    let q := x/(2*x-1)
    have hq₀ : 0 ≤ q := by dsimp [q]; positivity
    have hq₁ : q ≤ 1 := (div_le_iff₀ hden).2 (by linarith only [hx])
    have hqdiff : q-1/2 = 1/(2*(2*x-1)) := by
      have hk : q*(2*x-1)=x := div_mul_cancel₀ x hden.ne'
      apply (eq_div_iff (show 2*(2*x-1) ≠ 0 by positivity)).2
      calc
        _ = 2*(q*(2*x-1))-(2*x-1) := by ring
        _ = 1 := by rw [hk]; ring
    have hqdiff₀ : 0 ≤ q-1/2 := by rw [hqdiff]; positivity
    have hqdiff₁ : q-1/2 ≤ 1/(2*x) := by
      rw [hqdiff]
      exact one_div_le_one_div_of_le (by positivity) (by linarith only [hx])
    have hform : (-a n)*x*Real.sqrt n = u n*q := by
      rw [hformula n hn]
      change u n / (Real.sqrt n * (2*x-1))*x*Real.sqrt n = _
      unfold q
      field_simp [hden.ne', hs.ne']
    have huu := hu n hn
    have hleft : |u n*q-U*q| ≤ 1/(8*x) := by
      rw [← sub_mul, abs_mul, abs_of_nonpos (sub_nonpos.mpr huu.2.1), abs_of_nonneg hq₀]
      rw [show -(u n-U)=U-u n by ring]
      calc
        _ ≤ (U-u n)*1 := mul_le_mul_of_nonneg_left hq₁ (sub_nonneg.mpr huu.2.1)
        _ ≤ _ := by rw [mul_one]; exact huu.2.2
    have hright : |U*q-U/2| ≤ 1/(2*x) := by
      rw [show U*q-U/2=U*(q-1/2) by ring, abs_of_nonneg (mul_nonneg hU.1 hqdiff₀)]
      calc
        _ ≤ 1*(q-1/2) := mul_le_mul_of_nonneg_right hU.2 hqdiff₀
        _ ≤ _ := by rw [one_mul]; exact hqdiff₁
    change |(-a n)*x*Real.sqrt n-U/2| ≤ 5/(8*x)
    rw [hform]
    calc
      _ ≤ _ := abs_sub_le (u n*q) (U*q) (U/2)
      _ ≤ 1/(8*x)+1/(2*x) := add_le_add hleft hright
      _ = _ := by ring

/-- Elementary explicit tilt cap for the actual Schröder critical parameter. -/
private theorem actual_tilt_cap_numeric :
    let b : ℝ := Real.sqrt 2-1
    let ρ := b^2
    0 < ρ^2 ∧ ρ^2 ≤ 1/16 := by
  dsimp
  have hsq : Real.sqrt (2:ℝ)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : 0 ≤ Real.sqrt (2:ℝ) := Real.sqrt_nonneg _
  have hb : 0 < Real.sqrt (2:ℝ)-1 := by nlinarith only [hsq, hs]
  have hb' : Real.sqrt (2:ℝ)-1 ≤ 1/2 := by nlinarith only [hsq, hs]
  refine ⟨by positivity, ?_⟩
  have hρ : (Real.sqrt (2:ℝ)-1)^2 ≤ (1/2:ℝ)^2 :=
    pow_le_pow_left₀ hb.le hb' _
  have hr := pow_le_pow_left₀ (sq_nonneg (Real.sqrt (2:ℝ)-1)) hρ 2
  norm_num at hr
  exact hr

/-- Positivity of the leading constant needs no Cauchy-product theorem:
the size of the entire negative tail is at most the cubic moment 1/8. -/
private theorem signed_tilt_sum_bounds (a : ℕ → ℝ) (ha : ∀ n, |a n| ≤ 1)
    (hzero : a 0 = 1) (hsign : ∀ n : ℕ, 1 ≤ n → a n ≤ 0)
    (r : ℝ) (hr : 0 ≤ r) (hr₁ : r ≤ 1 / 16) :
    7/8 ≤ (∑' j, a j * r ^ j) ∧ (∑' j, a j * r ^ j) ≤ 1 := by
  let p (j : ℕ) := a j*r^j
  have hsum : Summable p := by
    apply (summable_geometric_of_lt_one hr (show r<1 by linarith only [hr₁])).of_norm_bounded
    intro j
    rw [show p j=a j*r^j by rfl, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hr _)]
    exact (mul_le_mul_of_nonneg_right (ha j) (pow_nonneg hr _)).trans_eq (one_mul _)
  have hneg (j : ℕ) : p (j + 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (hsign _ (by omega)) (pow_nonneg hr _)
  have hb (N : ℕ) : -(∑ j ∈ Finset.range N, p (j+1)) ≤ 1/8 := by
    rw [← Finset.sum_neg_distrib]
    apply le_trans _ (finite_cubic_moment_cap a ha r hr hr₁ N)
    apply Finset.sum_le_sum
    intro j _
    have hj : 1 ≤ ((j:ℝ)+1) := by linarith only [show 0 ≤ (j:ℝ) by positivity]
    have hj₃ : 1 ≤ ((j:ℝ)+1)^3 := by
      simpa using pow_le_pow_left₀ (show 0 ≤ (1:ℝ) by norm_num) hj 3
    have hk : -p (j+1) = |a (j+1)| * r^(j+1) := by
      dsimp only [p]
      rw [abs_of_nonpos (hsign _ (by omega)), neg_mul]
    rw [hk]
    have hprod : 0 ≤ |a (j + 1)| * r ^ (j + 1) := by positivity
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hj₃ hprod
  have hf (N : ℕ) :
      7/8 ≤ (∑ j ∈ Finset.range (N+1), p j) ∧
      (∑ j ∈ Finset.range (N+1), p j) ≤ 1 := by
    rw [Finset.sum_range_succ']
    have hz : p 0 = 1 := by simp [p,hzero]
    have hh : (∑ j ∈ Finset.range N, p (j+1)) ≤ 0 :=
      Finset.sum_nonpos (fun j _ => hneg j)
    constructor <;> linarith only [hb N, hh, hz]
  refine ⟨ge_of_tendsto hsum.hasSum.tendsto_sum_nat ?_,
    le_of_tendsto hsum.hasSum.tendsto_sum_nat ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with N hN
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    exact (hf j).1
  · filter_upwards [eventually_ge_atTop 1] with N hN
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    exact (hf j).2

/-- All estimates discharged from exact signed-root data alone; C is strictly
positive. The remaining inputs are algebraic coefficient statements, not bounds
on an unknown kernel or assumptions on its decay. -/
private theorem coefficient_remainder_from_exact_normalization
    (a u κ : ℕ → ℝ) (r U : ℝ)
    (hr : 0 ≤ r) (hr₁ : r ≤ 1 / 16) (hU : 0 < U ∧ U ≤ 1)
    (hzero : a 0 = 1)
    (hu : ∀ n : ℕ, 1 ≤ n → 0 ≤ u n ∧ u n ≤ U ∧ U-u n ≤ 1/(8*(n:ℝ)))
    (hformula : ∀ n : ℕ, 1 ≤ n → -a n = u n/(Real.sqrt n*(2*(n:ℝ)-1)))
    (hstep : ∀ n : ℕ, 1 ≤ n → a (n+1)-a n = (3/(2*((n:ℝ)+1)))*(-a n))
    (hexact : ∀ n : ℕ, 2 ≤ n → κ n = -(1/2:ℝ) *
      ∑ j ∈ Finset.range (n+1), a (n-j)*(a j * r ^ j)) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m →
      |κ m-C/((m:ℝ)*Real.sqrt m)| ≤ (21/16)/((m:ℝ)^2*Real.sqrt m) := by
  obtain ⟨ha, hc, hp⟩ := central_root_data a u U ⟨hU.1.le,hU.2⟩ hzero hu hformula
  let A := ∑' j, a j*r^j
  have hb := signed_tilt_sum_bounds a ha hzero
    (fun n hn => by linarith only [(hc n hn).1]) r hr hr₁
  have hA : 0 < A := by dsimp [A]; linarith only [hb.1]
  refine ⟨A*U/4, div_pos (mul_pos hA hU.1) (by norm_num), ?_⟩
  exact strict_kernel_remainder_of_root_data a κ r U A hr hr₁
    ⟨hA.le, hb.2⟩ rfl ha hc hstep hp hexact

/-- Signed binomial coefficients for the constant-one formal square root of `1 - X`. -/
private noncomputable def explicitRootCoeff : ℕ → ℝ
  | 0 => 1
  | n+1 => -(Nat.centralBinom (n+1) : ℝ) /
      (4^(n+1)*(2*((n+1 : ℕ) : ℝ)-1))

private theorem explicitRootCoeff_normalized (n : ℕ) (hn : 1 ≤ n) :
    -explicitRootCoeff n = centralProfile n/(Real.sqrt n*(2*(n:ℝ)-1)) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hn : 0 < ((j+1 : ℕ) : ℝ) := by positivity
  have hs : 0 < Real.sqrt (j+1 : ℕ) := by positivity
  have hd : 0 < 2*((j+1:ℕ):ℝ)-1 := by
    have : 1 ≤ ((j+1:ℕ):ℝ) := by exact_mod_cast (show 1 ≤ j+1 by omega)
    linarith
  simp only [explicitRootCoeff, neg_div, neg_neg, centralProfile, scaledBinom]
  field_simp [hd.ne', hs.ne']

private theorem explicitRootCoeff_ratio (n : ℕ) (hn : 1 ≤ n) :
    explicitRootCoeff (n + 1) =
      ((2 * (n : ℝ) - 1) / (2 * ((n : ℝ) + 1))) * explicitRootCoeff n := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let x : ℝ := ((j+1:ℕ):ℝ)
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ j+1 by omega)
  have hx1 : x+1 ≠ 0 := by linarith
  have hx2 : 2*x-1 ≠ 0 := by linarith
  have hx3 : 2*(x+1)-1 ≠ 0 := by linarith
  have hc : (x+1) * (Nat.centralBinom ((j+1)+1) : ℝ) =
      2 * (2*x+1) * (Nat.centralBinom (j+1) : ℝ) := by
    dsimp [x]
    exact_mod_cast Nat.succ_mul_centralBinom_succ (j+1)
  simp only [explicitRootCoeff]
  rw [Nat.cast_succ (j+1)]
  change -(Nat.centralBinom ((j+1)+1) : ℝ) / (4^((j+1)+1)*(2*(x+1)-1)) =
    ((2*x-1)/(2*(x+1))) *
      (-(Nat.centralBinom (j+1) : ℝ)/(4^(j+1)*(2*x-1)))
  rw [pow_succ (4:ℝ) (j+1)]
  field_simp [hx1,hx2,hx3]
  nlinarith only [hc]

private theorem explicitRootCoeff_step (n : ℕ) (hn : 1 ≤ n) :
    explicitRootCoeff (n + 1) - explicitRootCoeff n =
      (3 / (2 * ((n : ℝ) + 1))) * (-explicitRootCoeff n) := by
  rw [explicitRootCoeff_ratio n hn]
  field_simp [show (n : ℝ) + 1 ≠ 0 by positivity]
  ring

private def canonicalRoot : PowerSeries ℝ :=
  rescale (-1 : ℝ) (binomialSeries ℝ (1 / 2 : ℝ))

private theorem canonicalRoot_constant : constantCoeff canonicalRoot = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, canonicalRoot, coeff_rescale, pow_zero, one_mul,
    coeff_zero_eq_constantCoeff_apply, binomialSeries_constantCoeff]

private theorem canonicalRoot_square : canonicalRoot ^ 2 = 1 - X := by
  unfold canonicalRoot
  rw [← map_pow, pow_two, ← binomialSeries_add,
    show (1 / 2 : ℝ) + 1 / 2 = ((1 : ℕ) : ℝ) by norm_num, binomialSeries_nat]
  simp [rescale_X, sub_eq_add_neg]

private theorem canonicalRoot_coeff_step (n : ℕ) :
    ((n : ℝ) + 1) * coeff (n + 1) canonicalRoot =
      ((n : ℝ) - 1 / 2) * coeff n canonicalRoot := by
  have h := Ring.choose_smul_choose (1 / 2 : ℝ) (n := n + 1) (k := n) (by omega)
  rw [Nat.choose_succ_self_right, show n + 1 - n = 1 by omega,
    Ring.choose_one_right, nsmul_eq_mul, Nat.cast_succ] at h
  simp only [canonicalRoot, coeff_rescale, binomialSeries_coeff, smul_eq_mul, mul_one, pow_succ]
  linear_combination -((-1 : ℝ) ^ n) * h

private abbrev S : PowerSeries ℝ :=
  PowerSeries.largeSchroderSeries.map (Nat.castRingHom ℝ)

/-- Critical normalization is by actual block length, not shifted index. -/
private def normalizedB : PowerSeries ℝ :=
  rescale rho ((X * PowerSeries.largeSchroderSeries).map (Nat.castRingHom ℝ))

private theorem normalizedB_coeff (n : ℕ) :
    coeff (n+1) normalizedB = shapeWeight n := by
  rw [normalizedB, coeff_rescale, coeff_map,
    coeff_X_mul_largeSchroderSeries _ (by omega)]
  simp only [Nat.add_sub_cancel, shapeWeight,
    actual_schroder_cardinality.2.1 (n+1) (by omega)]
  rfl

private theorem normalizedB_quadratic :
    normalizedB = C rho * X + (C rho * X) * normalizedB + normalizedB ^ 2 := by
  have hs : S = 1 + X * S + X * S^2 := by
    have h := congrArg (PowerSeries.map (Nat.castRingHom ℝ))
      largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq
    simpa only [map_add, map_one, map_mul, map_pow, PowerSeries.map_X, S] using h
  have hg : X*S = X + X*(X*S) + (X*S)^2 := by
    linear_combination X*hs
  have hr := congrArg (rescale rho) hg
  simpa only [normalizedB, map_mul, map_add, map_pow, PowerSeries.map_X, rescale_X, S] using hr

private theorem rho_discriminant : 1 + rho^2 = 6*rho := by
  have hsq : Real.sqrt (2:ℝ)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hρ : rho = 3 - 2*Real.sqrt (2:ℝ) := by
    unfold rho b
    nlinarith
  rw [hρ]
  nlinarith

private def normalizedDiscriminantRoot : PowerSeries ℝ := 1 - C rho * X - 2*normalizedB

private theorem normalizedDiscriminantRoot_square :
    normalizedDiscriminantRoot ^ 2 = (1-X)*(1-C (rho^2)*X) := by
  have hρ : (C (1:ℝ) + C (rho^2) : PowerSeries ℝ) = 6 * C rho := by
    calc
      _ = C (1 + rho^2) := (map_add C _ _).symm
      _ = C (6*rho) := congrArg C rho_discriminant
      _ = _ := by
        have h6 : C (6:ℝ) = (6:PowerSeries ℝ) := map_natCast C 6
        rw [map_mul, h6]
  have hh : (1:PowerSeries ℝ) + C (rho^2) = 6 * C rho := by simpa using hρ
  unfold normalizedDiscriminantRoot
  have hp : (C (rho^2) : PowerSeries ℝ) = (C rho)^2 := map_pow C _ _
  linear_combination -4*normalizedB_quadratic + X*hh - X^2*hp

private theorem normalizedDiscriminantRoot_constant :
    constantCoeff normalizedDiscriminantRoot = 1 := by
  simp [normalizedDiscriminantRoot, normalizedB]

/-- For a normalized formal square root of 1-X, the actual critical
kernel tail is its rescaled coefficient convolution, with no singleton
correction for block lengths ≥ 2. -/
private theorem normalized_kernel_tail_convolution (R : PowerSeries ℝ)
    (hR : R ^ 2 = 1 - X) (hR0 : constantCoeff R = 1) (n : ℕ) :
    kernelWeight (n+1) = -(1/2 : ℝ) *
      ∑ p ∈ Finset.antidiagonal (n+2), coeff p.1 R *
        (rho^2)^p.2 * coeff p.2 R := by
  have hrs : (rescale (rho^2) R)^2 = 1-C (rho^2)*X := by
    have hv := congrArg (rescale (rho^2)) hR
    simpa only [map_pow, map_sub, map_one, rescale_X] using hv
  let Q := R * rescale (rho^2) R
  have hq : Q^2 = (1-X)*(1-C (rho^2)*X) := by
    dsimp [Q]
    rw [mul_pow, hR, hrs]
  have hrc : constantCoeff (rescale (rho^2) R) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
      coeff_zero_eq_constantCoeff_apply, hR0]
  have hq0 : constantCoeff Q = 1 := by simp [Q, hR0, hrc]
  have hsame : normalizedDiscriminantRoot = Q := by
    have hz : (normalizedDiscriminantRoot-Q)*(normalizedDiscriminantRoot+Q)=0 := by
      rw [mul_comm, ← sq_sub_sq, normalizedDiscriminantRoot_square, hq, sub_self]
    rcases mul_eq_zero.mp hz with hs | hs
    · exact sub_eq_zero.mp hs
    · have h0 : constantCoeff (normalizedDiscriminantRoot+Q) = (2 : ℝ) := by
        rw [map_add, normalizedDiscriminantRoot_constant, hq0]
        norm_num
      rw [hs, map_zero] at h0
      norm_num at h0
  have h := congrArg (coeff (n+2)) hsame
  have hc : coeff (n+2) normalizedDiscriminantRoot = -2 * shapeWeight (n+1) := by
    unfold normalizedDiscriminantRoot
    rw [map_sub, map_sub, coeff_one, coeff_C_mul, coeff_X]
    rw [show (2 : PowerSeries ℝ) * normalizedB = C (2 : ℝ) * normalizedB by rw [map_ofNat]]
    rw [coeff_C_mul, show n+2=(n+1)+1 by omega, normalizedB_coeff]
    simp
  rw [hc] at h
  simp only [Q, coeff_mul, coeff_rescale, ← mul_assoc] at h
  simp only [kernelWeight, Nat.succ_ne_zero, ite_false, add_zero]
  linarith only [h]

private theorem canonicalRoot_coeff (n : ℕ) : coeff n canonicalRoot = explicitRootCoeff n := by
  induction n with
  | zero =>
    simpa only [coeff_zero_eq_constantCoeff_apply, explicitRootCoeff] using canonicalRoot_constant
  | succ n ih =>
    have hs := canonicalRoot_coeff_step n
    rw [ih] at hs
    cases n with
    | zero =>
      simp only [explicitRootCoeff, Nat.cast_zero] at hs
      norm_num [explicitRootCoeff, Nat.centralBinom, Nat.choose] at *
      linarith
    | succ n =>
      rw [explicitRootCoeff_ratio (n + 1) (by omega)]
      have hp : ((n + 1 : ℕ) : ℝ) + 1 ≠ 0 := by positivity
      apply (mul_left_cancel₀ hp)
      rw [hs]
      field_simp [hp]

/-- The actual kernel at every jump of length at least two. Length one has
the distinct singleton term rho/2 in the definition of `kernelWeight`. -/
theorem actual_kernel_weight_strict_remainder :
    ∃ C > (0 : ℝ), ∀ m : ℕ, 2 ≤ m →
      |kernelWeight (m - 1) - C / ((m : ℝ) * Real.sqrt m)| ≤
        (21 / 16) / ((m : ℝ)^2 * Real.sqrt m) := by
  let r : ℝ := (rho ^ 2)
  have hr : 0 < r ∧ r ≤ 1 / 16 := actual_tilt_cap_numeric
  obtain ⟨U, hUlo, hUsq, _, hu⟩ := centralProfile_limit_with_remainder
  have hU : 0 < U ∧ U ≤ 1 := by
    constructor
    · linarith only [hUlo]
    · nlinarith only [hUlo, hUsq]
  apply coefficient_remainder_from_exact_normalization explicitRootCoeff centralProfile
    (fun m => kernelWeight (m - 1)) r U
    hr.1.le hr.2 hU rfl
  · intro n hn
    have hp : 0 ≤ centralProfile n := by unfold centralProfile scaledBinom; positivity
    exact ⟨hp, sub_nonneg.mp (hu n hn).1, (hu n hn).2⟩
  · exact explicitRootCoeff_normalized
  · exact explicitRootCoeff_step
  · intro n hn
    have hx : kernelWeight (n - 1) = -(1 / 2 : ℝ) *
        ∑ p ∈ Finset.antidiagonal n, explicitRootCoeff p.1 *
          r ^ p.2 * explicitRootCoeff p.2 := by
      obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = j + 2 := ⟨n - 2, by omega⟩
      rw [show j + 2 - 1 = j + 1 by omega]
      simpa only [canonicalRoot_coeff] using
        normalized_kernel_tail_convolution canonicalRoot canonicalRoot_square
          canonicalRoot_constant j
    rw [hx]
    congr 1
    have hm := Finset.Nat.sum_antidiagonal_swap
      (n := n) (f := fun p => explicitRootCoeff p.1 * r ^ p.2 * explicitRootCoeff p.2)
    rw [← hm]
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => explicitRootCoeff j * r ^ i * explicitRootCoeff i) n]
    apply Finset.sum_congr rfl
    intro i hi
    ring

end
end D5.S1.Words.Patterns.Separable.OccupiedKernelCoefficient
