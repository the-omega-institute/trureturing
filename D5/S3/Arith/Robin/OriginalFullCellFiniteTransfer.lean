/- GID: D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/OriginalFullCellFiniteTransfer
   mirror-E: none(waiver:finite-analytic-inequality)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Moebius, mathlib/module/Mathlib.Algebra.BigOperators.Module]
   utility: none
   digest: The unchanged actual Mobius response has finite full-positive transfer with its nonzero integer mean, full first moment, both variation jumps and exact pole-centered prefix. -/

import D5.S3.Arith.Robin.OriginalResidualFiniteTransfer

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
open scoped BigOperators

namespace D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer

open D5.S3.Arith.Robin.ActualOddMobiusFinitePairing (mobiusPrefix prefix_abel)
open D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
  (response variation variation_nonneg centered centered_floor centered_pair_variation_bound centered_pair_variation_sharp_bound weighted_floor_bound
   reciprocal_log_step weighted_log_step log_bounds prefix_bound sum_indices prefix_error_bound)

/-- Total coefficient, without a vanishing-moment condition. -/
def totalMass (N : ℕ) (b : ℕ → ℝ) : ℝ := ∑ m ∈ Ico N (2 * N), b m

/-- The complete first moment on the original integer block. -/
def firstMoment (N : ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Ico N (2 * N), (m : ℝ)*b m

/-- At positive d, the remainder quotient is the literal fractional part of m/d. -/
def fracPair (N : ℕ) (b : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ m ∈ Ico N (2 * N), b m*((m % d : ℕ)/(d : ℝ))

def logPair (N : ℕ) (b : ℕ → ℝ) (d : ℕ) : ℝ :=
  Real.log ((N : ℝ)/d)*fracPair N b d

def logDifference (N : ℕ) (b : ℕ → ℝ) (k : ℕ) : ℝ :=
  logPair N b k-logPair N b (k+1)

def weightedVariation (N h : ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Ico h N, (k : ℝ)*|logDifference N b k|

/-- Pairing with the unchanged affine-and-floor response. -/
def pairing (N : ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Ico N (2 * N), b m*response N m

/-- The positive Abel convention retains the literal constant +2. -/
def replacement (N q : ℕ) (b F : ℕ → ℝ) : ℝ :=
  (∑ k ∈ Ico (q + 1) N, (F k+2)*logDifference N b k)/Real.log N

/-- The actual finite pole-centered logarithmic Mobius prefix at h=q + 1. -/
def polePrefix (q : ℕ) : ℝ :=
  (∑ d ∈ Ioc 0 q, (ArithmeticFunction.moebius d : ℝ)*
    Real.log ((q + 1 : ℕ)/(d : ℝ))) + 2*Real.log (q + 1 : ℕ)

/-- The reciprocal part of the nonzero integer mean. -/
def reciprocalPrefix (N q : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 q, (ArithmeticFunction.moebius d : ℝ)*Real.log ((N : ℝ)/d)/d

/-- The entire finite correction, including its mean boundary. -/
def meanCorrection (N q : ℕ) (b : ℕ → ℝ) : ℝ :=
  totalMass N b/(2*Real.log N)*(polePrefix q-reciprocalPrefix N q+
    (mobiusPrefix q+2)*Real.log ((N : ℝ)/(q + 1 : ℕ))/(q + 1 : ℕ))

private def centeredPair (N : ℕ) (b : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ m ∈ Ico N (2 * N), b m*centered d m

private def centeredLogPair (N : ℕ) (b : ℕ → ℝ) (d : ℕ) : ℝ :=
  Real.log ((N : ℝ)/d)*centeredPair N b d

private def lowError (N q : ℕ) (b : ℕ → ℝ) : ℝ :=
  ((∑ d ∈ Ioc 0 q, (ArithmeticFunction.moebius d : ℝ)*centeredLogPair N b d)-
    (mobiusPrefix q+2)*centeredLogPair N b (q + 1))/Real.log N

private theorem remainder_identity {d : ℕ} (hd : 0 < d) (m : ℕ) :
    ((m % d : ℕ) : ℝ)/(d : ℝ) = (m : ℝ)/d-(m / d : ℕ) := by
  have he := centered_floor hd m
  unfold centered at he
  linarith

private theorem frac_pair_floor {N d : ℕ} (b : ℕ → ℝ) (hd : 0 < d) :
    fracPair N b d = firstMoment N b/d-
      D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.floorPair N b d := by
  unfold fracPair firstMoment D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.floorPair
  rw [sum_div, ← sum_sub_distrib]
  apply sum_congr rfl
  intro m _
  rw [remainder_identity hd]
  ring

private theorem frac_pair_centered (N d : ℕ) (b : ℕ → ℝ) :
    fracPair N b d = totalMass N b*((d : ℝ)-1)/(2*d)+centeredPair N b d := by
  unfold fracPair totalMass centeredPair centered
  rw [sum_mul, sum_div, ← sum_add_distrib]
  apply sum_congr rfl
  intro m _
  ring

private theorem mass_nonneg {N : ℕ} (b : ℕ → ℝ)
    (hb : ∀ m ∈ Ico N (2 * N), 0 ≤ b m) : 0 ≤ totalMass N b :=
  sum_nonneg hb

private theorem moment_bounds {N : ℕ} (b : ℕ → ℝ)
    (hb : ∀ m ∈ Ico N (2 * N), 0 ≤ b m) :
    0 ≤ firstMoment N b ∧ firstMoment N b ≤ 2 * N*totalMass N b := by
  constructor
  · exact sum_nonneg fun m hm => mul_nonneg (Nat.cast_nonneg _) (hb m hm)
  · unfold firstMoment totalMass
    rw [mul_sum]
    exact sum_le_sum fun m hm => mul_le_mul_of_nonneg_right
      (by exact_mod_cast (mem_Ico.mp hm).2.le) (hb m hm)

private theorem frac_pair_bounds {N d : ℕ} (b : ℕ → ℝ) (hd : 0 < d)
    (hb : ∀ m ∈ Ico N (2 * N), 0 ≤ b m) :
    0 ≤ fracPair N b d ∧ fracPair N b d ≤ totalMass N b := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · exact sum_nonneg fun m hm => mul_nonneg (hb m hm) (by positivity)
  · apply sum_le_sum
    intro m hm
    have hr : ((m % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt m hd).le
    exact (mul_le_mul_of_nonneg_left ((div_le_one hd').mpr hr) (hb m hm)).trans_eq
      (mul_one _)

private theorem frac_pair_difference {N k : ℕ} (b : ℕ → ℝ) (hk : 0 < k) :
    fracPair N b k-fracPair N b (k+1) = firstMoment N b/((k : ℝ)*(k+1))-
      ∑ m ∈ Ico N (2 * N), b m*
        (((m / k : ℕ) : ℝ)-((m / (k+1) : ℕ) : ℝ)) := by
  rw [frac_pair_floor b hk, frac_pair_floor b (by omega)]
  have he : (∑ m ∈ Ico N (2 * N), b m*
      (((m / k : ℕ) : ℝ)-((m / (k+1) : ℕ) : ℝ))) =
      D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.floorPair N b k-
      D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.floorPair N b (k+1) := by
    simp only [D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.floorPair,
      mul_sub, sum_sub_distrib]
  rw [he]
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  <;> ring

private theorem weighted_variation_bound {N h : ℕ} (hh : 0 < h) (hN : h < N)
    (b : ℕ → ℝ) (hb : ∀ m ∈ Ico N (2 * N), 0 ≤ b m) :
    weightedVariation N h b ≤ (N : ℝ)*totalMass N b*
      (1+2*Real.log ((N : ℝ)/h)^2+
        2*Real.log ((N : ℝ)/h)*(1+Real.log (2*(N : ℝ)/h))) := by
  let u := Real.log ((N : ℝ)/h)
  let v := Real.log (2*(N : ℝ)/h)
  have hu : 0 ≤ u := (log_bounds hh hN.le).1
  have hA := mass_nonneg b hb
  have hB := moment_bounds b hb
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hv : 0 ≤ v := Real.log_nonneg ((one_le_div hh0).mpr (by exact_mod_cast (by omega : h ≤ 2 * N)))
  have hpoint (k : ℕ) (hk : k ∈ Ico h N) :
      (k : ℝ)*|logDifference N b k| ≤
        u*(firstMoment N b/(k+1 : ℕ)+
          ∑ m ∈ Ico N (2 * N), b m*((k : ℝ)*
            (((m / k : ℕ) : ℝ)-((m / (k+1) : ℕ) : ℝ))))+totalMass N b := by
    obtain ⟨hkh, hkN⟩ := mem_Ico.mp hk
    have hk0 : 0 < k := lt_of_lt_of_le hh hkh
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
    have hlog := (log_bounds hk0 hkN.le).1
    have hstep : 0 ≤ Real.log (k+1 : ℕ)-Real.log (k : ℝ) :=
      sub_nonneg.mpr (Real.log_le_log hk' (by push_cast; linarith))
    have hlogu : Real.log ((N : ℝ)/k) ≤ u :=
      Real.log_le_log (div_pos hN0 hk')
        (div_le_div_of_nonneg_left hN0.le hh0 (by exact_mod_cast hkh))
    let D := ∑ m ∈ Ico N (2 * N), b m*
      (((m / k : ℕ) : ℝ)-((m / (k+1) : ℕ) : ℝ))
    have hD : 0 ≤ D := by
      apply sum_nonneg
      intro m hm
      apply mul_nonneg (hb m hm) (sub_nonneg.mpr ?_)
      exact_mod_cast Nat.div_le_div_left (by omega : k ≤ k+1) hk0
    have hB0 : 0 ≤ firstMoment N b/((k : ℝ)*(k+1)) :=
      div_nonneg hB.1 (by positivity)
    have hid : logDifference N b k =
        Real.log ((N : ℝ)/k)*(fracPair N b k-fracPair N b (k+1))+
          (Real.log (k+1 : ℕ)-Real.log (k : ℝ))*fracPair N b (k+1) := by
      unfold logDifference logPair
      rw [Real.log_div hN0.ne' hk'.ne', Real.log_div hN0.ne' (by positivity)]
      ring
    have hraw : |logDifference N b k| ≤
        Real.log ((N : ℝ)/k)*(firstMoment N b/((k : ℝ)*(k+1))+D)+
          (Real.log (k+1 : ℕ)-Real.log (k : ℝ))*totalMass N b := by
      rw [hid, frac_pair_difference b hk0]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_of_nonneg hlog]
        exact mul_le_mul_of_nonneg_left
          ((abs_sub _ _).trans_eq (by rw [abs_of_nonneg hB0, abs_of_nonneg hD])) hlog
      · rw [abs_mul, abs_of_nonneg hstep, abs_of_nonneg (frac_pair_bounds b (by omega) hb).1]
        exact mul_le_mul_of_nonneg_left (frac_pair_bounds b (by omega) hb).2 hstep
    calc
      _ ≤ (k : ℝ)*(Real.log ((N : ℝ)/k)*(firstMoment N b/((k : ℝ)*(k+1))+D)+
          (Real.log (k+1 : ℕ)-Real.log (k : ℝ))*totalMass N b) :=
        mul_le_mul_of_nonneg_left hraw hk'.le
      _ ≤ (k : ℝ)*(u*(firstMoment N b/((k : ℝ)*(k+1))+D))+totalMass N b := by
        rw [mul_add]
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hlogu (add_nonneg hB0 hD)) hk'.le
        · nlinarith [mul_le_mul_of_nonneg_right (weighted_log_step hk0) hA]
      _ = _ := by
        have he : (k : ℝ)*(firstMoment N b/((k : ℝ)*(k+1))) =
            firstMoment N b/(k+1 : ℕ) := by push_cast; field_simp
        have hD' : (∑ m ∈ Ico N (2 * N), b m*((k : ℝ)*
            (((m / k : ℕ) : ℝ)-((m / (k+1) : ℕ) : ℝ)))) = (k : ℝ)*D := by
          dsimp [D]
          rw [mul_sum]
          apply sum_congr rfl
          intro m _
          ring
        rw [hD']
        calc
          _ = u*((k : ℝ)*(firstMoment N b/((k : ℝ)*(k+1)))+(k : ℝ)*D)+totalMass N b := by ring
          _ = _ := by rw [he]
  have hcount : (∑ k ∈ Ico h N, ∑ m ∈ Ico N (2 * N), b m*((k : ℝ)*
      (((m / k : ℕ) : ℝ)-((m / (k+1) : ℕ) : ℝ)))) ≤
        totalMass N b*(2 * N*(1+v)) := by
    rw [sum_comm, totalMass, sum_mul]
    apply sum_le_sum
    intro m hm
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left
      (weighted_floor_bound hh hN (mem_Ico.mp hm).2) (hb m hm)
  have hrec : (∑ k ∈ Ico h N, (1 : ℝ)/(k+1 : ℕ)) ≤ u := by
    calc
      _ ≤ ∑ k ∈ Ico h N, (Real.log (k+1 : ℕ)-Real.log (k : ℝ)) := by
        apply sum_le_sum
        intro k hk
        exact reciprocal_log_step (by have := mem_Ico.mp hk; omega)
      _ = u := by
        dsimp only [u]
        rw [sum_Ico_sub (fun k : ℕ => Real.log (k : ℝ)) hN.le,
          Real.log_div hN0.ne' hh0.ne']
  have hmoment : (∑ k ∈ Ico h N, firstMoment N b/(k+1 : ℕ)) ≤
      2 * N*totalMass N b*u := by
    calc
      _ = firstMoment N b*(∑ k ∈ Ico h N, (1 : ℝ)/(k+1 : ℕ)) := by
        simp only [mul_sum, mul_one_div]
      _ ≤ firstMoment N b*u := mul_le_mul_of_nonneg_left hrec hB.1
      _ ≤ _ := mul_le_mul_of_nonneg_right hB.2 hu
  unfold weightedVariation
  calc
    _ ≤ ∑ k ∈ Ico h N, (u*(firstMoment N b/(k+1 : ℕ)+
        ∑ m ∈ Ico N (2 * N), b m*((k : ℝ)*
          (((m / k : ℕ) : ℝ)-((m / (k+1) : ℕ) : ℝ))))+totalMass N b) :=
      sum_le_sum hpoint
    _ = u*((∑ k ∈ Ico h N, firstMoment N b/(k+1 : ℕ))+
        ∑ k ∈ Ico h N, ∑ m ∈ Ico N (2 * N), b m*((k : ℝ)*
          (((m / k : ℕ) : ℝ)-((m / (k+1) : ℕ) : ℝ))))+
        (N-h : ℕ)*totalMass N b := by
      rw [sum_add_distrib, ← mul_sum, sum_add_distrib]
      simp
    _ ≤ u*(2 * N*totalMass N b*u+totalMass N b*(2 * N*(1+v)))+
        (N : ℝ)*totalMass N b := by
      exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add hmoment hcount) hu)
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le N h) hA)
    _ = _ := by dsimp [u, v]; ring

private theorem response_fractional {N : ℕ} (m : ℕ) :
    response N m = 1+(∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ)*
      Real.log ((N : ℝ)/d)*((m % d : ℕ)/(d : ℝ)))/Real.log N := by
  have he : (∑ d ∈ Ioc 0 N,
      D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.coefficient N d/d)*(m : ℝ)-
      (∑ d ∈ Ioc 0 N,
        D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.coefficient N d*(m / d : ℕ)) =
      (∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ)*
        Real.log ((N : ℝ)/d)*((m % d : ℕ)/(d : ℝ)))/Real.log N := by
    rw [sum_mul, ← sum_sub_distrib, sum_div]
    apply sum_congr rfl
    intro d hd
    rw [remainder_identity (mem_Ioc.mp hd).1]
    unfold D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.coefficient
    ring
  unfold response
  linarith

private theorem pairing_identity (N : ℕ) (b : ℕ → ℝ) :
    pairing N b = totalMass N b+
      (∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ)*logPair N b d)/Real.log N := by
  unfold pairing
  simp_rw [response_fractional, mul_add, mul_one]
  rw [sum_add_distrib]
  congr 1
  simp_rw [← mul_div_assoc, mul_sum]
  rw [← sum_div, sum_comm]
  congr 1
  apply sum_congr rfl
  intro d _
  unfold logPair fracPair
  rw [mul_sum, mul_sum]
  apply sum_congr rfl
  intro m _
  ring

private theorem kernel_top {N : ℕ} (hN : 0 < N) (b : ℕ → ℝ) : logPair N b N = 0 := by
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  simp [logPair, div_self hN0]

private theorem kernel_centered {N d : ℕ} (b : ℕ → ℝ) (hd : 0 < d) :
    logPair N b d = totalMass N b/2*
      (Real.log ((N : ℝ)/d)-Real.log ((N : ℝ)/d)/d)+centeredLogPair N b d := by
  unfold logPair centeredLogPair
  rw [frac_pair_centered]
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

private theorem centered_log_bound {N d : ℕ} (hN : 1 < N) (b : ℕ → ℝ)
    (hd : 0 < d) (hdN : d ≤ N) (V : ℝ) (hV : 0 ≤ V)
    (hpair : |centeredPair N b d| ≤ (d : ℝ)*V) :
    |centeredLogPair N b d| ≤ Real.log N*(d : ℝ)*V := by
  have hl := log_bounds hd hdN
  unfold centeredLogPair
  rw [abs_mul, abs_of_nonneg hl.1]
  calc
    _ ≤ Real.log ((N : ℝ)/d)*((d : ℝ)*V) :=
      mul_le_mul_of_nonneg_left hpair hl.1
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_right hl.2
        (mul_nonneg (Nat.cast_nonneg d) hV)
      nlinarith

private theorem low_error_bound {N q : ℕ} (hN : 1 < N) (hq : q + 1 ≤ N)
    (b : ℕ → ℝ) (V : ℝ) (hV : 0 ≤ V)
    (hpair : ∀ {d : ℕ}, 0 < d → |centeredPair N b d| ≤ (d : ℝ)*V) :
    |lowError N q b| ≤ (q + 1 : ℕ)*((3 : ℝ)*q/2+2)*V := by
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hsum : |∑ d ∈ Ioc 0 q, (ArithmeticFunction.moebius d : ℝ)*centeredLogPair N b d| ≤
      Real.log N*V*((q : ℝ)*(q + 1)/2) := by
    calc
      _ ≤ ∑ d ∈ Ioc 0 q, |(ArithmeticFunction.moebius d : ℝ)*centeredLogPair N b d| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Ioc 0 q, Real.log N*(d : ℝ)*V := by
        apply sum_le_sum
        intro d hd
        rw [abs_mul]
        calc
          _ ≤ 1*|centeredLogPair N b d| := mul_le_mul_of_nonneg_right
            (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)) (abs_nonneg _)
          _ ≤ _ := by
            simpa using centered_log_bound hN b (mem_Ioc.mp hd).1
              (by have := mem_Ioc.mp hd; omega) V hV (hpair (mem_Ioc.mp hd).1)
      _ = _ := by
        have he : (∑ d ∈ Ioc 0 q, Real.log N*(d : ℝ)*V) =
            Real.log N*V*(∑ d ∈ Ioc 0 q, (d : ℝ)) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro d _
          ring
        rw [he, sum_indices]
  have hprefix : |mobiusPrefix q+2| ≤ (q : ℝ)+2 := by
    calc
      _ ≤ |mobiusPrefix q|+|2| := abs_add_le _ _
      _ ≤ _ := by norm_num; exact prefix_bound q
  have hterm : |(mobiusPrefix q+2)*centeredLogPair N b (q + 1)| ≤
      ((q : ℝ)+2)*(Real.log N*(q + 1 : ℕ)*V) := by
    rw [abs_mul]
    exact mul_le_mul hprefix (centered_log_bound hN b (by omega) hq V hV (hpair (by omega)))
      (abs_nonneg _) (by positivity)
  unfold lowError
  rw [abs_div, abs_of_pos hL]
  apply (div_le_iff₀ hL).mpr
  calc
    _ ≤ _ := (abs_sub _ _).trans (add_le_add hsum hterm)
    _ = _ := by push_cast; ring

private theorem sharp_low_error_bound {N q : ℕ} (hN : 1 < N) (hq : q + 1 ≤ N)
    (b : ℕ → ℝ) : |lowError N q b| ≤
      if q = 0 then 0 else (q + 1 : ℕ)*((3 : ℝ)*q/2+2)*variation N b/16 := by
  by_cases hq0 : q = 0
  · subst q
    simp [lowError, centeredLogPair, centeredPair, centered, Nat.mod_one]
  · rw [if_neg hq0]
    have he := low_error_bound hN hq b (variation N b/16)
      (div_nonneg (variation_nonneg N b) (by norm_num)) (fun {d} hd => by
        have hp := centered_pair_variation_sharp_bound (by omega : 0 < N) b hd
        change |centeredPair N b d| ≤ (d : ℝ)/16*variation N b at hp
        convert hp using 1 <;> ring)
    convert he using 1 <;> ring

private theorem prefix_log_identity {N q : ℕ} (hN : 0 < N) :
    (∑ d ∈ Ioc 0 q, (ArithmeticFunction.moebius d : ℝ)*Real.log ((N : ℝ)/d)) =
      (∑ d ∈ Ioc 0 q, (ArithmeticFunction.moebius d : ℝ)*
        Real.log ((q + 1 : ℕ)/(d : ℝ)))+
      mobiusPrefix q*Real.log ((N : ℝ)/(q + 1 : ℕ)) := by
  unfold mobiusPrefix
  rw [sum_mul, ← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  have hd0 : (d : ℝ) ≠ 0 := by have := (mem_Ioc.mp hd).1; positivity
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  rw [Real.log_div hN0 hd0, Real.log_div (by positivity) hd0,
    Real.log_div hN0 (by positivity)]
  ring

/-- The finite low prefix retains the literal truncated pole payment. -/
private theorem low_identity {N q : ℕ} (hN : 1 < N) (b : ℕ → ℝ) :
    totalMass N b+((∑ k ∈ Ioc 0 q, mobiusPrefix k*logDifference N b k)-
      2*logPair N b (q + 1))/Real.log N = meanCorrection N q b+lowError N q b := by
  have habel := prefix_abel (logPair N b) q
  change (∑ k ∈ Ioc 0 q, mobiusPrefix k*logDifference N b k) = _ at habel
  have hsum : (∑ d ∈ Ioc 0 q, (ArithmeticFunction.moebius d : ℝ)*logPair N b d) =
      totalMass N b/2*((∑ d ∈ Ioc 0 q, (ArithmeticFunction.moebius d : ℝ)*
        Real.log ((N : ℝ)/d))-reciprocalPrefix N q)+
      ∑ d ∈ Ioc 0 q, (ArithmeticFunction.moebius d : ℝ)*centeredLogPair N b d := by
    unfold reciprocalPrefix
    rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro d hd
    rw [kernel_centered b (mem_Ioc.mp hd).1]
    ring
  rw [habel, hsum, kernel_centered b (by omega), prefix_log_identity (by omega : 0 < N)]
  unfold meanCorrection polePrefix lowError
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  rw [Real.log_div hN0 (by positivity)]
  have hL0 : Real.log (N : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hN))
  have hh0 : ((q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

private theorem abel_identity {N : ℕ} (hN : 0 < N) (b : ℕ → ℝ) :
    pairing N b = totalMass N b+
      (∑ k ∈ Ioc 0 (N-1), mobiusPrefix k*logDifference N b k)/Real.log N := by
  rw [pairing_identity]
  have hKN := kernel_top hN b
  have he := prefix_abel (logPair N b) (N-1)
  rw [show N-1+1 = N by omega, hKN, mul_zero, sub_zero] at he
  have hs : (∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ)*logPair N b d) =
      ∑ d ∈ Ioc 0 (N-1), (ArithmeticFunction.moebius d : ℝ)*logPair N b d := by
    conv_lhs => rw [show N = (N-1)+1 by omega]
    rw [sum_Ioc_succ_top (Nat.zero_le (N-1))]
    simp only [show N-1+1 = N by omega, hKN, mul_zero, add_zero]
  rw [hs, ← he]
  rfl

private theorem transfer_identity {N q : ℕ} (hN : 3 ≤ N) (hq : q ≤ N-2)
    (b F : ℕ → ℝ) :
    pairing N b-replacement N q b F-meanCorrection N q b = lowError N q b-
      (∑ k ∈ Ico (q + 1) N, (F k-mobiusPrefix k)*logDifference N b k)/Real.log N := by
  have hN1 : 1 < N := by omega
  have hN0 : 0 < N := by omega
  have hh : q + 1 < N := by omega
  let P := ∑ k ∈ Ioc 0 q, mobiusPrefix k*logDifference N b k
  let T := ∑ k ∈ Ico (q + 1) N, (F k-mobiusPrefix k)*logDifference N b k
  have hsplit : (∑ k ∈ Ioc 0 (N-1), mobiusPrefix k*logDifference N b k) =
      P+∑ k ∈ Ico (q + 1) N, mobiusPrefix k*logDifference N b k := by
    have he := sum_Ioc_consecutive (f := fun k => mobiusPrefix k*logDifference N b k)
      (Nat.zero_le q) (by omega : q ≤ N-1)
    have hset : Ioc q (N-1) = Ico (q + 1) N := by
      ext k
      simp only [mem_Ioc, mem_Ico]
      omega
    rw [hset] at he
    exact he.symm
  have htel : (∑ k ∈ Ico (q + 1) N, logDifference N b k) = logPair N b (q + 1) := by
    have he := sum_Ico_sub (logPair N b) hh.le
    have hs : (∑ k ∈ Ico (q + 1) N, logDifference N b k) =
        -(∑ k ∈ Ico (q + 1) N, (logPair N b (k+1)-logPair N b k)) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro k _
      unfold logDifference
      ring
    rw [hs, he, kernel_top hN0 b]
    ring
  change _ = lowError N q b-T/Real.log N
  have he := abel_identity hN0 b
  rw [hsplit] at he
  have hlo := low_identity (q := q) hN1 b
  change totalMass N b+(P-2*logPair N b (q + 1))/Real.log N = _ at hlo
  rw [he]
  unfold replacement
  dsimp [T]
  simp_rw [add_mul, sub_mul]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, htel]
  linear_combination hlo

private theorem transfer_of_low_bound {N q : ℕ} (hN : 3 ≤ N) (hq : q ≤ N-2)
    (b F : ℕ → ℝ) (ε c : ℝ) (hε : 0 ≤ ε) (hc : 0 ≤ c)
    (hb : ∀ m ∈ Ico N (2 * N), 0 ≤ b m)
    (herr : ∀ k ∈ Ico (q + 1) N, |F k-mobiusPrefix k| ≤ ε*(k : ℝ)+c) (A : ℝ) (hlow : |lowError N q b| ≤ A) :
    |pairing N b-replacement N q b F-meanCorrection N q b| ≤
      (ε+c/(q + 1 : ℕ))/Real.log N*((N : ℝ)*totalMass N b*
        (1+2*Real.log ((N : ℝ)/(q + 1 : ℕ))^2+
          2*Real.log ((N : ℝ)/(q + 1 : ℕ))*(1+Real.log (2*(N : ℝ)/(q + 1 : ℕ)))))+
      A := by
  have hN1 : 1 < N := by omega
  have hN0 : 0 < N := by omega
  have hh : q + 1 < N := by omega
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN1)
  have hfactor : 0 ≤ (ε+c/(q + 1 : ℕ))/Real.log N := by positivity
  let T := ∑ k ∈ Ico (q + 1) N, (F k-mobiusPrefix k)*logDifference N b k
  have hexact := transfer_identity hN hq b F
  have hT : |T|/Real.log N ≤
      (ε+c/(q + 1 : ℕ))/Real.log N*weightedVariation N (q + 1) b := by
    have he := prefix_error_bound (by omega : 0 < q + 1) (logDifference N b) F hc herr
    change |T| ≤ (ε+c/(q + 1 : ℕ))*weightedVariation N (q + 1) b at he
    apply (div_le_iff₀ hL).mpr
    have hid : ((ε+c/(q + 1 : ℕ))/Real.log N*weightedVariation N (q + 1) b)*Real.log N =
        (ε+c/(q + 1 : ℕ))*weightedVariation N (q + 1) b := by field_simp
    rw [hid]
    exact he
  rw [hexact]
  calc
    _ ≤ |lowError N q b|+|T/Real.log N| := abs_sub _ _
    _ = |lowError N q b|+|T|/Real.log N := by rw [abs_div, abs_of_pos hL]
    _ ≤ A+
        (ε+c/(q + 1 : ℕ))/Real.log N*weightedVariation N (q + 1) b :=
      add_le_add hlow hT
    _ ≤ A+
        (ε+c/(q + 1 : ℕ))/Real.log N*((N : ℝ)*totalMass N b*
          (1+2*Real.log ((N : ℝ)/(q + 1 : ℕ))^2+
            2*Real.log ((N : ℝ)/(q + 1 : ℕ))*(1+Real.log (2*(N : ℝ)/(q + 1 : ℕ))))) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (weighted_variation_bound (by omega) hh b hb) hfactor)
    _ = _ := add_comm _ _

/-- Finite full-positive JK13 for the actual response. No moment vanishes by hypothesis. -/
theorem originalFullCell_finite_transfer {N q : ℕ} (hN : 3 ≤ N) (hq : q ≤ N-2)
    (b F : ℕ → ℝ) (ε c : ℝ) (hε : 0 ≤ ε) (hc : 0 ≤ c)
    (hb : ∀ m ∈ Ico N (2 * N), 0 ≤ b m)
    (herr : ∀ k ∈ Ico (q + 1) N, |F k-mobiusPrefix k| ≤ ε*(k : ℝ)+c) :
    |pairing N b-replacement N q b F-meanCorrection N q b| ≤
      (ε+c/(q + 1 : ℕ))/Real.log N*((N : ℝ)*totalMass N b*
        (1+2*Real.log ((N : ℝ)/(q + 1 : ℕ))^2+
          2*Real.log ((N : ℝ)/(q + 1 : ℕ))*(1+Real.log (2*(N : ℝ)/(q + 1 : ℕ)))))+
      (q + 1 : ℕ)*((3 : ℝ)*q/2+2)*variation N b := by
  exact transfer_of_low_bound hN hq b F ε c hε hc hb herr _
    (low_error_bound (by omega) (by omega) b (variation N b) (variation_nonneg N b)
      (fun {_} hd => centered_pair_variation_bound (by omega) b hd))

/-- The midpoint primitive sharpens the low error, which vanishes exactly at q=0. -/
theorem originalFullCell_finite_transfer_sharp {N q : ℕ} (hN : 3 ≤ N) (hq : q ≤ N-2)
    (b F : ℕ → ℝ) (ε c : ℝ) (hε : 0 ≤ ε) (hc : 0 ≤ c)
    (hb : ∀ m ∈ Ico N (2 * N), 0 ≤ b m)
    (herr : ∀ k ∈ Ico (q + 1) N, |F k-mobiusPrefix k| ≤ ε*(k : ℝ)+c) :
    |pairing N b-replacement N q b F-meanCorrection N q b| ≤
      (ε+c/(q + 1 : ℕ))/Real.log N*((N : ℝ)*totalMass N b*
        (1+2*Real.log ((N : ℝ)/(q + 1 : ℕ))^2+
          2*Real.log ((N : ℝ)/(q + 1 : ℕ))*(1+Real.log (2*(N : ℝ)/(q + 1 : ℕ)))))+
      (if q = 0 then 0 else (q + 1 : ℕ)*((3 : ℝ)*q/2+2)*variation N b/16) := by
  exact transfer_of_low_bound hN hq b F ε c hε hc hb herr _
    (sharp_low_error_bound (by omega) (by omega) b)

#print axioms originalFullCell_finite_transfer
#print axioms originalFullCell_finite_transfer_sharp

end D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer
