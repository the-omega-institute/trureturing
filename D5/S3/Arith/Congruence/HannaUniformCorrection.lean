/- GID: D5/S3/Arith/Congruence/HannaUniformCorrection
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/HannaUniformCorrection
   mirror-E: none(waiver:symbolic-unbounded-family)
   anchors: []
   utility: none
   digest: Bounded corrections and positive Euler exponents for every integer power weight. -/

/- admission_basis: escape-witness. Proposed content: exponent_bounds proves a simultaneous positive lower and power upper bound through strong induction and the proper-divisor budget. The prime-power conclusions consume the generalized original owner induction, never a duplicate square proof. Every weight is an integer and weight_cast supplies the nonnegative-domain correspondence. utility none: unbounded symbolic family. Source attribution: the square results are due to Su; Bala owns the cited universal shift (not extended here); all-s literature novelty is unverified. -/


import D5.S1.Recurrence.Witt.BoundedEulerCorrection
import D5.S1.Recurrence.Witt.EulerExponentialCoefficients
import D5.S3.Combinatorics.Partitions.ColouredEulerLedger
import D5.S3.Arith.Divisors.ProperDivisorPowerBudget
import D5.S3.Arith.Congruence.BoundedPowerCorrection

noncomputable section

namespace D5.S3.Arith.Congruence.HannaUniformCorrection

open Finset PowerSeries
open D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality
open D5.S1.Recurrence.Witt.BoundedEulerCorrection
open D5.S3.Arith.Divisors.ProperDivisorPowerBudget

/-- Natural powers are used for the integer recursion; `weight_cast` below
identifies them with the requested integer powers on the full nonnegative domain. -/
def weight (s : ℤ) (n : ℕ) : ℤ := (n : ℤ) ^ s.toNat

def a (s : ℤ) : ℕ → ℤ := correction (weight s)
def c (s : ℤ) : ℕ → ℤ := ledger (weight s)

/-- The actual rational formal exponential, with an integer weight parameter. -/
def F (s : ℤ) : PowerSeries ℚ :=
  exponentialSum (fun n => (n : ℚ) ^ s - (a s n : ℚ))

def IsPowerCorrection (s : ℤ) (b : ℕ → ℤ) : Prop :=
  (∀ n, 0 < n → 0 ≤ b n ∧ b n < (n : ℤ)) ∧
    D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure.IntegralSeries
      (exponentialSum (fun n => (n : ℚ) ^ s - (b n : ℚ)))

theorem weight_cast (s : ℤ) (hs : 0 ≤ s) (n : ℕ) :
    (weight s n : ℚ) = (n : ℚ) ^ s := by
  simp only [weight, Int.cast_pow, Int.cast_natCast]
  rw [← zpow_natCast, Int.toNat_of_nonneg hs]

theorem correction_spec (s : ℤ) : IsCorrection (weight s) (a s) :=
  correction_integral (weight s)

private theorem power_correction_iff (s : ℤ) (hs : 0 ≤ s) (b : ℕ → ℤ) :
    IsPowerCorrection s b ↔ IsCorrection (weight s) b := by
  have he : (fun (n : ℕ) => (n : ℚ) ^ s - (b n : ℚ)) =
      (fun n => ((weight s n - b n : ℤ) : ℚ)) := by
    funext n
    rw [Int.cast_sub, weight_cast s hs n]
  simp only [IsPowerCorrection, IsCorrection, he]

/-- Existence and uniqueness on exactly the positive indices. -/
theorem correction_exists_unique (s : ℤ) (hs : 0 ≤ s) :
    IsPowerCorrection s (a s) ∧
      ∀ b, IsPowerCorrection s b → ∀ n, 0 < n → b n = a s n := by
  refine ⟨(power_correction_iff s hs _).mpr (correction_spec s), ?_⟩
  intro b hb n hn
  exact correction_unique (weight s) b ((power_correction_iff s hs b).mp hb) n hn

private theorem ghost_equation (s : ℤ) (n : ℕ) (hn : 0 < n) :
    weight s n - a s n = divisorGhost (c s) n :=
  correction_equation (weight s) n hn

/-- Actual exponent-to-exponential equality, with the primitive ledger's
zero-based indexing shifted explicitly to positive part sizes. -/
theorem euler_representation (s : ℤ) (hs : 0 ≤ s) :
    (eulerSeries (fun i => c s (i + 1))).map (Int.castRingHom ℚ) = F s := by
  apply euler_series_exponential
  intro n hn
  have hc : divisorGhost (fun d => c s (d - 1 + 1)) n = divisorGhost (c s) n := by
    unfold divisorGhost
    apply sum_congr rfl
    intro d hd
    dsimp only
    rw [Nat.sub_add_cancel (Nat.pos_of_mem_divisors hd)]
  rw [hc, ← weight_cast s hs n]
  exact_mod_cast correction_equation (weight s) n hn

/-- Each positive-index exponent is between one and the stipulated power bound.
The lower bound uses the finite complementary-divisor estimate. -/
theorem exponent_bounds (s : ℤ) (hs : 2 ≤ s) :
    ∀ n, 0 < n → 1 ≤ c s n ∧ c s n ≤ (n : ℤ) ^ (s.toNat - 1) := by
  have hsN : 2 ≤ s.toNat := by omega
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
    have hab := (correction_spec s).1 n hn
    have he := correction_equation (weight s) n hn
    change weight s n - a s n = divisorGhost (c s) n at he
    have hsplit : divisorGhost (c s) n = properGhost (c s) n + (n : ℤ) * c s n := by
      rw [divisorGhost, ← Nat.cons_self_properDivisors hn.ne', sum_cons]
      simp only [properGhost]
      ring
    rw [hsplit] at he
    have hT0 : 0 ≤ properGhost (c s) n := by
      apply sum_nonneg
      intro d hd
      exact mul_nonneg (Nat.cast_nonneg d)
        (le_trans (by norm_num) (ih d (Nat.mem_properDivisors.mp hd).2
          (Nat.pos_of_mem_properDivisors hd)).1)
    have hTle : properGhost (c s) n ≤ ∑ d ∈ n.properDivisors, (d : ℤ) ^ s.toNat := by
      apply sum_le_sum
      intro d hd
      have hb := (ih d (Nat.mem_properDivisors.mp hd).2
        (Nat.pos_of_mem_properDivisors hd)).2
      calc
        (d : ℤ) * c s d ≤ (d : ℤ) * (d : ℤ) ^ (s.toNat - 1) :=
          mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg d)
        _ = (d : ℤ) ^ s.toNat := by
          rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ s.toNat)]
    have hbudget := power_budget s.toNat n hsN hn
    have hpow : (n : ℤ) ^ s.toNat = (n : ℤ) * (n : ℤ) ^ (s.toNat - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ s.toNat)]
    dsimp only [weight] at he
    constructor <;> nlinarith

/-- Every prime, including two, has the same correction at each positive power. -/
theorem correction_prime_power (s : ℤ) (hs : 2 ≤ s) (p r : ℕ)
    (hp : p.Prime) (hr : 1 ≤ r) : a s (p ^ r) = (p : ℤ) - 1 := by
  apply D5.S3.Arith.Congruence.HannaPrimePowerCorrection.bounded_power_corrections
    s.toNat (by omega) (a s) (correction_spec s).1 _ p r hp hr
  intro q hq k
  have h := divisor_ghost_gauss (c s) q hq k 1 Nat.one_pos
  simp only [one_mul] at h
  rw [← ghost_equation s _ (pow_pos hq.pos _),
    ← ghost_equation s _ (pow_pos hq.pos _)] at h
  exact h

private theorem ghost_prime_power_step (b : ℕ → ℤ) (p k : ℕ) (hp : p.Prime) :
    divisorGhost b (p ^ (k + 1)) - divisorGhost b (p ^ k) =
      (p : ℤ) ^ (k + 1) * b (p ^ (k + 1)) := by
  simp only [divisorGhost, Nat.sum_divisors_prime_pow hp]
  rw [sum_range_succ]
  push_cast
  ring

theorem exponent_prime (s : ℤ) (hs : 2 ≤ s) (p : ℕ) (hp : p.Prime) :
    c s p = (p : ℤ) ^ (s.toNat - 1) - 1 := by
  have h := ghost_prime_power_step (c s) p 0 hp
  simp only [zero_add, pow_one, pow_zero] at h
  have haP : a s p = (p : ℤ) - 1 := by
    simpa only [pow_one] using correction_prime_power s hs p 1 hp le_rfl
  rw [← ghost_equation s p hp.pos,
    ← ghost_equation s 1 Nat.one_pos,
    haP] at h
  have ha1 : a s 1 = 0 := by
    have := (correction_spec s).1 1 Nat.one_pos
    omega
  simp only [weight, ha1, Nat.cast_one, one_pow, sub_zero] at h
  have he : (p : ℤ) ^ s.toNat = (p : ℤ) * (p : ℤ) ^ (s.toNat - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ s.toNat)]
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
  rw [he] at h
  nlinarith

theorem exponent_prime_power (s : ℤ) (hs : 2 ≤ s) (p r : ℕ)
    (hp : p.Prime) (hr : 2 ≤ r) :
    c s (p ^ r) = (p : ℤ) ^ (s.toNat * (r - 1) - r) * ((p : ℤ) ^ s.toNat - 1) := by
  have hr1 : 1 ≤ r := by omega
  have hrm : 1 ≤ r - 1 := by omega
  have hsN : 2 ≤ s.toNat := by omega
  have hexp : r ≤ s.toNat * (r - 1) := by
    have hrsub : r - 1 + 1 = r := Nat.sub_add_cancel hr1
    nlinarith
  have h := ghost_prime_power_step (c s) p (r - 1) hp
  rw [Nat.sub_add_cancel hr1] at h
  rw [← ghost_equation s _ (pow_pos hp.pos _),
    ← ghost_equation s _ (pow_pos hp.pos _),
    correction_prime_power s hs p r hp hr1,
    correction_prime_power s hs p (r - 1) hp hrm] at h
  simp only [weight, Nat.cast_pow, ← pow_mul] at h
  have hpow : (p : ℤ) ^ r *
      ((p : ℤ) ^ (s.toNat * (r - 1) - r) * ((p : ℤ) ^ s.toNat - 1)) =
      (p : ℤ) ^ (r * s.toNat) - (p : ℤ) ^ ((r - 1) * s.toNat) := by
    have hbase : r + (s.toNat * (r - 1) - r) = (r - 1) * s.toNat := by
      rw [Nat.add_sub_of_le hexp, Nat.mul_comm]
    have hstep : (r - 1) * s.toNat + s.toNat = r * s.toNat := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hr1]
    rw [← mul_assoc, ← pow_add, hbase, mul_sub, mul_one, ← pow_add, hstep]
  have hp0 : (p : ℤ) ^ r ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  apply mul_left_cancel₀ hp0
  rw [hpow]
  linear_combination -h

/-- The independent integer coefficients of the constructed Euler series. -/
def f (s : ℤ) (n : ℕ) : ℤ := coeff n (eulerSeries (fun i => c s (i + 1)))

/-- These integers are the actual ordinary coefficients of the literal exponential. -/
theorem coefficient_eq (s : ℤ) (hs : 0 ≤ s) (n : ℕ) :
    (f s n : ℚ) = coeff n (F s) := by
  rw [← euler_representation s hs, coeff_map]
  rfl

private theorem F_eq (s : ℤ) (hs : 0 ≤ s) :
    F s = exponentialSum (fun n => ((weight s n - a s n : ℤ) : ℚ)) := by
  unfold F
  congr 1
  funext n
  rw [Int.cast_sub, weight_cast s hs n]

/-- A genuine finite carrier of coloured partitions, with each multiplicity
represented by a multiset of colours. -/
abbrev ColouredPartition (s : ℤ) (n : ℕ) :=
  D5.S3.Combinatorics.Partitions.ColouredEulerLedger.ColouredPartition
    (fun d => (c s d).toNat) n

/-- The actual exponential coefficients count the independent coloured carrier. -/
theorem coefficient_cardinality (s : ℤ) (hs : 2 ≤ s) (n : ℕ) :
    f s n = (Nat.card (ColouredPartition s n) : ℤ) := by
  have he : (fun i => c s (i + 1)) =
      (fun i => (((c s (i + 1)).toNat : ℕ) : ℤ)) := by
    funext i
    exact (Int.toNat_of_nonneg (le_trans (by norm_num)
      (exponent_bounds s hs (i + 1) (by omega)).1)).symm
  unfold f
  rw [he]
  exact D5.S3.Combinatorics.Partitions.ColouredEulerLedger.coloured_coefficient (fun d => (c s d).toNat) n

private theorem ghost_positive (s : ℤ) (hs : 2 ≤ s) (n : ℕ) (hn : 0 < n) :
    0 < weight s n - a s n := by
  have hb := (correction_spec s).1 n hn
  have hpow : (n : ℤ) ≤ (n : ℤ) ^ s.toNat :=
    le_self_pow₀ (by exact_mod_cast hn) (by omega)
  dsimp only [weight]
  omega

private theorem ghost_increasing (s : ℤ) (hs : 2 ≤ s) (n : ℕ) (hn : 0 < n) :
    weight s n - a s n ≤ weight s (n + 1) - a s (n + 1) := by
  have hsN : 2 ≤ s.toNat := by omega
  have hb := (correction_spec s).1 n hn
  have hb' := (correction_spec s).1 (n + 1) (by omega)
  have hnZ : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hm : (n : ℤ) ^ (s.toNat - 1) ≤ (n + 1 : ℤ) ^ (s.toNat - 1) :=
    pow_le_pow_left₀ (by omega) (by omega) _
  have hlarge : (n + 1 : ℤ) ≤ (n + 1 : ℤ) ^ (s.toNat - 1) :=
    le_self_pow₀ (by omega) (by omega)
  have hmul := mul_le_mul_of_nonneg_left hm (show (0 : ℤ) ≤ n by omega)
  have hp (m : ℤ) : m ^ s.toNat = m * m ^ (s.toNat - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ s.toNat)]
  dsimp only [weight]
  rw [hp, hp]
  push_cast at hb' ⊢
  nlinarith

/-- Every actual coefficient is strictly positive, including degree zero. -/
theorem coefficient_positive (s : ℤ) (hs : 2 ≤ s) (n : ℕ) : 0 < f s n := by
  have h := D5.S1.Recurrence.Witt.EulerExponentialCoefficients.coefficient_positive
    (fun n => ((weight s n - a s n : ℤ) : ℚ)) (by
      intro m hm
      exact_mod_cast ghost_positive s hs m hm) n
  rw [← F_eq s (by omega), ← coefficient_eq s (by omega)] at h
  exact_mod_cast h

/-- Increasing corrected ghosts force nondecreasing actual coefficients. -/
theorem coefficient_monotone (s : ℤ) (hs : 2 ≤ s) : Monotone (f s) := by
  have h := D5.S1.Recurrence.Witt.EulerExponentialCoefficients.coefficient_monotone
    (fun n => ((weight s n - a s n : ℤ) : ℚ)) (by
      intro m hm
      exact_mod_cast ghost_positive s hs m hm) (by
        have hb := (correction_spec s).1 1 Nat.one_pos
        have ha : a s 1 = 0 := by omega
        simp [weight, ha]) (by
          intro m hm
          exact_mod_cast ghost_increasing s hs m hm)
  intro i j hij
  have hij' := h hij
  dsimp only at hij'
  rw [← F_eq s (by omega), ← coefficient_eq s (by omega),
    ← coefficient_eq s (by omega)] at hij'
  exact_mod_cast hij'

private theorem coeff_exponential_ones : ∀ n, coeff n (exponentialSum (fun _ => (1 : ℚ))) = 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simpa only [coeff_zero_eq_constantCoeff] using exponential_sum_constant _
      | succ n =>
        have h := D5.S1.Recurrence.Witt.EulerExponentialCoefficients.coefficient_recurrence
          (fun _ => (1 : ℚ)) (n + 1)
        have he : (∑ k ∈ range (n + 1), (1 : ℚ) *
            coeff (n + 1 - (k + 1)) (exponentialSum (fun _ => (1 : ℚ)))) = n + 1 := by
          calc
            _ = ∑ k ∈ range (n + 1), (1 : ℚ) := by
              apply sum_congr rfl
              intro k hk
              rw [ih _ (by have := mem_range.mp hk; omega), one_mul]
            _ = _ := by simp
        rw [he] at h
        have hn : (0 : ℚ) < n + 1 := by positivity
        push_cast at h
        nlinarith

private theorem boundary_candidates :
    IsPowerCorrection 0 (fun _ => 0) ∧
      IsPowerCorrection 1 (fun n => (n : ℤ) - 1) := by
  have hInt : D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure.IntegralSeries
      (exponentialSum (fun _ => (1 : ℚ))) := by
    intro n
    exact ⟨1, by simpa using coeff_exponential_ones n⟩
  constructor
  · constructor
    · intro n hn
      dsimp only
      exact ⟨le_rfl, by exact_mod_cast hn⟩
    · simpa only [zpow_zero, Int.cast_zero, sub_zero] using hInt
  · constructor
    · intro n hn
      have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
      dsimp only
      constructor <;> omega
    · have he : (fun (n : ℕ) => (n : ℚ) ^ (1 : ℤ) - (((n : ℤ) - 1 : ℤ) : ℚ)) =
          (fun _ => (1 : ℚ)) := by
        funext n
        push_cast
        simp
      rw [he]
      exact hInt

/-- Both boundary corrections are determined uniquely on the positive indices. -/
theorem correction_boundary (n : ℕ) (hn : 0 < n) :
    a 0 n = 0 ∧ a 1 n = (n : ℤ) - 1 := by
  exact ⟨((correction_exists_unique 0 (by omega)).2 _ boundary_candidates.1 n hn).symm,
    ((correction_exists_unique 1 (by omega)).2 _ boundary_candidates.2 n hn).symm⟩

/-- Both literal exponentials at weights zero and one are the geometric series. -/
theorem F_boundary : F 0 = (1 - X)⁻¹ ∧ F 1 = (1 - X)⁻¹ := by
  have hOne : exponentialSum (fun _ => (1 : ℚ)) = (1 - X)⁻¹ := by
    apply (PowerSeries.eq_inv_iff_mul_eq_one (by simp)).mpr
    have he : exponentialSum (fun _ => (1 : ℚ)) = PowerSeries.mk 1 := by
      ext n
      simp only [coeff_exponential_ones, coeff_mk, Pi.one_apply]
    rw [he]
    exact mk_one_mul_one_sub_eq_one ℚ
  have hF (s : ℤ) (hs : s = 0 ∨ s = 1) : F s = exponentialSum (fun _ => (1 : ℚ)) := by
    unfold F exponentialSum
    congr 1
    apply PowerSeries.ext
    intro n
    simp only [logarithmicInput, coeff_mk]
    split_ifs with hn
    · rfl
    · have hb := correction_boundary n (Nat.pos_of_ne_zero hn)
      rcases hs with rfl | rfl
      · simp [hb.1]
      · simp [hb.2]
  exact ⟨(hF 0 (Or.inl rfl)).trans hOne, (hF 1 (Or.inr rfl)).trans hOne⟩

end D5.S3.Arith.Congruence.HannaUniformCorrection
