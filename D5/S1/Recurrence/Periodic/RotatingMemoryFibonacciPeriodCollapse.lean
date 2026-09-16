/- GID: D5/S1/Recurrence/Periodic/RotatingMemoryFibonacciPeriodCollapse
   generality: G
   mirror-B: D5/B/S1/Recurrence/Periodic/RotatingMemoryFibonacciPeriodCollapse
   mirror-E: none(waiver:formal-unit-only)
   anchors: []
   utility: none
   digest: Every rotating-memory tail Hankel matrix is nonsingular over the rationals. -/

/-
Source: Abdelaidoum, Mehiri, and Belbachir, "Rotating-Memory Fibonacci
Numbers and Periodic Tilings", arXiv:2609.12569v1, Definition 1 and
Theorem 1. The source proves period collapse but does not state the tail
Hankel nonsingularity consequence.

Search note: no exact implementation was found in this repository, pinned
Mathlib, or the completed A17 GitHub searches for rotating-memory Fibonacci
and period-collapse terminology, including arXiv identifier 2609.12569.

proof_shape(period_collapse): content
escape_witness(period_collapse): the live full-cycle induction derives the
  published factor from the recursive sequence definition.
proof_shape(tail_hankel_det_ne_zero): content
escape_witness(tail_hankel_det_ne_zero): the live arbitrary-dimension kernel
  elimination subtracts adjacent rows of the factorized threshold matrix,
  isolates every positive coordinate, and then uses the first row to isolate
  coordinate zero.
admission_basis: escape-witness
-/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Periodic.RotatingMemoryFibonacciPeriodCollapse

open scoped BigOperators

def rotatingMemory (k n : ℕ) : ℕ :=
  if n = 0 then 0 else if n = 1 then 1 else
    ∑ j ∈ Finset.range (2 + n % k), rotatingMemory k (n - (j + 1))
termination_by n
decreasing_by
  apply Nat.sub_lt
  · omega
  · omega

theorem period_collapse (k n : ℕ) (hk : 2 ≤ k) (hn : k ≤ n) :
    rotatingMemory k (n + k) = 3 * 2 ^ (k - 2) * rotatingMemory k n := by
  have nonreset_doubling (m : ℕ) (hm : 3 ≤ m) (hmod : m % k ≠ 0) :
      rotatingMemory k m = 2 * rotatingMemory k (m - 1) := by
    have hm0 : m ≠ 0 := by omega
    have hm1 : m ≠ 1 := by omega
    have hprev0 : m - 1 ≠ 0 := by omega
    have hprev1 : m - 1 ≠ 1 := by omega
    have hmod_succ : m % k = (m - 1) % k + 1 := by
      have hpos : 1 ≤ m % k := Nat.one_le_iff_ne_zero.mpr hmod
      have hsub : m % k - 1 = (m - 1) % k := Nat.mod_sub_of_le hpos
      omega
    have hrec_m : rotatingMemory k m =
        ∑ j ∈ Finset.range (2 + m % k), rotatingMemory k (m - (j + 1)) := by
      rw [rotatingMemory]
      simp only [if_neg hm0, if_neg hm1]
    have hrec_prev : rotatingMemory k (m - 1) =
        ∑ j ∈ Finset.range (2 + (m - 1) % k),
          rotatingMemory k ((m - 1) - (j + 1)) := by
      rw [rotatingMemory]
      simp only [if_neg hprev0, if_neg hprev1]
    let f : ℕ → ℕ := fun j => rotatingMemory k (m - (j + 1))
    have htail : rotatingMemory k (m - 1) =
        ∑ j ∈ Finset.range (2 + (m - 1) % k), f (j + 1) := by
      rw [hrec_prev]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [f]
      congr 1
      omega
    rw [hmod_succ] at hrec_m
    have hrange : 2 + ((m - 1) % k + 1) = 3 + (m - 1) % k := by omega
    rw [hrange] at hrec_m
    calc
      rotatingMemory k m = ∑ j ∈ Finset.range (3 + (m - 1) % k), f j := by
        simpa [f] using hrec_m
      _ = (∑ j ∈ Finset.range (2 + (m - 1) % k), f (j + 1)) + f 0 := by
        rw [show 3 + (m - 1) % k = (2 + (m - 1) % k) + 1 by omega]
        rw [Finset.sum_range_succ']
      _ = rotatingMemory k (m - 1) + rotatingMemory k (m - 1) := by
        rw [← htail]
      _ = 2 * rotatingMemory k (m - 1) := by omega
  have reset_balance (m : ℕ) (hm : 4 ≤ m) (hmod : m % k = 0) :
      2 * rotatingMemory k m = 3 * rotatingMemory k (m - 1) := by
    have hm0 : m ≠ 0 := by omega
    have hm1 : m ≠ 1 := by omega
    have hrec : rotatingMemory k m =
        rotatingMemory k (m - 1) + rotatingMemory k (m - 2) := by
      rw [rotatingMemory]
      simp only [if_neg hm0, if_neg hm1, hmod, Nat.add_zero]
      simp [Finset.sum_range_succ]
    have hprevmod : (m - 1) % k ≠ 0 := by
      intro hprev
      have hkm : k ∣ m := Nat.dvd_iff_mod_eq_zero.mpr hmod
      have hkm1 : k ∣ m - 1 := Nat.dvd_iff_mod_eq_zero.mpr hprev
      have hkone : k ∣ 1 := by
        have hdiff := Nat.dvd_sub hkm hkm1
        have hsub : m - (m - 1) = 1 := by omega
        rw [hsub] at hdiff
        exact hdiff
      have hkle : k ≤ 1 := Nat.le_of_dvd (by omega) hkone
      omega
    have hdouble := nonreset_doubling (m - 1) (by omega) hprevmod
    have hdouble' : rotatingMemory k (m - 1) =
        2 * rotatingMemory k (m - 2) := by
      simpa [Nat.sub_sub] using hdouble
    omega
  have within_block_doubling (j : ℕ) (hj : j < k) :
      rotatingMemory k (k + j) = 2 ^ j * rotatingMemory k k := by
    induction j with
    | zero => simp
    | succ j ih =>
        have hjk : j < k := by omega
        have hmod : (k + (j + 1)) % k ≠ 0 := by
          simp [Nat.mod_eq_of_lt (show j + 1 < k by omega)]
        have hdouble := nonreset_doubling (k + (j + 1)) (by omega) hmod
        calc
          rotatingMemory k (k + (j + 1)) =
              2 * rotatingMemory k (k + j) := by
                simpa [Nat.add_assoc, Nat.add_sub_cancel] using hdouble
          _ = 2 * (2 ^ j * rotatingMemory k k) := by rw [ih hjk]
          _ = 2 ^ (j + 1) * rotatingMemory k k := by
            rw [pow_succ]
            ring
  have period_at_base :
      rotatingMemory k (k + k) = 3 * 2 ^ (k - 2) * rotatingMemory k k := by
    have hblock := within_block_doubling (k - 1) (by omega)
    have hidx : k + (k - 1) = (k + k) - 1 := by omega
    rw [hidx] at hblock
    have hreset := reset_balance (k + k) (by omega) (by simp)
    apply Nat.mul_left_cancel (by decide : 0 < 2)
    calc
      2 * rotatingMemory k (k + k) = 3 * rotatingMemory k ((k + k) - 1) := hreset
      _ = 3 * (2 ^ (k - 1) * rotatingMemory k k) := by rw [hblock]
      _ = 2 * (3 * 2 ^ (k - 2) * rotatingMemory k k) := by
        have hp : k - 1 = (k - 2) + 1 := by omega
        rw [hp, pow_succ]
        ring
  induction n, hn using Nat.le_induction with
  | base =>
      simpa [Nat.add_comm] using period_at_base
  | succ m hm ih =>
      by_cases hreset : (m + 1) % k = 0
      · have hreset' : (m + k + 1) % k = 0 := by
          simpa [Nat.add_mod, Nat.add_mod_right] using hreset
        have hmleft : 4 ≤ m + 1 := by
          by_contra hsmall
          have hm2 : m = 2 := by omega
          have hk2 : k = 2 := by omega
          subst m
          subst k
          norm_num at hreset
        have hleft := reset_balance (m + 1) hmleft hreset
        have hright := reset_balance (m + k + 1) (by omega) hreset'
        have hleft' : 2 * rotatingMemory k (m + 1) = 3 * rotatingMemory k m := by
          simpa using hleft
        have hright' : 2 * rotatingMemory k (m + k + 1) =
            3 * rotatingMemory k (m + k) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hright
        apply Nat.mul_left_cancel (by decide : 0 < 2)
        calc
          2 * rotatingMemory k (m + 1 + k) =
              3 * rotatingMemory k (m + k) := by
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hright'
          _ = 3 * (3 * 2 ^ (k - 2) * rotatingMemory k m) := by rw [ih]
          _ = 3 * 2 ^ (k - 2) * (3 * rotatingMemory k m) := by ring
          _ = 3 * 2 ^ (k - 2) * (2 * rotatingMemory k (m + 1)) := by rw [hleft']
          _ = 2 * (3 * 2 ^ (k - 2) * rotatingMemory k (m + 1)) := by ring
      · have hreset' : (m + k + 1) % k ≠ 0 := by
          simpa [Nat.add_mod, Nat.add_mod_right] using hreset
        have hleft := nonreset_doubling (m + 1) (by omega) hreset
        have hright := nonreset_doubling (m + k + 1) (by omega) hreset'
        have hleft' : rotatingMemory k (m + 1) =
            2 * rotatingMemory k m := by
          simpa using hleft
        have hright' : rotatingMemory k (m + k + 1) =
            2 * rotatingMemory k (m + k) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hright
        calc
          rotatingMemory k (m + 1 + k) = 2 * rotatingMemory k (m + k) := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hright'
          _ = 2 * (3 * 2 ^ (k - 2) * rotatingMemory k m) := by rw [ih]
          _ = 3 * 2 ^ (k - 2) * (2 * rotatingMemory k m) := by ring
          _ = 3 * 2 ^ (k - 2) * rotatingMemory k (m + 1) := by rw [hleft']

theorem tail_hankel_det_ne_zero (k : ℕ) (hk : 2 ≤ k) :
    Matrix.det (fun i j : Fin k => (rotatingMemory k (k + (i : ℕ) + (j : ℕ)) : ℚ)) ≠ 0 := by
  have nonreset_doubling (m : ℕ) (hm : 3 ≤ m) (hmod : m % k ≠ 0) :
      rotatingMemory k m = 2 * rotatingMemory k (m - 1) := by
    have hm0 : m ≠ 0 := by omega
    have hm1 : m ≠ 1 := by omega
    have hprev0 : m - 1 ≠ 0 := by omega
    have hprev1 : m - 1 ≠ 1 := by omega
    have hmod_succ : m % k = (m - 1) % k + 1 := by
      have hpos : 1 ≤ m % k := Nat.one_le_iff_ne_zero.mpr hmod
      have hsub : m % k - 1 = (m - 1) % k := Nat.mod_sub_of_le hpos
      omega
    have hrec_m : rotatingMemory k m = ∑ j ∈ Finset.range (2 + m % k),
        rotatingMemory k (m - (j + 1)) := by
      rw [rotatingMemory]
      simp only [if_neg hm0, if_neg hm1]
    have hrec_prev : rotatingMemory k (m - 1) = ∑ j ∈ Finset.range (2 + (m - 1) % k),
        rotatingMemory k ((m - 1) - (j + 1)) := by
      rw [rotatingMemory]
      simp only [if_neg hprev0, if_neg hprev1]
    let f : ℕ → ℕ := fun j => rotatingMemory k (m - (j + 1))
    have htail : rotatingMemory k (m - 1) = ∑ j ∈ Finset.range (2 + (m - 1) % k),
        f (j + 1) := by
      rw [hrec_prev]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [f]
      congr 1
      omega
    rw [hmod_succ] at hrec_m
    have hrange : 2 + ((m - 1) % k + 1) = 3 + (m - 1) % k := by omega
    rw [hrange] at hrec_m
    calc
      rotatingMemory k m = ∑ j ∈ Finset.range (3 + (m - 1) % k), f j := by
        simpa [f] using hrec_m
      _ = (∑ j ∈ Finset.range (2 + (m - 1) % k), f (j + 1)) + f 0 := by
        rw [show 3 + (m - 1) % k = (2 + (m - 1) % k) + 1 by omega]
        rw [Finset.sum_range_succ']
      _ = rotatingMemory k (m - 1) + rotatingMemory k (m - 1) := by
        rw [← htail]
      _ = 2 * rotatingMemory k (m - 1) := by omega
  have within_block_doubling (j : ℕ) (hj : j < k) :
      rotatingMemory k (k + j) = 2 ^ j * rotatingMemory k k := by
    induction j with
    | zero => simp
    | succ j ih =>
        have hjk : j < k := by omega
        have hmod : (k + (j + 1)) % k ≠ 0 := by
          simp [Nat.mod_eq_of_lt (show j + 1 < k by omega)]
        have hdouble := nonreset_doubling (k + (j + 1)) (by omega) hmod
        calc
          rotatingMemory k (k + (j + 1)) = 2 * rotatingMemory k (k + j) := by
            simpa [Nat.add_assoc, Nat.add_sub_cancel] using hdouble
          _ = 2 * (2 ^ j * rotatingMemory k k) := by rw [ih hjk]
          _ = 2 ^ (j + 1) * rotatingMemory k k := by
            rw [pow_succ]
            ring
  have all_positive : ∀ m : ℕ, 1 ≤ m → 0 < rotatingMemory k m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro hm
        by_cases hm1 : m = 1
        · subst m
          simp [rotatingMemory]
        · have hm0 : m ≠ 0 := by omega
          have hm2 : 2 ≤ m := by omega
          have hprev : 0 < rotatingMemory k (m - 1) := ih (m - 1) (by omega) (by omega)
          rw [rotatingMemory, if_neg hm0, if_neg hm1]
          have hle : rotatingMemory k (m - (0 + 1)) ≤ ∑ j ∈ Finset.range (2 + m % k),
              rotatingMemory k (m - (j + 1)) := Finset.single_le_sum
            (fun i hi => Nat.zero_le (rotatingMemory k (m - (i + 1)))) (by simp)
          exact lt_of_lt_of_le hprev (by simpa using hle)
  let H : Matrix (Fin k) (Fin k) ℚ := fun i j =>
    (rotatingMemory k (k + (i : ℕ) + (j : ℕ)) : ℚ)
  let A : ℚ := rotatingMemory k k
  let C : Matrix (Fin k) (Fin k) ℚ := fun i j => if i.val + j.val < k then 1 else 3 / 4
  have hA_positive : 0 < A := by dsimp [A]; exact_mod_cast all_positive k (by omega)
  have hA_ne : A ≠ 0 := ne_of_gt hA_positive
  have hankel_factorization (i j : Fin k) : H i j =
      A * (2 : ℚ) ^ i.val * C i j * (2 : ℚ) ^ j.val := by
    by_cases hij : i.val + j.val < k
    · have hwithin_nat := within_block_doubling (i.val + j.val) hij
      have hwithin : (rotatingMemory k (k + (i.val + j.val)) : ℚ) =
          (2 : ℚ) ^ (i.val + j.val) * A := by
        dsimp [A]; exact_mod_cast hwithin_nat
      rw [show H i j = (rotatingMemory k (k + (i.val + j.val)) : ℚ) by
        simp [H, Nat.add_assoc]]
      rw [hwithin, show C i j = 1 by simp [C, hij], pow_add]
      ring
    · have hsum_ge : k ≤ i.val + j.val := by omega
      have htail_lt : i.val + j.val - k < k := by
        have hi := i.isLt
        have hj := j.isLt
        omega
      have hwithin_nat := within_block_doubling (i.val + j.val - k) htail_lt
      have hwithin_at_sum_nat : rotatingMemory k (i.val + j.val) =
          2 ^ (i.val + j.val - k) * rotatingMemory k k := by
        simpa [show k + (i.val + j.val - k) = i.val + j.val by omega]
          using hwithin_nat
      have hwithin_at_sum : (rotatingMemory k (i.val + j.val) : ℚ) =
          (2 : ℚ) ^ (i.val + j.val - k) * A := by
        dsimp [A]; exact_mod_cast hwithin_at_sum_nat
      have hperiod_nat := period_collapse k (i.val + j.val) hk hsum_ge
      have hperiod : (rotatingMemory k (i.val + j.val + k) : ℚ) =
          3 * (2 : ℚ) ^ (k - 2) * (rotatingMemory k (i.val + j.val) : ℚ) := by
        exact_mod_cast hperiod_nat
      have hexponents : (k - 2) + (i.val + j.val - k) = i.val + j.val - 2 := by
        omega
      have hpower_split : (2 : ℚ) ^ (i.val + j.val) =
          4 * (2 : ℚ) ^ (i.val + j.val - 2) := by
        calc
          (2 : ℚ) ^ (i.val + j.val) =
              (2 : ℚ) ^ ((i.val + j.val - 2) + 2) := by congr 1; omega
          _ = (2 : ℚ) ^ (i.val + j.val - 2) * (2 : ℚ) ^ 2 := by rw [pow_add]
          _ = 4 * (2 : ℚ) ^ (i.val + j.val - 2) := by ring
      have hpowers : (2 : ℚ) ^ i.val * (2 : ℚ) ^ j.val =
          4 * (2 : ℚ) ^ (i.val + j.val - 2) := by
        rw [← pow_add, hpower_split]
      rw [show H i j = (rotatingMemory k (i.val + j.val + k) : ℚ) by
        simp [H, Nat.add_comm, Nat.add_left_comm]]
      rw [hperiod, hwithin_at_sum, show C i j = 3 / 4 by simp [C, hij]]
      calc
        3 * (2 : ℚ) ^ (k - 2) * ((2 : ℚ) ^ (i.val + j.val - k) * A) =
            3 * (2 : ℚ) ^ (i.val + j.val - 2) * A := by
              calc
                3 * (2 : ℚ) ^ (k - 2) * ((2 : ℚ) ^ (i.val + j.val - k) * A) =
                    3 * ((2 : ℚ) ^ (k - 2) * (2 : ℚ) ^ (i.val + j.val - k)) * A := by
                      ring
                _ = 3 * (2 : ℚ) ^ (i.val + j.val - 2) * A := by
                  rw [← pow_add, hexponents]
        _ = A * ((2 : ℚ) ^ i.val * (2 : ℚ) ^ j.val) * (3 / 4) := by
              rw [hpowers]
              ring
        _ = A * (2 : ℚ) ^ i.val * (3 / 4) * (2 : ℚ) ^ j.val := by ring
  have kernel_trivial : ∀ x : Fin k → ℚ, H.mulVec x = 0 → x = 0 := by
    intro x hx
    let y : Fin k → ℚ := fun j => (2 : ℚ) ^ j.val * x j
    have row_equation (i : Fin k) : ∑ j, C i j * y j = 0 := by
      have hi := congrFun hx i
      change (∑ j, H i j * x j) = 0 at hi
      have hfactored : (A * (2 : ℚ) ^ i.val) * (∑ j, C i j * y j) = 0 := by
        calc
          (A * (2 : ℚ) ^ i.val) * (∑ j, C i j * y j) = ∑ j, H i j * x j := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j hj
                rw [hankel_factorization]
                dsimp [y]
                ring
          _ = 0 := hi
      exact (mul_eq_zero.mp hfactored).resolve_left
        (mul_ne_zero hA_ne (pow_ne_zero _ (by norm_num)))
    have hy_pos (j : Fin k) (hj : 0 < j.val) : y j = 0 := by
      let r0 : Fin k := ⟨k - j.val - 1, by omega⟩
      let r1 : Fin k := ⟨k - j.val, by omega⟩
      have hrow0 := row_equation r0
      have hrow1 := row_equation r1
      have hdiff : ∑ l, (C r0 l - C r1 l) * y l = 0 := by
        calc
          ∑ l, (C r0 l - C r1 l) * y l =
              ∑ l, (C r0 l * y l - C r1 l * y l) := by
                apply Finset.sum_congr rfl
                intro l hl
                ring
          _ = (∑ l, C r0 l * y l) - ∑ l, C r1 l * y l := by
            rw [Finset.sum_sub_distrib]
          _ = 0 := by rw [hrow0, hrow1, sub_zero]
      have hcoefficient (l : Fin k) :
          C r0 l - C r1 l = if l = j then (1 : ℚ) / 4 else 0 := by
        dsimp [C, r0, r1]
        split <;> split <;> split <;> norm_num <;> omega
      simp_rw [hcoefficient] at hdiff
      have hisolated : (1 : ℚ) / 4 * y j = 0 := by simpa using hdiff
      linarith
    let z : Fin k := ⟨0, by omega⟩
    have hsum : ∑ j, y j = 0 := by simpa [C, z] using row_equation z
    have hsum_single : (∑ j, y j) = y z := by
      apply Finset.sum_eq_single z
      · intro j hj hjz
        apply hy_pos j
        have hj_ne_zero : j.val ≠ 0 := by
          intro hj0
          apply hjz
          exact Fin.ext hj0
        omega
      · simp
    have hy_zero : y z = 0 := by rw [hsum_single] at hsum; exact hsum
    have hy_all (j : Fin k) : y j = 0 := by
      by_cases hj : j.val = 0
      · have hjz : j = z := Fin.ext hj
        simpa [hjz] using hy_zero
      · exact hy_pos j (by omega)
    funext j
    have hj := hy_all j
    dsimp [y] at hj
    exact (mul_eq_zero.mp hj).resolve_left (pow_ne_zero _ (by norm_num))
  have hinjective : Function.Injective H.mulVec := by
    intro x y hxy
    have hzero : H.mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    exact sub_eq_zero.mp (kernel_trivial (x - y) hzero)
  change H.det ≠ 0
  have hunit : IsUnit H := Matrix.mulVec_injective_iff_isUnit.mp hinjective
  exact ((Matrix.isUnit_iff_isUnit_det H).mp hunit).ne_zero

end D5.S1.Recurrence.Periodic.RotatingMemoryFibonacciPeriodCollapse
