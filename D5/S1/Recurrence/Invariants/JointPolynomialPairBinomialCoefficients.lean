/- GID: D5/S1/Recurrence/Invariants/JointPolynomialPairBinomialCoefficients
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/JointPolynomialPairBinomialCoefficients
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [Mathlib.Data.Nat.Choose.Sum]
   utility: none
   digest: The joint polynomial recursion has Schulte's conjectured binomial coefficients. -/

import Mathlib.Data.Nat.Choose.Sum

namespace D5.S1.Recurrence.Invariants.JointPolynomialPairBinomialCoefficients

open Finset

/-- Coefficient sequences of the jointly generated pair, with stage zero
corresponding to the OEIS initial polynomials `u(1,x) = v(1,x) = 1`. -/
def coefficientPair : Nat -> (Nat -> Nat) × (Nat -> Nat)
  | 0 => (fun i => if i = 0 then 1 else 0, fun i => if i = 0 then 1 else 0)
  | n + 1 =>
      (fun i =>
        (coefficientPair n).1 i +
          if i = 0 then 0 else (coefficientPair n).2 (i - 1),
       fun i =>
        if i = 0 then 0
        else (coefficientPair n).1 (i - 1) + (coefficientPair n).2 (i - 1))

/-- The coefficients of `u(n,x)` in the OEIS recursion. -/
def u (n i : Nat) : Nat := (coefficientPair (n - 1)).1 i

/-- The coefficients of `v(n,x)` in the OEIS recursion. -/
def v (n i : Nat) : Nat := (coefficientPair (n - 1)).2 i

/-- The triangular entry `T(n,k) = [x^(k-1)] u(n,x)`. -/
def T (n k : Nat) : Nat := u n (k - 1)

/-- Werner Schulte's 2017 conjecture for OEIS A208342. -/
theorem schulte_a208342 : forall n k : Nat, 0 < k -> k <= n ->
    T n k =
      ∑ j ∈ range ((k - 1) / 2 + 1),
        Nat.choose (k - 1 - j) j * Nat.choose (n - k + j) j := by
  intro n k hk hkn
  let A : Nat -> Nat -> Nat := fun m i =>
    ∑ j ∈ range (i + 1), Nat.choose (i - j) j * Nat.choose (m - i + j) j
  let B : Nat -> Nat -> Nat := fun m i =>
    (if i = m then 1 else 0) +
      ∑ r ∈ range (i + 1), Nat.choose (i - r) (r + 1) * Nat.choose (m - i + r) r
  have closed : forall m i : Nat,
      ((coefficientPair m).1 i = if i <= m then A m i else 0) ∧
      ((coefficientPair m).2 i = if i <= m then B m i else 0) := by
    intro m
    induction m with
    | zero =>
        intro i
        by_cases hi : i = 0
        · subst i
          simp [coefficientPair, A, B]
        · have hi' : ¬i <= 0 := by omega
          simp [coefficientPair, hi, hi']
    | succ m ih =>
        intro i
        by_cases hi0 : i = 0
        · subst i
          have hu0 := (ih 0).1
          constructor
          · simpa [coefficientPair, A] using hu0
          · simp [coefficientPair, B]
        · have hi : 0 < i := Nat.pos_of_ne_zero hi0
          rcases ih i with ⟨ihu, ihv⟩
          rcases ih (i - 1) with ⟨ihu', ihv'⟩
          simp only [coefficientPair]
          constructor
          · by_cases him : i <= m
            · have him' : i - 1 <= m := by omega
              have his : i <= m + 1 := by omega
              rw [if_neg hi0, ihu, if_pos him, ihv', if_pos him', if_pos his]
              have hA : A (m + 1) i = A m i + B m (i - 1) := by
                simp only [A, B]
                rw [if_neg (by omega : ¬i - 1 = m)]
                rw [show i - 1 + 1 = i by omega]
                rw [sum_range_succ', sum_range_succ']
                simp only [Nat.choose_zero_right, mul_one]
                rw [zero_add]
                have hsum :
                    (∑ r ∈ range i,
                      Nat.choose (i - (r + 1)) (r + 1) *
                        Nat.choose (m + 1 - i + (r + 1)) (r + 1)) =
                    (∑ r ∈ range i,
                      Nat.choose (i - (r + 1)) (r + 1) *
                        Nat.choose (m - i + (r + 1)) (r + 1)) +
                    ∑ r ∈ range i,
                      Nat.choose (i - 1 - r) (r + 1) *
                        Nat.choose (m - (i - 1) + r) r := by
                  rw [← sum_add_distrib]
                  apply sum_congr rfl
                  intro r hr
                  have hrlt : r < i := mem_range.mp hr
                  have htop : m + 1 - i + (r + 1) =
                      (m - i + (r + 1)) + 1 := by omega
                  have hfirst : i - 1 - r = i - (r + 1) := by omega
                  have hsecond : m - (i - 1) + r = m - i + (r + 1) := by omega
                  rw [htop, Nat.choose_succ_succ', hfirst, hsecond, mul_add]
                  ac_rfl
                omega
              exact hA.symm
            · by_cases hib : i = m + 1
              · subst i
                rw [if_neg (by omega : ¬m + 1 = 0), ihu, if_neg (by omega),
                  ihv', if_pos (by omega), if_pos (by omega)]
                have hA : A (m + 1) (m + 1) = B m m := by
                  simp [A, B, sum_range_succ']; omega
                simpa using hA.symm
              · have hgt : m + 1 < i := by omega
                rw [if_neg hi0, ihu, if_neg (by omega), ihv', if_neg (by omega),
                  if_neg (by omega)]
          · by_cases him : i <= m
            · have him' : i - 1 <= m := by omega
              have his : i <= m + 1 := by omega
              rw [if_neg hi0, ihu', if_pos him', ihv', if_pos him', if_pos his]
              have hB : B (m + 1) i = A m (i - 1) + B m (i - 1) := by
                simp only [A, B]
                rw [if_neg (by omega : ¬i = m + 1), if_neg (by omega : ¬i - 1 = m)]
                rw [show i - 1 + 1 = i by omega]
                rw [zero_add, zero_add, sum_range_succ]
                simp only [Nat.sub_self, Nat.choose_zero_succ, zero_mul, add_zero]
                rw [← sum_add_distrib]
                apply sum_congr rfl
                intro r hr
                have hrlt : r < i := mem_range.mp hr
                have hfirst : i - r = (i - 1 - r) + 1 := by omega
                have hsecond : m + 1 - i + r = m - (i - 1) + r := by omega
                rw [hfirst, Nat.choose_succ_succ', hsecond, add_mul]
              exact hB.symm
            · by_cases hib : i = m + 1
              · subst i
                rw [if_neg (by omega : ¬m + 1 = 0), ihu', if_pos (by omega),
                  ihv', if_pos (by omega), if_pos (by omega)]
                have hB : B (m + 1) (m + 1) = A m m + B m m := by
                  simp only [A, B]
                  simp only [if_true]
                  rw [sum_range_succ]
                  simp only [Nat.sub_self, zero_add, Nat.choose_self, mul_one,
                    Nat.choose_zero_succ, add_zero]
                  have hsum :
                      (∑ r ∈ range (m + 1), Nat.choose (m + 1 - r) (r + 1)) =
                      (∑ r ∈ range (m + 1), Nat.choose (m - r) r) +
                        ∑ r ∈ range (m + 1), Nat.choose (m - r) (r + 1) := by
                    rw [← sum_add_distrib]
                    apply sum_congr rfl
                    intro r hr
                    have hrlt : r < m + 1 := mem_range.mp hr
                    have hfirst : m + 1 - r = (m - r) + 1 := by omega
                    rw [hfirst, Nat.choose_succ_succ']
                  rw [hsum]
                  omega
                exact hB.symm
              · have hgt : m + 1 < i := by omega
                rw [if_neg hi0, ihu', if_neg (by omega), ihv', if_neg (by omega),
                  if_neg (by omega)]
  have hi : k - 1 <= n - 1 := by omega
  have hmain := (closed (n - 1) (k - 1)).1
  rw [T, u, hmain, if_pos hi]
  simp only [A]
  have hsub : n - 1 - (k - 1) = n - k := by omega
  rw [hsub]
  symm
  apply sum_subset (range_mono (by omega))
  intro j hjLarge hjSmall
  have hj : (k - 1) / 2 + 1 <= j := by simpa using hjSmall
  have hlt : k - 1 - j < j := by omega
  simp [Nat.choose_eq_zero_of_lt hlt]

#print axioms schulte_a208342

end D5.S1.Recurrence.Invariants.JointPolynomialPairBinomialCoefficients
