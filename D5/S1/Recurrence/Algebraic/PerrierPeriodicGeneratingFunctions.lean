/- GID: D5/S1/Recurrence/Algebraic/PerrierPeriodicGeneratingFunctions
   generality: G
   mirror-B: D5/B/S1/Recurrence/Algebraic/PerrierPeriodicGeneratingFunctions
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Perrier's period-one series satisfy both numerator identities over commutative rings. -/

import Mathlib.RingTheory.PowerSeries.Inverse

/-!
R. Perrier, *Multidimensional Continued Fractions and Riordan Arrays*,
ECA 6:4 (2026), DOI 10.54550/ECA2026V6S4R33, Section 5 (printed pp. 14–15),
states the recurrence and the conjectured generating functions without naming a
coefficient domain. The ambient construction is integral: its companion matrices
have 'nonnegative integer entries' (printed p. 7), and its period parameter is
k ∈ ℤ>0 in the 2×2 section and k ∈ ℤ in the 3×3 section. An arbitrary-field
statement cannot be instantiated at ℤ; the commutative-ring statement here can.

The constant term of D is 1, a unit in every commutative ring. Consequently D is
an invertible formal power series, and the multiplicative identities R₁ · D = P
and Rₖ · D = Q are equivalent to the printed quotients R₁(t) = P(t)/D(t) and
Rₖ(t) = Q(t)/D(t). The multiplicative form states these identities over a ring.

Set k = d + 1, with arbitrary d : ℕ, including d = 0. Natural time zero is
source time minus one. The shifted generating-function convention comes from
printed pp. 8 and 12; Section 5 says 'The same method extends to higher dimensions'
without repeating that definition. The subsequent conjecture concerning equation
(7) is outside this result. Preregistration and domain correction:
https://github.com/the-omega-institute/trureturing/issues/8627.
-/

set_option autoImplicit false

namespace D5.S1.Recurrence.Algebraic.PerrierPeriodicGeneratingFunctions
noncomputable section
open PowerSeries
open scoped BigOperators

variable {K : Type*} [CommRing K] {d : ℕ}

/-- Natural time zero is the source's time minus one. -/
def Recurrence (m a : Fin d → K) (r : ℕ → Fin (d + 1) → K) : Prop :=
  r 0 0 = 1 ∧ (∀ j, r 0 j.succ = a j) ∧
  (∀ n, r (n + 1) 0 = r n (Fin.last d)) ∧
  (∀ n j, r (n + 1) j.succ = r n j.castSucc + m j * r n (Fin.last d))

/-- The shifted generating function: coefficient n is source time n minus one. -/
def R (r : ℕ → Fin (d + 1) → K) (j : Fin (d + 1)) : PowerSeries K :=
  PowerSeries.mk (fun n => r n j)

/-- The common denominator printed in Perrier, Section 5. -/
def D (m : Fin d → K) : PowerSeries K :=
  1 - ∑ j : Fin d, C (m j) * X^(d - j.val) - X^(d + 1)

/-- The first-coordinate numerator printed in Perrier, Section 5. -/
def P (m a : Fin d → K) : PowerSeries K :=
  1 + ∑ j : Fin d, C (a j - m j) * X^(d - j.val)

/-- The last-coordinate numerator printed in Perrier, Section 5. -/
def Q (a : Fin d → K) : PowerSeries K :=
  X^d + ∑ j : Fin d, C (a j) * X^(d - 1 - j.val)

/-- Perrier, Section 5: the two shifted generating functions for every recurrence solution. -/
theorem result (m a : Fin d → K) (r : ℕ → Fin (d + 1) → K)
    (h : Recurrence m a r) :
    R r 0 * D m = P m a ∧ R r (Fin.last d) * D m = Q a := by
  classical
  obtain ⟨hz, ha, hn, hj⟩ := h
  have h0 : R r 0 = 1 + X * R r (Fin.last d) := by
    ext n
    cases n with
    | zero => simpa [R] using hz
    | succ n => simpa [R] using hn n
  have hs (j : Fin d) : R r j.succ =
      C (a j) + X * (R r j.castSucc + C (m j) * R r (Fin.last d)) := by
    ext n
    cases n with
    | zero => simpa [R] using ha j
    | succ n => simpa [R] using hj n j
  let A : PowerSeries K := ∑ j : Fin d, C (a j) * X^(d - 1 - j.val)
  let M : PowerSeries K := ∑ j : Fin d, C (m j) * X^(d - j.val)
  let T : PowerSeries K := ∑ j : Fin d, X^(d - j.val) * R r j.castSucc
  have hexp (j : Fin d) : d - j.val = (d - 1 - j.val)+1 := by omega
  have htel : X^d * R r 0 +
      (∑ j : Fin d, X^(d - 1 - j.val) * R r j.succ) = T + R r (Fin.last d) := by
    have hb := (Fin.sum_univ_succ (fun j : Fin (d + 1) =>
      (X : PowerSeries K)^(d - j.val) * R r j)).symm.trans
      (Fin.sum_univ_castSucc (fun j : Fin (d + 1) =>
        (X : PowerSeries K)^(d - j.val) * R r j))
    simpa [T, Nat.sub_sub, Nat.add_comm] using hb
  have hsum : (∑ j : Fin d, X^(d - 1 - j.val) * R r j.succ) =
      A + T + M * R r (Fin.last d) := by
    calc
      _ = ∑ j : Fin d, (C (a j) * X^(d - 1 - j.val) +
          X^(d - j.val) * R r j.castSucc +
          (C (m j) * X^(d - j.val)) * R r (Fin.last d)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hs, hexp, pow_succ]
        ring
      _ = _ := by simp [A, T, M, Finset.sum_add_distrib, Finset.sum_mul]
  have hbalance : R r (Fin.last d) =
      X^d * R r 0 + A + M * R r (Fin.last d) := by
    rw [hsum] at htel
    apply add_left_cancel (a := T)
    calc
      T + R r (Fin.last d) = X^d * R r 0 + (A + T + M * R r (Fin.last d)) := htel.symm
      _ = T + (X^d * R r 0 + A + M * R r (Fin.last d)) := by ring
  have hlast : R r (Fin.last d) * D m = Q a := by
    have heq : R r (Fin.last d) =
        (X^d + A) + (X^(d + 1) + M) * R r (Fin.last d) := by
      calc
        _ = X^d * (1 + X * R r (Fin.last d)) + A + M * R r (Fin.last d) := by
          rw [← h0]
          exact hbalance
        _ = _ := by rw [pow_succ]; ring
    calc
      _ = R r (Fin.last d) - (X^(d + 1) + M) * R r (Fin.last d) := by
        dsimp [D, M]
        ring
      _ = X^d + A := sub_eq_of_eq_add heq
      _ = Q a := rfl
  have hQP : D m + X * Q a = P m a := by
    have hA : X * A = ∑ j : Fin d, C (a j) * X^(d - j.val) := by
      dsimp [A]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hexp, pow_succ]
      ring
    change 1 - M - X^(d + 1) + X * (X^d + A) = P m a
    rw [mul_add, hA, pow_succ]
    simp only [P, map_sub, sub_mul, Finset.sum_sub_distrib]
    dsimp [M]
    ring
  have hfirst : R r 0 * D m = P m a := by
    rw [h0]
    calc
      _ = D m + X * (R r (Fin.last d) * D m) := by ring
      _ = P m a := by rw [hlast]; exact hQP
  exact ⟨hfirst, hlast⟩

end
end D5.S1.Recurrence.Algebraic.PerrierPeriodicGeneratingFunctions
