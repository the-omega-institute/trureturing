/- GID: D5/S0/Certificates/BradshawConjectureTwentyRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/BradshawConjectureTwentyRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/BradshawConjectureTwentyRefutation.claim; result=D5/S0/Certificates/BradshawConjectureTwentyRefutation.result; claim=D5/S0/Certificates/BradshawConjectureTwentyRefutation.claim
   digest: The nonsquarefree input 125 refutes Bradshaw's generalized Collatz conjecture. -/

import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.BradshawConjectureTwentyRefutation

/-- Bradshaw's arithmetic derivative properties, including the values at zero and one. -/
def IsArithmeticDerivative (D : ℕ → ℕ) : Prop :=
  D 0 = 0 ∧ D 1 = 0 ∧ (∀ p, p.Prime → D p = 1) ∧
    ∀ m n, D (m * n) = D m * n + m * D n

/-- Bradshaw's generalized Collatz map, with natural-number division. -/
def C (a b n : ℕ) : ℕ :=
  if n % 2 = 1 then (a * n + b) / 2 else n / 2

/-- Conjecture 20 restricted to positive inputs; this is weaker than the source claim. -/
def claim : Prop :=
  ∀ D : ℕ → ℕ, IsArithmeticDerivative D → ∀ a b n : ℕ,
    a % 2 = b % 2 → 1 ≤ n → D (C a b n) = C a b (D n) → Squarefree n

/-- The arithmetic derivative commutes with `C 17 7` at the nonsquarefree input `125`. -/
theorem result : ¬ claim := by
  classical
  let D0 : ℕ → ℕ := fun n => n.factorization.sum (fun p k => k * (n / p))
  have hD0 : IsArithmeticDerivative D0 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [D0]
    · simp [D0]
    · intro p hp
      simp [D0, hp.factorization, Nat.div_self hp.pos]
    · intro m n
      by_cases hm : m = 0
      · subst m
        simp [D0]
      by_cases hn : n = 0
      · subst n
        simp [D0]
      change (m * n).factorization.sum (fun p k => k * (m * n / p)) =
        m.factorization.sum (fun p k => k * (m / p)) * n +
          m * n.factorization.sum (fun p k => k * (n / p))
      rw [Nat.factorization_mul hm hn,
        Finsupp.sum_add_index' (fun _ => zero_mul _)
          (fun _ _ _ => add_mul _ _ _), Finsupp.sum_mul, Finsupp.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro p hp
        have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hp
        change m.factorization p * (m * n / p) = m.factorization p * (m / p) * n
        rw [mul_comm m n, Nat.mul_div_assoc n hpm]
        ac_rfl
      · apply Finset.sum_congr rfl
        intro p hp
        have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
        change n.factorization p * (m * n / p) = m * (n.factorization p * (n / p))
        rw [Nat.mul_div_assoc m hpn]
        ac_rfl
  -- The numerical values use only the defining properties, without unfolding D0.
  have values : ∀ D : ℕ → ℕ, IsArithmeticDerivative D →
      D 125 = 75 ∧ D 1066 = 641 := by
    intro D hD
    have h2 : D 2 = 1 := hD.2.2.1 2 (by norm_num)
    have h5 : D 5 = 1 := hD.2.2.1 5 (by norm_num)
    have h13 : D 13 = 1 := hD.2.2.1 13 (by norm_num)
    have h41 : D 41 = 1 := hD.2.2.1 41 (by norm_num)
    have h25 : D 25 = 10 := by
      have h := hD.2.2.2 5 5
      norm_num [h5] at h
      exact h
    have h125 : D 125 = 75 := by
      have h := hD.2.2.2 5 25
      norm_num [h5, h25] at h
      exact h
    have h533 : D 533 = 54 := by
      have h := hD.2.2.2 13 41
      norm_num [h13, h41] at h
      exact h
    have h1066 : D 1066 = 641 := by
      have h := hD.2.2.2 2 533
      norm_num [h2, h533] at h
      exact h
    exact ⟨h125, h1066⟩
  intro hclaim
  obtain ⟨h125, h1066⟩ := values D0 hD0
  have hcomm : D0 (C 17 7 125) = C 17 7 (D0 125) := by
    norm_num [C, h125, h1066]
  have hsq := hclaim D0 hD0 17 7 125 (by norm_num) (by norm_num) hcomm
  exact (Nat.squarefree_iff_prime_squarefree.mp hsq) 5 (by norm_num) (by norm_num)

#print axioms result

end D5.S0.Certificates.BradshawConjectureTwentyRefutation
