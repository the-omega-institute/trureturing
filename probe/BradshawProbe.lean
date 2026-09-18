import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum.Prime

/-!
Refutation of Bradshaw, JIS 28 (2025), Article 25.1.8, Conjecture 20.
Preregistered in the-omega-institute/trureturing issue #8643.
The public surface is exactly the source predicates/map, the claim, and its negation.
-/

set_option autoImplicit false

def IsArithmeticDerivative (D : ℕ → ℕ) : Prop :=
  D 0 = 0 ∧ D 1 = 0 ∧ (∀ p, p.Prime → D p = 1) ∧
    ∀ m n, D (m * n) = D m * n + m * D n

def C (a b n : ℕ) : ℕ :=
  if n % 2 = 1 then (a * n + b) / 2 else n / 2

def claim : Prop :=
  ∀ D : ℕ → ℕ, IsArithmeticDerivative D → ∀ a b n : ℕ,
    a % 2 = b % 2 → 1 ≤ n → D (C a b n) = C a b (D n) → Squarefree n

theorem result : ¬ claim := by
  classical
  -- Construct an actual derivative, including its values and product rule at zero.
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
  -- These values follow only from the four axioms, for every admissible D.
  have values : ∀ D : ℕ → ℕ, IsArithmeticDerivative D →
      D 125 = 75 ∧ D 1066 = 641 ∧ D 75 = 55 := by
    intro D hD
    have h2 : D 2 = 1 := hD.2.2.1 2 (by norm_num)
    have h3 : D 3 = 1 := hD.2.2.1 3 (by norm_num)
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
    have h75 : D 75 = 55 := by
      have h := hD.2.2.2 3 25
      norm_num [h3, h25] at h
      exact h
    exact ⟨h125, h1066, h75⟩
  intro hclaim
  obtain ⟨h125, h1066, _h75⟩ := values D0 hD0
  have hcomm : D0 (C 17 7 125) = C 17 7 (D0 125) := by
    norm_num [C, h125, h1066]
  have hsq := hclaim D0 hD0 17 7 125 (by norm_num) (by norm_num) hcomm
  exact (Nat.squarefree_iff_prime_squarefree.mp hsq) 5 (by norm_num) (by norm_num)

#print axioms result
