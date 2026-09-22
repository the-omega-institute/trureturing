/- GID: D5/S3/Arith/Powerful/PowerfulNumber
   generality: G
   mirror-B: D5/B/S3/Arith/Powerful/PowerfulNumber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Squarefree]
   utility: none
   digest: Powerful positive integers are products of a square and a cube. -/

import Mathlib.Data.Nat.Squarefree

set_option autoImplicit false
set_option linter.dupNamespace false

namespace D5.S3.Arith.Powerful.PowerfulNumber

/-- A natural number is powerful when it is nonzero and every prime divisor has its square as a divisor. -/
def Powerful (n : ℕ) : Prop :=
  n ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- Golomb's representation: every positive powerful integer is a square times a cube. -/
theorem golomb_representation {n : ℕ} (hn : 1 ≤ n) (hpower : Powerful n) :
    ∃ a b : ℕ, n = a ^ 2 * b ^ 3 ∧ Squarefree b := by
  obtain ⟨c, d, hdc, hc⟩ := Nat.sq_mul_squarefree n
  have hn0 : n ≠ 0 := by omega
  have hc0 : c ≠ 0 := hc.ne_zero
  have hd0 : d ≠ 0 := by
    intro hd
    exact hn0 (by simpa [hd] using hdc.symm)
  have hcd : c ∣ d := by
    rw [← Nat.factorization_le_iff_dvd hc0 hd0]
    intro p
    by_cases hp : p.Prime
    · by_cases hcp : c.factorization p = 0
      · simp [hcp]
      · have hcp' : 1 ≤ c.factorization p := by omega
        have hcp1 : c.factorization p = 1 :=
          (hc.natFactorization_le_one p).antisymm hcp'
        have hpp : 2 ≤ n.factorization p := by
          apply (hp.pow_dvd_iff_le_factorization hn0).mp
          apply hpower.2 p hp
          rw [← hdc]
          exact dvd_mul_of_dvd_right
            ((hp.dvd_iff_one_le_factorization hc0).mpr hcp') _
        have hfac : n.factorization p = 2 * d.factorization p + c.factorization p := by
          rw [← hdc, Nat.factorization_mul (pow_ne_zero 2 hd0) hc0,
            Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
        rw [hfac, hcp1] at hpp
        omega
    · simp [Nat.factorization_eq_zero_of_not_prime c hp]
  rcases hcd with ⟨e, rfl⟩
  refine ⟨e, c, ?_, hc⟩
  rw [← hdc]
  ring

end D5.S3.Arith.Powerful.PowerfulNumber
