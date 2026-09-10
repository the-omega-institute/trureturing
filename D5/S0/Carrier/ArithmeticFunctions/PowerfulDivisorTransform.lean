/- GID: D5/S0/Carrier/ArithmeticFunctions/PowerfulDivisorTransform
   generality: G
   mirror-B: D5/B/S0/Carrier/ArithmeticFunctions/PowerfulDivisorTransform
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Powerful-divisor sums preserve multiplicativity and are inverse Moebius transforms. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Powerful-divisor transforms

This module proves Werner Schulte's 2025 conjecture recorded in OEIS A069208.  The
characteristic function of the powerful numbers is A112526.
-/

namespace D5.S0.Carrier.ArithmeticFunctions.PowerfulDivisorTransform

open scoped ArithmeticFunction.zeta BigOperators

noncomputable section

/-- A positive natural number is powerful when every prime divisor has its square as a divisor. -/
def Powerful (n : ℕ) : Prop :=
  n ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- The characteristic arithmetic function of the powerful numbers (OEIS A112526). -/
def powerfulIndicator : ArithmeticFunction ℕ :=
  by
    classical
    exact ⟨fun n ↦ if Powerful n then 1 else 0, by simp [Powerful]⟩

/-- The sum of an arithmetic function over the powerful divisors of an integer. -/
def powerfulDivisorSum {R : Type*} [AddCommMonoid R] (f : ArithmeticFunction R) :
    ArithmeticFunction R :=
  by
    classical
    exact ⟨fun n ↦ ∑ d ∈ n.divisors.filter Powerful, f d, by simp⟩

private theorem powerful_mul_iff {m n : ℕ} (hmn : m.Coprime n) :
    Powerful (m * n) ↔ Powerful m ∧ Powerful n := by
  constructor
  · intro h
    have hm0 : m ≠ 0 := fun hm ↦ h.1 (by simp [hm])
    have hn0 : n ≠ 0 := fun hn ↦ h.1 (by simp [hn])
    refine ⟨⟨hm0, ?_⟩, ⟨hn0, ?_⟩⟩
    · intro p hp hpm
      exact (hmn.coprime_dvd_left hpm).pow_left 2 |>.dvd_of_dvd_mul_right
        (h.2 p hp (hpm.trans (dvd_mul_right m n)))
    · intro p hp hpn
      exact (hmn.coprime_dvd_right hpn).pow_right 2 |>.symm.dvd_of_dvd_mul_left
        (h.2 p hp (hpn.trans (dvd_mul_left n m)))
  · rintro ⟨hm, hn⟩
    refine ⟨mul_ne_zero hm.1 hn.1, ?_⟩
    intro p hp hpmn
    rcases hp.dvd_mul.mp hpmn with hpm | hpn
    · exact (hm.2 p hp hpm).mul_right n
    · exact (hn.2 p hp hpn).mul_left m

private theorem powerfulIndicator_isMultiplicative :
    powerfulIndicator.IsMultiplicative := by
  classical
  constructor
  · simp [powerfulIndicator, Powerful]
  · intro m n hmn
    change (if Powerful (m * n) then 1 else 0) =
      (if Powerful m then 1 else 0) * (if Powerful n then 1 else 0)
    rw [if_congr (powerful_mul_iff hmn) rfl rfl]
    by_cases hm : Powerful m <;> simp [hm]

/-- Powerful-divisor summation is the inverse Moebius transform of A112526 times `f`. -/
theorem powerfulDivisorSum_eq_inverseMoebius {R : Type*} [CommSemiring R]
    (f : ArithmeticFunction R) :
    powerfulDivisorSum f =
      (ζ : ArithmeticFunction R) * ((powerfulIndicator : ArithmeticFunction R).pmul f) := by
  classical
  ext n
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  simp only [powerfulDivisorSum, ArithmeticFunction.coe_mk,
    ArithmeticFunction.pmul_apply, ArithmeticFunction.natCoe_apply]
  simp only [powerfulIndicator, ArithmeticFunction.coe_mk]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : Powerful d <;> simp [hd]

/-- Summing a multiplicative arithmetic function over powerful divisors remains multiplicative. -/
theorem powerfulDivisorSum_isMultiplicative {R : Type*} [CommSemiring R]
    {f : ArithmeticFunction R} (hf : f.IsMultiplicative) :
    (powerfulDivisorSum f).IsMultiplicative := by
  rw [powerfulDivisorSum_eq_inverseMoebius]
  exact ArithmeticFunction.isMultiplicative_zeta.natCast.mul
    (powerfulIndicator_isMultiplicative.natCast.pmul hf)

example : ∃ f : ArithmeticFunction ℕ,
    f.IsMultiplicative ∧ f ≠ 0 ∧ (powerfulDivisorSum f).IsMultiplicative := by
  refine ⟨ArithmeticFunction.pow 1, ArithmeticFunction.isMultiplicative_pow, ?_,
    powerfulDivisorSum_isMultiplicative ArithmeticFunction.isMultiplicative_pow⟩
  intro h
  have h1 := congrArg (fun g : ArithmeticFunction ℕ ↦ g 1) h
  simp at h1

end

end D5.S0.Carrier.ArithmeticFunctions.PowerfulDivisorTransform
