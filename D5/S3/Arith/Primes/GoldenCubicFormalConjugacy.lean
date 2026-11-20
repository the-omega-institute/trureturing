/- GID: D5/S3/Arith/Primes/GoldenCubicFormalConjugacy
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicFormalConjugacy
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: A root-free rational formal series conjugates every Chebyshev multiplier to rescaling. -/

import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Arith.Primes.GoldenCubicFormalConjugacy

open PowerSeries

/-- The root-free linearizing coordinate over the rationals as formal coefficients.
The p-adic evaluation and inverse are separate analytic assertions. -/
noncomputable def coordinate : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n = 0 then 0 else 2 / ((2*n).factorial : ℚ)

@[simp] theorem coeff_coordinate (n : ℕ) :
    coeff n coordinate = if n = 0 then 0 else 2 / ((2*n).factorial : ℚ) := by
  simp [coordinate]

@[simp] theorem coeff_coordinate_one : coeff 1 coordinate = 1 := by
  norm_num [coeff_coordinate, Nat.factorial]

private noncomputable def squareSubst : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ :=
  expand 2 (by decide)

private theorem coeff_squareSubst (f : PowerSeries ℚ) (n : ℕ) :
    coeff n (squareSubst f) =
      if 2 ∣ n then coeff (n / 2) f else 0 := by
  exact coeff_expand 2 (by decide) f

private theorem squareSubst_injective : Function.Injective squareSubst := by
  intro f g h
  ext n
  have h' := congrArg (fun s : PowerSeries ℚ => coeff (2*n) s) h
  simpa [squareSubst] using h'

private theorem rescale_squareSubst (f : PowerSeries ℚ) (a : ℚ) :
    squareSubst (rescale (a^2) f) = rescale a (squareSubst f) := by
  ext n
  by_cases h : 2 ∣ n
  · have he : 2 * (n / 2) = n := by omega
    have hp : a^n = (a^2)^(n/2) := by
      rw [← pow_mul, he]
    simp [coeff_squareSubst, h, hp]
  · simp [coeff_squareSubst, h]

private noncomputable def E (a : ℚ) : PowerSeries ℚ :=
  rescale a (PowerSeries.exp ℚ)

private theorem coeff_E (a : ℚ) (n : ℕ) :
    coeff n (E a) = a^n * (1 / (n.factorial : ℚ)) := by
  simp [E]

private theorem squareSubst_coordinate :
    squareSubst coordinate = E 1 + E (-1) - 2 := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [coeff_squareSubst, map_add, map_sub, coeff_E, coeff_one,
      show (2 : PowerSeries ℚ) = 1+1 by ring]
    norm_num
  · have htwo : coeff n (2 : PowerSeries ℚ) = 0 := by
      rw [show (2 : PowerSeries ℚ) = 1+1 by ring, map_add, coeff_one, ite_eq_right hn, add_zero]
    simp only [coeff_squareSubst, map_add, map_sub, coeff_E, htwo, sub_zero, one_pow,
      one_mul]
    by_cases h : 2 ∣ n
    · have he : 2 * (n / 2) = n := by omega
      have hn2 : n / 2 ≠ 0 := by omega
      have hp : (-1 : ℚ)^n = 1 := by
        rw [← he, pow_mul]
        norm_num
      simp only [h, ite_true, coeff_coordinate, ite_eq_right hn2, he, hp, one_mul]
      ring
    · have he : 2 * (n / 2) + 1 = n := by omega
      have hp : (-1 : ℚ)^n = -1 := by
        conv_lhs => rw [← he, pow_add, pow_mul]
        norm_num
      simp only [h, ite_false, hp]
      ring

private theorem E_mul (a b : ℚ) : E a * E b = E (a+b) :=
  exp_mul_exp_eq_exp_add a b

private theorem E_zero : E 0 = 1 := by
  simp [E]

private theorem exp_pair_rec (a : ℚ) :
    (E 1 + E (-1)) * (E (a+1) + E (-(a+1))) - (E a + E (-a)) =
      E (a+2) + E (-(a+2)) := by
  simp only [add_mul, mul_add, E_mul]
  rw [show 1+(a+1) = a+2 by ring, show 1+(-(a+1)) = -a by ring,
    show -1+(a+1) = a by ring, show -1+(-(a+1)) = -(a+2) by ring]
  ring

private theorem cheb_exp_pair (k : ℕ) :
    (Polynomial.aeval (E 1 + E (-1))) (Polynomial.Chebyshev.C ℚ (k:ℤ)) =
      E (k:ℚ) + E (-(k:ℚ)) := by
  induction k using Nat.twoStepInduction with
  | zero =>
    simp only [Nat.cast_zero, Polynomial.Chebyshev.C_zero, neg_zero, E_zero, map_ofNat]
    ring
  | one => simp
  | more k ih0 ih1 =>
    push_cast at ih1 ⊢
    rw [Polynomial.Chebyshev.C_add_two, map_sub, map_mul, Polynomial.aeval_X]
    rw [ih1, ih0]
    exact exp_pair_rec _

/-- The same coordinate linearizes every integral Chebyshev multiplier. -/
theorem chebyshev_formal_conjugacy (k : ℕ) :
    (Polynomial.aeval (coordinate+2)) (Polynomial.Chebyshev.C ℚ (k:ℤ)) - 2 =
      rescale ((k:ℚ)^2) coordinate := by
  apply squareSubst_injective
  rw [rescale_squareSubst, map_sub, map_ofNat, ← Polynomial.aeval_algHom_apply]
  have hf : squareSubst (coordinate+2) = E 1+E (-1) := by
    rw [map_add, map_ofNat, squareSubst_coordinate]; ring
  rw [hf, cheb_exp_pair, squareSubst_coordinate]
  have h (x : ℚ) : rescale (k:ℚ) (E x) = E (x*k) := by
    unfold E
    rw [rescale_rescale]
  rw [map_sub, map_add, h, h, map_ofNat, one_mul, neg_one_mul]

/-- The cubic polynomial update is formally conjugate to multiplication by nine.
The proof goes through formal coefficient substitution only; it requires no
choice of a square root in an evaluation field. -/
theorem formal_conjugacy :
    coordinate^3 + 6*coordinate^2 + 9*coordinate = rescale (9 : ℚ) coordinate := by
  have hC : Polynomial.Chebyshev.C ℚ 3 = Polynomial.X^3 - 3*Polynomial.X := by
    rw [show (3:ℤ)=1+2 by decide, Polynomial.Chebyshev.C_add_two,
      show (1:ℤ)+1=2 by decide, Polynomial.Chebyshev.C_two,
      Polynomial.Chebyshev.C_one]
    ring
  have h := chebyshev_formal_conjugacy 3
  norm_num [hC, map_sub, map_mul, map_pow, Polynomial.aeval_X, map_ofNat] at h
  calc
    _ = (coordinate+2)^3 - 3*(coordinate+2) - 2 := by ring
    _ = _ := h


end D5.S3.Arith.Primes.GoldenCubicFormalConjugacy
