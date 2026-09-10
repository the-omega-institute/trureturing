/- GID: D5/S1/Recurrence/Residue/IntegralEGFComposition
   generality: G
   mirror-B: D5/B/S1/Recurrence/Residue/IntegralEGFComposition
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Integer differential recurrence for composition of exponential generating series. -/

import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open PowerSeries Finset

namespace D5.S1.Recurrence.Residue.IntegralEGFComposition

/-- Factorial-normalized coefficient of a rational formal power series. -/
noncomputable def eCoeff (f : PowerSeries ℚ) (n : ℕ) : ℚ := n.factorial * coeff n f

@[simp] theorem eCoeff_zero (f : PowerSeries ℚ) : eCoeff f 0 = constantCoeff f := by
  simp [eCoeff, coeff_zero_eq_constantCoeff]

@[simp] theorem eCoeff_derivative (f : PowerSeries ℚ) (n : ℕ) :
    eCoeff (derivative ℚ f) n = eCoeff f (n + 1) := by
  simp [eCoeff, coeff_derivative, Nat.factorial_succ]
  ring

theorem eCoeff_mul (f g : PowerSeries ℚ) (n : ℕ) :
    eCoeff (f * g) n =
      ∑ i ∈ range (n + 1), (n.choose i : ℚ) * eCoeff f i * eCoeff g (n - i) := by
  rw [eCoeff, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i f * coeff j g) n, mul_sum]
  apply sum_congr rfl
  intro i hi
  have h : (n.choose i : ℚ) * i.factorial * (n - i).factorial = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial (mem_range_succ_iff.mp hi)
  dsimp [eCoeff]
  rw [← h]
  ring

@[simp] theorem eCoeff_X_mul (f : PowerSeries ℚ) (n : ℕ) :
    eCoeff (X * f) (n + 1) = (n + 1 : ℚ) * eCoeff f n := by
  simp [eCoeff, Nat.factorial_succ, mul_assoc]

@[simp] theorem eCoeff_exp (n : ℕ) : eCoeff (exp ℚ) n = 1 := by
  simp [eCoeff, coeff_exp, Nat.factorial_ne_zero]

@[simp] theorem eCoeff_X (n : ℕ) : eCoeff (X : PowerSeries ℚ) n = if n = 1 then 1 else 0 := by
  by_cases h : n = 1 <;> simp [eCoeff, coeff_X, h]

/-- The integral chain-rule recurrence; the inner sequence has implicit constant term zero. -/
def composition {R : Type*} [CommSemiring R] (f g : ℕ → R) : ℕ → R
  | 0 => f 0
  | n + 1 => ∑ i : Fin (n + 1), (n.choose i : R) *
      composition (fun j => f (j + 1)) g i * g (n - i + 1)
termination_by n => n

theorem eCoeff_composition (f g : PowerSeries ℚ) (hg : constantCoeff g = 0) (n : ℕ) :
    eCoeff (f.subst g) n = composition (eCoeff f) (eCoeff g) n := by
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    cases n with
    | zero =>
      simp only [eCoeff_zero, composition]
      rw [← coeff_zero_eq_constantCoeff, coeff_subst' (.of_constantCoeff_zero hg)]
      simp only [coeff_zero_eq_constantCoeff, map_pow, hg, zero_pow_eq,
        smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [finsum_eq_single _ 0] <;> simp_all [coeff_zero_eq_constantCoeff]
    | succ n =>
      rw [← eCoeff_derivative, derivative_subst (.of_constantCoeff_zero hg), eCoeff_mul]
      rw [composition, Fin.sum_univ_eq_sum_range (fun i => (n.choose i : ℚ) *
        composition (fun j => eCoeff f (j + 1)) (eCoeff g) i * eCoeff g (n - i + 1))]
      apply sum_congr rfl
      intro i hi
      rw [ih i (mem_range.mp hi), eCoeff_derivative]
      rw [show eCoeff (derivative ℚ f) = (fun j => eCoeff f (j + 1)) from
        funext (eCoeff_derivative f)]

theorem composition_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (f g : ℕ → R) (n : ℕ) :
    φ (composition f g n) = composition (fun j => φ (f j)) (fun j => φ (g j)) n := by
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    cases n with
    | zero => simp only [composition]
    | succ n =>
      simp only [composition, map_sum, map_mul, map_natCast]
      apply sum_congr rfl
      intro i _
      rw [ih i i.isLt]

theorem composition_congr {R : Type*} [CommSemiring R] {f f' g g' : ℕ → R}
    {n : ℕ} (hf : ∀ i ≤ n, f i = f' i) (hg : ∀ i ≤ n, g i = g' i) :
    composition f g n = composition f' g' n := by
  induction n using Nat.strong_induction_on generalizing f f' with
  | h n ih =>
    cases n with
    | zero => simpa only [composition] using hf 0 (by omega)
    | succ n =>
      simp only [composition]
      apply sum_congr rfl
      intro i _
      rw [ih i i.isLt (fun j hj => hf (j + 1) (by omega))
        (fun j hj => hg j (by omega)), hg (n - i + 1) (by omega)]

/-- Natural integral EGF coefficients, independent of any congruence assertion. -/
def Natural (f : PowerSeries ℚ) : Prop := ∀ n, ∃ a : ℕ, eCoeff f n = a

/-- Integral EGF coefficients, allowing subtraction and halving of even coefficients. -/
def Integral (f : PowerSeries ℚ) : Prop := ∀ n, ∃ a : ℤ, eCoeff f n = a

theorem natural_subst {f g : PowerSeries ℚ} (hf : Natural f) (hg : Natural g)
    (hz : constantCoeff g = 0) : Natural (f.subst g) := by
  classical
  choose a ha using hf
  choose b hb using hg
  intro n
  refine ⟨composition a b n, ?_⟩
  rw [eCoeff_composition f g hz]
  rw [funext ha, funext hb]
  exact (composition_map (Nat.castRingHom ℚ) a b n).symm

theorem integral_subst {f g : PowerSeries ℚ} (hf : Integral f) (hg : Integral g)
    (hz : constantCoeff g = 0) : Integral (f.subst g) := by
  classical
  choose a ha using hf
  choose b hb using hg
  intro n
  refine ⟨composition a b n, ?_⟩
  rw [eCoeff_composition f g hz]
  rw [funext ha, funext hb]
  exact (composition_map (Int.castRingHom ℚ) a b n).symm

end D5.S1.Recurrence.Residue.IntegralEGFComposition
