# Checked normalization experiment

This is a Lean experiment, not a deposited theorem or the A397902 conclusion.
`lake env lean /tmp/A397902Normalization.lean` on the preheated tree: EXIT=0.
The two printed axiom closures contain only propext, Classical.choice, Quot.sound.
Source SHA-256: `5326966d90fe4e8804005d340251933de11bf0f46518932a32cd7baebefa649e`.

```lean
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
open PowerSeries
noncomputable section
namespace A397902Attempt
variable {R : Type*} [CommRing R]
def geom (e : ℕ) : PowerSeries R := mk fun n => (e : R)^n
lemma geom_eq (e : ℕ) : (1 - C (e : R) * X) * geom (R := R) e = 1 := by
  ext n
  cases n with
  | zero => simp [geom]
  | succ n =>
    rw [sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul, coeff_succ_X_mul]
    simp [geom, pow_succ, mul_comm]
lemma geom_derivative (e : ℕ) : derivative R (geom e) = C (e : R) * (geom e)^2 := by
  have h := congrArg (fun f => derivative R f) (geom_eq (R := R) e)
  simp only [Derivation.map_sub, Derivation.leibniz, derivative_one, derivative_C,
    derivative_X, smul_eq_mul, mul_zero, mul_one, zero_sub] at h
  have h' := congrArg (fun f => f * geom (R := R) e) h
  have hg := geom_eq (R := R) e
  linear_combination h' - derivative R (geom e) * hg
lemma coeff_power_divisible (F : PowerSeries ℤ) (n e : ℕ) (hn : 0 < n)
    (hcop : Nat.Coprime e n) : (e : ℤ) ∣ coeff n (F^e) := by
  have h := congrArg (coeff (n-1)) (derivative_pow F e)
  rw [coeff_derivative, Nat.sub_add_cancel hn] at h
  have he : (e : PowerSeries ℤ) = C (e : ℤ) := by simp
  rw [he, mul_assoc, coeff_C_mul] at h
  apply hcop.isCoprime.dvd_of_dvd_mul_left
  refine ⟨coeff (n-1) (F^(e-1) * derivative ℤ F), ?_⟩
  have hncast : ((n-1 : ℕ) : ℤ) + 1 = n := by exact_mod_cast Nat.sub_add_cancel hn
  simpa only [hncast, mul_comm] using h
lemma square_exponent_divisible (F : PowerSeries ℤ) (n : ℕ) (hn : 0 < n) :
    (((n+1)^2 : ℕ) : ℤ) ∣ coeff n (F^((n+1)^2)) := by
  exact coeff_power_divisible F n ((n+1)^2) hn ((Nat.coprime_self_add_left.mpr (Nat.coprime_one_left n)).pow_left 2)

def row (F : PowerSeries R) (n : ℕ) : R :=
  coeff n (F^((n+1)^2) * geom ((n+1)^2))
def derivRow (F : PowerSeries R) (n : ℕ) : R :=
  coeff (n-1) (F^((n+1)^2-1) * derivative R F * geom ((n+1)^2) +
    F^((n+1)^2) * geom ((n+1)^2)^2)
def normalized (F : PowerSeries R) (n : ℕ) : R := row F n - (n+2) * derivRow F n

lemma derivative_row (F : PowerSeries R) (n : ℕ) (hn : 0 < n) :
    (n : R) * row F n = ((n+1)^2 : ℕ) * derivRow F n := by
  have h := congrArg (coeff (n-1)) ((derivative R).leibniz
    (F^((n+1)^2)) (geom ((n+1)^2)))
  rw [coeff_derivative, Nat.sub_add_cancel hn, derivative_pow, geom_derivative] at h
  have hc : (((n+1)^2 : ℕ) : PowerSeries R) = C (((n+1)^2 : ℕ) : R) := by simp
  simp only [smul_eq_mul, hc] at h
  have hfact : F ^ ((n+1)^2) * (C (((n+1)^2 : ℕ) : R) * geom ((n+1)^2)^2) +
      geom ((n+1)^2) * (C (((n+1)^2 : ℕ) : R) * F^((n+1)^2-1) * derivative R F) =
      C (((n+1)^2 : ℕ) : R) *
        (F^((n+1)^2-1) * derivative R F * geom ((n+1)^2) +
        F^((n+1)^2) * geom ((n+1)^2)^2) := by ring
  rw [hfact, coeff_C_mul] at h
  have hncast : ((n-1 : ℕ) : R) + 1 = n := by
    exact (by simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun k : ℕ => (k : R)) (Nat.sub_add_cancel hn))
  simpa only [row, derivRow, hncast, mul_comm] using h

lemma exact_normalization (F : PowerSeries R) (n : ℕ) (hn : 0 < n) :
    row F n = (((n+1)^2 : ℕ) : R) * normalized F n := by
  have h := derivative_row F n hn
  simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] at h ⊢
  dsimp [normalized]
  linear_combination -(n+2 : R) * h

#print axioms coeff_power_divisible
#print axioms exact_normalization
end A397902Attempt
```
