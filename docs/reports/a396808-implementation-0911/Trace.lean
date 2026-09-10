import Mathlib.Tactic.ReduceModChar
import D5.S3.Arith.ArtinSchreierTracePowersOfTwo
set_option autoImplicit false
open scoped PowerSeries
open Polynomial
namespace A396808Trace
noncomputable section
abbrev F3 := ZMod 3
abbrev PS := F3⟦X⟧

private instance : CharP PS 3 :=
  charP_of_injective_ringHom PowerSeries.C_injective 3

def tracePoly : ℕ → F3[X]
  | 0 => 0
  | 1 => 1
  | 2 => 1 + 2 * Polynomial.X
  | m + 3 => tracePoly (m + 2) + Polynomial.X * tracePoly (m + 1) +
      Polynomial.X ^ 2 * tracePoly m

private theorem trace_degree (m : ℕ) : (tracePoly m).natDegree ≤ 2 * m / 3 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases m with _ | _ | _ | m
    · simp [tracePoly]
    · simp [tracePoly]
    · norm_num [tracePoly]
      apply Polynomial.natDegree_add_le_of_degree_le
      · simp
      · exact (Polynomial.natDegree_mul_le).trans (by norm_num)
    · change (tracePoly (m+3)).natDegree ≤ _
      rw [tracePoly]
      apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · apply (Polynomial.natDegree_add_le _ _).trans
        apply max_le
        · have h := ih (m+2) (by omega)
          omega
        · apply Polynomial.natDegree_mul_le.trans
          have h := ih (m+1) (by omega)
          simp only [Polynomial.natDegree_X]
          omega
      · apply Polynomial.natDegree_mul_le.trans
        have h := ih m (by omega)
        simp only [Polynomial.natDegree_X_pow]
        omega

private theorem cube_identity (t : PS) :
    (1+t^2+t^4)^3 = (1+t^2+t^4)^2 + (t-t^3)^2*(1+t^2+t^4) + (t-t^3)^4 := by
  have : CharP PS 3 := inferInstance
  ring_nf
  reduce_mod_char!
  ring_nf
  reduce_mod_char!

private theorem cube_plus (t : PS) :
    ((t^2+t)^2)^3 = ((t^2+t)^2)^2 + (t-t^3)^2*((t^2+t)^2) + (t-t^3)^4 := by
  have : CharP PS 3 := inferInstance
  ring_nf
  reduce_mod_char!


private theorem cube_minus (t : PS) :
    ((t^2-t)^2)^3 = ((t^2-t)^2)^2 + (t-t^3)^2*((t^2-t)^2) + (t-t^3)^4 := by
  have : CharP PS 3 := inferInstance
  ring_nf
  reduce_mod_char!


private theorem roots_sum (t : PS) :
    (1+t^2+t^4) + (t^2+t)^2 + (t^2-t)^2 = 1 := by
  have : CharP PS 3 := inferInstance
  ring_nf
  reduce_mod_char!


private theorem roots_squares (t : PS) :
    (1+t^2+t^4)^2 + ((t^2+t)^2)^2 + ((t^2-t)^2)^2 = 1 + 2*(t-t^3)^2 := by
  have : CharP PS 3 := inferInstance
  ring_nf
  reduce_mod_char!
  ring_nf

private theorem root_pow (z : PS)
    (hz : z^3 = z^2 + PowerSeries.X^2*z + PowerSeries.X^4) (m : ℕ) :
    z^(m+3) = z^(m+2) + PowerSeries.X^2*z^(m+1) + PowerSeries.X^4*z^m := by
  calc
    z^(m+3) = z^m*z^3 := pow_add _ _ _
    _ = _ := by rw [hz]; ring

private theorem trace_identity (t : PS) (ht : t^3 = t - PowerSeries.X) (m : ℕ) :
    PowerSeries.expand 2 (by decide) (tracePoly m : PS) =
      (1+t^2+t^4)^m + ((t^2+t)^2)^m + ((t^2-t)^2)^m := by
  have hx : t-t^3 = PowerSeries.X := by linear_combination -ht
  have h0 := cube_identity t
  have h1 := cube_plus t
  have h2 := cube_minus t
  rw [hx] at h0 h1 h2
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases m with _ | _ | _ | m
    · simp only [tracePoly, Polynomial.coe_zero, map_zero, pow_zero]
      have : CharP PS 3 := inferInstance
      ring_nf
      reduce_mod_char!
    · simpa [tracePoly] using (roots_sum t).symm
    · have hs := roots_squares t
      rw [hx] at hs
      have hc : ((2 : F3[X]) : PS) = 2 := by
        change (Polynomial.coeToPowerSeries.ringHom (2 : F3[X])) = 2
        exact map_ofNat _ _
      simpa [tracePoly, hc, map_ofNat] using hs.symm
    · rw [tracePoly, Polynomial.coe_add, Polynomial.coe_add, Polynomial.coe_mul,
        Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, map_add, map_add,
        map_mul, map_mul, map_pow, PowerSeries.expand_X,
        ih (m+2) (by omega), ih (m+1) (by omega), ih m (by omega),
        root_pow _ h0, root_pow _ h1, root_pow _ h2]
      ring

private theorem coeff_root_pow_eq_zero (t : PS)
    (ht : t^3 = t - PowerSeries.X) (ht0 : PowerSeries.constantCoeff t = 0)
    (m n : ℕ) (hdegree : 2*m/3 < n) (hexponent : n < m) :
    PowerSeries.coeff (2*n) ((1+t^2+t^4)^m) = 0 := by
  have hp : (tracePoly m).coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (trace_degree m) hdegree)
  have hv : PowerSeries.coeff (2*n) (((t^2+t)^2)^m) = 0 := by
    rw [← pow_mul]
    apply PowerSeries.coeff_of_lt_order
    apply lt_of_lt_of_le _ (PowerSeries.le_order_pow_of_constantCoeff_eq_zero (2*m)
      (by simp [ht0] : PowerSeries.constantCoeff (t^2+t) = 0))
    exact_mod_cast (by omega : 2*n < 2*m)
  have hw : PowerSeries.coeff (2*n) (((t^2-t)^2)^m) = 0 := by
    rw [← pow_mul]
    apply PowerSeries.coeff_of_lt_order
    apply lt_of_lt_of_le _ (PowerSeries.le_order_pow_of_constantCoeff_eq_zero (2*m)
      (by simp [ht0] : PowerSeries.constantCoeff (t^2-t) = 0))
    exact_mod_cast (by omega : 2*n < 2*m)
  have h := congrArg (PowerSeries.coeff (2*n)) (trace_identity t ht m)
  simp only [PowerSeries.coeff_expand_mul, Polynomial.coeff_coe, map_add, hp, hv, hw,
    add_zero] at h
  exact h.symm

#print axioms coeff_root_pow_eq_zero
end
end A396808Trace
