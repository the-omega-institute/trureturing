/- GID: D5/S0/Tower/Tribonacci/Binet
   generality: I
   mirror-B: D5/B/S0/Tower/Tribonacci/Binet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact Tribonacci Binet data has contracting secondary roots. -/

import D5.S0.Tower.Tribonacci.PerronRoot

namespace D5.S0.Tower.Tribonacci.Binet

open D5.S0.Tower.Tribonacci.Names
open D5.S0.Tower.Tribonacci.Values
open D5.S0.Tower.Tribonacci.PerronRoot
open Filter

local notation "t" => tribonacciConstant

/-- The complex characteristic polynomial of the Tribonacci recurrence. -/
noncomputable def tribonacciCharacteristicPolynomial : Polynomial Complex :=
  Polynomial.X ^ 3 - Polynomial.X ^ 2 - Polynomial.X - 1

/-- The exact coefficient of the Perron term in the Tribonacci Binet expansion. -/
noncomputable def tribonacciBinetCoefficient : Real :=
  t ^ 2 / (t ^ 2 + 2 * t + 3)

/-- Applying the residual quadratic factor isolates the Perron component exactly. -/
theorem tribonacci_perron_projection (n : Nat) :
    (tribonacci (n + 2) : Real) +
        (t - 1) * tribonacci (n + 1) + t⁻¹ * tribonacci n =
      t ^ (n + 1) := by
  induction n with
  | zero => norm_num [tribonacci]
  | succ n ih =>
      rw [show n + 1 + 2 = n + 3 by omega,
        show n + 1 + 1 = n + 2 by omega,
        show n + 1 + 1 = n + 2 by omega]
      have hrec : (tribonacci (n + 3) : Real) =
          tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n := by
        exact_mod_cast tribonacci_add_three n
      calc
        (tribonacci (n + 3) : Real) +
              (t - 1) * tribonacci (n + 2) + t⁻¹ * tribonacci (n + 1) =
            t * ((tribonacci (n + 2) : Real) +
              (t - 1) * tribonacci (n + 1) + t⁻¹ * tribonacci n) := by
          rw [hrec]
          field_simp [tribonacciConstant_ne_zero]
          nlinarith [tribonacciConstant_cubic]
        _ = t * t ^ (n + 1) := by rw [ih]
        _ = t ^ (n + 1 + 1) := by rw [pow_succ]; ring

/-- The Binet remainder is an exact linear combination of two consecutive residual errors. -/
theorem tribonacci_binet_error_eq (n : Nat) :
    (tribonacci n : Real) - tribonacciBinetCoefficient * t ^ n =
      -(t / (t ^ 2 + 2 * t + 3)) *
        ((2 * t - 1) * tribonacciError n + tribonacciError (n + 1)) := by
  have hden : 0 < t ^ 2 + 2 * t + 3 := by
    nlinarith [sq_nonneg t, tribonacciConstant_pos]
  have hden_identity :
      t ^ 2 + 2 * t + 3 = t ^ 2 * (2 * t - 1) + 1 := by
    nlinarith [tribonacciConstant_cubic]
  have hprojection := tribonacci_perron_projection n
  field_simp [tribonacciConstant_ne_zero] at hprojection
  rw [pow_succ] at hprojection
  let d : Real := t ^ 2 + 2 * t + 3
  have hd : d ≠ 0 := by exact hden.ne'
  rw [tribonacciBinetCoefficient, tribonacciError, tribonacciError]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  change (tribonacci n : Real) - (t ^ 2 / d) * t ^ n =
    -(t / d) * ((2 * t - 1) *
      ((tribonacci (n + 1) : Real) - t * tribonacci n) +
      ((tribonacci (n + 2) : Real) - t * tribonacci (n + 1)))
  rw [show (tribonacci n : Real) - (t ^ 2 / d) * t ^ n =
      (d * tribonacci n - t ^ 2 * t ^ n) / d by field_simp [hd],
    show -(t / d) * ((2 * t - 1) *
        ((tribonacci (n + 1) : Real) - t * tribonacci n) +
        ((tribonacci (n + 2) : Real) - t * tribonacci (n + 1))) =
      (-t * ((2 * t - 1) *
        ((tribonacci (n + 1) : Real) - t * tribonacci n) +
        ((tribonacci (n + 2) : Real) - t * tribonacci (n + 1)))) / d by
      field_simp [hd]]
  rw [div_left_inj' hd]
  dsimp [d]
  linear_combination hprojection + (tribonacci n : Real) * hden_identity

/-- After removing the exact Perron term, the Tribonacci sequence converges to zero. -/
theorem tribonacci_binet_tendsto_zero :
    Tendsto
      (fun n : Nat =>
        (tribonacci n : Real) - tribonacciBinetCoefficient * t ^ n)
      atTop (nhds 0) := by
  have herror := tribonacci_error_tendsto_zero
  have herror_succ :
      Tendsto (fun n : Nat => tribonacciError (n + 1)) atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat
      (f := tribonacciError) (l := nhds 0) 1).2 herror
  have hcombined : Tendsto
      (fun n : Nat => (2 * t - 1) * tribonacciError n + tribonacciError (n + 1))
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul herror).add herror_succ
  rw [show (fun n : Nat =>
      (tribonacci n : Real) - tribonacciBinetCoefficient * t ^ n) =
        fun n : Nat => -(t / (t ^ 2 + 2 * t + 3)) *
          ((2 * t - 1) * tribonacciError n + tribonacciError (n + 1)) by
    funext n
    exact tribonacci_binet_error_eq n]
  have hscaled : Tendsto
      (fun n : Nat => -(t / (t ^ 2 + 2 * t + 3)) *
        ((2 * t - 1) * tribonacciError n + tribonacciError (n + 1)))
      atTop (nhds (-(t / (t ^ 2 + 2 * t + 3)) * 0)) :=
    tendsto_const_nhds.mul hcombined
  simpa using hscaled

/-- Every complex Tribonacci root other than the Perron root lies in the open unit disk. -/
theorem abs_lt_one_of_tribonacci_root_ne_perron {z : Complex}
    (hz : z ^ 3 = z ^ 2 + z + 1) (hz_ne : z ≠ (t : Complex)) :
    ‖z‖ < 1 := by
  have ht_cubic : (t : Complex) ^ 3 = (t : Complex) ^ 2 + (t : Complex) + 1 := by
    exact_mod_cast tribonacciConstant_cubic
  have hfactor :
      (z - (t : Complex)) *
        (z ^ 2 + z * t + t ^ 2 - z - t - 1) = 0 := by
    calc
      (z - (t : Complex)) *
          (z ^ 2 + z * t + t ^ 2 - z - t - 1) =
        (z ^ 3 - z ^ 2 - z - 1) -
          ((t : Complex) ^ 3 - t ^ 2 - t - 1) := by ring
      _ = 0 := by rw [hz, ht_cubic]; ring
  have hresidual : z ^ 2 + z * t + t ^ 2 - z - t - 1 = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hz_ne)
  have ht_inverse : t ^ 2 - t - 1 = t⁻¹ := by
    field_simp [tribonacciConstant_ne_zero]
    nlinarith [tribonacciConstant_cubic]
  have ht_inverse_complex :
      (((t ^ 2 - t - 1 : Real) : Complex)) = ((t⁻¹ : Real) : Complex) :=
    congrArg (fun x : Real => (x : Complex)) ht_inverse
  have hquad :
      z ^ 2 + ((t - 1 : Real) : Complex) * z + ((t⁻¹ : Real) : Complex) = 0 := by
    calc
      z ^ 2 + ((t - 1 : Real) : Complex) * z + ((t⁻¹ : Real) : Complex) =
          z ^ 2 + ((t - 1 : Real) : Complex) * z +
            ((t ^ 2 - t - 1 : Real) : Complex) := by rw [ht_inverse_complex]
      _ = z ^ 2 + z * t + t ^ 2 - z - t - 1 := by push_cast; ring
      _ = 0 := hresidual
  have him := congrArg Complex.im hquad
  have hre := congrArg Complex.re hquad
  norm_num [pow_two, Complex.mul_re, Complex.mul_im] at him hre
  have him_factor : z.im * (2 * z.re + (t - 1)) = 0 := by
    nlinarith [him]
  have him_ne : z.im ≠ 0 := by
    intro him_zero
    rw [him_zero] at hre
    have hdisc := tribonacci_errorEnergy_discriminant_pos
    nlinarith [sq_nonneg (2 * z.re + (t - 1))]
  have hre_value : 2 * z.re + (t - 1) = 0 :=
    (mul_eq_zero.mp him_factor).resolve_left him_ne
  have hre_mul : 2 * z.re ^ 2 + (t - 1) * z.re = 0 := by
    calc
      2 * z.re ^ 2 + (t - 1) * z.re =
          z.re * (2 * z.re + (t - 1)) := by ring
      _ = 0 := by rw [hre_value, mul_zero]
  have hnormSq : Complex.normSq z = t⁻¹ := by
    rw [Complex.normSq_apply]
    nlinarith [hre, hre_mul]
  apply (sq_lt_one_iff₀ (norm_nonneg z)).mp
  rw [Complex.sq_norm, hnormSq]
  exact inv_lt_one_of_one_lt₀ one_lt_tribonacciConstant

/-- The non-Perron members of the characteristic root multiset are inside the unit disk. -/
theorem tribonacci_secondary_root_abs_lt_one {z : Complex}
    (hz : z ∈ tribonacciCharacteristicPolynomial.roots)
    (hz_ne : z ≠ (t : Complex)) : ‖z‖ < 1 := by
  have hpoly_ne : tribonacciCharacteristicPolynomial ≠ 0 := by
    intro hzero
    have heval := congrArg (Polynomial.eval (2 : Complex)) hzero
    norm_num [tribonacciCharacteristicPolynomial] at heval
  have hisRoot := (Polynomial.mem_roots hpoly_ne).mp hz
  apply abs_lt_one_of_tribonacci_root_ne_perron (hz_ne := hz_ne)
  rw [Polynomial.IsRoot] at hisRoot
  have heval : z ^ 3 - z ^ 2 - z - 1 = 0 := by
    simpa [tribonacciCharacteristicPolynomial] using hisRoot
  calc
    z ^ 3 = (z ^ 3 - z ^ 2 - z - 1) + (z ^ 2 + z + 1) := by ring
    _ = z ^ 2 + z + 1 := by rw [heval, zero_add]

end D5.S0.Tower.Tribonacci.Binet
