/- GID: D5/S3/QuantumContext/HesseSicCertificate
   generality: I
   mirror-B: D5/B/S3/QuantumContext/HesseSicCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Certify the nine-vector dimension-three Hesse SIC configuration. -/

/- Library-search audit trail (2026-09-05):
   * Exact searches of current `origin/dev` found no `omega`, `hesseVector`, `hesseKet`,
     `hesse_sic_certificate`, Fin-nine overlap theorem, or dimension-three projector sum.
   * Generic `Matrix.vecMulVec` and complex-inner-product uses exist in D5, but none supplies
     the Hesse coordinates, their off-diagonal overlap table, or their resolution of identity.
   * Pinned Mathlib has no Hesse, SIC, SIC-POVM, or equiangular certificate. Its complex
     exponential, Euclidean inner-product, finite matrix, and norm identities are reused below.
-/

import Mathlib

open scoped BigOperators ComplexConjugate

namespace D5.S3.QuantumContext.HesseSicCertificate

noncomputable section

/-- The standard primitive cube root `exp (2 pi i / 3)`. -/
def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

/-- The real normalization `1 / sqrt 2`, written as `sqrt 2 / 2`. -/
private def invSqrtTwo : ℂ := (Real.sqrt 2 / 2 : ℝ)

private lemma omega_cubed : omega ^ 3 = 1 := by
  rw [omega]
  calc
    Complex.exp (2 * Real.pi * Complex.I / 3) ^ 3 =
        Complex.exp ((3 : ℂ) * (2 * Real.pi * Complex.I / 3)) :=
      (Complex.exp_nat_mul _ 3).symm
    _ = Complex.exp (2 * Real.pi * Complex.I) := by
      congr 1
      ring
    _ = 1 := Complex.exp_two_pi_mul_I

private lemma omega_ne_one : omega ≠ 1 := by
  intro h
  have hdvd : (3 : ℕ) ∣ 1 :=
    (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (k := 1) (N := 3) (by norm_num)).mp (by
      simpa [omega] using h)
  norm_num at hdvd

private lemma omega_ne_zero : omega ≠ 0 := Complex.exp_ne_zero _

private lemma omega_sum : 1 + omega + omega ^ 2 = 0 := by
  have hfac : (omega - 1) * (omega ^ 2 + omega + 1) = 0 := by
    rw [show (omega - 1) * (omega ^ 2 + omega + 1) = omega ^ 3 - 1 by ring,
      omega_cubed]
    ring
  rcases mul_eq_zero.mp hfac with h | h
  · exact (omega_ne_one (sub_eq_zero.mp h)).elim
  · linear_combination h

private lemma omega_norm : ‖omega‖ = 1 := by
  rw [omega, show 2 * (Real.pi : ℂ) * Complex.I / 3 =
      ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

private lemma omega_normSq : Complex.normSq omega = 1 := by
  rw [Complex.normSq_eq_norm_sq, omega_norm]
  norm_num

@[simp] private lemma star_omega : star omega = omega ^ 2 := by
  apply mul_left_cancel₀ omega_ne_zero
  calc
    omega * star omega = (Complex.normSq omega : ℂ) := by
      simpa using (Complex.mul_conj omega)
    _ = 1 := by rw [omega_normSq]; norm_num
    _ = omega ^ 3 := omega_cubed.symm
    _ = omega * omega ^ 2 := by ring

private lemma invSqrtTwo_sq : invSqrtTwo ^ 2 = (1 / 2 : ℂ) := by
  apply Complex.ext
  · norm_num [invSqrtTwo, pow_two]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  · norm_num [invSqrtTwo, pow_two]

@[simp] private lemma invSqrtTwo_mul_self :
    invSqrtTwo * invSqrtTwo = (1 / 2 : ℂ) := by
  simpa [pow_two] using invSqrtTwo_sq

private lemma invSqrtTwo_norm : ‖invSqrtTwo‖ = Real.sqrt 2 / 2 := by
  simp [invSqrtTwo]

private lemma invSqrtTwo_norm_sq : ‖invSqrtTwo‖ ^ 2 = (1 / 2 : ℝ) := by
  rw [invSqrtTwo_norm, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

@[simp] private lemma star_invSqrtTwo : star invSqrtTwo = invSqrtTwo := by
  simp [invSqrtTwo]

@[simp] private lemma starRingEnd_omega : (starRingEnd ℂ) omega = omega ^ 2 := by
  exact star_omega

@[simp] private lemma starRingEnd_invSqrtTwo :
    (starRingEnd ℂ) invSqrtTwo = invSqrtTwo := by
  exact star_invSqrtTwo

private lemma omega_sq_reduce : omega ^ 2 = -omega - 1 := by
  linear_combination omega_sum

private lemma omega_pow_four : omega ^ 4 = omega := by
  calc
    omega ^ 4 = omega ^ 3 * omega := by ring
    _ = omega := by rw [omega_cubed]; ring

private lemma omega_pow_five : omega ^ 5 = omega ^ 2 := by
  calc
    omega ^ 5 = omega ^ 3 * omega ^ 2 := by ring
    _ = omega ^ 2 := by rw [omega_cubed]; ring

private lemma omega_pow_six : omega ^ 6 = 1 := by
  calc
    omega ^ 6 = (omega ^ 3) ^ 2 := by ring
    _ = 1 := by rw [omega_cubed]; ring

private lemma omega_pow_seven : omega ^ 7 = omega := by
  calc
    omega ^ 7 = (omega ^ 3) ^ 2 * omega := by ring
    _ = omega := by rw [omega_cubed]; ring

private lemma omega_pow_eight : omega ^ 8 = omega ^ 2 := by
  calc
    omega ^ 8 = (omega ^ 3) ^ 2 * omega ^ 2 := by ring
    _ = omega ^ 2 := by rw [omega_cubed]; ring

private lemma omega_pow_ten : omega ^ 10 = omega := by
  calc
    omega ^ 10 = (omega ^ 3) ^ 3 * omega := by ring
    _ = omega := by rw [omega_cubed]; ring

private lemma omega_pow_twelve : omega ^ 12 = 1 := by
  calc
    omega ^ 12 = (omega ^ 3) ^ 4 := by ring
    _ = 1 := by rw [omega_cubed]; ring

private lemma omega_pow_fifteen : omega ^ 15 = 1 := by
  calc
    omega ^ 15 = (omega ^ 3) ^ 5 := by ring
    _ = 1 := by rw [omega_cubed]; ring

private lemma invSqrtTwo_pow_four : invSqrtTwo ^ 4 = (1 / 4 : ℂ) := by
  calc
    invSqrtTwo ^ 4 = (invSqrtTwo ^ 2) ^ 2 := by ring
    _ = (1 / 4 : ℂ) := by rw [invSqrtTwo_sq]; norm_num

private lemma sq_norm_eq_iff_mul_star (z : ℂ) (x : ℝ) :
    ‖z‖ ^ 2 = x ↔ z * star z = (x : ℂ) := by
  rw [← Complex.normSq_eq_norm_sq,
    show z * star z = (Complex.normSq z : ℂ) by simpa using Complex.mul_conj z]
  norm_cast

/-- The nine raw Hesse vectors, in three support blocks and three cube-root phases. -/
def hesseVector : Fin 9 → (Fin 3 → ℂ) := ![
  ![0, invSqrtTwo, -invSqrtTwo],
  ![0, invSqrtTwo, -(invSqrtTwo * omega)],
  ![0, invSqrtTwo, -(invSqrtTwo * omega ^ 2)],
  ![-invSqrtTwo, 0, invSqrtTwo],
  ![-(invSqrtTwo * omega), 0, invSqrtTwo],
  ![-(invSqrtTwo * omega ^ 2), 0, invSqrtTwo],
  ![invSqrtTwo, -invSqrtTwo, 0],
  ![invSqrtTwo, -(invSqrtTwo * omega), 0],
  ![invSqrtTwo, -(invSqrtTwo * omega ^ 2), 0]
]

/-- The same coordinates with the Euclidean (`L²`) norm and inner product. -/
def hesseKet (r : Fin 9) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 (hesseVector r)

set_option maxHeartbeats 1000000 in
/-- The dimension-three Hesse SIC certificate: unit vectors, constant off-diagonal
overlap squared `1/4`, and rank-one projectors summing to `3 I₃`. -/
theorem hesse_sic_certificate :
    (∀ r : Fin 9, ‖hesseKet r‖ ^ 2 = 1) ∧
    (∀ r s : Fin 9, r ≠ s → ‖inner ℂ (hesseKet r) (hesseKet s)‖ ^ 2 = (1 / 4 : ℝ)) ∧
    (∑ r : Fin 9, Matrix.vecMulVec (hesseVector r) (star (hesseVector r))) =
      (3 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  constructor
  · intro r
    rw [EuclideanSpace.norm_sq_eq]
    fin_cases r <;>
      simp [hesseKet, hesseVector, Fin.sum_univ_succ, invSqrtTwo_norm_sq,
        omega_norm] <;> norm_num
  constructor
  · intro r s hrs
    rw [sq_norm_eq_iff_mul_star]
    simp only [hesseKet, PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply]
    fin_cases r <;> fin_cases s <;>
      simp_all [hesseVector, Fin.sum_univ_succ] <;>
      ring_nf <;>
      simp [invSqrtTwo_sq, invSqrtTwo_pow_four,
        omega_cubed, omega_pow_four, omega_pow_five, omega_pow_six,
        omega_pow_eight, omega_pow_ten, omega_pow_twelve,
        omega_pow_fifteen, omega_sq_reduce] <;>
      ring
  · ext i j
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply]
    fin_cases i <;> fin_cases j <;>
      simp [hesseVector, Fin.sum_univ_succ] <;>
      ring_nf <;>
      simp [invSqrtTwo_sq,
        omega_cubed, omega_pow_four, omega_pow_six, omega_sq_reduce] <;>
      ring

example : PUnit := PUnit.unit
example : Fin 9 := 0
example : Fin 3 → ℂ := fun _ => 0

#print axioms hesse_sic_certificate

end

end D5.S3.QuantumContext.HesseSicCertificate
