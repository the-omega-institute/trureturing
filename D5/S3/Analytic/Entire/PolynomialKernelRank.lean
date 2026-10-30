/- GID: D5/S3/Analytic/Entire/PolynomialKernelRank
   generality: G
   mirror-B: D5/B/S3/Analytic/Entire/PolynomialKernelRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Algebraic coefficient probes of separated entire kernels and the full complex quadratic discriminant obstruction. -/

import D5.S3.Analytic.Entire.WeightedHankelLowerRank
import D5.S3.Analytic.Entire.ExponentialBlockIndependence
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.LinearAlgebra.Matrix.Block

/-! Coefficient extraction is extended algebraically to all functions. It
does not assume that arbitrary separated factors are polynomials or Fock vectors. -/

noncomputable section
open scoped BigOperators

namespace D5.S3.Analytic.Entire

private def polynomialEvaluation : Polynomial ℂ →ₗ[ℂ] (ℂ → ℂ) where
  toFun p := fun z => p.eval z
  map_add' p q := by ext z; exact Polynomial.eval_add
  map_smul' c p := by ext z; exact Polynomial.eval_smul c p z

private theorem polynomial_evaluation_injective : Function.Injective polynomialEvaluation := by
  intro p q h
  exact Polynomial.funext (congrFun h)

private def polynomialCoefficient (n : ℕ) : (ℂ → ℂ) →ₗ[ℂ] ℂ :=
  (Polynomial.lcoeff ℂ n).comp polynomialEvaluation.leftInverse

private theorem polynomial_coefficient_eval (n : ℕ) (p : Polynomial ℂ) :
    polynomialCoefficient n (fun z => p.eval z) = p.coeff n := by
  change (polynomialEvaluation.leftInverse (polynomialEvaluation p)).coeff n = p.coeff n
  rw [LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr polynomial_evaluation_injective)]

private def kernelProbe {ι κ : Type*}
    (l : ι → (ℂ → ℂ) →ₗ[ℂ] ℂ) (r : κ → (ℂ → ℂ) →ₗ[ℂ] ℂ)
    (F : ℂ → ℂ → ℂ) : Matrix ι κ ℂ :=
  fun i j => r j (fun w => l i (fun z => F z w))

/-- Any finite family of algebraic linear probes preserves a separation
rank bound. No continuity of the probes is required. -/
private theorem kernel_probe_rank_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    {k : ℕ} {F : ℂ → ℂ → ℂ}
    (hF : SeparatedLE k F)
    (l : ι → (ℂ → ℂ) →ₗ[ℂ] ℂ) (r : κ → (ℂ → ℂ) →ₗ[ℂ] ℂ) :
    (kernelProbe l r F).rank ≤ k := by
  classical
  obtain ⟨g, h, _, _, hsep⟩ := hF
  let A : Matrix ι (Fin k) ℂ := fun i a => l i (g a)
  let B : Matrix (Fin k) κ ℂ := fun a j => r j (h a)
  have hleft (i : ι) (w : ℂ) :
      l i (fun z => F z w) = ∑ a, h a w * l i (g a) := by
    have heq : (fun z => F z w) = ∑ a, h a w • g a := by
      ext z
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simpa only [mul_comm] using hsep z w
    rw [heq, map_sum]
    simp only [map_smul, smul_eq_mul]
  have hfactor : kernelProbe l r F = A * B := by
    ext i j
    have heq : (fun w => l i (fun z => F z w)) = ∑ a, l i (g a) • h a := by
      ext w
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hleft]
      apply Finset.sum_congr rfl
      intro a _
      exact mul_comm _ _
    change r j (fun w => l i (fun z => F z w)) = ∑ a, A i a * B a j
    rw [heq, map_sum]
    simp only [map_smul, smul_eq_mul, A, B]
  rw [hfactor]
  exact (Matrix.rank_mul_le_left A B).trans (by simpa using Matrix.rank_le_card_width A)

private def polynomialRow (p : Polynomial ℂ) : ℕ → Polynomial ℂ
  | 0 => Polynomial.X ^ 2 * p
  | 1 => Polynomial.X ^ 2 * Polynomial.hasseDeriv 1 p -
      Polynomial.C 2 * (Polynomial.X * p)
  | i+2 => Polynomial.X ^ 2 * Polynomial.hasseDeriv (i+2) p -
      Polynomial.C 2 * (Polynomial.X * Polynomial.hasseDeriv (i+1) p) +
        Polynomial.hasseDeriv i p

private theorem polynomial_row_probe (p : Polynomial ℂ) (i : ℕ) (w : ℂ) :
    polynomialCoefficient i (fun z => weightedHankel (fun z => p.eval z) z w) =
      (polynomialRow p i).eval w := by
  let q : Polynomial ℂ := Polynomial.X^2 * Polynomial.taylor w p -
    Polynomial.C (2*w) * (Polynomial.X * Polynomial.taylor w p) +
      Polynomial.C (w^2) * Polynomial.taylor w p
  have hq : (fun z => weightedHankel (fun z => p.eval z) z w) = fun z => q.eval z := by
    funext z
    simp only [q, weightedHankel, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.taylor_eval]
    ring
  rw [hq, polynomial_coefficient_eval]
  rcases i with _ | (_ | i)
  · simp only [q, polynomialRow, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_mul_zero,
      Polynomial.taylor_coeff_zero, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X]
    norm_num
  · simp only [q, polynomialRow, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_mul,
      Polynomial.taylor_coeff, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
    ring
  · simp only [q, polynomialRow, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul, Polynomial.coeff_X_mul,
      Polynomial.taylor_coeff, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    ring

private def topWeight (m : ℕ) : ℕ → ℂ
  | 0 => 1
  | 1 => (m : ℂ) - 2
  | i+2 => (m.choose (i+2) : ℂ) - 2 * (m.choose (i+1) : ℂ) + (m.choose i : ℂ)

private theorem polynomial_row_coefficient (p : Polynomial ℂ) (i n : ℕ) (hn : 2 ≤ n) :
    (polynomialRow p i).coeff n = topWeight (n+i-2) i * p.coeff (n+i-2) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 2 n]
  rcases i with _ | (_ | i)
  · simp [polynomialRow, topWeight]
  · have h₁ : n+2+1-2 = n+1 := by omega
    rw [h₁]
    simp only [polynomialRow, topWeight, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul,
      Polynomial.coeff_X_mul, Polynomial.hasseDeriv_coeff]
    simp only [Nat.choose_one_right]
    ring
  · have h₁ : n+2+(i+2)-2 = n+i+2 := by omega
    rw [h₁]
    simp only [polynomialRow, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul, Polynomial.coeff_X_mul,
      Polynomial.hasseDeriv_coeff]
    simp only [topWeight]
    have h₄ : n+(i+2) = n+i+2 := by omega
    have h₅ : n+1+(i+1) = n+i+2 := by omega
    have h₆ : n+2+i = n+i+2 := by omega
    rw [h₄, h₅, h₆]
    ring

private theorem top_weight_two_ne_zero (m : ℕ) (hm : 3 ≤ m) : topWeight m 2 ≠ 0 := by
  have hchoose : (2 : ℂ) * (m.choose 2 : ℂ) = (m : ℂ) * ((m : ℂ)-1) := by
    have h := congrArg (fun n : ℕ => (n : ℂ)) (Nat.descFactorial_eq_factorial_mul_choose m 2)
    norm_num [Nat.descFactorial_succ, Nat.descFactorial_one,
      Nat.cast_sub (show 1 ≤ m by omega)] at h
    linear_combination -h
  intro hzero
  have hpoly : (m : ℂ)^2 - 5*(m : ℂ) + 2 = 0 := by
    norm_num [topWeight] at hzero
    linear_combination -hchoose + 2*hzero
  have hreal : (m : ℝ)^2 - 5*(m : ℝ) + 2 = 0 := by exact_mod_cast hpoly
  by_cases hlarge : 5 ≤ m
  · have hlarge' : (5 : ℝ) ≤ m := by exact_mod_cast hlarge
    nlinarith [mul_nonneg (show 0 ≤ (m : ℝ) by positivity) (sub_nonneg.mpr hlarge')]
  · interval_cases m <;> norm_num at hreal

private theorem top_weight_three_ne_zero (m : ℕ) (hm : 3 ≤ m) (hm7 : m ≠ 7) :
    topWeight m 3 ≠ 0 := by
  have h₂ := congrArg (fun n : ℕ => (n : ℂ)) (Nat.descFactorial_eq_factorial_mul_choose m 2)
  have h₃ := congrArg (fun n : ℕ => (n : ℂ)) (Nat.descFactorial_eq_factorial_mul_choose m 3)
  norm_num [Nat.descFactorial_succ, Nat.descFactorial_one,
    Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_sub (show 2 ≤ m by omega)] at h₂ h₃
  have hidentity : (6 : ℂ) * topWeight m 3 =
      (m : ℂ) * ((m : ℂ)-2) * ((m : ℂ)-7) := by
    simp only [topWeight, Nat.choose_one_right]
    linear_combination -h₃ + 6*h₂
  have h₀ : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have h2 : (m : ℂ)-2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show m ≠ 2 by omega))
  have h7 : (m : ℂ)-7 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hm7)
  intro h
  rw [h, mul_zero] at hidentity
  exact mul_ne_zero (mul_ne_zero h₀ h2) h7 hidentity.symm

private def largeDegreeRows (m : ℕ) : Fin 4 → ℕ :=
  ![0, 1, 2, if m = 7 then 4 else 3]

private theorem large_degree_rows_strictMono (m : ℕ) : StrictMono (largeDegreeRows m) := by
  intro i j hij
  by_cases hm : m = 7 <;> fin_cases i <;> fin_cases j <;>
    norm_num [largeDegreeRows, hm] at *

private theorem large_degree_row_le (m : ℕ) (hm : 3 ≤ m) (i : Fin 4) :
    largeDegreeRows m i ≤ m := by
  by_cases h : m = 7 <;> fin_cases i <;> simp [largeDegreeRows, h] <;> omega

private theorem large_degree_top_weight_ne_zero (m : ℕ) (hm : 3 ≤ m) (i : Fin 4) :
    topWeight m (largeDegreeRows m i) ≠ 0 := by
  fin_cases i
  · norm_num [largeDegreeRows, topWeight]
  · simp only [largeDegreeRows, Matrix.cons_val_one, topWeight]
    exact sub_ne_zero.mpr (by exact_mod_cast (show m ≠ 2 by omega))
  · exact top_weight_two_ne_zero m hm
  · by_cases h : m = 7
    · subst m
      norm_num [largeDegreeRows, topWeight, Nat.choose_succ_succ]
    · simpa [largeDegreeRows, h] using
        top_weight_three_ne_zero m hm h

/-- Every polynomial of degree at least three gives a nonzero triangular
four-by-four coefficient minor, even when arbitrary entire separated factors
are allowed. Lower coefficients cannot cancel its top-degree diagonal. -/
theorem polynomial_degree_ge_three_not_separated_three (p : Polynomial ℂ)
    (hm : 3 ≤ p.natDegree) :
    ¬ SeparatedLE 3 (weightedHankel (fun z => p.eval z)) := by
  classical
  let m := p.natDegree
  let I := largeDegreeRows m
  let J : Fin 4 → ℕ := fun j => m+2-I j
  let M := kernelProbe (fun i => polynomialCoefficient (I i))
    (fun j => polynomialCoefficient (J j)) (weightedHankel (fun z => p.eval z))
  have hJ (j : Fin 4) : 2 ≤ J j := by
    have h := large_degree_row_le m hm j
    dsimp [J, I]
    omega
  have hentry (i j : Fin 4) :
      M i j = topWeight (J j+I i-2) (I i) * p.coeff (J j+I i-2) := by
    change polynomialCoefficient (J j)
      (fun w => polynomialCoefficient (I i)
        (fun z => weightedHankel (fun z => p.eval z) z w)) = _
    simp only [polynomial_row_probe]
    rw [polynomial_coefficient_eval, polynomial_row_coefficient p (I i) (J j) (hJ j)]
  have htri : M.IsUpperTriangular := by
    intro i j hij
    have hlt : I j < I i := large_degree_rows_strictMono m hij
    have hle : I j ≤ m := large_degree_row_le m hm j
    have hdegree : p.natDegree < J j+I i-2 := by
      change m < J j+I i-2
      dsimp [J]
      omega
    rw [hentry, Polynomial.coeff_eq_zero_of_natDegree_lt hdegree, mul_zero]
  have hdiag (i : Fin 4) : M i i ≠ 0 := by
    have hi : I i ≤ m := large_degree_row_le m hm i
    have heq : J i+I i-2 = m := by dsimp [J]; omega
    rw [hentry, heq, Polynomial.coeff_natDegree]
    exact mul_ne_zero (large_degree_top_weight_ne_zero m hm i)
      (Polynomial.leadingCoeff_ne_zero.mpr (by
        intro hp
        rw [hp, Polynomial.natDegree_zero] at hm
        omega))
  have hdet : M.det ≠ 0 := htri.det_ne_zero_iff.mpr hdiag
  intro hsep
  have hrank := kernel_probe_rank_le hsep
    (fun i => polynomialCoefficient (I i)) (fun j => polynomialCoefficient (J j))
  have hfull : M.rank = 4 := by simpa using Matrix.rank_of_det_ne_zero hdet
  change M.rank ≤ 3 at hrank
  omega

private def linearMinor (A B : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, A, B; 0, -2*A, -B, 0; A, -B, 0, 0; B, 0, 0, 0]

/-- A genuine degree-one polynomial has weighted-kernel rank at least four,
even when the candidate separated factors are arbitrary entire functions. -/
theorem linear_not_separated_three (A B : ℂ) (hB : B ≠ 0) :
    ¬ SeparatedLE 3 (weightedHankel (fun z => A+B*z)) := by
  classical
  let p : Polynomial ℂ := Polynomial.C A + Polynomial.C B * Polynomial.X
  let rows : Fin 4 → Polynomial ℂ :=
    ![Polynomial.C A * Polynomial.X^2 + Polynomial.C B * Polynomial.X^3,
      Polynomial.C (-2*A) * Polynomial.X + Polynomial.C (-B) * Polynomial.X^2,
      Polynomial.C A + Polynomial.C (-B) * Polynomial.X, Polynomial.C B]
  have hd₁ : Polynomial.hasseDeriv 1 p = Polynomial.C B := by
    dsimp only [p]
    rw [map_add, Polynomial.hasseDeriv_C 1 A (by decide),
      Polynomial.C_mul_X_eq_monomial, Polynomial.hasseDeriv_monomial]
    norm_num
  have hd₂ : Polynomial.hasseDeriv 2 p = 0 := by
    dsimp only [p]
    rw [map_add, Polynomial.hasseDeriv_C 2 A (by decide),
      Polynomial.C_mul_X_eq_monomial, Polynomial.hasseDeriv_monomial]
    norm_num
  have hd₃ : Polynomial.hasseDeriv 3 p = 0 := by
    dsimp only [p]
    rw [map_add, Polynomial.hasseDeriv_C 3 A (by decide),
      Polynomial.C_mul_X_eq_monomial, Polynomial.hasseDeriv_monomial]
    norm_num [Nat.choose_eq_zero_of_lt (by decide : 1 < 3)]
  have hr (i : Fin 4) : polynomialRow p i = rows i := by
    fin_cases i <;> norm_num [rows, polynomialRow, hd₁, hd₂, hd₃, p,
      Polynomial.C_ofNat] <;> ring
  have hp : (fun z : ℂ => A+B*z) = fun z => p.eval z := by
    funext z
    simp [p]
  have hprobe : kernelProbe (fun i : Fin 4 => polynomialCoefficient i)
      (fun i : Fin 4 => polynomialCoefficient i)
      (weightedHankel (fun z => A+B*z)) = linearMinor A B := by
    rw [hp]
    ext i j
    change polynomialCoefficient j
      (fun w => polynomialCoefficient i (fun z => weightedHankel (fun z => p.eval z) z w)) = _
    simp only [polynomial_row_probe]
    rw [polynomial_coefficient_eval, hr]
    fin_cases i <;> fin_cases j <;> dsimp [rows, linearMinor] <;>
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_C_mul_X, Polynomial.coeff_C] <;> norm_num
  have hdet : (linearMinor A B).det = B^4 := by
    norm_num [linearMinor, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
    ring
  intro hsep
  have hrank := kernel_probe_rank_le hsep
    (fun i : Fin 4 => polynomialCoefficient i) (fun i : Fin 4 => polynomialCoefficient i)
  rw [hprobe] at hrank
  have hfull := Matrix.rank_of_det_ne_zero (show (linearMinor A B).det ≠ 0 by
    rw [hdet]; exact pow_ne_zero 4 hB)
  rw [hfull] at hrank
  norm_num at hrank

private def quadraticRows (A B C : ℂ) : Fin 4 → Polynomial ℂ :=
  ![Polynomial.C A * Polynomial.X ^ 2 + Polynomial.C B * Polynomial.X ^ 3 +
      Polynomial.C C * Polynomial.X ^ 4,
    Polynomial.C (-2 * A) * Polynomial.X + Polynomial.C (-B) * Polynomial.X ^ 2,
    Polynomial.C A + Polynomial.C (-B) * Polynomial.X +
      Polynomial.C (-2 * C) * Polynomial.X ^ 2,
    Polynomial.C C]

private def quadraticMinor (A B C : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, A, C; 0, -2*A, -B, 0; A, -B, -2*C, 0; C, 0, 0, 0]

private theorem quadratic_coefficient_probe (A B C : ℂ) :
    kernelProbe (fun i : Fin 4 => polynomialCoefficient (![0, 1, 2, 4] i))
      (fun i : Fin 4 => polynomialCoefficient (![0, 1, 2, 4] i))
      (weightedHankel (fun z => A + B*z + C*z^2)) = quadraticMinor A B C := by
  classical
  let q (w : ℂ) : Polynomial ℂ :=
    Polynomial.C (w^2 * (A + B*w + C*w^2)) +
    Polynomial.C (-2*A*w-B*w^2) * Polynomial.X +
    Polynomial.C (A-B*w-2*C*w^2) * Polynomial.X^2 +
    Polynomial.C B * Polynomial.X^3 + Polynomial.C C * Polynomial.X^4
  have hrow (w : ℂ) :
      (fun z => weightedHankel (fun z => A+B*z+C*z^2) z w) = fun z => (q w).eval z := by
    ext z
    simp only [weightedHankel, q, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    ring
  have hrows (i : Fin 4) :
      (fun w => polynomialCoefficient (![0, 1, 2, 4] i)
        (fun z => weightedHankel (fun z => A+B*z+C*z^2) z w)) =
      fun w => (quadraticRows A B C i).eval w := by
    ext w
    rw [hrow, polynomial_coefficient_eval]
    fin_cases i <;> dsimp [q, quadraticRows] <;>
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X] <;> norm_num <;> ring
  ext i j
  change polynomialCoefficient (![0, 1, 2, 4] j)
    (fun w => polynomialCoefficient (![0, 1, 2, 4] i)
      (fun z => weightedHankel (fun z => A+B*z+C*z^2) z w)) = _
  rw [hrows, polynomial_coefficient_eval]
  fin_cases i <;> fin_cases j <;> dsimp [quadraticRows, quadraticMinor] <;>
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X, Polynomial.coeff_C] <;> norm_num

private theorem quadratic_minor_det (A B C : ℂ) :
    (quadraticMinor A B C).det = C ^ 2 * (B ^ 2 - 4 * A * C) := by
  norm_num [quadraticMinor, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- The complete complex discriminant obstruction for a genuine degree-two
polynomial, using all entire separated factors rather than polynomial factors. -/
theorem quadratic_separated_three_iff (A B C : ℂ) (hC : C ≠ 0) :
    SeparatedLE 3 (weightedHankel (fun z => A + B*z + C*z^2)) ↔ B^2 = 4*A*C := by
  constructor
  · intro hsep
    have hrank := kernel_probe_rank_le hsep
      (fun i : Fin 4 => polynomialCoefficient (![0, 1, 2, 4] i))
      (fun i : Fin 4 => polynomialCoefficient (![0, 1, 2, 4] i))
    rw [quadratic_coefficient_probe] at hrank
    have hdet : (quadraticMinor A B C).det = 0 := by
      by_contra h
      have hfull := Matrix.rank_of_det_ne_zero h
      rw [hfull] at hrank
      norm_num at hrank
    rw [quadratic_minor_det] at hdet
    exact sub_eq_zero.mp ((mul_eq_zero.mp hdet).resolve_left (pow_ne_zero 2 hC))
  · intro hdisc
    have hA : A = B^2 / (4*C) := by
      apply (eq_div_iff (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hC)).mpr
      linear_combination -hdisc
    have hp : (fun z : ℂ => A + B*z + C*z^2) =
        fun z => C * Complex.exp (0*z) * (z - (-B/(2*C)))^2 := by
      ext z
      simp only [zero_mul, Complex.exp_zero, mul_one]
      rw [hA]
      field_simp [hC]
      <;> ring
    rw [hp]
    exact separated_three_exponential_square C 0 (-B/(2*C))

private theorem separated_mul_factors {k : ℕ} {F : ℂ → ℂ → ℂ}
    (hF : SeparatedLE k F) (a b : ℂ → ℂ)
    (ha : Differentiable ℂ a) (hb : Differentiable ℂ b) :
    SeparatedLE k (fun z w => a z * b w * F z w) := by
  classical
  obtain ⟨g, h, hg, hh, hsep⟩ := hF
  refine ⟨fun i z => a z * g i z, fun i w => b w * h i w,
    fun i => ha.mul (hg i), fun i => hb.mul (hh i), ?_⟩
  intro z w
  simp only [hsep, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The polynomial part of every nonzero rank-three block is either a
constant or a quadratic with a double root. All complex coefficients remain
in scope, including zero linear coefficient and a root at zero. -/
theorem polynomial_separated_three_profile (p : Polynomial ℂ) (hp : p ≠ 0)
    (hsep : SeparatedLE 3 (weightedHankel (fun z => p.eval z))) :
    ∃ c : ℂ, c ≠ 0 ∧
      ((fun z => p.eval z) = (fun _ => c) ∨
        ∃ β : ℂ, (fun z => p.eval z) = (fun z => c*(z-β)^2)) := by
  have hdeg : p.natDegree < 3 := by
    by_contra h
    exact polynomial_degree_ge_three_not_separated_three p (Nat.le_of_not_gt h) hsep
  have hpform (z : ℂ) : p.eval z = p.coeff 0 + p.coeff 1*z + p.coeff 2*z^2 := by
    rw [Polynomial.eval_eq_sum_range' hdeg z]
    norm_num [Finset.sum_range_succ] <;> ring
  by_cases hzero : p.natDegree = 0
  · have h₁ : p.coeff 1 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have h₂ : p.coeff 2 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hc : p.coeff 0 ≠ 0 := by
      simpa only [← hzero, Polynomial.coeff_natDegree] using Polynomial.leadingCoeff_ne_zero.mpr hp
    refine ⟨p.coeff 0, hc, Or.inl ?_⟩
    funext z
    simp only [hpform, h₁, h₂, zero_mul, add_zero]
  by_cases hone : p.natDegree = 1
  · have h₁ : p.coeff 1 ≠ 0 := by
      simpa only [← hone, Polynomial.coeff_natDegree] using Polynomial.leadingCoeff_ne_zero.mpr hp
    have h₂ : p.coeff 2 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have heq : (fun z => p.eval z) = fun z => p.coeff 0+p.coeff 1*z := by
      funext z
      simp only [hpform, h₂, zero_mul, add_zero]
    rw [heq] at hsep
    exact (linear_not_separated_three _ _ h₁ hsep).elim
  have htwo : p.natDegree = 2 := by omega
  have hC : p.coeff 2 ≠ 0 := by
    simpa only [← htwo, Polynomial.coeff_natDegree] using Polynomial.leadingCoeff_ne_zero.mpr hp
  have hdisc : (p.coeff 1)^2 = 4*p.coeff 0*p.coeff 2 := by
    apply (quadratic_separated_three_iff _ _ _ hC).mp
    simpa only [← hpform] using hsep
  have hA : p.coeff 0 = (p.coeff 1)^2 / (4*p.coeff 2) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hC)).mpr
    linear_combination -hdisc
  refine ⟨p.coeff 2, hC, Or.inr ⟨-p.coeff 1/(2*p.coeff 2), ?_⟩⟩
  funext z
  rw [hpform, hA]
  field_simp [hC]
  <;> ring

private theorem weighted_exponential_separated_iff (f : ℂ → ℂ) (α : ℂ) (k : ℕ) :
    SeparatedLE k (weightedHankel (fun z => Complex.exp (α*z) * f z)) ↔
      SeparatedLE k (weightedHankel f) := by
  have he (β : ℂ) : Differentiable ℂ (fun z => Complex.exp (β*z)) :=
    Complex.differentiable_exp.comp (differentiable_id.const_mul β)
  constructor
  · intro h
    have h' := separated_mul_factors h (fun z => Complex.exp (-α*z))
      (fun z => Complex.exp (-α*z)) (he (-α)) (he (-α))
    convert h' using 1
    funext z w
    simp only [weightedHankel, mul_add, Complex.exp_add, neg_mul, Complex.exp_neg]
    field_simp [Complex.exp_ne_zero]
    <;> ring
  · intro h
    have h' := separated_mul_factors h (fun z => Complex.exp (α*z))
      (fun z => Complex.exp (α*z)) (he α) (he α)
    convert h' using 1
    funext z w
    simp only [weightedHankel, mul_add, Complex.exp_add]
    ring

/-- Two distinct nonzero exponent blocks already force a four-dimensional
minor. The projections act on arbitrary entire factors through their
algebraic extensions, so no polynomial-factor premise is hidden here. -/
theorem two_exponential_blocks_not_separated_three {ι : Type*} [Fintype ι]
    (α : ι → ℂ) (hα : Function.Injective α) (p : ι → Polynomial ℂ)
    (i j : ι) (hij : i ≠ j) (hi : p i ≠ 0) (hj : p j ≠ 0) :
    ¬ SeparatedLE 3 (weightedHankel (blockEvaluation α p)) := by
  classical
  let f : ι → ℂ → ℂ := fun b z => Complex.exp (α b*z) * (p b).eval z
  let K : ι → ℂ → ℂ → ℂ := fun b => weightedHankel (f b)
  have hf (b : ι) : Continuous (f b) :=
    ((Complex.differentiable_exp.comp (differentiable_id.const_mul (α b))).mul
      (p b).differentiable).continuous
  have hf0 (b : ι) (hb : p b ≠ 0) : f b ≠ 0 := by
    intro h
    apply exponential_polynomial_block_ne_zero (α b) hb
    exact Subtype.ext h
  obtain ⟨u, hu⟩ := weighted_hankel_three_point_minor (hf i) (hf0 i hi)
  have hex : ∃ x y : ℂ, K j x y ≠ 0 := by
    by_contra h
    push_neg at h
    obtain ⟨v, hv⟩ := weighted_hankel_three_point_minor (hf j) (hf0 j hj)
    have hzero : (Matrix.of (fun a b => K j (v a) (v b))) = 0 := by
      ext a b
      exact h _ _
    apply hv
    change (Matrix.of (fun a b => K j (v a) (v b))).det = 0
    rw [hzero, Matrix.det_zero]
  obtain ⟨x, y, hxy⟩ := hex
  let F := weightedHankel (blockEvaluation α p)
  let l : Fin 3 ⊕ Fin 1 → (ℂ → ℂ) →ₗ[ℂ] ℂ :=
    Sum.elim (fun a => (LinearMap.proj (u a)).comp (blockProjection α i))
      (fun _ => (LinearMap.proj x).comp (blockProjection α j))
  let r : Fin 3 ⊕ Fin 1 → (ℂ → ℂ) →ₗ[ℂ] ℂ :=
    Sum.elim (fun a => (LinearMap.proj (u a)).comp (blockProjection α i))
      (fun _ => (LinearMap.proj y).comp (blockProjection α j))
  let A : Matrix (Fin 3) (Fin 3) ℂ := fun a b => K i (u a) (u b)
  let D : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => K j x y
  have hleft (b : ι) (z w : ℂ) :
      blockProjection α b (fun t => F t w) z = K b z w :=
    congrFun (block_projection_weighted_sum α hα p b w) z
  have hright (b c : ι) (z w : ℂ) :
      blockProjection α b (fun t => K c z t) w =
        if b = c then K c z w else 0 := by
    have h := congrFun (block_projection_weighted_single_right α hα b c (p c) z) w
    simpa only [K, f, ite_apply, Pi.zero_apply] using h
  have hmatrix : kernelProbe l r F = Matrix.fromBlocks A 0 0 D := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    all_goals
      simp only [kernelProbe, l, r, Sum.elim_inl, Sum.elim_inr,
        LinearMap.comp_apply, LinearMap.proj_apply, hleft]
    · change blockProjection α i (fun t => K i (u a) t) (u b) = K i (u a) (u b)
      simpa only [if_pos rfl, ite_true] using hright i i (u a) (u b)
    · change blockProjection α j (fun t => K i (u a) t) y = 0
      simpa only [if_neg (Ne.symm hij)] using hright j i (u a) y
    · change blockProjection α i (fun t => K j x t) (u b) = 0
      simpa only [if_neg hij] using hright i j x (u b)
    · change blockProjection α j (fun t => K j x t) y = K j x y
      simpa only [if_pos rfl, ite_true] using hright j j x y
  have hD : D.det ≠ 0 := by
    rw [Matrix.det_fin_one D]
    exact hxy
  have hdet : (kernelProbe l r F).det ≠ 0 := by
    rw [hmatrix, Matrix.det_fromBlocks_zero₂₁]
    exact mul_ne_zero hu hD
  have hfull : (kernelProbe l r F).rank = 4 := by
    simpa using Matrix.rank_of_det_ne_zero hdet
  intro hsep
  have hrank := kernel_probe_rank_le hsep l r
  change (kernelProbe l r F).rank ≤ 3 at hrank
  omega

/-- The exhaustive rank-three classification on the entire complex plane.
Finite separation first gives a finite exponential-polynomial presentation;
distinct-block projections and every polynomial degree case then force one
of exactly the two stated profiles. -/
theorem separated_three_iff_profile {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hf0 : f ≠ 0) :
    SeparatedLE 3 (weightedHankel f) ↔
      ∃ c α : ℂ, c ≠ 0 ∧
        (f = (fun z => c*Complex.exp (α*z)) ∨
          ∃ β : ℂ, f = (fun z => c*Complex.exp (α*z)*(z-β)^2)) := by
  classical
  constructor
  · intro hsep
    have hep := exponential_polynomial_of_weighted_separation hf ⟨3, hsep⟩
    obtain ⟨s, p, hp, hs⟩ := hep.distinct_presentation
    let α : s → ℂ := Subtype.val
    let q : s → Polynomial ℂ := fun i => p i
    have hα : Function.Injective α := Subtype.val_injective
    have hfun : f = blockEvaluation α q := by
      funext z
      rw [hs z]
      exact (Finset.sum_coe_sort s (fun β => Complex.exp (β*z)*(p β).eval z)).symm
    have hsep' : SeparatedLE 3 (weightedHankel (blockEvaluation α q)) := by
      rwa [hfun] at hsep
    have hsingle (i j : s) : i = j := by
      by_contra hij
      exact two_exponential_blocks_not_separated_three α hα q i j hij
        (hp i i.property) (hp j j.property) hsep'
    have hnonempty : s.Nonempty := by
      by_contra h
      have hnil := Finset.not_nonempty_iff_eq_empty.mp h
      apply hf0
      funext z
      rw [hs z, hnil]
      simp
    obtain ⟨β, hβ⟩ := hnonempty
    have hset : s = {β} := by
      ext γ
      constructor
      · intro hγ
        exact Finset.mem_singleton.mpr
          (congrArg Subtype.val (hsingle ⟨γ, hγ⟩ ⟨β, hβ⟩))
      · intro hγ
        have hγβ := Finset.mem_singleton.mp hγ
        simpa only [hγβ] using hβ
    have heq : f = fun z => Complex.exp (β*z)*(p β).eval z := by
      funext z
      rw [hs z, hset, Finset.sum_singleton]
    have hpoly : SeparatedLE 3 (weightedHankel (fun z => (p β).eval z)) := by
      apply (weighted_exponential_separated_iff _ β 3).mp
      simpa only [← heq] using hsep
    obtain ⟨c, hc, hconstant | ⟨root, hquadratic⟩⟩ :=
      polynomial_separated_three_profile (p β) (hp β hβ) hpoly
    · refine ⟨c, β, hc, Or.inl ?_⟩
      rw [heq]
      funext z
      rw [congrFun hconstant z]
      ring
    · refine ⟨c, β, hc, Or.inr ⟨root, ?_⟩⟩
      rw [heq]
      funext z
      rw [congrFun hquadratic z]
      ring
  · rintro ⟨c, α, _, h | ⟨β, h⟩⟩
    · rw [h]
      exact separated_three_exponential c α
    · rw [h]
      exact separated_three_exponential_square c α β

#print axioms quadratic_separated_three_iff
#print axioms polynomial_degree_ge_three_not_separated_three
#print axioms linear_not_separated_three
#print axioms two_exponential_blocks_not_separated_three
#print axioms separated_three_iff_profile

end D5.S3.Analytic.Entire
