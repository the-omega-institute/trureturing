/- GID: D5/S3/Zeros/Jensen/FactorialJensenKernelBound
   generality: G
   mirror-B: D5/B/S3/Zeros/Jensen/FactorialJensenKernelBound
   mirror-E: none(waiver:all-degree-symbolic-estimate)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Series]
   utility: none
   digest: The full factorial Jensen polynomial kernel has a degree-uniform energy bound. -/

/-
This is the exact finite polynomial T_n of r79, with its anti-diagonals
enumerated before its entries.  The index i below stands for I-1, where
1 <= I <= n.  For each j < I and l < I-j, put the complete divided-
difference weight at (a,b)=(j+l,I-1-l).  Hence a+b+1=I+j and j<=a,b.
Every pair has I-j matrix locations and I-j polynomial monomials.
-/

import Mathlib.Data.Matrix.Basis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.Jensen.FactorialJensenKernelBound

open scoped BigOperators

/-- The exact moment-free coefficient in the normalized source Jensen sum. -/
def fallingEvenCoefficient (n k : ℕ) : ℝ :=
  (n.descFactorial k : ℝ) / (n : ℝ)^k / ((2*k).factorial : ℝ)

/-- The polynomial extension of (r^d-s^d)/(r-s), including both endpoints
and the diagonal. -/
def powerDividedDifference (d : ℕ) (r s : ℝ) : ℝ :=
  ∑ k : Fin d, r^(d-1-k.val) * s^k.val

private def pairWeight (n i j : ℕ) (r s : ℝ) : ℝ :=
  fallingEvenCoefficient n i * fallingEvenCoefficient n j *
    r^j * s^j * powerDividedDifference (i-j) r s

private def antiDiagonalRow {n : ℕ} (i : Fin n) (j : Fin (i.val + 1))
    (l : Fin (i.val + 1 - j.val)) : Fin n :=
  ⟨j.val+l.val, by have := i.isLt; have := j.isLt; have := l.isLt; omega⟩

private def antiDiagonalColumn {n : ℕ} (i : Fin n) (j : Fin (i.val + 1))
    (l : Fin (i.val + 1 - j.val)) : Fin n :=
  ⟨i.val-l.val, by have := i.isLt; omega⟩

/-- The exact n by n finite factorial Jensen kernel.  Each pair I>j contributes
its full divided-difference polynomial at every one of its I-j anti-diagonal
locations.  No division by r-s occurs in this definition. -/
def factorialJensenKernel (n : ℕ) (r s : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i : Fin n, ∑ j : Fin (i.val + 1), ∑ l : Fin (i.val + 1 - j.val),
    Matrix.single (antiDiagonalRow i j l) (antiDiagonalColumn i j l)
      (pairWeight n (i.val + 1) j.val r s)

private def entrySum (n : ℕ) : Matrix (Fin n) (Fin n) ℝ →+ ℝ where
  toFun A := ∑ a, ∑ b, A a b
  map_zero' := by simp
  map_add' A B := by simp [Finset.sum_add_distrib]

private theorem entry_sum_single {n : ℕ} (a b : Fin n) (w : ℝ) :
    entrySum n (Matrix.single a b w) = w := by
  simp [entrySum, Matrix.single, Matrix.of_apply, ite_and]

private theorem anti_diagonal_entry {n : ℕ} (i : Fin n) (j : Fin (i.val + 1))
    (a b : Fin n) (w : ℝ) :
    (∑ l : Fin (i.val + 1 - j.val),
      Matrix.single (antiDiagonalRow i j l) (antiDiagonalColumn i j l) w) a b =
      if j.val ≤ a.val ∧ a.val ≤ i.val ∧ a.val+b.val=i.val+j.val then w else 0 := by
  classical
  simp only [Matrix.sum_apply, Matrix.single_apply]
  by_cases h : j.val ≤ a.val ∧ a.val ≤ i.val ∧ a.val+b.val=i.val+j.val
  · rw [if_pos h]
    let l₀ : Fin (i.val + 1 - j.val) := ⟨a.val-j.val, by omega⟩
    rw [Finset.sum_eq_single l₀]
    · apply if_pos
      constructor
      · apply Fin.ext
        dsimp [antiDiagonalRow, l₀]
        omega
      · apply Fin.ext
        dsimp [antiDiagonalColumn, l₀]
        omega
    · intro l _ hne
      apply if_neg
      intro hl
      apply hne
      apply Fin.ext
      have he := congrArg Fin.val hl.1
      dsimp [antiDiagonalRow, l₀] at he ⊢
      omega
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro l _
    apply if_neg
    intro hl
    apply h
    have ha := congrArg Fin.val hl.1
    have hb := congrArg Fin.val hl.2
    have hj := j.isLt
    have hll := l.isLt
    dsimp [antiDiagonalRow, antiDiagonalColumn] at ha hb
    omega

private theorem kernel_entry (n : ℕ) (r s : ℝ) (a b : Fin n) :
    factorialJensenKernel n r s a b =
      ∑ i : Fin n, ∑ j : Fin (i.val + 1),
        if j.val ≤ a.val ∧ a.val ≤ i.val ∧ a.val+b.val=i.val+j.val then
          pairWeight n (i.val + 1) j.val r s else 0 := by
  simp only [factorialJensenKernel, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Matrix.sum_apply] using
    anti_diagonal_entry i j a b (pairWeight n (i.val + 1) j.val r s)

private theorem falling_nonneg (n k : ℕ) : 0 ≤ fallingEvenCoefficient n k := by
  unfold fallingEvenCoefficient
  positivity

private theorem falling_le (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    fallingEvenCoefficient n k ≤ 1 / ((2*k).factorial : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : (0 : ℝ) < (n : ℝ)^k := pow_pos hn0 _
  have hf : (n.descFactorial k : ℝ) ≤ (n : ℝ)^k := by
    exact_mod_cast Nat.descFactorial_le_pow n k
  have hr : (n.descFactorial k : ℝ) / (n : ℝ)^k ≤ 1 :=
    (div_le_one hp).mpr hf
  exact div_le_div_of_nonneg_right hr (by positivity)

private theorem divided_difference_nonneg (d : ℕ) (r s : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) : 0 ≤ powerDividedDifference d r s := by
  unfold powerDividedDifference
  apply Finset.sum_nonneg
  intro k _
  positivity

private theorem divided_difference_le (d : ℕ) (r s M : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrM : r ≤ M) (hsM : s ≤ M) :
    powerDividedDifference d r s ≤ (d : ℝ)*M^(d-1) := by
  have hM : 0 ≤ M := hr.trans hrM
  calc
    powerDividedDifference d r s ≤ ∑ _k : Fin d, M^(d-1) := by
      apply Finset.sum_le_sum
      intro k _
      have hk := k.isLt
      calc
        r^(d-1-k.val)*s^k.val ≤ M^(d-1-k.val)*M^k.val := by
          exact mul_le_mul (pow_le_pow_left₀ hr hrM _)
            (pow_le_pow_left₀ hs hsM _) (pow_nonneg hs _) (pow_nonneg hM _)
        _ = M^(d-1) := by rw [← pow_add, show d-1-k.val+k.val=d-1 by omega]
    _ = (d : ℝ)*M^(d-1) := by simp

private theorem pair_nonneg (n i j : ℕ) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    0 ≤ pairWeight n i j r s := by
  unfold pairWeight
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (falling_nonneg _ _) (falling_nonneg _ _))
      (pow_nonneg hr _)) (pow_nonneg hs _))
    (divided_difference_nonneg _ _ _ hr hs)

private theorem kernel_nonneg (n : ℕ) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (a b : Fin n) : 0 ≤ factorialJensenKernel n r s a b := by
  rw [kernel_entry]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact pair_nonneg _ _ _ _ _ hr hs
  · exact le_rfl

private theorem kernel_mass (n : ℕ) (r s : ℝ) :
    entrySum n (factorialJensenKernel n r s) =
      ∑ i : Fin n, ∑ j : Fin (i.val + 1),
        ((i.val + 1 - j.val : ℕ) : ℝ)*pairWeight n (i.val + 1) j.val r s := by
  simp only [factorialJensenKernel, map_sum, entry_sum_single,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private theorem square_factorial_le (i : ℕ) :
    ((i+1 : ℕ) : ℝ)^2 / ((2*(i+1)).factorial : ℝ) ≤
      1 / (2*((2*i).factorial : ℝ)) := by
  have hF : (0 : ℝ) < ((2*i).factorial : ℝ) := by positivity
  have hi : (0 : ℝ) ≤ i := by positivity
  have heq : ((2*(i+1)).factorial : ℝ) =
      (2*(i : ℝ)+2)*(2*(i : ℝ)+1)*((2*i).factorial : ℝ) := by
    rw [show 2*(i+1)=(2*i+1)+1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  rw [heq]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hb : 2*((i : ℝ)+1)^2 ≤ (2*(i : ℝ)+2)*(2*(i : ℝ)+1) := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hb hF.le
  push_cast
  nlinarith [hm]

def evenFactorialSum (n : ℕ) (M : ℝ) : ℝ :=
  ∑ k : Fin n, M^k.val / ((2*k.val).factorial : ℝ)

private theorem even_sum_nonneg (n : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    0 ≤ evenFactorialSum n M := by
  unfold evenFactorialSum
  apply Finset.sum_nonneg
  intro k _
  positivity

private theorem even_sum_mono (m n : ℕ) (hmn : m ≤ n) (M : ℝ) (hM : 0 ≤ M) :
    evenFactorialSum m M ≤ evenFactorialSum n M := by
  unfold evenFactorialSum
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => M^k / ((2*k).factorial : ℝ)) m,
    Fin.sum_univ_eq_sum_range (fun k : ℕ => M^k / ((2*k).factorial : ℝ)) n]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
  intro k _ _
  positivity

theorem even_sum_le_cosh (n : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    evenFactorialSum n M ≤ Real.cosh (Real.sqrt M) := by
  have hsum : HasSum (fun k : ℕ => M^k / ((2*k).factorial : ℝ))
      (Real.cosh (Real.sqrt M)) := by
    simpa only [pow_mul, Real.sq_sqrt hM] using Real.hasSum_cosh (Real.sqrt M)
  unfold evenFactorialSum
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => M^k / ((2*k).factorial : ℝ)) n]
  exact sum_le_hasSum (Finset.range n) (fun k _ => by positivity) hsum

private theorem pair_mass_le (n : ℕ) (hn : 1 ≤ n) (i j : ℕ) (hj : j ≤ i)
    (r s M : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hrM : r ≤ M) (hsM : s ≤ M) :
    ((i+1-j : ℕ) : ℝ)*pairWeight n (i+1) j r s ≤
      (1/2 : ℝ)*(M^i / ((2*i).factorial : ℝ))*(M^j / ((2*j).factorial : ℝ)) := by
  have hM : 0 ≤ M := hr.trans hrM
  have hd : (0 : ℝ) ≤ ((i+1-j : ℕ) : ℝ) := by positivity
  have hdle : ((i+1-j : ℕ) : ℝ) ≤ ((i+1 : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le (i+1) j
  have hcI := falling_le n hn (i+1)
  have hcj := falling_le n hn j
  have hpI := falling_nonneg n (i+1)
  have hpj := falling_nonneg n j
  have hdd := divided_difference_le (i+1-j) r s M hr hs hrM hsM
  have hd0 := divided_difference_nonneg (i+1-j) r s hr hs
  have hpower : r^j*s^j ≤ M^j*M^j :=
    mul_le_mul (pow_le_pow_left₀ hr hrM j) (pow_le_pow_left₀ hs hsM j)
      (pow_nonneg hs _) (pow_nonneg hM _)
  have hmonomial := mul_le_mul hpower hdd hd0
    (mul_nonneg (pow_nonneg hM _) (pow_nonneg hM _))
  have hcoefficient : fallingEvenCoefficient n (i+1)*fallingEvenCoefficient n j ≤
      (1/((2*(i+1)).factorial : ℝ))*(1/((2*j).factorial : ℝ)) :=
    mul_le_mul hcI hcj hpj (by positivity)
  have hfull := mul_le_mul (pow_le_pow_left₀ hd hdle 2) hcoefficient
    (mul_nonneg hpI hpj) (sq_nonneg (((i+1 : ℕ) : ℝ)))
  calc
    ((i+1-j : ℕ) : ℝ)*pairWeight n (i+1) j r s ≤
        ((i+1-j : ℕ) : ℝ)^2 * fallingEvenCoefficient n (i+1) *
          fallingEvenCoefficient n j * (M^i*M^j) := by
      unfold pairWeight
      calc
        _ = (((i+1-j : ℕ) : ℝ)*fallingEvenCoefficient n (i+1)*
            fallingEvenCoefficient n j)*(r^j*s^j*powerDividedDifference (i+1-j) r s) := by
          ring
        _ ≤ (((i+1-j : ℕ) : ℝ)*fallingEvenCoefficient n (i+1)*
            fallingEvenCoefficient n j)*(M^j*M^j*(((i+1-j : ℕ) : ℝ)*M^(i+1-j-1))) :=
          mul_le_mul_of_nonneg_left hmonomial (mul_nonneg (mul_nonneg hd hpI) hpj)
        _ = ((i+1-j : ℕ) : ℝ)^2 * fallingEvenCoefficient n (i+1) *
            fallingEvenCoefficient n j * (M^j*M^j*M^(i+1-j-1)) := by ring
        _ = _ := by
          rw [← pow_add M j j, ← pow_add M (j+j) (i+1-j-1),
            show j+j+(i+1-j-1)=i+j by omega, pow_add]
    _ ≤ ((i+1 : ℕ) : ℝ)^2 * (1/((2*(i+1)).factorial : ℝ)) *
          (1/((2*j).factorial : ℝ)) * (M^i*M^j) := by
      calc
        _ = (((i+1-j : ℕ) : ℝ)^2 *
            (fallingEvenCoefficient n (i+1)*fallingEvenCoefficient n j))*(M^i*M^j) := by
          ring
        _ ≤ (((i+1 : ℕ) : ℝ)^2 *
            ((1/((2*(i+1)).factorial : ℝ))*(1/((2*j).factorial : ℝ))))*(M^i*M^j) :=
          mul_le_mul_of_nonneg_right hfull (mul_nonneg (pow_nonneg hM i) (pow_nonneg hM j))
        _ = _ := by ring
    _ = (((i+1 : ℕ) : ℝ)^2 / ((2*(i+1)).factorial : ℝ)) *
          (M^i*M^j / ((2*j).factorial : ℝ)) := by ring
    _ ≤ (1 / (2*((2*i).factorial : ℝ))) *
          (M^i*M^j / ((2*j).factorial : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (square_factorial_le i) (by positivity)
    _ = _ := by ring

private theorem kernel_mass_le_finite (n : ℕ) (hn : 1 ≤ n) (r s M : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrM : r ≤ M) (hsM : s ≤ M) :
    entrySum n (factorialJensenKernel n r s) ≤ (1/2 : ℝ)*(evenFactorialSum n M)^2 := by
  have hM : 0 ≤ M := hr.trans hrM
  rw [kernel_mass]
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin (i.val + 1),
        (1/2 : ℝ)*(M^i.val/((2*i.val).factorial : ℝ))*
          (M^j.val/((2*j.val).factorial : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact pair_mass_le n hn i.val j.val (by have := j.isLt; omega) r s M hr hs hrM hsM
    _ = ∑ i : Fin n, (1/2 : ℝ)*(M^i.val/((2*i.val).factorial : ℝ))*
        evenFactorialSum (i.val + 1) M := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [evenFactorialSum, Finset.mul_sum]
    _ ≤ ∑ i : Fin n, (1/2 : ℝ)*(M^i.val/((2*i.val).factorial : ℝ))*
        evenFactorialSum n M := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left
      · exact even_sum_mono (i.val + 1) n i.isLt M hM
      · positivity
    _ = (1/2 : ℝ)*(evenFactorialSum n M)^2 := by
      simp only [evenFactorialSum, ← Finset.sum_mul, ← Finset.mul_sum]
      ring

private theorem cosh_le_exp (x : ℝ) (hx : 0 ≤ x) : Real.cosh x ≤ Real.exp x := by
  rw [Real.cosh_eq]
  have h := Real.exp_le_exp.mpr (show -x ≤ x by linarith)
  linarith

private theorem energy_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ ∑ i, (v i)^2 := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (v i))

private theorem coordinate_product_le_energy {n : ℕ} (v : Fin n → ℝ) (a b : Fin n) :
    |v a * v b| ≤ ∑ i, (v i)^2 := by
  have ha : (v a)^2 ≤ ∑ i, (v i)^2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (v i)) (Finset.mem_univ a)
  have hb : (v b)^2 ≤ ∑ i, (v i)^2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (v i)) (Finset.mem_univ b)
  rw [abs_mul]
  nlinarith [sq_nonneg (|v a|-|v b|), sq_abs (v a), sq_abs (v b)]

private theorem quadratic_le_mass {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ a b, 0 ≤ A a b) (v : Fin n → ℝ) :
    |∑ a, ∑ b, v a * A a b * v b| ≤ (∑ i, (v i)^2)*entrySum n A := by
  calc
    _ ≤ ∑ a, |∑ b, v a*A a b*v b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, ∑ b, |v a*A a b*v b| := by
      apply Finset.sum_le_sum
      intro a _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, ∑ b, (∑ i, (v i)^2)*A a b := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      calc
        |v a*A a b*v b| = |v a*v b| * A a b := by
          simp only [abs_mul, abs_of_nonneg (hA a b)]
          ring
        _ ≤ (∑ i, (v i)^2)*A a b :=
          mul_le_mul_of_nonneg_right (coordinate_product_le_energy v a b) (hA a b)
    _ = _ := by simp [entrySum, Finset.mul_sum]

/-- All degrees, with the exact falling-factorial source normalization: the entire
finite polynomial kernel is entrywise nonnegative and has total mass at most
one half cosh(sqrt(max(r,s))) squared, hence one half exp(2 sqrt(max(r,s))).
The quadratic form is controlled in the Euclidean coefficient energy, with
no factor depending on n.  This estimates absolute size, not positivity of
the integrated theta form. -/
theorem factorial_jensen_kernel_uniform_bound (n : ℕ) (hn : 1 ≤ n)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (∀ a b, 0 ≤ factorialJensenKernel n r s a b) ∧
    (∑ a, ∑ b, factorialJensenKernel n r s a b) ≤
      (1/2 : ℝ)*(Real.cosh (Real.sqrt (max r s)))^2 ∧
    (∑ a, ∑ b, factorialJensenKernel n r s a b) ≤
      (1/2 : ℝ)*Real.exp (2*Real.sqrt (max r s)) ∧
    (∀ v : Fin n → ℝ,
      |∑ a, ∑ b, v a*factorialJensenKernel n r s a b*v b| ≤
        ((1/2 : ℝ)*Real.exp (2*Real.sqrt (max r s)))*(∑ i, (v i)^2)) := by
  have hM : 0 ≤ max r s := hr.trans (le_max_left _ _)
  have hN := kernel_nonneg n r s hr hs
  have hfinite := kernel_mass_le_finite n hn r s (max r s) hr hs
    (le_max_left _ _) (le_max_right _ _)
  have hsum := even_sum_le_cosh n (max r s) hM
  have hsum0 := even_sum_nonneg n (max r s) hM
  have hC0 : 0 ≤ Real.cosh (Real.sqrt (max r s)) := (Real.cosh_pos _).le
  have hC : entrySum n (factorialJensenKernel n r s) ≤
      (1/2 : ℝ)*(Real.cosh (Real.sqrt (max r s)))^2 := by
    apply hfinite.trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsum0 hsum 2) (by norm_num)
  have hE : entrySum n (factorialJensenKernel n r s) ≤
      (1/2 : ℝ)*Real.exp (2*Real.sqrt (max r s)) := by
    apply hC.trans
    calc
      _ ≤ (1/2 : ℝ)*(Real.exp (Real.sqrt (max r s)))^2 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hC0 (cosh_le_exp _ (Real.sqrt_nonneg _)) 2) (by norm_num)
      _ = _ := by rw [two_mul, Real.exp_add]; ring
  refine ⟨hN, hC, hE, ?_⟩
  intro v
  calc
    _ ≤ (∑ i, (v i)^2)*entrySum n (factorialJensenKernel n r s) :=
      quadratic_le_mass _ hN v
    _ ≤ (∑ i, (v i)^2)*((1/2 : ℝ)*Real.exp (2*Real.sqrt (max r s))) :=
      mul_le_mul_of_nonneg_left hE (energy_nonneg v)
    _ = _ := by ring

end D5.S3.Zeros.Jensen.FactorialJensenKernelBound
