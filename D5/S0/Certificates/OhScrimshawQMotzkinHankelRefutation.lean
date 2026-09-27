/- GID: D5/S0/Certificates/OhScrimshawQMotzkinHankelRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/OhScrimshawQMotzkinHankelRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/OhScrimshawQMotzkinHankelRefutation.claim; result=D5/S0/Certificates/OhScrimshawQMotzkinHankelRefutation.result; claim=D5/S0/Certificates/OhScrimshawQMotzkinHankelRefutation.claim
   digest: Refutes the printed two-shifted q-Motzkin Hankel conjecture of arXiv:1805.00113v1, Appendix A, at n = 3, where the determinant is 3 at q = 1 and the printed factor is 2; makes no claim against a corrected summation range. -/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.OhScrimshawQMotzkinHankelRefutation

open scoped BigOperators
open Polynomial

/-!
Oh–Scrimshaw, *Identities from representation theory*, arXiv:1805.00113v1, Appendix
"Other q-determinants", the first conjecture labelled `conj:factored_motzkin_2shifted`:
with Cigler's `q`-Motzkin numbers `M̃†_{n+1} = M̃†_n + Σ_{k<n} q^{k+1} M̃†_k M̃†_{n-k-1}`,
`M̃†_0 = 1`, and `f_n(q) = Σ_{1 ≤ k ≤ n, k ≢ 1 (mod 3)} q^k` for `n ≡ 0 (mod 3)`,
`f_n(q) = (q+1) Σ_{k ≤ ⌊n/3⌋} q^{3k}` otherwise, the determinants
`det[M̃†_{i+j+2}(q)]_{i,j=0}^{n-1}` equal `q^{c_n} f_n(q)` for some `c_n ∈ ℤ_{≥0}`.
At `n = 3` the determinant is `q^{11}(1 + q^2 + q^3)`; evaluating at `q = 1` gives `3`,
while `f_3(1) = 2`.
-/

/-- Cigler's `q`-Motzkin numbers over a commutative ring, with parameter `q`. -/
def qMotzkin {R : Type*} [CommRing R] (q : R) : ℕ → R
  | 0 => 1
  | n + 1 => qMotzkin q n +
      ∑ k : Fin n, q ^ (k.val + 1) * qMotzkin q k.val * qMotzkin q (n - k.val - 1)
decreasing_by all_goals omega

/-- The printed factor `f_n(q)`. -/
def fPrinted {R : Type*} [CommRing R] (q : R) (n : ℕ) : R :=
  if n % 3 = 0 then ∑ k ∈ (Finset.Icc 1 n).filter (fun k => k % 3 ≠ 1), q ^ k
  else (q + 1) * ∑ k ∈ Finset.range (n / 3 + 1), q ^ (3 * k)

/-- The two-shifted Hankel determinant `det[M̃†_{i+j+2}(q)]_{i,j=0}^{n-1}`. -/
def hankelTwoShifted {R : Type*} [CommRing R] (q : R) (n : ℕ) : R :=
  Matrix.det (Matrix.of fun i j : Fin n => qMotzkin q (i.val + j.val + 2))

/-- The printed conjecture, as an identity in `ℤ[q]` for every `n ≥ 1`. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ c : ℕ, hankelTwoShifted (X : ℤ[X]) n = X ^ c * fPrinted (X : ℤ[X]) n

/-- At `n = 3`, evaluation at `q = 1` sends the determinant to the Motzkin Hankel
determinant `det[[2,4,9],[4,9,21],[9,21,51]] = 3` and the printed side to `f_3(1) = 2`. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨c, hc⟩ := h 3 (by norm_num)
  have hmap : ∀ n, (qMotzkin (X : ℤ[X]) n).eval 1 = qMotzkin (1 : ℤ) n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      cases n with
      | zero => simp [qMotzkin]
      | succ n =>
        rw [qMotzkin, qMotzkin, eval_add, eval_finsetSum, ih n (by omega)]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [eval_mul, eval_mul, eval_pow, eval_X, ih k.val (by omega),
          ih (n - k.val - 1) (by omega)]
  have v0 : qMotzkin (1 : ℤ) 0 = 1 := by rw [qMotzkin]
  have v1 : qMotzkin (1 : ℤ) 1 = 1 := by rw [qMotzkin]; simp [v0]
  have v2 : qMotzkin (1 : ℤ) 2 = 2 := by
    rw [qMotzkin]; simp [v0, v1]
  have v3 : qMotzkin (1 : ℤ) 3 = 4 := by
    rw [qMotzkin]; simp [Fin.sum_univ_succ, v0, v1, v2]
  have v4 : qMotzkin (1 : ℤ) 4 = 9 := by
    rw [qMotzkin]; simp [Fin.sum_univ_succ, v0, v1, v2, v3]
  have v5 : qMotzkin (1 : ℤ) 5 = 21 := by
    rw [qMotzkin]; simp [Fin.sum_univ_succ, v0, v1, v2, v3, v4]
  have v6 : qMotzkin (1 : ℤ) 6 = 51 := by
    rw [qMotzkin]; simp [Fin.sum_univ_succ, v0, v1, v2, v3, v4, v5]
  have hdet : (hankelTwoShifted (X : ℤ[X]) 3).eval 1 = 3 := by
    unfold hankelTwoShifted
    rw [← coe_evalRingHom, RingHom.map_det, Matrix.det_fin_three]
    simp [RingHom.mapMatrix_apply, hmap, v2, v3, v4, v5, v6]
  have hf : (fPrinted (X : ℤ[X]) 3).eval 1 = 2 := by
    rw [fPrinted, if_pos (by norm_num), eval_finsetSum]
    simp only [eval_pow, eval_X, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : ((Finset.Icc 1 3).filter (fun k => k % 3 ≠ 1)).card = 2 := by decide
    rw [hcard]
    norm_num
  have h1 := congrArg (eval (1 : ℤ)) hc
  rw [hdet, eval_mul, eval_pow, eval_X, one_pow, one_mul, hf] at h1
  norm_num at h1

#print axioms claim
#print axioms result

end D5.S0.Certificates.OhScrimshawQMotzkinHankelRefutation
