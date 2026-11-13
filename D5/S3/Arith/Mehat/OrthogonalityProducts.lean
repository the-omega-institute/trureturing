/- GID: D5/S3/Arith/Mehat/OrthogonalityProducts
   generality: G
   mirror-B: D5/B/S3/Arith/Mehat/OrthogonalityProducts
   mirror-E: none
   anchors: [mathlib/module/Mathlib.Algebra.MvPolynomial.Funext]
   utility: none
   digest: Integer quaternion factors with distinct indexed squared-entry products. -/

import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Mehat.OrthogonalityProducts

open scoped BigOperators
open MvPolynomial Matrix

/-- The exact positive-`k` assertion of Mehat, Problem 9.2. -/
def Problem92 : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ (A : Fin k → Matrix (Fin 3) (Fin 3) ℤ) (gamma : Fin k → ℤ),
    (∀ i, gamma i ≠ 0 ∧ A i * (A i)ᵀ = gamma i • (1 : Matrix (Fin 3) (Fin 3) ℤ)) ∧
    Function.Injective (fun p : Fin k → Fin 3 × Fin 3 => ∏ i, (A i (p i).1 (p i).2) ^ 2)

/-- The exact unbounded order assertion of Mehat, Problem 9.1. -/
def Problem91 : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ (M : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℤ) (gamma : ℤ),
    gamma ≠ 0 ∧ M * Mᵀ = gamma • (1 : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℤ) ∧
    (∑ i, M i i ^ 2) = gamma ∧ (∑ i, M i i.rev ^ 2) = gamma ∧
    Function.Injective (fun p : Fin (3 ^ k) × Fin (3 ^ k) => (M p.1 p.2) ^ 2)

/-- Quaternion parametrization of the nine entries, with no diagonal requirement on a factor. -/
def quaternionMatrix {R : Type*} [CommRing R] (a : Fin 4 → R) : Matrix (Fin 3) (Fin 3) R :=
  !![a 0 ^ 2 + a 1 ^ 2 - a 2 ^ 2 - a 3 ^ 2, 2 * (a 1 * a 2 - a 0 * a 3), 2 * (a 1 * a 3 + a 0 * a 2);
     2 * (a 1 * a 2 + a 0 * a 3), a 0 ^ 2 - a 1 ^ 2 + a 2 ^ 2 - a 3 ^ 2, 2 * (a 2 * a 3 - a 0 * a 1);
     2 * (a 1 * a 3 - a 0 * a 2), 2 * (a 2 * a 3 + a 0 * a 1), a 0 ^ 2 - a 1 ^ 2 - a 2 ^ 2 + a 3 ^ 2]

private noncomputable def entry (p : Fin 3 × Fin 3) : MvPolynomial (Fin 4) ℤ :=
  quaternionMatrix (fun i => X i) p.1 p.2

private theorem eval_entry (a : Fin 4 → ℤ) (p : Fin 3 × Fin 3) :
    eval a (entry p) = quaternionMatrix a p.1 p.2 := by
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> simp [entry, quaternionMatrix]

private theorem integer_nonzero_point {σ : Type*} (p : MvPolynomial σ ℤ) (hp : p ≠ 0) :
    ∃ a : σ → ℤ, eval a p ≠ 0 := by
  by_contra h
  apply hp
  apply MvPolynomial.funext
  intro a
  simpa using not_not.mp (fun ha => h ⟨a, ha⟩)


private def separatingPoint (p q : Fin 3 × Fin 3) : Fin 4 → ℤ :=
  (![![![0, 0, 0, 0], ![-1, -1, -1, 1], ![-1, -1, -1, -1], ![-1, -1, -1, -1], ![-1, 0, -1, 0], ![-1, -1, -1, 1], ![-1, -1, -1, 1], ![-1, -1, -1, -1], ![-1, 0, 0, -1]] ,
     ![![-1, -1, 0, 0], ![0, 0, 0, 0], ![-1, -1, -1, -1], ![-1, -1, -1, -1], ![-1, 0, -1, 0], ![-1, -1, 0, 0], ![-1, 0, -1, 0], ![-1, -1, -1, -1], ![-1, 0, 0, 0]] ,
     ![![-1, -1, 0, 0], ![-1, -1, -1, 1], ![0, 0, 0, 0], ![-1, 0, 0, -1], ![-1, 0, 0, 0], ![-1, -1, -1, 1], ![-1, -1, -1, 1], ![-1, -1, 0, 0], ![-1, 0, 0, -1]] ,
     ![![-1, -1, 0, 0], ![-1, -1, -1, 1], ![-1, 0, -1, 0], ![0, 0, 0, 0], ![-1, 0, -1, 0], ![-1, -1, -1, 1], ![-1, -1, -1, 1], ![-1, -1, 0, 0], ![-1, 0, 0, 0]] ,
     ![![-1, -1, 0, 0], ![-1, -1, -1, 1], ![-1, -1, -1, -1], ![-1, -1, -1, -1], ![0, 0, 0, 0], ![-1, -1, -1, 1], ![-1, -1, -1, 1], ![-1, -1, -1, -1], ![-1, 0, 0, -1]] ,
     ![![-1, 0, 0, 0], ![-1, 0, 0, -1], ![-1, -1, -1, -1], ![-1, -1, -1, -1], ![-1, 0, -1, 0], ![0, 0, 0, 0], ![-1, 0, -1, 0], ![-1, -1, -1, -1], ![-1, 0, 0, -1]] ,
     ![![-1, -1, 0, 0], ![-1, 0, 0, -1], ![-1, -1, -1, -1], ![-1, -1, -1, -1], ![-1, 0, 0, 0], ![-1, -1, 0, 0], ![0, 0, 0, 0], ![-1, -1, -1, -1], ![-1, 0, 0, -1]] ,
     ![![-1, 0, 0, 0], ![-1, -1, -1, 1], ![-1, 0, -1, 0], ![-1, 0, 0, -1], ![-1, 0, -1, 0], ![-1, -1, -1, 1], ![-1, -1, -1, 1], ![0, 0, 0, 0], ![-1, 0, 0, -1]] ,
     ![![-1, -1, 0, 0], ![-1, -1, -1, 1], ![-1, -1, -1, -1], ![-1, -1, -1, -1], ![-1, 0, -1, 0], ![-1, -1, -1, 1], ![-1, -1, -1, 1], ![-1, -1, -1, -1], ![0, 0, 0, 0]]]) ⟨p.1.val * 3 + p.2.val, by omega⟩ ⟨q.1.val * 3 + q.2.val, by omega⟩

private theorem separatingPoint_spec (p q : Fin 3 × Fin 3) (hpq : p ≠ q) :
    quaternionMatrix (separatingPoint p q) p.1 p.2 = 0 ∧
    quaternionMatrix (separatingPoint p q) q.1 q.2 ≠ 0 := by
  revert p q
  decide

private theorem entry_nonzero_value (p : Fin 3 × Fin 3) :
    quaternionMatrix ![1, 2, 3, 4] p.1 p.2 ≠ (0 : ℤ) := by
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> norm_num [quaternionMatrix]

private theorem collision_ne_zero {T : Type*} (P : T → ℤ)
    (hP : ∀ t, P t ≠ 0) (hI : Function.Injective P)
    (a b : T × (Fin 3 × Fin 3)) (hab : a ≠ b) :
    C (P a.1) * entry a.2 ^ 2 - C (P b.1) * entry b.2 ^ 2 ≠ 0 := by
  intro h
  have he (x : Fin 4 → ℤ) :
      P a.1 * quaternionMatrix x a.2.1 a.2.2 ^ 2 =
      P b.1 * quaternionMatrix x b.2.1 b.2.2 ^ 2 := by
    have hh := congrArg (eval x) h
    simpa only [map_sub, map_mul, map_pow, eval_C, eval_entry, map_zero, sub_eq_zero] using hh
  by_cases hij : a.2 = b.2
  · have hx := he ![1,2,3,4]
    rw [hij] at hx
    have ht : a.1 = b.1 := hI (mul_right_cancel₀ (pow_ne_zero 2 (entry_nonzero_value b.2)) hx)
    exact hab (Prod.ext ht hij)
  · obtain ⟨ha,hb⟩ := separatingPoint_spec a.2 b.2 hij
    have hx := he (separatingPoint a.2 b.2)
    rw [ha, zero_pow (by decide), mul_zero] at hx
    exact (mul_ne_zero (hP _) (pow_ne_zero 2 hb)) hx.symm


private theorem extend_products {T : Type*} [Fintype T] (P : T → ℤ)
    (hP : ∀ t, P t ≠ 0) (hI : Function.Injective P) :
    ∃ x : Fin 4 → ℤ,
      (∀ e : Fin 3 × Fin 3, quaternionMatrix x e.1 e.2 ≠ 0) ∧
      Function.Injective (fun a : T × (Fin 3 × Fin 3) =>
        P a.1 * quaternionMatrix x a.2.1 a.2.2 ^ 2) := by
  classical
  let S := Finset.univ.filter (fun ab : (T × (Fin 3 × Fin 3)) × (T × (Fin 3 × Fin 3)) =>
    ab.1 ≠ ab.2)
  let F : MvPolynomial (Fin 4) ℤ := (∏ e : Fin 3 × Fin 3, entry e) *
    ∏ ab ∈ S, (C (P ab.1.1) * entry ab.1.2 ^ 2 - C (P ab.2.1) * entry ab.2.2 ^ 2)
  have hentry (e : Fin 3 × Fin 3) : entry e ≠ 0 := by
    intro h
    have hh := congrArg (eval ![1,2,3,4]) h
    exact entry_nonzero_value e (by simpa only [eval_entry, map_zero] using hh)
  have hF : F ≠ 0 := by
    apply mul_ne_zero
    · exact Finset.prod_ne_zero_iff.mpr (fun e _ => hentry e)
    · apply Finset.prod_ne_zero_iff.mpr
      intro ab hab
      exact collision_ne_zero P hP hI ab.1 ab.2 (Finset.mem_filter.mp hab).2
  obtain ⟨x,hx⟩ := integer_nonzero_point F hF
  have hx' : (∏ e : Fin 3 × Fin 3, quaternionMatrix x e.1 e.2) *
      (∏ ab ∈ S, (P ab.1.1 * quaternionMatrix x ab.1.2.1 ab.1.2.2 ^ 2 -
        P ab.2.1 * quaternionMatrix x ab.2.2.1 ab.2.2.2 ^ 2)) ≠ 0 := by
    simpa only [F, map_mul, map_prod, map_sub, map_pow, eval_C, eval_entry] using hx
  refine ⟨x, ?_, ?_⟩
  · exact fun e => Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hx').1 e (Finset.mem_univ e)
  · intro a b hab
    by_contra hne
    have hc := Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hx').2 (a,b)
      (show (a,b) ∈ S by simp [S,hne])
    exact hc (sub_eq_zero.mpr hab)


private theorem quaternion_orth (x : Fin 4 → ℤ) :
    quaternionMatrix x * (quaternionMatrix x)ᵀ =
      (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) ^ 2 •
        (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem quaternion_constant_ne_zero (x : Fin 4 → ℤ)
    (hx : ∀ e : Fin 3 × Fin 3, quaternionMatrix x e.1 e.2 ≠ 0) :
    (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) ^ 2 ≠ 0 := by
  apply pow_ne_zero
  intro h
  have h00 : x 0 ^ 2 + x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2 = 0 := by
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)]
  exact hx (0,0) (by simpa [quaternionMatrix] using h00)

private theorem factors_all (k : ℕ) :
    ∃ (A : Fin k → Matrix (Fin 3) (Fin 3) ℤ) (gamma : Fin k → ℤ),
      (∀ i, gamma i ≠ 0 ∧ A i * (A i)ᵀ = gamma i • (1 : Matrix (Fin 3) (Fin 3) ℤ)) ∧
      (∀ i r c, A i r c ≠ 0) ∧
      Function.Injective (fun p : Fin k → Fin 3 × Fin 3 => ∏ i, (A i (p i).1 (p i).2) ^ 2) := by
  induction k with
  | zero =>
    refine ⟨Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro p q _; exact Subsingleton.elim p q
  | succ k ih =>
    obtain ⟨A,gamma,horth,hne,hinj⟩ := ih
    let P := fun p : Fin k → Fin 3 × Fin 3 => ∏ i, (A i (p i).1 (p i).2) ^ 2
    have hP : ∀ p, P p ≠ 0 := by
      intro p
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero 2 (hne i _ _))
    obtain ⟨x,hx,hI⟩ := extend_products P hP hinj
    let g := (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) ^ 2
    refine ⟨Fin.cons (quaternionMatrix x) A, Fin.cons g gamma, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨quaternion_constant_ne_zero x hx, quaternion_orth x⟩
      · exact horth j
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · intro r c; exact hx (r,c)
      · exact hne j
    · intro p q hpq
      have hpair : ((fun i : Fin k => p i.succ), p 0) =
          ((fun i : Fin k => q i.succ), q 0) := by
        apply hI
        simpa only [P, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_comm] using hpq
      have htail := congrArg Prod.fst hpair
      have hhead := congrArg Prod.snd hpair
      funext i
      exact Fin.cases hhead (fun j => congrFun htail j) i

/-- Problem 9.2, with all positive `k` and every one of the `9^k` indexed choices. -/
theorem problem92 : Problem92 := by
  intro k _hk
  obtain ⟨A,gamma,horth,_hne,hinj⟩ := factors_all k
  exact ⟨A,gamma,horth,hinj⟩

end D5.S3.Arith.Mehat.OrthogonalityProducts
