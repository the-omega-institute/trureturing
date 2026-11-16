/- GID: D5/S0/Computability/Diophantine/IntegerToRational
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A finite polynomial definition of the integers gives a uniform integer-to-rational solvability compiler. -/

import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic

/-! The conditional construction of UPPM_RG_002, Theorem 3.1. The defining
polynomial is a premise, not a constructed solution of the integer-definition
problem. Neither integer H10 undecidability nor the arithmetic premises of
ZInQ.FrozenTarget are asserted here. See local preregistration #31217. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Computability.Diophantine.IntegerToRational

open MvPolynomial

/-- The entire integer-definition clause, with all witnesses rational. -/
def DefinesIntegers {m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℤ) : Prop :=
  ∀ q : ℚ, (∃ w : Fin m → ℚ, eval₂ (Int.castRingHom ℚ) (Fin.cons q w) P = 0) ↔
    ∃ z : ℤ, (z : ℚ) = q

/-- Row-major finite indexing: coordinate `(i,j)` has number `j+(m+1)*i`. -/
def coordinate {n m : ℕ} (i : Fin n) (j : Fin (m + 1)) : Fin (n * (m + 1)) :=
  finProdFinEquiv (i, j)

/-- Each original variable is the first coordinate of its own witness block. -/
def original {n m : ℕ} (i : Fin n) : Fin (n * (m + 1)) := coordinate i 0

/-- One polynomial over integers, evaluated at one joint assignment. -/
noncomputable def compile {n m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℤ)
    (f : MvPolynomial (Fin n) ℤ) : MvPolynomial (Fin (n * (m + 1))) ℤ :=
  let rows : Fin (n + 1) → MvPolynomial (Fin (n * (m + 1))) ℤ :=
    Fin.cons (rename original f) (fun i => rename (coordinate i) P)
  ∑ k : Fin (n + 1), (rows k) ^ 2

private theorem compile_zero_iff {n m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℤ)
    (f : MvPolynomial (Fin n) ℤ) (x : Fin (n * (m + 1)) → ℚ) :
    eval₂ (Int.castRingHom ℚ) x (compile P f) = 0 ↔
      eval₂ (Int.castRingHom ℚ) (x ∘ original) f = 0 ∧
      ∀ i : Fin n, eval₂ (Int.castRingHom ℚ) (x ∘ coordinate i) P = 0 := by
  rw [compile, eval₂_sum]
  simp only [eval₂_pow]
  rw [Finset.sum_sq_eq_zero_iff]
  simp only [Finset.mem_univ, forall_true_left]
  constructor
  · intro h
    constructor
    · simpa only [Fin.cons_zero, eval₂_rename] using h 0
    · intro i
      simpa only [Fin.cons_succ, eval₂_rename] using h i.succ
  · rintro ⟨hf, hP⟩ k
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa only [Fin.cons_zero, eval₂_rename] using hf
    · simpa only [Fin.cons_succ, eval₂_rename] using hP i

/-- For every finite input dimension, rational solvability of the compiled
polynomial is exactly integer solvability of the input polynomial. -/
theorem solvability {n m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℤ)
    (hP : DefinesIntegers P) (f : MvPolynomial (Fin n) ℤ) :
    (∃ x : Fin (n * (m + 1)) → ℚ, eval₂ (Int.castRingHom ℚ) x (compile P f) = 0) ↔
      ∃ z : Fin n → ℤ, eval z f = 0 := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hf, hw⟩ := (compile_zero_iff P f x).mp hx
    have hz : ∀ i : Fin n, ∃ z : ℤ, (z : ℚ) = x (original i) := by
      intro i
      apply (hP (x (original i))).mp
      refine ⟨fun j => x (coordinate i j.succ), ?_⟩
      convert hw i using 1
      congr 1
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    choose z hz using hz
    refine ⟨z, Rat.intCast_injective ?_⟩
    have heq : (fun i => (z i : ℚ)) = x ∘ original := by
      funext i
      exact hz i
    have hzc : eval₂ (Int.castRingHom ℚ) (fun i => (z i : ℚ)) f = 0 := by
      rw [heq]
      exact hf
    have hc := MvPolynomial.eval₂_comp (Int.castRingHom ℚ) z f
    change (Int.castRingHom ℚ) (eval z f) = 0
    calc
      (Int.castRingHom ℚ) (eval z f) =
          eval₂ (Int.castRingHom ℚ) (⇑(Int.castRingHom ℚ) ∘ z) f := hc
      _ = eval₂ (Int.castRingHom ℚ) (fun i => (z i : ℚ)) f := by
        rfl
      _ = 0 := hzc
  · rintro ⟨z, hz⟩
    have hw : ∀ i : Fin n, ∃ w : Fin m → ℚ,
        eval₂ (Int.castRingHom ℚ) (Fin.cons (z i : ℚ) w) P = 0 := by
      intro i
      exact (hP (z i)).mpr ⟨z i, rfl⟩
    choose w hw using hw
    let y : Fin n × Fin (m + 1) → ℚ := fun ij =>
      (Fin.cons (z ij.1 : ℚ) (w ij.1) : Fin (m + 1) → ℚ) ij.2
    let x : Fin (n * (m + 1)) → ℚ := y ∘ finProdFinEquiv.symm
    refine ⟨x, (compile_zero_iff P f x).mpr ⟨?_, ?_⟩⟩
    · have hcast := congrArg (Int.castRingHom ℚ) hz
      rw [eval₂_comp] at hcast
      convert hcast using 1
      simp only [Function.comp_def, x, y, original, coordinate,
        Equiv.symm_apply_apply, Fin.cons_zero]
      rfl
    · intro i
      convert hw i using 1
      congr 1
      funext j
      simp only [Function.comp_def, x, y, coordinate, Equiv.symm_apply_apply]

end D5.S0.Computability.Diophantine.IntegerToRational
