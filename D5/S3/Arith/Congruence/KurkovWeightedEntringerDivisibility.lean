/- GID: D5/S3/Arith/Congruence/KurkovWeightedEntringerDivisibility
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/KurkovWeightedEntringerDivisibility
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.RingTheory.Binomial]
   utility: none
   digest: Reflected polynomial rows for the modified Entringer triangle of OEIS A386363. -/

import D5.S3.VertexAlgebra.Analysis.IntegerNewton
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.Basic

/-! Reflected row extensions, with denominator cancellation before modular reduction. -/

set_option autoImplicit false
noncomputable section
open Finset Polynomial Function

namespace D5.S3.Arith.Congruence.KurkovWeightedEntringerDivisibility

/-- The literal source triangle; values beyond the row are auxiliary. -/
def triangle : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, 0 => 0
  | n + 1, 1 => triangle n n
  | n + 1, k + 2 => triangle (n + 1) (k + 1) + (n - 1) * triangle n (n - (k + 1))
termination_by n k => (n, k)

/-- A386381, with its index-zero term equal to one. -/
def a (n : ℕ) : ℕ := triangle n n

private def B (j : ℕ) : ℚ[X] := (j.factorial : ℚ)⁻¹ • descPochhammer ℚ j

private theorem B_eval (j : ℕ) (x : ℤ) :
    (B j).eval (x : ℚ) = (Ring.choose x j : ℤ) := by
  rw [B, eval_smul, ← descPochhammer_eval_cast]
  rw [Polynomial.eval_eq_smeval, Ring.descPochhammer_eq_factorial_smul_choose]
  simp only [nsmul_eq_mul, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
  field_simp

private theorem B_degree (j : ℕ) : (B j).natDegree ≤ j := by
  exact (natDegree_smul_le _ _).trans (by rw [descPochhammer_natDegree])

private theorem ext_int {p q : ℚ[X]} (h : ∀ z : ℤ, p.eval (z : ℚ) = q.eval (z : ℚ)) : p = q := by
  apply eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Int.cast_injective (α := ℚ))).mono
  rintro _ ⟨z, rfl⟩
  exact h z

private theorem diff_vanish (p : ℚ[X]) (r : ℕ) (hr : p.natDegree < r) :
    (fwdDiff (1 : ℤ))^[r] (fun z : ℤ => p.eval (z : ℚ)) = 0 := by
  funext z
  have h := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hr) (z : ℚ)
  rw [fwdDiff_iter_eq_sum_shift] at h ⊢
  simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one, nsmul_eq_mul, mul_one,
    Pi.zero_apply] using h

private def S (N : ℤ) (p : ℚ[X]) : ℚ[X] :=
  let g := p.comp (C (N : ℚ) - X)
  ∑ j ∈ range (g.natDegree + 1),
    C (((fwdDiff (1 : ℤ))^[j] (fun z : ℤ => g.eval (z : ℚ))) 0) *
      ((B (j + 1)).comp (X + 1) - C ((B (j + 1)).eval 2))

private theorem S_anchor (N : ℤ) (p : ℚ[X]) : (S N p).eval 1 = 0 := by
  simp [S, eval_finsetSum, show (1 : ℚ) + 1 = 2 by norm_num]

private theorem S_difference (N x : ℤ) (p : ℚ[X]) :
    (S N p).eval (x : ℚ) - (S N p).eval ((x - 1 : ℤ) : ℚ) =
      p.eval ((N - x : ℤ) : ℚ) := by
  let g := p.comp (C (N : ℚ) - X)
  have hn := D5.S3.VertexAlgebra.Analysis.IntegerNewton.int_newton_of_fwdDiff_iter_eq_zero
    (fun z : ℤ => g.eval (z : ℚ)) (g.natDegree + 1)
    (diff_vanish g _ (Nat.lt_succ_self _)) x
  have hb (j : ℕ) :
      ((B (j + 1)).comp (X + 1) - C ((B (j + 1)).eval 2)).eval (x : ℚ) -
      ((B (j + 1)).comp (X + 1) - C ((B (j + 1)).eval 2)).eval ((x - 1 : ℤ) : ℚ) =
        (Ring.choose x j : ℤ) := by
    simp only [eval_sub, eval_comp, eval_add, eval_X, eval_one, eval_C]
    rw [show (x : ℚ) + 1 = ((x + 1 : ℤ) : ℚ) by push_cast; rfl,
      show ((x - 1 : ℤ) : ℚ) + 1 = (x : ℚ) by push_cast; ring,
      B_eval, B_eval, Ring.choose_succ_succ]
    push_cast
    ring
  dsimp only [S]
  simp only [eval_finsetSum, eval_mul, eval_C, ← sum_sub_distrib, ← mul_sub, hb]
  simpa [g, zsmul_eq_mul, mul_comm] using hn.symm

private theorem S_degree (N : ℤ) (p : ℚ[X]) : (S N p).natDegree ≤ p.natDegree + 1 := by
  dsimp only [S]
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hg : (p.comp (C (N : ℚ) - X)).natDegree ≤ p.natDegree := by
    have hl : (C (N : ℚ) - X).natDegree ≤ 1 := by
      simpa using (natDegree_sub_le (C (N : ℚ)) X)
    exact natDegree_comp_le.trans ((Nat.mul_le_mul_left _ hl).trans (by simp))
  have hj' : j + 1 ≤ p.natDegree + 1 := by have := mem_range.mp hj; omega
  apply (natDegree_C_mul_le _ _).trans
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact (natDegree_comp_le.trans (by simpa using B_degree (j + 1))).trans hj'
  · simp

private def IntegerValued (p : ℚ[X]) : Prop :=
  ∃ f : ℤ → ℤ, ∀ z : ℤ, p.eval (z : ℚ) = (f z : ℚ)

private theorem diff_cast (f : ℤ → ℤ) (j : ℕ) (x : ℤ) :
    ((fwdDiff (1 : ℤ))^[j] (fun z : ℤ => (f z : ℚ))) x =
      (((fwdDiff (1 : ℤ))^[j] f) x : ℚ) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    simp only [iterate_succ_apply', fwdDiff, ih, Int.cast_sub]

private theorem S_integerValued (N : ℤ) {p : ℚ[X]} (hp : IntegerValued p) :
    IntegerValued (S N p) := by
  obtain ⟨f, hf⟩ := hp
  let g := p.comp (C (N : ℚ) - X)
  let F : ℤ → ℤ := fun z => f (N - z)
  have hF : (fun z : ℤ => g.eval (z : ℚ)) = fun z : ℤ => (F z : ℚ) := by
    funext z
    simpa [g, F] using hf (N - z)
  refine ⟨fun x => ∑ j ∈ range (g.natDegree + 1),
    ((fwdDiff (1 : ℤ))^[j] F) 0 *
      (Ring.choose (x + 1) (j + 1) - Ring.choose (2 : ℤ) (j + 1)), ?_⟩
  intro x
  dsimp only [S]
  change (∑ j ∈ range (g.natDegree + 1),
    C (((fwdDiff (1 : ℤ))^[j] (fun z : ℤ => g.eval (z : ℚ))) 0) *
      ((B (j + 1)).comp (X + 1) - C ((B (j + 1)).eval 2))).eval (x : ℚ) = _
  simp only [eval_finsetSum, eval_mul, eval_C, eval_sub, eval_comp, eval_add,
    eval_X, eval_one, hF, diff_cast, Int.cast_sum, Int.cast_mul, Int.cast_sub]
  apply sum_congr rfl
  intro j hj
  rw [show (x : ℚ) + 1 = ((x + 1 : ℤ) : ℚ) by push_cast; rfl, B_eval]
  have h2 := B_eval (j + 1) 2
  norm_num only [Int.cast_ofNat] at h2
  rw [h2]

private def Integral (p : ℚ[X]) : Prop :=
  ∃ q : ℤ[X], q.map (Int.castRingHom ℚ) = p

private theorem factorial_integral (j : ℕ) {p : ℚ[X]}
    (hd : p.natDegree ≤ j) (hp : IntegerValued p) :
    Integral ((j.factorial : ℚ) • p) := by
  obtain ⟨f, hf⟩ := hp
  have hfun : (fun z : ℤ => p.eval (z : ℚ)) = fun z : ℤ => (f z : ℚ) := funext hf
  refine ⟨∑ i ∈ range (j + 1),
    C ((((fwdDiff (1 : ℤ))^[i] f) 0) * (j.factorial / i.factorial : ℕ)) *
      descPochhammer ℤ i, ?_⟩
  apply ext_int
  intro z
  have hn := D5.S3.VertexAlgebra.Analysis.IntegerNewton.int_newton_of_fwdDiff_iter_eq_zero
    (fun z : ℤ => p.eval (z : ℚ)) (j + 1)
    (diff_vanish p _ (by omega)) z
  rw [hfun] at hn
  simp only [diff_cast, zsmul_eq_mul] at hn
  simp only [Polynomial.map_sum, Polynomial.map_mul, map_C, descPochhammer_map,
    eval_finsetSum, eval_mul, eval_C, Int.coe_castRingHom, Int.cast_mul,
    Int.cast_natCast, eval_smul, smul_eq_mul]
  rw [hn, mul_sum]
  apply sum_congr rfl
  intro i hi
  have hi' : i ≤ j := by have := mem_range.mp hi; omega
  have he : (j.factorial / i.factorial : ℕ) * i.factorial = j.factorial :=
    Nat.div_mul_cancel (Nat.factorial_dvd_factorial hi')
  have hc : ((j.factorial / i.factorial : ℕ) : ℚ) * i.factorial = j.factorial := by
    exact_mod_cast he
  rw [← descPochhammer_eval_cast, Polynomial.eval_eq_smeval,
    Ring.descPochhammer_eq_factorial_smul_choose]
  simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  calc
    _ = (((fwdDiff (1 : ℤ))^[i] f) 0 : ℚ) *
      (((j.factorial / i.factorial : ℕ) : ℚ) * i.factorial) * (Ring.choose z i : ℤ) := by ring
    _ = _ := by rw [hc]; ring

private def Q (N : ℤ) : ℕ → ℚ[X]
  | 0 => 1
  | j + 1 => S N (Q (N - 1) j)

private theorem Q_degree (N : ℤ) (j : ℕ) : (Q N j).natDegree ≤ j := by
  induction j generalizing N with
  | zero => simp [Q]
  | succ j ih => exact (S_degree N _).trans (Nat.succ_le_succ (ih (N - 1)))

private theorem Q_integerValued (N : ℤ) (j : ℕ) : IntegerValued (Q N j) := by
  induction j generalizing N with
  | zero => exact ⟨fun _ => 1, by simp [Q]⟩
  | succ j ih => exact S_integerValued N (ih (N - 1))

private theorem Q_integral (N : ℤ) (j : ℕ) :
    Integral ((j.factorial : ℚ) • Q N j) :=
  factorial_integral j (Q_degree N j) (Q_integerValued N j)

private def P (r : ℕ) : ℚ[X] :=
  ∑ j ∈ range (r + 1),
    ((r.descFactorial j * a (r + 1 - j) : ℕ) : ℚ) • Q (r + 2) j

private theorem P_integral (r : ℕ) : Integral (P r) := by
  let q := fun j => Classical.choose (Q_integral (r + 2) j)
  have hq (j : ℕ) : (q j).map (Int.castRingHom ℚ) = (j.factorial : ℚ) • Q (r + 2) j :=
    Classical.choose_spec (Q_integral (r + 2) j)
  refine ⟨∑ j ∈ range (r + 1), C ((r.choose j * a (r + 1 - j) : ℕ) : ℤ) * q j, ?_⟩
  simp only [P, Polynomial.map_sum]
  apply sum_congr rfl
  intro j hj
  rw [Polynomial.map_mul, map_C, hq, ← smul_eq_C_mul, smul_smul]
  congr 1
  simp only [Int.coe_castRingHom]
  push_cast
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

private theorem P_anchor (r : ℕ) : (P r).eval 1 = (a (r + 1) : ℚ) := by
  rw [P, sum_range_succ']
  simp [Q, eval_finsetSum, S_anchor]

private theorem P_difference (r : ℕ) (x : ℤ) :
    (P (r + 1)).eval (x : ℚ) - (P (r + 1)).eval ((x - 1 : ℤ) : ℚ) =
      (r + 1 : ℚ) * (P r).eval (((r : ℤ) + 3 - x : ℤ) : ℚ) := by
  rw [P, sum_range_succ']
  simp only [eval_add, eval_smul, smul_eq_mul, Q, eval_one,
    Nat.descFactorial_zero, one_mul, Nat.sub_zero, mul_one]
  rw [show ∀ u v c : ℚ, (u + c) - (v + c) = u - v by intros; ring]
  simp only [eval_finsetSum, eval_smul, smul_eq_mul, ← sum_sub_distrib, ← mul_sub, S_difference]
  simp only [P, eval_finsetSum, eval_smul, smul_eq_mul, mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [Nat.succ_descFactorial_succ]
  have hn : r + 1 + 1 - (j + 1) = r + 1 - j := by omega
  simp only [hn, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hN : (r : ℤ) + 1 + 2 - 1 = (r : ℤ) + 2 := by push_cast; ring
  have hX : ((r : ℤ) + 1 + 2 - x : ℤ) = (r : ℤ) + 3 - x := by push_cast; ring
  rw [hN, hX]
  ring

private def rowPoly (r : ℕ) : ℤ[X] := Classical.choose (P_integral r)

private theorem rowPoly_cast_eval (r : ℕ) (x : ℤ) :
    ((rowPoly r).eval x : ℚ) = (P r).eval (x : ℚ) := by
  have h := Classical.choose_spec (P_integral r)
  rw [← h, eval_intCast_map]
  rfl

private theorem rowPoly_anchor (r : ℕ) : (rowPoly r).eval 1 = (a (r + 1) : ℤ) := by
  have h := P_anchor r
  rw [← rowPoly_cast_eval r 1] at h
  exact_mod_cast h

private theorem rowPoly_difference (r : ℕ) (x : ℤ) :
    (rowPoly (r + 1)).eval x - (rowPoly (r + 1)).eval (x - 1) =
      (r + 1 : ℤ) * (rowPoly r).eval ((r : ℤ) + 3 - x) := by
  have h := P_difference r x
  simp only [← rowPoly_cast_eval] at h
  exact_mod_cast h

private theorem rowPoly_zero (x : ℤ) : (rowPoly 0).eval x = 1 := by
  have h := rowPoly_cast_eval 0 x
  norm_num [P, Q, a, triangle] at h
  exact_mod_cast h

private theorem triangle_last (r : ℕ) : a (r + 2) = triangle (r + 2) (r + 1) := by
  simp [a, triangle]

private theorem rowPoly_interior (r k : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r + 1) :
    (rowPoly r).eval (k : ℤ) = (triangle (r + 2) k : ℤ) := by
  induction r generalizing k with
  | zero =>
    have : k = 1 := by omega
    subst k
    norm_num [rowPoly_zero, triangle]
  | succ r ih =>
    induction k using Nat.strong_induction_on with
    | h k ik =>
      by_cases h1 : k = 1
      · subst k
        simpa [a, triangle] using rowPoly_anchor (r + 1)
      have hk2 : 2 ≤ k := by omega
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk2
      have he := rowPoly_difference r (2 + j)
      have hp := ik (1 + j) (by omega) (by omega) (by omega)
      have hq := ih (r + 1 - j) (by omega) (by omega)
      have hx : (r : ℤ) + 3 - (2 + j) = ((r + 1 - j : ℕ) : ℤ) := by
        have hj : j ≤ r + 1 := by omega
        rw [Nat.cast_sub hj]
        push_cast
        ring
      rw [hx, show (2 : ℤ) + j - 1 = ((1 + j : ℕ) : ℤ) by push_cast; ring,
        hp, hq] at he
      have hs : triangle (r + 1 + 2) (2 + j) =
          triangle (r + 1 + 2) (1 + j) + (r + 1) * triangle (r + 2) (r + 1 - j) := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_sub_cancel,
          Nat.add_sub_add_right] using (triangle.eq_4 (r + 2) j)
      rw [hs]
      push_cast
      linear_combination he

private theorem rowPoly_diagonal (r : ℕ) :
    (rowPoly r).eval (r + 1 : ℤ) = (a (r + 2) : ℤ) := by
  rw [triangle_last]
  exact_mod_cast rowPoly_interior r (r + 1) (by omega) le_rfl

end D5.S3.Arith.Congruence.KurkovWeightedEntringerDivisibility
