/- GID: D5/S3/Arith/Congruence/ReflectedRows/KurkovWeightedEntringerDivisibility
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/ReflectedRows/KurkovWeightedEntringerDivisibility
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.RingTheory.Binomial]
   utility: none
   digest: Reflected polynomial rows for the modified Entringer triangle of OEIS A386363. -/

import D5.S3.VertexAlgebra.Analysis.IntegerNewton
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.Basic

/-!
Reflected row extensions, with denominator cancellation before modular reduction.

admission_basis: open-problem-resolution (#31218).
proof_shape: triangle: content (the source recursion); a: bind-only (consumed by result);
result: content. The live new inference constructs integral row extensions, identifies
source interior values, and proves the pointwise all-modulus row transfer E_shift.
No helper is an independent open-problem result or a separate admission witness.
The sole direct frozen theorem supplier is
D5/S3/VertexAlgebra/Analysis/IntegerNewton.int_newton_of_fwdDiff_iter_eq_zero,
module statement_id sha256:9b6a04e2c8ddf2b06b173b77c64a5f485394d4901052055670b2f498ffd73027.
It is applied directly in S_difference and factorial_integral. The remaining
external suppliers are the pinned Mathlib imports. No third-party code is transplanted.
-/

set_option autoImplicit false
noncomputable section
open Finset Polynomial Function

namespace D5.S3.Arith.Congruence.ReflectedRows.KurkovWeightedEntringerDivisibility

/-- The literal source triangle; values beyond the row are auxiliary. -/
def triangle : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | _n + 1, 0 => 0
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
  have hN : (r : ℤ) + 1 + 2 - 1 = (r : ℤ) + 2 := by ring
  have hX : ((r : ℤ) + 1 + 2 - x : ℤ) = (r : ℤ) + 3 - x := by ring
  rw [hN, hX]
  ring

private def rowPoly (r : ℕ) : ℤ[X] := Classical.choose (P_integral r)

private theorem rowPoly_cast_eval (r : ℕ) (x : ℤ) :
    (((rowPoly r).eval x : ℤ) : ℚ) = (P r).eval (x : ℚ) := by
  have h := Classical.choose_spec (P_integral r)
  rw [← h, eval_intCast_map]
  rfl

private theorem rowPoly_anchor (r : ℕ) : (rowPoly r).eval 1 = (a (r + 1) : ℤ) := by
  have h := P_anchor r
  have hc := rowPoly_cast_eval r 1
  norm_num only [Int.cast_one] at hc
  rw [← hc] at h
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
        have h1 : r + 2 - 1 = r + 1 := by omega
        have h2 : r + 2 - (j + 1) = r + 1 - j := by omega
        simpa only [h1, h2, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using triangle.eq_4 (r + 2) j
      rw [hs]
      push_cast
      linear_combination he

private theorem rowPoly_diagonal (r : ℕ) :
    (rowPoly r).eval (r + 1 : ℤ) = (a (r + 2) : ℤ) := by
  rw [triangle_last]
  exact_mod_cast rowPoly_interior r (r + 1) (by omega) le_rfl

private def E (d r : ℕ) (x : ℤ) : ZMod d :=
  (rowPoly r).eval₂ (Int.castRingHom (ZMod d)) (x : ZMod d)

private theorem E_period (d r : ℕ) (x : ℤ) : E d r (x + d) = E d r x := by
  simp only [E, Int.cast_add, Int.cast_natCast, ZMod.natCast_self, add_zero]

private theorem E_cast (d r : ℕ) (x : ℤ) :
    E d r x = (((rowPoly r).eval x : ℤ) : ZMod d) :=
  eval₂_at_apply (Int.castRingHom (ZMod d)) x

private theorem E_anchor (d r : ℕ) : E d r 1 = (a (r + 1) : ZMod d) := by
  rw [E_cast, rowPoly_anchor]
  simp only [Int.cast_natCast]

private theorem E_diagonal (d r : ℕ) : E d r (r + 1) = (a (r + 2) : ZMod d) := by
  rw [E_cast, rowPoly_diagonal]
  simp only [Int.cast_natCast]

private theorem E_difference (d r : ℕ) (x : ℤ) :
    E d (r + 1) x - E d (r + 1) (x - 1) =
      (r + 1 : ZMod d) * E d r ((r : ℤ) + 3 - x) := by
  have h := congrArg (Int.castRingHom (ZMod d)) (rowPoly_difference r x)
  simp only [E_cast]
  simpa using h

private theorem integer_difference_ext {V : Type*} [AddCommGroup V] (f g : ℤ → V)
    (ha : f 1 = g 1)
    (hd : ∀ x, f x - f (x - 1) = g x - g (x - 1)) : ∀ x, f x = g x := by
  have h0 : f 0 = g 0 := by
    have h := hd 1
    norm_num only [sub_self] at h
    rw [ha] at h
    exact sub_right_inj.mp h
  intro x
  refine Int.induction_on x h0 ?_ ?_
  · intro i hi
    have h := hd (i + 1)
    rw [show (i : ℤ) + 1 - 1 = i by ring, hi] at h
    exact sub_left_inj.mp h
  · intro i hi
    have h := hd (-(i : ℤ))
    rw [hi] at h
    exact sub_right_inj.mp h

private theorem E_shift (d : ℕ) (hd : 0 < d) (r : ℕ) (x : ℤ) :
    E d (r + d) x = (a (d + 1) : ZMod d) * E d r x := by
  induction r generalizing x with
  | zero =>
    have he (y : ℤ) : E d d y - E d d (y - 1) = 0 := by
      obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
      simpa [ZMod.natCast_self] using E_difference (t + 1) t y
    have hz (y : ℤ) : E d 0 y = 1 := by simp [E, rowPoly_zero]
    simp only [Nat.zero_add]
    rw [hz, mul_one]
    apply integer_difference_ext (fun y => E d d y) (fun _ => (a (d + 1) : ZMod d))
    · exact E_anchor d d
    · intro y
      rw [he, sub_self]
  | succ r ih =>
    have ha : E d (r + 1 + d) 1 = (a (d + 1) : ZMod d) * E d (r + 1) 1 := by
      calc
        _ = (a (r + d + 2) : ZMod d) := by rw [E_anchor]; congr 2 <;> omega
        _ = E d (r + d) ((r : ℤ) + 1 + d) := by
          convert (E_diagonal d (r + d)).symm using 1 <;> push_cast <;> congr 1 <;> ring
        _ = (a (d + 1) : ZMod d) * E d r ((r : ℤ) + 1 + d) := ih _
        _ = (a (d + 1) : ZMod d) * E d r ((r : ℤ) + 1) := by rw [E_period]
        _ = _ := by rw [E_diagonal, E_anchor]
    apply integer_difference_ext (fun y => E d (r + 1 + d) y)
      (fun y => (a (d + 1) : ZMod d) * E d (r + 1) y) ha
    intro y
    have hs : r + 1 + d = (r + d) + 1 := by omega
    rw [hs, E_difference, ih, ← mul_sub, E_difference]
    push_cast
    rw [ZMod.natCast_self, add_zero]
    have hx : (r : ℤ) + d + 3 - y = ((r : ℤ) + 3 - y) + d := by ring
    rw [hx, E_period]
    ring

private theorem sequence_shift (d n : ℕ) (hd : 0 < d) (hn : 0 < n) :
    (a (n + d) : ZMod d) = (a (d + 1) : ZMod d) * (a n : ZMod d) := by
  by_cases h1 : n = 1
  · subst n
    simp [a, triangle, Nat.add_comm]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 2 ≤ n)
  have h := E_shift d hd r ((r : ℤ) + 1 + d)
  rw [E_period d r] at h
  have hl : E d (r + d) ((r : ℤ) + 1 + d) = (a (2 + r + d) : ZMod d) := by
    have hx : (r : ℤ) + 1 + d = ((r + d : ℕ) : ℤ) + 1 := by push_cast; ring
    rw [hx, E_diagonal]
    congr 2 <;> omega
  rw [hl, E_diagonal] at h
  simpa only [Nat.add_comm 2 r] using h

private theorem divisor_propagation (k m d : ℕ) (hd : 0 < d) (h : d ∣ a k) :
    d ∣ a (k + m * d) := by
  by_cases hk : k = 0
  · subst k
    have hd1 : d = 1 := Nat.dvd_one.mp (by simpa [a, triangle] using h)
    simp [hd1]
  induction m with
  | zero => simpa using h
  | succ m ih =>
    apply (ZMod.natCast_eq_zero_iff _ d).mp
    have hs := sequence_shift d (k + m * d) hd (by omega)
    have hz := (ZMod.natCast_eq_zero_iff _ d).mpr ih
    rw [hz, mul_zero] at hs
    simpa only [Nat.succ_mul, Nat.add_assoc] using hs

private theorem triangle_ge_first (n k : ℕ) (hk : 1 ≤ k) :
    triangle (n + 1) 1 ≤ triangle (n + 1) k := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => rfl
    | succ k =>
      rw [triangle.eq_4]
      exact (ih (by omega)).trans (Nat.le_add_right _ _)

private theorem a_positive (n : ℕ) : 0 < a n := by
  induction n with
  | zero => norm_num [a, triangle]
  | succ n ih =>
    have h := triangle_ge_first n (n + 1) (by omega)
    have h' : a n ≤ a (n + 1) := by simpa only [a, triangle.eq_3] using h
    exact ih.trans_le h'

/-- Conjecture 1, including its stated particular consequence. The positive
integer modulus is converted to a natural only in the nonnegative index. -/
theorem result :
    (∀ (k m : ℕ) (d : ℤ), 0 < d → d ∣ (a k : ℤ) →
      d ∣ (a (k + m * d.toNat) : ℤ)) ∧
    (∀ k m : ℕ, a k ∣ a (k + m * a k)) := by
  constructor
  · intro k m d hd h
    have hd' : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hd.le
    have hn : d.toNat ∣ a k := by exact_mod_cast (hd' ▸ h)
    have hp := divisor_propagation k m d.toNat (by omega) hn
    rw [← hd']
    exact_mod_cast hp
  · intro k m
    exact divisor_propagation k m (a k) (a_positive k) (dvd_refl _)

#print axioms result


end D5.S3.Arith.Congruence.ReflectedRows.KurkovWeightedEntringerDivisibility
