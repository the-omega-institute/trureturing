/- GID: D5/S1/Recurrence/GallardoRahavandrainyCollatzLengthBound
   generality: I
   mirror-B: D5/B/S1/Recurrence/GallardoRahavandrainyCollatzLengthBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: A quadratic bound for binary-polynomial Collatz length. -/

/-
admission_basis: open-problem-resolution (#20129; Proved)
escape_witness: none (the module uses the open-problem-resolution basis).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20796.
Direct frozen dependencies: the declarations of
D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz used below.
The source formulas for evenTerm, rA and claim are retained; M, oddPart and
oddSeq are used at their original owner. Natural division is floor division.
evenTerm: proof_shape: bind-only; consumers: rA, rA_le_hit; escape_witness: none. Direct frozen dependencies: M, oddSeq.
rA: proof_shape: bind-only; consumers: claim, rA_le_hit, result; escape_witness: none. Direct frozen dependencies: M, oddSeq.
claim: proof_shape: bind-only; consumers: result (statement type); escape_witness: none. Direct frozen dependencies: M, oddSeq.
oddPart_data: proof_shape: bind-only; consumers: oddPart_odd, oddPart_degree, step_data; escape_witness: none. Direct frozen dependencies: oddPart, Dynamics.oddPart_factor, Dynamics.nonzero_eq_one.
oddPart_odd: proof_shape: bind-only; consumers: step_odd, oddSeq_hit; escape_witness: none. Direct frozen dependencies: oddPart, Dynamics.oddPart_factor, Dynamics.nonzero_eq_one.
oddPart_degree: proof_shape: bind-only; consumers: oddSeq_hit; escape_witness: none. Direct frozen dependencies: oddPart, Dynamics.oddPart_factor, Dynamics.nonzero_eq_one.
numerator_nonzero: proof_shape: bind-only; consumers: step_odd, step_data; escape_witness: none. Direct frozen dependencies: M, Dynamics.q_ne_zero, Dynamics.degree_q.
step_odd: proof_shape: bind-only; consumers: iterate_odd, plateau_escape; escape_witness: none. Direct frozen dependencies: M, oddPart, Dynamics.q_ne_zero, Dynamics.oddPart_factor, Dynamics.nonzero_eq_one, Dynamics.degree_q.
numerator_degree: proof_shape: bind-only; consumers: numerator_nonzero, step_data; escape_witness: none. Direct frozen dependencies: M, Dynamics.q_ne_zero, Dynamics.degree_q.
step_data: proof_shape: bind-only; consumers: step_degree, step_same_factor; escape_witness: none. Direct frozen dependencies: M, oddPart, Dynamics.nonzero_of_odd, Dynamics.q_ne_zero, Dynamics.oddPart_factor, Dynamics.nonzero_eq_one, Dynamics.degree_q.
step_degree: proof_shape: bind-only; consumers: plateau_escape; escape_witness: none. Direct frozen dependencies: M, oddPart, Dynamics.nonzero_of_odd, Dynamics.q_ne_zero, Dynamics.oddPart_factor, Dynamics.nonzero_eq_one, Dynamics.degree_q.
step_same_factor: proof_shape: bind-only; consumers: step_same_plateau; escape_witness: none. Direct frozen dependencies: M, oddPart, Dynamics.nonzero_of_odd, Dynamics.q_ne_zero, Dynamics.oddPart_factor, Dynamics.nonzero_eq_one, Dynamics.degree_q.
plateau: proof_shape: bind-only; consumers: plateau_bound, step_same_plateau, plateau_escape; escape_witness: none. Direct frozen dependencies: none.
plus_one_ne_zero: proof_shape: bind-only; consumers: plateau_positive, plateau_bound, step_same_plateau; escape_witness: none. Direct frozen dependencies: none.
positive_degree: proof_shape: bind-only; consumers: plateau_bound, step_same_plateau, plateau_escape, reaches_one; escape_witness: none. Direct frozen dependencies: Dynamics.eq_one_of_degree_zero.
plateau_positive: proof_shape: bind-only; consumers: plateau_escape; escape_witness: none. Direct frozen dependencies: none.
plateau_bound: proof_shape: bind-only; consumers: reaches_one; escape_witness: none. Direct frozen dependencies: Dynamics.eq_one_of_degree_zero.
step_same_plateau: proof_shape: bind-only; consumers: plateau_escape; escape_witness: none. Direct frozen dependencies: M, oddPart, Dynamics.nonzero_of_odd, Dynamics.q_ne_zero, Dynamics.oddPart_factor, Dynamics.nonzero_eq_one, Dynamics.degree_q, Dynamics.eq_one_of_degree_zero.
step: proof_shape: bind-only; consumers: plateau_escape, reaches_one; escape_witness: none. Direct frozen dependencies: M, oddPart.
iterate_odd: proof_shape: bind-only; consumers: reaches_one; escape_witness: none. Direct frozen dependencies: M, oddPart, Dynamics.q_ne_zero, Dynamics.oddPart_factor, Dynamics.nonzero_eq_one, Dynamics.degree_q.
plateau_escape: proof_shape: content; consumers: reaches_one; escape_witness: none. Direct frozen dependencies: M, oddPart, Dynamics.nonzero_of_odd, Dynamics.q_ne_zero, Dynamics.oddPart_factor, Dynamics.nonzero_eq_one, Dynamics.degree_q, Dynamics.eq_one_of_degree_zero.
square_budget_step: proof_shape: bind-only; consumers: reaches_one; escape_witness: none. Direct frozen dependencies: none.
reaches_one: proof_shape: content; consumers: oddSeq_hit; escape_witness: none. Direct frozen dependencies: M, oddPart, Dynamics.nonzero_of_odd, Dynamics.q_ne_zero, Dynamics.oddPart_factor, Dynamics.nonzero_eq_one, Dynamics.degree_q, Dynamics.eq_one_of_degree_zero.
step_one: proof_shape: bind-only; consumers: oddSeq_tail; escape_witness: none. Direct frozen dependencies: M, oddPart, Dynamics.oddPart_factor.
oddSeq_eq_iterate: proof_shape: bind-only; consumers: oddSeq_hit, oddSeq_tail; escape_witness: none. Direct frozen dependencies: M, oddSeq.eq_2, oddPart, oddSeq.
oddSeq_hit: proof_shape: content; consumers: rA_quadratic; escape_witness: none. Direct frozen dependencies: M, oddSeq.eq_2, oddPart, Dynamics.nonzero_of_odd, Dynamics.q_ne_zero, oddSeq, Dynamics.oddPart_factor, Dynamics.nonzero_eq_one, Dynamics.degree_q, Dynamics.eq_one_of_degree_zero.
oddSeq_tail: proof_shape: bind-only; consumers: rA_le_hit; escape_witness: none. Direct frozen dependencies: M, oddSeq.eq_2, oddPart, oddSeq, Dynamics.oddPart_factor.
rA_le_hit: proof_shape: bind-only; consumers: rA_quadratic; escape_witness: none. Direct frozen dependencies: M, oddSeq.eq_2, oddPart, oddSeq, Dynamics.oddPart_factor.
rA_quadratic: proof_shape: content; consumers: result; escape_witness: none. Direct frozen dependencies: M, oddSeq.eq_2, oddPart, Dynamics.nonzero_of_odd, Dynamics.q_ne_zero, oddSeq, Dynamics.oddPart_factor, Dynamics.nonzero_eq_one, Dynamics.degree_q, Dynamics.eq_one_of_degree_zero.
result: proof_shape: content; consumers: settlement; escape_witness: none. Direct frozen dependencies: M, oddSeq.eq_2, oddPart, Dynamics.nonzero_of_odd, Dynamics.q_ne_zero, oddSeq, Dynamics.oddPart_factor, Dynamics.nonzero_eq_one, Dynamics.degree_q, Dynamics.eq_one_of_degree_zero.

Frozen dependency declaration identities (protected origin/dev base):
D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.Dynamics.degree_q: sha256:ec11456930cae49ecce719715ba0a4095a5203c0da78d18e315334d6d2634369
D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.Dynamics.eq_one_of_degree_zero: sha256:572b27175e72a674ffe84491511b5135cc190ad335dc3a9015a1f5106e6fa13e
D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.Dynamics.nonzero_eq_one: sha256:d00902ad3d990675293864000c0dad424edd3a8ee1bcc2a33aa639d011ae236b
D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.Dynamics.nonzero_of_odd: sha256:71f61c3343f58e3bbf935aa7e23b18afdccd83e89287e73a3978cf85cbaed803
D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.Dynamics.oddPart_factor: sha256:3bd834d766891e481f522223d8891e75905481b154f522c2dcbec77d98b6eb33
D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.Dynamics.q_ne_zero: sha256:57a9a483782bb38e5d8e4f1bfac097f9b9b070997389041eac2009760bee47a6
D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.M: sha256:a24a0175ed4a6409c033182746a2df6a0b17370dd2c65b8a5007b820a431434e
D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.oddPart: sha256:430bc6d50cb3f928dc4263b3edc0809bd2d385f5df64a906637b94eeb63129e9
D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.oddSeq: sha256:81ad65efa7797d5e76c47bc6469c07615534e2732713e219bf050c5869e9c99f
D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.oddSeq.eq_2: sha256:21e2042cb7482798087174e1b68a2a090a24c846ea690217e06227203ae9cfc5
-/

import D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz

/-! Binding conventions for L. H. Gallardo and O. Rahavandrainy, "A variant of Collatz's Conjecture over Binary
Polynomials", arXiv:2510.07530v1 (8 October 2025); Rev. Un. Mat. Argentina 69 (2026), 295–302.

* §1: A ∈ 𝔽₂[x] is odd if it has no linear factor; M₁ = x² + x + 1. "A₀ = A, …, A₁ is the odd polynomial such that
  A₀ = x^{a₀}(x + 1)^{b₀} A₁, A₂ = 1 + M₁A₁, …, A_{2k} = 1 + M₁A_{2k−1}, … A_{2k+1} = A_{2k}/(x^{a_{2k}}(x + 1)^{b_{2k}})."
  These are the frozen owners `M`, `oddPart` and `oddSeq` (`oddSeq A k = A_{2k+1}`).
* Conjecture 1.1 / Theorem 1.2: "there exists m ∈ ℕ* such that for all k ≥ m, A_{2k} = x(x + 1) and A_{2k+1} = 1", and
  "the sequences of polynomials obtained from Collatz transformations are of finite length r_A … where m ∈ ℕ* and
  r_A = m + 1 ≤ 2^{deg(A)−1}"; `m` is the least such index.
* §1, after Theorem 1.2: "several computations suggest that here also r_A is bounded by a polynomial in deg(A)". -/

namespace D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound

open Polynomial D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz
open D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.Dynamics

/-- The even terms `A_{2k}`: `A₀ = A` and `A_{2k} = 1 + M₁ A_{2k−1}` for `k ≥ 1`. -/
noncomputable def evenTerm (A : (ZMod 2)[X]) (k : ℕ) : (ZMod 2)[X] :=
  if k = 0 then A else 1 + M * oddSeq A (k - 1)

/-- Theorem 1.2's length `r_A = m + 1`, with `m ≥ 1` least such that `A_{2k} = x(x + 1)` and `A_{2k+1} = 1` for all
`k ≥ m`. -/
noncomputable def rA (A : (ZMod 2)[X]) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ ∀ k, m ≤ k → evenTerm A k = X * (X + 1) ∧ oddSeq A k = 1} + 1

/-- The prediction: `r_A` is bounded by a polynomial in `deg(A)`. -/
def claim : Prop :=
  ∃ p : ℕ[X], ∀ A : (ZMod 2)[X], A ≠ 0 → rA A ≤ p.eval A.natDegree

end D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound


namespace D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound
open Polynomial D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz
open D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.Dynamics
open scoped CharTwo

private theorem oddPart_data (F : (ZMod 2)[X]) (hF : F ≠ 0) :
    ∃ a b : ℕ, F = X ^ a * (X - C 1) ^ b * oddPart F ∧
      (oddPart F).eval 0 = 1 ∧ (oddPart F).eval 1 = 1 := by
  let a := F.rootMultiplicity 0
  let U := F /ₘ X ^ a
  have hu : X ^ a * U = F := by
    simpa only [C_0, sub_zero] using pow_mul_divByMonic_rootMultiplicity_eq F (0 : ZMod 2)
  have hu0 : U.eval 0 ≠ 0 := by
    simpa only [C_0, sub_zero] using eval_divByMonic_pow_rootMultiplicity_ne_zero (0 : ZMod 2) hF
  have hu_ne : U ≠ 0 := by intro h; simp [h] at hu0
  let b := U.rootMultiplicity 1
  let V := U /ₘ (X - C 1) ^ b
  have hv : (X - C 1) ^ b * V = U := pow_mul_divByMonic_rootMultiplicity_eq U 1
  have hv1 : V.eval 1 ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero 1 hu_ne
  have hv0 : V.eval 0 ≠ 0 := by
    intro h
    have hh := congrArg (Polynomial.eval (0 : ZMod 2)) hv
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, h, mul_zero] at hh
    exact hu0 hh.symm
  have v0 : V.eval 0 = 1 := nonzero_eq_one _ hv0
  have v1 : V.eval 1 = 1 := nonzero_eq_one _ hv1
  have hf : F = X ^ a * (X - C 1) ^ b * V := by rw [mul_assoc, hv, hu]
  have ho : oddPart F = V := by rw [hf]; exact oddPart_factor a b V v0 v1
  exact ⟨a, b, by rwa [ho], by rwa [ho], by rwa [ho]⟩

private theorem oddPart_odd (F : (ZMod 2)[X]) (hF : F ≠ 0) :
    (oddPart F).eval 0 = 1 ∧ (oddPart F).eval 1 = 1 := by
  obtain ⟨a,b,h,ho⟩ := oddPart_data F hF
  exact ho

private theorem oddPart_degree (F : (ZMod 2)[X]) (hF : F ≠ 0) :
    (oddPart F).natDegree ≤ F.natDegree := by
  obtain ⟨a,b,h,ho⟩ := oddPart_data F hF
  exact natDegree_le_of_dvd ⟨X^a*(X-C 1)^b, by simpa only [mul_comm] using h⟩ hF

private theorem numerator_degree (F : (ZMod 2)[X]) (hF : F ≠ 0) :
    (1 + M * F).natDegree = F.natDegree + 2 := by
  have hd : (M * F).natDegree = F.natDegree + 2 := by
    rw [natDegree_mul q_ne_zero hF, degree_q]; omega
  rw [natDegree_add_eq_right_of_natDegree_lt (by simp only [natDegree_one]; omega), hd]

private theorem numerator_nonzero (F : (ZMod 2)[X]) : 1 + M * F ≠ 0 := by
  by_cases hF : F = 0
  · simp [hF]
  have hdeg2 := numerator_degree F hF
  intro h
  simp [h] at hdeg2

private theorem step_odd (F : (ZMod 2)[X]) :
    (oddPart (1 + M * F)).eval 0 = 1 ∧ (oddPart (1 + M * F)).eval 1 = 1 :=
  oddPart_odd _ (numerator_nonzero F)

private theorem step_data (F : (ZMod 2)[X]) (h0 : F.eval 0 = 1) (h1 : F.eval 1 = 1) :
    ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧
      1 + M * F = X ^ a * (X - C 1) ^ b * oddPart (1 + M * F) ∧
      F.natDegree + 2 = a + b + (oddPart (1 + M * F)).natDegree := by
  obtain ⟨a,b,hf,hU0,hU1⟩ := oddPart_data _ (numerator_nonzero F)
  have ha : 1 ≤ a := by
    by_contra hh
    have ha0 : a = 0 := Nat.eq_zero_of_not_pos hh
    have he := congrArg (Polynomial.eval (0 : ZMod 2)) hf
    simp only [eval_add, eval_one, eval_mul, eval_pow, eval_X, eval_sub, eval_C, ha0, pow_zero, hU0, h0] at he
    simp [M] at he
  have hb : 1 ≤ b := by
    by_contra hh
    have hb0 : b = 0 := Nat.eq_zero_of_not_pos hh
    have he := congrArg (Polynomial.eval (1 : ZMod 2)) hf
    simp only [eval_add, eval_one, eval_mul, eval_pow, eval_X, hb0, pow_zero, hU1, h1] at he
    simp [M] at he
  refine ⟨a,b,ha,hb,hf,?_⟩
  have hd := congrArg Polynomial.natDegree hf
  rw [numerator_degree F (nonzero_of_odd F h0)] at hd
  rw [natDegree_mul (mul_ne_zero (pow_ne_zero a X_ne_zero)
    (pow_ne_zero b (X_sub_C_ne_zero 1))) (nonzero_of_odd _ hU0),
    natDegree_mul (pow_ne_zero a X_ne_zero) (pow_ne_zero b (X_sub_C_ne_zero 1)),
    natDegree_pow, natDegree_pow, natDegree_X, natDegree_X_sub_C, mul_one, mul_one] at hd
  exact hd

private theorem step_degree (F : (ZMod 2)[X]) (h0 : F.eval 0 = 1) (h1 : F.eval 1 = 1) :
    (oddPart (1 + M * F)).natDegree ≤ F.natDegree := by
  obtain ⟨a,b,ha,hb,hf,hd⟩ := step_data F h0 h1
  omega

private theorem step_same_factor (F : (ZMod 2)[X]) (h0 : F.eval 0 = 1) (h1 : F.eval 1 = 1)
    (hd : (oddPart (1 + M * F)).natDegree = F.natDegree) :
    1 + M * F = X * (X + 1) * oddPart (1 + M * F) := by
  obtain ⟨a,b,ha,hb,hf,he⟩ := step_data F h0 h1
  have ha1 : a = 1 := by omega
  have hb1 : b = 1 := by omega
  simpa [ha1,hb1,sub_eq_add_neg] using hf

private noncomputable def plateau (F : (ZMod 2)[X]) : ℕ :=
  min ((F + 1).rootMultiplicity 0) ((F + 1).rootMultiplicity 1)

private theorem plus_one_ne_zero (F : (ZMod 2)[X]) (hne : F ≠ 1) : F + 1 ≠ 0 := by
  intro hh
  apply hne
  calc F = (F + 1) + 1 := by simp
       _ = 1 := by rw [hh, zero_add]

private theorem positive_degree (F : (ZMod 2)[X]) (h0 : F.eval 0 = 1) (hne : F ≠ 1) :
    0 < F.natDegree := by
  exact Nat.pos_of_ne_zero (fun hd => hne (eq_one_of_degree_zero F h0 hd))

private theorem plateau_positive (F : (ZMod 2)[X]) (h0 : F.eval 0 = 1) (h1 : F.eval 1 = 1)
    (hne : F ≠ 1) : 0 < plateau F := by
  apply lt_min
  · exact (rootMultiplicity_pos (plus_one_ne_zero F hne)).mpr (by simp [IsRoot,h0])
  · exact (rootMultiplicity_pos (plus_one_ne_zero F hne)).mpr (by simp [IsRoot,h1])

private theorem plateau_bound (F : (ZMod 2)[X]) (h0 : F.eval 0 = 1) (hne : F ≠ 1) :
    plateau F ≤ F.natDegree / 2 := by
  have hc : IsCoprime (X : (ZMod 2)[X]) (X - C 1) := by
    simpa using isCoprime_X_sub_C_of_isUnit_sub (show IsUnit ((0 : ZMod 2) - 1) by simp)
  have hl0 : plateau F ≤ (F + 1).rootMultiplicity 0 := min_le_left _ _
  have hl1 : plateau F ≤ (F + 1).rootMultiplicity 1 := min_le_right _ _
  have h0div : (X : (ZMod 2)[X]) ^ plateau F ∣ F + 1 := by
    simpa only [C_0, sub_zero] using
      (le_rootMultiplicity_iff (plus_one_ne_zero F hne)).mp hl0
  have h1div : (X - C 1 : (ZMod 2)[X]) ^ plateau F ∣ F + 1 :=
    (le_rootMultiplicity_iff (plus_one_ne_zero F hne)).mp hl1
  have hh := natDegree_le_of_dvd (hc.pow.mul_dvd h0div h1div) (plus_one_ne_zero F hne)
  rw [natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ (X_sub_C_ne_zero 1)),
    natDegree_pow, natDegree_pow, natDegree_X, natDegree_X_sub_C, mul_one,
    natDegree_add_eq_left_of_natDegree_lt (by simpa using positive_degree F h0 hne)] at hh
  omega

private theorem step_same_plateau (F : (ZMod 2)[X]) (h0 : F.eval 0 = 1) (h1 : F.eval 1 = 1)
    (hne : F ≠ 1) (hd : (oddPart (1 + M * F)).natDegree = F.natDegree) :
    plateau F = plateau (oddPart (1 + M * F)) + 1 := by
  let U := oddPart (1 + M * F)
  have hU : U ≠ 1 := by
    intro hh
    have hpos := positive_degree F h0 hne
    change U.natDegree = F.natDegree at hd
    simp [hh] at hd
    omega
  have heq : M * (F + 1) = (X * (X + 1)) * (U + 1) := by
    have hf := step_same_factor F h0 h1 hd
    change 1 + M * F = X * (X + 1) * U at hf
    calc M * (F + 1) = (1 + M * F) + (1 + M) := by ring_nf; simp
         _ = (X * (X + 1)) * U + (X * (X + 1)) := by
           rw [hf]; congr 1; dsimp [M]; ring_nf; simp
         _ = (X * (X + 1)) * (U + 1) := by ring
  have hp : (X * (X + 1) : (ZMod 2)[X]) ≠ 0 :=
    mul_ne_zero X_ne_zero (by simpa only [sub_eq_add_neg, C_1, CharTwo.neg_one_eq_one] using X_sub_C_ne_zero (1 : ZMod 2))
  have hval (t : ZMod 2) (ht : t = 0 ∨ t = 1) :
      (F + 1).rootMultiplicity t = (U + 1).rootMultiplicity t + 1 := by
    have hm : M.rootMultiplicity t = 0 := by
      apply rootMultiplicity_eq_zero
      rcases ht with rfl | rfl <;> simp [IsRoot,M]
    have hpt : (X * (X + 1) : (ZMod 2)[X]).rootMultiplicity t = 1 := by
      have hpform : (X * (X + 1) : (ZMod 2)[X]) = (X - C 0) * (X - C 1) := by simp
      rw [hpform, rootMultiplicity_mul (by simpa only [← hpform] using hp)]
      rw [rootMultiplicity_X_sub_C, rootMultiplicity_X_sub_C]
      rcases ht with rfl | rfl <;> norm_num
    have hh := congrArg (fun Q : (ZMod 2)[X] => Q.rootMultiplicity t) heq
    rw [rootMultiplicity_mul (mul_ne_zero q_ne_zero (plus_one_ne_zero F hne)),
      rootMultiplicity_mul (mul_ne_zero hp (plus_one_ne_zero U hU)), hm, hpt] at hh
    omega
  unfold plateau
  rw [hval 0 (Or.inl rfl), hval 1 (Or.inr rfl), min_add_add_right]

private noncomputable def step (F : (ZMod 2)[X]) : (ZMod 2)[X] := oddPart (1 + M * F)

private theorem iterate_odd (F : (ZMod 2)[X]) (h0 : F.eval 0 = 1) (h1 : F.eval 1 = 1) (k : ℕ) :
    (step^[k] F).eval 0 = 1 ∧ (step^[k] F).eval 1 = 1 := by
  cases k with
  | zero => exact ⟨h0,h1⟩
  | succ k => rw [Function.iterate_succ_apply']; exact step_odd _

private theorem plateau_escape (F : (ZMod 2)[X]) (h0 : F.eval 0 = 1) (h1 : F.eval 1 = 1)
    (hne : F ≠ 1) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ plateau F ∧ (step^[k] F).natDegree < F.natDegree := by
  generalize he : plateau F = r
  induction r using Nat.strong_induction_on generalizing F with
  | h r ih =>
    let U := step F
    have hU0 : U.eval 0 = 1 := (step_odd F).1
    have hU1 : U.eval 1 = 1 := (step_odd F).2
    have hle : U.natDegree ≤ F.natDegree := step_degree F h0 h1
    by_cases hlt : U.natDegree < F.natDegree
    · refine ⟨1, le_rfl, ?_, ?_⟩
      · have := plateau_positive F h0 h1 hne; omega
      · simpa only [Function.iterate_one] using hlt
    have hd : U.natDegree = F.natDegree := by omega
    have hUne : U ≠ 1 := by
      intro hh
      have hp := positive_degree F h0 hne
      simp only [hh, natDegree_one] at hd
      omega
    have hr : plateau F = plateau U + 1 := step_same_plateau F h0 h1 hne hd
    obtain ⟨k,hk0,hkr,hkd⟩ := ih (plateau U) (by omega) U hU0 hU1 hUne rfl
    refine ⟨k+1, by omega, by omega, ?_⟩
    rw [Function.iterate_succ_apply]
    exact hkd.trans_eq hd

private theorem square_budget_step (n : ℕ) :
    (n + 1) / 2 + n ^ 2 / 4 = (n + 1) ^ 2 / 4 := by
  have hmod := Nat.mod_lt n (by decide : 0 < 2)
  have hn := Nat.mod_add_div n 2
  by_cases hh : n % 2 = 0
  · obtain ⟨q,hq⟩ : ∃ q, n = 2*q := ⟨n/2, by omega⟩
    subst n
    have hsq : (2*q)^2 = 4*q^2 := by ring
    have hsq1 : (2*q+1)^2 = 4*(q^2+q)+1 := by ring
    rw [hsq, hsq1]
    omega
  · obtain ⟨q,hq⟩ : ∃ q, n = 2*q+1 := ⟨n/2, by omega⟩
    subst n
    have hsq : (2*q+1)^2 = 4*(q^2+q)+1 := by ring
    have hsq1 : (2*q+1+1)^2 = 4*(q^2+q+q+1) := by ring
    rw [hsq, hsq1]
    omega

private theorem reaches_one (F : (ZMod 2)[X]) (h0 : F.eval 0 = 1) (h1 : F.eval 1 = 1) :
    ∃ k : ℕ, k ≤ F.natDegree ^ 2 / 4 ∧ step^[k] F = 1 := by
  generalize hd : F.natDegree = n
  induction n using Nat.strong_induction_on generalizing F with
  | h n ih =>
    by_cases he : F = 1
    · exact ⟨0, Nat.zero_le _, by simpa using he⟩
    obtain ⟨k,hk0,hk,hkd⟩ := plateau_escape F h0 h1 he
    let U := step^[k] F
    have hU0 := (iterate_odd F h0 h1 k).1
    have hU1 := (iterate_odd F h0 h1 k).2
    obtain ⟨s,hs,hseq⟩ := ih U.natDegree (by simpa only [← hd] using hkd) U hU0 hU1 rfl
    have hnpos : 0 < n := by simpa only [← hd] using positive_degree F h0 he
    have hUle : U.natDegree ≤ n - 1 := by change U.natDegree < F.natDegree at hkd; omega
    have hsle : U.natDegree^2 / 4 ≤ (n-1)^2 / 4 :=
      Nat.div_le_div_right (Nat.pow_le_pow_left hUle 2)
    have hkb : k ≤ n/2 := by
      exact hk.trans (by simpa only [hd] using plateau_bound F h0 he)
    have hbudget := square_budget_step (n-1)
    have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
    rw [hpred] at hbudget
    refine ⟨k+s, by omega, ?_⟩
    rw [Nat.add_comm k s, Function.iterate_add_apply]
    exact hseq

end D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound


namespace D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound
open Polynomial D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz
open D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.Dynamics
open scoped CharTwo

private theorem step_one : step 1 = 1 := by
  have hp : 1 + M * 1 = X ^ 1 * (X - C 1) ^ 1 * (1 : (ZMod 2)[X]) := by
    dsimp [M]; ring_nf; simp
  change oddPart (1 + M * 1) = 1
  rw [hp]
  exact oddPart_factor 1 1 1 (by simp) (by simp)

private theorem oddSeq_eq_iterate (A : (ZMod 2)[X]) (k : ℕ) :
    oddSeq A k = step^[k] (oddPart A) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [oddSeq, ih, Function.iterate_succ_apply']; rfl

private theorem oddSeq_hit (A : (ZMod 2)[X]) (hA : A ≠ 0) :
    ∃ s : ℕ, s ≤ A.natDegree ^ 2 / 4 ∧ oddSeq A s = 1 := by
  obtain ⟨s,hs,hh⟩ := reaches_one (oddPart A) (oddPart_odd A hA).1 (oddPart_odd A hA).2
  refine ⟨s, hs.trans ?_, ?_⟩
  · exact Nat.div_le_div_right (Nat.pow_le_pow_left (oddPart_degree A hA) 2)
  · rwa [oddSeq_eq_iterate]

private theorem oddSeq_tail (A : (ZMod 2)[X]) (s : ℕ) (hs : oddSeq A s = 1)
    (k : ℕ) (hk : s ≤ k) : oddSeq A k = 1 := by
  rw [oddSeq_eq_iterate] at hs ⊢
  have he : k = (k - s) + s := (Nat.sub_add_cancel hk).symm
  rw [he, Function.iterate_add_apply, hs]
  exact Function.iterate_fixed step_one (k - s)

private theorem rA_le_hit (A : (ZMod 2)[X]) (s : ℕ) (hs : oddSeq A s = 1) :
    rA A ≤ s + 2 := by
  have hmem : s + 1 ∈ {m : ℕ | 1 ≤ m ∧ ∀ k, m ≤ k →
      evenTerm A k = X * (X + 1) ∧ oddSeq A k = 1} := by
    refine ⟨by omega, ?_⟩
    intro k hk
    refine ⟨?_, oddSeq_tail A s hs k (by omega)⟩
    rw [evenTerm, ite_eq_right (by omega), oddSeq_tail A s hs (k - 1) (by omega)]
    dsimp [M]; ring_nf; simp
  have hh := Nat.sInf_le hmem
  unfold rA
  omega

/-- The source's length is uniformly bounded by the explicit quadratic estimate. -/
theorem rA_quadratic (A : (ZMod 2)[X]) (hA : A ≠ 0) :
    rA A ≤ 2 + A.natDegree ^ 2 / 4 := by
  obtain ⟨s,hs,hh⟩ := oddSeq_hit A hA
  have hb := rA_le_hit A s hh
  omega

theorem result : D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound.claim := by
  refine ⟨X ^ 2 + 2, ?_⟩
  intro A hA
  have hb := rA_quadratic A hA
  have hd : A.natDegree ^ 2 / 4 ≤ A.natDegree ^ 2 := Nat.div_le_self _ _
  simpa using (show rA A ≤ A.natDegree ^ 2 + 2 by omega)

end D5.S1.Recurrence.GallardoRahavandrainyCollatzLengthBound
