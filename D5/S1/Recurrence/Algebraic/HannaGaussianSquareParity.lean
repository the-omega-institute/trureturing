/- GID: D5/S1/Recurrence/Algebraic/HannaGaussianSquareParity
   generality: G
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaGaussianSquareParity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna Gaussian series coefficients are odd exactly at squares. -/

/-
admission_basis: open-problem-resolution (#21417; Proved)
Direct frozen dependencies: none (all declarations below).
summand: proof_shape: bind-only; escape_witness: none;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianSquareParity.A, D5.S1.Recurrence.Algebraic.HannaGaussianSquareParity.coefficient_matrix, D5.S1.Recurrence.Algebraic.HannaGaussianSquareParity.result.
A: proof_shape: bind-only; escape_witness: none;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianSquareParity.claim, D5.S1.Recurrence.Algebraic.HannaGaussianSquareParity.coefficient_matrix, D5.S1.Recurrence.Algebraic.HannaGaussianSquareParity.result.
claim: proof_shape: bind-only; escape_witness: none;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianSquareParity.result.
coefficient_matrix: proof_shape: bind-only; escape_witness: none;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianSquareParity.result.
diagonal_parity: proof_shape: content; escape_witness: D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.weight_odd;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianSquareParity.result.
result: proof_shape: content; escape_witness: D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.kernel_coefficient;
The summand, coefficient construction and claim retain the source expressions.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22307
-/

import D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity

namespace D5.S1.Recurrence.Algebraic.HannaGaussianSquareParity

open PowerSeries
open scoped BigOperators

/-- The m-th summand of OEIS A323689, written in the source variable x. -/
noncomputable def summand (m : ℕ) : PowerSeries ℂ :=
  (X ^ m + C Complex.I) ^ m *
    ((1 + C Complex.I * X ^ m) ^ (m + 1))⁻¹

/-- Positive-degree coefficients of the source sum; its constant term is set to 1. -/
noncomputable def A : PowerSeries ℂ :=
  mk fun N => if N = 0 then 1 else
    ∑ m ∈ Finset.Icc 1 N, coeff N (summand m)

/-- The %C off-square conjecture together with the %F square-index parity assertion. -/
def claim : Prop :=
  ∀ N : ℕ, ∃ z : ℤ, coeff N A = (z : ℂ) ∧
    (Odd z ↔ ∃ r : ℕ, N = r ^ 2)

end D5.S1.Recurrence.Algebraic.HannaGaussianSquareParity

namespace D5.S1.Recurrence.Algebraic.HannaGaussianSquareParity
open PowerSeries D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity
open scoped BigOperators

private theorem coefficient_matrix (N : ℕ) (hN : 0 < N) :
    coeff N A = ∑ m ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      if m*k=N then coeff k (kernel m) else 0 := by
  simp only [A, coeff_mk, ite_eq_right (Nat.ne_of_gt hN)]
  apply Finset.sum_congr rfl
  intro m hm
  have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.mp hm).1; omega
  rw [summand, ← kernel_expansion m m hm0]
  apply expansion_coefficient
  intro k hk
  apply Finset.mem_Icc.mpr
  constructor <;> nlinarith [(Finset.mem_Icc.mp hm).1]

private theorem diagonal_parity (N : ℕ) (hN : 0 < N) :
    Odd (∑ m ∈ Finset.Icc 1 N, if m*m=N then weight m m else 0) ↔
      ∃ r : ℕ, N=r^2 := by
  classical
  by_cases h : ∃ r : ℕ, N=r^2
  · obtain ⟨r,hr⟩ := h
    have hrm : r ∈ Finset.Icc 1 N := by
      apply Finset.mem_Icc.mpr
      constructor <;> nlinarith
    have hs : (∑ m ∈ Finset.Icc 1 N, if m*m=N then weight m m else 0) = weight r r := by
      rw [Finset.sum_eq_single r]
      · rw [ite_eq_left (by nlinarith : r*r=N)]
      · intro b hb hbr
        rw [ite_eq_right]
        intro he
        exact hbr (by nlinarith)
      · exact fun hn => (hn hrm).elim
    rw [hs]
    exact iff_of_true (weight_odd r r) ⟨r,hr⟩
  · have hs : (∑ m ∈ Finset.Icc 1 N, if m*m=N then weight m m else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      rw [ite_eq_right]
      intro he
      exact h ⟨m,by nlinarith⟩
    simp [hs,h]

theorem result : D5.S1.Recurrence.Algebraic.HannaGaussianSquareParity.claim := by
  intro N
  by_cases hN : N=0
  · subst N
    refine ⟨1, ?_, ?_⟩
    · simp [A]
    · exact iff_of_true (by norm_num) ⟨0, rfl⟩
  · have hN' : 0<N := Nat.pos_of_ne_zero hN
    obtain ⟨z,hz,he⟩ := supported_matrix_integral (Finset.Icc 1 N)
      (fun m k => m*k=N) (fun m k => by rw [Nat.mul_comm])
    refine ⟨z,(coefficient_matrix N hN').trans hz, ?_⟩
    rw [← diagonal_parity N hN']
    obtain ⟨t,ht⟩ := he
    constructor
    · rintro ⟨q,hq⟩
      exact ⟨q-t,by omega⟩
    · rintro ⟨q,hq⟩
      exact ⟨q+t,by omega⟩

end D5.S1.Recurrence.Algebraic.HannaGaussianSquareParity
