/- GID: D5/S1/Recurrence/Algebraic/HannaGaussianShiftedSquareParity
   generality: G
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaGaussianShiftedSquareParity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna Gaussian series coefficients are odd exactly at shifted squares. -/

/-
admission_basis: open-problem-resolution (#21418; Proved)
Direct frozen dependencies: none (all declarations below).
summand: proof_shape: bind-only; escape_witness: none;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianShiftedSquareParity.A, D5.S1.Recurrence.Algebraic.HannaGaussianShiftedSquareParity.coefficient_matrix.
A: proof_shape: bind-only; escape_witness: none;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianShiftedSquareParity.claim, D5.S1.Recurrence.Algebraic.HannaGaussianShiftedSquareParity.coefficient_matrix, D5.S1.Recurrence.Algebraic.HannaGaussianShiftedSquareParity.result.
claim: proof_shape: bind-only; escape_witness: none;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianShiftedSquareParity.result.
coefficient_matrix: proof_shape: bind-only; escape_witness: none;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianShiftedSquareParity.result.
diagonal_parity: proof_shape: content; escape_witness: D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.weight_odd;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianShiftedSquareParity.result.
result: proof_shape: content; escape_witness: D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.kernel_coefficient;
The summand, coefficient construction and claim retain the source expressions.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22307
-/

import D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity

namespace D5.S1.Recurrence.Algebraic.HannaGaussianShiftedSquareParity

open PowerSeries
open scoped BigOperators

/-- The m-th summand of OEIS A324300, including its leading x^m. -/
noncomputable def summand (m : ℕ) : PowerSeries ℂ :=
  X ^ m * (X ^ (m + 1) + C Complex.I) ^ m *
    ((1 + C Complex.I * X ^ (m + 1)) ^ (m + 1))⁻¹

/-- The locally finite sum in the source, with no constant-term replacement. -/
noncomputable def A : PowerSeries ℂ :=
  mk fun N => ∑ m ∈ Finset.range (N + 1), coeff N (summand m)

/-- The %C conjecture and %F assertion in the source's original k*(k+2) indexing. -/
def claim : Prop :=
  ∀ N : ℕ, ∃ z : ℤ, coeff N A = (z : ℂ) ∧
    (Odd z ↔ ∃ k : ℕ, N = k * (k + 2))

end D5.S1.Recurrence.Algebraic.HannaGaussianShiftedSquareParity

namespace D5.S1.Recurrence.Algebraic.HannaGaussianShiftedSquareParity
open PowerSeries D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity
open scoped BigOperators

private theorem coefficient_matrix (N : ℕ) :
    coeff N A = ∑ m ∈ Finset.range (N+1), ∑ k ∈ Finset.range (N+1),
      if m+(m+1)*k=N then coeff k (kernel m) else 0 := by
  simp only [A, coeff_mk]
  apply Finset.sum_congr rfl
  intro m hm
  have hmN : m ≤ N := Finset.mem_range_succ_iff.mp hm
  have hm0 : m+1 ≠ 0 := Ne.symm (Nat.zero_ne_add_one m)
  rw [summand, mul_assoc, ← kernel_expansion m (m+1) hm0]
  apply shifted_expansion_coefficient m (m+1) N hm0 hmN
  intro k hk
  apply Finset.mem_range.mpr
  nlinarith

private theorem diagonal_parity (N : ℕ) :
    Odd (∑ m ∈ Finset.range (N+1), if m+(m+1)*m=N then weight m m else 0) ↔
      ∃ k : ℕ, N=k*(k+2) := by
  classical
  by_cases h : ∃ k : ℕ, N=k*(k+2)
  · obtain ⟨r,hr⟩ := h
    have hrm : r ∈ Finset.range (N+1) := by
      apply Finset.mem_range.mpr
      nlinarith
    have hs : (∑ m ∈ Finset.range (N+1), if m+(m+1)*m=N then weight m m else 0) = weight r r := by
      rw [Finset.sum_eq_single r]
      · rw [ite_eq_left (by nlinarith : r+(r+1)*r=N)]
      · intro b hb hbr
        rw [ite_eq_right]
        intro he
        exact hbr (by nlinarith)
      · exact fun hn => (hn hrm).elim
    rw [hs]
    exact iff_of_true (weight_odd r r) ⟨r,hr⟩
  · have hs : (∑ m ∈ Finset.range (N+1), if m+(m+1)*m=N then weight m m else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      rw [ite_eq_right]
      intro he
      exact h ⟨m,by nlinarith⟩
    simp [hs,h]

theorem result : D5.S1.Recurrence.Algebraic.HannaGaussianShiftedSquareParity.claim := by
  intro N
  obtain ⟨z,hz,he⟩ := supported_matrix_integral (Finset.range (N+1))
    (fun m k => m+(m+1)*k=N) (fun m k => by
      constructor <;> intro h <;> nlinarith)
  refine ⟨z,(coefficient_matrix N).trans hz, ?_⟩
  rw [← diagonal_parity N]
  obtain ⟨t,ht⟩ := he
  constructor
  · rintro ⟨q,hq⟩
    exact ⟨q-t,by omega⟩
  · rintro ⟨q,hq⟩
    exact ⟨q+t,by omega⟩

end D5.S1.Recurrence.Algebraic.HannaGaussianShiftedSquareParity
