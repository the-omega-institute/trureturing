/- GID: D5/S1/Words/Palindromes/PeriodDoubling/PrefixPalindromicLengthNotAutomatic
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/PrefixPalindromicLengthNotAutomatic
   mirror-E: none(waiver:infinite-binary-kernel)
   anchors: []
   utility: none
   digest: The period-doubling PPL-difference has an infinite binary kernel. -/

/-
proof_shape: content (result; support expanded within this delivery)
escape_witness: The marked-prefix obstruction gives unbounded sparse evaluation rank.
admission_basis: escape-witness
Direct frozen dependencies: D5/S1/Words/Palindromes/FridPrefix/PalindromicLength.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.SparseKernelRank
namespace D5.S1.Words.Palindromes.PeriodDoubling

open D5.S1.Words.FridPrefix (PL PalFactors)
open scoped BigOperators
set_option autoImplicit false

/-- Conjecture 17: the literal PPL-difference has an infinite binary kernel. -/
def claim : Prop :=
  let P : ℕ → ℕ := fun n => PL (List.ofFn (fun i : Fin n => u_pd i))
  ¬(twoKernel (fun n => (P (n+1) : ℤ)-(P n : ℤ))).Finite

theorem result : claim := by
  classical
  dsimp only [claim]
  intro hfinite
  let P : ℕ → ℚ := fun n => (PL (List.ofFn (fun i : Fin n => u_pd i)) : ℚ)
  have hzero : P 0=0 := by
    have h : PL ([] : List Bool)=0 := by
      apply Nat.eq_zero_of_le_zero
      apply Nat.find_le
      exact ⟨[],rfl,rfl,by simp⟩
    simpa [P] using h
  have hq : (twoKernel (fun n => P (n+1)-P n)).Finite := by
    apply (hfinite.image (fun u : ℕ → ℤ => fun n => (u n : ℚ))).subset
    intro g hg
    obtain ⟨e,r,hr,rfl⟩:=hg
    refine ⟨(fun n => (PL (List.ofFn (fun i : Fin (2^e*n+r+1) => u_pd i)) : ℤ)-
      (PL (List.ofFn (fun i : Fin (2^e*n+r) => u_pd i)) : ℤ)),⟨e,r,hr,rfl⟩,?_⟩
    funext n
    simp only [P,Int.cast_sub,Int.cast_natCast]
  have finite_difference_kernel_span (P : ℕ → ℚ) (hzero : P 0 = 0)
      (hfinite : (twoKernel (fun n => P (n + 1) - P n)).Finite) :
      FiniteDimensional ℚ (Submodule.span ℚ (twoKernel P)) := by
    classical
    let d : ℕ → ℚ := fun n => P (n + 1) - P n
    let H : (ℕ → ℚ) → (ℕ → ℚ) := fun u n => ∑ k ∈ Finset.range n, u k
    let U : Set (ℕ → ℚ) := twoKernel d ∪ H '' twoKernel d
    have hU : U.Finite := hfinite.union (hfinite.image H)
    have blocks (q n : ℕ) :
        (∑ k ∈ Finset.range (q * n), d k) =
          ∑ s ∈ Finset.range q, ∑ k ∈ Finset.range n, d (q * k + s) := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Nat.mul_succ, Finset.sum_range_add, ih]
        simp_rw [Finset.sum_range_succ]
        rw [Finset.sum_add_distrib]
    have decomposition (e r n : ℕ) :
        P (2 ^ e * n + r) =
          (∑ s ∈ Finset.range (2 ^ e), H (fun k => d (2 ^ e * k + s)) n) +
            ∑ s ∈ Finset.range r, d (2 ^ e * n + s) := by
      have ht : ∑ k ∈ Finset.range (2 ^ e * n + r), d k = P (2 ^ e * n + r) := by
        simp only [d, Finset.sum_range_sub, hzero, sub_zero]
      rw [← ht, Finset.sum_range_add, blocks]
    have contain : Submodule.span ℚ (twoKernel P) ≤ Submodule.span ℚ U := by
      apply Submodule.span_le.mpr
      intro f hf
      obtain ⟨e, r, hr, rfl⟩ := hf
      have heq : (fun n => P (2 ^ e * n + r)) =
          (∑ s ∈ Finset.range (2 ^ e), H (fun k => d (2 ^ e * k + s))) +
            ∑ s ∈ Finset.range r, (fun n => d (2 ^ e * n + s)) := by
        funext n
        simpa using decomposition e r n
      rw [heq]
      apply Submodule.add_mem
      · apply Submodule.sum_mem
        intro s hs
        apply Submodule.subset_span
        right
        exact ⟨fun k => d (2 ^ e * k + s), ⟨e, s, Finset.mem_range.mp hs, rfl⟩, rfl⟩
      · apply Submodule.sum_mem
        intro s hs
        apply Submodule.subset_span
        left
        exact ⟨e, s, (Finset.mem_range.mp hs).trans hr, rfl⟩
    haveI : FiniteDimensional ℚ (Submodule.span ℚ U) :=
      (Submodule.fg_iff_finiteDimensional _).mp (Submodule.fg_span hU)
    exact Submodule.finiteDimensional_of_le contain
  exact stronger_PPL_kernel_span (finite_difference_kernel_span P hzero hq)

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.result
