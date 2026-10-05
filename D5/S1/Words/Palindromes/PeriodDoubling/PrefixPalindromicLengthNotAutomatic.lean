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
Direct frozen dependencies: none; the period-doubling modules are delivered together.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.SparseKernelRank
namespace D5.S1.Words.Palindromes.PeriodDoubling
set_option autoImplicit false

/-- Conjecture 17: the literal PPL-difference has an infinite binary kernel. -/
def claim : Prop :=
  let P : ℕ → ℕ := fun n => PL (List.ofFn (fun i : Fin n => u_pd i))
  ¬(twoKernel (fun n => (P (n+1) : ℤ)-(P n : ℤ))).Finite

theorem result : claim := by
  dsimp only [claim]
  intro hfinite
  let P : ℕ → ℚ := fun n => (PL (List.ofFn (fun i : Fin n => u_pd i)) : ℚ)
  have hzero : P 0=0 := by
    have h : PL ([] : List Bool)=0 := by
      apply Nat.eq_zero_of_le_zero
      apply Nat.sInf_le
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
  exact stronger_PPL_kernel_span (finite_difference_kernel_span P hzero hq)

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.result
