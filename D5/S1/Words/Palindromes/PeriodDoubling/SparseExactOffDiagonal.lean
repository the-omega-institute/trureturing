/- GID: D5/S1/Words/Palindromes/PeriodDoubling/SparseExactOffDiagonal
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/SparseExactOffDiagonal
   mirror-E: none(waiver:unbounded-sparse-family-exact-values)
   anchors: []
   utility: none
   digest: Odd sparse families beyond the diagonal attain the signed-weight lower bound. -/

/-
proof_shape: content (offdiagonal_exact_family)
escape_witness: The sparse cut construction and canonical signed digits attain equal upper and lower costs.
admission_basis: escape-witness
Direct frozen dependencies: none; the period-doubling modules are delivered together.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.SparseInitialArithmetic
import D5.S1.Words.Palindromes.PeriodDoubling.SparseFamilyUpper
import D5.S1.Words.Palindromes.PeriodDoubling.SignedCutLowerBound
namespace D5.S1.Words.Palindromes.PeriodDoubling
open scoped BigOperators
set_option autoImplicit false
theorem offdiagonal_exact_family (a b : ℕ) (ha : 0<a) (hao : a%2=1) (hbo : b%2=1) (hab : 2*a+1 ≤ b) :
    let N : ℕ → ℕ → ℕ := fun a b =>
      (∑ i ∈ Finset.range a,2^(2*b+2+3*i)) + (∑ j ∈ Finset.range b,2^(2*j+1))
    PL (List.ofFn (fun i : Fin (N a b) => u_pd i))=a+b := by
  dsimp only
  let n:=(∑ i ∈ Finset.range a,2^(2*b+2+3*i)) + (∑ j ∈ Finset.range b,2^(2*j+1))
  have hF:=(sparse_initial_arithmetic a b).2.1
  change signedWeight (((n+1)/2 : ℕ) : ℤ)=a+b at hF
  have hlower:=palindromic_suffix_signed_bound.2 n
  rw [hF] at hlower
  have hu:=sparse_family_upper a b 0 ha hao hbo (by omega) (by decide)
  dsimp only at hu
  have hne : b ≠ 2*a-1 := by omega
  change PL (List.ofFn (fun i : Fin (n+0) => u_pd i)) ≤ _ at hu
  simp only [Nat.add_zero,if_neg hne] at hu
  exact Nat.le_antisymm hu hlower

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.offdiagonal_exact_family
