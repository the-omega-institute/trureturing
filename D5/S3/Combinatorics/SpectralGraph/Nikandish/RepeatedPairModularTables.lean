/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairModularTables
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/RepeatedPairModularTables
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairModularTables.actual_five; instance=D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairModularTables.five_table
   digest: Complete small-prime quadratic tables and arbitrary-tail actual graph consumers. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.RepeatedPairModularResidues

/-! Source: repeated-pair-modular, PR9 revision
6d491f77b35dec808fc777b69939c56cdae5dc02. These are the complete
prime-three and prime-five residue tables. They are necessary tests,
not a classification of integral spectra. All finite tail coordinates
and all distinct graph primes remain in the actual consumers. -/
set_option autoImplicit false
noncomputable section
open Polynomial
namespace D5.S3.Combinatorics.SpectralGraph.RepeatedPairModularTables
open RepeatedPairModular RepeatedPairModularResidues RepeatedPairSupport
open IdealIntersectionSupport IdealIntersectionObstructions

/-- All three residues, including the repeated-root residue. -/
theorem three_table (k : ZMod 3) :
    (X^2-X-C k).Splits ↔ k ≠ 1 := by
  rw [quadratic_splits_iff_root]
  have h : ∀ k : ZMod 3, (∃ r : ZMod 3, r^2-r-k=0) ↔ k ≠ 1 := by
    decide +kernel
  exact h k

/-- All five residues, with discriminant zero included. -/
theorem five_table (k : ZMod 5) :
    (X^2-X-C k).Splits ↔ k ≠ 3 ∧ k ≠ 4 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [quadratic_splits_iff_root]
  have h : ∀ k : ZMod 5, (∃ r : ZMod 5, r^2-r-k=0) ↔ k ≠ 3 ∧ k ≠ 4 := by
    decide +kernel
  exact h k

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The full arbitrary-tail prime-three obstruction on the actual graph. -/
theorem actual_three (p : Fin 2 ⊕ ι → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (a : ℕ) (k : ι → ℕ) (ha : 0 < a) (hk : ∀ i, 0 < k i)
    (H : ActualLaplacianIntegral (modulus p (pairExponents a k)))
    (h3 : 3 ∣ a+1) : ∀ i, (k i : ZMod 3) ≠ 1 := by
  intro i
  exact (three_table _).mp (actual_prime_splits p hp hinj a k ha hk H 3 h3 i)

/-- The full arbitrary-tail prime-five obstruction on the actual graph. -/
theorem actual_five (p : Fin 2 ⊕ ι → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (a : ℕ) (k : ι → ℕ) (ha : 0 < a) (hk : ∀ i, 0 < k i)
    (H : ActualLaplacianIntegral (modulus p (pairExponents a k)))
    (h5 : 5 ∣ a+1) : ∀ i, (k i : ZMod 5) ≠ 3 ∧ (k i : ZMod 5) ≠ 4 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro i
  exact (five_table _).mp (actual_prime_splits p hp hinj a k ha hk H 5 h5 i)

end D5.S3.Combinatorics.SpectralGraph.RepeatedPairModularTables
