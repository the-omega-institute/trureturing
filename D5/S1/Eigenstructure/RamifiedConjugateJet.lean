/- GID: D5/S1/Eigenstructure/RamifiedConjugateJet
   generality: G
   mirror-B: D5/B/S1/Eigenstructure/RamifiedConjugateJet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A repeated residue eigenvalue carries the infinite power jet of its nilpotent part. -/

import D5.S0.Observation.PowerTraceSimilarityCountermodel
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.RingDivision

/- Library-search audit trail (2026-09-01):
   * Repository searches for `RamJet`, ramified conjugate jets, matrix-valued
     `Nat` sequences, repeated characteristic roots, and nonzero square-zero
     witnesses found no existing D5 jet definition. The exact standard matrix
     witness in `power_traces_do_not_determine_similarity` is reused below.
   * The adjacent `FibonacciMatrixDiscriminant` and golden-prime modules record
     discriminant five and its ramified-square classification, but neither
     retains the nilpotent direction after the eigenvalues merge.
   * Pinned Mathlib searches found `Matrix.charpoly_fin_two` and
     `Polynomial.rootMultiplicity_X_sub_C_pow`; both are applied directly.
     GitHub code searches found no third-party Lean declaration named
     `RamifiedConjugateJet` or matching the matrix/root-multiplicity witness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Eigenstructure.RamifiedConjugateJet

open Polynomial
open D5.S0.Observation.PowerTraceSimilarityCountermodel

/-- The ramified conjugate jet has a scalar center followed by every positive
power of the residual operator. Index zero is the first-order term. -/
def ramifiedConjugateJet {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι R) (lambdaZero : R) : R × (ℕ → Matrix ι ι R) :=
  (lambdaZero, fun k => (T - lambdaZero • (1 : Matrix ι ι R)) ^ (k + 1))

/-- Over the residue field at five, a nonzero square-zero Jordan direction gives
a realizable ramified jet centered at `3`. Its characteristic polynomial has
`3` as a double root, and the entire infinite tail is the positive-power
sequence of that nilpotent direction. -/
theorem exists_golden_ramified_conjugate_jet :
    let N : Matrix (Fin 2) (Fin 2) (ZMod 5) := Matrix.single 0 1 1
    let T : Matrix (Fin 2) (Fin 2) (ZMod 5) :=
      (3 : ZMod 5) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) + N
    N ≠ 0 ∧
      N ^ 2 = 0 ∧
      N.rank = 1 ∧
      T.charpoly = (X - C (3 : ZMod 5)) ^ 2 ∧
      rootMultiplicity (3 : ZMod 5) T.charpoly = 2 ∧
      ramifiedConjugateJet T 3 =
        ((3 : ZMod 5), fun k => N ^ (k + 1)) ∧
      (ramifiedConjugateJet T 3).2 0 = N ∧
      ∀ k, 1 ≤ k → (ramifiedConjugateJet T 3).2 k = 0 := by
  dsimp only
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let N : Matrix (Fin 2) (Fin 2) (ZMod 5) := Matrix.single 0 1 1
  let T : Matrix (Fin 2) (Fin 2) (ZMod 5) :=
    (3 : ZMod 5) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) + N
  have existing := power_traces_do_not_determine_similarity (K := ZMod 5)
  dsimp only at existing
  have hRank : N.rank = 1 := by
    simpa [N] using existing.2.2.2.2.1
  have hNne : N ≠ 0 := by
    intro hZero
    rw [hZero, Matrix.rank_zero] at hRank
    omega
  have hN2 : N ^ 2 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, N, Matrix.mul_apply, Fin.sum_univ_two]
  have hShift : T - (3 : ZMod 5) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) = N := by
    simp only [T]
    abel
  have hCharpoly : T.charpoly = (X - C (3 : ZMod 5)) ^ 2 := by
    rw [Matrix.charpoly_fin_two]
    norm_num [T, N, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.one_apply,
      Matrix.single_apply]
    ring_nf
    rw [show (6 : ZMod 5) = 1 by decide, show (9 : ZMod 5) = 4 by decide]
    have hLinear :
        (C (3 : ZMod 5) : Polynomial (ZMod 5)) * C 2 = C 1 := by
      simpa only [map_mul] using
        congrArg (C : ZMod 5 → Polynomial (ZMod 5))
          (show (3 : ZMod 5) * 2 = 1 by decide)
    have hSquare :
        (C (3 : ZMod 5) : Polynomial (ZMod 5)) ^ 2 = C 4 := by
      simpa only [map_pow] using
        congrArg (C : ZMod 5 → Polynomial (ZMod 5))
          (show (3 : ZMod 5) ^ 2 = 4 by decide)
    rw [show (2 : Polynomial (ZMod 5)) = C 2 from
        (C_eq_natCast (R := ZMod 5) 2).symm,
      mul_assoc, hLinear, hSquare]
  have hMultiplicity : rootMultiplicity (3 : ZMod 5) T.charpoly = 2 := by
    rw [hCharpoly]
    exact rootMultiplicity_X_sub_C_pow 3 2
  have hJet : ramifiedConjugateJet T 3 =
      ((3 : ZMod 5), fun k => N ^ (k + 1)) := by
    simp only [ramifiedConjugateJet, hShift]
  refine ⟨hNne, hN2, hRank, hCharpoly, hMultiplicity, hJet, ?_, ?_⟩
  · simp [ramifiedConjugateJet]
  · intro k hk
    rw [hJet]
    change N ^ (k + 1) = 0
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [show 1 + m + 1 = 2 + m by omega, pow_add, hN2, zero_mul]

#print axioms exists_golden_ramified_conjugate_jet

end D5.S1.Eigenstructure.RamifiedConjugateJet
