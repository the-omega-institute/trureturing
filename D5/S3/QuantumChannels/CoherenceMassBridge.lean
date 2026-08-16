/- GID: D5/S3/QuantumChannels/CoherenceMassBridge
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bridge qubit discarded mass to off-diagonal coherence and pinching fixed points. -/

import Mathlib
import D5.S3.Observer.StateNotPath
import D5.S3.QuantumChannels.PinchingProjection

/- Provenance: Native proof over pinned mathlib. -/

/- SEARCH RECEIPT
Repository reuse:
* D5/S3/Quantum/FiniteDimensional.lean:14-15 defines `QubitMatrix` as a `Fin 2`
  complex matrix.
* D5/S3/QuantumChannels/Pinching.lean:16-26 defines `pinching`, the custom
  trace-based `hilbertSchmidtInner`, and the entrywise pinching formula.
* D5/S3/QuantumChannels/PinchingProjection.lean:103-108 proves
  `pinching_discarded_coherence_mass`; the first theorem below is its exact
  `offDiag` reformulation.
* D5/S3/Observer/StateNotPath.lean:16-18 defines `offDiag`, and lines 28-46 prove
  `classical_diagonal_iterates_off_diag_eq_zero`; both are reused directly.
Pinned mathlib reuse:
* Mathlib/Data/Complex/Basic.lean:87-89 gives `Complex.ofReal_re`, used by
  simplification after applying `Complex.re` to the complex mass equation.
* Mathlib/Data/Complex/Basic.lean:555-560 gives `Complex.normSq_nonneg` and
  `Complex.normSq_eq_zero`; both are reused to identify the zero set.
* Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1070-1081 generates
  `add_eq_zero_iff_of_nonneg` via `[to_additive]`; it is reused to split the sum.
Inspected but not used:
* Mathlib/Data/Complex/Basic.lean:136-138 provides `Complex.ofReal_eq_zero`.
  Taking real parts is shorter here and avoids an explicit cast rewrite.
* Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean:38-50 and 155-178
  show that `starProjection` requires an `InnerProductSpace`, a submodule, and
  `HasOrthogonalProjection`. Its API does not directly apply to this repository's
  bare `pinching` function and custom Hilbert-Schmidt product.
Local proof boundary:
* The zero-mass and fixed-point converses are proved here by nonnegativity and
  exhaustive `Fin 2` matrix extensionality. No Hermitian, trace, or positivity
  assumptions are needed because all three statements hold for arbitrary matrices.
* The hypothesis in the iterate theorem is necessary: the private theorem below
  uses `n = 0` and `qubitX`, whose discarded mass is nonzero for every coefficient.
-/

namespace D5.S3.QuantumChannels.CoherenceMassBridge

open D5.S3.Observer.StateNotPath
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.QubitWitnesses
open D5.S3.QuantumChannels.Pinching
open D5.S3.QuantumChannels.PinchingProjection

/-- Hilbert-Schmidt mass discarded by qubit pinching is the squared mass of `offDiag`. -/
theorem pinching_discarded_mass_eq_offDiag_normSq (rho : QubitMatrix) :
    hilbertSchmidtInner (rho - pinching rho) (rho - pinching rho) =
      Complex.normSq (offDiag rho).1 + Complex.normSq (offDiag rho).2 := by
  simpa [offDiag] using pinching_discarded_coherence_mass rho

/-- Pinching discards zero Hilbert-Schmidt mass exactly when both off-diagonal entries vanish. -/
theorem pinching_discarded_mass_eq_zero_iff (rho : QubitMatrix) :
    hilbertSchmidtInner (rho - pinching rho) (rho - pinching rho) = 0 ↔
      offDiag rho = 0 := by
  rw [pinching_discarded_mass_eq_offDiag_normSq]
  constructor
  · intro hMass
    have hReal :
        Complex.normSq (offDiag rho).1 + Complex.normSq (offDiag rho).2 = 0 := by
      simpa using congrArg Complex.re hMass
    have hComponents := (add_eq_zero_iff_of_nonneg
      (Complex.normSq_nonneg (offDiag rho).1)
      (Complex.normSq_nonneg (offDiag rho).2)).mp hReal
    apply Prod.ext
    · exact Complex.normSq_eq_zero.mp hComponents.1
    · exact Complex.normSq_eq_zero.mp hComponents.2
  · intro hOffDiag
    simp [hOffDiag]

/-- A qubit matrix is fixed by standard-basis pinching exactly when it has no off-diagonal part. -/
theorem pinching_eq_self_iff_offDiag_eq_zero (rho : QubitMatrix) :
    pinching rho = rho ↔ offDiag rho = 0 := by
  constructor
  · intro hFixed
    apply Prod.ext
    · change rho 0 1 = 0
      have hEntry := congrFun (congrFun hFixed (0 : Fin 2)) (1 : Fin 2)
      simpa using hEntry.symm
    · change rho 1 0 = 0
      have hEntry := congrFun (congrFun hFixed (1 : Fin 2)) (0 : Fin 2)
      simpa using hEntry.symm
  · intro hOffDiag
    have h01 : rho 0 1 = 0 := by
      simpa [offDiag] using congrArg Prod.fst hOffDiag
    have h10 : rho 1 0 = 0 := by
      simpa [offDiag] using congrArg Prod.snd hOffDiag
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10]

/-- Every classical-diagonal iterate has zero discarded mass on diagonal input. -/
theorem classical_diagonal_iterates_discarded_mass_eq_zero
    (c : DampingCoefficient) (n : ℕ) (rho : QubitMatrix)
    (hDiagonal : offDiag rho = 0) :
    hilbertSchmidtInner
        (((classicalDiagonalChannel c)^[n]) rho -
          pinching (((classicalDiagonalChannel c)^[n]) rho))
        (((classicalDiagonalChannel c)^[n]) rho -
          pinching (((classicalDiagonalChannel c)^[n]) rho)) = 0 := by
  exact (pinching_discarded_mass_eq_zero_iff
    (((classicalDiagonalChannel c)^[n]) rho)).2
      (classical_diagonal_iterates_off_diag_eq_zero c n rho hDiagonal)

private theorem hDiagonal_is_necessary (c : DampingCoefficient) :
    hilbertSchmidtInner
        (((classicalDiagonalChannel c)^[0]) qubitX -
          pinching (((classicalDiagonalChannel c)^[0]) qubitX))
        (((classicalDiagonalChannel c)^[0]) qubitX -
          pinching (((classicalDiagonalChannel c)^[0]) qubitX)) ≠ 0 := by
  rw [pinching_discarded_mass_eq_offDiag_normSq]
  norm_num [offDiag, qubitX]

#print axioms pinching_discarded_mass_eq_offDiag_normSq
#print axioms pinching_discarded_mass_eq_zero_iff
#print axioms pinching_eq_self_iff_offDiag_eq_zero
#print axioms classical_diagonal_iterates_discarded_mass_eq_zero

end D5.S3.QuantumChannels.CoherenceMassBridge
