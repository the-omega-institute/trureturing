/- GID: D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinChains/EclecticTwoWallUniversality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two-wall eclectic power ranks have hypereclectic bounds and generic equality. -/

import D5.S3.Quantum.SpinChains.TwoWallWeights
import D5.S3.Quantum.SpinChains.PolynomialPowerRanks
import Mathlib.Analysis.Complex.Exponential

open scoped BigOperators

namespace D5.S3.Quantum.SpinChains.EclecticTwoWallUniversality

open Module TwoWallWords TwoWallSl2 TwoWallWeights Sl2WeightFiltration PolynomialPowerRanks

/-- The cyclicity classes are indexed by k in Fin L, where L = a+b+2. -/
noncomputable def eigenvalue (a b : ℕ) (k : Fin (a + b + 2)) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / ((a + b + 2 : ℕ) : ℂ))

/-- The eigenspace of the literal one-site right shift. -/
noncomputable def sector (a b : ℕ) (k : Fin (a + b + 2)) :
    Submodule ℂ (Space ℂ a b) :=
  (U ℂ a b).eigenspace (eigenvalue a b k)

/-- The three literal bond sums restricted to a cyclicity class. -/
noncomputable def sectorF (a b : ℕ) (k : Fin (a + b + 2)) (i : Fin 3) :
    Module.End ℂ (sector a b k) :=
  (F ℂ a b i).restrict (Module.End.mapsTo_genEigenspace_of_comm
    ((cyclic_action ℂ a b).2.2.2.2.2.1 i) (eigenvalue a b k) 1)

/-- The eclectic operator restricted to the same cyclicity class. -/
noncomputable def sectorT (a b : ℕ) (k : Fin (a + b + 2)) (ξ : Fin 3 → ℂ) :
    Module.End ℂ (sector a b k) :=
  (T ℂ a b ξ).restrict (Module.End.mapsTo_genEigenspace_of_comm
    ((cyclic_action ℂ a b).2.2.2.2.2.2 ξ) (eigenvalue a b k) 1)

/-- For each filling, all couplings obey the power-rank bound, and one polynomial
normalized at (0,0,1) certifies equality in every cyclicity class and every power. -/
def claim : Prop :=
  ∀ (a b : ℕ), 2 ≤ a → 2 ≤ b →
    (∀ (ξ : Fin 3 → ℂ) (k : Fin (a + b + 2)) (r : ℕ),
      finrank ℂ (LinearMap.range (sectorT a b k ξ ^ r)) ≤
        finrank ℂ (LinearMap.range (sectorF a b k 2 ^ r))) ∧
    (∃ P : MvPolynomial (Fin 3) ℂ, MvPolynomial.eval ![0, 0, 1] P = 1 ∧
      ∀ ξ : Fin 3 → ℂ, MvPolynomial.eval ξ P ≠ 0 →
        ∀ (k : Fin (a + b + 2)) (r : ℕ),
          finrank ℂ (LinearMap.range (sectorT a b k ξ ^ r)) =
            finrank ℂ (LinearMap.range (sectorF a b k 2 ^ r)))

private theorem upper_bound (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (ξ : Fin 3 → ℂ) (k : Fin (a + b + 2)) (r : ℕ) :
    finrank ℂ (LinearMap.range (sectorT a b k ξ ^ r)) ≤
      finrank ℂ (LinearMap.range (sectorF a b k 2 ^ r)) := by
  have action := literal_action ℂ a b
  have symmetries := action.2.2.2.2.1.2
  have relations := action.2.2.1
  rw [action.2.2.2.1] at relations symmetries
  have bound := eigenspace_rank_comparison relations
    (weight_structure ℂ a b).2.2.1 (T ℂ a b ξ)
    (((weight_control ℂ a b).2.2.2.1 ha hb).2.1 ξ)
    symmetries.1 symmetries.2.1 symmetries.2.2
    ((cyclic_action ℂ a b).2.2.2.2.2.2 ξ) (eigenvalue a b k) r
  exact bound

end D5.S3.Quantum.SpinChains.EclecticTwoWallUniversality
