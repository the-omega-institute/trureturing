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

private theorem sectorT_eq (a b : ℕ) (k : Fin (a + b + 2)) (ξ : Fin 3 → ℂ) :
    sectorT a b k ξ =
      ξ 0 • sectorF a b k 0 + ξ 1 • sectorF a b k 1 + ξ 2 • sectorF a b k 2 := by
  ext x
  rfl

private theorem hypereclectic_point (a b : ℕ) (k : Fin (a + b + 2)) :
    sectorT a b k ![0, 0, 1] = sectorF a b k 2 := by
  rw [sectorT_eq]
  simp

private theorem sector_nilpotent (a b : ℕ) (k : Fin (a + b + 2)) :
    sectorF a b k 2 ^ (a * b + 1) = 0 := by
  exact Module.End.submodule_pow_eq_zero_of_pow_eq_zero
    (G := F3 ℂ a b) rfl (weight_control ℂ a b).2.2.2.2

private theorem class_certificate (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (k : Fin (a + b + 2)) :
    ∃ P : MvPolynomial (Fin 3) ℂ, MvPolynomial.eval ![0, 0, 1] P = 1 ∧
      ∀ ξ : Fin 3 → ℂ, MvPolynomial.eval ξ P ≠ 0 → ∀ r : ℕ,
        finrank ℂ (LinearMap.range (sectorT a b k ξ ^ r)) =
          finrank ℂ (LinearMap.range (sectorF a b k 2 ^ r)) := by
  classical
  let B := Module.finBasis ℂ (sector a b k)
  let M := LinearMap.toMatrixAlgEquiv B
  let A : Matrix (Fin (finrank ℂ (sector a b k)))
      (Fin (finrank ℂ (sector a b k))) (MvPolynomial (Fin 3) ℂ) := fun i j =>
    MvPolynomial.X 0 * MvPolynomial.C (M (sectorF a b k 0) i j) +
    MvPolynomial.X 1 * MvPolynomial.C (M (sectorF a b k 1) i j) +
    MvPolynomial.X 2 * MvPolynomial.C (M (sectorF a b k 2) i j)
  have evaluate (ξ : Fin 3 → ℂ) :
      A.map (MvPolynomial.eval ξ) = M (sectorT a b k ξ) := by
    rw [sectorT_eq, map_add, map_add, map_smul, map_smul, map_smul]
    ext i j
    change MvPolynomial.eval ξ (A i j) = _
    simp [A, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have ranks (N : Module.End ℂ (sector a b k)) (r : ℕ) :
      (M N ^ r).rank = finrank ℂ (LinearMap.range (N ^ r)) := by
    change ((LinearMap.toMatrix B B) N ^ r).rank = _
    rw [LinearMap.toMatrix_pow, Matrix.rank_eq_finrank_range_toLin _ B B]
    rw [Matrix.toLin_toMatrix]
  have nilpotent : A.map (MvPolynomial.eval ![0, 0, 1]) ^ (a * b + 1) = 0 := by
    rw [evaluate, hypereclectic_point, ← map_pow, sector_nilpotent, map_zero]
  have bounded (ξ : Fin 3 → ℂ) (r : ℕ) :
      (A.map (MvPolynomial.eval ξ) ^ r).rank ≤
        (A.map (MvPolynomial.eval ![0, 0, 1]) ^ r).rank := by
    rw [evaluate, evaluate, hypereclectic_point, ranks, ranks]
    exact upper_bound a b ha hb ξ k r
  obtain ⟨P, hP, h⟩ := exists_polynomial_power_rank_certificate A ![0, 0, 1]
    (a * b + 1) nilpotent bounded
  refine ⟨P, hP, ?_⟩
  intro ξ hξ r
  have eq := h ξ hξ r
  rwa [evaluate, evaluate, hypereclectic_point, ranks, ranks] at eq

/-- A single polynomial for a filling certifies all cyclicity classes and all power ranks. -/
theorem result : claim := by
  classical
  intro a b ha hb
  refine ⟨upper_bound a b ha hb, ?_⟩
  choose P hP h using class_certificate a b ha hb
  refine ⟨∏ k : Fin (a + b + 2), P k, ?_, ?_⟩
  · rw [map_prod]
    exact Finset.prod_eq_one fun k _ => hP k
  · intro ξ hξ k r
    apply h k ξ _ r
    rw [map_prod] at hξ
    exact (Finset.prod_ne_zero_iff.mp hξ) k (Finset.mem_univ k)

#print axioms result

end D5.S3.Quantum.SpinChains.EclecticTwoWallUniversality
