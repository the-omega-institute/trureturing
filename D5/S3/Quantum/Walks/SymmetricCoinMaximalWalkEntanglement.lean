/- GID: D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement
   generality: I
   mirror-B: D5/B/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The symmetric coin maximizes full-mode geometric entanglement on every circle. -/

import D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate

namespace D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement

/-- A normalized two-component coin, with component zero denoting the left mover. -/
def unitCoin (c : Fin 2 → ℂ) : Prop := ∑ b, Complex.normSq (c b) = 1

/-- The Hadamard coin followed by the controlled periodic shift. -/
def hadamardStep (p : ℕ) (ψ : Fin 2 × ZMod p → ℂ) : Fin 2 × ZMod p → ℂ :=
  fun j => if j.1 = 0 then
    (ψ (0, j.2 + 1) + ψ (1, j.2 + 1)) / (Real.sqrt 2 : ℂ)
  else (ψ (0, j.2 - 1) - ψ (1, j.2 - 1)) / (Real.sqrt 2 : ℂ)

/-- The localized coin after `n` steps of the source's circle walk. -/
def walkState (p n : ℕ) (c : Fin 2 → ℂ) : Fin 2 × ZMod p → ℂ :=
  (hadamardStep p)^[n] (fun j => if j.2 = 0 then c j.1 else 0)

/-- The symmetric source coin, with angles `θ = φ = π / 2`. -/
def cStar : Fin 2 → ℂ := ![1 / (Real.sqrt 2 : ℂ), Complex.I / (Real.sqrt 2 : ℂ)]

/-- The generalized W vector in the computational basis of all individual modes. -/
def wState {ι : Type*} [Fintype ι] (λ : ι → ℂ) : (ι → Bool) → ℂ := by
  classical
  exact fun s => ∑ k, if s = Function.update (fun _ => false) k true then λ k else 0

/-- An ordinary tensor product of the two-component local vectors. -/
def productState {ι : Type*} [Fintype ι] (z : ι → Fin 2 → ℂ) : (ι → Bool) → ℂ :=
  fun s => ∏ k, z k (if s k then 1 else 0)

/-- Every local vector has unit Hilbert norm. -/
def unitFactors {ι : Type*} (z : ι → Fin 2 → ℂ) : Prop := ∀ k, unitCoin (z k)

/-- The standard inner product of a product vector with the generalized W vector. -/
def overlap {ι : Type*} [Fintype ι] (λ : ι → ℂ) (z : ι → Fin 2 → ℂ) : ℂ :=
  ∑ s : ι → Bool, conj (productState z s) * wState λ s

/-- The full-partition maximum product overlap squared. -/
def gMax {ι : Type*} [Fintype ι] (λ : ι → ℂ) : ℝ :=
  sSup {t | ∃ z : ι → Fin 2 → ℂ, unitFactors z ∧ t = Complex.normSq (overlap λ z)}

/-- The source's pure-state geometric measure for the partition into individual modes. -/
def geometricEntanglement {ι : Type*} [Fintype ι] (λ : ι → ℂ) : ℝ := 1 - gMax λ

/-- The source expectation, for every positive circle size, time, and normalized coin. -/
def claim : Prop :=
  ∀ (p : ℕ) (hp : 1 ≤ p) (n : ℕ) (c : Fin 2 → ℂ), unitCoin c →
    letI : NeZero p := ⟨by omega⟩
    geometricEntanglement (walkState p n c) ≤ geometricEntanglement (walkState p n cStar)

private lemma overlap_expansion {ι : Type*} [Fintype ι] (λ : ι → ℂ)
    (z : ι → Fin 2 → ℂ) : overlap λ z =
      ∑ k, λ k * conj (z k 1 * ∏ l ∈ Finset.univ.erase k, z l 0) := by
  classical
  sorry

private lemma overlap_bounded {ι : Type*} [Fintype ι] (λ : ι → ℂ) :
    BddAbove {t | ∃ z : ι → Fin 2 → ℂ,
      unitFactors z ∧ t = Complex.normSq (overlap λ z)} := by
  sorry

private lemma overlap_attained {ι : Type*} [Fintype ι] (λ : ι → ℂ) :
    ∃ z : ι → Fin 2 → ℂ, unitFactors z ∧ gMax λ = Complex.normSq (overlap λ z) := by
  sorry

private lemma phase_invariance {ι : Type*} [Fintype ι] (λ μ : ι → ℂ)
    (h : ∀ k, Complex.normSq (λ k) = Complex.normSq (μ k)) : gMax λ = gMax μ := by
  sorry

private lemma two_factor_max (a b r s : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    ∃ x y : Fin 2 → ℝ,
      (∀ k, 0 ≤ x k) ∧ (∀ k, 0 ≤ y k) ∧
      x 0 ^ 2 + x 1 ^ 2 = 1 ∧ y 0 ^ 2 + y 1 ^ 2 = 1 ∧
      (a * x 0 * y 0 + b * s * x 0 * y 1 + b * r * x 1 * y 0) ^ 2 =
        ((a ^ 2 + b ^ 2 * (r ^ 2 + s ^ 2)) +
          Real.sqrt ((a ^ 2 + b ^ 2 * (r ^ 2 + s ^ 2)) ^ 2 -
            4 * b ^ 4 * (r ^ 2 * s ^ 2))) / 2 ∧
      ∀ u v : Fin 2 → ℝ, u 0 ^ 2 + u 1 ^ 2 = 1 → v 0 ^ 2 + v 1 ^ 2 = 1 →
        (a * u 0 * v 0 + b * s * u 0 * v 1 + b * r * u 1 * v 0) ^ 2 ≤
          (a * x 0 * y 0 + b * s * x 0 * y 1 + b * r * x 1 * y 0) ^ 2 := by
  sorry

private lemma pair_balancing {ι : Type*} [Fintype ι] (λ μ : ι → ℂ) (i j : ι)
    (hij : i ≠ j)
    (hrest : ∀ k, k ≠ i → k ≠ j → Complex.normSq (μ k) = Complex.normSq (λ k))
    (hsum : Complex.normSq (μ i) + Complex.normSq (μ j) =
      Complex.normSq (λ i) + Complex.normSq (λ j))
    (hprod : Complex.normSq (λ i) * Complex.normSq (λ j) ≤
      Complex.normSq (μ i) * Complex.normSq (μ j)) : gMax μ ≤ gMax λ := by
  sorry

private lemma walk_linearity (p n : ℕ) (c : Fin 2 → ℂ) (j : Fin 2 × ZMod p) :
    walkState p n c j = c 0 * walkState p n ![1, 0] j +
      c 1 * walkState p n ![0, 1] j := by
  sorry

private lemma walk_reflection (p n : ℕ) :
    (∀ j, (walkState p n ![1, 0] j).im = 0 ∧ (walkState p n ![0, 1] j).im = 0) ∧
    (∀ x : ZMod p,
      walkState p n ![1, 0] (1, -x) =
        -(-1 : ℂ) ^ n * walkState p n ![0, 1] (0, x) ∧
      walkState p n ![0, 1] (1, -x) =
        (-1 : ℂ) ^ n * walkState p n ![1, 0] (0, x)) := by
  sorry

private lemma walk_pair_probabilities (p n : ℕ) (c : Fin 2 → ℂ) (hc : unitCoin c) :
    ∀ x : ZMod p,
      Complex.normSq (walkState p n cStar (0, x)) =
        Complex.normSq (walkState p n cStar (1, -x)) ∧
      Complex.normSq (walkState p n cStar (0, x)) +
          Complex.normSq (walkState p n cStar (1, -x)) =
        Complex.normSq (walkState p n c (0, x)) +
          Complex.normSq (walkState p n c (1, -x)) := by
  sorry

private lemma pair_average_le (p : ℕ) [NeZero p] (λ μ : Fin 2 × ZMod p → ℂ)
    (h : ∀ x : ZMod p,
      Complex.normSq (μ (0, x)) = Complex.normSq (μ (1, -x)) ∧
      Complex.normSq (μ (0, x)) + Complex.normSq (μ (1, -x)) =
        Complex.normSq (λ (0, x)) + Complex.normSq (λ (1, -x))) : gMax μ ≤ gMax λ := by
  sorry

theorem result : claim := by
  intro p hp n c hc
  letI : NeZero p := ⟨by omega⟩
  have h := pair_average_le p (walkState p n c) (walkState p n cStar)
    (walk_pair_probabilities p n c hc)
  exact sub_le_sub_left h 1

end D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement
