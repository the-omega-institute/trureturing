/- GID: D5/S3/QuantumBounds/HighSpinCHSHNonviolation
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/HighSpinCHSHNonviolation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Local spin components satisfy the CHSH bound for every spin at least one. -/

import D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix Kronecker
open Matrix Complex
open D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment (spinComponent)

namespace D5.S3.QuantumBounds.HighSpinCHSHNonviolation

/-- A measurement direction has Euclidean length one. -/
def unit (u : Fin 3 → ℝ) : Prop := u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1

/-- The CHSH operator for the source's linear spin observables. -/
def chshOperator (n : ℕ) (a c b d : Fin 3 → ℝ) :
    Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) ℂ :=
  spinComponent n a ⊗ₖ spinComponent n b +
    spinComponent n a ⊗ₖ spinComponent n d +
    spinComponent n c ⊗ₖ spinComponent n b -
    spinComponent n c ⊗ₖ spinComponent n d

/-- Nonviolation for every density matrix and every four local spin directions, n = 2s ≥ 2. -/
def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ∀ ρ : Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) ℂ,
      ρ.PosSemidef → ρ.trace = 1 → ∀ a c b d : Fin 3 → ℝ,
        unit a → unit c → unit b → unit d →
          ‖(ρ * chshOperator n a c b d).trace‖ ≤ (n : ℝ) ^ 2 / 2

private def dicke (n : ℕ) : Matrix (Finset (Fin n)) (Fin (n + 1)) ℂ :=
  fun x k => if x.card = k.val then (1 / Real.sqrt (n.choose k.val : ℝ) : ℝ) else 0

private def slotPauli (n : ℕ) (r : Fin n) (u : Fin 3 → ℝ) :
    Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ :=
  fun x y =>
    (if x = y then (if r ∈ x then -(u 2 : ℂ) else (u 2 : ℂ)) else 0) +
    (if y = x ∆ {r} then
      (u 0 : ℂ) + (if r ∈ x then I * (u 1 : ℂ) else -I * (u 1 : ℂ)) else 0)

private def dilation (n : ℕ) :
    Matrix (Finset (Fin n) × Finset (Fin n)) (Fin (n + 1) × Fin (n + 1)) ℂ :=
  dicke n ⊗ₖ dicke n

private def liftedOperator (n : ℕ) (hn : 2 ≤ n) (a c b d : Fin 3 → ℝ) :
    Matrix (Finset (Fin n) × Finset (Fin n)) (Finset (Fin n) × Finset (Fin n)) ℂ :=
  let r : Fin n := ⟨0, by omega⟩
  let t : Fin n := ⟨1, by omega⟩
  let α := slotPauli n r a ⊗ₖ (1 : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ)
  let γ := slotPauli n t c ⊗ₖ (1 : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ)
  let β := (1 : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ) ⊗ₖ slotPauli n r b
  let δ := (1 : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ) ⊗ₖ slotPauli n t d
  α * (β + δ) + γ * (β - δ)

private lemma dicke_isometry (n : ℕ) : (dicke n)ᴴ * dicke n = 1 := by
  sorry

private lemma slot_compression (n : ℕ) (r : Fin n) (u : Fin 3 → ℝ) :
    (dicke n)ᴴ * slotPauli n r u * dicke n = (2 / n : ℂ) • spinComponent n u := by
  sorry

private lemma slot_hermitian (n : ℕ) (r : Fin n) (u : Fin 3 → ℝ) :
    (slotPauli n r u).IsHermitian := by
  sorry

private lemma slot_square (n : ℕ) (r : Fin n) (u : Fin 3 → ℝ) (hu : unit u) :
    slotPauli n r u * slotPauli n r u = 1 := by
  sorry

private lemma slots_commute (n : ℕ) (r t : Fin n) (hrt : r ≠ t)
    (u v : Fin 3 → ℝ) : Commute (slotPauli n r u) (slotPauli n t v) := by
  sorry

private lemma dilation_isometry (n : ℕ) : (dilation n)ᴴ * dilation n = 1 := by
  change (dicke n ⊗ₖ dicke n)ᴴ * (dicke n ⊗ₖ dicke n) = 1
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, dicke_isometry, one_kronecker_one]

private lemma chsh_dilation (n : ℕ) (hn : 2 ≤ n) (a c b d : Fin 3 → ℝ) :
    chshOperator n a c b d = ((n : ℂ) / 2) ^ 2 •
      ((dilation n)ᴴ * liftedOperator n hn a c b d * dilation n) := by
  have hc := slot_compression n
  have hi := dicke_isometry n
  sorry

private lemma lifted_hermitian (n : ℕ) (hn : 2 ≤ n) (a c b d : Fin 3 → ℝ) :
    (liftedOperator n hn a c b d).IsHermitian := by
  have hh := slot_hermitian n
  sorry

private lemma lifted_square (n : ℕ) (hn : 2 ≤ n) (a c b d : Fin 3 → ℝ)
    (ha : unit a) (hc : unit c) (hb : unit b) (hd : unit d) :
    (liftedOperator n hn a c b d) ^ 2 = (4 : ℂ) • 1 := by
  have hs := slot_square n
  have hcomm := slots_commute n
  sorry

private lemma dilated_density (n : ℕ)
    (ρ : Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) :
    (dilation n * ρ * (dilation n)ᴴ).PosSemidef ∧
      (dilation n * ρ * (dilation n)ᴴ).trace = 1 := by
  have hi := dilation_isometry n
  sorry

private lemma density_involution_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ l : Matrix ι ι ℂ) (hτ : τ.PosSemidef) (ht : τ.trace = 1)
    (hl : l.IsHermitian) (hs : l ^ 2 = (4 : ℂ) • 1) : ‖(τ * l).trace‖ ≤ 2 := by
  sorry

private lemma expectation_bound (n : ℕ) (hn : 2 ≤ n)
    (ρ : Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hρ : ρ.PosSemidef) (ht : ρ.trace = 1) (a c b d : Fin 3 → ℝ)
    (ha : unit a) (hc : unit c) (hb : unit b) (hd : unit d) :
    ‖(ρ * chshOperator n a c b d).trace‖ ≤ (n : ℝ) ^ 2 / 2 := by
  have hτ := dilated_density n ρ hρ ht
  have hbnd := density_involution_bound _ _ hτ.1 hτ.2
    (lifted_hermitian n hn a c b d) (lifted_square n hn a c b d ha hc hb hd)
  have he := chsh_dilation n hn a c b d
  sorry

theorem result : claim := by
  intro n hn ρ hρ ht a c b d ha hc hb hd
  exact expectation_bound n hn ρ hρ ht a c b d ha hc hb hd

end D5.S3.QuantumBounds.HighSpinCHSHNonviolation
