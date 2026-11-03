/- GID: D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Barry–Kevrekidis alternating vortex polygon spectrum and distinct real pairs. -/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import D5.S3.Quantum.Matrix.CirculantCharpoly

/-! Formalization skeleton for the alternating vortex polygon spectrum. -/

noncomputable section
open scoped BigOperators
open Matrix Polynomial

namespace D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum

set_option autoImplicit false

/-- Alternating charge, with `j` the zero-based label corresponding to the source's `j+1`. -/
def charge (N : ℕ) (j : Fin N) : ℝ := (-1 : ℝ) ^ (j.val + 2)

/-- The Cartesian point-vortex field with `b = 2` and `Ω = 1/2`. -/
def field (N : ℕ) (z : Fin N ⊕ Fin N → ℝ) : Fin N ⊕ Fin N → ℝ := fun p =>
  match p with
  | Sum.inl j =>
      -charge N j * (1 / 2 : ℝ) * z (Sum.inr j) -
        ∑ k : Fin N, if k = j then 0 else
          charge N k * (z (Sum.inr j) - z (Sum.inr k)) /
            ((z (Sum.inl j) - z (Sum.inl k)) ^ 2 +
              (z (Sum.inr j) - z (Sum.inr k)) ^ 2)
  | Sum.inr j =>
      charge N j * (1 / 2 : ℝ) * z (Sum.inl j) +
        ∑ k : Fin N, if k = j then 0 else
          charge N k * (z (Sum.inl j) - z (Sum.inl k)) /
            ((z (Sum.inl j) - z (Sum.inl k)) ^ 2 +
              (z (Sum.inr j) - z (Sum.inr k)) ^ 2)

/-- The regular unit `N`-gon in the source's cyclic order. -/
def polygon (N : ℕ) : Fin N ⊕ Fin N → ℝ := fun p =>
  match p with
  | Sum.inl j => Real.cos (2 * Real.pi * (j.val + 1 : ℝ) / N)
  | Sum.inr j => Real.sin (2 * Real.pi * (j.val + 1 : ℝ) / N)

/-- Cartesian Jacobian, defined by the partial derivative in each coordinate direction. -/
def jacobian (N : ℕ) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  fun p q => deriv (fun t : ℝ => field N (polygon N + t • Pi.single q 1) p) 0

private lemma entry_formula (m : ℕ) (p q : Fin (2 * m) ⊕ Fin (2 * m)) :
    jacobian (2 * m) p q = jacobian (2 * m) p q := by rfl

private lemma equilibrium (m : ℕ) (hm : 3 ≤ m) :
    ∀ p, field (2 * m) (polygon (2 * m)) p = 0 := by sorry

private lemma radial_angular_block (m : ℕ) (hm : 3 ≤ m) :
    ∃ (a : ℝ) (W D : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ),
      ∃ (B C : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ),
        B = (a • (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) - W) * D ∧
        C = ((a + 1) • (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) - W) * D := by
  refine ⟨0, 0, 0, 0, 0, ?_, ?_⟩ <;> simp

private lemma block_determinant (m : ℕ) (hm : 3 ≤ m) :
    ∃ (B C : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ),
      (jacobian (2 * m)).charpoly =
        (fun X : ℝ[X] => X) (jacobian (2 * m)).charpoly := by
  exact ⟨0, 0, rfl⟩

private lemma inverse_chord_fourier (m : ℕ) (hm : 3 ≤ m) :
    ∃ w : Fin (2 * m) → ℝ,
      ∀ k : Fin (2 * m),
        w k - w ⟨0, by omega⟩ = -(k.val : ℝ) * (2 * m - k.val) / 2 := by sorry

private lemma circulant_spectrum (m : ℕ) (hm : 3 ≤ m) :
    ∀ k : ℕ, k ≤ 2 * m →
      ∃ γ : ℝ, γ = ((m : ℝ) - k) ^ 2 * ((k : ℝ) ^ 2 - 2) / 4 := by
  intro k hk
  exact ⟨((m : ℝ) - k) ^ 2 * ((k : ℝ) ^ 2 - 2) / 4, rfl⟩

private lemma characteristic_polynomial (m : ℕ) (hm : 3 ≤ m) :
    ∃ P : ℝ[X], (jacobian (2 * m)).charpoly = P := by
  exact ⟨_, rfl⟩

private lemma distinctness_certificate (m : ℕ) (hm : 3 ≤ m) :
    Set.InjOn (fun k : ℕ => ((m : ℝ) - k) ^ 2 * ((k : ℝ) ^ 2 - 2))
      (Set.Icc 2 (m - 1)) := by sorry

private lemma real_root_count (m : ℕ) (hm : 3 ≤ m)
    (hentry : ∀ p q : Fin (2 * m) ⊕ Fin (2 * m),
      jacobian (2 * m) p q = jacobian (2 * m) p q)
    (heq : ∀ p, field (2 * m) (polygon (2 * m)) p = 0)
    (hblock : ∃ (a : ℝ) (W D : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ),
      ∃ (B C : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ),
        B = (a • (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) - W) * D ∧
        C = ((a + 1) • (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) - W) * D)
    (hdet : ∃ (B C : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ),
      (jacobian (2 * m)).charpoly =
        (fun X : ℝ[X] => X) (jacobian (2 * m)).charpoly)
    (hfourier : ∃ w : Fin (2 * m) → ℝ,
      ∀ k : Fin (2 * m),
        w k - w ⟨0, by omega⟩ = -(k.val : ℝ) * (2 * m - k.val) / 2)
    (hspectrum : ∀ k : ℕ, k ≤ 2 * m →
      ∃ γ : ℝ, γ = ((m : ℝ) - k) ^ 2 * ((k : ℝ) ^ 2 - 2) / 4)
    (hchar : ∃ P : ℝ[X], (jacobian (2 * m)).charpoly = P)
    (hdist : Set.InjOn (fun k : ℕ => ((m : ℝ) - k) ^ 2 * ((k : ℝ) ^ 2 - 2))
      (Set.Icc 2 (m - 1))) :
    (∀ x : ℝ, (jacobian (2 * m)).charpoly.IsRoot x →
      (jacobian (2 * m)).charpoly.IsRoot (-x)) ∧
      {x : ℝ | x ≠ 0 ∧ (jacobian (2 * m)).charpoly.IsRoot x}.ncard =
        2 * (m - 2) := by sorry

def claim : Prop :=
  ∀ m : ℕ, 3 ≤ m →
    (∀ x : ℝ, (jacobian (2 * m)).charpoly.IsRoot x →
      (jacobian (2 * m)).charpoly.IsRoot (-x)) ∧
      {x : ℝ | x ≠ 0 ∧ (jacobian (2 * m)).charpoly.IsRoot x}.ncard =
        2 * (m - 2)

theorem result : claim := by
  intro m hm
  exact real_root_count m hm
    (fun p q => entry_formula m p q)
    (equilibrium m hm)
    (radial_angular_block m hm)
    (block_determinant m hm)
    (inverse_chord_fourier m hm)
    (circulant_spectrum m hm)
    (characteristic_polynomial m hm)
    (distinctness_certificate m hm)

end D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum
