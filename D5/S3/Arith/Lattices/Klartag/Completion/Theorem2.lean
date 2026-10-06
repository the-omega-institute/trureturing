/- GID: D5/S3/Arith/Lattices/Klartag/Completion/Theorem2
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/Theorem2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform constants and completion of lattice packing. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import Mathlib
import D5.S3.Arith.Lattices.Klartag.Tail.TailAtStep
import D5.S3.Arith.Lattices.Klartag.Walk.ChainWalk
import D5.S3.Arith.Lattices.Klartag.State.StateInvariant4
import D5.S3.Arith.Lattices.Klartag.Contact.ContactIntegrated
import D5.S3.Arith.Lattices.Klartag.State.RawDataInst2

set_option linter.unusedSectionVars false

open MeasureTheory
open Matrix
open Metric
open Finset

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Completion.Theorem2

open scoped ENNReal RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Completion.Assembly
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst
open D5.S3.Arith.Lattices.Klartag.Construction.LatticeTransfer
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetup

/-- **The light-contact property** §5 proves and `Assembly.exists_phi_of_params` discards: on the
chosen line `g`, the total contact weight over the window is below Markov's threshold. -/
def LightContact {p m : ℕ} [NeZero p] (w : (Fin (m + 1) → ℤ) → ℝ≥0∞) (supp : Finset (Fin (m + 1) → ℤ))
    (theta : ℝ≥0∞) (g : Fin (m + 1) → ZMod p) : Prop :=
  ∑ y ∈ supp.filter (fun y => y ∈ latZ p (m + 1) g), w y < theta

/-- **`exists_phi_of_params` with the light-contact fact kept.**  The only change is that the
fourth component of `exists_good_line_of_params` is no longer thrown away. -/
theorem exists_phi_of_params' {p m : ℕ} [Fact (Nat.Prime p)] [NeZero p] (P : Params p (m + 1))
    {c₀ : ℝ}
    (hchain : ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 →
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 → ‖toE (m + 1) y‖ ≤ P.R → y ∉ latZ p (m + 1) g) →
      LightContact P.w P.supp P.theta g →
      ChainOutput P.alpha g c₀) :
    ∃ φ : EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)),
      ENNReal.ofReal (c₀ * (m : ℝ) ^ 2) ≤ volume (φ '' Metric.ball 0 1) ∧
      {v ∈ φ '' Metric.ball 0 1 | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  obtain ⟨g, hg0, hfreeR, hlight⟩ := exists_good_line_of_params P
  obtain ⟨A, S, hApos, hS, heq68, hfree⟩ := hchain g hg0 hfreeR hlight
  obtain ⟨B, hBdet, hBabs, hBmem⟩ :=
    exists_scaled_basisMatrix (p := p) (n := m + 1) (Nat.le_add_left 1 m) P.alpha_pos
      P.alpha_norm hg0
  have hfreeB : ∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
      (WithLp.toLp 2 (B *ᵥ (fun i => (y i : ℝ))) : EuclideanSpace ℝ (Fin (m + 1)))
        ∉ ChainEllipsoid.ellipsoid A := by
    intro y hy
    refine hfree _ (hBmem y) (mulVec_ne_zero hBdet ?_)
    intro hz
    refine hy (funext fun i => ?_)
    have hzi := congrFun hz i
    simp only [Pi.zero_apply] at hzi ⊢
    exact_mod_cast hzi
  obtain ⟨A', S', hA'pos, hS', hvol, hint⟩ :=
    chain_hyp_of_transfer hApos hS hBdet hfreeB (transfer_det_of_eq68 hBabs heq68)
  refine ⟨Matrix.toEuclideanLin S', ?_, ?_⟩
  · rw [ChainEllipsoid.image_ball_eq_ellipsoid hS']
    exact ChainEllipsoid.volume_ellipsoid_ge hA'pos hS' hvol
  · rw [ChainEllipsoid.image_ball_eq_ellipsoid hS']
    exact hint

/-- `Threshold2.remaining_of_lemma43`, threaded. -/
theorem remaining_of_lemma43' {c₀ : ℝ} (hc₀ : 0 < c₀)
    (H : ∀ m : ℕ, Threshold2.n₁ ≤ m →
      ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (P : Params p (m + 1)),
        ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 →
          (∀ y : Fin (m + 1) → ℤ, y ≠ 0 → ‖toE (m + 1) y‖ ≤ P.R → y ∉ latZ p (m + 1) g) →
          LightContact P.w P.supp P.theta g →
          ChainOutput P.alpha g c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  refine Threshold.klartag_packing_of_phi (N₁ := Threshold2.n₁) hc₀ ?_
  intro m hm
  obtain ⟨p, hp, hp0, P, hchain⟩ := H m hm
  exact exists_phi_of_params' P hchain

end D5.S3.Arith.Lattices.Klartag.Completion.Theorem2
