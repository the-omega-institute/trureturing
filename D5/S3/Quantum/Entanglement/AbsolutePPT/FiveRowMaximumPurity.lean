/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowMaximumPurity
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/FiveRowMaximumPurity
   mirror-E: none(waiver:source-only-assembly)
   anchors: []
   utility: none
   digest: Full arbitrary-density five-row APPT maximum assembly with actual mixed-density attainers for every n >= 5. -/

/-
The five-row purity bound applies to arbitrary complex positive-semidefinite,
trace-one APPT matrices.  The existing `diagonal_spectral_reduction` supplies
one ordered spectrum and its actual APPT diagonal; the P1/P2 upper consumers
use that same spectrum in the respective ranges 5 <= n <= 18 and 19 <= n.
The equality witnesses are the normalized-ray and contraction mixed densities,
provided by `normalized_ray (Pi.single ...)` and `five_row_attainment`.

The construction composes symbolic implications for arbitrary spectra and
densities with existing attainers; it introduces no new finite computation.
This is the rationale for utility: none.

proof_shape: result: content when the same-delivery small-n helpers are
inlined relative to the immutable baseline. Its outer assembly script is
bind-only relative to the immediate physical-upper and attainment APIs.
The live small-n path is FiveRowP1Physical.top_three_moment through pool_hyp,
actual_to_hyp and physical_upper. The original upper clause consumes that
tail estimate; neither an extra binding theorem nor an attainer supplies it.
-/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity
import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Physical
import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Physical
import D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

open Matrix
open scoped BigOperators ComplexOrder
open D5.S3.Quantum.Entanglement.AbsolutePPT
open D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment
open D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Physical
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Physical
open D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowMaximumPurity
noncomputable section

/-- The two exact branch values, split at the 18/19 boundary.
The product is formed in `Nat` before its coercion to `Real`. -/
def bound (n : ℕ) : ℝ :=
  if n ≤ 18 then
    ((((5*n : ℕ) : ℝ) + 8) / ((((5*n : ℕ) : ℝ) + 2)^2))
  else
    5 / (24*(n : ℝ))

/-- Universal purity bound and actual attainment for each n >= 5. -/
def claim : Prop :=
  ∀ n : ℕ, 5 ≤ n →
    (∀ rho : Matrix (Fin 5 × Fin n) (Fin 5 × Fin n) ℂ,
      rho.PosSemidef → rho.trace = 1 → APPT rho →
        (rho * rho).trace.re ≤ bound n) ∧
    (∃ rho : Matrix (Fin 5 × Fin n) (Fin 5 × Fin n) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
        (rho * rho).trace.re = bound n)

/-- A single ordered-spectrum reduction gives the two upper branches;
the normalized-ray and contraction densities attain the respective values. -/
theorem result : claim := by
  intro n hn
  constructor
  · intro rho hrho htrace happt
    let e : (Fin 5 × Fin n) ≃ Fin (5*n) := finProdFinEquiv
    obtain ⟨l, ho, hnonneg, hmass, hdiag, hpur⟩ :=
      QuadbitQuintitMaximumPurity.diagonal_spectral_reduction e rho hrho htrace happt
    rw [hpur]
    by_cases hsmall : n ≤ 18
    · rw [bound, if_pos hsmall]
      have hb := FiveRowP1Physical.physical_upper n hn hsmall e l ho hnonneg hdiag
      simpa only [hmass, one_pow, mul_one] using hb
    · have hn19 : 19 ≤ n := by omega
      rw [bound, if_neg hsmall]
      have hb := FiveRowP2Physical.physical_upper_from_exact_bridges
        n hn19 e l ho hnonneg hdiag
      simpa only [hmass, one_pow, mul_one] using hb
  · by_cases hsmall : n ≤ 18
    · letI : NeZero n := ⟨by omega⟩
      let v : Fin 5 × Fin n → ℂ := Pi.single (0, 0) 1
      have hv : star v ⬝ᵥ v = (1 : ℂ) := by
        classical
        simp [v, dotProduct, Pi.single_apply]
      obtain ⟨hd, ht, ha, hp⟩ :=
        QuadbitQuintitMaximumPurity.normalized_ray v hv
      refine ⟨QuadbitQuintitMaximumPurity.normalizedRay v, ⟨hd, ht⟩, ha, ?_⟩
      simpa only [bound, if_pos hsmall] using hp
    · have hn19 : 19 ≤ n := by omega
      obtain ⟨_hRank, hd, ht, ha, hp⟩ :=
        ContractionAttainment.five_row_attainment n (by omega : 0 < n)
      refine ⟨ContractionAttainment.fiveRowDensity n, ⟨hd, ht⟩, ha, ?_⟩
      simpa only [bound, if_neg hsmall] using hp


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowMaximumPurity
