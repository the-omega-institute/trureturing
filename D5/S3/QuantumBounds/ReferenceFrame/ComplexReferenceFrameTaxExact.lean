/- GID: D5/S3/QuantumBounds/ReferenceFrame/ComplexReferenceFrameTaxExact
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/ReferenceFrame/ComplexReferenceFrameTaxExact
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Package the exact complex reference-frame fidelity, tax, and paired top space. -/

import D5.S3.QuantumBounds.ReferenceFrame.Complexification

namespace D5.S3.QuantumBounds.ReferenceFrame.ComplexReferenceFrameTaxExact

open scoped BigOperators
open scoped Matrix
open D5.S3.QuantumBounds.ReferenceFrameTax
open D5.S3.QuantumBounds.ReferenceFrame.ChannelFidelityBridge
open D5.S3.QuantumBounds.ReferenceFrame.Complexification

/-!
Library search found exact complex-amplitude declarations for the fidelity reduction, sharp
optimum, paired top eigenspace, and flat state. This theorem only packages those declarations.
The lower bound on the ladder length is necessary because the one-level flat tax is one.
-/

/-- The finite exchange model has the exact complex-amplitude reference-frame tax. -/
theorem complex_reference_frame_tax_exact (N : ℕ) (hN : 2 ≤ N) :
    (exchangeUnitary N)ᴴ * exchangeUnitary N = 1 ∧
    (∀ x : JointBasis N, totalExcitation (exchangeBasis x) = totalExcitation x) ∧
    (∀ c : Fin N → ℂ,
      (1 / 4 : ℝ) * (∑ r : Fin N,
          (let K : Matrix (Fin 2) (Fin 2) ℂ := (fun sOut sIn ↦ ∑ m : Fin N,
              exchangeUnitary N (sOut, r) (sIn, m) * c m);
            Complex.normSq (Matrix.trace (bitFlipᴴ * K)))) =
        ∑ m : Fin N,
          Complex.normSq
            (((if _h : 0 < m.val then
                c ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ else 0) +
              (if _h : m.val + 1 < N then c ⟨m.val + 1, _h⟩ else 0)) / 2)) ∧
    IsGreatest
      {q : ℝ | ∃ c : Fin N → ℂ,
        (∑ i : Fin N, Complex.normSq (c i)) = 1 ∧
        (1 / 4 : ℝ) * (∑ r : Fin N,
            (let K : Matrix (Fin 2) (Fin 2) ℂ := (fun sOut sIn ↦ ∑ m : Fin N,
                exchangeUnitary N (sOut, r) (sIn, m) * c m);
              Complex.normSq (Matrix.trace (bitFlipᴴ * K)))) = q}
      (Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2) ∧
    1 - Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 =
      Real.sin (Real.pi / (N + 1 : ℝ)) ^ 2 ∧
    1 - (1 / 4 : ℝ) * (∑ r : Fin N,
        (let K : Matrix (Fin 2) (Fin 2) ℂ := (fun sOut sIn ↦ ∑ m : Fin N,
            exchangeUnitary N (sOut, r) (sIn, m) *
              ((1 / Real.sqrt (N : ℝ) : ℝ) : ℂ));
          Complex.normSq (Matrix.trace (bitFlipᴴ * K)))) =
      3 / (2 * (N : ℝ)) ∧
    (let average : Module.End ℂ (Fin N → ℂ) :=
      { toFun := fun c m ↦
          ((if _h : 0 < m.val then
              c ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ else 0) +
            (if _h : m.val + 1 < N then c ⟨m.val + 1, _h⟩ else 0)) / 2
        map_add' := by
          intro c d
          funext m
          by_cases hl : 0 < m.val <;> by_cases hr : m.val + 1 < N <;>
            simp [hl, hr] <;> ring
        map_smul' := by
          intro a c
          funext m
          by_cases hl : 0 < m.val <;> by_cases hr : m.val + 1 < N <;>
            simp [hl, hr, Pi.smul_apply, smul_eq_mul] <;> ring };
      Module.finrank ℂ
        (Module.End.eigenspace (average.comp average)
          (Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 : ℂ)) = 2) := by
  refine ⟨exchange_unitary_is_unitary N, exchange_basis_preserves_total_excitation,
    ?_, complex_tax_optimum_eq_real_optimum N (by omega),
    reference_frame_tax_optimal_identity N (by omega), flat_tax_complex N hN,
    complex_top_eigenspace_finrank N hN⟩
  intro c
  exact complex_entanglement_fidelity_eq_nearest_neighbor_quadratic c

#print axioms complex_reference_frame_tax_exact

end D5.S3.QuantumBounds.ReferenceFrame.ComplexReferenceFrameTaxExact
