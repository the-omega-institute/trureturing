/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeInverseIterateCutoff
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeInverseIterateCutoff
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform upper cutoff for the actual inverse-coordinate BPZ summands. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeInvertedIterate
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualInvolution
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualLinearField
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeResidueIterate
import D5.S3.VertexAlgebra.SignedFields.SignedFieldResidueLocality
import OmegaBuild.Commands

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeInverseIterateCutoff

open scoped BigOperators VertexOperator
open HalfFockSpectralFiberSource (actualInverse)
open LatticeSugawaraCurrents (sugawaraMode)
open P48qAllJetWickField (NativeStates nativeField)
open P48qNativeDualCoefficients (bpzTerm sourceLOne_pow_eq_zero_of_lt)
open P48qThirdTwistedField (State)
open P48qTwistedChargeAction (lattice)
open private gram_det_unit from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition

noncomputable section

local notation "L₀" => sugawaraMode lattice (actualInverse lattice) 0
local notation "L₁" => sugawaraMode lattice (actualInverse lattice) 1

/-- The inverse-coordinate BPZ summands have one actual upper mode cutoff.
Above the source weight, `L(1)^j a` vanishes.  For the finitely many remaining
source powers, the native coefficient is zero once its actual mode lies below
the Hahn order of its value on the fixed state.  The second conjunct records
the resulting finite BPZ sum itself. -/
theorem bpzConjugated_iterate_uniform_cutoff (a : NativeStates) (d : ℕ)
    (ha : L₀ a = (d : ℂ) • a) (v : State) :
    ∃ K : ℤ,
      (∀ k ≥ K, ∀ j : ℕ, bpzTerm a d k j v = 0) ∧
        (∀ k ≥ K,
          (-1 : ℂ) ^ d • ∑ j ∈ Finset.range (d + 1),
            (j.factorial : ℂ)⁻¹ • bpzTerm a d k j v = 0) := by
  let bound (j : ℕ) : ℤ :=
    -6 * (d : ℤ) + 3 * (j : ℤ) -
        ((HahnModule.of ℂ).symm (nativeField ((L₁ ^ j) a) v)).order + 1
  let bounds : Finset ℤ := (Finset.range (d + 1)).image bound
  have hBounds : bounds.Nonempty := by
    refine ⟨bound 0, ?_⟩
    exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩
  let K : ℤ := bounds.max' hBounds
  have hterm : ∀ k ≥ K, ∀ j : ℕ, bpzTerm a d k j v = 0 := by
    intro k hk j
    by_cases hj : d < j
    · have hz := sourceLOne_pow_eq_zero_of_lt a d ha j hj
      simp only [bpzTerm, hz, map_zero, Pi.zero_apply, LinearMap.zero_apply]
    · have hjd : j ≤ d := by omega
      have hmem : bound j ∈ bounds :=
        Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
      have hbound : bound j ≤ K := Finset.le_max' bounds (bound j) hmem
      have hmode : -k - 6 * (d : ℤ) + 3 * (j : ℤ) <
          ((HahnModule.of ℂ).symm (nativeField ((L₁ ^ j) a) v)).order := by
        dsimp only [bound] at hbound
        omega
      unfold bpzTerm
      apply VertexOperator.coeff_eq_zero_of_lt_order
      exact hmode
  refine ⟨K, hterm, ?_⟩
  intro k hk
  have hsum :
      (∑ j ∈ Finset.range (d + 1),
        (j.factorial : ℂ)⁻¹ • bpzTerm a d k j v) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hterm k hk j, smul_zero]
  rw [hsum, smul_zero]

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeInverseIterateCutoff
