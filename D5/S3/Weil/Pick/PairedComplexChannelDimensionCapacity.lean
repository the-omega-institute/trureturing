/- GID: D5/S3/Weil/Pick/PairedComplexChannelDimensionCapacity
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/PairedComplexChannelDimensionCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Paired complex channels have two complex dimensions of capacity per finite sensor. -/

import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/- Library-search audit trail (2026-08-30):
   * Repository searches for paired-channel finrank, dimension capacity, and
     blind-direction bounds found no exact D5 owner.
   * Frozen finite-observability and weighted-kernel nodes identify zero-energy
     directions, but do not compute the two-complex-coordinate capacity of a
     finite paired sensor family.
   * Pinned Mathlib supplies `Module.finrank_pi_fintype`,
     `LinearMap.finrank_le_finrank_of_injective`, submodule finrank monotonicity,
     rank-nullity, and `Function.not_injective_iff`; these are applied directly. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Pick.PairedComplexChannelDimensionCapacity

/-- A finite paired complex sensor has two scalar complex coordinates per
index. -/
def pairedComplexChannelCapacity (Index : Type*) [Fintype Index] : Nat :=
  Fintype.card Index * 2

private theorem paired_complex_channel_codomain_finrank
    (Index : Type*) [Fintype Index] :
    Module.finrank ℂ (Index -> ℂ × ℂ) =
      pairedComplexChannelCapacity Index := by
  simpa [pairedComplexChannelCapacity] using
    (Module.finrank_pi_fintype
      (R := ℂ) (M := fun _ : Index => ℂ × ℂ))

/-- An injective observation into finitely many paired complex scalar channels
cannot have more source dimensions than the channel capacity. More generally,
the kernel dimension is at least the source dimension minus that capacity, and
strict dimension excess produces an explicit nonzero blind direction. -/
theorem paired_complex_channel_dimension_capacity
    {Index V : Type*} [Fintype Index]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (observation : V →ₗ[ℂ] (Index -> ℂ × ℂ)) :
    (Function.Injective observation ->
        Module.finrank ℂ V <= pairedComplexChannelCapacity Index) ∧
      (Module.finrank ℂ V - pairedComplexChannelCapacity Index <=
        Module.finrank ℂ (LinearMap.ker observation)) ∧
      (pairedComplexChannelCapacity Index < Module.finrank ℂ V ->
        ∃ blind : V, blind ≠ 0 ∧ observation blind = 0) := by
  classical
  have hcodomain :
      Module.finrank ℂ (Index -> ℂ × ℂ) =
        pairedComplexChannelCapacity Index :=
    paired_complex_channel_codomain_finrank Index
  have hinjectiveBound :
      Function.Injective observation ->
        Module.finrank ℂ V <= pairedComplexChannelCapacity Index := by
    intro hinjective
    calc
      Module.finrank ℂ V <= Module.finrank ℂ (Index -> ℂ × ℂ) :=
        LinearMap.finrank_le_finrank_of_injective hinjective
      _ = pairedComplexChannelCapacity Index := hcodomain
  have hrangeBound :
      Module.finrank ℂ (LinearMap.range observation) <=
        pairedComplexChannelCapacity Index := by
    calc
      Module.finrank ℂ (LinearMap.range observation) <=
          Module.finrank ℂ (Index -> ℂ × ℂ) :=
        (LinearMap.range observation).finrank_le
      _ = pairedComplexChannelCapacity Index := hcodomain
  have hrankNullity :
      Module.finrank ℂ (LinearMap.range observation) +
          Module.finrank ℂ (LinearMap.ker observation) =
        Module.finrank ℂ V :=
    observation.finrank_range_add_finrank_ker
  have hnullity :
      Module.finrank ℂ V - pairedComplexChannelCapacity Index <=
        Module.finrank ℂ (LinearMap.ker observation) := by
    omega
  refine ⟨hinjectiveBound, hnullity, ?_⟩
  intro hexcess
  have hnotInjective : Not (Function.Injective observation) := by
    intro hinjective
    exact (not_lt_of_ge (hinjectiveBound hinjective)) hexcess
  rcases Function.not_injective_iff.mp hnotInjective with
    ⟨first, second, hsame, hdifferent⟩
  refine ⟨first - second, sub_ne_zero.mpr hdifferent, ?_⟩
  rw [map_sub, hsame, sub_self]

#print axioms paired_complex_channel_dimension_capacity

end D5.S3.Weil.Pick.PairedComplexChannelDimensionCapacity
