/- GID: D5/S3/Combinatorics/Matroids/IntegralWeightSplitting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/IntegralWeightSplitting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native finite matroid exchange inequalities imply integral global base optimality. -/

import D5.S3.Combinatorics.Matroids.NativeWeightedBaseRankSaturation
import D5.S3.Combinatorics.Graph.LayeredCirculation.SupplierDual
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Matroids.IntegralWeightSplitting

open scoped BigOperators
open Set Matroid

universe u
variable {E : Type u} [Finite E]

/-- The actual integral finite sum over a set of carrier elements. -/
noncomputable def weightSum (q : E → ℤ) (B : Set E) : ℤ :=
  ∑ e ∈ B.toFinite.toFinset, q e

/-- Single-element exchange optimality implies optimality against every native base. -/
theorem exchange_local_is_global_minimum (M : Matroid E) (q : E → ℤ)
    {B : Set E} (hB : M.IsBase B)
    (hlocal : ∀ b ∈ B, ∀ e ∈ M.E \ B,
      M.IsBase (insert e (B \ {b})) → q b ≤ q e) :
    ∀ C, M.IsBase C → weightSum q B ≤ weightSum q C := by
  classical
  let r : E → ℝ := fun e => (q e : ℝ)
  have hsat : ∀ t : ℝ,
      (B ∩ NativeWeightedBaseRankSaturation.lowerWeightSet M r t).ncard =
        (M.eRk (NativeWeightedBaseRankSaturation.lowerWeightSet M r t)).toNat := by
    intro t
    let X := NativeWeightedBaseRankSaturation.lowerWeightSet M r t
    have hXE : X ⊆ M.E := fun _ h => h.1
    have hI : M.Indep (B ∩ X) := hB.indep.inter_right X
    have hBasis : M.IsBasis (B ∩ X) X := by
      by_contra hnot
      obtain ⟨J, hJ⟩ := M.exists_isBasis X hXE
      obtain ⟨e, heJ, heI⟩ :=
        hI.exists_insert_of_not_isBasis inter_subset_right hnot hJ
      have heX : e ∈ X := hJ.subset heJ.1
      have heNotB : e ∉ B := fun heB => heJ.2 ⟨heB, heX⟩
      obtain ⟨b, hb, hex⟩ :=
        D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis.exchange_base_over_independent_subset
          hB heNotB heI
      have hbe : r b ≤ r e := by
        exact_mod_cast hlocal b hb.1 e ⟨heX.1, heNotB⟩ hex
      have hbX : b ∈ X := ⟨hB.subset_ground hb.1, hbe.trans heX.2⟩
      exact hb.2 ⟨hb.1, hbX⟩
    rw [ncard_def, hBasis.encard_eq_eRk]
  have hmin := ((NativeWeightedBaseRankSaturation.native_weighted_base_rank_saturation
    M r).2 B hB).mpr hsat
  intro C hC
  have h := hmin C hC
  dsimp [NativeWeightedBaseRankSaturation.baseWeight, r] at h
  unfold weightSum
  exact_mod_cast h

#print axioms exchange_local_is_global_minimum

end D5.S3.Combinatorics.Matroids.IntegralWeightSplitting
