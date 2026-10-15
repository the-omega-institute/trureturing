/- GID: D5/S3/VertexAlgebra/OriginalZeroChargeBrstAction
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/OriginalZeroChargeBrstAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original normal-ordered ghost charge on the complete native low-energy support. -/

import D5.S3.VertexAlgebra.OriginalZeroChargeEnergyBasis

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalZeroChargeBrstAction

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraConformal
  LatticeBcGhostBrstCharge BcGhostFockSupport BcGhostBrstSupport
  OriginalZeroChargeEnergySector OriginalZeroChargeEnergyBasis
open scoped BigOperators TensorProduct

noncomputable section

def ghostDoubleSum (ghost : Fock ℂ) : Fock ℂ :=
  ∑ mode ∈ modeInterval ghost, ∑ row ∈ rowInterval ghost,
    (mode - row : ℂ) • expanded ghost (mode, row)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
theorem ghostDoubleSum_nonpositive (subset : Finset ℕ)
    (nonpositive : BcGhostLZeroSpectrum.energy subset ≤ 0) :
    ghostDoubleSum (Finsupp.single subset 1) =
      if subset = {3} then (4 : ℂ) • Finsupp.single {1, 5} 1
      else if subset = {1} then (2 : ℂ) • Finsupp.single {1, 3} 1 else 0 := by
  have alternatives := (ghost_nonpositive_classification subset).mp nonpositive
  rcases alternatives with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num (config := { maxSteps := 2000000 })
      [ghostDoubleSum, modeInterval, rowInterval, bound, occupied,
      Int.Icc_eq_finset_map, Int.toNat, Finset.sum_map, Finset.sum_range_succ,
      expanded, normalPair, b, c, create, annihilate,
      Finsupp.linearCombination_single, createBasis, annihilateBasis, sign,
      LinearMap.comp_apply, Finsupp.smul_single, Finset.filter_insert,
      Finset.filter_singleton]
  all_goals norm_num [Finset.erase_insert, Finset.erase_singleton, Finset.filter_insert,
    Finset.filter_singleton, Finset.insert_comm,
    ← Finsupp.single_add,
    show ({5, 1} : Finset ℕ) = {1, 5} from by decide,
    show ({3, 1} : Finset ℕ) = {1, 3} from by decide,
    show ({1, 5, 3} : Finset ℕ) = {1, 3, 5} from by decide,
    show ({1, 5} : Finset ℕ).erase 5 = {1} from by decide,
    show ({1, 3} : Finset ℕ) ≠ {1} from by decide,
    show ({1, 5} : Finset ℕ) ≠ {3} from by decide,
    show ({1, 5} : Finset ℕ) ≠ {1} from by decide,
    show ({1, 3, 5} : Finset ℕ) ≠ {3} from by decide,
    show ({1, 3, 5} : Finset ℕ) ≠ {1} from by decide]

theorem Q_tmul_split (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (matter : Carrier D) (ghost : Fock ℂ) :
    Q D H (matter ⊗ₜ[ℂ] ghost) =
      (∑ᶠ mode : ℤ, sugawaraMode D H mode matter ⊗ₜ[ℂ] c (-mode) ghost) +
        (2 : ℂ)⁻¹ • (matter ⊗ₜ[ℂ] ghostDoubleSum ghost) := by
  have outerFinite := BcGhostStressTails.outer_has_finite_support ghost
  have ghostFinite : Function.HasFiniteSupport (fun mode : ℤ =>
      (2 : ℂ)⁻¹ • (matter ⊗ₜ[ℂ] BcGhostStressTails.outerNormalPair mode ghost)) :=
    outerFinite.fun_comp (g := fun value : Fock ℂ => (2 : ℂ)⁻¹ • (matter ⊗ₜ[ℂ] value))
      (by simp)
  have expansion (mode : ℤ) : A D H mode (matter ⊗ₜ[ℂ] ghost) =
      sugawaraMode D H mode matter ⊗ₜ[ℂ] c (-mode) ghost +
        (2 : ℂ)⁻¹ • (matter ⊗ₜ[ℂ] BcGhostStressTails.outerNormalPair mode ghost) := by
    by_cases normal : -1 ≤ mode <;>
      simp [A, N, M, G, C, BcGhostStressTails.outerNormalPair, normal]
  have matterFinite : Function.HasFiniteSupport
      (fun mode : ℤ => sugawaraMode D H mode matter ⊗ₜ[ℂ] c (-mode) ghost) := by
    have difference := (A_finite D H (matter ⊗ₜ[ℂ] ghost)).sub ghostFinite
    have familyEquality :
        ((fun mode : ℤ => A D H mode (matter ⊗ₜ[ℂ] ghost)) -
          fun mode : ℤ => (2 : ℂ)⁻¹ •
            (matter ⊗ₜ[ℂ] BcGhostStressTails.outerNormalPair mode ghost)) =
        (fun mode : ℤ => sugawaraMode D H mode matter ⊗ₜ[ℂ] c (-mode) ghost) := by
      funext mode
      change A D H mode (matter ⊗ₜ[ℂ] ghost) -
        (2 : ℂ)⁻¹ • (matter ⊗ₜ[ℂ] BcGhostStressTails.outerNormalPair mode ghost) = _
      rw [expansion, add_sub_cancel_right]
    rw [familyEquality] at difference
    exact difference
  have mapped := (TensorProduct.mk ℂ (Carrier D) (Fock ℂ) matter).toAddMonoidHom.map_finsum
    outerFinite
  simp only [LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply] at mapped
  change (∑ᶠ mode : ℤ, A D H mode (matter ⊗ₜ[ℂ] ghost)) = _
  simp_rw [expansion]
  rw [finsum_add_distrib matterFinite ghostFinite]
  congr 1
  rw [← smul_finsum', ← mapped, BcGhostBrstSupport.normalGhost_joint_finsum,
    BcGhostBrstSupport.expanded_joint_sum]
  · rfl
  · exact outerFinite.fun_comp (by simp : matter ⊗ₜ[ℂ] (0 : Fock ℂ) = 0)

#print axioms ghostDoubleSum_nonpositive
#print axioms Q_tmul_split

end
end D5.S3.VertexAlgebra.OriginalZeroChargeBrstAction
