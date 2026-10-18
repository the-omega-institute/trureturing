import D5.S3.ConceptDynamics.Coding.OriginalRoot.OriginalRootPeriod6Rows
import D5.S3.ConceptDynamics.Coding.OriginalRoot.OriginalRootPeriod6Time

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding

open CountedOrderTypeGyration (integerGyrationValue)
open CountedOrderTypeGyration.SignedSupport
  (prunedShard integerGyrationValue_eq_supportedEvaluator
    supportedEvaluator_eq_pruned prunedEvaluator_eq_shards)
open ResetQ4LocalizedGyrationCharacter (Gamma gamma originalAdjacency onePlusSignedFactor
  gamma_time_signed_evaluation gamma_onePlus_signed_evaluation)
open scoped BigOperators Matrix

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 100000 in
theorem gamma_time_value :
    Multiplicative.toAdd
        (Gamma ResetQ4OriginalLocalizedCubes.time) = (0 : ZMod 3) := by
  have hR : ∀ i j : Fin 8,
      originalAdjacency i j = 0 ∨ originalAdjacency i j = 1 := by decide
  have hS : ∀ i j : Fin 8,
      (1 : Matrix (Fin 8) (Fin 8) ℤ) i j = -1 ∨
        (1 : Matrix (Fin 8) (Fin 8) ℤ) i j = 0 ∨
          (1 : Matrix (Fin 8) (Fin 8) ℤ) i j = 1 := by decide
  have h3Shard (i : Fin 8) :
      prunedShard 2 originalAdjacency (1 : Matrix (Fin 8) (Fin 8) ℤ) i =
        (![-4,0,0,0,0,0,0,0] : Fin 8 → ℤ) i := by
    fin_cases i <;> decide +kernel
  have h6Shard (i : Fin 8) :
      prunedShard 5 originalAdjacency (1 : Matrix (Fin 8) (Fin 8) ℤ) i =
        (![-35,0,0,0,0,0,0,0] : Fin 8 → ℤ) i := by
    fin_cases i <;> rw [prunedShard_time_eq_fast6] <;> decide +kernel
  have h3 :
      integerGyrationValue 3 originalAdjacency 1 = -4 := by
    rw [integerGyrationValue_eq_supportedEvaluator 3 _ _ hR hS,
      supportedEvaluator_eq_pruned, prunedEvaluator_eq_shards 2]
    simp_rw [h3Shard]
    norm_num [Fin.sum_univ_succ]
  have h6 :
      integerGyrationValue 6 originalAdjacency 1 = -35 := by
    rw [integerGyrationValue_eq_supportedEvaluator 6 _ _ hR hS,
      supportedEvaluator_eq_pruned, prunedEvaluator_eq_shards 5]
    simp_rw [h6Shard]
    norm_num [Fin.sum_univ_succ]
  have hGamma : Multiplicative.toAdd (Gamma ResetQ4OriginalLocalizedCubes.time) =
      Multiplicative.toAdd (gamma 3 (by decide) ResetQ4OriginalLocalizedCubes.time) +
        Multiplicative.toAdd (gamma 6 (by decide) ResetQ4OriginalLocalizedCubes.time) := by
    simp [Gamma, map_mul]
  rw [hGamma, gamma_time_signed_evaluation, gamma_time_signed_evaluation, h3, h6]
  decide

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 100000 in
theorem gamma_onePlus_value :
    Multiplicative.toAdd
        (Gamma ResetQ4OriginalLocalizedCubes.onePlusTime) = (2 : ZMod 3) := by
  have hR : ∀ i j : Fin 8,
      (1 + originalAdjacency) i j = 0 ∨ (1 + originalAdjacency) i j = 1 := by decide
  have hS : ∀ i j : Fin 8,
      onePlusSignedFactor i j = -1 ∨ onePlusSignedFactor i j = 0 ∨
        onePlusSignedFactor i j = 1 := by decide
  have h3Shard (i : Fin 8) :
      prunedShard 2 (1 + originalAdjacency) onePlusSignedFactor i =
        (![(-1 : ℤ), -1, -1, -2, -1, -2, 0, 0] : Fin 8 → ℤ) i := by
    fin_cases i <;> decide +kernel
  have h6Shard (i : Fin 8) :
      prunedShard 5 (1 + originalAdjacency) onePlusSignedFactor i =
        (![(-31 : ℤ), -10, -8, 2, -5, 3, -4, 0] : Fin 8 → ℤ) i := by
    rw [prunedShard_onePlus_eq_split3]
    simp_rw [onePlusShardLeaf_eq_value]
    fin_cases i <;> decide +kernel
  have h3 :
      integerGyrationValue 3 (1 + originalAdjacency) onePlusSignedFactor = -8 := by
    rw [integerGyrationValue_eq_supportedEvaluator 3 _ _ hR hS,
      supportedEvaluator_eq_pruned, prunedEvaluator_eq_shards 2]
    simp_rw [h3Shard]
    norm_num [Fin.sum_univ_succ]
  have h6 :
      integerGyrationValue 6 (1 + originalAdjacency) onePlusSignedFactor = -53 := by
    rw [integerGyrationValue_eq_supportedEvaluator 6 _ _ hR hS,
      supportedEvaluator_eq_pruned, prunedEvaluator_eq_shards 5]
    simp_rw [h6Shard]
    norm_num [Fin.sum_univ_succ]
  have hGamma : Multiplicative.toAdd (Gamma ResetQ4OriginalLocalizedCubes.onePlusTime) =
      Multiplicative.toAdd (gamma 3 (by decide) ResetQ4OriginalLocalizedCubes.onePlusTime) +
        Multiplicative.toAdd (gamma 6 (by decide) ResetQ4OriginalLocalizedCubes.onePlusTime) := by
    simp [Gamma, map_mul]
  rw [hGamma, gamma_onePlus_signed_evaluation, gamma_onePlus_signed_evaluation, h3, h6]
  decide

theorem gamma_factor_value (i j : Fin 3)
    (v : ResetQ4OriginalLocalizedCubes.Centralizer) :
    Multiplicative.toAdd
        (Gamma (ResetQ4OriginalLocalizedCubes.time ^ (i : ℕ) *
          ResetQ4OriginalLocalizedCubes.onePlusTime ^ (j : ℕ) * v ^ 3)) =
      (j.val : ZMod 3) * 2 := by
  simp only [map_mul, toAdd_mul, map_pow, toAdd_pow]
  rw [gamma_time_value, gamma_onePlus_value]
  have hchar : (3 : ZMod 3) = 0 := by decide
  simp [nsmul_eq_mul, hchar]

end D5.S3.ConceptDynamics.Coding
