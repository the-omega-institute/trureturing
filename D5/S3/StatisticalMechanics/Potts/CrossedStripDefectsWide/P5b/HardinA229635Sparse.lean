/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Sparse
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Sparse
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.initial_power,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.step_checks,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.residual_entries,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.initial_readout,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.image_entries
   digest: Agreement of sparse integer iteration with the certified width-six matrix. -/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Transfer
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635SparseCheck0
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635SparseCheck1
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635SparseCheck2
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635SparseCheck3

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sparse

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

open scoped BigOperators
open HardinA229635State HardinA229635Transfer HardinA229635SparseData

private theorem transpose_correct (j : State) : incomingClasses j = transposeLists j := by
  by_cases h0 : j.val < 32
  · let k : Fin 32 := ⟨j.val - 0, by omega⟩
    have hj : (⟨0 + k.val, by omega⟩ : State) = j := Fin.ext (by dsimp [k]; omega)
    simpa only [hj] using HardinA229635SparseCheck0.exact_transpose k
  by_cases h1 : j.val < 64
  · let k : Fin 32 := ⟨j.val - 32, by omega⟩
    have hj : (⟨32 + k.val, by omega⟩ : State) = j := Fin.ext (by dsimp [k]; omega)
    simpa only [hj] using HardinA229635SparseCheck1.exact_transpose k
  by_cases h2 : j.val < 96
  · let k : Fin 32 := ⟨j.val - 64, by omega⟩
    have hj : (⟨64 + k.val, by omega⟩ : State) = j := Fin.ext (by dsimp [k]; omega)
    simpa only [hj] using HardinA229635SparseCheck2.exact_transpose k
  let k : Fin 31 := ⟨j.val - 96, by omega⟩
  have hj : (⟨96 + k.val, by omega⟩ : State) = j := Fin.ext (by dsimp [k]; omega)
  simpa only [hj] using HardinA229635SparseCheck3.exact_transpose k

private theorem old_weights : ∀ (i : Fin 31) (j : State),
    (((outgoingClasses (i.castAdd 96)).count j : ℕ) : ℤ) = T (i.castAdd 96) j := by
  decide +kernel

private theorem outward_weight (i j : State) :
    ((outgoingClasses i).count j : ℤ) = T i j := by
  refine Fin.addCases (m := 31) (n := 96) (fun k => old_weights k j) ?_ i
  intro k
  rw [outgoingClasses, T, Fin.addCases_right, Fin.addCases_right]

private theorem inward_count (i j : State) :
    (incomingClasses j).count i = (outgoingClasses i).count j := by
  rw [transpose_correct, transposeLists, List.count_flatten, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply, List.count_replicate, beq_iff_eq]
  exact Finset.sum_ite_eq' _ _ _ |>.trans (by simp)

private theorem sum_with_multiplicities (adj : List State) (v : State → ℤ) :
    (adj.map v).sum = ∑ i : State, v i * (adj.count i : ℤ) := by
  induction adj with
  | nil => simp
  | cons j adj ih =>
    simp only [List.map_cons, List.sum_cons, List.count_cons, Nat.cast_add,
      beq_iff_eq, mul_add, Finset.sum_add_distrib]
    rw [ih]
    have he : (∑ i : State, v i * (↑(if j = i then 1 else 0 : ℕ) : ℤ)) = v j := by
      simp [mul_ite]
    rw [he, add_comm]

theorem step_correct (v : State → ℤ) : step v = Matrix.vecMul v T := by
  funext j
  change ((incomingClasses j).map v).sum = ∑ i : State, v i * T i j
  rw [sum_with_multiplicities]
  simp only [inward_count, outward_weight]

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sparse
