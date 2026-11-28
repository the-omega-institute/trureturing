/- GID: D5/S3/Combinatorics/Turnpike/PrunedSingletonCutPair12
   generality: G
   mirror-B: none(waiver:covered-by-pruned-singleton-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Singleton cuts for coordinate pair (1, 2) -/

module

public import D5.S3.Combinatorics.Turnpike.PrunedSingletonCutData

/-! Omega original.
# Singleton cuts for coordinate pair (1, 2)

Each of the 84 triangle shards checks all label pairs for this coordinate pair.
The pair coverage theorem is consumed by the complete cut aggregator.
-/
@[expose] public section
namespace Omega.Turnpike.PrunedSingletonCutCertificate
open Omega.Turnpike
open scoped BigOperators
noncomputable section

private theorem cut_012_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,2),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_013_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,3),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_014_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,4),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_015_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_016_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_017_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_018_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_023_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,3),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_024_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,4),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_025_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_026_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_027_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_028_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_034_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,4),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_035_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_036_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_037_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_038_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_045_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_046_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_047_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_048_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_056_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_057_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_058_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_067_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,6,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_068_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,6,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_078_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,7,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_123_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,3),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_124_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,4),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_125_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_126_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_127_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_128_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_134_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,4),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_135_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_136_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_137_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_138_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_145_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_146_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_147_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_148_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_156_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_157_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_158_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_167_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,6,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_168_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,6,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_178_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,7,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_234_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,4),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_235_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_236_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_237_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_238_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_245_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_246_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_247_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_248_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_256_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_257_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_258_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_267_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,6,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_268_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,6,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_278_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,7,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_345_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_346_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_347_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_348_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_356_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_357_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_358_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_367_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,6,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_368_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,6,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_378_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,7,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_456_12 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_457_12 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_458_12 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_467_12 : ∀ a b : Fin 20,
    CutCheck ⟨(4,6,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_468_12 : ∀ a b : Fin 20,
    CutCheck ⟨(4,6,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_478_12 : ∀ a b : Fin 20,
    CutCheck ⟨(4,7,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_567_12 : ∀ a b : Fin 20,
    CutCheck ⟨(5,6,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_568_12 : ∀ a b : Fin 20,
    CutCheck ⟨(5,6,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_578_12 : ∀ a b : Fin 20,
    CutCheck ⟨(5,7,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_678_12 : ∀ a b : Fin 20,
    CutCheck ⟨(6,7,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel

theorem cuts_12 : ∀ τ ∈ triangleCover, ∀ a b : Fin 20,
    CutCheck τ 1 2 0 a b := by
  simp only [triangleCover, List.forall_mem_cons]
  exact ⟨cut_012_12,
    cut_013_12,
    cut_014_12,
    cut_015_12,
    cut_016_12,
    cut_017_12,
    cut_018_12,
    cut_023_12,
    cut_024_12,
    cut_025_12,
    cut_026_12,
    cut_027_12,
    cut_028_12,
    cut_034_12,
    cut_035_12,
    cut_036_12,
    cut_037_12,
    cut_038_12,
    cut_045_12,
    cut_046_12,
    cut_047_12,
    cut_048_12,
    cut_056_12,
    cut_057_12,
    cut_058_12,
    cut_067_12,
    cut_068_12,
    cut_078_12,
    cut_123_12,
    cut_124_12,
    cut_125_12,
    cut_126_12,
    cut_127_12,
    cut_128_12,
    cut_134_12,
    cut_135_12,
    cut_136_12,
    cut_137_12,
    cut_138_12,
    cut_145_12,
    cut_146_12,
    cut_147_12,
    cut_148_12,
    cut_156_12,
    cut_157_12,
    cut_158_12,
    cut_167_12,
    cut_168_12,
    cut_178_12,
    cut_234_12,
    cut_235_12,
    cut_236_12,
    cut_237_12,
    cut_238_12,
    cut_245_12,
    cut_246_12,
    cut_247_12,
    cut_248_12,
    cut_256_12,
    cut_257_12,
    cut_258_12,
    cut_267_12,
    cut_268_12,
    cut_278_12,
    cut_345_12,
    cut_346_12,
    cut_347_12,
    cut_348_12,
    cut_356_12,
    cut_357_12,
    cut_358_12,
    cut_367_12,
    cut_368_12,
    cut_378_12,
    cut_456_12,
    cut_457_12,
    cut_458_12,
    cut_467_12,
    cut_468_12,
    cut_478_12,
    cut_567_12,
    cut_568_12,
    cut_578_12,
    cut_678_12, List.forall_mem_nil _⟩

end
end Omega.Turnpike.PrunedSingletonCutCertificate
