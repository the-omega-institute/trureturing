/- GID: D5/S3/Combinatorics/Turnpike/PrunedSingletonCutPair02
   generality: G
   mirror-B: none(waiver:covered-by-pruned-singleton-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Singleton cuts for coordinate pair (0, 2) -/

module

public import D5.S3.Combinatorics.Turnpike.PrunedSingletonCutData

/-! Omega original.
# Singleton cuts for coordinate pair (0, 2)

Each of the 84 triangle shards checks all label pairs for this coordinate pair.
The pair coverage theorem is consumed by the complete cut aggregator.
-/
@[expose] public section
namespace Omega.Turnpike.PrunedSingletonCutCertificate
open Omega.Turnpike
open scoped BigOperators
noncomputable section

private theorem cut_012_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,2),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_013_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,3),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_014_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,4),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_015_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_016_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_017_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_018_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_023_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,3),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_024_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,4),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_025_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_026_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_027_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_028_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_034_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,4),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_035_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_036_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_037_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_038_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_045_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_046_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_047_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_048_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_056_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_057_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_058_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_067_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,6,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_068_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,6,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_078_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,7,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_123_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,3),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_124_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,4),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_125_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_126_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_127_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_128_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_134_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,4),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_135_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_136_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_137_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_138_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_145_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_146_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_147_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_148_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_156_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_157_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_158_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_167_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,6,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_168_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,6,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_178_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,7,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_234_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,4),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_235_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_236_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_237_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_238_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_245_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_246_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_247_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_248_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_256_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_257_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_258_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_267_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,6,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_268_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,6,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_278_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,7,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_345_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_346_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_347_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_348_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_356_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_357_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_358_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_367_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,6,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_368_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,6,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_378_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,7,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_456_02 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_457_02 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_458_02 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_467_02 : ∀ a b : Fin 20,
    CutCheck ⟨(4,6,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_468_02 : ∀ a b : Fin 20,
    CutCheck ⟨(4,6,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_478_02 : ∀ a b : Fin 20,
    CutCheck ⟨(4,7,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_567_02 : ∀ a b : Fin 20,
    CutCheck ⟨(5,6,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_568_02 : ∀ a b : Fin 20,
    CutCheck ⟨(5,6,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_578_02 : ∀ a b : Fin 20,
    CutCheck ⟨(5,7,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_678_02 : ∀ a b : Fin 20,
    CutCheck ⟨(6,7,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel

theorem cuts_02 : ∀ τ ∈ triangleCover, ∀ a b : Fin 20,
    CutCheck τ 0 2 1 a b := by
  simp only [triangleCover, List.forall_mem_cons]
  exact ⟨cut_012_02,
    cut_013_02,
    cut_014_02,
    cut_015_02,
    cut_016_02,
    cut_017_02,
    cut_018_02,
    cut_023_02,
    cut_024_02,
    cut_025_02,
    cut_026_02,
    cut_027_02,
    cut_028_02,
    cut_034_02,
    cut_035_02,
    cut_036_02,
    cut_037_02,
    cut_038_02,
    cut_045_02,
    cut_046_02,
    cut_047_02,
    cut_048_02,
    cut_056_02,
    cut_057_02,
    cut_058_02,
    cut_067_02,
    cut_068_02,
    cut_078_02,
    cut_123_02,
    cut_124_02,
    cut_125_02,
    cut_126_02,
    cut_127_02,
    cut_128_02,
    cut_134_02,
    cut_135_02,
    cut_136_02,
    cut_137_02,
    cut_138_02,
    cut_145_02,
    cut_146_02,
    cut_147_02,
    cut_148_02,
    cut_156_02,
    cut_157_02,
    cut_158_02,
    cut_167_02,
    cut_168_02,
    cut_178_02,
    cut_234_02,
    cut_235_02,
    cut_236_02,
    cut_237_02,
    cut_238_02,
    cut_245_02,
    cut_246_02,
    cut_247_02,
    cut_248_02,
    cut_256_02,
    cut_257_02,
    cut_258_02,
    cut_267_02,
    cut_268_02,
    cut_278_02,
    cut_345_02,
    cut_346_02,
    cut_347_02,
    cut_348_02,
    cut_356_02,
    cut_357_02,
    cut_358_02,
    cut_367_02,
    cut_368_02,
    cut_378_02,
    cut_456_02,
    cut_457_02,
    cut_458_02,
    cut_467_02,
    cut_468_02,
    cut_478_02,
    cut_567_02,
    cut_568_02,
    cut_578_02,
    cut_678_02, List.forall_mem_nil _⟩

end
end Omega.Turnpike.PrunedSingletonCutCertificate
