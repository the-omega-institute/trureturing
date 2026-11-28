/- GID: D5/S3/Combinatorics/Turnpike/PrunedSingletonCutPair01
   generality: G
   mirror-B: none(waiver:covered-by-pruned-singleton-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Singleton cuts for coordinate pair (0, 1) -/

module

public import D5.S3.Combinatorics.Turnpike.PrunedSingletonCutData

/-! Omega original.
# Singleton cuts for coordinate pair (0, 1)

Each of the 84 triangle shards checks all label pairs for this coordinate pair.
The pair coverage theorem is consumed by the complete cut aggregator.
-/
@[expose] public section
namespace Omega.Turnpike.PrunedSingletonCutCertificate
open Omega.Turnpike
open scoped BigOperators
noncomputable section

private theorem cut_012_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,2),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_013_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,3),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_014_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,4),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_015_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_016_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_017_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_018_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_023_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,3),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_024_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,4),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_025_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_026_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_027_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_028_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_034_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,4),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_035_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_036_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_037_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_038_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_045_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_046_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_047_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_048_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_056_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_057_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_058_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_067_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,6,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_068_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,6,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_078_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,7,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_123_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,3),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_124_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,4),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_125_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_126_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_127_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_128_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_134_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,4),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_135_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_136_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_137_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_138_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_145_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_146_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_147_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_148_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_156_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_157_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_158_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_167_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,6,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_168_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,6,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_178_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,7,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_234_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,4),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_235_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_236_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_237_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_238_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_245_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_246_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_247_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_248_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_256_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_257_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_258_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_267_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,6,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_268_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,6,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_278_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,7,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_345_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_346_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_347_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_348_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_356_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_357_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_358_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_367_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,6,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_368_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,6,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_378_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,7,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_456_01 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_457_01 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_458_01 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_467_01 : ∀ a b : Fin 20,
    CutCheck ⟨(4,6,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_468_01 : ∀ a b : Fin 20,
    CutCheck ⟨(4,6,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_478_01 : ∀ a b : Fin 20,
    CutCheck ⟨(4,7,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_567_01 : ∀ a b : Fin 20,
    CutCheck ⟨(5,6,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_568_01 : ∀ a b : Fin 20,
    CutCheck ⟨(5,6,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_578_01 : ∀ a b : Fin 20,
    CutCheck ⟨(5,7,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_678_01 : ∀ a b : Fin 20,
    CutCheck ⟨(6,7,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel

theorem cuts_01 : ∀ τ ∈ triangleCover, ∀ a b : Fin 20,
    CutCheck τ 0 1 2 a b := by
  simp only [triangleCover, List.forall_mem_cons]
  exact ⟨cut_012_01,
    cut_013_01,
    cut_014_01,
    cut_015_01,
    cut_016_01,
    cut_017_01,
    cut_018_01,
    cut_023_01,
    cut_024_01,
    cut_025_01,
    cut_026_01,
    cut_027_01,
    cut_028_01,
    cut_034_01,
    cut_035_01,
    cut_036_01,
    cut_037_01,
    cut_038_01,
    cut_045_01,
    cut_046_01,
    cut_047_01,
    cut_048_01,
    cut_056_01,
    cut_057_01,
    cut_058_01,
    cut_067_01,
    cut_068_01,
    cut_078_01,
    cut_123_01,
    cut_124_01,
    cut_125_01,
    cut_126_01,
    cut_127_01,
    cut_128_01,
    cut_134_01,
    cut_135_01,
    cut_136_01,
    cut_137_01,
    cut_138_01,
    cut_145_01,
    cut_146_01,
    cut_147_01,
    cut_148_01,
    cut_156_01,
    cut_157_01,
    cut_158_01,
    cut_167_01,
    cut_168_01,
    cut_178_01,
    cut_234_01,
    cut_235_01,
    cut_236_01,
    cut_237_01,
    cut_238_01,
    cut_245_01,
    cut_246_01,
    cut_247_01,
    cut_248_01,
    cut_256_01,
    cut_257_01,
    cut_258_01,
    cut_267_01,
    cut_268_01,
    cut_278_01,
    cut_345_01,
    cut_346_01,
    cut_347_01,
    cut_348_01,
    cut_356_01,
    cut_357_01,
    cut_358_01,
    cut_367_01,
    cut_368_01,
    cut_378_01,
    cut_456_01,
    cut_457_01,
    cut_458_01,
    cut_467_01,
    cut_468_01,
    cut_478_01,
    cut_567_01,
    cut_568_01,
    cut_578_01,
    cut_678_01, List.forall_mem_nil _⟩

end
end Omega.Turnpike.PrunedSingletonCutCertificate
