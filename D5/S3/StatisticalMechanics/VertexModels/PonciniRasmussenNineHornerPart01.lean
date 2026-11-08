/- GID: D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart01
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart01
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Data.Int.Basic]
   utility: kind=numeric-reduction; basis=refutes=gid:D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.claim; result=D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.result; claim=D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.claim
   digest: Four split integer Horner steps for the nine-strand certificate. -/
import D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenNineHornerData
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-! Exact integer data and finite kernel reduction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.style.longLine false

namespace D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner
private theorem step4_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step4_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step4_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step4_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step4_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step4_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step4_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step4_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step4_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step4_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step4_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step4_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step4_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step4_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step4_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step4_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step4_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step4_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step4_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step4_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step4_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step4_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step4_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step4_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step4_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step4_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step4_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step4_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step4_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step4_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step4_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step4_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step4_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step4_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step4_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step4_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step4_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step4_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step4_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step4_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step4_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step4_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step4_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step4_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step4_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step4_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step4_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step4_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step4_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step4_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step4_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step4_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step4_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step4_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step4_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step4_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step4_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step4_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step4_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step4_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step4_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step4_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step4_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step4_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 4) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step4_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 4) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step4_part0 j
  · exact step4_part1 j
  · exact step4_part2 j
  · exact step4_part3 j
  · exact step4_part4 j
  · exact step4_part5 j
  · exact step4_part6 j
  · exact step4_part7 j
  · exact step4_part8 j
  · exact step4_part9 j
  · exact step4_part10 j
  · exact step4_part11 j
  · exact step4_part12 j
  · exact step4_part13 j
  · exact step4_part14 j
  · exact step4_part15 j
  · exact step4_part16 j
  · exact step4_part17 j
  · exact step4_part18 j
  · exact step4_part19 j
  · exact step4_part20 j
  · exact step4_part21 j
  · exact step4_part22 j
  · exact step4_part23 j
  · exact step4_part24 j
  · exact step4_part25 j
  · exact step4_part26 j
  · exact step4_part27 j
  · exact step4_part28 j
  · exact step4_part29 j
  · exact step4_part30 j
  · exact step4_part31 j
  · exact step4_part32 j
  · exact step4_part33 j
  · exact step4_part34 j
  · exact step4_part35 j
  · exact step4_part36 j
  · exact step4_part37 j
  · exact step4_part38 j
  · exact step4_part39 j
  · exact step4_part40 j
  · exact step4_part41 j
  · exact step4_part42 j
  · exact step4_part43 j
  · exact step4_part44 j
  · exact step4_part45 j
  · exact step4_part46 j
  · exact step4_part47 j
  · exact step4_part48 j
  · exact step4_part49 j
  · exact step4_part50 j
  · exact step4_part51 j
  · exact step4_part52 j
  · exact step4_part53 j
  · exact step4_part54 j
  · exact step4_part55 j
  · exact step4_part56 j
  · exact step4_part57 j
  · exact step4_part58 j
  · exact step4_part59 j
  · exact step4_part60 j
  · exact step4_part61 j
  · exact step4_part62 j
  · exact step4_part63 j
private theorem step4_all (i : Fin 8192) : (sparseHamiltonian (state 4) i + (if (i : Fin 8192).val == 4861 then (12285 : Int) else 0)) = state 5 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step4_blocks b j
theorem step4 : (fun i => sparseHamiltonian (state 4) i + (if i.val == 4861 then (12285 : Int) else 0)) = state 5 := funext step4_all
private theorem step5_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step5_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step5_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step5_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step5_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step5_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step5_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step5_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step5_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step5_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step5_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step5_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step5_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step5_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step5_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step5_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step5_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step5_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step5_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step5_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step5_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step5_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step5_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step5_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step5_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step5_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step5_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step5_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step5_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step5_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step5_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step5_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step5_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step5_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step5_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step5_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step5_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step5_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step5_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step5_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step5_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step5_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step5_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step5_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step5_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step5_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step5_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step5_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step5_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step5_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step5_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step5_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step5_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step5_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step5_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step5_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step5_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step5_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step5_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step5_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step5_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step5_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step5_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step5_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 5) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step5_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 5) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step5_part0 j
  · exact step5_part1 j
  · exact step5_part2 j
  · exact step5_part3 j
  · exact step5_part4 j
  · exact step5_part5 j
  · exact step5_part6 j
  · exact step5_part7 j
  · exact step5_part8 j
  · exact step5_part9 j
  · exact step5_part10 j
  · exact step5_part11 j
  · exact step5_part12 j
  · exact step5_part13 j
  · exact step5_part14 j
  · exact step5_part15 j
  · exact step5_part16 j
  · exact step5_part17 j
  · exact step5_part18 j
  · exact step5_part19 j
  · exact step5_part20 j
  · exact step5_part21 j
  · exact step5_part22 j
  · exact step5_part23 j
  · exact step5_part24 j
  · exact step5_part25 j
  · exact step5_part26 j
  · exact step5_part27 j
  · exact step5_part28 j
  · exact step5_part29 j
  · exact step5_part30 j
  · exact step5_part31 j
  · exact step5_part32 j
  · exact step5_part33 j
  · exact step5_part34 j
  · exact step5_part35 j
  · exact step5_part36 j
  · exact step5_part37 j
  · exact step5_part38 j
  · exact step5_part39 j
  · exact step5_part40 j
  · exact step5_part41 j
  · exact step5_part42 j
  · exact step5_part43 j
  · exact step5_part44 j
  · exact step5_part45 j
  · exact step5_part46 j
  · exact step5_part47 j
  · exact step5_part48 j
  · exact step5_part49 j
  · exact step5_part50 j
  · exact step5_part51 j
  · exact step5_part52 j
  · exact step5_part53 j
  · exact step5_part54 j
  · exact step5_part55 j
  · exact step5_part56 j
  · exact step5_part57 j
  · exact step5_part58 j
  · exact step5_part59 j
  · exact step5_part60 j
  · exact step5_part61 j
  · exact step5_part62 j
  · exact step5_part63 j
private theorem step5_all (i : Fin 8192) : (sparseHamiltonian (state 5) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 6 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step5_blocks b j
theorem step5 : (fun i => sparseHamiltonian (state 5) i + (if i.val == 4861 then (0 : Int) else 0)) = state 6 := funext step5_all
private theorem step6_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step6_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step6_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step6_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step6_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step6_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step6_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step6_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step6_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step6_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step6_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step6_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step6_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step6_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step6_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step6_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step6_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step6_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step6_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step6_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step6_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step6_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step6_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step6_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step6_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step6_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step6_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step6_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step6_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step6_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step6_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step6_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step6_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step6_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step6_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step6_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step6_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step6_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step6_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step6_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step6_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step6_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step6_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step6_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step6_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step6_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step6_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step6_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step6_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step6_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step6_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step6_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step6_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step6_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step6_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step6_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step6_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step6_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step6_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step6_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step6_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step6_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step6_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step6_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 6) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step6_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 6) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step6_part0 j
  · exact step6_part1 j
  · exact step6_part2 j
  · exact step6_part3 j
  · exact step6_part4 j
  · exact step6_part5 j
  · exact step6_part6 j
  · exact step6_part7 j
  · exact step6_part8 j
  · exact step6_part9 j
  · exact step6_part10 j
  · exact step6_part11 j
  · exact step6_part12 j
  · exact step6_part13 j
  · exact step6_part14 j
  · exact step6_part15 j
  · exact step6_part16 j
  · exact step6_part17 j
  · exact step6_part18 j
  · exact step6_part19 j
  · exact step6_part20 j
  · exact step6_part21 j
  · exact step6_part22 j
  · exact step6_part23 j
  · exact step6_part24 j
  · exact step6_part25 j
  · exact step6_part26 j
  · exact step6_part27 j
  · exact step6_part28 j
  · exact step6_part29 j
  · exact step6_part30 j
  · exact step6_part31 j
  · exact step6_part32 j
  · exact step6_part33 j
  · exact step6_part34 j
  · exact step6_part35 j
  · exact step6_part36 j
  · exact step6_part37 j
  · exact step6_part38 j
  · exact step6_part39 j
  · exact step6_part40 j
  · exact step6_part41 j
  · exact step6_part42 j
  · exact step6_part43 j
  · exact step6_part44 j
  · exact step6_part45 j
  · exact step6_part46 j
  · exact step6_part47 j
  · exact step6_part48 j
  · exact step6_part49 j
  · exact step6_part50 j
  · exact step6_part51 j
  · exact step6_part52 j
  · exact step6_part53 j
  · exact step6_part54 j
  · exact step6_part55 j
  · exact step6_part56 j
  · exact step6_part57 j
  · exact step6_part58 j
  · exact step6_part59 j
  · exact step6_part60 j
  · exact step6_part61 j
  · exact step6_part62 j
  · exact step6_part63 j
private theorem step6_all (i : Fin 8192) : (sparseHamiltonian (state 6) i + (if (i : Fin 8192).val == 4861 then (-569445 : Int) else 0)) = state 7 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step6_blocks b j
theorem step6 : (fun i => sparseHamiltonian (state 6) i + (if i.val == 4861 then (-569445 : Int) else 0)) = state 7 := funext step6_all
private theorem step7_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step7_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step7_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step7_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step7_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step7_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step7_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step7_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step7_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step7_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step7_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step7_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step7_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step7_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step7_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step7_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step7_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step7_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step7_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step7_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step7_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step7_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step7_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step7_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step7_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step7_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step7_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step7_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step7_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step7_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step7_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step7_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step7_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step7_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step7_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step7_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step7_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step7_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step7_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step7_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step7_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step7_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step7_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step7_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step7_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step7_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step7_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step7_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step7_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step7_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step7_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step7_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step7_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step7_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step7_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step7_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step7_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step7_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step7_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step7_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step7_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step7_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step7_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step7_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 7) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step7_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 7) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step7_part0 j
  · exact step7_part1 j
  · exact step7_part2 j
  · exact step7_part3 j
  · exact step7_part4 j
  · exact step7_part5 j
  · exact step7_part6 j
  · exact step7_part7 j
  · exact step7_part8 j
  · exact step7_part9 j
  · exact step7_part10 j
  · exact step7_part11 j
  · exact step7_part12 j
  · exact step7_part13 j
  · exact step7_part14 j
  · exact step7_part15 j
  · exact step7_part16 j
  · exact step7_part17 j
  · exact step7_part18 j
  · exact step7_part19 j
  · exact step7_part20 j
  · exact step7_part21 j
  · exact step7_part22 j
  · exact step7_part23 j
  · exact step7_part24 j
  · exact step7_part25 j
  · exact step7_part26 j
  · exact step7_part27 j
  · exact step7_part28 j
  · exact step7_part29 j
  · exact step7_part30 j
  · exact step7_part31 j
  · exact step7_part32 j
  · exact step7_part33 j
  · exact step7_part34 j
  · exact step7_part35 j
  · exact step7_part36 j
  · exact step7_part37 j
  · exact step7_part38 j
  · exact step7_part39 j
  · exact step7_part40 j
  · exact step7_part41 j
  · exact step7_part42 j
  · exact step7_part43 j
  · exact step7_part44 j
  · exact step7_part45 j
  · exact step7_part46 j
  · exact step7_part47 j
  · exact step7_part48 j
  · exact step7_part49 j
  · exact step7_part50 j
  · exact step7_part51 j
  · exact step7_part52 j
  · exact step7_part53 j
  · exact step7_part54 j
  · exact step7_part55 j
  · exact step7_part56 j
  · exact step7_part57 j
  · exact step7_part58 j
  · exact step7_part59 j
  · exact step7_part60 j
  · exact step7_part61 j
  · exact step7_part62 j
  · exact step7_part63 j
private theorem step7_all (i : Fin 8192) : (sparseHamiltonian (state 7) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 8 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step7_blocks b j
theorem step7 : (fun i => sparseHamiltonian (state 7) i + (if i.val == 4861 then (0 : Int) else 0)) = state 8 := funext step7_all

end D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner
