/- GID: D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart06
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart06
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
private theorem step24_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step24_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step24_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step24_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step24_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step24_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step24_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step24_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step24_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step24_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step24_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step24_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step24_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step24_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step24_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step24_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step24_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step24_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step24_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step24_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step24_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step24_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step24_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step24_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step24_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step24_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step24_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step24_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step24_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step24_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step24_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step24_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step24_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step24_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step24_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step24_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step24_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step24_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step24_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step24_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step24_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step24_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step24_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step24_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step24_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step24_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step24_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step24_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step24_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step24_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step24_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step24_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step24_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step24_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step24_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step24_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step24_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step24_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step24_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step24_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step24_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step24_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step24_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step24_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 24) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step24_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 24) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step24_part0 j
  · exact step24_part1 j
  · exact step24_part2 j
  · exact step24_part3 j
  · exact step24_part4 j
  · exact step24_part5 j
  · exact step24_part6 j
  · exact step24_part7 j
  · exact step24_part8 j
  · exact step24_part9 j
  · exact step24_part10 j
  · exact step24_part11 j
  · exact step24_part12 j
  · exact step24_part13 j
  · exact step24_part14 j
  · exact step24_part15 j
  · exact step24_part16 j
  · exact step24_part17 j
  · exact step24_part18 j
  · exact step24_part19 j
  · exact step24_part20 j
  · exact step24_part21 j
  · exact step24_part22 j
  · exact step24_part23 j
  · exact step24_part24 j
  · exact step24_part25 j
  · exact step24_part26 j
  · exact step24_part27 j
  · exact step24_part28 j
  · exact step24_part29 j
  · exact step24_part30 j
  · exact step24_part31 j
  · exact step24_part32 j
  · exact step24_part33 j
  · exact step24_part34 j
  · exact step24_part35 j
  · exact step24_part36 j
  · exact step24_part37 j
  · exact step24_part38 j
  · exact step24_part39 j
  · exact step24_part40 j
  · exact step24_part41 j
  · exact step24_part42 j
  · exact step24_part43 j
  · exact step24_part44 j
  · exact step24_part45 j
  · exact step24_part46 j
  · exact step24_part47 j
  · exact step24_part48 j
  · exact step24_part49 j
  · exact step24_part50 j
  · exact step24_part51 j
  · exact step24_part52 j
  · exact step24_part53 j
  · exact step24_part54 j
  · exact step24_part55 j
  · exact step24_part56 j
  · exact step24_part57 j
  · exact step24_part58 j
  · exact step24_part59 j
  · exact step24_part60 j
  · exact step24_part61 j
  · exact step24_part62 j
  · exact step24_part63 j
private theorem step24_all (i : Fin 8192) : (sparseHamiltonian (state 24) i + (if (i : Fin 8192).val == 4861 then (2162620108980042 : Int) else 0)) = state 25 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step24_blocks b j
theorem step24 : (fun i => sparseHamiltonian (state 24) i + (if i.val == 4861 then (2162620108980042 : Int) else 0)) = state 25 := funext step24_all
private theorem step25_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step25_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step25_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step25_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step25_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step25_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step25_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step25_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step25_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step25_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step25_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step25_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step25_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step25_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step25_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step25_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step25_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step25_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step25_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step25_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step25_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step25_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step25_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step25_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step25_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step25_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step25_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step25_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step25_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step25_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step25_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step25_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step25_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step25_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step25_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step25_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step25_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step25_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step25_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step25_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step25_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step25_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step25_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step25_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step25_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step25_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step25_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step25_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step25_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step25_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step25_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step25_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step25_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step25_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step25_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step25_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step25_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step25_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step25_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step25_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step25_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step25_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step25_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step25_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 25) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step25_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 25) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step25_part0 j
  · exact step25_part1 j
  · exact step25_part2 j
  · exact step25_part3 j
  · exact step25_part4 j
  · exact step25_part5 j
  · exact step25_part6 j
  · exact step25_part7 j
  · exact step25_part8 j
  · exact step25_part9 j
  · exact step25_part10 j
  · exact step25_part11 j
  · exact step25_part12 j
  · exact step25_part13 j
  · exact step25_part14 j
  · exact step25_part15 j
  · exact step25_part16 j
  · exact step25_part17 j
  · exact step25_part18 j
  · exact step25_part19 j
  · exact step25_part20 j
  · exact step25_part21 j
  · exact step25_part22 j
  · exact step25_part23 j
  · exact step25_part24 j
  · exact step25_part25 j
  · exact step25_part26 j
  · exact step25_part27 j
  · exact step25_part28 j
  · exact step25_part29 j
  · exact step25_part30 j
  · exact step25_part31 j
  · exact step25_part32 j
  · exact step25_part33 j
  · exact step25_part34 j
  · exact step25_part35 j
  · exact step25_part36 j
  · exact step25_part37 j
  · exact step25_part38 j
  · exact step25_part39 j
  · exact step25_part40 j
  · exact step25_part41 j
  · exact step25_part42 j
  · exact step25_part43 j
  · exact step25_part44 j
  · exact step25_part45 j
  · exact step25_part46 j
  · exact step25_part47 j
  · exact step25_part48 j
  · exact step25_part49 j
  · exact step25_part50 j
  · exact step25_part51 j
  · exact step25_part52 j
  · exact step25_part53 j
  · exact step25_part54 j
  · exact step25_part55 j
  · exact step25_part56 j
  · exact step25_part57 j
  · exact step25_part58 j
  · exact step25_part59 j
  · exact step25_part60 j
  · exact step25_part61 j
  · exact step25_part62 j
  · exact step25_part63 j
private theorem step25_all (i : Fin 8192) : (sparseHamiltonian (state 25) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 26 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step25_blocks b j
theorem step25 : (fun i => sparseHamiltonian (state 25) i + (if i.val == 4861 then (0 : Int) else 0)) = state 26 := funext step25_all
private theorem step26_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step26_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step26_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step26_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step26_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step26_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step26_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step26_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step26_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step26_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step26_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step26_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step26_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step26_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step26_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step26_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step26_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step26_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step26_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step26_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step26_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step26_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step26_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step26_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step26_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step26_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step26_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step26_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step26_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step26_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step26_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step26_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step26_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step26_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step26_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step26_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step26_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step26_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step26_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step26_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step26_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step26_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step26_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step26_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step26_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step26_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step26_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step26_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step26_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step26_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step26_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step26_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step26_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step26_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step26_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step26_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step26_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step26_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step26_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step26_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step26_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step26_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step26_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step26_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 26) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step26_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 26) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step26_part0 j
  · exact step26_part1 j
  · exact step26_part2 j
  · exact step26_part3 j
  · exact step26_part4 j
  · exact step26_part5 j
  · exact step26_part6 j
  · exact step26_part7 j
  · exact step26_part8 j
  · exact step26_part9 j
  · exact step26_part10 j
  · exact step26_part11 j
  · exact step26_part12 j
  · exact step26_part13 j
  · exact step26_part14 j
  · exact step26_part15 j
  · exact step26_part16 j
  · exact step26_part17 j
  · exact step26_part18 j
  · exact step26_part19 j
  · exact step26_part20 j
  · exact step26_part21 j
  · exact step26_part22 j
  · exact step26_part23 j
  · exact step26_part24 j
  · exact step26_part25 j
  · exact step26_part26 j
  · exact step26_part27 j
  · exact step26_part28 j
  · exact step26_part29 j
  · exact step26_part30 j
  · exact step26_part31 j
  · exact step26_part32 j
  · exact step26_part33 j
  · exact step26_part34 j
  · exact step26_part35 j
  · exact step26_part36 j
  · exact step26_part37 j
  · exact step26_part38 j
  · exact step26_part39 j
  · exact step26_part40 j
  · exact step26_part41 j
  · exact step26_part42 j
  · exact step26_part43 j
  · exact step26_part44 j
  · exact step26_part45 j
  · exact step26_part46 j
  · exact step26_part47 j
  · exact step26_part48 j
  · exact step26_part49 j
  · exact step26_part50 j
  · exact step26_part51 j
  · exact step26_part52 j
  · exact step26_part53 j
  · exact step26_part54 j
  · exact step26_part55 j
  · exact step26_part56 j
  · exact step26_part57 j
  · exact step26_part58 j
  · exact step26_part59 j
  · exact step26_part60 j
  · exact step26_part61 j
  · exact step26_part62 j
  · exact step26_part63 j
private theorem step26_all (i : Fin 8192) : (sparseHamiltonian (state 26) i + (if (i : Fin 8192).val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step26_blocks b j
theorem step26 : (fun i => sparseHamiltonian (state 26) i + (if i.val == 4861 then (-8462844884056308 : Int) else 0)) = state 27 := funext step26_all
private theorem step27_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step27_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step27_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step27_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step27_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step27_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step27_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step27_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step27_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step27_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step27_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step27_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step27_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step27_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step27_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step27_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step27_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step27_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step27_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step27_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step27_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step27_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step27_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step27_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step27_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step27_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step27_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step27_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step27_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step27_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step27_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step27_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step27_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step27_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step27_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step27_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step27_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step27_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step27_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step27_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step27_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step27_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step27_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step27_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step27_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step27_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step27_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step27_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step27_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step27_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step27_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step27_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step27_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step27_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step27_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step27_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step27_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step27_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step27_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step27_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step27_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step27_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step27_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step27_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 27) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step27_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 27) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step27_part0 j
  · exact step27_part1 j
  · exact step27_part2 j
  · exact step27_part3 j
  · exact step27_part4 j
  · exact step27_part5 j
  · exact step27_part6 j
  · exact step27_part7 j
  · exact step27_part8 j
  · exact step27_part9 j
  · exact step27_part10 j
  · exact step27_part11 j
  · exact step27_part12 j
  · exact step27_part13 j
  · exact step27_part14 j
  · exact step27_part15 j
  · exact step27_part16 j
  · exact step27_part17 j
  · exact step27_part18 j
  · exact step27_part19 j
  · exact step27_part20 j
  · exact step27_part21 j
  · exact step27_part22 j
  · exact step27_part23 j
  · exact step27_part24 j
  · exact step27_part25 j
  · exact step27_part26 j
  · exact step27_part27 j
  · exact step27_part28 j
  · exact step27_part29 j
  · exact step27_part30 j
  · exact step27_part31 j
  · exact step27_part32 j
  · exact step27_part33 j
  · exact step27_part34 j
  · exact step27_part35 j
  · exact step27_part36 j
  · exact step27_part37 j
  · exact step27_part38 j
  · exact step27_part39 j
  · exact step27_part40 j
  · exact step27_part41 j
  · exact step27_part42 j
  · exact step27_part43 j
  · exact step27_part44 j
  · exact step27_part45 j
  · exact step27_part46 j
  · exact step27_part47 j
  · exact step27_part48 j
  · exact step27_part49 j
  · exact step27_part50 j
  · exact step27_part51 j
  · exact step27_part52 j
  · exact step27_part53 j
  · exact step27_part54 j
  · exact step27_part55 j
  · exact step27_part56 j
  · exact step27_part57 j
  · exact step27_part58 j
  · exact step27_part59 j
  · exact step27_part60 j
  · exact step27_part61 j
  · exact step27_part62 j
  · exact step27_part63 j
private theorem step27_all (i : Fin 8192) : (sparseHamiltonian (state 27) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 28 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step27_blocks b j
theorem step27 : (fun i => sparseHamiltonian (state 27) i + (if i.val == 4861 then (0 : Int) else 0)) = state 28 := funext step27_all

end D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner
