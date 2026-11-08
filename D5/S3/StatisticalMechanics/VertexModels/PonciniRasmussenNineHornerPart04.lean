/- GID: D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart04
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart04
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
private theorem step16_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step16_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step16_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step16_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step16_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step16_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step16_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step16_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step16_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step16_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step16_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step16_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step16_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step16_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step16_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step16_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step16_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step16_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step16_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step16_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step16_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step16_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step16_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step16_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step16_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step16_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step16_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step16_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step16_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step16_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step16_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step16_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step16_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step16_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step16_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step16_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step16_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step16_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step16_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step16_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step16_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step16_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step16_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step16_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step16_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step16_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step16_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step16_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step16_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step16_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step16_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step16_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step16_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step16_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step16_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step16_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step16_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step16_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step16_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step16_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step16_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step16_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step16_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step16_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 16) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step16_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 16) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step16_part0 j
  · exact step16_part1 j
  · exact step16_part2 j
  · exact step16_part3 j
  · exact step16_part4 j
  · exact step16_part5 j
  · exact step16_part6 j
  · exact step16_part7 j
  · exact step16_part8 j
  · exact step16_part9 j
  · exact step16_part10 j
  · exact step16_part11 j
  · exact step16_part12 j
  · exact step16_part13 j
  · exact step16_part14 j
  · exact step16_part15 j
  · exact step16_part16 j
  · exact step16_part17 j
  · exact step16_part18 j
  · exact step16_part19 j
  · exact step16_part20 j
  · exact step16_part21 j
  · exact step16_part22 j
  · exact step16_part23 j
  · exact step16_part24 j
  · exact step16_part25 j
  · exact step16_part26 j
  · exact step16_part27 j
  · exact step16_part28 j
  · exact step16_part29 j
  · exact step16_part30 j
  · exact step16_part31 j
  · exact step16_part32 j
  · exact step16_part33 j
  · exact step16_part34 j
  · exact step16_part35 j
  · exact step16_part36 j
  · exact step16_part37 j
  · exact step16_part38 j
  · exact step16_part39 j
  · exact step16_part40 j
  · exact step16_part41 j
  · exact step16_part42 j
  · exact step16_part43 j
  · exact step16_part44 j
  · exact step16_part45 j
  · exact step16_part46 j
  · exact step16_part47 j
  · exact step16_part48 j
  · exact step16_part49 j
  · exact step16_part50 j
  · exact step16_part51 j
  · exact step16_part52 j
  · exact step16_part53 j
  · exact step16_part54 j
  · exact step16_part55 j
  · exact step16_part56 j
  · exact step16_part57 j
  · exact step16_part58 j
  · exact step16_part59 j
  · exact step16_part60 j
  · exact step16_part61 j
  · exact step16_part62 j
  · exact step16_part63 j
private theorem step16_all (i : Fin 8192) : (sparseHamiltonian (state 16) i + (if (i : Fin 8192).val == 4861 then (1188246329388 : Int) else 0)) = state 17 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step16_blocks b j
theorem step16 : (fun i => sparseHamiltonian (state 16) i + (if i.val == 4861 then (1188246329388 : Int) else 0)) = state 17 := funext step16_all
private theorem step17_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step17_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step17_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step17_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step17_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step17_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step17_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step17_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step17_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step17_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step17_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step17_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step17_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step17_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step17_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step17_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step17_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step17_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step17_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step17_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step17_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step17_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step17_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step17_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step17_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step17_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step17_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step17_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step17_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step17_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step17_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step17_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step17_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step17_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step17_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step17_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step17_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step17_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step17_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step17_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step17_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step17_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step17_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step17_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step17_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step17_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step17_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step17_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step17_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step17_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step17_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step17_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step17_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step17_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step17_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step17_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step17_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step17_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step17_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step17_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step17_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step17_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step17_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step17_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 17) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step17_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 17) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step17_part0 j
  · exact step17_part1 j
  · exact step17_part2 j
  · exact step17_part3 j
  · exact step17_part4 j
  · exact step17_part5 j
  · exact step17_part6 j
  · exact step17_part7 j
  · exact step17_part8 j
  · exact step17_part9 j
  · exact step17_part10 j
  · exact step17_part11 j
  · exact step17_part12 j
  · exact step17_part13 j
  · exact step17_part14 j
  · exact step17_part15 j
  · exact step17_part16 j
  · exact step17_part17 j
  · exact step17_part18 j
  · exact step17_part19 j
  · exact step17_part20 j
  · exact step17_part21 j
  · exact step17_part22 j
  · exact step17_part23 j
  · exact step17_part24 j
  · exact step17_part25 j
  · exact step17_part26 j
  · exact step17_part27 j
  · exact step17_part28 j
  · exact step17_part29 j
  · exact step17_part30 j
  · exact step17_part31 j
  · exact step17_part32 j
  · exact step17_part33 j
  · exact step17_part34 j
  · exact step17_part35 j
  · exact step17_part36 j
  · exact step17_part37 j
  · exact step17_part38 j
  · exact step17_part39 j
  · exact step17_part40 j
  · exact step17_part41 j
  · exact step17_part42 j
  · exact step17_part43 j
  · exact step17_part44 j
  · exact step17_part45 j
  · exact step17_part46 j
  · exact step17_part47 j
  · exact step17_part48 j
  · exact step17_part49 j
  · exact step17_part50 j
  · exact step17_part51 j
  · exact step17_part52 j
  · exact step17_part53 j
  · exact step17_part54 j
  · exact step17_part55 j
  · exact step17_part56 j
  · exact step17_part57 j
  · exact step17_part58 j
  · exact step17_part59 j
  · exact step17_part60 j
  · exact step17_part61 j
  · exact step17_part62 j
  · exact step17_part63 j
private theorem step17_all (i : Fin 8192) : (sparseHamiltonian (state 17) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 18 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step17_blocks b j
theorem step17 : (fun i => sparseHamiltonian (state 17) i + (if i.val == 4861 then (0 : Int) else 0)) = state 18 := funext step17_all
private theorem step18_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step18_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step18_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step18_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step18_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step18_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step18_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step18_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step18_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step18_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step18_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step18_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step18_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step18_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step18_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step18_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step18_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step18_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step18_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step18_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step18_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step18_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step18_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step18_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step18_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step18_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step18_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step18_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step18_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step18_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step18_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step18_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step18_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step18_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step18_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step18_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step18_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step18_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step18_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step18_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step18_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step18_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step18_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step18_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step18_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step18_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step18_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step18_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step18_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step18_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step18_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step18_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step18_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step18_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step18_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step18_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step18_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step18_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step18_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step18_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step18_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step18_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step18_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step18_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 18) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step18_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 18) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step18_part0 j
  · exact step18_part1 j
  · exact step18_part2 j
  · exact step18_part3 j
  · exact step18_part4 j
  · exact step18_part5 j
  · exact step18_part6 j
  · exact step18_part7 j
  · exact step18_part8 j
  · exact step18_part9 j
  · exact step18_part10 j
  · exact step18_part11 j
  · exact step18_part12 j
  · exact step18_part13 j
  · exact step18_part14 j
  · exact step18_part15 j
  · exact step18_part16 j
  · exact step18_part17 j
  · exact step18_part18 j
  · exact step18_part19 j
  · exact step18_part20 j
  · exact step18_part21 j
  · exact step18_part22 j
  · exact step18_part23 j
  · exact step18_part24 j
  · exact step18_part25 j
  · exact step18_part26 j
  · exact step18_part27 j
  · exact step18_part28 j
  · exact step18_part29 j
  · exact step18_part30 j
  · exact step18_part31 j
  · exact step18_part32 j
  · exact step18_part33 j
  · exact step18_part34 j
  · exact step18_part35 j
  · exact step18_part36 j
  · exact step18_part37 j
  · exact step18_part38 j
  · exact step18_part39 j
  · exact step18_part40 j
  · exact step18_part41 j
  · exact step18_part42 j
  · exact step18_part43 j
  · exact step18_part44 j
  · exact step18_part45 j
  · exact step18_part46 j
  · exact step18_part47 j
  · exact step18_part48 j
  · exact step18_part49 j
  · exact step18_part50 j
  · exact step18_part51 j
  · exact step18_part52 j
  · exact step18_part53 j
  · exact step18_part54 j
  · exact step18_part55 j
  · exact step18_part56 j
  · exact step18_part57 j
  · exact step18_part58 j
  · exact step18_part59 j
  · exact step18_part60 j
  · exact step18_part61 j
  · exact step18_part62 j
  · exact step18_part63 j
private theorem step18_all (i : Fin 8192) : (sparseHamiltonian (state 18) i + (if (i : Fin 8192).val == 4861 then (-10605723426434 : Int) else 0)) = state 19 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step18_blocks b j
theorem step18 : (fun i => sparseHamiltonian (state 18) i + (if i.val == 4861 then (-10605723426434 : Int) else 0)) = state 19 := funext step18_all
private theorem step19_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step19_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step19_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step19_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step19_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step19_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step19_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step19_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step19_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step19_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step19_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step19_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step19_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step19_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step19_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step19_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step19_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step19_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step19_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step19_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step19_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step19_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step19_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step19_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step19_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step19_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step19_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step19_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step19_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step19_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step19_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step19_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step19_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step19_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step19_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step19_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step19_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step19_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step19_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step19_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step19_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step19_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step19_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step19_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step19_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step19_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step19_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step19_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step19_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step19_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step19_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step19_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step19_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step19_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step19_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step19_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step19_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step19_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step19_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step19_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step19_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step19_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step19_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step19_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 19) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step19_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 19) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step19_part0 j
  · exact step19_part1 j
  · exact step19_part2 j
  · exact step19_part3 j
  · exact step19_part4 j
  · exact step19_part5 j
  · exact step19_part6 j
  · exact step19_part7 j
  · exact step19_part8 j
  · exact step19_part9 j
  · exact step19_part10 j
  · exact step19_part11 j
  · exact step19_part12 j
  · exact step19_part13 j
  · exact step19_part14 j
  · exact step19_part15 j
  · exact step19_part16 j
  · exact step19_part17 j
  · exact step19_part18 j
  · exact step19_part19 j
  · exact step19_part20 j
  · exact step19_part21 j
  · exact step19_part22 j
  · exact step19_part23 j
  · exact step19_part24 j
  · exact step19_part25 j
  · exact step19_part26 j
  · exact step19_part27 j
  · exact step19_part28 j
  · exact step19_part29 j
  · exact step19_part30 j
  · exact step19_part31 j
  · exact step19_part32 j
  · exact step19_part33 j
  · exact step19_part34 j
  · exact step19_part35 j
  · exact step19_part36 j
  · exact step19_part37 j
  · exact step19_part38 j
  · exact step19_part39 j
  · exact step19_part40 j
  · exact step19_part41 j
  · exact step19_part42 j
  · exact step19_part43 j
  · exact step19_part44 j
  · exact step19_part45 j
  · exact step19_part46 j
  · exact step19_part47 j
  · exact step19_part48 j
  · exact step19_part49 j
  · exact step19_part50 j
  · exact step19_part51 j
  · exact step19_part52 j
  · exact step19_part53 j
  · exact step19_part54 j
  · exact step19_part55 j
  · exact step19_part56 j
  · exact step19_part57 j
  · exact step19_part58 j
  · exact step19_part59 j
  · exact step19_part60 j
  · exact step19_part61 j
  · exact step19_part62 j
  · exact step19_part63 j
private theorem step19_all (i : Fin 8192) : (sparseHamiltonian (state 19) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 20 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step19_blocks b j
theorem step19 : (fun i => sparseHamiltonian (state 19) i + (if i.val == 4861 then (0 : Int) else 0)) = state 20 := funext step19_all

end D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner
