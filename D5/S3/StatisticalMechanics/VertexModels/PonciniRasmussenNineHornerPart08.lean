/- GID: D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart08
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart08
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
private theorem step32_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step32_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step32_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step32_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step32_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step32_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step32_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step32_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step32_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step32_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step32_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step32_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step32_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step32_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step32_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step32_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step32_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step32_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step32_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step32_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step32_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step32_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step32_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step32_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step32_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step32_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step32_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step32_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step32_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step32_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step32_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step32_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step32_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step32_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step32_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step32_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step32_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step32_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step32_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step32_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step32_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step32_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step32_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step32_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step32_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step32_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step32_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step32_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step32_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step32_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step32_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step32_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step32_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step32_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step32_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step32_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step32_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step32_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step32_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step32_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step32_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step32_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step32_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step32_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 32) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step32_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 32) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step32_part0 j
  · exact step32_part1 j
  · exact step32_part2 j
  · exact step32_part3 j
  · exact step32_part4 j
  · exact step32_part5 j
  · exact step32_part6 j
  · exact step32_part7 j
  · exact step32_part8 j
  · exact step32_part9 j
  · exact step32_part10 j
  · exact step32_part11 j
  · exact step32_part12 j
  · exact step32_part13 j
  · exact step32_part14 j
  · exact step32_part15 j
  · exact step32_part16 j
  · exact step32_part17 j
  · exact step32_part18 j
  · exact step32_part19 j
  · exact step32_part20 j
  · exact step32_part21 j
  · exact step32_part22 j
  · exact step32_part23 j
  · exact step32_part24 j
  · exact step32_part25 j
  · exact step32_part26 j
  · exact step32_part27 j
  · exact step32_part28 j
  · exact step32_part29 j
  · exact step32_part30 j
  · exact step32_part31 j
  · exact step32_part32 j
  · exact step32_part33 j
  · exact step32_part34 j
  · exact step32_part35 j
  · exact step32_part36 j
  · exact step32_part37 j
  · exact step32_part38 j
  · exact step32_part39 j
  · exact step32_part40 j
  · exact step32_part41 j
  · exact step32_part42 j
  · exact step32_part43 j
  · exact step32_part44 j
  · exact step32_part45 j
  · exact step32_part46 j
  · exact step32_part47 j
  · exact step32_part48 j
  · exact step32_part49 j
  · exact step32_part50 j
  · exact step32_part51 j
  · exact step32_part52 j
  · exact step32_part53 j
  · exact step32_part54 j
  · exact step32_part55 j
  · exact step32_part56 j
  · exact step32_part57 j
  · exact step32_part58 j
  · exact step32_part59 j
  · exact step32_part60 j
  · exact step32_part61 j
  · exact step32_part62 j
  · exact step32_part63 j
private theorem step32_all (i : Fin 8192) : (sparseHamiltonian (state 32) i + (if (i : Fin 8192).val == 4861 then (145778728152448221 : Int) else 0)) = state 33 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step32_blocks b j
theorem step32 : (fun i => sparseHamiltonian (state 32) i + (if i.val == 4861 then (145778728152448221 : Int) else 0)) = state 33 := funext step32_all
private theorem step33_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step33_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step33_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step33_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step33_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step33_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step33_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step33_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step33_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step33_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step33_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step33_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step33_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step33_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step33_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step33_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step33_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step33_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step33_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step33_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step33_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step33_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step33_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step33_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step33_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step33_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step33_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step33_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step33_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step33_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step33_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step33_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step33_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step33_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step33_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step33_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step33_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step33_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step33_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step33_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step33_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step33_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step33_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step33_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step33_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step33_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step33_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step33_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step33_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step33_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step33_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step33_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step33_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step33_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step33_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step33_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step33_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step33_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step33_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step33_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step33_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step33_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step33_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step33_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 33) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step33_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 33) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step33_part0 j
  · exact step33_part1 j
  · exact step33_part2 j
  · exact step33_part3 j
  · exact step33_part4 j
  · exact step33_part5 j
  · exact step33_part6 j
  · exact step33_part7 j
  · exact step33_part8 j
  · exact step33_part9 j
  · exact step33_part10 j
  · exact step33_part11 j
  · exact step33_part12 j
  · exact step33_part13 j
  · exact step33_part14 j
  · exact step33_part15 j
  · exact step33_part16 j
  · exact step33_part17 j
  · exact step33_part18 j
  · exact step33_part19 j
  · exact step33_part20 j
  · exact step33_part21 j
  · exact step33_part22 j
  · exact step33_part23 j
  · exact step33_part24 j
  · exact step33_part25 j
  · exact step33_part26 j
  · exact step33_part27 j
  · exact step33_part28 j
  · exact step33_part29 j
  · exact step33_part30 j
  · exact step33_part31 j
  · exact step33_part32 j
  · exact step33_part33 j
  · exact step33_part34 j
  · exact step33_part35 j
  · exact step33_part36 j
  · exact step33_part37 j
  · exact step33_part38 j
  · exact step33_part39 j
  · exact step33_part40 j
  · exact step33_part41 j
  · exact step33_part42 j
  · exact step33_part43 j
  · exact step33_part44 j
  · exact step33_part45 j
  · exact step33_part46 j
  · exact step33_part47 j
  · exact step33_part48 j
  · exact step33_part49 j
  · exact step33_part50 j
  · exact step33_part51 j
  · exact step33_part52 j
  · exact step33_part53 j
  · exact step33_part54 j
  · exact step33_part55 j
  · exact step33_part56 j
  · exact step33_part57 j
  · exact step33_part58 j
  · exact step33_part59 j
  · exact step33_part60 j
  · exact step33_part61 j
  · exact step33_part62 j
  · exact step33_part63 j
private theorem step33_all (i : Fin 8192) : (sparseHamiltonian (state 33) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 34 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step33_blocks b j
theorem step33 : (fun i => sparseHamiltonian (state 33) i + (if i.val == 4861 then (0 : Int) else 0)) = state 34 := funext step33_all
private theorem step34_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step34_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step34_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step34_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step34_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step34_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step34_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step34_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step34_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step34_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step34_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step34_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step34_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step34_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step34_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step34_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step34_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step34_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step34_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step34_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step34_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step34_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step34_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step34_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step34_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step34_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step34_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step34_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step34_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step34_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step34_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step34_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step34_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step34_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step34_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step34_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step34_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step34_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step34_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step34_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step34_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step34_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step34_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step34_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step34_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step34_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step34_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step34_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step34_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step34_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step34_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step34_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step34_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step34_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step34_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step34_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step34_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step34_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step34_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step34_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step34_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step34_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step34_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step34_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 34) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step34_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 34) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step34_part0 j
  · exact step34_part1 j
  · exact step34_part2 j
  · exact step34_part3 j
  · exact step34_part4 j
  · exact step34_part5 j
  · exact step34_part6 j
  · exact step34_part7 j
  · exact step34_part8 j
  · exact step34_part9 j
  · exact step34_part10 j
  · exact step34_part11 j
  · exact step34_part12 j
  · exact step34_part13 j
  · exact step34_part14 j
  · exact step34_part15 j
  · exact step34_part16 j
  · exact step34_part17 j
  · exact step34_part18 j
  · exact step34_part19 j
  · exact step34_part20 j
  · exact step34_part21 j
  · exact step34_part22 j
  · exact step34_part23 j
  · exact step34_part24 j
  · exact step34_part25 j
  · exact step34_part26 j
  · exact step34_part27 j
  · exact step34_part28 j
  · exact step34_part29 j
  · exact step34_part30 j
  · exact step34_part31 j
  · exact step34_part32 j
  · exact step34_part33 j
  · exact step34_part34 j
  · exact step34_part35 j
  · exact step34_part36 j
  · exact step34_part37 j
  · exact step34_part38 j
  · exact step34_part39 j
  · exact step34_part40 j
  · exact step34_part41 j
  · exact step34_part42 j
  · exact step34_part43 j
  · exact step34_part44 j
  · exact step34_part45 j
  · exact step34_part46 j
  · exact step34_part47 j
  · exact step34_part48 j
  · exact step34_part49 j
  · exact step34_part50 j
  · exact step34_part51 j
  · exact step34_part52 j
  · exact step34_part53 j
  · exact step34_part54 j
  · exact step34_part55 j
  · exact step34_part56 j
  · exact step34_part57 j
  · exact step34_part58 j
  · exact step34_part59 j
  · exact step34_part60 j
  · exact step34_part61 j
  · exact step34_part62 j
  · exact step34_part63 j
private theorem step34_all (i : Fin 8192) : (sparseHamiltonian (state 34) i + (if (i : Fin 8192).val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step34_blocks b j
theorem step34 : (fun i => sparseHamiltonian (state 34) i + (if i.val == 4861 then (-244086630072528699 : Int) else 0)) = state 35 := funext step34_all
private theorem step35_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step35_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step35_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step35_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step35_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step35_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step35_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step35_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step35_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step35_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step35_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step35_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step35_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step35_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step35_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step35_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step35_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step35_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step35_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step35_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step35_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step35_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step35_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step35_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step35_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step35_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step35_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step35_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step35_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step35_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step35_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step35_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step35_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step35_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step35_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step35_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step35_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step35_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step35_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step35_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step35_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step35_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step35_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step35_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step35_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step35_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step35_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step35_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step35_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step35_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step35_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step35_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step35_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step35_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step35_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step35_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step35_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step35_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step35_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step35_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step35_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step35_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step35_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step35_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 35) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step35_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 35) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step35_part0 j
  · exact step35_part1 j
  · exact step35_part2 j
  · exact step35_part3 j
  · exact step35_part4 j
  · exact step35_part5 j
  · exact step35_part6 j
  · exact step35_part7 j
  · exact step35_part8 j
  · exact step35_part9 j
  · exact step35_part10 j
  · exact step35_part11 j
  · exact step35_part12 j
  · exact step35_part13 j
  · exact step35_part14 j
  · exact step35_part15 j
  · exact step35_part16 j
  · exact step35_part17 j
  · exact step35_part18 j
  · exact step35_part19 j
  · exact step35_part20 j
  · exact step35_part21 j
  · exact step35_part22 j
  · exact step35_part23 j
  · exact step35_part24 j
  · exact step35_part25 j
  · exact step35_part26 j
  · exact step35_part27 j
  · exact step35_part28 j
  · exact step35_part29 j
  · exact step35_part30 j
  · exact step35_part31 j
  · exact step35_part32 j
  · exact step35_part33 j
  · exact step35_part34 j
  · exact step35_part35 j
  · exact step35_part36 j
  · exact step35_part37 j
  · exact step35_part38 j
  · exact step35_part39 j
  · exact step35_part40 j
  · exact step35_part41 j
  · exact step35_part42 j
  · exact step35_part43 j
  · exact step35_part44 j
  · exact step35_part45 j
  · exact step35_part46 j
  · exact step35_part47 j
  · exact step35_part48 j
  · exact step35_part49 j
  · exact step35_part50 j
  · exact step35_part51 j
  · exact step35_part52 j
  · exact step35_part53 j
  · exact step35_part54 j
  · exact step35_part55 j
  · exact step35_part56 j
  · exact step35_part57 j
  · exact step35_part58 j
  · exact step35_part59 j
  · exact step35_part60 j
  · exact step35_part61 j
  · exact step35_part62 j
  · exact step35_part63 j
private theorem step35_all (i : Fin 8192) : (sparseHamiltonian (state 35) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 36 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step35_blocks b j
theorem step35 : (fun i => sparseHamiltonian (state 35) i + (if i.val == 4861 then (0 : Int) else 0)) = state 36 := funext step35_all

end D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner
