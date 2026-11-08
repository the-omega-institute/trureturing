/- GID: D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart02
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart02
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
private theorem step8_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step8_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step8_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step8_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step8_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step8_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step8_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step8_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step8_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step8_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step8_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step8_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step8_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step8_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step8_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step8_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step8_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step8_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step8_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step8_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step8_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step8_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step8_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step8_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step8_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step8_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step8_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step8_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step8_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step8_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step8_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step8_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step8_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step8_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step8_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step8_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step8_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step8_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step8_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step8_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step8_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step8_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step8_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step8_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step8_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step8_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step8_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step8_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step8_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step8_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step8_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step8_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step8_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step8_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step8_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step8_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step8_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step8_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step8_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step8_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step8_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step8_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step8_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step8_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 8) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step8_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 8) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step8_part0 j
  · exact step8_part1 j
  · exact step8_part2 j
  · exact step8_part3 j
  · exact step8_part4 j
  · exact step8_part5 j
  · exact step8_part6 j
  · exact step8_part7 j
  · exact step8_part8 j
  · exact step8_part9 j
  · exact step8_part10 j
  · exact step8_part11 j
  · exact step8_part12 j
  · exact step8_part13 j
  · exact step8_part14 j
  · exact step8_part15 j
  · exact step8_part16 j
  · exact step8_part17 j
  · exact step8_part18 j
  · exact step8_part19 j
  · exact step8_part20 j
  · exact step8_part21 j
  · exact step8_part22 j
  · exact step8_part23 j
  · exact step8_part24 j
  · exact step8_part25 j
  · exact step8_part26 j
  · exact step8_part27 j
  · exact step8_part28 j
  · exact step8_part29 j
  · exact step8_part30 j
  · exact step8_part31 j
  · exact step8_part32 j
  · exact step8_part33 j
  · exact step8_part34 j
  · exact step8_part35 j
  · exact step8_part36 j
  · exact step8_part37 j
  · exact step8_part38 j
  · exact step8_part39 j
  · exact step8_part40 j
  · exact step8_part41 j
  · exact step8_part42 j
  · exact step8_part43 j
  · exact step8_part44 j
  · exact step8_part45 j
  · exact step8_part46 j
  · exact step8_part47 j
  · exact step8_part48 j
  · exact step8_part49 j
  · exact step8_part50 j
  · exact step8_part51 j
  · exact step8_part52 j
  · exact step8_part53 j
  · exact step8_part54 j
  · exact step8_part55 j
  · exact step8_part56 j
  · exact step8_part57 j
  · exact step8_part58 j
  · exact step8_part59 j
  · exact step8_part60 j
  · exact step8_part61 j
  · exact step8_part62 j
  · exact step8_part63 j
private theorem step8_all (i : Fin 8192) : (sparseHamiltonian (state 8) i + (if (i : Fin 8192).val == 4861 then (18215115 : Int) else 0)) = state 9 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step8_blocks b j
theorem step8 : (fun i => sparseHamiltonian (state 8) i + (if i.val == 4861 then (18215115 : Int) else 0)) = state 9 := funext step8_all
private theorem step9_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step9_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step9_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step9_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step9_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step9_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step9_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step9_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step9_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step9_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step9_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step9_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step9_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step9_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step9_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step9_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step9_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step9_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step9_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step9_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step9_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step9_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step9_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step9_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step9_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step9_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step9_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step9_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step9_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step9_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step9_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step9_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step9_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step9_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step9_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step9_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step9_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step9_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step9_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step9_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step9_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step9_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step9_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step9_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step9_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step9_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step9_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step9_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step9_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step9_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step9_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step9_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step9_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step9_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step9_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step9_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step9_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step9_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step9_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step9_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step9_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step9_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step9_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step9_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 9) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step9_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 9) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step9_part0 j
  · exact step9_part1 j
  · exact step9_part2 j
  · exact step9_part3 j
  · exact step9_part4 j
  · exact step9_part5 j
  · exact step9_part6 j
  · exact step9_part7 j
  · exact step9_part8 j
  · exact step9_part9 j
  · exact step9_part10 j
  · exact step9_part11 j
  · exact step9_part12 j
  · exact step9_part13 j
  · exact step9_part14 j
  · exact step9_part15 j
  · exact step9_part16 j
  · exact step9_part17 j
  · exact step9_part18 j
  · exact step9_part19 j
  · exact step9_part20 j
  · exact step9_part21 j
  · exact step9_part22 j
  · exact step9_part23 j
  · exact step9_part24 j
  · exact step9_part25 j
  · exact step9_part26 j
  · exact step9_part27 j
  · exact step9_part28 j
  · exact step9_part29 j
  · exact step9_part30 j
  · exact step9_part31 j
  · exact step9_part32 j
  · exact step9_part33 j
  · exact step9_part34 j
  · exact step9_part35 j
  · exact step9_part36 j
  · exact step9_part37 j
  · exact step9_part38 j
  · exact step9_part39 j
  · exact step9_part40 j
  · exact step9_part41 j
  · exact step9_part42 j
  · exact step9_part43 j
  · exact step9_part44 j
  · exact step9_part45 j
  · exact step9_part46 j
  · exact step9_part47 j
  · exact step9_part48 j
  · exact step9_part49 j
  · exact step9_part50 j
  · exact step9_part51 j
  · exact step9_part52 j
  · exact step9_part53 j
  · exact step9_part54 j
  · exact step9_part55 j
  · exact step9_part56 j
  · exact step9_part57 j
  · exact step9_part58 j
  · exact step9_part59 j
  · exact step9_part60 j
  · exact step9_part61 j
  · exact step9_part62 j
  · exact step9_part63 j
private theorem step9_all (i : Fin 8192) : (sparseHamiltonian (state 9) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 10 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step9_blocks b j
theorem step9 : (fun i => sparseHamiltonian (state 9) i + (if i.val == 4861 then (0 : Int) else 0)) = state 10 := funext step9_all
private theorem step10_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step10_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step10_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step10_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step10_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step10_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step10_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step10_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step10_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step10_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step10_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step10_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step10_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step10_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step10_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step10_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step10_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step10_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step10_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step10_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step10_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step10_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step10_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step10_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step10_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step10_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step10_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step10_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step10_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step10_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step10_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step10_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step10_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step10_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step10_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step10_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step10_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step10_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step10_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step10_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step10_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step10_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step10_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step10_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step10_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step10_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step10_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step10_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step10_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step10_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step10_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step10_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step10_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step10_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step10_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step10_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step10_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step10_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step10_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step10_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step10_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step10_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step10_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step10_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 10) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step10_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 10) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step10_part0 j
  · exact step10_part1 j
  · exact step10_part2 j
  · exact step10_part3 j
  · exact step10_part4 j
  · exact step10_part5 j
  · exact step10_part6 j
  · exact step10_part7 j
  · exact step10_part8 j
  · exact step10_part9 j
  · exact step10_part10 j
  · exact step10_part11 j
  · exact step10_part12 j
  · exact step10_part13 j
  · exact step10_part14 j
  · exact step10_part15 j
  · exact step10_part16 j
  · exact step10_part17 j
  · exact step10_part18 j
  · exact step10_part19 j
  · exact step10_part20 j
  · exact step10_part21 j
  · exact step10_part22 j
  · exact step10_part23 j
  · exact step10_part24 j
  · exact step10_part25 j
  · exact step10_part26 j
  · exact step10_part27 j
  · exact step10_part28 j
  · exact step10_part29 j
  · exact step10_part30 j
  · exact step10_part31 j
  · exact step10_part32 j
  · exact step10_part33 j
  · exact step10_part34 j
  · exact step10_part35 j
  · exact step10_part36 j
  · exact step10_part37 j
  · exact step10_part38 j
  · exact step10_part39 j
  · exact step10_part40 j
  · exact step10_part41 j
  · exact step10_part42 j
  · exact step10_part43 j
  · exact step10_part44 j
  · exact step10_part45 j
  · exact step10_part46 j
  · exact step10_part47 j
  · exact step10_part48 j
  · exact step10_part49 j
  · exact step10_part50 j
  · exact step10_part51 j
  · exact step10_part52 j
  · exact step10_part53 j
  · exact step10_part54 j
  · exact step10_part55 j
  · exact step10_part56 j
  · exact step10_part57 j
  · exact step10_part58 j
  · exact step10_part59 j
  · exact step10_part60 j
  · exact step10_part61 j
  · exact step10_part62 j
  · exact step10_part63 j
private theorem step10_all (i : Fin 8192) : (sparseHamiltonian (state 10) i + (if (i : Fin 8192).val == 4861 then (-427662891 : Int) else 0)) = state 11 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step10_blocks b j
theorem step10 : (fun i => sparseHamiltonian (state 10) i + (if i.val == 4861 then (-427662891 : Int) else 0)) = state 11 := funext step10_all
private theorem step11_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step11_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step11_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step11_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step11_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step11_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step11_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step11_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step11_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step11_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step11_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step11_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step11_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step11_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step11_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step11_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step11_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step11_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step11_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step11_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step11_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step11_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step11_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step11_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step11_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step11_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step11_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step11_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step11_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step11_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step11_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step11_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step11_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step11_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step11_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step11_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step11_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step11_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step11_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step11_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step11_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step11_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step11_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step11_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step11_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step11_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step11_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step11_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step11_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step11_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step11_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step11_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step11_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step11_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step11_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step11_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step11_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step11_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step11_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step11_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step11_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step11_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step11_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step11_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 11) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step11_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 11) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step11_part0 j
  · exact step11_part1 j
  · exact step11_part2 j
  · exact step11_part3 j
  · exact step11_part4 j
  · exact step11_part5 j
  · exact step11_part6 j
  · exact step11_part7 j
  · exact step11_part8 j
  · exact step11_part9 j
  · exact step11_part10 j
  · exact step11_part11 j
  · exact step11_part12 j
  · exact step11_part13 j
  · exact step11_part14 j
  · exact step11_part15 j
  · exact step11_part16 j
  · exact step11_part17 j
  · exact step11_part18 j
  · exact step11_part19 j
  · exact step11_part20 j
  · exact step11_part21 j
  · exact step11_part22 j
  · exact step11_part23 j
  · exact step11_part24 j
  · exact step11_part25 j
  · exact step11_part26 j
  · exact step11_part27 j
  · exact step11_part28 j
  · exact step11_part29 j
  · exact step11_part30 j
  · exact step11_part31 j
  · exact step11_part32 j
  · exact step11_part33 j
  · exact step11_part34 j
  · exact step11_part35 j
  · exact step11_part36 j
  · exact step11_part37 j
  · exact step11_part38 j
  · exact step11_part39 j
  · exact step11_part40 j
  · exact step11_part41 j
  · exact step11_part42 j
  · exact step11_part43 j
  · exact step11_part44 j
  · exact step11_part45 j
  · exact step11_part46 j
  · exact step11_part47 j
  · exact step11_part48 j
  · exact step11_part49 j
  · exact step11_part50 j
  · exact step11_part51 j
  · exact step11_part52 j
  · exact step11_part53 j
  · exact step11_part54 j
  · exact step11_part55 j
  · exact step11_part56 j
  · exact step11_part57 j
  · exact step11_part58 j
  · exact step11_part59 j
  · exact step11_part60 j
  · exact step11_part61 j
  · exact step11_part62 j
  · exact step11_part63 j
private theorem step11_all (i : Fin 8192) : (sparseHamiltonian (state 11) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 12 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step11_blocks b j
theorem step11 : (fun i => sparseHamiltonian (state 11) i + (if i.val == 4861 then (0 : Int) else 0)) = state 12 := funext step11_all

end D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner
