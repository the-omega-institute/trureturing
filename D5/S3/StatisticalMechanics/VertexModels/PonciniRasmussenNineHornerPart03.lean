/- GID: D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart03
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart03
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
private theorem step12_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step12_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step12_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step12_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step12_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step12_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step12_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step12_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step12_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step12_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step12_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step12_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step12_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step12_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step12_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step12_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step12_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step12_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step12_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step12_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step12_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step12_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step12_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step12_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step12_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step12_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step12_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step12_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step12_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step12_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step12_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step12_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step12_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step12_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step12_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step12_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step12_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step12_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step12_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step12_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step12_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step12_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step12_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step12_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step12_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step12_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step12_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step12_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step12_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step12_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step12_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step12_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step12_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step12_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step12_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step12_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step12_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step12_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step12_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step12_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step12_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step12_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step12_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step12_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 12) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step12_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 12) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step12_part0 j
  · exact step12_part1 j
  · exact step12_part2 j
  · exact step12_part3 j
  · exact step12_part4 j
  · exact step12_part5 j
  · exact step12_part6 j
  · exact step12_part7 j
  · exact step12_part8 j
  · exact step12_part9 j
  · exact step12_part10 j
  · exact step12_part11 j
  · exact step12_part12 j
  · exact step12_part13 j
  · exact step12_part14 j
  · exact step12_part15 j
  · exact step12_part16 j
  · exact step12_part17 j
  · exact step12_part18 j
  · exact step12_part19 j
  · exact step12_part20 j
  · exact step12_part21 j
  · exact step12_part22 j
  · exact step12_part23 j
  · exact step12_part24 j
  · exact step12_part25 j
  · exact step12_part26 j
  · exact step12_part27 j
  · exact step12_part28 j
  · exact step12_part29 j
  · exact step12_part30 j
  · exact step12_part31 j
  · exact step12_part32 j
  · exact step12_part33 j
  · exact step12_part34 j
  · exact step12_part35 j
  · exact step12_part36 j
  · exact step12_part37 j
  · exact step12_part38 j
  · exact step12_part39 j
  · exact step12_part40 j
  · exact step12_part41 j
  · exact step12_part42 j
  · exact step12_part43 j
  · exact step12_part44 j
  · exact step12_part45 j
  · exact step12_part46 j
  · exact step12_part47 j
  · exact step12_part48 j
  · exact step12_part49 j
  · exact step12_part50 j
  · exact step12_part51 j
  · exact step12_part52 j
  · exact step12_part53 j
  · exact step12_part54 j
  · exact step12_part55 j
  · exact step12_part56 j
  · exact step12_part57 j
  · exact step12_part58 j
  · exact step12_part59 j
  · exact step12_part60 j
  · exact step12_part61 j
  · exact step12_part62 j
  · exact step12_part63 j
private theorem step12_all (i : Fin 8192) : (sparseHamiltonian (state 12) i + (if (i : Fin 8192).val == 4861 then (7652877936 : Int) else 0)) = state 13 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step12_blocks b j
theorem step12 : (fun i => sparseHamiltonian (state 12) i + (if i.val == 4861 then (7652877936 : Int) else 0)) = state 13 := funext step12_all
private theorem step13_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step13_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step13_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step13_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step13_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step13_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step13_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step13_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step13_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step13_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step13_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step13_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step13_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step13_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step13_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step13_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step13_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step13_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step13_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step13_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step13_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step13_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step13_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step13_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step13_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step13_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step13_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step13_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step13_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step13_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step13_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step13_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step13_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step13_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step13_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step13_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step13_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step13_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step13_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step13_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step13_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step13_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step13_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step13_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step13_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step13_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step13_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step13_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step13_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step13_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step13_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step13_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step13_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step13_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step13_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step13_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step13_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step13_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step13_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step13_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step13_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step13_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step13_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step13_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 13) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step13_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 13) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step13_part0 j
  · exact step13_part1 j
  · exact step13_part2 j
  · exact step13_part3 j
  · exact step13_part4 j
  · exact step13_part5 j
  · exact step13_part6 j
  · exact step13_part7 j
  · exact step13_part8 j
  · exact step13_part9 j
  · exact step13_part10 j
  · exact step13_part11 j
  · exact step13_part12 j
  · exact step13_part13 j
  · exact step13_part14 j
  · exact step13_part15 j
  · exact step13_part16 j
  · exact step13_part17 j
  · exact step13_part18 j
  · exact step13_part19 j
  · exact step13_part20 j
  · exact step13_part21 j
  · exact step13_part22 j
  · exact step13_part23 j
  · exact step13_part24 j
  · exact step13_part25 j
  · exact step13_part26 j
  · exact step13_part27 j
  · exact step13_part28 j
  · exact step13_part29 j
  · exact step13_part30 j
  · exact step13_part31 j
  · exact step13_part32 j
  · exact step13_part33 j
  · exact step13_part34 j
  · exact step13_part35 j
  · exact step13_part36 j
  · exact step13_part37 j
  · exact step13_part38 j
  · exact step13_part39 j
  · exact step13_part40 j
  · exact step13_part41 j
  · exact step13_part42 j
  · exact step13_part43 j
  · exact step13_part44 j
  · exact step13_part45 j
  · exact step13_part46 j
  · exact step13_part47 j
  · exact step13_part48 j
  · exact step13_part49 j
  · exact step13_part50 j
  · exact step13_part51 j
  · exact step13_part52 j
  · exact step13_part53 j
  · exact step13_part54 j
  · exact step13_part55 j
  · exact step13_part56 j
  · exact step13_part57 j
  · exact step13_part58 j
  · exact step13_part59 j
  · exact step13_part60 j
  · exact step13_part61 j
  · exact step13_part62 j
  · exact step13_part63 j
private theorem step13_all (i : Fin 8192) : (sparseHamiltonian (state 13) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 14 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step13_blocks b j
theorem step13 : (fun i => sparseHamiltonian (state 13) i + (if i.val == 4861 then (0 : Int) else 0)) = state 14 := funext step13_all
private theorem step14_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step14_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step14_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step14_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step14_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step14_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step14_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step14_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step14_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step14_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step14_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step14_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step14_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step14_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step14_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step14_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step14_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step14_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step14_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step14_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step14_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step14_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step14_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step14_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step14_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step14_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step14_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step14_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step14_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step14_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step14_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step14_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step14_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step14_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step14_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step14_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step14_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step14_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step14_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step14_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step14_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step14_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step14_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step14_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step14_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step14_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step14_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step14_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step14_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step14_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step14_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step14_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step14_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step14_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step14_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step14_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step14_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step14_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step14_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step14_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step14_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step14_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step14_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step14_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 14) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step14_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 14) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step14_part0 j
  · exact step14_part1 j
  · exact step14_part2 j
  · exact step14_part3 j
  · exact step14_part4 j
  · exact step14_part5 j
  · exact step14_part6 j
  · exact step14_part7 j
  · exact step14_part8 j
  · exact step14_part9 j
  · exact step14_part10 j
  · exact step14_part11 j
  · exact step14_part12 j
  · exact step14_part13 j
  · exact step14_part14 j
  · exact step14_part15 j
  · exact step14_part16 j
  · exact step14_part17 j
  · exact step14_part18 j
  · exact step14_part19 j
  · exact step14_part20 j
  · exact step14_part21 j
  · exact step14_part22 j
  · exact step14_part23 j
  · exact step14_part24 j
  · exact step14_part25 j
  · exact step14_part26 j
  · exact step14_part27 j
  · exact step14_part28 j
  · exact step14_part29 j
  · exact step14_part30 j
  · exact step14_part31 j
  · exact step14_part32 j
  · exact step14_part33 j
  · exact step14_part34 j
  · exact step14_part35 j
  · exact step14_part36 j
  · exact step14_part37 j
  · exact step14_part38 j
  · exact step14_part39 j
  · exact step14_part40 j
  · exact step14_part41 j
  · exact step14_part42 j
  · exact step14_part43 j
  · exact step14_part44 j
  · exact step14_part45 j
  · exact step14_part46 j
  · exact step14_part47 j
  · exact step14_part48 j
  · exact step14_part49 j
  · exact step14_part50 j
  · exact step14_part51 j
  · exact step14_part52 j
  · exact step14_part53 j
  · exact step14_part54 j
  · exact step14_part55 j
  · exact step14_part56 j
  · exact step14_part57 j
  · exact step14_part58 j
  · exact step14_part59 j
  · exact step14_part60 j
  · exact step14_part61 j
  · exact step14_part62 j
  · exact step14_part63 j
private theorem step14_all (i : Fin 8192) : (sparseHamiltonian (state 14) i + (if (i : Fin 8192).val == 4861 then (-106986874650 : Int) else 0)) = state 15 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step14_blocks b j
theorem step14 : (fun i => sparseHamiltonian (state 14) i + (if i.val == 4861 then (-106986874650 : Int) else 0)) = state 15 := funext step14_all
private theorem step15_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step15_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step15_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step15_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step15_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step15_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step15_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step15_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step15_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step15_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step15_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step15_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step15_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step15_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step15_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step15_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step15_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step15_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step15_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step15_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step15_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step15_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step15_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step15_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step15_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step15_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step15_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step15_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step15_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step15_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step15_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step15_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step15_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step15_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step15_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step15_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step15_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step15_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step15_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step15_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step15_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step15_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step15_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step15_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step15_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step15_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step15_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step15_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step15_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step15_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step15_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step15_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step15_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step15_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step15_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step15_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step15_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step15_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step15_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step15_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step15_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step15_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step15_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step15_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 15) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step15_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 15) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step15_part0 j
  · exact step15_part1 j
  · exact step15_part2 j
  · exact step15_part3 j
  · exact step15_part4 j
  · exact step15_part5 j
  · exact step15_part6 j
  · exact step15_part7 j
  · exact step15_part8 j
  · exact step15_part9 j
  · exact step15_part10 j
  · exact step15_part11 j
  · exact step15_part12 j
  · exact step15_part13 j
  · exact step15_part14 j
  · exact step15_part15 j
  · exact step15_part16 j
  · exact step15_part17 j
  · exact step15_part18 j
  · exact step15_part19 j
  · exact step15_part20 j
  · exact step15_part21 j
  · exact step15_part22 j
  · exact step15_part23 j
  · exact step15_part24 j
  · exact step15_part25 j
  · exact step15_part26 j
  · exact step15_part27 j
  · exact step15_part28 j
  · exact step15_part29 j
  · exact step15_part30 j
  · exact step15_part31 j
  · exact step15_part32 j
  · exact step15_part33 j
  · exact step15_part34 j
  · exact step15_part35 j
  · exact step15_part36 j
  · exact step15_part37 j
  · exact step15_part38 j
  · exact step15_part39 j
  · exact step15_part40 j
  · exact step15_part41 j
  · exact step15_part42 j
  · exact step15_part43 j
  · exact step15_part44 j
  · exact step15_part45 j
  · exact step15_part46 j
  · exact step15_part47 j
  · exact step15_part48 j
  · exact step15_part49 j
  · exact step15_part50 j
  · exact step15_part51 j
  · exact step15_part52 j
  · exact step15_part53 j
  · exact step15_part54 j
  · exact step15_part55 j
  · exact step15_part56 j
  · exact step15_part57 j
  · exact step15_part58 j
  · exact step15_part59 j
  · exact step15_part60 j
  · exact step15_part61 j
  · exact step15_part62 j
  · exact step15_part63 j
private theorem step15_all (i : Fin 8192) : (sparseHamiltonian (state 15) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 16 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step15_blocks b j
theorem step15 : (fun i => sparseHamiltonian (state 15) i + (if i.val == 4861 then (0 : Int) else 0)) = state 16 := funext step15_all

end D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner
