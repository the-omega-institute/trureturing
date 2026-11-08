/- GID: D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart12
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart12
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Data.Int.Basic]
   utility: kind=numeric-reduction; basis=refutes=gid:D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.claim; result=D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.result; claim=D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.claim
   digest: Four split integer Horner steps for the nine-strand certificate. -/
import D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenNineHornerData
import Mathlib.Tactic.FinCases

/-! Exact integer data and finite kernel reduction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.style.longLine false

namespace D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner
private theorem step48_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨0+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨128+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨256+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨384+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨512+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨640+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨768+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨896+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨1024+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨1152+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨1280+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨1408+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨1536+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨1664+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨1792+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨1920+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨2048+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨2176+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨2304+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨2432+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨2560+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨2688+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨2816+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨2944+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨3072+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨3200+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨3328+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨3456+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨3584+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨3712+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨3840+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨3968+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨4096+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨4224+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨4352+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨4480+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨4608+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨4736+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨4864+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨4992+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨5120+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨5248+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨5376+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨5504+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨5632+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨5760+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨5888+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨6016+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨6144+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨6272+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨6400+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨6528+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨6656+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨6784+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨6912+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨7040+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨7168+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨7296+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨7424+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨7552+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨7680+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨7808+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨7936+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 48) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨8064+j.val, by omega⟩ := by
  decide +kernel
private theorem step48_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 48) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step48_part0 j
  · exact step48_part1 j
  · exact step48_part2 j
  · exact step48_part3 j
  · exact step48_part4 j
  · exact step48_part5 j
  · exact step48_part6 j
  · exact step48_part7 j
  · exact step48_part8 j
  · exact step48_part9 j
  · exact step48_part10 j
  · exact step48_part11 j
  · exact step48_part12 j
  · exact step48_part13 j
  · exact step48_part14 j
  · exact step48_part15 j
  · exact step48_part16 j
  · exact step48_part17 j
  · exact step48_part18 j
  · exact step48_part19 j
  · exact step48_part20 j
  · exact step48_part21 j
  · exact step48_part22 j
  · exact step48_part23 j
  · exact step48_part24 j
  · exact step48_part25 j
  · exact step48_part26 j
  · exact step48_part27 j
  · exact step48_part28 j
  · exact step48_part29 j
  · exact step48_part30 j
  · exact step48_part31 j
  · exact step48_part32 j
  · exact step48_part33 j
  · exact step48_part34 j
  · exact step48_part35 j
  · exact step48_part36 j
  · exact step48_part37 j
  · exact step48_part38 j
  · exact step48_part39 j
  · exact step48_part40 j
  · exact step48_part41 j
  · exact step48_part42 j
  · exact step48_part43 j
  · exact step48_part44 j
  · exact step48_part45 j
  · exact step48_part46 j
  · exact step48_part47 j
  · exact step48_part48 j
  · exact step48_part49 j
  · exact step48_part50 j
  · exact step48_part51 j
  · exact step48_part52 j
  · exact step48_part53 j
  · exact step48_part54 j
  · exact step48_part55 j
  · exact step48_part56 j
  · exact step48_part57 j
  · exact step48_part58 j
  · exact step48_part59 j
  · exact step48_part60 j
  · exact step48_part61 j
  · exact step48_part62 j
  · exact step48_part63 j
private theorem step48_all (i : Fin 8192) : (sparseHamiltonian (state 48) i + (if (i : Fin 8192).val == 4861 then (5347591521504921 : Int) else 0)) = state 49 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  simpa only [hi] using step48_blocks b j
theorem step48 : (fun i => sparseHamiltonian (state 48) i + (if i.val == 4861 then (5347591521504921 : Int) else 0)) = state 49 := funext step48_all
private theorem step49_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨0+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨128+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨256+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨384+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨512+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨640+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨768+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨896+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨1024+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨1152+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨1280+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨1408+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨1536+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨1664+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨1792+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨1920+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨2048+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨2176+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨2304+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨2432+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨2560+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨2688+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨2816+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨2944+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨3072+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨3200+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨3328+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨3456+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨3584+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨3712+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨3840+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨3968+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨4096+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨4224+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨4352+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨4480+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨4608+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨4736+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨4864+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨4992+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨5120+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨5248+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨5376+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨5504+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨5632+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨5760+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨5888+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨6016+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨6144+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨6272+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨6400+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨6528+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨6656+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨6784+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨6912+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨7040+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨7168+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨7296+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨7424+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨7552+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨7680+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨7808+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨7936+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 49) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨8064+j.val, by omega⟩ := by
  decide +kernel
private theorem step49_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 49) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step49_part0 j
  · exact step49_part1 j
  · exact step49_part2 j
  · exact step49_part3 j
  · exact step49_part4 j
  · exact step49_part5 j
  · exact step49_part6 j
  · exact step49_part7 j
  · exact step49_part8 j
  · exact step49_part9 j
  · exact step49_part10 j
  · exact step49_part11 j
  · exact step49_part12 j
  · exact step49_part13 j
  · exact step49_part14 j
  · exact step49_part15 j
  · exact step49_part16 j
  · exact step49_part17 j
  · exact step49_part18 j
  · exact step49_part19 j
  · exact step49_part20 j
  · exact step49_part21 j
  · exact step49_part22 j
  · exact step49_part23 j
  · exact step49_part24 j
  · exact step49_part25 j
  · exact step49_part26 j
  · exact step49_part27 j
  · exact step49_part28 j
  · exact step49_part29 j
  · exact step49_part30 j
  · exact step49_part31 j
  · exact step49_part32 j
  · exact step49_part33 j
  · exact step49_part34 j
  · exact step49_part35 j
  · exact step49_part36 j
  · exact step49_part37 j
  · exact step49_part38 j
  · exact step49_part39 j
  · exact step49_part40 j
  · exact step49_part41 j
  · exact step49_part42 j
  · exact step49_part43 j
  · exact step49_part44 j
  · exact step49_part45 j
  · exact step49_part46 j
  · exact step49_part47 j
  · exact step49_part48 j
  · exact step49_part49 j
  · exact step49_part50 j
  · exact step49_part51 j
  · exact step49_part52 j
  · exact step49_part53 j
  · exact step49_part54 j
  · exact step49_part55 j
  · exact step49_part56 j
  · exact step49_part57 j
  · exact step49_part58 j
  · exact step49_part59 j
  · exact step49_part60 j
  · exact step49_part61 j
  · exact step49_part62 j
  · exact step49_part63 j
private theorem step49_all (i : Fin 8192) : (sparseHamiltonian (state 49) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 50 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  simpa only [hi] using step49_blocks b j
theorem step49 : (fun i => sparseHamiltonian (state 49) i + (if i.val == 4861 then (0 : Int) else 0)) = state 50 := funext step49_all
private theorem step50_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨0+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨128+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨256+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨384+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨512+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨640+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨768+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨896+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨1024+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨1152+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨1280+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨1408+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨1536+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨1664+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨1792+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨1920+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨2048+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨2176+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨2304+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨2432+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨2560+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨2688+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨2816+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨2944+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨3072+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨3200+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨3328+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨3456+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨3584+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨3712+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨3840+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨3968+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨4096+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨4224+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨4352+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨4480+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨4608+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨4736+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨4864+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨4992+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨5120+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨5248+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨5376+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨5504+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨5632+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨5760+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨5888+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨6016+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨6144+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨6272+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨6400+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨6528+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨6656+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨6784+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨6912+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨7040+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨7168+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨7296+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨7424+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨7552+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨7680+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨7808+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨7936+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 50) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨8064+j.val, by omega⟩ := by
  decide +kernel
private theorem step50_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 50) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step50_part0 j
  · exact step50_part1 j
  · exact step50_part2 j
  · exact step50_part3 j
  · exact step50_part4 j
  · exact step50_part5 j
  · exact step50_part6 j
  · exact step50_part7 j
  · exact step50_part8 j
  · exact step50_part9 j
  · exact step50_part10 j
  · exact step50_part11 j
  · exact step50_part12 j
  · exact step50_part13 j
  · exact step50_part14 j
  · exact step50_part15 j
  · exact step50_part16 j
  · exact step50_part17 j
  · exact step50_part18 j
  · exact step50_part19 j
  · exact step50_part20 j
  · exact step50_part21 j
  · exact step50_part22 j
  · exact step50_part23 j
  · exact step50_part24 j
  · exact step50_part25 j
  · exact step50_part26 j
  · exact step50_part27 j
  · exact step50_part28 j
  · exact step50_part29 j
  · exact step50_part30 j
  · exact step50_part31 j
  · exact step50_part32 j
  · exact step50_part33 j
  · exact step50_part34 j
  · exact step50_part35 j
  · exact step50_part36 j
  · exact step50_part37 j
  · exact step50_part38 j
  · exact step50_part39 j
  · exact step50_part40 j
  · exact step50_part41 j
  · exact step50_part42 j
  · exact step50_part43 j
  · exact step50_part44 j
  · exact step50_part45 j
  · exact step50_part46 j
  · exact step50_part47 j
  · exact step50_part48 j
  · exact step50_part49 j
  · exact step50_part50 j
  · exact step50_part51 j
  · exact step50_part52 j
  · exact step50_part53 j
  · exact step50_part54 j
  · exact step50_part55 j
  · exact step50_part56 j
  · exact step50_part57 j
  · exact step50_part58 j
  · exact step50_part59 j
  · exact step50_part60 j
  · exact step50_part61 j
  · exact step50_part62 j
  · exact step50_part63 j
private theorem step50_all (i : Fin 8192) : (sparseHamiltonian (state 50) i + (if (i : Fin 8192).val == 4861 then (-762922848588417 : Int) else 0)) = state 51 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  simpa only [hi] using step50_blocks b j
theorem step50 : (fun i => sparseHamiltonian (state 50) i + (if i.val == 4861 then (-762922848588417 : Int) else 0)) = state 51 := funext step50_all
private theorem step51_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨0+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨128+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨256+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨384+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨512+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨640+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨768+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨896+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨1024+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨1152+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨1280+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨1408+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨1536+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨1664+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨1792+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨1920+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨2048+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨2176+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨2304+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨2432+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨2560+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨2688+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨2816+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨2944+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨3072+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨3200+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨3328+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨3456+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨3584+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨3712+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨3840+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨3968+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨4096+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨4224+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨4352+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨4480+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨4608+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨4736+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨4864+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨4992+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨5120+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨5248+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨5376+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨5504+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨5632+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨5760+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨5888+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨6016+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨6144+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨6272+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨6400+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨6528+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨6656+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨6784+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨6912+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨7040+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨7168+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨7296+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨7424+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨7552+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨7680+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨7808+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨7936+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 51) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨8064+j.val, by omega⟩ := by
  decide +kernel
private theorem step51_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 51) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step51_part0 j
  · exact step51_part1 j
  · exact step51_part2 j
  · exact step51_part3 j
  · exact step51_part4 j
  · exact step51_part5 j
  · exact step51_part6 j
  · exact step51_part7 j
  · exact step51_part8 j
  · exact step51_part9 j
  · exact step51_part10 j
  · exact step51_part11 j
  · exact step51_part12 j
  · exact step51_part13 j
  · exact step51_part14 j
  · exact step51_part15 j
  · exact step51_part16 j
  · exact step51_part17 j
  · exact step51_part18 j
  · exact step51_part19 j
  · exact step51_part20 j
  · exact step51_part21 j
  · exact step51_part22 j
  · exact step51_part23 j
  · exact step51_part24 j
  · exact step51_part25 j
  · exact step51_part26 j
  · exact step51_part27 j
  · exact step51_part28 j
  · exact step51_part29 j
  · exact step51_part30 j
  · exact step51_part31 j
  · exact step51_part32 j
  · exact step51_part33 j
  · exact step51_part34 j
  · exact step51_part35 j
  · exact step51_part36 j
  · exact step51_part37 j
  · exact step51_part38 j
  · exact step51_part39 j
  · exact step51_part40 j
  · exact step51_part41 j
  · exact step51_part42 j
  · exact step51_part43 j
  · exact step51_part44 j
  · exact step51_part45 j
  · exact step51_part46 j
  · exact step51_part47 j
  · exact step51_part48 j
  · exact step51_part49 j
  · exact step51_part50 j
  · exact step51_part51 j
  · exact step51_part52 j
  · exact step51_part53 j
  · exact step51_part54 j
  · exact step51_part55 j
  · exact step51_part56 j
  · exact step51_part57 j
  · exact step51_part58 j
  · exact step51_part59 j
  · exact step51_part60 j
  · exact step51_part61 j
  · exact step51_part62 j
  · exact step51_part63 j
private theorem step51_all (i : Fin 8192) : (sparseHamiltonian (state 51) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 52 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  simpa only [hi] using step51_blocks b j
theorem step51 : (fun i => sparseHamiltonian (state 51) i + (if i.val == 4861 then (0 : Int) else 0)) = state 52 := funext step51_all

end D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner
