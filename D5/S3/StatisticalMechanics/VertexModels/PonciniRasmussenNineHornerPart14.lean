/- GID: D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart14
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart14
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
private theorem step56_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨0+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨128+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨256+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨384+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨512+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨640+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨768+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨896+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨1024+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨1152+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨1280+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨1408+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨1536+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨1664+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨1792+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨1920+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨2048+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨2176+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨2304+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨2432+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨2560+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨2688+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨2816+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨2944+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨3072+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨3200+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨3328+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨3456+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨3584+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨3712+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨3840+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨3968+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨4096+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨4224+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨4352+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨4480+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨4608+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨4736+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨4864+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨4992+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨5120+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨5248+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨5376+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨5504+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨5632+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨5760+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨5888+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨6016+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨6144+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨6272+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨6400+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨6528+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨6656+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨6784+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨6912+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨7040+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨7168+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨7296+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨7424+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨7552+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨7680+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨7808+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨7936+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 56) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨8064+j.val, by omega⟩ := by
  decide +kernel
private theorem step56_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 56) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step56_part0 j
  · exact step56_part1 j
  · exact step56_part2 j
  · exact step56_part3 j
  · exact step56_part4 j
  · exact step56_part5 j
  · exact step56_part6 j
  · exact step56_part7 j
  · exact step56_part8 j
  · exact step56_part9 j
  · exact step56_part10 j
  · exact step56_part11 j
  · exact step56_part12 j
  · exact step56_part13 j
  · exact step56_part14 j
  · exact step56_part15 j
  · exact step56_part16 j
  · exact step56_part17 j
  · exact step56_part18 j
  · exact step56_part19 j
  · exact step56_part20 j
  · exact step56_part21 j
  · exact step56_part22 j
  · exact step56_part23 j
  · exact step56_part24 j
  · exact step56_part25 j
  · exact step56_part26 j
  · exact step56_part27 j
  · exact step56_part28 j
  · exact step56_part29 j
  · exact step56_part30 j
  · exact step56_part31 j
  · exact step56_part32 j
  · exact step56_part33 j
  · exact step56_part34 j
  · exact step56_part35 j
  · exact step56_part36 j
  · exact step56_part37 j
  · exact step56_part38 j
  · exact step56_part39 j
  · exact step56_part40 j
  · exact step56_part41 j
  · exact step56_part42 j
  · exact step56_part43 j
  · exact step56_part44 j
  · exact step56_part45 j
  · exact step56_part46 j
  · exact step56_part47 j
  · exact step56_part48 j
  · exact step56_part49 j
  · exact step56_part50 j
  · exact step56_part51 j
  · exact step56_part52 j
  · exact step56_part53 j
  · exact step56_part54 j
  · exact step56_part55 j
  · exact step56_part56 j
  · exact step56_part57 j
  · exact step56_part58 j
  · exact step56_part59 j
  · exact step56_part60 j
  · exact step56_part61 j
  · exact step56_part62 j
  · exact step56_part63 j
private theorem step56_all (i : Fin 8192) : (sparseHamiltonian (state 56) i + (if (i : Fin 8192).val == 4861 then (43808164416 : Int) else 0)) = state 57 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  simpa only [hi] using step56_blocks b j
theorem step56 : (fun i => sparseHamiltonian (state 56) i + (if i.val == 4861 then (43808164416 : Int) else 0)) = state 57 := funext step56_all
private theorem step57_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨0+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨128+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨256+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨384+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨512+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨640+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨768+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨896+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨1024+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨1152+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨1280+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨1408+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨1536+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨1664+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨1792+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨1920+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨2048+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨2176+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨2304+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨2432+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨2560+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨2688+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨2816+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨2944+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨3072+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨3200+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨3328+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨3456+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨3584+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨3712+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨3840+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨3968+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨4096+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨4224+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨4352+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨4480+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨4608+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨4736+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨4864+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨4992+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨5120+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨5248+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨5376+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨5504+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨5632+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨5760+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨5888+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨6016+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨6144+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨6272+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨6400+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨6528+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨6656+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨6784+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨6912+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨7040+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨7168+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨7296+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨7424+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨7552+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨7680+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨7808+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨7936+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 57) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨8064+j.val, by omega⟩ := by
  decide +kernel
private theorem step57_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 57) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step57_part0 j
  · exact step57_part1 j
  · exact step57_part2 j
  · exact step57_part3 j
  · exact step57_part4 j
  · exact step57_part5 j
  · exact step57_part6 j
  · exact step57_part7 j
  · exact step57_part8 j
  · exact step57_part9 j
  · exact step57_part10 j
  · exact step57_part11 j
  · exact step57_part12 j
  · exact step57_part13 j
  · exact step57_part14 j
  · exact step57_part15 j
  · exact step57_part16 j
  · exact step57_part17 j
  · exact step57_part18 j
  · exact step57_part19 j
  · exact step57_part20 j
  · exact step57_part21 j
  · exact step57_part22 j
  · exact step57_part23 j
  · exact step57_part24 j
  · exact step57_part25 j
  · exact step57_part26 j
  · exact step57_part27 j
  · exact step57_part28 j
  · exact step57_part29 j
  · exact step57_part30 j
  · exact step57_part31 j
  · exact step57_part32 j
  · exact step57_part33 j
  · exact step57_part34 j
  · exact step57_part35 j
  · exact step57_part36 j
  · exact step57_part37 j
  · exact step57_part38 j
  · exact step57_part39 j
  · exact step57_part40 j
  · exact step57_part41 j
  · exact step57_part42 j
  · exact step57_part43 j
  · exact step57_part44 j
  · exact step57_part45 j
  · exact step57_part46 j
  · exact step57_part47 j
  · exact step57_part48 j
  · exact step57_part49 j
  · exact step57_part50 j
  · exact step57_part51 j
  · exact step57_part52 j
  · exact step57_part53 j
  · exact step57_part54 j
  · exact step57_part55 j
  · exact step57_part56 j
  · exact step57_part57 j
  · exact step57_part58 j
  · exact step57_part59 j
  · exact step57_part60 j
  · exact step57_part61 j
  · exact step57_part62 j
  · exact step57_part63 j
private theorem step57_all (i : Fin 8192) : (sparseHamiltonian (state 57) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 58 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  simpa only [hi] using step57_blocks b j
theorem step57 : (fun i => sparseHamiltonian (state 57) i + (if i.val == 4861 then (0 : Int) else 0)) = state 58 := funext step57_all

end D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner
