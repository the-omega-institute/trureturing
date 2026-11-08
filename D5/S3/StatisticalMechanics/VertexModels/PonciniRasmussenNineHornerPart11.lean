/- GID: D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart11
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart11
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
private theorem step44_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨0+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨128+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨256+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨384+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨512+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨640+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨768+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨896+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨1024+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨1152+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨1280+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨1408+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨1536+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨1664+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨1792+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨1920+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨2048+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨2176+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨2304+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨2432+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨2560+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨2688+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨2816+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨2944+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨3072+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨3200+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨3328+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨3456+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨3584+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨3712+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨3840+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨3968+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨4096+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨4224+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨4352+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨4480+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨4608+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨4736+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨4864+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨4992+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨5120+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨5248+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨5376+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨5504+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨5632+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨5760+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨5888+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨6016+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨6144+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨6272+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨6400+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨6528+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨6656+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨6784+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨6912+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨7040+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨7168+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨7296+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨7424+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨7552+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨7680+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨7808+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨7936+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 44) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨8064+j.val, by omega⟩ := by
  decide +kernel
private theorem step44_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 44) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step44_part0 j
  · exact step44_part1 j
  · exact step44_part2 j
  · exact step44_part3 j
  · exact step44_part4 j
  · exact step44_part5 j
  · exact step44_part6 j
  · exact step44_part7 j
  · exact step44_part8 j
  · exact step44_part9 j
  · exact step44_part10 j
  · exact step44_part11 j
  · exact step44_part12 j
  · exact step44_part13 j
  · exact step44_part14 j
  · exact step44_part15 j
  · exact step44_part16 j
  · exact step44_part17 j
  · exact step44_part18 j
  · exact step44_part19 j
  · exact step44_part20 j
  · exact step44_part21 j
  · exact step44_part22 j
  · exact step44_part23 j
  · exact step44_part24 j
  · exact step44_part25 j
  · exact step44_part26 j
  · exact step44_part27 j
  · exact step44_part28 j
  · exact step44_part29 j
  · exact step44_part30 j
  · exact step44_part31 j
  · exact step44_part32 j
  · exact step44_part33 j
  · exact step44_part34 j
  · exact step44_part35 j
  · exact step44_part36 j
  · exact step44_part37 j
  · exact step44_part38 j
  · exact step44_part39 j
  · exact step44_part40 j
  · exact step44_part41 j
  · exact step44_part42 j
  · exact step44_part43 j
  · exact step44_part44 j
  · exact step44_part45 j
  · exact step44_part46 j
  · exact step44_part47 j
  · exact step44_part48 j
  · exact step44_part49 j
  · exact step44_part50 j
  · exact step44_part51 j
  · exact step44_part52 j
  · exact step44_part53 j
  · exact step44_part54 j
  · exact step44_part55 j
  · exact step44_part56 j
  · exact step44_part57 j
  · exact step44_part58 j
  · exact step44_part59 j
  · exact step44_part60 j
  · exact step44_part61 j
  · exact step44_part62 j
  · exact step44_part63 j
private theorem step44_all (i : Fin 8192) : (sparseHamiltonian (state 44) i + (if (i : Fin 8192).val == 4861 then (74962166731413102 : Int) else 0)) = state 45 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  simpa only [hi] using step44_blocks b j
theorem step44 : (fun i => sparseHamiltonian (state 44) i + (if i.val == 4861 then (74962166731413102 : Int) else 0)) = state 45 := funext step44_all
private theorem step45_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨0+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨128+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨256+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨384+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨512+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨640+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨768+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨896+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨1024+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨1152+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨1280+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨1408+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨1536+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨1664+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨1792+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨1920+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨2048+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨2176+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨2304+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨2432+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨2560+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨2688+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨2816+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨2944+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨3072+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨3200+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨3328+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨3456+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨3584+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨3712+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨3840+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨3968+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨4096+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨4224+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨4352+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨4480+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨4608+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨4736+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨4864+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨4992+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨5120+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨5248+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨5376+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨5504+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨5632+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨5760+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨5888+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨6016+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨6144+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨6272+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨6400+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨6528+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨6656+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨6784+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨6912+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨7040+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨7168+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨7296+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨7424+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨7552+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨7680+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨7808+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨7936+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 45) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨8064+j.val, by omega⟩ := by
  decide +kernel
private theorem step45_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 45) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step45_part0 j
  · exact step45_part1 j
  · exact step45_part2 j
  · exact step45_part3 j
  · exact step45_part4 j
  · exact step45_part5 j
  · exact step45_part6 j
  · exact step45_part7 j
  · exact step45_part8 j
  · exact step45_part9 j
  · exact step45_part10 j
  · exact step45_part11 j
  · exact step45_part12 j
  · exact step45_part13 j
  · exact step45_part14 j
  · exact step45_part15 j
  · exact step45_part16 j
  · exact step45_part17 j
  · exact step45_part18 j
  · exact step45_part19 j
  · exact step45_part20 j
  · exact step45_part21 j
  · exact step45_part22 j
  · exact step45_part23 j
  · exact step45_part24 j
  · exact step45_part25 j
  · exact step45_part26 j
  · exact step45_part27 j
  · exact step45_part28 j
  · exact step45_part29 j
  · exact step45_part30 j
  · exact step45_part31 j
  · exact step45_part32 j
  · exact step45_part33 j
  · exact step45_part34 j
  · exact step45_part35 j
  · exact step45_part36 j
  · exact step45_part37 j
  · exact step45_part38 j
  · exact step45_part39 j
  · exact step45_part40 j
  · exact step45_part41 j
  · exact step45_part42 j
  · exact step45_part43 j
  · exact step45_part44 j
  · exact step45_part45 j
  · exact step45_part46 j
  · exact step45_part47 j
  · exact step45_part48 j
  · exact step45_part49 j
  · exact step45_part50 j
  · exact step45_part51 j
  · exact step45_part52 j
  · exact step45_part53 j
  · exact step45_part54 j
  · exact step45_part55 j
  · exact step45_part56 j
  · exact step45_part57 j
  · exact step45_part58 j
  · exact step45_part59 j
  · exact step45_part60 j
  · exact step45_part61 j
  · exact step45_part62 j
  · exact step45_part63 j
private theorem step45_all (i : Fin 8192) : (sparseHamiltonian (state 45) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 46 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  simpa only [hi] using step45_blocks b j
theorem step45 : (fun i => sparseHamiltonian (state 45) i + (if i.val == 4861 then (0 : Int) else 0)) = state 46 := funext step45_all
private theorem step46_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨0+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨128+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨256+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨384+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨512+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨640+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨768+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨896+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨1024+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨1152+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨1280+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨1408+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨1536+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨1664+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨1792+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨1920+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨2048+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨2176+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨2304+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨2432+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨2560+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨2688+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨2816+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨2944+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨3072+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨3200+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨3328+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨3456+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨3584+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨3712+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨3840+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨3968+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨4096+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨4224+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨4352+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨4480+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨4608+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨4736+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨4864+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨4992+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨5120+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨5248+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨5376+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨5504+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨5632+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨5760+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨5888+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨6016+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨6144+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨6272+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨6400+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨6528+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨6656+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨6784+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨6912+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨7040+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨7168+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨7296+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨7424+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨7552+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨7680+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨7808+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨7936+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 46) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨8064+j.val, by omega⟩ := by
  decide +kernel
private theorem step46_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 46) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step46_part0 j
  · exact step46_part1 j
  · exact step46_part2 j
  · exact step46_part3 j
  · exact step46_part4 j
  · exact step46_part5 j
  · exact step46_part6 j
  · exact step46_part7 j
  · exact step46_part8 j
  · exact step46_part9 j
  · exact step46_part10 j
  · exact step46_part11 j
  · exact step46_part12 j
  · exact step46_part13 j
  · exact step46_part14 j
  · exact step46_part15 j
  · exact step46_part16 j
  · exact step46_part17 j
  · exact step46_part18 j
  · exact step46_part19 j
  · exact step46_part20 j
  · exact step46_part21 j
  · exact step46_part22 j
  · exact step46_part23 j
  · exact step46_part24 j
  · exact step46_part25 j
  · exact step46_part26 j
  · exact step46_part27 j
  · exact step46_part28 j
  · exact step46_part29 j
  · exact step46_part30 j
  · exact step46_part31 j
  · exact step46_part32 j
  · exact step46_part33 j
  · exact step46_part34 j
  · exact step46_part35 j
  · exact step46_part36 j
  · exact step46_part37 j
  · exact step46_part38 j
  · exact step46_part39 j
  · exact step46_part40 j
  · exact step46_part41 j
  · exact step46_part42 j
  · exact step46_part43 j
  · exact step46_part44 j
  · exact step46_part45 j
  · exact step46_part46 j
  · exact step46_part47 j
  · exact step46_part48 j
  · exact step46_part49 j
  · exact step46_part50 j
  · exact step46_part51 j
  · exact step46_part52 j
  · exact step46_part53 j
  · exact step46_part54 j
  · exact step46_part55 j
  · exact step46_part56 j
  · exact step46_part57 j
  · exact step46_part58 j
  · exact step46_part59 j
  · exact step46_part60 j
  · exact step46_part61 j
  · exact step46_part62 j
  · exact step46_part63 j
private theorem step46_all (i : Fin 8192) : (sparseHamiltonian (state 46) i + (if (i : Fin 8192).val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  simpa only [hi] using step46_blocks b j
theorem step46 : (fun i => sparseHamiltonian (state 46) i + (if i.val == 4861 then (-24185673946500264 : Int) else 0)) = state 47 := funext step46_all
private theorem step47_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨0+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨128+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨256+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨384+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨512+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨640+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨768+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨896+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨1024+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨1152+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨1280+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨1408+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨1536+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨1664+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨1792+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨1920+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨2048+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨2176+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨2304+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨2432+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨2560+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨2688+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨2816+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨2944+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨3072+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨3200+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨3328+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨3456+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨3584+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨3712+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨3840+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨3968+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨4096+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨4224+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨4352+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨4480+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨4608+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨4736+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨4864+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨4992+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨5120+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨5248+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨5376+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨5504+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨5632+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨5760+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨5888+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨6016+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨6144+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨6272+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨6400+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨6528+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨6656+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨6784+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨6912+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨7040+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨7168+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨7296+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨7424+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨7552+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨7680+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨7808+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨7936+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 47) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨8064+j.val, by omega⟩ := by
  decide +kernel
private theorem step47_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 47) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step47_part0 j
  · exact step47_part1 j
  · exact step47_part2 j
  · exact step47_part3 j
  · exact step47_part4 j
  · exact step47_part5 j
  · exact step47_part6 j
  · exact step47_part7 j
  · exact step47_part8 j
  · exact step47_part9 j
  · exact step47_part10 j
  · exact step47_part11 j
  · exact step47_part12 j
  · exact step47_part13 j
  · exact step47_part14 j
  · exact step47_part15 j
  · exact step47_part16 j
  · exact step47_part17 j
  · exact step47_part18 j
  · exact step47_part19 j
  · exact step47_part20 j
  · exact step47_part21 j
  · exact step47_part22 j
  · exact step47_part23 j
  · exact step47_part24 j
  · exact step47_part25 j
  · exact step47_part26 j
  · exact step47_part27 j
  · exact step47_part28 j
  · exact step47_part29 j
  · exact step47_part30 j
  · exact step47_part31 j
  · exact step47_part32 j
  · exact step47_part33 j
  · exact step47_part34 j
  · exact step47_part35 j
  · exact step47_part36 j
  · exact step47_part37 j
  · exact step47_part38 j
  · exact step47_part39 j
  · exact step47_part40 j
  · exact step47_part41 j
  · exact step47_part42 j
  · exact step47_part43 j
  · exact step47_part44 j
  · exact step47_part45 j
  · exact step47_part46 j
  · exact step47_part47 j
  · exact step47_part48 j
  · exact step47_part49 j
  · exact step47_part50 j
  · exact step47_part51 j
  · exact step47_part52 j
  · exact step47_part53 j
  · exact step47_part54 j
  · exact step47_part55 j
  · exact step47_part56 j
  · exact step47_part57 j
  · exact step47_part58 j
  · exact step47_part59 j
  · exact step47_part60 j
  · exact step47_part61 j
  · exact step47_part62 j
  · exact step47_part63 j
private theorem step47_all (i : Fin 8192) : (sparseHamiltonian (state 47) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 48 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  simpa only [hi] using step47_blocks b j
theorem step47 : (fun i => sparseHamiltonian (state 47) i + (if i.val == 4861 then (0 : Int) else 0)) = state 48 := funext step47_all

end D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner
