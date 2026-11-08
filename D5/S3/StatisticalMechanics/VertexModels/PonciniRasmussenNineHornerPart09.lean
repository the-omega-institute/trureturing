/- GID: D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart09
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart09
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
private theorem step36_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step36_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step36_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step36_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step36_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step36_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step36_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step36_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step36_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step36_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step36_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step36_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step36_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step36_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step36_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step36_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step36_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step36_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step36_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step36_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step36_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step36_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step36_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step36_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step36_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step36_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step36_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step36_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step36_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step36_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step36_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step36_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step36_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step36_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step36_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step36_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step36_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step36_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step36_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step36_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step36_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step36_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step36_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step36_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step36_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step36_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step36_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step36_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step36_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step36_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step36_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step36_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step36_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step36_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step36_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step36_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step36_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step36_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step36_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step36_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step36_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step36_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step36_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step36_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 36) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step36_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 36) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step36_part0 j
  · exact step36_part1 j
  · exact step36_part2 j
  · exact step36_part3 j
  · exact step36_part4 j
  · exact step36_part5 j
  · exact step36_part6 j
  · exact step36_part7 j
  · exact step36_part8 j
  · exact step36_part9 j
  · exact step36_part10 j
  · exact step36_part11 j
  · exact step36_part12 j
  · exact step36_part13 j
  · exact step36_part14 j
  · exact step36_part15 j
  · exact step36_part16 j
  · exact step36_part17 j
  · exact step36_part18 j
  · exact step36_part19 j
  · exact step36_part20 j
  · exact step36_part21 j
  · exact step36_part22 j
  · exact step36_part23 j
  · exact step36_part24 j
  · exact step36_part25 j
  · exact step36_part26 j
  · exact step36_part27 j
  · exact step36_part28 j
  · exact step36_part29 j
  · exact step36_part30 j
  · exact step36_part31 j
  · exact step36_part32 j
  · exact step36_part33 j
  · exact step36_part34 j
  · exact step36_part35 j
  · exact step36_part36 j
  · exact step36_part37 j
  · exact step36_part38 j
  · exact step36_part39 j
  · exact step36_part40 j
  · exact step36_part41 j
  · exact step36_part42 j
  · exact step36_part43 j
  · exact step36_part44 j
  · exact step36_part45 j
  · exact step36_part46 j
  · exact step36_part47 j
  · exact step36_part48 j
  · exact step36_part49 j
  · exact step36_part50 j
  · exact step36_part51 j
  · exact step36_part52 j
  · exact step36_part53 j
  · exact step36_part54 j
  · exact step36_part55 j
  · exact step36_part56 j
  · exact step36_part57 j
  · exact step36_part58 j
  · exact step36_part59 j
  · exact step36_part60 j
  · exact step36_part61 j
  · exact step36_part62 j
  · exact step36_part63 j
private theorem step36_all (i : Fin 8192) : (sparseHamiltonian (state 36) i + (if (i : Fin 8192).val == 4861 then (324477075047489821 : Int) else 0)) = state 37 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step36_blocks b j
theorem step36 : (fun i => sparseHamiltonian (state 36) i + (if i.val == 4861 then (324477075047489821 : Int) else 0)) = state 37 := funext step36_all
private theorem step37_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step37_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step37_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step37_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step37_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step37_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step37_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step37_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step37_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step37_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step37_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step37_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step37_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step37_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step37_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step37_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step37_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step37_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step37_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step37_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step37_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step37_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step37_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step37_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step37_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step37_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step37_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step37_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step37_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step37_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step37_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step37_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step37_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step37_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step37_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step37_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step37_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step37_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step37_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step37_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step37_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step37_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step37_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step37_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step37_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step37_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step37_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step37_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step37_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step37_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step37_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step37_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step37_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step37_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step37_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step37_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step37_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step37_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step37_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step37_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step37_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step37_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step37_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step37_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 37) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step37_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 37) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step37_part0 j
  · exact step37_part1 j
  · exact step37_part2 j
  · exact step37_part3 j
  · exact step37_part4 j
  · exact step37_part5 j
  · exact step37_part6 j
  · exact step37_part7 j
  · exact step37_part8 j
  · exact step37_part9 j
  · exact step37_part10 j
  · exact step37_part11 j
  · exact step37_part12 j
  · exact step37_part13 j
  · exact step37_part14 j
  · exact step37_part15 j
  · exact step37_part16 j
  · exact step37_part17 j
  · exact step37_part18 j
  · exact step37_part19 j
  · exact step37_part20 j
  · exact step37_part21 j
  · exact step37_part22 j
  · exact step37_part23 j
  · exact step37_part24 j
  · exact step37_part25 j
  · exact step37_part26 j
  · exact step37_part27 j
  · exact step37_part28 j
  · exact step37_part29 j
  · exact step37_part30 j
  · exact step37_part31 j
  · exact step37_part32 j
  · exact step37_part33 j
  · exact step37_part34 j
  · exact step37_part35 j
  · exact step37_part36 j
  · exact step37_part37 j
  · exact step37_part38 j
  · exact step37_part39 j
  · exact step37_part40 j
  · exact step37_part41 j
  · exact step37_part42 j
  · exact step37_part43 j
  · exact step37_part44 j
  · exact step37_part45 j
  · exact step37_part46 j
  · exact step37_part47 j
  · exact step37_part48 j
  · exact step37_part49 j
  · exact step37_part50 j
  · exact step37_part51 j
  · exact step37_part52 j
  · exact step37_part53 j
  · exact step37_part54 j
  · exact step37_part55 j
  · exact step37_part56 j
  · exact step37_part57 j
  · exact step37_part58 j
  · exact step37_part59 j
  · exact step37_part60 j
  · exact step37_part61 j
  · exact step37_part62 j
  · exact step37_part63 j
private theorem step37_all (i : Fin 8192) : (sparseHamiltonian (state 37) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 38 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step37_blocks b j
theorem step37 : (fun i => sparseHamiltonian (state 37) i + (if i.val == 4861 then (0 : Int) else 0)) = state 38 := funext step37_all
private theorem step38_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step38_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step38_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step38_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step38_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step38_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step38_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step38_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step38_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step38_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step38_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step38_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step38_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step38_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step38_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step38_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step38_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step38_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step38_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step38_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step38_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step38_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step38_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step38_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step38_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step38_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step38_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step38_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step38_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step38_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step38_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step38_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step38_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step38_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step38_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step38_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step38_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step38_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step38_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step38_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step38_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step38_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step38_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step38_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step38_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step38_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step38_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step38_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step38_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step38_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step38_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step38_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step38_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step38_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step38_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step38_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step38_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step38_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step38_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step38_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step38_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step38_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step38_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step38_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 38) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step38_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 38) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step38_part0 j
  · exact step38_part1 j
  · exact step38_part2 j
  · exact step38_part3 j
  · exact step38_part4 j
  · exact step38_part5 j
  · exact step38_part6 j
  · exact step38_part7 j
  · exact step38_part8 j
  · exact step38_part9 j
  · exact step38_part10 j
  · exact step38_part11 j
  · exact step38_part12 j
  · exact step38_part13 j
  · exact step38_part14 j
  · exact step38_part15 j
  · exact step38_part16 j
  · exact step38_part17 j
  · exact step38_part18 j
  · exact step38_part19 j
  · exact step38_part20 j
  · exact step38_part21 j
  · exact step38_part22 j
  · exact step38_part23 j
  · exact step38_part24 j
  · exact step38_part25 j
  · exact step38_part26 j
  · exact step38_part27 j
  · exact step38_part28 j
  · exact step38_part29 j
  · exact step38_part30 j
  · exact step38_part31 j
  · exact step38_part32 j
  · exact step38_part33 j
  · exact step38_part34 j
  · exact step38_part35 j
  · exact step38_part36 j
  · exact step38_part37 j
  · exact step38_part38 j
  · exact step38_part39 j
  · exact step38_part40 j
  · exact step38_part41 j
  · exact step38_part42 j
  · exact step38_part43 j
  · exact step38_part44 j
  · exact step38_part45 j
  · exact step38_part46 j
  · exact step38_part47 j
  · exact step38_part48 j
  · exact step38_part49 j
  · exact step38_part50 j
  · exact step38_part51 j
  · exact step38_part52 j
  · exact step38_part53 j
  · exact step38_part54 j
  · exact step38_part55 j
  · exact step38_part56 j
  · exact step38_part57 j
  · exact step38_part58 j
  · exact step38_part59 j
  · exact step38_part60 j
  · exact step38_part61 j
  · exact step38_part62 j
  · exact step38_part63 j
private theorem step38_all (i : Fin 8192) : (sparseHamiltonian (state 38) i + (if (i : Fin 8192).val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step38_blocks b j
theorem step38 : (fun i => sparseHamiltonian (state 38) i + (if i.val == 4861 then (-338328989148555271 : Int) else 0)) = state 39 := funext step38_all
private theorem step39_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step39_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step39_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step39_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step39_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step39_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step39_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step39_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step39_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step39_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step39_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step39_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step39_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step39_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step39_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step39_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step39_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step39_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step39_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step39_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step39_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step39_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step39_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step39_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step39_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step39_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step39_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step39_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step39_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step39_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step39_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step39_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step39_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step39_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step39_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step39_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step39_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step39_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step39_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step39_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step39_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step39_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step39_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step39_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step39_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step39_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step39_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step39_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step39_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step39_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step39_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step39_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step39_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step39_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step39_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step39_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step39_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step39_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step39_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step39_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step39_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step39_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step39_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step39_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 39) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step39_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 39) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step39_part0 j
  · exact step39_part1 j
  · exact step39_part2 j
  · exact step39_part3 j
  · exact step39_part4 j
  · exact step39_part5 j
  · exact step39_part6 j
  · exact step39_part7 j
  · exact step39_part8 j
  · exact step39_part9 j
  · exact step39_part10 j
  · exact step39_part11 j
  · exact step39_part12 j
  · exact step39_part13 j
  · exact step39_part14 j
  · exact step39_part15 j
  · exact step39_part16 j
  · exact step39_part17 j
  · exact step39_part18 j
  · exact step39_part19 j
  · exact step39_part20 j
  · exact step39_part21 j
  · exact step39_part22 j
  · exact step39_part23 j
  · exact step39_part24 j
  · exact step39_part25 j
  · exact step39_part26 j
  · exact step39_part27 j
  · exact step39_part28 j
  · exact step39_part29 j
  · exact step39_part30 j
  · exact step39_part31 j
  · exact step39_part32 j
  · exact step39_part33 j
  · exact step39_part34 j
  · exact step39_part35 j
  · exact step39_part36 j
  · exact step39_part37 j
  · exact step39_part38 j
  · exact step39_part39 j
  · exact step39_part40 j
  · exact step39_part41 j
  · exact step39_part42 j
  · exact step39_part43 j
  · exact step39_part44 j
  · exact step39_part45 j
  · exact step39_part46 j
  · exact step39_part47 j
  · exact step39_part48 j
  · exact step39_part49 j
  · exact step39_part50 j
  · exact step39_part51 j
  · exact step39_part52 j
  · exact step39_part53 j
  · exact step39_part54 j
  · exact step39_part55 j
  · exact step39_part56 j
  · exact step39_part57 j
  · exact step39_part58 j
  · exact step39_part59 j
  · exact step39_part60 j
  · exact step39_part61 j
  · exact step39_part62 j
  · exact step39_part63 j
private theorem step39_all (i : Fin 8192) : (sparseHamiltonian (state 39) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 40 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step39_blocks b j
theorem step39 : (fun i => sparseHamiltonian (state 39) i + (if i.val == 4861 then (0 : Int) else 0)) = state 40 := funext step39_all

end D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner
