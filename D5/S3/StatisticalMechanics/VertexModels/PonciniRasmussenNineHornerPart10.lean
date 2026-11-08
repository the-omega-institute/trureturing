/- GID: D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart10
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart10
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
private theorem step40_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step40_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step40_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step40_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step40_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step40_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step40_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step40_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step40_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step40_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step40_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step40_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step40_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step40_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step40_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step40_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step40_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step40_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step40_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step40_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step40_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step40_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step40_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step40_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step40_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step40_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step40_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step40_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step40_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step40_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step40_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step40_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step40_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step40_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step40_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step40_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step40_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step40_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step40_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step40_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step40_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step40_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step40_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step40_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step40_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step40_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step40_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step40_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step40_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step40_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step40_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step40_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step40_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step40_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step40_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step40_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step40_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step40_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step40_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step40_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step40_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step40_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step40_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step40_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 40) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step40_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 40) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step40_part0 j
  · exact step40_part1 j
  · exact step40_part2 j
  · exact step40_part3 j
  · exact step40_part4 j
  · exact step40_part5 j
  · exact step40_part6 j
  · exact step40_part7 j
  · exact step40_part8 j
  · exact step40_part9 j
  · exact step40_part10 j
  · exact step40_part11 j
  · exact step40_part12 j
  · exact step40_part13 j
  · exact step40_part14 j
  · exact step40_part15 j
  · exact step40_part16 j
  · exact step40_part17 j
  · exact step40_part18 j
  · exact step40_part19 j
  · exact step40_part20 j
  · exact step40_part21 j
  · exact step40_part22 j
  · exact step40_part23 j
  · exact step40_part24 j
  · exact step40_part25 j
  · exact step40_part26 j
  · exact step40_part27 j
  · exact step40_part28 j
  · exact step40_part29 j
  · exact step40_part30 j
  · exact step40_part31 j
  · exact step40_part32 j
  · exact step40_part33 j
  · exact step40_part34 j
  · exact step40_part35 j
  · exact step40_part36 j
  · exact step40_part37 j
  · exact step40_part38 j
  · exact step40_part39 j
  · exact step40_part40 j
  · exact step40_part41 j
  · exact step40_part42 j
  · exact step40_part43 j
  · exact step40_part44 j
  · exact step40_part45 j
  · exact step40_part46 j
  · exact step40_part47 j
  · exact step40_part48 j
  · exact step40_part49 j
  · exact step40_part50 j
  · exact step40_part51 j
  · exact step40_part52 j
  · exact step40_part53 j
  · exact step40_part54 j
  · exact step40_part55 j
  · exact step40_part56 j
  · exact step40_part57 j
  · exact step40_part58 j
  · exact step40_part59 j
  · exact step40_part60 j
  · exact step40_part61 j
  · exact step40_part62 j
  · exact step40_part63 j
private theorem step40_all (i : Fin 8192) : (sparseHamiltonian (state 40) i + (if (i : Fin 8192).val == 4861 then (272486148975235188 : Int) else 0)) = state 41 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step40_blocks b j
theorem step40 : (fun i => sparseHamiltonian (state 40) i + (if i.val == 4861 then (272486148975235188 : Int) else 0)) = state 41 := funext step40_all
private theorem step41_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step41_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step41_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step41_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step41_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step41_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step41_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step41_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step41_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step41_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step41_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step41_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step41_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step41_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step41_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step41_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step41_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step41_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step41_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step41_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step41_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step41_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step41_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step41_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step41_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step41_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step41_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step41_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step41_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step41_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step41_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step41_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step41_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step41_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step41_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step41_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step41_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step41_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step41_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step41_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step41_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step41_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step41_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step41_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step41_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step41_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step41_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step41_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step41_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step41_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step41_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step41_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step41_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step41_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step41_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step41_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step41_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step41_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step41_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step41_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step41_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step41_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step41_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step41_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 41) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step41_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 41) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step41_part0 j
  · exact step41_part1 j
  · exact step41_part2 j
  · exact step41_part3 j
  · exact step41_part4 j
  · exact step41_part5 j
  · exact step41_part6 j
  · exact step41_part7 j
  · exact step41_part8 j
  · exact step41_part9 j
  · exact step41_part10 j
  · exact step41_part11 j
  · exact step41_part12 j
  · exact step41_part13 j
  · exact step41_part14 j
  · exact step41_part15 j
  · exact step41_part16 j
  · exact step41_part17 j
  · exact step41_part18 j
  · exact step41_part19 j
  · exact step41_part20 j
  · exact step41_part21 j
  · exact step41_part22 j
  · exact step41_part23 j
  · exact step41_part24 j
  · exact step41_part25 j
  · exact step41_part26 j
  · exact step41_part27 j
  · exact step41_part28 j
  · exact step41_part29 j
  · exact step41_part30 j
  · exact step41_part31 j
  · exact step41_part32 j
  · exact step41_part33 j
  · exact step41_part34 j
  · exact step41_part35 j
  · exact step41_part36 j
  · exact step41_part37 j
  · exact step41_part38 j
  · exact step41_part39 j
  · exact step41_part40 j
  · exact step41_part41 j
  · exact step41_part42 j
  · exact step41_part43 j
  · exact step41_part44 j
  · exact step41_part45 j
  · exact step41_part46 j
  · exact step41_part47 j
  · exact step41_part48 j
  · exact step41_part49 j
  · exact step41_part50 j
  · exact step41_part51 j
  · exact step41_part52 j
  · exact step41_part53 j
  · exact step41_part54 j
  · exact step41_part55 j
  · exact step41_part56 j
  · exact step41_part57 j
  · exact step41_part58 j
  · exact step41_part59 j
  · exact step41_part60 j
  · exact step41_part61 j
  · exact step41_part62 j
  · exact step41_part63 j
private theorem step41_all (i : Fin 8192) : (sparseHamiltonian (state 41) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 42 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step41_blocks b j
theorem step41 : (fun i => sparseHamiltonian (state 41) i + (if i.val == 4861 then (0 : Int) else 0)) = state 42 := funext step41_all
private theorem step42_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step42_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step42_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step42_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step42_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step42_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step42_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step42_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step42_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step42_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step42_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step42_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step42_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step42_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step42_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step42_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step42_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step42_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step42_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step42_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step42_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step42_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step42_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step42_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step42_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step42_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step42_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step42_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step42_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step42_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step42_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step42_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step42_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step42_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step42_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step42_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step42_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step42_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step42_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step42_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step42_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step42_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step42_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step42_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step42_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step42_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step42_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step42_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step42_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step42_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step42_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step42_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step42_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step42_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step42_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step42_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step42_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step42_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step42_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step42_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step42_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step42_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step42_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step42_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 42) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step42_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 42) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step42_part0 j
  · exact step42_part1 j
  · exact step42_part2 j
  · exact step42_part3 j
  · exact step42_part4 j
  · exact step42_part5 j
  · exact step42_part6 j
  · exact step42_part7 j
  · exact step42_part8 j
  · exact step42_part9 j
  · exact step42_part10 j
  · exact step42_part11 j
  · exact step42_part12 j
  · exact step42_part13 j
  · exact step42_part14 j
  · exact step42_part15 j
  · exact step42_part16 j
  · exact step42_part17 j
  · exact step42_part18 j
  · exact step42_part19 j
  · exact step42_part20 j
  · exact step42_part21 j
  · exact step42_part22 j
  · exact step42_part23 j
  · exact step42_part24 j
  · exact step42_part25 j
  · exact step42_part26 j
  · exact step42_part27 j
  · exact step42_part28 j
  · exact step42_part29 j
  · exact step42_part30 j
  · exact step42_part31 j
  · exact step42_part32 j
  · exact step42_part33 j
  · exact step42_part34 j
  · exact step42_part35 j
  · exact step42_part36 j
  · exact step42_part37 j
  · exact step42_part38 j
  · exact step42_part39 j
  · exact step42_part40 j
  · exact step42_part41 j
  · exact step42_part42 j
  · exact step42_part43 j
  · exact step42_part44 j
  · exact step42_part45 j
  · exact step42_part46 j
  · exact step42_part47 j
  · exact step42_part48 j
  · exact step42_part49 j
  · exact step42_part50 j
  · exact step42_part51 j
  · exact step42_part52 j
  · exact step42_part53 j
  · exact step42_part54 j
  · exact step42_part55 j
  · exact step42_part56 j
  · exact step42_part57 j
  · exact step42_part58 j
  · exact step42_part59 j
  · exact step42_part60 j
  · exact step42_part61 j
  · exact step42_part62 j
  · exact step42_part63 j
private theorem step42_all (i : Fin 8192) : (sparseHamiltonian (state 42) i + (if (i : Fin 8192).val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step42_blocks b j
theorem step42 : (fun i => sparseHamiltonian (state 42) i + (if i.val == 4861 then (-166252500600659604 : Int) else 0)) = state 43 := funext step42_all
private theorem step43_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step43_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step43_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step43_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step43_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step43_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step43_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step43_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step43_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step43_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step43_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step43_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step43_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step43_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step43_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step43_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step43_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step43_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step43_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step43_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step43_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step43_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step43_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step43_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step43_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step43_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step43_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step43_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step43_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step43_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step43_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step43_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step43_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step43_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step43_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step43_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step43_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step43_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step43_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step43_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step43_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step43_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step43_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step43_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step43_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step43_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step43_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step43_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step43_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step43_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step43_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step43_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step43_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step43_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step43_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step43_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step43_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step43_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step43_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step43_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step43_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step43_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step43_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step43_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 43) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step43_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 43) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step43_part0 j
  · exact step43_part1 j
  · exact step43_part2 j
  · exact step43_part3 j
  · exact step43_part4 j
  · exact step43_part5 j
  · exact step43_part6 j
  · exact step43_part7 j
  · exact step43_part8 j
  · exact step43_part9 j
  · exact step43_part10 j
  · exact step43_part11 j
  · exact step43_part12 j
  · exact step43_part13 j
  · exact step43_part14 j
  · exact step43_part15 j
  · exact step43_part16 j
  · exact step43_part17 j
  · exact step43_part18 j
  · exact step43_part19 j
  · exact step43_part20 j
  · exact step43_part21 j
  · exact step43_part22 j
  · exact step43_part23 j
  · exact step43_part24 j
  · exact step43_part25 j
  · exact step43_part26 j
  · exact step43_part27 j
  · exact step43_part28 j
  · exact step43_part29 j
  · exact step43_part30 j
  · exact step43_part31 j
  · exact step43_part32 j
  · exact step43_part33 j
  · exact step43_part34 j
  · exact step43_part35 j
  · exact step43_part36 j
  · exact step43_part37 j
  · exact step43_part38 j
  · exact step43_part39 j
  · exact step43_part40 j
  · exact step43_part41 j
  · exact step43_part42 j
  · exact step43_part43 j
  · exact step43_part44 j
  · exact step43_part45 j
  · exact step43_part46 j
  · exact step43_part47 j
  · exact step43_part48 j
  · exact step43_part49 j
  · exact step43_part50 j
  · exact step43_part51 j
  · exact step43_part52 j
  · exact step43_part53 j
  · exact step43_part54 j
  · exact step43_part55 j
  · exact step43_part56 j
  · exact step43_part57 j
  · exact step43_part58 j
  · exact step43_part59 j
  · exact step43_part60 j
  · exact step43_part61 j
  · exact step43_part62 j
  · exact step43_part63 j
private theorem step43_all (i : Fin 8192) : (sparseHamiltonian (state 43) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 44 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step43_blocks b j
theorem step43 : (fun i => sparseHamiltonian (state 43) i + (if i.val == 4861 then (0 : Int) else 0)) = state 44 := funext step43_all

end D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner
