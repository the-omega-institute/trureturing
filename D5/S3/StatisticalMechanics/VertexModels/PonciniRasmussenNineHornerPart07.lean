/- GID: D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart07
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart07
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
private theorem step28_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step28_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step28_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step28_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step28_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step28_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step28_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step28_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step28_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step28_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step28_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step28_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step28_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step28_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step28_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step28_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step28_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step28_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step28_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step28_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step28_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step28_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step28_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step28_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step28_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step28_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step28_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step28_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step28_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step28_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step28_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step28_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step28_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step28_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step28_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step28_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step28_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step28_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step28_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step28_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step28_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step28_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step28_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step28_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step28_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step28_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step28_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step28_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step28_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step28_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step28_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step28_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step28_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step28_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step28_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step28_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step28_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step28_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step28_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step28_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step28_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step28_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step28_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step28_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 28) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step28_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 28) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step28_part0 j
  · exact step28_part1 j
  · exact step28_part2 j
  · exact step28_part3 j
  · exact step28_part4 j
  · exact step28_part5 j
  · exact step28_part6 j
  · exact step28_part7 j
  · exact step28_part8 j
  · exact step28_part9 j
  · exact step28_part10 j
  · exact step28_part11 j
  · exact step28_part12 j
  · exact step28_part13 j
  · exact step28_part14 j
  · exact step28_part15 j
  · exact step28_part16 j
  · exact step28_part17 j
  · exact step28_part18 j
  · exact step28_part19 j
  · exact step28_part20 j
  · exact step28_part21 j
  · exact step28_part22 j
  · exact step28_part23 j
  · exact step28_part24 j
  · exact step28_part25 j
  · exact step28_part26 j
  · exact step28_part27 j
  · exact step28_part28 j
  · exact step28_part29 j
  · exact step28_part30 j
  · exact step28_part31 j
  · exact step28_part32 j
  · exact step28_part33 j
  · exact step28_part34 j
  · exact step28_part35 j
  · exact step28_part36 j
  · exact step28_part37 j
  · exact step28_part38 j
  · exact step28_part39 j
  · exact step28_part40 j
  · exact step28_part41 j
  · exact step28_part42 j
  · exact step28_part43 j
  · exact step28_part44 j
  · exact step28_part45 j
  · exact step28_part46 j
  · exact step28_part47 j
  · exact step28_part48 j
  · exact step28_part49 j
  · exact step28_part50 j
  · exact step28_part51 j
  · exact step28_part52 j
  · exact step28_part53 j
  · exact step28_part54 j
  · exact step28_part55 j
  · exact step28_part56 j
  · exact step28_part57 j
  · exact step28_part58 j
  · exact step28_part59 j
  · exact step28_part60 j
  · exact step28_part61 j
  · exact step28_part62 j
  · exact step28_part63 j
private theorem step28_all (i : Fin 8192) : (sparseHamiltonian (state 28) i + (if (i : Fin 8192).val == 4861 then (26973986982247197 : Int) else 0)) = state 29 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step28_blocks b j
theorem step28 : (fun i => sparseHamiltonian (state 28) i + (if i.val == 4861 then (26973986982247197 : Int) else 0)) = state 29 := funext step28_all
private theorem step29_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step29_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step29_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step29_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step29_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step29_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step29_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step29_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step29_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step29_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step29_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step29_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step29_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step29_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step29_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step29_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step29_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step29_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step29_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step29_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step29_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step29_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step29_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step29_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step29_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step29_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step29_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step29_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step29_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step29_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step29_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step29_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step29_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step29_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step29_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step29_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step29_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step29_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step29_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step29_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step29_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step29_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step29_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step29_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step29_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step29_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step29_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step29_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step29_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step29_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step29_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step29_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step29_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step29_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step29_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step29_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step29_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step29_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step29_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step29_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step29_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step29_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step29_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step29_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 29) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step29_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 29) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step29_part0 j
  · exact step29_part1 j
  · exact step29_part2 j
  · exact step29_part3 j
  · exact step29_part4 j
  · exact step29_part5 j
  · exact step29_part6 j
  · exact step29_part7 j
  · exact step29_part8 j
  · exact step29_part9 j
  · exact step29_part10 j
  · exact step29_part11 j
  · exact step29_part12 j
  · exact step29_part13 j
  · exact step29_part14 j
  · exact step29_part15 j
  · exact step29_part16 j
  · exact step29_part17 j
  · exact step29_part18 j
  · exact step29_part19 j
  · exact step29_part20 j
  · exact step29_part21 j
  · exact step29_part22 j
  · exact step29_part23 j
  · exact step29_part24 j
  · exact step29_part25 j
  · exact step29_part26 j
  · exact step29_part27 j
  · exact step29_part28 j
  · exact step29_part29 j
  · exact step29_part30 j
  · exact step29_part31 j
  · exact step29_part32 j
  · exact step29_part33 j
  · exact step29_part34 j
  · exact step29_part35 j
  · exact step29_part36 j
  · exact step29_part37 j
  · exact step29_part38 j
  · exact step29_part39 j
  · exact step29_part40 j
  · exact step29_part41 j
  · exact step29_part42 j
  · exact step29_part43 j
  · exact step29_part44 j
  · exact step29_part45 j
  · exact step29_part46 j
  · exact step29_part47 j
  · exact step29_part48 j
  · exact step29_part49 j
  · exact step29_part50 j
  · exact step29_part51 j
  · exact step29_part52 j
  · exact step29_part53 j
  · exact step29_part54 j
  · exact step29_part55 j
  · exact step29_part56 j
  · exact step29_part57 j
  · exact step29_part58 j
  · exact step29_part59 j
  · exact step29_part60 j
  · exact step29_part61 j
  · exact step29_part62 j
  · exact step29_part63 j
private theorem step29_all (i : Fin 8192) : (sparseHamiltonian (state 29) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 30 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step29_blocks b j
theorem step29 : (fun i => sparseHamiltonian (state 29) i + (if i.val == 4861 then (0 : Int) else 0)) = state 30 := funext step29_all
private theorem step30_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step30_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step30_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step30_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step30_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step30_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step30_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step30_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step30_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step30_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step30_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step30_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step30_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step30_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step30_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step30_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step30_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step30_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step30_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step30_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step30_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step30_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step30_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step30_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step30_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step30_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step30_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step30_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step30_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step30_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step30_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step30_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step30_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step30_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step30_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step30_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step30_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step30_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step30_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step30_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step30_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step30_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step30_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step30_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step30_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step30_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step30_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step30_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step30_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step30_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step30_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step30_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step30_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step30_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step30_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step30_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step30_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step30_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step30_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step30_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step30_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step30_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step30_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step30_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 30) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step30_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 30) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step30_part0 j
  · exact step30_part1 j
  · exact step30_part2 j
  · exact step30_part3 j
  · exact step30_part4 j
  · exact step30_part5 j
  · exact step30_part6 j
  · exact step30_part7 j
  · exact step30_part8 j
  · exact step30_part9 j
  · exact step30_part10 j
  · exact step30_part11 j
  · exact step30_part12 j
  · exact step30_part13 j
  · exact step30_part14 j
  · exact step30_part15 j
  · exact step30_part16 j
  · exact step30_part17 j
  · exact step30_part18 j
  · exact step30_part19 j
  · exact step30_part20 j
  · exact step30_part21 j
  · exact step30_part22 j
  · exact step30_part23 j
  · exact step30_part24 j
  · exact step30_part25 j
  · exact step30_part26 j
  · exact step30_part27 j
  · exact step30_part28 j
  · exact step30_part29 j
  · exact step30_part30 j
  · exact step30_part31 j
  · exact step30_part32 j
  · exact step30_part33 j
  · exact step30_part34 j
  · exact step30_part35 j
  · exact step30_part36 j
  · exact step30_part37 j
  · exact step30_part38 j
  · exact step30_part39 j
  · exact step30_part40 j
  · exact step30_part41 j
  · exact step30_part42 j
  · exact step30_part43 j
  · exact step30_part44 j
  · exact step30_part45 j
  · exact step30_part46 j
  · exact step30_part47 j
  · exact step30_part48 j
  · exact step30_part49 j
  · exact step30_part50 j
  · exact step30_part51 j
  · exact step30_part52 j
  · exact step30_part53 j
  · exact step30_part54 j
  · exact step30_part55 j
  · exact step30_part56 j
  · exact step30_part57 j
  · exact step30_part58 j
  · exact step30_part59 j
  · exact step30_part60 j
  · exact step30_part61 j
  · exact step30_part62 j
  · exact step30_part63 j
private theorem step30_all (i : Fin 8192) : (sparseHamiltonian (state 30) i + (if (i : Fin 8192).val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step30_blocks b j
theorem step30 : (fun i => sparseHamiltonian (state 30) i + (if i.val == 4861 then (-69786597194594871 : Int) else 0)) = state 31 := funext step30_all
private theorem step31_part0 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨0+j.val, by omega⟩ + (if (⟨0+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨0+j.val, by omega⟩ := by decide +kernel
private theorem step31_part1 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨128+j.val, by omega⟩ + (if (⟨128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨128+j.val, by omega⟩ := by decide +kernel
private theorem step31_part2 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨256+j.val, by omega⟩ + (if (⟨256+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨256+j.val, by omega⟩ := by decide +kernel
private theorem step31_part3 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨384+j.val, by omega⟩ + (if (⟨384+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨384+j.val, by omega⟩ := by decide +kernel
private theorem step31_part4 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨512+j.val, by omega⟩ + (if (⟨512+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨512+j.val, by omega⟩ := by decide +kernel
private theorem step31_part5 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨640+j.val, by omega⟩ + (if (⟨640+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨640+j.val, by omega⟩ := by decide +kernel
private theorem step31_part6 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨768+j.val, by omega⟩ + (if (⟨768+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨768+j.val, by omega⟩ := by decide +kernel
private theorem step31_part7 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨896+j.val, by omega⟩ + (if (⟨896+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨896+j.val, by omega⟩ := by decide +kernel
private theorem step31_part8 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨1024+j.val, by omega⟩ + (if (⟨1024+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨1024+j.val, by omega⟩ := by decide +kernel
private theorem step31_part9 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨1152+j.val, by omega⟩ + (if (⟨1152+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨1152+j.val, by omega⟩ := by decide +kernel
private theorem step31_part10 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨1280+j.val, by omega⟩ + (if (⟨1280+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨1280+j.val, by omega⟩ := by decide +kernel
private theorem step31_part11 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨1408+j.val, by omega⟩ + (if (⟨1408+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨1408+j.val, by omega⟩ := by decide +kernel
private theorem step31_part12 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨1536+j.val, by omega⟩ + (if (⟨1536+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨1536+j.val, by omega⟩ := by decide +kernel
private theorem step31_part13 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨1664+j.val, by omega⟩ + (if (⟨1664+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨1664+j.val, by omega⟩ := by decide +kernel
private theorem step31_part14 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨1792+j.val, by omega⟩ + (if (⟨1792+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨1792+j.val, by omega⟩ := by decide +kernel
private theorem step31_part15 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨1920+j.val, by omega⟩ + (if (⟨1920+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨1920+j.val, by omega⟩ := by decide +kernel
private theorem step31_part16 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨2048+j.val, by omega⟩ + (if (⟨2048+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨2048+j.val, by omega⟩ := by decide +kernel
private theorem step31_part17 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨2176+j.val, by omega⟩ + (if (⟨2176+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨2176+j.val, by omega⟩ := by decide +kernel
private theorem step31_part18 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨2304+j.val, by omega⟩ + (if (⟨2304+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨2304+j.val, by omega⟩ := by decide +kernel
private theorem step31_part19 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨2432+j.val, by omega⟩ + (if (⟨2432+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨2432+j.val, by omega⟩ := by decide +kernel
private theorem step31_part20 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨2560+j.val, by omega⟩ + (if (⟨2560+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨2560+j.val, by omega⟩ := by decide +kernel
private theorem step31_part21 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨2688+j.val, by omega⟩ + (if (⟨2688+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨2688+j.val, by omega⟩ := by decide +kernel
private theorem step31_part22 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨2816+j.val, by omega⟩ + (if (⟨2816+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨2816+j.val, by omega⟩ := by decide +kernel
private theorem step31_part23 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨2944+j.val, by omega⟩ + (if (⟨2944+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨2944+j.val, by omega⟩ := by decide +kernel
private theorem step31_part24 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨3072+j.val, by omega⟩ + (if (⟨3072+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨3072+j.val, by omega⟩ := by decide +kernel
private theorem step31_part25 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨3200+j.val, by omega⟩ + (if (⟨3200+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨3200+j.val, by omega⟩ := by decide +kernel
private theorem step31_part26 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨3328+j.val, by omega⟩ + (if (⟨3328+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨3328+j.val, by omega⟩ := by decide +kernel
private theorem step31_part27 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨3456+j.val, by omega⟩ + (if (⟨3456+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨3456+j.val, by omega⟩ := by decide +kernel
private theorem step31_part28 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨3584+j.val, by omega⟩ + (if (⟨3584+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨3584+j.val, by omega⟩ := by decide +kernel
private theorem step31_part29 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨3712+j.val, by omega⟩ + (if (⟨3712+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨3712+j.val, by omega⟩ := by decide +kernel
private theorem step31_part30 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨3840+j.val, by omega⟩ + (if (⟨3840+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨3840+j.val, by omega⟩ := by decide +kernel
private theorem step31_part31 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨3968+j.val, by omega⟩ + (if (⟨3968+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨3968+j.val, by omega⟩ := by decide +kernel
private theorem step31_part32 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨4096+j.val, by omega⟩ + (if (⟨4096+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨4096+j.val, by omega⟩ := by decide +kernel
private theorem step31_part33 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨4224+j.val, by omega⟩ + (if (⟨4224+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨4224+j.val, by omega⟩ := by decide +kernel
private theorem step31_part34 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨4352+j.val, by omega⟩ + (if (⟨4352+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨4352+j.val, by omega⟩ := by decide +kernel
private theorem step31_part35 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨4480+j.val, by omega⟩ + (if (⟨4480+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨4480+j.val, by omega⟩ := by decide +kernel
private theorem step31_part36 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨4608+j.val, by omega⟩ + (if (⟨4608+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨4608+j.val, by omega⟩ := by decide +kernel
private theorem step31_part37 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨4736+j.val, by omega⟩ + (if (⟨4736+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨4736+j.val, by omega⟩ := by decide +kernel
private theorem step31_part38 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨4864+j.val, by omega⟩ + (if (⟨4864+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨4864+j.val, by omega⟩ := by decide +kernel
private theorem step31_part39 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨4992+j.val, by omega⟩ + (if (⟨4992+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨4992+j.val, by omega⟩ := by decide +kernel
private theorem step31_part40 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨5120+j.val, by omega⟩ + (if (⟨5120+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨5120+j.val, by omega⟩ := by decide +kernel
private theorem step31_part41 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨5248+j.val, by omega⟩ + (if (⟨5248+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨5248+j.val, by omega⟩ := by decide +kernel
private theorem step31_part42 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨5376+j.val, by omega⟩ + (if (⟨5376+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨5376+j.val, by omega⟩ := by decide +kernel
private theorem step31_part43 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨5504+j.val, by omega⟩ + (if (⟨5504+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨5504+j.val, by omega⟩ := by decide +kernel
private theorem step31_part44 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨5632+j.val, by omega⟩ + (if (⟨5632+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨5632+j.val, by omega⟩ := by decide +kernel
private theorem step31_part45 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨5760+j.val, by omega⟩ + (if (⟨5760+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨5760+j.val, by omega⟩ := by decide +kernel
private theorem step31_part46 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨5888+j.val, by omega⟩ + (if (⟨5888+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨5888+j.val, by omega⟩ := by decide +kernel
private theorem step31_part47 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨6016+j.val, by omega⟩ + (if (⟨6016+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨6016+j.val, by omega⟩ := by decide +kernel
private theorem step31_part48 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨6144+j.val, by omega⟩ + (if (⟨6144+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨6144+j.val, by omega⟩ := by decide +kernel
private theorem step31_part49 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨6272+j.val, by omega⟩ + (if (⟨6272+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨6272+j.val, by omega⟩ := by decide +kernel
private theorem step31_part50 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨6400+j.val, by omega⟩ + (if (⟨6400+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨6400+j.val, by omega⟩ := by decide +kernel
private theorem step31_part51 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨6528+j.val, by omega⟩ + (if (⟨6528+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨6528+j.val, by omega⟩ := by decide +kernel
private theorem step31_part52 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨6656+j.val, by omega⟩ + (if (⟨6656+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨6656+j.val, by omega⟩ := by decide +kernel
private theorem step31_part53 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨6784+j.val, by omega⟩ + (if (⟨6784+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨6784+j.val, by omega⟩ := by decide +kernel
private theorem step31_part54 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨6912+j.val, by omega⟩ + (if (⟨6912+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨6912+j.val, by omega⟩ := by decide +kernel
private theorem step31_part55 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨7040+j.val, by omega⟩ + (if (⟨7040+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨7040+j.val, by omega⟩ := by decide +kernel
private theorem step31_part56 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨7168+j.val, by omega⟩ + (if (⟨7168+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨7168+j.val, by omega⟩ := by decide +kernel
private theorem step31_part57 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨7296+j.val, by omega⟩ + (if (⟨7296+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨7296+j.val, by omega⟩ := by decide +kernel
private theorem step31_part58 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨7424+j.val, by omega⟩ + (if (⟨7424+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨7424+j.val, by omega⟩ := by decide +kernel
private theorem step31_part59 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨7552+j.val, by omega⟩ + (if (⟨7552+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨7552+j.val, by omega⟩ := by decide +kernel
private theorem step31_part60 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨7680+j.val, by omega⟩ + (if (⟨7680+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨7680+j.val, by omega⟩ := by decide +kernel
private theorem step31_part61 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨7808+j.val, by omega⟩ + (if (⟨7808+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨7808+j.val, by omega⟩ := by decide +kernel
private theorem step31_part62 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨7936+j.val, by omega⟩ + (if (⟨7936+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨7936+j.val, by omega⟩ := by decide +kernel
private theorem step31_part63 : ∀ j : Fin 128, (sparseHamiltonian (state 31) ⟨8064+j.val, by omega⟩ + (if (⟨8064+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨8064+j.val, by omega⟩ := by decide +kernel
private theorem step31_blocks (b : Fin 64) (j : Fin 128) : (sparseHamiltonian (state 31) ⟨b.val*128+j.val, by omega⟩ + (if (⟨b.val*128+j.val, by omega⟩ : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 ⟨b.val*128+j.val, by omega⟩ := by
  fin_cases b
  · exact step31_part0 j
  · exact step31_part1 j
  · exact step31_part2 j
  · exact step31_part3 j
  · exact step31_part4 j
  · exact step31_part5 j
  · exact step31_part6 j
  · exact step31_part7 j
  · exact step31_part8 j
  · exact step31_part9 j
  · exact step31_part10 j
  · exact step31_part11 j
  · exact step31_part12 j
  · exact step31_part13 j
  · exact step31_part14 j
  · exact step31_part15 j
  · exact step31_part16 j
  · exact step31_part17 j
  · exact step31_part18 j
  · exact step31_part19 j
  · exact step31_part20 j
  · exact step31_part21 j
  · exact step31_part22 j
  · exact step31_part23 j
  · exact step31_part24 j
  · exact step31_part25 j
  · exact step31_part26 j
  · exact step31_part27 j
  · exact step31_part28 j
  · exact step31_part29 j
  · exact step31_part30 j
  · exact step31_part31 j
  · exact step31_part32 j
  · exact step31_part33 j
  · exact step31_part34 j
  · exact step31_part35 j
  · exact step31_part36 j
  · exact step31_part37 j
  · exact step31_part38 j
  · exact step31_part39 j
  · exact step31_part40 j
  · exact step31_part41 j
  · exact step31_part42 j
  · exact step31_part43 j
  · exact step31_part44 j
  · exact step31_part45 j
  · exact step31_part46 j
  · exact step31_part47 j
  · exact step31_part48 j
  · exact step31_part49 j
  · exact step31_part50 j
  · exact step31_part51 j
  · exact step31_part52 j
  · exact step31_part53 j
  · exact step31_part54 j
  · exact step31_part55 j
  · exact step31_part56 j
  · exact step31_part57 j
  · exact step31_part58 j
  · exact step31_part59 j
  · exact step31_part60 j
  · exact step31_part61 j
  · exact step31_part62 j
  · exact step31_part63 j
private theorem step31_all (i : Fin 8192) : (sparseHamiltonian (state 31) i + (if (i : Fin 8192).val == 4861 then (0 : Int) else 0)) = state 32 i := by
  let b : Fin 64 := ⟨i.val/128, by omega⟩
  let j : Fin 128 := ⟨i.val%128, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨b.val*128+j.val, by omega⟩ : Fin 8192) = i := Fin.ext (by dsimp [b,j]; omega)
  have hiNat : b.val*128+j.val = i.val := by dsimp [b,j]; omega
  simpa only [hi, hiNat] using step31_blocks b j
theorem step31 : (fun i => sparseHamiltonian (state 31) i + (if i.val == 4861 then (0 : Int) else 0)) = state 32 := funext step31_all

end D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner
