/- GID: D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.claim; result=D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.result; claim=D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.claim
   digest: A self-dual irreducible extreme thermal process factors on proper sets of levels. -/

import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Matrix.Stochastic

/-! An exact five-level factorization satisfying detailed balance. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.StatisticalMechanics.ThermalProcessSelfDualFactorizationRefutation

open scoped BigOperators Matrix

noncomputable section

/-- Column-stochastic matrices preserving the Gibbs weights. -/
def thermalProcesses {d : ℕ} (g : Fin d → ℝ) : Set (Matrix (Fin d) (Fin d) ℝ) :=
  {T | T ∈ Matrix.colStochastic ℝ (Fin d) ∧ T *ᵥ g = g}

/-- A process acting trivially on at least one level. -/
def actsOnFewerLevels {d : ℕ} (T : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∃ k, T k k = 1

/-- Detailed balance with respect to the Gibbs weights. -/
def selfDual {d : ℕ} (g : Fin d → ℝ) (T : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ i j, T i j * g j = T j i * g i

/-- No nonempty proper set of levels gives a block diagonal decomposition. -/
def irreducible {d : ℕ} (T : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ¬ ∃ S : Finset (Fin d), S.Nonempty ∧ Sᶜ.Nonempty ∧
    ∀ i j, ((i ∈ S ∧ j ∉ S) ∨ (i ∉ S ∧ j ∈ S)) → T i j = 0

/-- The non-self-duality conjecture for irreducible extreme thermal products. -/
def claim : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (g : Fin d → ℝ),
    (∀ i, 0 < g i) → Function.Injective g →
    (∀ i, g i ≤ g ⟨0, by omega⟩) →
    ∀ A B C : Matrix (Fin d) (Fin d) ℝ,
      A ∈ Set.extremePoints ℝ (thermalProcesses g) →
      B ∈ Set.extremePoints ℝ (thermalProcesses g) →
      C ∈ Set.extremePoints ℝ (thermalProcesses g) →
      C = A * B → actsOnFewerLevels A → actsOnFewerLevels B →
      irreducible C → ¬ selfDual g C

private def g : Fin 5 → ℝ := ![8, 7, 4, 2, 3]

private def A : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, 1, 0, 1/2, 0;
     1/4, 0, 1, 1/2, 0;
     1/2, 0, 0, 0, 0;
     1/4, 0, 0, 0, 0;
     0, 0, 0, 0, 1]

private def B : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0;
     0, 1/7, 1, 1, 0;
     0, 1/7, 0, 0, 1;
     0, 2/7, 0, 0, 0;
     0, 3/7, 0, 0, 0]

private def C : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, 2/7, 1, 1, 0;
     1/4, 2/7, 0, 0, 1;
     1/2, 0, 0, 0, 0;
     1/4, 0, 0, 0, 0;
     0, 3/7, 0, 0, 0]

private theorem weights :
    (∀ i, 0 < g i) ∧ Function.Injective g ∧ (∀ i, g i ≤ g 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [g.eq_1]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | norm_num [g.eq_1] at hij
  · intro i
    fin_cases i <;> norm_num [g.eq_1]

private theorem A_thermal : A ∈ thermalProcesses g := by
  constructor
  · apply Matrix.mem_colStochastic_iff_sum.mpr
    constructor
    · intro i j
      fin_cases i <;> fin_cases j <;> norm_num [A.eq_1]
    · intro j
      fin_cases j <;> norm_num [A.eq_1, Fin.sum_univ_succ]
  · ext i
    fin_cases i <;>
      norm_num [A.eq_1, g.eq_1, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem B_thermal : B ∈ thermalProcesses g := by
  constructor
  · apply Matrix.mem_colStochastic_iff_sum.mpr
    constructor
    · intro i j
      fin_cases i <;> fin_cases j <;> norm_num [B.eq_1]
    · intro j
      fin_cases j <;> norm_num [B.eq_1, Fin.sum_univ_succ]
  · ext i
    fin_cases i <;>
      norm_num [B.eq_1, g.eq_1, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem C_thermal : C ∈ thermalProcesses g := by
  constructor
  · apply Matrix.mem_colStochastic_iff_sum.mpr
    constructor
    · intro i j
      fin_cases i <;> fin_cases j <;> norm_num [C.eq_1]
    · intro j
      fin_cases j <;> norm_num [C.eq_1, Fin.sum_univ_succ]
  · ext i
    fin_cases i <;>
      norm_num [C.eq_1, g.eq_1, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem extreme_of_support_unique {d : ℕ} {w : Fin d → ℝ}
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : M ∈ thermalProcesses w)
    (hunique : ∀ X ∈ thermalProcesses w,
      (∀ i j, M i j = 0 → X i j = 0) → X = M) :
    M ∈ Set.extremePoints ℝ (thermalProcesses w) := by
  refine ⟨hM, ?_⟩
  intro X hX Y hY hseg
  obtain ⟨a, b, ha, hb, _, heq⟩ := hseg
  apply hunique X hX
  intro i j hij
  have hentry := congrArg (fun N : Matrix (Fin d) (Fin d) ℝ => N i j) heq
  change a * X i j + b * Y i j = M i j at hentry
  rw [hij] at hentry
  have hx : 0 ≤ X i j := Matrix.nonneg_of_mem_colStochastic hX.1
  have hy : 0 ≤ Y i j := Matrix.nonneg_of_mem_colStochastic hY.1
  have hax : a * X i j = 0 :=
    le_antisymm (by linarith [mul_nonneg hb.le hy]) (mul_nonneg ha.le hx)
  exact (mul_eq_zero.mp hax).resolve_left ha.ne'

private theorem A_support_unique (X : Matrix (Fin 5) (Fin 5) ℝ)
    (hX : X ∈ thermalProcesses g) (hz : ∀ i j, A i j = 0 → X i j = 0) : X = A := by
  have z00 : X 0 0 = 0 := hz 0 0 (by norm_num [A.eq_1])
  have z02 : X 0 2 = 0 := hz 0 2 (by norm_num [A.eq_1])
  have z04 : X 0 4 = 0 := hz 0 4 (by norm_num [A.eq_1])
  have z11 : X 1 1 = 0 := hz 1 1 (by norm_num [A.eq_1])
  have z14 : X 1 4 = 0 := hz 1 4 (by norm_num [A.eq_1])
  have z21 : X 2 1 = 0 := hz 2 1 (by norm_num [A.eq_1])
  have z22 : X 2 2 = 0 := hz 2 2 (by norm_num [A.eq_1])
  have z23 : X 2 3 = 0 := hz 2 3 (by norm_num [A.eq_1])
  have z24 : X 2 4 = 0 := hz 2 4 (by norm_num [A.eq_1])
  have z31 : X 3 1 = 0 := hz 3 1 (by norm_num [A.eq_1])
  have z32 : X 3 2 = 0 := hz 3 2 (by norm_num [A.eq_1])
  have z33 : X 3 3 = 0 := hz 3 3 (by norm_num [A.eq_1])
  have z34 : X 3 4 = 0 := hz 3 4 (by norm_num [A.eq_1])
  have z40 : X 4 0 = 0 := hz 4 0 (by norm_num [A.eq_1])
  have z41 : X 4 1 = 0 := hz 4 1 (by norm_num [A.eq_1])
  have z42 : X 4 2 = 0 := hz 4 2 (by norm_num [A.eq_1])
  have z43 : X 4 3 = 0 := hz 4 3 (by norm_num [A.eq_1])
  have hc0 := Matrix.sum_col_of_mem_colStochastic hX.1 (0 : Fin 5)
  have hc1 := Matrix.sum_col_of_mem_colStochastic hX.1 (1 : Fin 5)
  have hc2 := Matrix.sum_col_of_mem_colStochastic hX.1 (2 : Fin 5)
  have hc3 := Matrix.sum_col_of_mem_colStochastic hX.1 (3 : Fin 5)
  have hc4 := Matrix.sum_col_of_mem_colStochastic hX.1 (4 : Fin 5)
  have hr0 := congrFun hX.2 (0 : Fin 5)
  have hr1 := congrFun hX.2 (1 : Fin 5)
  have hr2 := congrFun hX.2 (2 : Fin 5)
  have hr3 := congrFun hX.2 (3 : Fin 5)
  have hr4 := congrFun hX.2 (4 : Fin 5)
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, g.eq_1,
    z00, z02, z04, z11, z14, z21, z22, z23, z24, z31, z32, z33, z34, z40, z41, z42, z43]
    at hc0 hc1 hc2 hc3 hc4 hr0 hr1 hr2 hr3 hr4
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A.eq_1,
      z00, z02, z04, z11, z14, z21, z22, z23, z24, z31, z32, z33, z34, z40, z41, z42, z43] <;>
    linarith only [hc0, hc1, hc2, hc3, hc4, hr0, hr1, hr2, hr3, hr4]

private theorem B_support_unique (X : Matrix (Fin 5) (Fin 5) ℝ)
    (hX : X ∈ thermalProcesses g) (hz : ∀ i j, B i j = 0 → X i j = 0) : X = B := by
  have z01 : X 0 1 = 0 := hz 0 1 (by norm_num [B.eq_1])
  have z02 : X 0 2 = 0 := hz 0 2 (by norm_num [B.eq_1])
  have z03 : X 0 3 = 0 := hz 0 3 (by norm_num [B.eq_1])
  have z04 : X 0 4 = 0 := hz 0 4 (by norm_num [B.eq_1])
  have z10 : X 1 0 = 0 := hz 1 0 (by norm_num [B.eq_1])
  have z14 : X 1 4 = 0 := hz 1 4 (by norm_num [B.eq_1])
  have z20 : X 2 0 = 0 := hz 2 0 (by norm_num [B.eq_1])
  have z22 : X 2 2 = 0 := hz 2 2 (by norm_num [B.eq_1])
  have z23 : X 2 3 = 0 := hz 2 3 (by norm_num [B.eq_1])
  have z30 : X 3 0 = 0 := hz 3 0 (by norm_num [B.eq_1])
  have z32 : X 3 2 = 0 := hz 3 2 (by norm_num [B.eq_1])
  have z33 : X 3 3 = 0 := hz 3 3 (by norm_num [B.eq_1])
  have z34 : X 3 4 = 0 := hz 3 4 (by norm_num [B.eq_1])
  have z40 : X 4 0 = 0 := hz 4 0 (by norm_num [B.eq_1])
  have z42 : X 4 2 = 0 := hz 4 2 (by norm_num [B.eq_1])
  have z43 : X 4 3 = 0 := hz 4 3 (by norm_num [B.eq_1])
  have z44 : X 4 4 = 0 := hz 4 4 (by norm_num [B.eq_1])
  have hc0 := Matrix.sum_col_of_mem_colStochastic hX.1 (0 : Fin 5)
  have hc1 := Matrix.sum_col_of_mem_colStochastic hX.1 (1 : Fin 5)
  have hc2 := Matrix.sum_col_of_mem_colStochastic hX.1 (2 : Fin 5)
  have hc3 := Matrix.sum_col_of_mem_colStochastic hX.1 (3 : Fin 5)
  have hc4 := Matrix.sum_col_of_mem_colStochastic hX.1 (4 : Fin 5)
  have hr0 := congrFun hX.2 (0 : Fin 5)
  have hr1 := congrFun hX.2 (1 : Fin 5)
  have hr2 := congrFun hX.2 (2 : Fin 5)
  have hr3 := congrFun hX.2 (3 : Fin 5)
  have hr4 := congrFun hX.2 (4 : Fin 5)
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, g.eq_1,
    z01, z02, z03, z04, z10, z14, z20, z22, z23, z30, z32, z33, z34, z40, z42, z43, z44]
    at hc0 hc1 hc2 hc3 hc4 hr0 hr1 hr2 hr3 hr4
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [B.eq_1,
      z01, z02, z03, z04, z10, z14, z20, z22, z23, z30, z32, z33, z34, z40, z42, z43, z44] <;>
    linarith only [hc0, hc1, hc2, hc3, hc4, hr0, hr1, hr2, hr3, hr4]

private theorem C_support_unique (X : Matrix (Fin 5) (Fin 5) ℝ)
    (hX : X ∈ thermalProcesses g) (hz : ∀ i j, C i j = 0 → X i j = 0) : X = C := by
  have z00 : X 0 0 = 0 := hz 0 0 (by norm_num [C.eq_1])
  have z04 : X 0 4 = 0 := hz 0 4 (by norm_num [C.eq_1])
  have z12 : X 1 2 = 0 := hz 1 2 (by norm_num [C.eq_1])
  have z13 : X 1 3 = 0 := hz 1 3 (by norm_num [C.eq_1])
  have z21 : X 2 1 = 0 := hz 2 1 (by norm_num [C.eq_1])
  have z22 : X 2 2 = 0 := hz 2 2 (by norm_num [C.eq_1])
  have z23 : X 2 3 = 0 := hz 2 3 (by norm_num [C.eq_1])
  have z24 : X 2 4 = 0 := hz 2 4 (by norm_num [C.eq_1])
  have z31 : X 3 1 = 0 := hz 3 1 (by norm_num [C.eq_1])
  have z32 : X 3 2 = 0 := hz 3 2 (by norm_num [C.eq_1])
  have z33 : X 3 3 = 0 := hz 3 3 (by norm_num [C.eq_1])
  have z34 : X 3 4 = 0 := hz 3 4 (by norm_num [C.eq_1])
  have z40 : X 4 0 = 0 := hz 4 0 (by norm_num [C.eq_1])
  have z42 : X 4 2 = 0 := hz 4 2 (by norm_num [C.eq_1])
  have z43 : X 4 3 = 0 := hz 4 3 (by norm_num [C.eq_1])
  have z44 : X 4 4 = 0 := hz 4 4 (by norm_num [C.eq_1])
  have hc0 := Matrix.sum_col_of_mem_colStochastic hX.1 (0 : Fin 5)
  have hc1 := Matrix.sum_col_of_mem_colStochastic hX.1 (1 : Fin 5)
  have hc2 := Matrix.sum_col_of_mem_colStochastic hX.1 (2 : Fin 5)
  have hc3 := Matrix.sum_col_of_mem_colStochastic hX.1 (3 : Fin 5)
  have hc4 := Matrix.sum_col_of_mem_colStochastic hX.1 (4 : Fin 5)
  have hr0 := congrFun hX.2 (0 : Fin 5)
  have hr1 := congrFun hX.2 (1 : Fin 5)
  have hr2 := congrFun hX.2 (2 : Fin 5)
  have hr3 := congrFun hX.2 (3 : Fin 5)
  have hr4 := congrFun hX.2 (4 : Fin 5)
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, g.eq_1,
    z00, z04, z12, z13, z21, z22, z23, z24, z31, z32, z33, z34, z40, z42, z43, z44]
    at hc0 hc1 hc2 hc3 hc4 hr0 hr1 hr2 hr3 hr4
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [C.eq_1,
      z00, z04, z12, z13, z21, z22, z23, z24, z31, z32, z33, z34, z40, z42, z43, z44] <;>
    linarith only [hc0, hc1, hc2, hc3, hc4, hr0, hr1, hr2, hr3, hr4]

private theorem A_extreme : A ∈ Set.extremePoints ℝ (thermalProcesses g) := by
  exact extreme_of_support_unique A_thermal A_support_unique

private theorem B_extreme : B ∈ Set.extremePoints ℝ (thermalProcesses g) := by
  exact extreme_of_support_unique B_thermal B_support_unique

private theorem C_extreme : C ∈ Set.extremePoints ℝ (thermalProcesses g) := by
  exact extreme_of_support_unique C_thermal C_support_unique

private theorem product : C = A * B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A.eq_1, B.eq_1, C.eq_1, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem fewer_levels : actsOnFewerLevels A ∧ actsOnFewerLevels B := by
  exact ⟨⟨4, by norm_num [A.eq_1]⟩, ⟨0, by norm_num [B.eq_1]⟩⟩

private theorem C_irreducible : irreducible C := by
  rintro ⟨S, hS, hSc, hblock⟩
  have edge (i j : Fin 5) (hij : C i j ≠ 0) : i ∈ S ↔ j ∈ S := by
    constructor
    · intro hi
      by_contra hj
      exact hij (hblock i j (Or.inl ⟨hi, hj⟩))
    · intro hj
      by_contra hi
      exact hij (hblock i j (Or.inr ⟨hi, hj⟩))
  have h01 := edge 0 1 (by norm_num [C.eq_1])
  have h02 := edge 0 2 (by norm_num [C.eq_1])
  have h03 := edge 0 3 (by norm_num [C.eq_1])
  have h14 := edge 1 4 (by norm_num [C.eq_1])
  have hall (i : Fin 5) : i ∈ S ↔ 0 ∈ S := by
    fin_cases i
    · rfl
    · exact h01.symm
    · exact h02.symm
    · exact h03.symm
    · exact (h01.trans h14).symm
  obtain ⟨x, hx⟩ := hS
  obtain ⟨y, hy⟩ := hSc
  exact (Finset.mem_compl.mp hy) ((hall y).mpr ((hall x).mp hx))

private theorem C_selfDual : selfDual g C := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [C.eq_1, g.eq_1]

/-- The thermal-process non-self-duality conjecture fails in dimension five. -/
theorem result : ¬ claim := by
  intro h
  exact h 5 (by decide) g weights.1 weights.2.1 weights.2.2 A B C
    A_extreme B_extreme C_extreme product fewer_levels.1 fewer_levels.2
    C_irreducible C_selfDual

end
end D5.S3.StatisticalMechanics.ThermalProcessSelfDualFactorizationRefutation
