/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/TriangleGram
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rank-one decomposition of the coefficient Gram for a weighted triangle edge. -/

import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ThreeBlockGram
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! The weighted edge energy gives a positive coefficient block by completing squares. -/

namespace RefinedBMV.ThreeBlockGram

open Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

/-- A coefficient allocation of the form `G (u,v)` fits inside the edge
Gram when its quadratic energy fits the backtracking coefficient. -/
theorem gramBlock_posSemidef_of_energy (d : Kernel) (alloc : Fin 3 → Fin 3 → ℝ)
    (i j k : Fin 3) (u v : ℝ)
    (ha : 0 < f d i j) (hdet : (g d i j / 2) ^ 2 ≤ f d i j * f d j i)
    (hi : alloc i j = f d i j * u + (g d i j / 2) * v)
    (hj : alloc j i = (g d i j / 2) * u + f d j i * v)
    (henergy : f d i j * u ^ 2 + 2 * (g d i j / 2) * u * v + f d j i * v ^ 2 ≤ h d k i j) :
    (gramBlock d alloc i j k).PosSemidef := by
  let a := f d i j
  let b := f d j i
  let c := g d i j / 2
  let r := h d k i j - (a * u ^ 2 + 2 * c * u * v + b * v ^ 2)
  let e : Fin 3 → ℂ := ![1, (c / a : ℝ), (u + c / a * v : ℝ)]
  let p : Fin 3 → ℂ := ![0, 1, (v : ℂ)]
  let q : Fin 3 → ℂ := ![0, 0, 1]
  have hr : 0 ≤ r := sub_nonneg.mpr henergy
  have hb : 0 ≤ b - c ^ 2 / a := by
    apply sub_nonneg.mpr
    have hab : c ^ 2 ≤ a * b := hdet
    exact (div_le_iff₀ (show 0 < a from ha)).mpr (mul_comm a b ▸ hab)
  have hp := ((posSemidef_vecMulVec_self_star e).smul ha.le).add
    (((posSemidef_vecMulVec_self_star p).smul hb).add
      ((posSemidef_vecMulVec_self_star q).smul hr))
  refine (show gramBlock d alloc i j k = _ from ?_) ▸ hp
  ext x y
  change gramBlock d alloc i j k x y =
    a • (e x * star (e y)) + ((b - c ^ 2 / a) • (p x * star (p y)) + r • (q x * star (q y)))
  fin_cases x <;> fin_cases y <;>
    simp [gramBlock, hi, hj, e, p, q, r, a, b, c, Complex.real_smul] <;>
    field_simp [(Complex.ofReal_ne_zero.mpr ha.ne')] <;> ring

/-- The three triangle demands, one for each repeated vertex. -/
def triangleDemand (d : Kernel) : Fin 3 → ℝ := ![h d 0 1 2, h d 1 0 2, h d 2 0 1]

private def triangleScale (d : Kernel) (w : Fin 3 → ℝ) (k : Fin 3) : ℝ :=
  w k * triangleDemand d k

/-- The sum of the three binary Gram matrices, each embedded in the two
coordinates opposite its weight index and scaled by the backtracking coefficient. -/
def triangleMatrix (d : Kernel) (w : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let s := triangleScale d w
  !![s 2 * f d 0 1 + s 1 * f d 0 2, s 2 * (g d 0 1 / 2), s 1 * (g d 0 2 / 2);
    s 2 * (g d 0 1 / 2), s 2 * f d 1 0 + s 0 * f d 1 2, s 0 * (g d 1 2 / 2);
    s 1 * (g d 0 2 / 2), s 0 * (g d 1 2 / 2), s 1 * f d 2 0 + s 0 * f d 2 1]

private def triangleEntry (d : Kernel) (w z : Fin 3 → ℝ) (i j k : Fin 3) : ℝ :=
  let s := triangleScale d w k
  f d i j * (s * z i) + (g d i j / 2) * (s * z j)

/-- Split each vertex demand between its two incident weighted Gram matrices. -/
def weightedTriangleAllocation (d : Kernel) (w z : Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  let l := triangleEntry d w z
  !![0, l 0 1 2, l 0 2 1; l 1 0 2, 0, l 1 2 0; l 2 0 1, l 2 1 0, 0]

/-- The quadratic form of one binary Gram matrix at its weighted coordinates. -/
def triangleEdgeEnergy (d : Kernel) (w z : Fin 3 → ℝ) (i j k : Fin 3) : ℝ :=
  let u := triangleScale d w k * z i
  let v := triangleScale d w k * z j
  f d i j * u ^ 2 + 2 * (g d i j / 2) * u * v + f d j i * v ^ 2

/-- The weighted linear system supplies all three demand identities. Its
three scalar energy bounds furnish the corresponding positive Gram blocks. -/
theorem allocation_of_triangleMatrix_mulVec (d : Kernel) (w z : Fin 3 → ℝ)
    (hs : triangleMatrix d w *ᵥ z = triangleDemand d)
    (hg : ∀ i j, g d i j = g d j i)
    (hf : ∀ i j, i ≠ j → 0 < f d i j)
    (hdet : ∀ i j, i ≠ j → (g d i j / 2) ^ 2 ≤ f d i j * f d j i)
    (h01 : triangleEdgeEnergy d w z 0 1 2 ≤ h d 2 0 1)
    (h02 : triangleEdgeEnergy d w z 0 2 1 ≤ h d 1 0 2)
    (h12 : triangleEdgeEnergy d w z 1 2 0 ≤ h d 0 1 2) :
    Allocation d (weightedTriangleAllocation d w z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hs0 := congrFun hs 0
    simp [triangleMatrix, triangleDemand, mulVec, dotProduct, Fin.sum_univ_three] at hs0
    simp [weightedTriangleAllocation, triangleEntry]
    linear_combination hs0
  · have hs1 := congrFun hs 1
    simp [triangleMatrix, triangleDemand, mulVec, dotProduct, Fin.sum_univ_three] at hs1
    simp [weightedTriangleAllocation, triangleEntry, ← hg 0 1]
    linear_combination hs1
  · have hs2 := congrFun hs 2
    simp [triangleMatrix, triangleDemand, mulVec, dotProduct, Fin.sum_univ_three] at hs2
    simp [weightedTriangleAllocation, triangleEntry, ← hg 0 2, ← hg 1 2]
    linear_combination hs2
  · apply gramBlock_posSemidef_of_energy d _ 0 1 2
      (triangleScale d w 2 * z 0) (triangleScale d w 2 * z 1)
      (hf 0 1 (by decide)) (hdet 0 1 (by decide)) rfl _ h01
    simp [weightedTriangleAllocation, triangleEntry, ← hg 0 1, add_comm]
  · apply gramBlock_posSemidef_of_energy d _ 0 2 1
      (triangleScale d w 1 * z 0) (triangleScale d w 1 * z 2)
      (hf 0 2 (by decide)) (hdet 0 2 (by decide)) rfl _ h02
    simp [weightedTriangleAllocation, triangleEntry, ← hg 0 2, add_comm]
  · apply gramBlock_posSemidef_of_energy d _ 1 2 0
      (triangleScale d w 0 * z 1) (triangleScale d w 0 * z 2)
      (hf 1 2 (by decide)) (hdet 1 2 (by decide)) rfl _ h12
    simp [weightedTriangleAllocation, triangleEntry, ← hg 1 2, add_comm]

/-- Cramer's rule for the weighted triangle system. -/
def triangleSolution (d : Kernel) (w : Fin 3 → ℝ) : Fin 3 → ℝ :=
  let M := triangleMatrix d w
  M.det⁻¹ • (M.adjugate *ᵥ triangleDemand d)

theorem triangleMatrix_mulVec_solution (d : Kernel) (w : Fin 3 → ℝ)
    (hdet : (triangleMatrix d w).det ≠ 0) :
    triangleMatrix d w *ᵥ triangleSolution d w = triangleDemand d := by
  unfold triangleSolution
  rw [mulVec_smul, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec,
    smul_smul, inv_mul_cancel₀ hdet, one_smul]

end

end RefinedBMV.ThreeBlockGram
