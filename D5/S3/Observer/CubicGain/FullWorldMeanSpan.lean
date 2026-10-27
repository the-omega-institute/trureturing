/- GID: D5/S3/Observer/CubicGain/FullWorldMeanSpan
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/FullWorldMeanSpan
   mirror-E: none(waiver:unrestricted-world-affine-span)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic, mathlib/module/Mathlib.LinearAlgebra.Matrix.NonsingularInverse]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Observer/CubicGain/FullWorldMeanSpan.full_world_mean_span; premises=D5/S3/Observer/CubicGain/FullWorldMeanSpan.source_certificate
   digest: The unrestricted original common-matrix polynomial mean family affinely spans all seventeen coordinates. -/

import D5.S3.Observer.CubicGain.OriginalWorld
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace D5.S3.Observer.CubicGain.FullWorldMeanSpan
open D5.S3.Observer.CubicGain

/-- The complete original domain, with no history or sample restriction. -/
def FullWorld (W : OriginalWorld) : Prop :=
  0 < W.1 ∧ W.1 < 1 ∧ 0 < W.2.1 ∧ originalPolynomial W ≠ 0

/-- Column vectorization: (11,21,12,22), with indices starting at zero in Lean. -/
def sourceVector (r b : ℝ) : Fin 4 → ℝ :=
  ![sourceMatrix r b 0 0, sourceMatrix r b 1 0,
    sourceMatrix r b 0 1, sourceMatrix r b 1 1]

/-- Drift followed by the four ascending ordinary-coefficient blocks. -/
def meanCoordinates (d : ℝ) (a v : Fin 4 → ℝ) : Fin 17 → ℝ :=
  ![d, a 0*v 0, a 0*v 1, a 0*v 2, a 0*v 3,
    a 1*v 0, a 1*v 1, a 1*v 2, a 1*v 3,
    a 2*v 0, a 2*v 1, a 2*v 2, a 2*v 3,
    a 3*v 0, a 3*v 1, a 3*v 2, a 3*v 3]

/-- Each world's four blocks use its one and the same program matrix. -/
def fullWorldMean (W : OriginalWorld) : Fin 17 → ℝ :=
  meanCoordinates W.2.2.1 W.2.2.2 (sourceVector W.1 W.2.1)

def fullMeanFamily : Set (Fin 17 → ℝ) :=
  fullWorldMean '' {W | FullWorld W}

/-- The four source programs in the native (r,b) coordinates. -/
def sourceR : Fin 4 → ℝ := ![1/4,1/4,1/4,1/3]
def sourceB : Fin 4 → ℝ := ![1/8,1/6,1/4,1/8]

def programColumns : Matrix (Fin 4) (Fin 4) ℝ :=
  fun j i => sourceVector (sourceR i) (sourceB i) j

/-- Exact arithmetic premises for the unrestricted-family construction. -/
theorem source_certificate :
    (∀ i : Fin 4, 0 < sourceR i ∧ sourceR i < 1 ∧
      0 < sourceB i) ∧
    programColumns.det = 1/768 := by
  constructor
  · intro i
    fin_cases i <;> norm_num [sourceR,sourceB]
  · norm_num [programColumns,sourceVector,sourceMatrix,sourceR,sourceB,
      Matrix.det_succ_row_zero,Fin.sum_univ_succ,Matrix.det_unique,
      Matrix.submatrix_apply,Fin.succAbove]

private def monomialWorld (i k : Fin 4) (q d : ℝ) : OriginalWorld :=
  (sourceR i,sourceB i,d,Pi.single k q)

private theorem monomial_legal (i k : Fin 4) (q d : ℝ) (hq : q ≠ 0) :
    FullWorld (monomialWorld i k q d) := by
  obtain ⟨hr,hr1,hb⟩ := source_certificate.1 i
  have hn : Polynomial.ofFn 4 (Pi.single k q : Gain) ≠ 0 := by
    intro hz
    have he := congrArg (fun p : Polynomial ℝ => p.coeff k.val) hz
    simp [Polynomial.ofFn_coeff_eq_val_of_lt _ k.isLt] at he
    exact hq he
  exact ⟨hr,hr1,hb,hn⟩

private def blockMap (k : Fin 4) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 17 → ℝ) where
  toFun v := meanCoordinates 0 (Pi.single k 1) v
  map_add' v w := by
    ext j
    fin_cases j <;> simp [meanCoordinates] <;> ring
  map_smul' q v := by
    ext j
    fin_cases j <;> simp [meanCoordinates] <;> ring

private theorem monomial_mean (i k : Fin 4) (q : ℝ) :
    fullWorldMean (monomialWorld i k q 0) =
      q • blockMap k (sourceVector (sourceR i) (sourceB i)) := by
  ext j
  fin_cases j <;>
    simp [fullWorldMean,monomialWorld,blockMap,meanCoordinates,Pi.single_apply] <;>
    split_ifs <;> ring

private def driftVector (d : ℝ) : Fin 17 → ℝ :=
  ![d,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

private theorem drift_difference (d : ℝ) :
    fullWorldMean (monomialWorld 0 0 1 d) -
      fullWorldMean (monomialWorld 0 0 1 0) = driftVector d := by
  ext j
  fin_cases j <;> simp [fullWorldMean,monomialWorld,meanCoordinates,driftVector]

private theorem block_directions (k : Fin 4) (v : Fin 4 → ℝ) :
    blockMap k v ∈ (affineSpan ℝ fullMeanFamily).direction := by
  let A := affineSpan ℝ fullMeanFamily
  have hm (i : Fin 4) (q : ℝ) (hq : q ≠ 0) :
      fullWorldMean (monomialWorld i k q 0) ∈ A :=
    subset_affineSpan ℝ fullMeanFamily ⟨_,monomial_legal i k q 0 hq,rfl⟩
  have habs : blockMap k (sourceVector (sourceR 0) (sourceB 0)) ∈ A.direction := by
    have h := A.vsub_mem_direction (hm 0 2 (by norm_num)) (hm 0 1 one_ne_zero)
    rw [monomial_mean,monomial_mean] at h
    simpa [vsub_eq_sub,two_smul] using h
  have hcol (i : Fin 4) :
      blockMap k (sourceVector (sourceR i) (sourceB i)) ∈ A.direction := by
    have h := A.vsub_mem_direction (hm i 1 one_ne_zero) (hm 0 1 one_ne_zero)
    rw [monomial_mean,monomial_mean] at h
    simp only [one_smul,vsub_eq_sub] at h
    simpa using A.direction.add_mem h habs
  have hu : IsUnit programColumns.det := by
    rw [source_certificate.2]
    norm_num
  obtain ⟨w,hw⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr hu)) v
  have hv : v = ∑ i : Fin 4, w i • sourceVector (sourceR i) (sourceB i) := by
    rw [← hw]
    ext j
    simp [Matrix.mulVec,dotProduct,programColumns,mul_comm]
  rw [hv,map_sum]
  apply A.direction.sum_mem
  intro i _
  simpa only [map_smul] using A.direction.smul_mem (w i) (hcol i)

/-- The full native world family has affine span all of literal R^17. -/
theorem full_world_mean_span :
    affineSpan ℝ (fullWorldMean '' {W : OriginalWorld | FullWorld W}) = ⊤ := by
  let A := affineSpan ℝ fullMeanFamily
  have hm (d : ℝ) : fullWorldMean (monomialWorld 0 0 1 d) ∈ A :=
    subset_affineSpan ℝ fullMeanFamily ⟨_,monomial_legal 0 0 1 d one_ne_zero,rfl⟩
  apply (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨_,hm 0⟩).mp
  apply top_unique
  intro x _
  have hd : driftVector (x 0) ∈ A.direction := by
    rw [← drift_difference]
    exact A.vsub_mem_direction (hm (x 0)) (hm 0)
  let b : Fin 4 → Fin 4 → ℝ := fun k j => x ⟨1+4*k.val+j.val,by omega⟩
  have hx : x = driftVector (x 0) + ∑ k : Fin 4, blockMap k (b k) := by
    ext j
    fin_cases j <;>
      norm_num [driftVector,Fin.sum_univ_four,blockMap,meanCoordinates,b,Pi.single_apply]
  rw [hx]
  apply A.direction.add_mem hd
  exact A.direction.sum_mem (fun k _ => block_directions k (b k))

#print axioms full_world_mean_span
end D5.S3.Observer.CubicGain.FullWorldMeanSpan
