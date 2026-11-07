/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19ZeroLattice/Result
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Module.Basic]
   utility: none
   digest: Integral exceptional19 ZeroLattice Result on original physical labels. -/
/- Source-only candidate: UNCOMPILED, no kernel or acceptance claim.
Owning mathematical provenance and remaining verification are in Result.scribe.cs. -/
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroLattice.Weights
import D5.S3.Combinatorics.Sequenceability.PositiveChargeIncidence
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.LinearAlgebra.Quotient.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroLattice
open scoped BigOperators
open MersenneExceptional19Stabilizer (degree base seed place total)
open MersenneExceptional19PermutationStabilizer (Annihilates eighth_facts)
open D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent (row)
open D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent.PositiveChargeGeometry
  (quotientLabel quotient_zero_iff)

/-- The original integer weighted-sum map, on every original coordinate. -/
def integerWeightedSum (r : ℕ) : (Fin (3*(18*r+12)) → ℤ) →ₗ[ℤ] ℤ where
  toFun z := ∑ i, z i * SourceWidth.actualSource (3*(18*r+12))
    ((2^(18*r+12)-1)*(2^((18*r+12)+1)-3)) i
  map_add' z t := by
    simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib]
  map_smul' k z := by
    simp [Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]

/-- The explicit primitive coordinate generator c0=-3e_(0,0)+2e_(2,0). -/
def coordinateGenerator (r : ℕ) : Fin (3*degree r) → ℤ :=
  (-3 : ℤ) • Pi.single (place 0 ⟨0,by dsimp [degree]; omega⟩) 1 +
    (2 : ℤ) • Pi.single (place 2 ⟨0,by dsimp [degree]; omega⟩) 1

private theorem weighted_sum_row (r : ℕ) (S : Finset (Fin (3*degree r))) :
    integerWeightedSum r (row S)=total r S := by
  classical
  change (∑ i : Fin (3*degree r), row S i *
    SourceWidth.actualSource (3*degree r) (seed r) i)=total r S
  unfold total
  simp only [row,ite_mul,one_mul,zero_mul]
  rw [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]

/-- ALL-r integral relation-lattice theorem for the ORIGINAL exceptional19
physical family. The generating family is ALL finsets with literal integer
actualSource sum zero, including empty/full sets when zero. No rank, span,
unit, saturation, finite-r or certificate premise occurs in this telescope. -/
theorem actual_integer_zero_span_eq_kernel (r : ℕ) :
    Submodule.span ℤ
      (row '' {S : Finset (Fin (3*(18*r+12))) |
        (∑ i ∈ S, SourceWidth.actualSource (3*(18*r+12))
          ((2^(18*r+12)-1)*(2^((18*r+12)+1)-3)) i)=0}) =
      LinearMap.ker (integerWeightedSum r) := by
  classical
  let L : Submodule ℤ (Fin (3*degree r) → ℤ) :=
    Submodule.span ℤ (row '' {S : Finset (Fin (3*degree r)) | total r S=0})
  change L=LinearMap.ker (integerWeightedSum r)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨S,hS,rfl⟩
    change integerWeightedSum r (row S)=0
    rw [weighted_sum_row]
    exact hS
  · intro z hz
    change integerWeightedSum r z=0 at hz
    let X : Fin (3*degree r) → (Fin (3*degree r) → ℤ) ⧸ L := quotientLabel L
    have hX : Annihilates r X := by
      intro S hS
      apply (quotient_zero_iff (M := L) S).mpr
      exact Submodule.subset_span ⟨S,hS,rfl⟩
    let c : (Fin (3*degree r) → ℤ) ⧸ L := L.mkQ (coordinateGenerator r)
    have hcoord (i : Fin (3*degree r)) : X i=primitive r i • c := by
      have hi := integral_reconstruction r X hX i
      simpa only [c,coordinateGenerator,map_add,map_smul,X,quotientLabel] using hi
    have qz : L.mkQ z=(∑ i, z i*primitive r i) • c := by
      calc
        L.mkQ z=L.mkQ (∑ i, z i • Pi.single i (1 : ℤ)) := by
          rw [← pi_eq_sum_univ' z]
        _=∑ i, z i • X i := by
          simp only [map_sum,map_smul,X,quotientLabel]
        _=∑ i, (z i*primitive r i) • c := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hcoord,smul_smul]
        _=(∑ i, z i*primitive r i) • c := by rw [Finset.sum_smul]
    have factor_ne : 19*((base r : ℤ)-1)≠0 := by
      obtain ⟨hB,he,hemod⟩ := eighth_facts r
      omega
    have scale : integerWeightedSum r z=
        (19*((base r : ℤ)-1))*(∑ i, z i*primitive r i) := by
      change (∑ i, z i*SourceWidth.actualSource (3*degree r) (seed r) i)=_
      simp_rw [source_eq_scale_primitive]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hzprim : (∑ i, z i*primitive r i)=0 := by
      rw [scale] at hz
      exact (mul_eq_zero.mp hz).resolve_left factor_ne
    have qzero : L.mkQ z=0 := by rw [qz,hzprim,zero_smul]
    exact (Submodule.Quotient.mk_eq_zero L).mp qzero

end D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroLattice
