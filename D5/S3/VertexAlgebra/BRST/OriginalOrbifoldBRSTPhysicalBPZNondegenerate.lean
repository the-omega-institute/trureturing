/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTPhysicalBPZNondegenerate
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTPhysicalBPZNondegenerate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Lagrange]
   utility: none
   digest: The native ghost-number-one physical Lie algebra has nondegenerate BPZ form. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTBPZGhostNumber
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTCohomologyBPZNondegenerate
import Mathlib.LinearAlgebra.Lagrange

/-! Finite ghost support in the native state basis gives a decomposition of each
relative cycle by polynomial interpolation on ghost number. The resulting grades
span cohomology, so BPZ selection extends either degree-one annihilator to an
annihilator of the full relative cohomology. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTPhysicalBPZNondegenerate

open D5.S3.Quantum.Fermionic.BcGhostCharge (charge)
open OriginalOrbifoldCriticalMatter (Matter State)
open OriginalOrbifoldBRSTZeroEnergy (FullLabel fullBasis)
open OriginalOrbifoldBRSTDescent (relativeStates relativeCycles relativeBoundaries
  RelativeCohomology)
open OriginalOrbifoldBRSTPhysicalLie (cycleNumber cohomologyNumber cohomologyNumber_mk grade)
open OriginalOrbifoldBRSTPhysicalPairing (cohomologyBPZ physicalBPZ)
open OriginalOrbifoldBRSTBPZGhostNumber (cohomologyBPZ_eq_zero_of_ghost_number)
open OriginalOrbifoldBRSTCohomologyBPZNondegenerate (cohomologyBPZ_nondegenerate)

open private number_coordinate from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalLie

noncomputable section

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private def cycleCoordinate (i : FullLabel) : relativeCycles →ₗ[ℂ] ℂ :=
  ((Finsupp.lapply i).comp fullBasis.repr.toLinearMap).comp
    (relativeStates.subtype.comp relativeCycles.subtype)

private theorem cycleCoordinate_ext {x y : relativeCycles}
    (h : ∀ i, cycleCoordinate i x = cycleCoordinate i y) : x = y :=
  Subtype.ext (Subtype.ext (fullBasis.repr.injective (Finsupp.ext h)))

private theorem cycleCoordinate_number (i : FullLabel) (z : relativeCycles) :
    cycleCoordinate i (cycleNumber z) = (charge i.2.2 : ℂ) * cycleCoordinate i z :=
  number_coordinate (z.1 : State) i

private theorem cycleCoordinate_aeval (i : FullLabel) (p : Polynomial ℂ) (z : relativeCycles) :
    cycleCoordinate i (Polynomial.aeval cycleNumber p z) =
      p.eval (charge i.2.2 : ℂ) * cycleCoordinate i z := by
  induction p using Polynomial.induction_on generalizing z with
  | C a =>
    simp [Polynomial.aeval_C, Module.algebraMap_end_apply, smul_eq_mul]
  | add p q hp hq =>
    simp [hp, hq, add_mul]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, Module.End.mul_apply, Polynomial.aeval_X,
      ih (cycleNumber z), cycleCoordinate_number i z]
    simp only [Polynomial.eval_mul, Polynomial.eval_X, mul_assoc]

private def ghostSupport (z : relativeCycles) : Finset ℤ :=
  (fullBasis.repr (z.1 : State)).support.image fun i => charge i.2.2

private theorem cycleCoordinate_eq_zero_of_notMem (z : relativeCycles) (i : FullLabel)
    (hi : charge i.2.2 ∉ ghostSupport z) : cycleCoordinate i z = 0 :=
  Finsupp.notMem_support_iff.mp fun h => hi (Finset.mem_image.mpr ⟨i, h, rfl⟩)

private def cyclePart (n : ℤ) (z : relativeCycles) : relativeCycles :=
  Polynomial.aeval cycleNumber (Lagrange.basis (ghostSupport z) (fun k : ℤ => (k : ℂ)) n) z

private theorem cyclePart_number (n : ℤ) (z : relativeCycles) :
    cycleNumber (cyclePart n z) = (n : ℂ) • cyclePart n z := by
  apply cycleCoordinate_ext
  intro i
  rw [cycleCoordinate_number, map_smul, smul_eq_mul]
  by_cases hin : n = charge i.2.2
  · rw [hin]
  · have hz : cycleCoordinate i (cyclePart n z) = 0 := by
      rw [cyclePart, cycleCoordinate_aeval]
      by_cases hi : charge i.2.2 ∈ ghostSupport z
      · rw [Lagrange.eval_basis_of_ne hin hi, zero_mul]
      · rw [cycleCoordinate_eq_zero_of_notMem z i hi, mul_zero]
    simp only [hz, mul_zero]

private theorem sum_cyclePart (z : relativeCycles) :
    ∑ n ∈ ghostSupport z, cyclePart n z = z := by
  by_cases hs : (ghostSupport z).Nonempty
  · have hinj : Set.InjOn (fun k : ℤ => (k : ℂ)) (ghostSupport z : Set ℤ) :=
      (Int.cast_injective (α := ℂ)).injOn
    have h := congrArg (fun p : Polynomial ℂ => Polynomial.aeval cycleNumber p z)
      (Lagrange.sum_basis hinj hs)
    simpa only [cyclePart, map_sum, LinearMap.sum_apply, map_one, Module.End.one_apply] using h
  · apply cycleCoordinate_ext
    intro i
    rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.sum_empty, map_zero]
    exact (cycleCoordinate_eq_zero_of_notMem z i (fun hi => hs ⟨_, hi⟩)).symm

private theorem iSup_grade_eq_top : (⨆ n : ℤ, grade n) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨z, rfl⟩ := relativeBoundaries.mkQ_surjective x
  let cl : relativeCycles →ₗ[ℂ] RelativeCohomology := relativeBoundaries.mkQ
  have hsum : (∑ n ∈ ghostSupport z, cl (cyclePart n z)) = cl z :=
    (map_sum cl (fun n => cyclePart n z) (ghostSupport z)).symm.trans
      (congrArg cl (sum_cyclePart z))
  change cl z ∈ ⨆ n : ℤ, grade n
  rw [← hsum]
  refine Submodule.sum_mem _ (fun n _ => le_iSup grade n ?_)
  change cl (cyclePart n z) ∈ cohomologyNumber.eigenspace (n : ℂ)
  refine Module.End.mem_eigenspace_iff.mpr ?_
  calc
    cohomologyNumber (cl (cyclePart n z)) = cl (cycleNumber (cyclePart n z)) :=
      cohomologyNumber_mk (cyclePart n z)
    _ = cl ((n : ℂ) • cyclePart n z) := congrArg cl (cyclePart_number n z)
    _ = (n : ℂ) • cl (cyclePart n z) := cl.map_smul _ _

private theorem eq_zero_of_grade_eq_zero (f : RelativeCohomology →ₗ[ℂ] ℂ)
    (h : ∀ (n : ℤ) (x : RelativeCohomology), x ∈ grade n → f x = 0)
    (x : RelativeCohomology) : f x = 0 := by
  have hle : (⨆ n : ℤ, grade n) ≤ LinearMap.ker f :=
    iSup_le fun n y hy => LinearMap.mem_ker.mpr (h n y hy)
  rw [iSup_grade_eq_top] at hle
  exact LinearMap.mem_ker.mp (hle (Submodule.mem_top (x := x)))

/-- Both radicals of BPZ vanish on the actual ghost-number-one physical BRST Lie algebra. -/
theorem physicalBPZ_nondegenerate : physicalBPZ.Nondegenerate := by
  constructor
  · intro x hx
    apply Subtype.ext
    apply cohomologyBPZ_nondegenerate.1
    apply eq_zero_of_grade_eq_zero (cohomologyBPZ (x : RelativeCohomology))
    intro n y hy
    by_cases hn : n = 1
    · subst n
      exact hx ⟨y, hy⟩
    · exact cohomologyBPZ_eq_zero_of_ghost_number (by omega) x.property hy
  · intro x hx
    apply Subtype.ext
    apply cohomologyBPZ_nondegenerate.2
    apply eq_zero_of_grade_eq_zero (cohomologyBPZ.flip (x : RelativeCohomology))
    intro n y hy
    by_cases hn : n = 1
    · subst n
      exact hx ⟨y, hy⟩
    · exact cohomologyBPZ_eq_zero_of_ghost_number (by omega) hy x.property

#print axioms physicalBPZ_nondegenerate

end

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTPhysicalBPZNondegenerate
