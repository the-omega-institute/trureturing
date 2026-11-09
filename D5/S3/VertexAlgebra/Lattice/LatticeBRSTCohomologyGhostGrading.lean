/- GID: D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading
   mirror-E: none(waiver:algebraic-original-brst-integer-grading)
   anchors: []
   utility: none
   digest: Full critical BRST integer eigenspace decomposition and homogeneous cycle lifts. -/

/- The actual State, Q, cycles, boundaries and Cohomology are retained without
momentum, energy, relative-kernel, positivity or finite-dimensional restrictions.
The all-state number diagonality and commutator are reused from their original
suppliers. Their lattice, ghost and Mathlib attributions are retained. No
literature novelty or physical reconstruction claim is made. -/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTZeroEnergyReduction
import D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTCohomology
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.DirectSum.Module
import Batteries.Tactic.OpenPrivate

/-! Integer spectral decomposition on the actual full kernel/image quotient. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

open scoped BigOperators TensorProduct Classical

namespace D5.S3.VertexAlgebra.LatticeBRSTCohomologyGhostGrading

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeMatterGhostCoupling (State)
open LatticeBRSTCohomologyField (cycles boundaries Cohomology classOf)
open LatticeBRSTZeroEnergyReduction (FullLabel fullBasis)
open LatticeMatterGhostDegree (tensorNumber)
open D5.S3.Quantum.Fermionic.BcGhostCharge (charge)
open private N_original_basis N_original_coefficient from
  D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTCohomology

noncomputable section

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

private theorem number_basis (i : FullLabel D) :
    tensorNumber D (fullBasis D i) = (charge i.2 : ℂ) • fullBasis D i := by
  exact N_original_basis (D := D) i

private theorem number_coefficient (x : State D) (i : FullLabel D) :
    (fullBasis D).repr (tensorNumber D x) i =
      (charge i.2 : ℂ) * (fullBasis D).repr x i := by
  exact N_original_coefficient (D := D) x i

private theorem number_charge (x : State D) :
    tensorNumber D (LatticeBRST.totalCharge D H x) -
      LatticeBRST.totalCharge D H (tensorNumber D x) =
        LatticeBRST.totalCharge D H x := by
  exact LinearMap.congr_fun (LatticeMatterGhostDegree.tensorNumber_Q D H) x

/-- The finite full-state component of an arbitrary integer ghost number. -/
def project (g : ℤ) : Module.End ℂ (State D) :=
  (fullBasis D).constr ℂ (fun i => if charge i.2 = g then fullBasis D i else 0)

private theorem project_basis (g : ℤ) (i : FullLabel D) :
    project D g (fullBasis D i) = if charge i.2 = g then fullBasis D i else 0 := by
  simp [project]

private theorem project_coefficient (g : ℤ) (x : State D) (i : FullLabel D) :
    (fullBasis D).repr (project D g x) i =
      if charge i.2 = g then (fullBasis D).repr x i else 0 := by
  let f : State D →ₗ[ℂ] ℂ := (Finsupp.lapply i).comp (fullBasis D).repr.toLinearMap
  have he : f.comp (project D g) = (if charge i.2 = g then (1 : ℂ) else 0) • f := by
    apply (fullBasis D).ext
    intro j
    by_cases hj : charge j.2 = g <;> by_cases hi : charge i.2 = g <;>
      by_cases hji : j = i <;>
      simp_all [f, project_basis, Module.Basis.repr_self]
  have hx := LinearMap.congr_fun he x
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul,
    ite_mul, one_mul, zero_mul, f, Finsupp.lapply_apply, LinearEquiv.coe_coe] using hx

private theorem project_number (g : ℤ) (x : State D) :
    tensorNumber D (project D g x) = (g : ℂ) • project D g x := by
  apply (fullBasis D).repr.injective
  ext i
  simp only [number_coefficient, project_coefficient, map_smul,
    Finsupp.smul_apply, smul_eq_mul]
  split_ifs with h
  · rw [h]
  · simp

private theorem charge_coefficient_degree (i j : FullLabel D)
    (hm : (fullBasis D).repr (LatticeBRST.totalCharge D H (fullBasis D i)) j ≠ 0) :
    charge j.2 = charge i.2 + 1 := by
  have h := congrArg (fun x : State D => (fullBasis D).repr x j)
    (number_charge D H (fullBasis D i))
  simp only [map_sub, Finsupp.sub_apply, number_coefficient, number_basis,
    map_smul, Finsupp.smul_apply, smul_eq_mul] at h
  have hz : ((charge j.2 : ℂ) - (charge i.2 : ℂ) - 1) *
      (fullBasis D).repr (LatticeBRST.totalCharge D H (fullBasis D i)) j = 0 := by
    linear_combination h
  have hc := (mul_eq_zero.mp hz).resolve_right hm
  have he : (charge j.2 : ℂ) = ((charge i.2 + 1 : ℤ) : ℂ) := by
    push_cast
    linear_combination hc
  exact_mod_cast he

private theorem project_charge (g : ℤ) (x : State D) :
    project D g (LatticeBRST.totalCharge D H x) =
      LatticeBRST.totalCharge D H (project D (g - 1) x) := by
  suffices he : (project D g).comp (LatticeBRST.totalCharge D H) =
      (LatticeBRST.totalCharge D H).comp (project D (g - 1)) by
    exact LinearMap.congr_fun he x
  apply (fullBasis D).ext
  intro i
  apply (fullBasis D).repr.injective
  ext j
  simp only [LinearMap.comp_apply, project_coefficient, project_basis]
  by_cases hm : (fullBasis D).repr (LatticeBRST.totalCharge D H (fullBasis D i)) j = 0
  · split_ifs <;> simp [hm]
  · have hd := charge_coefficient_degree D H i j hm
    have he : charge j.2 = g ↔ charge i.2 = g - 1 := by omega
    simp only [he]
    split_ifs <;> simp

/-- Exactly the ghost numbers in the finite support of this original state. -/
def stateDegrees (x : State D) : Finset ℤ :=
  (fullBasis D).repr x |>.support.image (fun i => charge i.2)

private theorem sum_project (x : State D) :
    ∑ g ∈ stateDegrees D x, project D g x = x := by
  apply (fullBasis D).repr.injective
  ext i
  let f : State D →ₗ[ℂ] ℂ := (Finsupp.lapply i).comp (fullBasis D).repr.toLinearMap
  change f (∑ g ∈ stateDegrees D x, project D g x) = _
  rw [map_sum]
  change (∑ g ∈ stateDegrees D x, (fullBasis D).repr (project D g x) i) = _
  simp_rw [project_coefficient]
  by_cases hi : i ∈ ((fullBasis D).repr x).support
  · have hg : charge i.2 ∈ stateDegrees D x := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    simp [hg]
  · simp [Finsupp.notMem_support_iff.mp hi]

private theorem number_cycle (z : cycles D H) :
    LatticeBRST.totalCharge D H (tensorNumber D z) = 0 := by
  have h := number_charge D H z
  rw [show LatticeBRST.totalCharge D H z = 0 from z.property, map_zero] at h
  simpa only [zero_sub, neg_eq_zero] using h

/-- Restriction of the original number operator to the actual full Q-kernel. -/
def cycleNumber : Module.End ℂ (cycles D H) :=
  (tensorNumber D).restrict (by intro z hz; exact number_cycle D H ⟨z, hz⟩)

private theorem project_cycle (g : ℤ) (z : cycles D H) :
    LatticeBRST.totalCharge D H (project D g z) = 0 := by
  have h := project_charge D H (g + 1) z
  rw [show g + 1 - 1 = g by omega,
    show LatticeBRST.totalCharge D H z = 0 from z.property, map_zero] at h
  exact h.symm

/-- Full-state projection restricted to actual cycles. -/
def cycleProject (g : ℤ) : Module.End ℂ (cycles D H) :=
  (project D g).restrict (by intro z hz; exact project_cycle D H g ⟨z, hz⟩)

variable (h26 : D.rank = 26)
  (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
  (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)

private theorem number_boundary (z : cycles D H)
    (hz : z ∈ boundaries D H h26 hHG hGH) :
    cycleNumber D H z ∈ boundaries D H h26 hHG hGH := by
  obtain ⟨x, hx⟩ := (LatticeBRSTCohomologyField.mem_boundaries D H h26 hHG hGH z).mp hz
  apply (LatticeBRSTCohomologyField.mem_boundaries D H h26 hHG hGH _).mpr
  refine ⟨tensorNumber D x + x, ?_⟩
  change LatticeBRST.totalCharge D H (tensorNumber D x + x) = tensorNumber D z
  rw [map_add, ← hx]
  simpa only [add_comm] using (sub_eq_iff_eq_add.mp (number_charge D H x)).symm

/-- The number operator on the existing full critical BRST quotient. -/
def number : Module.End ℂ (Cohomology D H h26 hHG hGH) :=
  (boundaries D H h26 hHG hGH).mapQ (boundaries D H h26 hHG hGH)
    (cycleNumber D H) (number_boundary D H h26 hHG hGH)

private theorem number_classOf (z : cycles D H) :
    number D H h26 hHG hGH (classOf D H h26 hHG hGH z) =
      classOf D H h26 hHG hGH (cycleNumber D H z) := rfl

/-- Integer eigenspaces of the actual quotient number operator. -/
def grade (g : ℤ) : Submodule ℂ (Cohomology D H h26 hHG hGH) :=
  Module.End.eigenspace (number D H h26 hHG hGH) (g : ℂ)

private theorem component_mem_grade (g : ℤ) (z : cycles D H) :
    classOf D H h26 hHG hGH (cycleProject D H g z) ∈
      grade D H h26 hHG hGH g := by
  rw [grade, Module.End.mem_eigenspace_iff, number_classOf, ← map_smul]
  apply congrArg (classOf D H h26 hHG hGH)
  apply Subtype.ext
  exact project_number D g z

/-- Every original cycle has a finite decomposition in the actual quotient. -/
theorem finite_class_decomposition (z : cycles D H) :
    (∑ g ∈ stateDegrees D (z : State D),
      classOf D H h26 hHG hGH (cycleProject D H g z)) =
        classOf D H h26 hHG hGH z := by
  rw [← map_sum]
  apply congrArg (classOf D H h26 hHG hGH)
  apply Subtype.ext
  simp only [Submodule.coe_sum]
  change (∑ g ∈ stateDegrees D (z : State D), project D g (z : State D)) = (z : State D)
  exact sum_project D (z : State D)

private theorem grades_independent : iSupIndep (grade D H h26 hHG hGH) := by
  exact (number D H h26 hHG hGH).eigenspaces_iSupIndep.comp
    (Int.cast_injective (α := ℂ))

private theorem grades_iSup : (⨆ g : ℤ, grade D H h26 hHG hGH g) = ⊤ := by
  apply top_unique
  intro c hc
  obtain ⟨z, rfl⟩ := LatticeBRSTCohomologyField.classOf_surjective D H h26 hHG hGH c
  rw [← finite_class_decomposition D H h26 hHG hGH z]
  apply Submodule.sum_mem
  intro g hg
  exact (le_iSup (grade D H h26 hHG hGH) g)
    (component_mem_grade D H h26 hHG hGH g z)

/-- The full original BRST quotient is the internal direct sum over ALL integers. -/
theorem grades_internal : DirectSum.IsInternal (grade D H h26 hHG hGH) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (grades_independent D H h26 hHG hGH) (grades_iSup D H h26 hHG hGH)

private theorem project_eq_zero_of_not_mem (g : ℤ) (x : State D)
    (hg : g ∉ stateDegrees D x) : project D g x = 0 := by
  apply (fullBasis D).repr.injective
  ext i
  rw [project_coefficient]
  simp only [map_zero, Finsupp.zero_apply]
  split_ifs with h
  · by_contra hn
    exact hg (Finset.mem_image.mpr ⟨i, Finsupp.mem_support_iff.mpr hn, h⟩)
  · rfl

/-- Projection extracts the SAME class from ANY cycle representative of an eigenclass. -/
theorem project_same_class (g : ℤ) (z : cycles D H)
    (hz : classOf D H h26 hHG hGH z ∈ grade D H h26 hHG hGH g) :
    classOf D H h26 hHG hGH (cycleProject D H g z) =
      classOf D H h26 hHG hGH z := by
  let s := insert g (stateDegrees D (z : State D))
  let c : ℤ → Cohomology D H h26 hHG hGH :=
    fun h => classOf D H h26 hHG hGH (cycleProject D H h z)
  have hsum : ∑ h ∈ s, c h = classOf D H h26 hHG hGH z := by
    dsimp [s, c]
    by_cases hg : g ∈ stateDegrees D (z : State D)
    · rw [Finset.insert_eq_of_mem hg, finite_class_decomposition]
    · rw [Finset.sum_insert hg, finite_class_decomposition]
      have hp : cycleProject D H g z = 0 := by
        apply Subtype.ext
        exact project_eq_zero_of_not_mem D g z hg
      rw [hp, map_zero, zero_add]
  have hd : classOf D H h26 hHG hGH z - c g ∈ grade D H h26 hHG hGH g :=
    (grade D H h26 hHG hGH g).sub_mem hz
      (component_mem_grade D H h26 hHG hGH g z)
  have ho : classOf D H h26 hHG hGH z - c g ∈
      ⨆ h : ℤ, ⨆ (_ : h ≠ g), grade D H h26 hHG hGH h := by
    have he : classOf D H h26 hHG hGH z - c g = ∑ h ∈ s.erase g, c h := by
      rw [← hsum, ← Finset.sum_erase_add _ _ (show g ∈ s by simp [s])]
      abel
    rw [he]
    apply Submodule.sum_mem
    intro h hh
    exact Submodule.mem_iSup_of_mem h
      (Submodule.mem_iSup_of_mem (Finset.mem_erase.mp hh).1
        (component_mem_grade D H h26 hHG hGH h z))
  have he : classOf D H h26 hHG hGH z - c g = 0 := by
    exact (Submodule.mem_bot ℂ).mp
      ((disjoint_iff_inf_le.mp ((grades_internal D H h26 hHG hGH).submodule_iSupIndep g))
        ⟨hd, ho⟩)
  exact (sub_eq_zero.mp he).symm

/-- Every integer eigenclass lifts to a cycle homogeneous for the ORIGINAL number operator. -/
theorem homogeneous_cycle_lift (g : ℤ) (c : Cohomology D H h26 hHG hGH)
    (hc : c ∈ grade D H h26 hHG hGH g) :
    ∃ z : cycles D H, classOf D H h26 hHG hGH z = c ∧
      tensorNumber D (z : State D) = (g : ℂ) • (z : State D) := by
  obtain ⟨z, rfl⟩ := LatticeBRSTCohomologyField.classOf_surjective D H h26 hHG hGH c
  exact ⟨cycleProject D H g z, project_same_class D H h26 hHG hGH g z hc,
    project_number D g z⟩

#print axioms finite_class_decomposition
#print axioms grades_internal
#print axioms project_same_class
#print axioms homogeneous_cycle_lift

end
end D5.S3.VertexAlgebra.LatticeBRSTCohomologyGhostGrading
