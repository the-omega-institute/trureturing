import D5.S3.VertexAlgebra.TemporaryBcGhostConformalGradingFiniteGrading
import Mathlib.Algebra.DirectSum.Module

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition

open BcGhostLZeroSpectrum BcGhostFiniteGrading
open scoped BigOperators DirectSum

noncomputable section

def gradeProjection (h : ℤ) : originalFock ℂ →ₗ[ℂ] grade h := by
  classical
  exact Finsupp.restrictDom ℂ ℂ (gradeLabels h)

def project (h : ℤ) : Module.End ℂ (originalFock ℂ) :=
  (grade h).subtype.comp (gradeProjection h)

theorem project_coefficient (h : ℤ) (state : originalFock ℂ) (subset : Finset ℕ) :
    project h state subset = if energy subset = h then state subset else 0 := by
  classical
  change (Finsupp.restrictDom ℂ ℂ (gradeLabels h) state : originalFock ℂ) subset = _
  rw [Finsupp.restrictDom_apply, Finsupp.filter_apply]
  simp only [gradeLabels, Set.mem_setOf_eq]

theorem project_homogeneous (level h : ℤ) (state : originalFock ℂ)
    (homogeneous : state ∈ grade level) :
    project h state = if level = h then state else 0 := by
  apply Finsupp.ext
  intro subset
  rw [project_coefficient]
  by_cases sameGrade : level = h
  · subst h
    rw [if_pos rfl]
    by_cases supported : energy subset = level
    · rw [if_pos supported]
    · rw [if_neg supported, (mem_grade_iff level state).mp homogeneous subset supported]
  · rw [if_neg sameGrade]
    change (if energy subset = h then state subset else 0) = 0
    by_cases selected : energy subset = h
    · rw [if_pos selected]
      apply (mem_grade_iff level state).mp homogeneous subset
      omega
    · rw [if_neg selected]

def gradeSupport (state : originalFock ℂ) : Finset ℤ := state.support.image energy

theorem project_eq_zero_outside_gradeSupport (state : originalFock ℂ) (h : ℤ)
    (absent : h ∉ gradeSupport state) : project h state = 0 := by
  apply Finsupp.ext
  intro subset
  rw [project_coefficient]
  change (if energy subset = h then state subset else 0) = 0
  by_cases homogeneous : energy subset = h
  · rw [if_pos homogeneous]
    by_contra nonzero
    apply absent
    exact Finset.mem_image.mpr ⟨subset, Finsupp.mem_support_iff.mpr nonzero, homogeneous⟩
  · rw [if_neg homogeneous]

theorem project_ne_zero_iff (state : originalFock ℂ) (h : ℤ) :
    project h state ≠ 0 ↔ h ∈ gradeSupport state := by
  constructor
  · intro nonzero
    by_contra absent
    exact nonzero (project_eq_zero_outside_gradeSupport state h absent)
  · intro present vanishes
    obtain ⟨subset, supported, homogeneous⟩ := Finset.mem_image.mp present
    have coefficientNonzero : state subset ≠ 0 := Finsupp.mem_support_iff.mp supported
    have coefficientEquality := congrArg (fun vector : originalFock ℂ => vector subset) vanishes
    rw [project_coefficient, if_pos homogeneous] at coefficientEquality
    exact coefficientNonzero coefficientEquality

theorem finite_reconstruction (state : originalFock ℂ) :
    (∑ h ∈ gradeSupport state, project h state) = state := by
  apply Finsupp.ext
  intro subset
  change (Finsupp.lapply subset : originalFock ℂ →ₗ[ℂ] ℂ)
    (∑ h ∈ gradeSupport state, project h state) = state subset
  rw [map_sum]
  change (∑ h ∈ gradeSupport state, project h state subset) = state subset
  simp_rw [project_coefficient]
  by_cases present : subset ∈ state.support
  · have gradePresent : energy subset ∈ gradeSupport state :=
      Finset.mem_image.mpr ⟨subset, present, rfl⟩
    simp [gradePresent]
  · have zeroCoefficient : state subset = 0 := by
      by_contra nonzero
      exact present (Finsupp.mem_support_iff.mpr nonzero)
    simp [zeroCoefficient]

theorem finite_homogeneous_family_unique (labels : Finset ℤ)
    (family : ℤ → originalFock ℂ)
    (homogeneous : ∀ h ∈ labels, family h ∈ originalL0.eigenspace (h : ℂ))
    (state : originalFock ℂ) (reconstructs : (∑ h ∈ labels, family h) = state)
    (h : ℤ) : project h state = if h ∈ labels then family h else 0 := by
  rw [← reconstructs, map_sum]
  calc
    (∑ level ∈ labels, project h (family level)) =
        ∑ level ∈ labels, if level = h then family level else 0 := by
      apply Finset.sum_congr rfl
      intro level present
      apply project_homogeneous level h (family level)
      rw [grade_eq_eigenspace]
      exact homogeneous level present
    _ = if h ∈ labels then family h else 0 := by simp

abbrev HomogeneousDirectSum := ⨁ h : ℤ, grade h

def assembly : HomogeneousDirectSum →ₗ[ℂ] originalFock ℂ :=
  DirectSum.toModule ℂ ℤ (originalFock ℂ) (fun h => (grade h).subtype)

def decomposition : originalFock ℂ →ₗ[ℂ] HomogeneousDirectSum :=
  Finsupp.linearCombination ℂ (fun subset =>
    DirectSum.lof ℂ ℤ (fun h => grade h) (energy subset)
      ⟨Finsupp.single subset 1,
        Finsupp.single_mem_supported ℂ 1 (show subset ∈ gradeLabels (energy subset) from rfl)⟩)

theorem assembly_decomposition : assembly.comp decomposition = LinearMap.id := by
  apply Finsupp.basisSingleOne.ext
  intro subset
  change assembly (decomposition (Finsupp.single subset 1)) = Finsupp.single subset 1
  simp [assembly, decomposition]

theorem decomposition_grade (h : ℤ) :
    decomposition.comp (grade h).subtype = DirectSum.lof ℂ ℤ (fun level => grade level) h := by
  apply (gradeBasis h).ext
  intro label
  change decomposition (gradeBasis h label : originalFock ℂ) =
    DirectSum.lof ℂ ℤ (fun level => grade level) h (gradeBasis h label)
  rw [gradeBasis_coe]
  rcases label with ⟨subset, homogeneous⟩
  change energy subset = h at homogeneous
  subst h
  simp only [decomposition, Finsupp.linearCombination_single, one_smul]
  apply congrArg (DirectSum.lof ℂ ℤ (fun level => grade level) (energy subset))
  apply Subtype.ext
  exact (gradeBasis_coe (energy subset) ⟨subset, rfl⟩).symm

theorem decomposition_assembly : decomposition.comp assembly = LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro h
  apply LinearMap.ext
  intro state
  change decomposition (assembly (DirectSum.lof ℂ ℤ (fun level => grade level) h state)) =
    DirectSum.lof ℂ ℤ (fun level => grade level) h state
  have assembled : assembly (DirectSum.lof ℂ ℤ (fun level => grade level) h state) =
      (state : originalFock ℂ) := by simp [assembly]
  rw [assembled]
  exact LinearMap.congr_fun (decomposition_grade h) state

def homogeneousEquiv : originalFock ℂ ≃ₗ[ℂ] HomogeneousDirectSum where
  toFun := decomposition
  invFun := assembly
  left_inv state := LinearMap.congr_fun assembly_decomposition state
  right_inv state := LinearMap.congr_fun decomposition_assembly state
  map_add' first second := decomposition.map_add first second
  map_smul' scalar state := decomposition.map_smul scalar state

theorem decomposition_eq_finite_sum (state : originalFock ℂ) :
    decomposition state = ∑ h ∈ gradeSupport state,
      DirectSum.lof ℂ ℤ (fun level => grade level) h (gradeProjection h state) := by
  apply homogeneousEquiv.symm.injective
  change assembly (decomposition state) =
    assembly (∑ h ∈ gradeSupport state,
      DirectSum.lof ℂ ℤ (fun level => grade level) h (gradeProjection h state))
  have original : assembly (decomposition state) = state :=
    LinearMap.congr_fun assembly_decomposition state
  have reconstructed : assembly (∑ h ∈ gradeSupport state,
      DirectSum.lof ℂ ℤ (fun level => grade level) h (gradeProjection h state)) = state := by
    rw [map_sum]
    simpa [assembly, project] using finite_reconstruction state
  exact original.trans reconstructed.symm

def actualHomogeneousEquiv :
    originalFock ℂ ≃ₗ[ℂ] ⨁ h : ℤ, originalL0.eigenspace (h : ℂ) :=
  homogeneousEquiv.trans
    (DirectSum.congrLinearEquiv (fun h => (eigenspaceGradeEquiv h).symm))

theorem actual_decomposition_eq_finite_sum (state : originalFock ℂ) :
    actualHomogeneousEquiv state = ∑ h ∈ gradeSupport state,
      DirectSum.lof ℂ ℤ (fun level => originalL0.eigenspace (level : ℂ)) h
        ((eigenspaceGradeEquiv h).symm (gradeProjection h state)) := by
  change DirectSum.lmap (fun h => (eigenspaceGradeEquiv h).symm.toLinearMap)
    (decomposition state) = _
  rw [decomposition_eq_finite_sum, map_sum]
  apply Finset.sum_congr rfl
  intro h present
  exact DirectSum.lmap_lof
    (fun level => (eigenspaceGradeEquiv level).symm.toLinearMap) h (gradeProjection h state)

#print axioms finite_reconstruction
#print axioms finite_homogeneous_family_unique
#print axioms actualHomogeneousEquiv
#print axioms actual_decomposition_eq_finite_sum

end

end D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition
