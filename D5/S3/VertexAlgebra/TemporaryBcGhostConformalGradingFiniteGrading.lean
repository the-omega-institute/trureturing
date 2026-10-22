import D5.S3.VertexAlgebra.BcGhostLZeroSpectrum
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.BcGhostFiniteGrading

open BcGhostFockSupport BcGhostLZeroSpectrum
open scoped BigOperators

noncomputable section

abbrev originalFock (K : Type*) [CommRing K] := BcGhostFockSupport.Fock K

abbrev originalL0 : Module.End ℂ (originalFock ℂ) := BcGhostFockSupport.L 0

theorem siteWeight_nonneg_of_ne_one (site : ℕ) (different : site ≠ 1) :
    0 ≤ siteWeight site := by
  unfold siteWeight
  split_ifs with even
  · omega
  · have quotientPositive : 1 ≤ site / 2 := by omega
    omega

theorem energy_lower_bound (subset : Finset ℕ) : -1 ≤ energy subset := by
  have nonnegative : 0 ≤ energy (subset.erase 1) := by
    unfold energy
    exact Finset.sum_nonneg fun site present =>
      siteWeight_nonneg_of_ne_one site (Finset.mem_erase.mp present).1
  by_cases present : 1 ∈ subset
  · have splitEnergy : energy subset = energy (subset.erase 1) + siteWeight 1 := by
      calc
        energy subset = energy (insert 1 (subset.erase 1)) := by
          rw [Finset.insert_erase present]
        _ = energy (subset.erase 1) + siteWeight 1 := by simp [energy, add_comm]
    have negativeWeight : siteWeight 1 = -1 := by norm_num [siteWeight]
    rw [splitEnergy, negativeWeight]
    omega
  · simpa [Finset.erase_eq_self.mpr present] using
      (le_trans (by norm_num : (-1 : ℤ) ≤ 0) nonnegative)

theorem occupied_siteWeight_le (subset : Finset ℕ) (site : ℕ)
    (present : site ∈ subset) : siteWeight site ≤ energy subset + 1 := by
  have remainderBound := energy_lower_bound (subset.erase site)
  have splitEnergy : energy subset = energy (subset.erase site) + siteWeight site := by
    calc
      energy subset = energy (insert site (subset.erase site)) := by
        rw [Finset.insert_erase present]
      _ = energy (subset.erase site) + siteWeight site := by simp [energy, add_comm]
  omega

theorem occupied_even_index_bound (h : ℤ) (subset : Finset ℕ)
    (homogeneous : energy subset = h) (index : ℕ) (present : 2 * index ∈ subset) :
    (index : ℤ) ≤ h - 1 := by
  have weightBound := occupied_siteWeight_le subset (2 * index) present
  have normalization : siteWeight (2 * index) = (index : ℤ) + 2 := by
    simp [siteWeight]
  rw [normalization, homogeneous] at weightBound
  omega

theorem occupied_odd_index_bound (h : ℤ) (subset : Finset ℕ)
    (homogeneous : energy subset = h) (index : ℕ) (present : 2 * index + 1 ∈ subset) :
    (index : ℤ) ≤ h + 2 := by
  have weightBound := occupied_siteWeight_le subset (2 * index + 1) present
  have parity : (2 * index + 1) % 2 ≠ 0 := by omega
  have quotient : (2 * index + 1) / 2 = index := by omega
  simp only [siteWeight, if_neg parity, quotient] at weightBound
  rw [homogeneous] at weightBound
  omega

def allowedSites (h : ℤ) : Finset ℕ := Finset.range (2 * (h + 2).toNat + 2)

theorem energy_subset_allowedSites (h : ℤ) (subset : Finset ℕ)
    (homogeneous : energy subset = h) : subset ⊆ allowedSites h := by
  intro site present
  have lowerBound : -1 ≤ h := by simpa [homogeneous] using energy_lower_bound subset
  have naturalBound : site / 2 ≤ (h + 2).toNat := by
    by_cases even : site % 2 = 0
    · have siteEquality : 2 * (site / 2) = site := by omega
      have evenBound := occupied_even_index_bound h subset homogeneous (site / 2)
        (by simpa [siteEquality] using present)
      omega
    · have siteEquality : 2 * (site / 2) + 1 = site := by omega
      have oddBound := occupied_odd_index_bound h subset homogeneous (site / 2)
        (by simpa [siteEquality] using present)
      omega
  change site ∈ Finset.range (2 * (h + 2).toNat + 2)
  rw [Finset.mem_range]
  omega

theorem energy_mem_powerset (h : ℤ) (subset : Finset ℕ)
    (homogeneous : energy subset = h) : subset ∈ (allowedSites h).powerset :=
  Finset.mem_powerset.mpr (energy_subset_allowedSites h subset homogeneous)

def gradeLabels (h : ℤ) : Set (Finset ℕ) := {subset | energy subset = h}

abbrev GradeLabel (h : ℤ) := {subset : Finset ℕ // energy subset = h}

instance gradeLabel_finite (h : ℤ) : Finite (GradeLabel h) := by
  let inclusion : GradeLabel h → ↥((allowedSites h).powerset) :=
    fun label => ⟨label.val, energy_mem_powerset h label.val label.property⟩
  exact Finite.of_injective inclusion (by
    intro first second equal
    apply Subtype.ext
    exact congrArg (fun value : ↥((allowedSites h).powerset) => value.val) equal)

instance gradeLabel_fintype (h : ℤ) : Fintype (GradeLabel h) :=
  Fintype.ofFinite (GradeLabel h)

def grade (h : ℤ) : Submodule ℂ (originalFock ℂ) :=
  Finsupp.supported ℂ ℂ (gradeLabels h)

theorem mem_grade_iff (h : ℤ) (state : originalFock ℂ) :
    state ∈ grade h ↔ ∀ subset, energy subset ≠ h → state subset = 0 := by
  simpa [grade, gradeLabels] using
    (Finsupp.mem_supported' (s := gradeLabels h) ℂ state)

theorem L_zero_coefficient (state : originalFock ℂ) (subset : Finset ℕ) :
    (originalL0 state) subset = (energy subset : ℂ) * state subset := by
  induction state using Finsupp.induction_linear with
  | zero => simp
  | add first second firstProof secondProof =>
      simp only [map_add, Finsupp.add_apply, firstProof, secondProof, mul_add]
  | single label scalar =>
      rw [BcGhostLZeroSpectrum.L_zero_single]
      by_cases equal : label = subset
      · subst label
        simp
      · simp [Finsupp.single_apply, equal]

theorem grade_eq_eigenspace (h : ℤ) :
    grade h = originalL0.eigenspace (h : ℂ) := by
  apply Submodule.ext
  intro state
  rw [mem_grade_iff, Module.End.mem_eigenspace_iff]
  constructor
  · intro supported
    apply Finsupp.ext
    intro subset
    rw [L_zero_coefficient, Finsupp.smul_apply, smul_eq_mul]
    by_cases homogeneous : energy subset = h
    · rw [homogeneous]
    · rw [supported subset homogeneous]
      simp
  · intro eigenstate subset different
    have coefficientEquality := congrArg (fun value : originalFock ℂ => value subset) eigenstate
    change (originalL0 state) subset = ((h : ℂ) • state) subset at coefficientEquality
    rw [L_zero_coefficient, Finsupp.smul_apply, smul_eq_mul] at coefficientEquality
    have scalarDifferent : (energy subset : ℂ) ≠ (h : ℂ) := by exact_mod_cast different
    have productZero : ((energy subset : ℂ) - (h : ℂ)) * state subset = 0 := by
      rw [sub_mul, coefficientEquality, sub_self]
    exact (mul_eq_zero.mp productZero).resolve_left (sub_ne_zero.mpr scalarDifferent)

def gradeEquiv (h : ℤ) : grade h ≃ₗ[ℂ] (GradeLabel h →₀ ℂ) :=
  Finsupp.supportedEquivFinsupp (R := ℂ) (gradeLabels h)

def gradeBasis (h : ℤ) : Module.Basis (GradeLabel h) ℂ (grade h) :=
  Module.Basis.ofRepr (gradeEquiv h)

theorem gradeBasis_coe (h : ℤ) (label : GradeLabel h) :
    (gradeBasis h label : originalFock ℂ) = Finsupp.single label.val 1 := by
  change ((gradeEquiv h).symm (Finsupp.single label 1) : originalFock ℂ) = _
  exact Finsupp.supportedEquivFinsupp_symm_single (R := ℂ) (gradeLabels h) label 1

instance grade_finiteDimensional (h : ℤ) : FiniteDimensional ℂ (grade h) := by
  let basis : Module.Basis (GradeLabel h) ℂ (GradeLabel h →₀ ℂ) := Finsupp.basisSingleOne
  letI : FiniteDimensional ℂ (GradeLabel h →₀ ℂ) := basis.finiteDimensional_of_finite
  exact (gradeEquiv h).symm.finiteDimensional

theorem grade_finrank (h : ℤ) :
    Module.finrank ℂ (grade h) = Fintype.card (GradeLabel h) :=
  Module.finrank_eq_card_basis (gradeBasis h)

def eigenspaceGradeEquiv (h : ℤ) : originalL0.eigenspace (h : ℂ) ≃ₗ[ℂ] grade h where
  toFun state := ⟨state.val, by rw [grade_eq_eigenspace]; exact state.property⟩
  invFun state := ⟨state.val, by rw [← grade_eq_eigenspace]; exact state.property⟩
  left_inv state := rfl
  right_inv state := rfl
  map_add' first second := rfl
  map_smul' scalar state := rfl

def eigenspaceEquiv (h : ℤ) : originalL0.eigenspace (h : ℂ) ≃ₗ[ℂ] (GradeLabel h →₀ ℂ) :=
  (eigenspaceGradeEquiv h).trans (gradeEquiv h)

def eigenspaceBasis (h : ℤ) :
    Module.Basis (GradeLabel h) ℂ (originalL0.eigenspace (h : ℂ)) :=
  Module.Basis.ofRepr (eigenspaceEquiv h)

theorem eigenspace_finiteDimensional (h : ℤ) :
    FiniteDimensional ℂ (originalL0.eigenspace (h : ℂ)) :=
  (eigenspaceBasis h).finiteDimensional_of_finite

theorem eigenspace_finrank (h : ℤ) :
    Module.finrank ℂ (originalL0.eigenspace (h : ℂ)) = Fintype.card (GradeLabel h) := by
  rw [← grade_eq_eigenspace]
  exact grade_finrank h

theorem grade_eq_bot_of_lt (h : ℤ) (below : h < -1) : grade h = ⊥ := by
  apply eq_bot_iff.mpr
  intro state supported
  change state = 0
  apply Finsupp.ext
  intro subset
  change state subset = 0
  apply (mem_grade_iff h state).mp supported subset
  have lowerBound := energy_lower_bound subset
  omega

theorem eigenspace_eq_bot_of_lt (h : ℤ) (below : h < -1) :
    originalL0.eigenspace (h : ℂ) = ⊥ := by
  rw [← grade_eq_eigenspace]
  exact grade_eq_bot_of_lt h below

theorem eigenvalue_integral (value : ℂ) (state : originalFock ℂ)
    (nonzero : state ≠ 0) (eigenstate : originalL0 state = value • state) :
    ∃ h : ℤ, -1 ≤ h ∧ value = (h : ℂ) := by
  have coefficientExists : ∃ subset, state subset ≠ 0 := by
    by_contra absent
    push_neg at absent
    apply nonzero
    ext subset
    exact absent subset
  obtain ⟨subset, coefficientNonzero⟩ := coefficientExists
  have coefficientEquality := congrArg (fun vector : originalFock ℂ => vector subset) eigenstate
  change (originalL0 state) subset = (value • state) subset at coefficientEquality
  rw [L_zero_coefficient, Finsupp.smul_apply, smul_eq_mul] at coefficientEquality
  have productZero : ((energy subset : ℂ) - value) * state subset = 0 := by
    rw [sub_mul, coefficientEquality, sub_self]
  have scalarEquality : (energy subset : ℂ) = value :=
    sub_eq_zero.mp ((mul_eq_zero.mp productZero).resolve_right coefficientNonzero)
  exact ⟨energy subset, energy_lower_bound subset, scalarEquality.symm⟩

#print axioms energy_lower_bound
#print axioms occupied_even_index_bound
#print axioms occupied_odd_index_bound
#print axioms grade_eq_eigenspace
#print axioms eigenspace_finiteDimensional
#print axioms eigenspace_eq_bot_of_lt
#print axioms eigenvalue_integral

end

end D5.S3.VertexAlgebra.BcGhostFiniteGrading
