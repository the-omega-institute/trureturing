import D5.S3.VertexAlgebra.TemporaryBcGhostConformalGradingHomogeneousDecomposition

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.BcGhostLowGrades

open BcGhostLZeroSpectrum BcGhostFiniteGrading BcGhostHomogeneousDecomposition
open scoped BigOperators

noncomputable section

def minimumLabels : Finset (Finset ℕ) := {{1}, {1, 3}}

def zeroLabels : Finset (Finset ℕ) := {∅, {3}, {1, 5}, {1, 3, 5}}

theorem mem_minimumLabels_iff (subset : Finset ℕ) :
    subset ∈ minimumLabels ↔ energy subset = -1 := by
  constructor
  · intro candidate
    simp only [minimumLabels, Finset.mem_insert, Finset.mem_singleton] at candidate
    rcases candidate with rfl | rfl <;> norm_num [energy, siteWeight]
  · intro homogeneous
    have smallSupport : subset ⊆ ({1, 3} : Finset ℕ) := by
      intro site present
      by_cases even : site % 2 = 0
      · have representation : 2 * (site / 2) = site := by omega
        have indexBound := occupied_even_index_bound (-1) subset homogeneous (site / 2)
          (by simpa [representation] using present)
        omega
      · have representation : 2 * (site / 2) + 1 = site := by omega
        have indexBound := occupied_odd_index_bound (-1) subset homogeneous (site / 2)
          (by simpa [representation] using present)
        have siteCases : site = 1 ∨ site = 3 := by omega
        rcases siteCases with rfl | rfl <;> simp
    have candidates := Finset.mem_powerset.mpr smallSupport
    have enumeration : ({1, 3} : Finset ℕ).powerset =
        {∅, {1}, {3}, {1, 3}} := by decide
    rw [enumeration] at candidates
    simp only [Finset.mem_insert, Finset.mem_singleton] at candidates
    rcases candidates with rfl | rfl | rfl | rfl <;>
      (norm_num [energy, siteWeight] at homogeneous <;> norm_num [minimumLabels])

theorem mem_zeroLabels_iff (subset : Finset ℕ) :
    subset ∈ zeroLabels ↔ energy subset = 0 := by
  constructor
  · intro candidate
    simp only [zeroLabels, Finset.mem_insert, Finset.mem_singleton] at candidate
    rcases candidate with rfl | rfl | rfl | rfl <;> norm_num [energy, siteWeight]
  · intro homogeneous
    have smallSupport : subset ⊆ ({1, 3, 5} : Finset ℕ) := by
      intro site present
      by_cases even : site % 2 = 0
      · have representation : 2 * (site / 2) = site := by omega
        have indexBound := occupied_even_index_bound 0 subset homogeneous (site / 2)
          (by simpa [representation] using present)
        omega
      · have representation : 2 * (site / 2) + 1 = site := by omega
        have indexBound := occupied_odd_index_bound 0 subset homogeneous (site / 2)
          (by simpa [representation] using present)
        have siteCases : site = 1 ∨ site = 3 ∨ site = 5 := by omega
        rcases siteCases with rfl | rfl | rfl <;> simp
    have candidates := Finset.mem_powerset.mpr smallSupport
    have enumeration : ({1, 3, 5} : Finset ℕ).powerset =
        {∅, {1}, {3}, {5}, {1, 3}, {1, 5}, {3, 5}, {1, 3, 5}} := by decide
    rw [enumeration] at candidates
    simp only [Finset.mem_insert, Finset.mem_singleton] at candidates
    rcases candidates with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (norm_num [energy, siteWeight] at homogeneous <;> norm_num [zeroLabels])

def minimumLabelEquiv : GradeLabel (-1) ≃ ↥minimumLabels where
  toFun label := ⟨label.val, (mem_minimumLabels_iff label.val).mpr label.property⟩
  invFun label := ⟨label.val, (mem_minimumLabels_iff label.val).mp label.property⟩
  left_inv label := rfl
  right_inv label := rfl

def zeroLabelEquiv : GradeLabel 0 ≃ ↥zeroLabels where
  toFun label := ⟨label.val, (mem_zeroLabels_iff label.val).mpr label.property⟩
  invFun label := ⟨label.val, (mem_zeroLabels_iff label.val).mp label.property⟩
  left_inv label := rfl
  right_inv label := rfl

theorem minimum_eigenspace_finrank :
    Module.finrank ℂ (originalL0.eigenspace (-1 : ℂ)) = 2 := by
  have uniform := eigenspace_finrank (-1)
  have labelCount : Fintype.card (GradeLabel (-1)) = 2 := by
    rw [Fintype.card_congr minimumLabelEquiv, Fintype.card_coe]
    decide
  rw [show ((-1 : ℤ) : ℂ) = (-1 : ℂ) by norm_num, labelCount] at uniform
  exact uniform

theorem zero_eigenspace_finrank :
    Module.finrank ℂ (originalL0.eigenspace (0 : ℂ)) = 4 := by
  have uniform := eigenspace_finrank 0
  have labelCount : Fintype.card (GradeLabel 0) = 4 := by
    rw [Fintype.card_congr zeroLabelEquiv, Fintype.card_coe]
    decide
  rw [show ((0 : ℤ) : ℂ) = (0 : ℂ) by norm_num, labelCount] at uniform
  exact uniform

theorem minimum_state_reconstruction (state : originalFock ℂ)
    (homogeneous : state ∈ originalL0.eigenspace (-1 : ℂ)) :
    state = Finsupp.single {1} (state {1}) + Finsupp.single {1, 3} (state {1, 3}) := by
  have gradeMember : state ∈ grade (-1) := by
    rw [grade_eq_eigenspace]
    simpa using homogeneous
  apply Finsupp.ext
  intro subset
  by_cases first : subset = {1}
  · subst subset
    simp [show ({1, 3} : Finset ℕ) ≠ {1} by decide]
  · by_cases second : subset = {1, 3}
    · subst subset
      simp [show ({1} : Finset ℕ) ≠ {1, 3} by decide]
    · have offGrade : energy subset ≠ -1 := by
        intro equal
        have member := (mem_minimumLabels_iff subset).mpr equal
        simp only [minimumLabels, Finset.mem_insert, Finset.mem_singleton] at member
        exact member.elim first second
      have coefficientZero := (mem_grade_iff (-1) state).mp gradeMember subset offGrade
      simp [Finsupp.single_apply, first, second, Ne.symm first, Ne.symm second, coefficientZero]

theorem zero_state_reconstruction (state : originalFock ℂ)
    (homogeneous : state ∈ originalL0.eigenspace (0 : ℂ)) :
    state = Finsupp.single ∅ (state ∅) + Finsupp.single {3} (state {3}) +
      Finsupp.single {1, 5} (state {1, 5}) +
      Finsupp.single {1, 3, 5} (state {1, 3, 5}) := by
  have gradeMember : state ∈ grade 0 := by
    rw [grade_eq_eigenspace]
    simpa using homogeneous
  apply Finsupp.ext
  intro subset
  by_cases empty : subset = ∅
  · subst subset
    simp
  · by_cases zeroSite : subset = {3}
    · subst subset
      simp [show ({1, 5} : Finset ℕ) ≠ {3} by decide,
        show ({1, 3, 5} : Finset ℕ) ≠ {3} by decide]
    · by_cases pair : subset = {1, 5}
      · subst subset
        simp [show ({3} : Finset ℕ) ≠ {1, 5} by decide,
          show ({1, 3, 5} : Finset ℕ) ≠ {1, 5} by decide]
      · by_cases triple : subset = {1, 3, 5}
        · subst subset
          simp [show ({3} : Finset ℕ) ≠ {1, 3, 5} by decide,
            show ({1, 5} : Finset ℕ) ≠ {1, 3, 5} by decide]
        · have offGrade : energy subset ≠ 0 := by
            intro equal
            have member := (mem_zeroLabels_iff subset).mpr equal
            simp only [zeroLabels, Finset.mem_insert, Finset.mem_singleton] at member
            rcases member with emptyCase | zeroCase | pairCase | tripleCase
            · exact empty emptyCase
            · exact zeroSite zeroCase
            · exact pair pairCase
            · exact triple tripleCase
          have coefficientZero := (mem_grade_iff 0 state).mp gradeMember subset offGrade
          simp [Finsupp.single_apply, empty, zeroSite, pair, triple, Ne.symm empty,
            Ne.symm zeroSite, Ne.symm pair, Ne.symm triple, coefficientZero]

#print axioms minimum_eigenspace_finrank
#print axioms zero_eigenspace_finrank
#print axioms minimum_state_reconstruction
#print axioms zero_state_reconstruction

end

end D5.S3.VertexAlgebra.BcGhostLowGrades
