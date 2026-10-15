/- GID: D5/S3/VertexAlgebra/BcGhostRelativeForm
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/BcGhostRelativeForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual zero-mode kernel needs c(0) insertion and has zero relative radicals.
-/

import D5.S3.VertexAlgebra.BcGhostBpZForm
import Mathlib.LinearAlgebra.Finsupp.Supported

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.BcGhostRelativeForm

noncomputable section

open D5.S3.VertexAlgebra.BcGhostFockSupport
open D5.S3.VertexAlgebra.BcGhostNumber
open D5.S3.VertexAlgebra.BcGhostStressCurrent
open D5.S3.VertexAlgebra.BcGhostSuperGenerators
open D5.S3.VertexAlgebra.BcGhostBpZForm
open scoped BigOperators

def Relative : Submodule ℂ GhostFock := LinearMap.ker (b 0)

def RelativeDegreeOne : Submodule ℂ GhostFock :=
  Relative ⊓ Finsupp.supported ℂ ℂ {sites | degree sites = 1}

def relativeForm : Relative →ₗ[ℂ] (Relative →ₗ[ℂ] ℂ) where
  toFun state := (bpzForm state).comp ((c 0).comp Relative.subtype)
  map_add' := by intro first second; ext other; simp
  map_smul' := by intro scalar state; ext other; simp

private theorem zero_mode_split (state : GhostFock) :
    b 0 (c 0 state) + c 0 (b 0 state) = state := by
  have law := congrArg (fun operator : Module.End ℂ GhostFock => operator state)
    (b_c (K := ℂ) 0 0)
  simpa using law

private theorem b0_square (state : GhostFock) : b 0 (b 0 state) = 0 := by
  have law := congrArg (fun operator : Module.End ℂ GhostFock => operator state)
    (b_b (K := ℂ) 0 0)
  have doubled : (2 : ℂ) • b 0 (b 0 state) = 0 := by
    simpa [two_smul] using law
  exact (smul_eq_zero.mp doubled).resolve_left (by norm_num)

private theorem c0_square (state : GhostFock) : c 0 (c 0 state) = 0 := by
  have law := congrArg (fun operator : Module.End ℂ GhostFock => operator state)
    (c_c (K := ℂ) 0 0)
  have doubled : (2 : ℂ) • c 0 (c 0 state) = 0 := by
    simpa [two_smul] using law
  exact (smul_eq_zero.mp doubled).resolve_left (by norm_num)

private theorem relative_reconstruction (state : Relative) :
    b 0 (c 0 (state : GhostFock)) = state := by
  have law := zero_mode_split state
  have member : b 0 (state : GhostFock) = 0 := state.property
  simpa [member] using law

theorem relative_isotropic (first second : Relative) :
    BPZ (first : GhostFock) (second : GhostFock) = 0 := by
  rw [← relative_reconstruction first, BPZ_b]
  have member : b 0 (second : GhostFock) = 0 := second.property
  simp [member, BPZ]

private theorem full_left_nondegenerate (state : GhostFock)
    (vanishing : ∀ other : GhostFock, BPZ state other = 0) : state = 0 := by
  ext sites
  have law := vanishing (basis (chi sites))
  rw [BPZ_symmetric, BPZ_basis, chi_involutive] at law
  exact (mul_eq_zero.mp law).resolve_left (eps_nonzero (chi sites))

private theorem relative_left_zero (state : Relative)
    (vanishing : ∀ other : Relative, relativeForm state other = 0) : state = 0 := by
  apply Subtype.ext
  apply full_left_nondegenerate
  intro other
  rw [← zero_mode_split other, BPZ_add_right]
  have first : BPZ (state : GhostFock) (b 0 (c 0 other)) = 0 :=
    relative_isotropic state ⟨b 0 (c 0 other), b0_square (c 0 other)⟩
  have second := vanishing ⟨b 0 other, b0_square other⟩
  change BPZ (state : GhostFock) (c 0 (b 0 other)) = 0 at second
  rw [first, second, add_zero]

private theorem relative_right_zero (state : Relative)
    (vanishing : ∀ other : Relative, relativeForm other state = 0) : state = 0 := by
  have inserted : c 0 (state : GhostFock) = 0 := by
    apply full_left_nondegenerate
    intro other
    rw [BPZ_symmetric, ← zero_mode_split other, BPZ_add_left]
    have first := vanishing ⟨b 0 (c 0 other), b0_square (c 0 other)⟩
    change BPZ (b 0 (c 0 other)) (c 0 (state : GhostFock)) = 0 at first
    rw [first, BPZ_c]
    simp [c0_square, BPZ]
  apply Subtype.ext
  rw [← relative_reconstruction state, inserted, map_zero]
  rfl

theorem relativeForm_radicals :
    LinearMap.ker relativeForm = ⊥ ∧ LinearMap.ker relativeForm.flip = ⊥ := by
  constructor
  · apply le_antisymm
    · intro state member
      have vanishing : ∀ other : Relative, relativeForm state other = 0 := by
        intro other
        exact LinearMap.congr_fun member other
      simpa using relative_left_zero state vanishing
    · exact bot_le
  · apply le_antisymm
    · intro state member
      have vanishing : ∀ other : Relative, relativeForm other state = 0 := by
        intro other
        exact LinearMap.congr_fun member other
      simpa using relative_right_zero state vanishing
    · exact bot_le

private theorem J_coeff (state : GhostFock) (sites : Finset ℕ) :
    J state sites = (degree sites : ℂ) * state sites := by
  classical
  induction state using Finsupp.induction_linear with
  | zero => simp
  | add first second firstLaw secondLaw => simp [firstLaw, secondLaw, mul_add]
  | single support scalar =>
    simp [J, Finsupp.single_apply, smul_smul, smul_eq_mul]
    split_ifs with same
    · subst support; ring
    · ring

private theorem homogeneous_eigenvalue (grade : ℤ) (state : GhostFock) :
    HomogeneousDegree grade state ↔ J state = (grade : ℂ) • state := by
  constructor
  · intro homogeneousState
    ext sites
    rw [J_coeff, Finsupp.smul_apply, smul_eq_mul]
    by_cases nonzero : state sites = 0
    · simp [nonzero]
    · rw [homogeneousState sites (Finsupp.mem_support_iff.mpr nonzero)]
  · intro eigenvalue sites member
    have law := congrArg (fun vector : GhostFock => vector sites) eigenvalue
    rw [J_coeff, Finsupp.smul_apply, smul_eq_mul] at law
    have casts : (degree sites : ℂ) = (grade : ℂ) :=
      mul_right_cancel₀ (Finsupp.mem_support_iff.mp member) law
    exact_mod_cast casts

private theorem c0_degree (grade : ℤ) (state : GhostFock)
    (homogeneousState : HomogeneousDegree grade state) :
    HomogeneousDegree (grade + 1) (c 0 state) := by
  apply (homogeneous_eigenvalue (grade + 1) (c 0 state)).mpr
  have law := congrArg (fun operator : Module.End ℂ GhostFock => operator state)
    (J_c_commutator (K := ℂ) 0)
  change J (c 0 state) - c 0 (J state) = c 0 state at law
  rw [(homogeneous_eigenvalue grade state).mp homogeneousState, map_smul] at law
  rw [Int.cast_add, Int.cast_one, add_smul, one_smul]
  exact (sub_eq_iff_eq_add.mp law).trans (add_comm _ _)

theorem relativeForm_degree_selection (leftGrade rightGrade : ℤ)
    (first second : Relative)
    (leftHomogeneous : HomogeneousDegree leftGrade first)
    (rightHomogeneous : HomogeneousDegree rightGrade second)
    (mismatch : leftGrade + rightGrade ≠ 2) : relativeForm first second = 0 := by
  apply BPZ_degree_selection leftGrade (rightGrade + 1) first (c 0 second)
    leftHomogeneous (c0_degree rightGrade second rightHomogeneous)
  omega

private theorem kernel_coefficients (state : GhostFock) :
    state ∈ Relative ↔ ∀ sites : Finset ℕ, 3 ∈ sites → state sites = 0 := by
  constructor
  · intro member sites occupied
    have absent : 3 ∉ sites.erase 3 := by simp
    have law := congrArg (fun vector : GhostFock => vector (sites.erase 3)) member
    change annihilate 3 state (sites.erase 3) = 0 at law
    rw [annihilate_coeff, if_neg absent, Finset.insert_erase occupied] at law
    exact (mul_eq_zero.mp law).resolve_left (pow_ne_zero _ (by norm_num))
  · intro coefficients
    change b 0 state = 0
    ext sites
    change annihilate 3 state sites = 0
    rw [annihilate_coeff]
    split_ifs with occupied
    · rfl
    · simp [coefficients (insert 3 sites) (by simp)]

private def degreePart (grade : ℤ) (state : GhostFock) : GhostFock :=
  state.filter (fun sites => degree sites = grade)

private theorem degreePart_relative (grade : ℤ) (state : Relative) :
    degreePart grade state ∈ Relative := by
  apply (kernel_coefficients _).mpr
  intro sites occupied
  simp [degreePart, Finsupp.filter_apply,
    (kernel_coefficients _).mp state.property sites occupied]

private theorem degreePart_homogeneous (grade : ℤ) (state : GhostFock) :
    HomogeneousDegree grade (degreePart grade state) := by
  intro sites member
  by_contra mismatch
  exact (Finsupp.mem_support_iff.mp member) (by simp [degreePart, mismatch])

private theorem basis_homogeneous (sites : Finset ℕ) :
    HomogeneousDegree (degree sites) (basis sites) := by
  intro support member
  have same : support = sites := by simpa [basis] using member
  rw [same]

private theorem relative_one_projection (state : Relative)
    (homogeneousState : HomogeneousDegree 1 state) (other : Relative) :
    BPZ (state : GhostFock) (c 0 (degreePart 1 other)) =
      BPZ (state : GhostFock) (c 0 other) := by
  classical
  have ambient (vector : GhostFock) :
      BPZ (state : GhostFock) (c 0 (degreePart 1 vector)) =
        BPZ (state : GhostFock) (c 0 vector) := by
    induction vector using Finsupp.induction_linear with
    | zero => simp [degreePart, Finsupp.filter_zero]
    | add first second firstLaw secondLaw =>
      have filtered : degreePart 1 (first + second) = degreePart 1 first + degreePart 1 second := by
        exact Finsupp.filter_add
      simp only [filtered, map_add, BPZ_add_right, firstLaw, secondLaw]
    | single sites scalar =>
      by_cases grade : degree sites = 1
      · simp [degreePart, Finsupp.filter_single_of_pos
          (p := fun sites : Finset ℕ => degree sites = 1) grade]
      · have basisZero : BPZ (state : GhostFock) (c 0 (basis sites)) = 0 := by
          by_cases occupied : 3 ∈ sites
          · simp [c, create, createBasis, basis, occupied, BPZ]
          · let restrictedBasis : Relative := ⟨basis sites, by
              change b 0 (basis sites) = 0
              simp [b, annihilate, annihilateBasis, basis, occupied]⟩
            exact relativeForm_degree_selection 1 (degree sites) state restrictedBasis
              homogeneousState (basis_homogeneous sites) (by omega)
        have singleBasis : Finsupp.single sites scalar = scalar • basis sites := by simp [basis]
        have filtered : degreePart 1 (Finsupp.single sites scalar) = 0 := by
          exact Finsupp.filter_single_of_neg
            (p := fun sites : Finset ℕ => degree sites = 1) grade
        rw [filtered, singleBasis, map_smul, BPZ_linear_right, basisZero, mul_zero]
        simp [BPZ]
  exact ambient other

def relativeOneForm : RelativeDegreeOne →ₗ[ℂ] (RelativeDegreeOne →ₗ[ℂ] ℂ) where
  toFun state := (bpzForm state).comp ((c 0).comp RelativeDegreeOne.subtype)
  map_add' := by intro first second; ext other; simp
  map_smul' := by intro scalar state; ext other; simp

private theorem one_homogeneous (state : RelativeDegreeOne) :
    HomogeneousDegree 1 (state : GhostFock) := state.property.2

private theorem degree_one_parity (state : GhostFock)
    (homogeneousState : HomogeneousDegree 1 state) : state ∈ homogeneous 1 := by
  intro sites mismatch
  by_contra nonzero
  have grade := homogeneousState sites (Finsupp.mem_support_iff.mpr nonzero)
  have partition := Finset.card_filter_add_card_filter_not
    (s := sites) (fun site : ℕ => site % 2 = 1)
  have complement : sites.filter (fun site => ¬ site % 2 = 1) =
      sites.filter (fun site => site % 2 = 0) := by
    ext site
    have alternatives : site % 2 = 0 ∨ site % 2 = 1 := by omega
    rcases alternatives with even | odd
    · simp [even]
    · simp [odd]
  rw [complement] at partition
  dsimp [degree] at grade
  have parity : subsetParity sites = 1 % 2 := by
    dsimp [subsetParity]
    omega
  exact mismatch parity

private theorem conj_b0 (state : GhostFock) :
    conjCoeffs (b 0 state) = b 0 (conjCoeffs state) := by
  classical
  ext sites
  change star (annihilate 3 state sites) = annihilate 3 (conjCoeffs state) sites
  rw [annihilate_coeff, annihilate_coeff]
  split_ifs <;> simp [conjCoeffs, sign]

private theorem conj_c0 (state : GhostFock) :
    conjCoeffs (c 0 state) = c 0 (conjCoeffs state) := by
  classical
  ext sites
  change star (create 3 state sites) = create 3 (conjCoeffs state) sites
  rw [create_coeff, create_coeff]
  split_ifs <;> simp [conjCoeffs, sign]

private theorem conj_homogeneous (grade : ℤ) (state : GhostFock)
    (homogeneousState : HomogeneousDegree grade state) :
    HomogeneousDegree grade (conjCoeffs state) := by
  intro sites member
  apply homogeneousState sites
  apply Finsupp.mem_support_iff.mpr
  intro zero
  exact (Finsupp.mem_support_iff.mp member) (by simp [conjCoeffs, zero])

def relativeOneConjugation : RelativeDegreeOne →ₛₗ[starRingEnd ℂ] RelativeDegreeOne where
  toFun state := ⟨conjCoeffs state, by
    constructor
    · change b 0 (conjCoeffs (state : GhostFock)) = 0
      rw [← conj_b0]
      have member : b 0 (state : GhostFock) = 0 := state.property.1
      simp [member, conjCoeffs]
    · exact conj_homogeneous 1 state (one_homogeneous state)⟩
  map_add' := by intro first second; apply Subtype.ext; ext sites; simp [conjCoeffs]
  map_smul' := by intro scalar state; apply Subtype.ext; ext sites; simp [conjCoeffs]

def relativeHermitianForm :
    RelativeDegreeOne →ₛₗ[starRingEnd ℂ] (RelativeDegreeOne →ₗ[ℂ] ℂ) :=
  relativeOneForm.comp relativeOneConjugation

theorem relativeHermitianForm_hermitian (first second : RelativeDegreeOne) :
    relativeHermitianForm first second = star (relativeHermitianForm second first) := by
  change Hghost (first : GhostFock) (c 0 (second : GhostFock)) =
    star (Hghost (second : GhostFock) (c 0 (first : GhostFock)))
  rw [Hghost_hermitian]
  congr 1
  rw [Hghost, conj_c0, BPZ_c]
  rw [Pi_homogeneous 1 _ (degree_one_parity _
    (conj_homogeneous 1 second (one_homogeneous second))), BPZ_linear_left]
  norm_num [Hghost]

theorem relativeOneForm_radicals :
    LinearMap.ker relativeOneForm = ⊥ ∧ LinearMap.ker relativeOneForm.flip = ⊥ := by
  have leftZero (state : RelativeDegreeOne)
      (vanishing : ∀ other : RelativeDegreeOne, relativeOneForm state other = 0) : state = 0 := by
    have restricted : (⟨(state : GhostFock), state.property.1⟩ : Relative) = 0 := by
      apply relative_left_zero
      intro other
      have projected := vanishing ⟨degreePart 1 other,
        degreePart_relative 1 other, degreePart_homogeneous 1 other⟩
      change BPZ (state : GhostFock) (c 0 (degreePart 1 other)) = 0 at projected
      rw [relative_one_projection ⟨(state : GhostFock), state.property.1⟩
        (one_homogeneous state) other] at projected
      exact projected
    apply Subtype.ext
    exact congrArg (fun vector : Relative => (vector : GhostFock)) restricted
  constructor
  · apply le_antisymm
    · intro state member
      have vanishing : ∀ other : RelativeDegreeOne, relativeOneForm state other = 0 := by
        intro other
        exact LinearMap.congr_fun member other
      simpa using leftZero state vanishing
    · exact bot_le
  · apply le_antisymm
    · intro state member
      have conjugateZero : relativeOneConjugation state = 0 := by
        apply leftZero
        intro other
        change relativeHermitianForm state other = 0
        rw [relativeHermitianForm_hermitian]
        have rightZero := LinearMap.congr_fun member (relativeOneConjugation other)
        change relativeHermitianForm other state = 0 at rightZero
        simp [rightZero]
      have stateZero : state = 0 := by
        apply Subtype.ext
        ext sites
        have coefficient := congrArg
          (fun vector : RelativeDegreeOne => (vector : GhostFock) sites) conjugateZero
        change star ((state : GhostFock) sites) = 0 at coefficient
        exact star_eq_zero.mp coefficient
      simpa using stateZero
    · exact bot_le

#print axioms relative_isotropic
#print axioms relativeForm_radicals
#print axioms relativeForm_degree_selection
#print axioms relativeOneForm_radicals
#print axioms relativeHermitianForm_hermitian

end
end D5.S3.VertexAlgebra.BcGhostRelativeForm
