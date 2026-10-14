/- GID: D5/S3/VertexAlgebra/BcGhostRotatedForm
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/BcGhostRotatedForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Energy-rotated ordered ghost pairing and actual opposite-mode transposes.
-/

import D5.S3.VertexAlgebra.BcGhostEnergyRotation
import D5.S3.VertexAlgebra.BcGhostBpZForm
import D5.S3.VertexAlgebra.BcGhostRelativeForm

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.BcGhostRotatedForm

open BcGhostFockSupport BcGhostLZeroSpectrum BcGhostEnergyRotation BcGhostBpZForm
open scoped BigOperators

noncomputable section

abbrev GhostFock := BcGhostBpZForm.GhostFock

theorem energy_chi (sites : Finset ℕ) : energy (chi sites) = energy sites := by
  have identity := BPZ_stress 0 (basis sites) (basis (chi sites))
  simp only [basis, L_zero_single, neg_zero, zpow_zero, one_mul] at identity
  change BPZ ((energy sites : ℂ) • basis sites) (basis (chi sites)) =
    BPZ (basis sites) ((energy (chi sites) : ℂ) • basis (chi sites)) at identity
  rw [BPZ_linear_left, BPZ_linear_right, BPZ_kernel, if_pos rfl] at identity
  have equality := mul_right_cancel₀ (eps_nonzero sites) identity
  exact_mod_cast equality.symm

theorem rotation_transpose (left right : GhostFock) :
    BPZ (rotation left) right = BPZ left (rotation right) := by
  induction left using Finsupp.induction_linear with
  | zero => simp [BPZ]
  | add first second firstProof secondProof =>
    simp only [map_add, BPZ_add_left, firstProof, secondProof]
  | single sites scalar =>
    have singleBasis : Finsupp.single sites scalar = scalar • basis sites := by
      simp [basis]
    rw [singleBasis, map_smul, BPZ_linear_left, BPZ_linear_left]
    congr 1
    rw [show rotation (basis sites) = phase sites • basis sites by
      simp [basis, rotation_single]]
    rw [BPZ_linear_left, BPZ_basis, BPZ_basis, rotation_coefficient]
    simp only [phase, energy_chi]
    ring

theorem rotation_conjugation (state : GhostFock) :
    rotation (conjCoeffs state) = conjCoeffs (rotation state) := by
  ext sites
  simp only [rotation_coefficient, conjCoeffs, Finsupp.mapRange_apply]
  simp [phase, phase_conj]

theorem rotation_normalPair (first second : ℤ) (state : GhostFock) :
    rotation (normalPair first second state) =
      (-1 : ℂ) ^ (first + second) • normalPair first second (rotation state) := by
  have passB (mode : ℤ) (vector : GhostFock) :
      rotation (b mode vector) = (-1 : ℂ) ^ mode • b mode (rotation vector) := by
    exact congrArg (fun operator : Module.End ℂ GhostFock => operator vector) (rotation_b mode)
  have passC (mode : ℤ) (vector : GhostFock) :
      rotation (c mode vector) = (-1 : ℂ) ^ mode • c mode (rotation vector) := by
    exact congrArg (fun operator : Module.End ℂ GhostFock => operator vector) (rotation_c mode)
  by_cases creator : first ≤ -2
  · simp only [normalPair, if_pos creator, LinearMap.comp_apply, passB, passC,
      map_smul, smul_smul, phase_add]
  · simp only [normalPair, if_neg creator, LinearMap.neg_apply, LinearMap.comp_apply,
      map_neg, passC, passB, map_smul, smul_smul, phase_add, smul_neg]
    rw [mul_comm]

theorem rotation_stress (mode : ℤ) (state : GhostFock) :
    rotation (L mode state) = (-1 : ℂ) ^ mode • L mode (rotation state) := by
  let radius := max (cutoff mode state) (cutoff mode (rotation state))
  have leftBound : cutoff mode state ≤ radius := le_max_left _ _
  have rightBound : cutoff mode (rotation state) ≤ radius := le_max_right _ _
  rw [L_interval_sum mode state (-radius) radius (by omega) leftBound,
    L_interval_sum mode (rotation state) (-radius) radius (by omega) rightBound,
    map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro index member
  rw [map_smul, rotation_normalPair, show mode + index + -index = mode by omega]
  simp only [smul_smul]
  rw [mul_comm]

def Gplus (left right : GhostFock) : ℂ := BPZ left (rotation right)

def HplusForm : GhostFock →ₗ⋆[ℂ] GhostFock →ₗ[ℂ] ℂ where
  toFun left := (bpzForm (conjCoeffs left)).comp rotation
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro right
    simp [conjCoeffs, BPZ, Finsupp.mapRange_add]
  map_smul' := by
    intro scalar state
    apply LinearMap.ext
    intro right
    change BPZ (conjCoeffs (scalar • state)) (rotation right) =
      star scalar * BPZ (conjCoeffs state) (rotation right)
    have conjugation : conjCoeffs (scalar • state) = star scalar • conjCoeffs state := by
      ext sites
      simp [conjCoeffs]
    rw [conjugation, BPZ_linear_left]

def Hplus (left right : GhostFock) : ℂ := HplusForm left right

theorem rotation_support (state : GhostFock) : (rotation state).support = state.support := by
  classical
  ext sites
  simp only [Finsupp.mem_support_iff, rotation_coefficient, ne_eq, mul_eq_zero]
  have nonzero : phase sites ≠ 0 := zpow_ne_zero _ (by norm_num)
  simp [nonzero]

private theorem rotation_degree (grade : ℤ) (state : GhostFock)
    (homogeneousState : HomogeneousDegree grade state) :
    HomogeneousDegree grade (rotation state) := by
  intro sites member
  exact homogeneousState sites (rotation_support state ▸ member)

private theorem conjugation_degree (grade : ℤ) (state : GhostFock)
    (homogeneousState : HomogeneousDegree grade state) :
    HomogeneousDegree grade (conjCoeffs state) := by
  intro sites member
  apply homogeneousState sites
  apply Finsupp.mem_support_iff.mpr
  intro zero
  have nonzero := Finsupp.mem_support_iff.mp member
  exact nonzero (by simp [conjCoeffs, zero])

theorem Hplus_degree_selection (leftGrade rightGrade : ℤ) (left right : GhostFock)
    (leftHomogeneous : HomogeneousDegree leftGrade left)
    (rightHomogeneous : HomogeneousDegree rightGrade right)
    (mismatch : leftGrade + rightGrade ≠ 3) : Hplus left right = 0 := by
  exact BPZ_degree_selection leftGrade rightGrade (conjCoeffs left) (rotation right)
    (conjugation_degree leftGrade left leftHomogeneous)
    (rotation_degree rightGrade right rightHomogeneous) mismatch

theorem Hplus_c0_degree_selection (leftGrade rightGrade : ℤ) (left right : GhostFock)
    (leftHomogeneous : HomogeneousDegree leftGrade left)
    (rightHomogeneous : HomogeneousDegree rightGrade right)
    (mismatch : leftGrade + rightGrade ≠ 2) : Hplus left (c 0 right) = 0 := by
  exact Hplus_degree_selection leftGrade (rightGrade + 1) left (c 0 right)
    leftHomogeneous (BcGhostRelativeForm.c0_degree rightGrade right rightHomogeneous) (by omega)

theorem Hplus_j_k : Hplus j k = -1 := by
  change BPZ (conjCoeffs j) (rotation k) = -1
  rw [show conjCoeffs j = basis {1} by simp [j, conjCoeffs, basis]]
  have rotated : rotation k = basis {1, 3} := by
    change rotation (-basis {1, 3}) = basis {1, 3}
    rw [map_neg, show rotation (basis {1, 3}) = phase {1, 3} • basis {1, 3} by
      simp only [basis, rotation_single]]
    norm_num [phase, BcGhostLZeroSpectrum.energy, BcGhostLZeroSpectrum.siteWeight]
  rw [rotated, BPZ_raw]
  norm_num [bpz, basis, Finsupp.linearCombination_single, rawBasisOperator,
    BcGhostSuperStateField.basisWord_singleton, reverseSign, reversedWord, bpzSite,
    c, topCoeff, topSites, create, createBasis, sign,
    Finsupp.single_apply, show (2 : ℤ).toNat = 2 from rfl,
    Finset.filter_insert, Finset.filter_singleton,
    show (-1 + 1 : ℤ).toNat = 0 from rfl,
    show (1 - (-1) : ℤ).toNat = 2 from rfl]
  decide

private def conjugation : GhostFock →ₗ⋆[ℂ] GhostFock where
  toFun := conjCoeffs
  map_add' := by intro first second; ext sites; simp [conjCoeffs]
  map_smul' := by intro scalar state; ext sites; simp [conjCoeffs]

private theorem conjugation_create (site : ℕ) (state : GhostFock) :
    conjCoeffs (create site state) = create site (conjCoeffs state) := by
  ext sites
  simp only [conjCoeffs, Finsupp.mapRange_apply, create_coeff]
  split <;> simp [sign]

private theorem conjugation_annihilate (site : ℕ) (state : GhostFock) :
    conjCoeffs (annihilate site state) = annihilate site (conjCoeffs state) := by
  ext sites
  simp only [conjCoeffs, Finsupp.mapRange_apply, annihilate_coeff]
  split <;> simp [sign]

theorem conjugation_b (mode : ℤ) (state : GhostFock) :
    conjCoeffs (b mode state) = b mode (conjCoeffs state) := by
  by_cases creator : mode ≤ -2
  · simpa only [b, if_pos creator] using
      conjugation_create (2 * (-mode - 2).toNat) state
  · simpa only [b, if_neg creator] using
      conjugation_annihilate (2 * (mode + 1).toNat + 1) state

private theorem conjugation_c (mode : ℤ) (state : GhostFock) :
    conjCoeffs (c mode state) = c mode (conjCoeffs state) := by
  by_cases creator : mode ≤ 1
  · simpa only [c, if_pos creator] using
      conjugation_create (2 * (1 - mode).toNat + 1) state
  · simpa only [c, if_neg creator] using
      conjugation_annihilate (2 * (mode - 2).toNat) state

theorem conjugation_Pi (state : GhostFock) :
    conjCoeffs (Pi state) = Pi (conjCoeffs state) := by
  ext sites
  simp [conjCoeffs, Pi_coeff]

private theorem conjugation_normalPair (first second : ℤ) (state : GhostFock) :
    conjCoeffs (normalPair first second state) =
      normalPair first second (conjCoeffs state) := by
  have negative (vector : GhostFock) : conjCoeffs (-vector) = -conjCoeffs vector := by
    exact map_neg conjugation vector
  unfold normalPair
  split <;> simp only [LinearMap.comp_apply, LinearMap.neg_apply, negative,
    conjugation_b, conjugation_c]

private theorem conjugation_stress (mode : ℤ) (state : GhostFock) :
    conjCoeffs (L mode state) = L mode (conjCoeffs state) := by
  let radius := max (cutoff mode state) (cutoff mode (conjCoeffs state))
  have leftBound : cutoff mode state ≤ radius := le_max_left _ _
  have rightBound : cutoff mode (conjCoeffs state) ≤ radius := le_max_right _ _
  change conjugation (L mode state) = L mode (conjCoeffs state)
  rw [L_interval_sum mode state (-radius) radius (by omega) leftBound,
    L_interval_sum mode (conjCoeffs state) (-radius) radius (by omega) rightBound, map_sum]
  apply Finset.sum_congr rfl
  intro index member
  rw [LinearMap.map_smulₛₗ]
  change star (mode - index : ℂ) • conjCoeffs (normalPair (mode + index) (-index) state) = _
  rw [conjugation_normalPair]
  simp

theorem Gplus_c (mode : ℤ) (left right : GhostFock) :
    Gplus (c mode left) right = -Gplus (Pi left) (c (-mode) right) := by
  unfold Gplus
  rw [BPZ_c]
  have pass := congrArg (fun operator : Module.End ℂ GhostFock => operator right)
    (rotation_c (-mode))
  change rotation (c (-mode) right) = (-1 : ℂ) ^ (-mode) • c (-mode) (rotation right) at pass
  rw [pass, BPZ_linear_right, phase_neg, zpow_sub₀ (by norm_num)]
  simp [div_eq_mul_inv]

theorem Gplus_stress (mode : ℤ) (left right : GhostFock) :
    Gplus (L mode left) right = Gplus left (L (-mode) right) := by
  unfold Gplus
  rw [BPZ_stress, rotation_stress, BPZ_linear_right, phase_neg]

theorem Hplus_hermitian (left right : GhostFock) :
    Hplus left right = star (Hplus right left) := by
  change Hghost left (rotation right) = star (Hghost right (rotation left))
  rw [Hghost_hermitian]
  congr 1
  change BPZ (conjCoeffs (rotation right)) left = BPZ (conjCoeffs right) (rotation left)
  rw [← rotation_conjugation, rotation_transpose]

theorem Hplus_c (mode : ℤ) (left right : GhostFock) :
    Hplus (c mode left) right = -Hplus (Pi left) (c (-mode) right) := by
  change Gplus (conjCoeffs (c mode left)) right =
    -Gplus (conjCoeffs (Pi left)) (c (-mode) right)
  rw [conjugation_c, conjugation_Pi, Gplus_c]

theorem Hplus_stress (mode : ℤ) (left right : GhostFock) :
    Hplus (L mode left) right = Hplus left (L (-mode) right) := by
  change Gplus (conjCoeffs (L mode left)) right =
    Gplus (conjCoeffs left) (L (-mode) right)
  rw [conjugation_stress, Gplus_stress]

private theorem Pi_normalPair (first second : ℤ) (state : GhostFock) :
    Pi (normalPair first second state) = normalPair first second (Pi state) := by
  by_cases creator : first ≤ -2
  · simp only [normalPair, if_pos creator, LinearMap.comp_apply,
      Pi_b, Pi_c, map_neg, neg_neg]
  · simp only [normalPair, if_neg creator, LinearMap.comp_apply, LinearMap.neg_apply,
      Pi_b, Pi_c, map_neg, neg_neg]

theorem Pi_stress (mode : ℤ) (state : GhostFock) :
    Pi (L mode state) = L mode (Pi state) := by
  let radius := max (cutoff mode state) (cutoff mode (Pi state))
  have leftBound : cutoff mode state ≤ radius := le_max_left _ _
  have rightBound : cutoff mode (Pi state) ≤ radius := le_max_right _ _
  rw [L_interval_sum mode state (-radius) radius (by omega) leftBound,
    L_interval_sum mode (Pi state) (-radius) radius (by omega) rightBound, map_sum]
  apply Finset.sum_congr rfl
  intro index member
  rw [map_smul, Pi_normalPair]

#print axioms rotation_support
#print axioms Hplus_degree_selection
#print axioms Hplus_c0_degree_selection
#print axioms Hplus_j_k

end
end D5.S3.VertexAlgebra.BcGhostRotatedForm
