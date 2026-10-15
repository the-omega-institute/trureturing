import D5.S3.VertexAlgebra.TemporaryBcGhostSuperGenerators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.BcGhostSuperStateField

open BcGhostFockSupport BcGhostSuperGenerators
open FieldNormalProduct SuperFieldProducts
open scoped VertexOperator

noncomputable section

theorem identity_modes (mode : ℤ) :
    ((identityField : VertexOperator ℂ Carrier)[[mode]]) =
      if mode = -1 then LinearMap.id else 0 := by
  rw [identityField, VertexOperator.ncoeff_of_coeff]
  simp only [show -mode - 1 = 0 ↔ mode = -1 by omega]

theorem identity_translation (mode : ℤ) :
    translation * ((identityField : VertexOperator ℂ Carrier)[[mode]]) -
      ((identityField : VertexOperator ℂ Carrier)[[mode]]) * translation =
        -(mode : ℂ) • ((identityField : VertexOperator ℂ Carrier)[[mode - 1]]) := by
  rw [identity_modes, identity_modes]
  by_cases distinguished : mode = -1
  · subst mode
    simp [← Module.End.one_eq_id]
  · by_cases zeroMode : mode = 0
    · subst mode
      simp
    · simp [distinguished, show mode - 1 ≠ -1 by omega]

theorem normal_right_identity (operator : VertexOperator ℂ Carrier) :
    normal 1 operator identityField = operator := by
  apply HVertexOperator.coeff_inj
  funext power
  apply LinearMap.ext
  intro vector
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff, normal_modes, one_smul]
  let mode : ℤ := -power - 1
  change (∑ᶠ offset : ℕ, (operator[[-(offset : ℤ) - 1]])
      (((identityField : VertexOperator ℂ Carrier)[[mode + offset]]) vector)) +
    (∑ᶠ offset : ℕ, ((identityField : VertexOperator ℂ Carrier)[[mode - offset - 1]])
      ((operator[[offset]]) vector)) = (operator[[mode]]) vector
  by_cases nonnegative : 0 ≤ mode
  · have firstZero (offset : ℕ) : (operator[[-(offset : ℤ) - 1]])
        (((identityField : VertexOperator ℂ Carrier)[[mode + offset]]) vector) = 0 := by
      simp [identity_modes, show mode + offset ≠ -1 by omega]
    simp only [firstZero, finsum_zero, zero_add]
    rw [finsum_eq_single _ mode.toNat]
    · simp [identity_modes, Int.toNat_of_nonneg nonnegative]
    · intro offset different
      simp [identity_modes, show mode - (offset : ℤ) - 1 ≠ -1 by omega]
  · have secondZero (offset : ℕ) :
        ((identityField : VertexOperator ℂ Carrier)[[mode - offset - 1]])
          ((operator[[offset]]) vector) = 0 := by
      simp [identity_modes, show mode - offset - 1 ≠ -1 by omega]
    simp only [secondZero, finsum_zero, add_zero]
    rw [finsum_eq_single _ (-mode - 1).toNat]
    · rw [identity_modes, Int.toNat_of_nonneg (by omega : 0 ≤ -mode - 1), if_pos (by omega)]
      simp only [LinearMap.id_apply]
      rw [show -(-mode - 1) - 1 = mode by omega]
    · intro offset different
      simp [identity_modes, show mode + (offset : ℤ) ≠ -1 by omega]

theorem finsum_mem (space : Submodule ℂ Carrier) (terms : ℕ → Carrier)
    (finite : Function.HasFiniteSupport terms) (member : ∀ offset, terms offset ∈ space) :
    (∑ᶠ offset : ℕ, terms offset) ∈ space := by
  classical
  rw [finsum_eq_sum_of_support_subset _ (s := finite.toFinset) (by
    intro offset inSupport
    exact finite.mem_toFinset.mpr inSupport)]
  exact space.sum_mem (fun offset _ => member offset)

theorem residue_mem (leftParity rightParity : ℕ) (exchange : ℂ) (parameter mode : ℤ)
    (left right : VertexOperator ℂ Carrier)
    (leftHomogeneous : ∀ index : ℤ, HomogeneousOperator leftParity ((left[[index]])))
    (rightHomogeneous : ∀ index : ℤ, HomogeneousOperator rightParity ((right[[index]]))) :
    HomogeneousOperator (leftParity + rightParity)
      (((residue exchange parameter left right)[[mode]])) := by
  intro inputParity vector vectorHomogeneous
  rw [residue_modes]
  change residueLeft parameter mode left right vector -
    (epsilon parameter * exchange) • residueRight parameter mode left right vector ∈
      homogeneous (leftParity + rightParity + inputParity)
  apply (homogeneous (leftParity + rightParity + inputParity)).sub_mem
  · apply finsum_mem _ _ (residue_left_finite parameter mode left right vector)
    intro offset
    apply (homogeneous (leftParity + rightParity + inputParity)).smul_mem
    have inner := rightHomogeneous (mode + offset) inputParity vector vectorHomogeneous
    have outer := leftHomogeneous (parameter - offset) (rightParity + inputParity)
      ((right[[mode + offset]]) vector) inner
    simpa only [Nat.add_assoc] using outer
  · apply (homogeneous (leftParity + rightParity + inputParity)).smul_mem
    apply finsum_mem _ _ (residue_right_finite parameter mode left right vector)
    intro offset
    apply (homogeneous (leftParity + rightParity + inputParity)).smul_mem
    have inner := leftHomogeneous offset inputParity vector vectorHomogeneous
    have outer := rightHomogeneous (parameter + mode - offset) (leftParity + inputParity)
      ((left[[offset]]) vector) inner
    have grade : rightParity + (leftParity + inputParity) =
        leftParity + rightParity + inputParity := by omega
    simpa only [grade] using outer

def wordField : List ℕ → VertexOperator ℂ Carrier
  | [] => identityField
  | site :: tail => normal ((-1 : ℂ) ^ tail.length) (siteField site) (wordField tail)

def wordVector : List ℕ → Carrier
  | [] => vacuum
  | site :: tail => create site (wordVector tail)

theorem word_creation (word : List ℕ) :
    ((wordField word)[[-1]]) (vacuum : Carrier) = wordVector word ∧
      ∀ mode : ℤ, 0 ≤ mode → ((wordField word)[[mode]]) (vacuum : Carrier) = 0 := by
  induction word with
  | nil =>
    constructor
    · simp [wordField, wordVector, identity_modes]
    · intro mode nonnegative
      simp [wordField, identity_modes, show mode ≠ -1 by omega]
  | cons site tail inductionHypothesis =>
    have law := residue_vacuum ((-1 : ℂ) ^ tail.length) (-1)
      (siteField site) (wordField tail) (vacuum : Carrier)
      (site_creative site) inductionHypothesis.2
    constructor
    · change ((residue ((-1 : ℂ) ^ tail.length) (-1) (siteField site)
        (wordField tail))[[-1]]) (vacuum : Carrier) = create site (wordVector tail)
      rw [law.1, site_creation_mode, inductionHypothesis.1]
    · exact law.2

def basisWord (sites : Finset ℕ) : List ℕ :=
  if empty : sites = ∅ then [] else
    let head := sites.min' (Finset.nonempty_iff_ne_empty.mpr empty)
    head :: basisWord (sites.erase head)
termination_by sites.card
decreasing_by
  simp_wf
  have member := Finset.min'_mem sites (Finset.nonempty_iff_ne_empty.mpr empty)
  have positive : 0 < sites.card := Finset.card_pos.mpr ⟨_, member⟩
  rw [Finset.card_erase_of_mem member]
  omega

theorem basisWord_length (sites : Finset ℕ) : (basisWord sites).length = sites.card := by
  classical
  by_cases empty : sites = ∅
  · simp [basisWord, empty]
  · let head := sites.min' (Finset.nonempty_iff_ne_empty.mpr empty)
    have member : head ∈ sites := Finset.min'_mem _ _
    have positive : 0 < sites.card := Finset.card_pos.mpr ⟨head, member⟩
    rw [basisWord, dif_neg empty, List.length_cons, basisWord_length (sites.erase head),
      Finset.card_erase_of_mem member]
    omega
termination_by sites.card
decreasing_by
  simp_wf
  have member := Finset.min'_mem sites (Finset.nonempty_iff_ne_empty.mpr empty)
  have positive : 0 < sites.card := Finset.card_pos.mpr ⟨_, member⟩
  rw [Finset.card_erase_of_mem member]
  omega

theorem basisWord_mem (sites : Finset ℕ) (site : ℕ) : site ∈ basisWord sites ↔ site ∈ sites := by
  classical
  by_cases empty : sites = ∅
  · simp [basisWord, empty]
  · let head := sites.min' (Finset.nonempty_iff_ne_empty.mpr empty)
    have headMember : head ∈ sites := Finset.min'_mem _ _
    rw [basisWord, dif_neg empty, List.mem_cons, basisWord_mem (sites.erase head), Finset.mem_erase]
    constructor
    · rintro (equality | ⟨different, member⟩)
      · simpa only [equality] using headMember
      · exact member
    · intro member
      by_cases same : site = head
      · exact Or.inl same
      · exact Or.inr ⟨same, member⟩
termination_by sites.card
decreasing_by
  simp_wf
  have member := Finset.min'_mem sites (Finset.nonempty_iff_ne_empty.mpr empty)
  have positive : 0 < sites.card := Finset.card_pos.mpr ⟨_, member⟩
  rw [Finset.card_erase_of_mem member]
  omega

theorem basisWord_increasing (sites : Finset ℕ) : List.Pairwise (· < ·) (basisWord sites) := by
  classical
  by_cases empty : sites = ∅
  · simp [basisWord, empty]
  · let head := sites.min' (Finset.nonempty_iff_ne_empty.mpr empty)
    have headMember : head ∈ sites := Finset.min'_mem _ _
    rw [basisWord, dif_neg empty, List.pairwise_cons]
    refine ⟨?_, basisWord_increasing (sites.erase head)⟩
    intro site member
    have erased := Finset.mem_erase.mp ((basisWord_mem (sites.erase head) site).mp member)
    have least : head ≤ site := Finset.min'_le _ site erased.2
    omega
termination_by sites.card
decreasing_by
  simp_wf
  have member := Finset.min'_mem sites (Finset.nonempty_iff_ne_empty.mpr empty)
  have positive : 0 < sites.card := Finset.card_pos.mpr ⟨_, member⟩
  rw [Finset.card_erase_of_mem member]
  omega

theorem basisWord_singleton (site : ℕ) : basisWord {site} = [site] := by
  classical
  simp [basisWord]

theorem wordVector_basis (sites : Finset ℕ) : wordVector (basisWord sites) = Finsupp.single sites 1 := by
  classical
  by_cases empty : sites = ∅
  · simp [basisWord, empty, wordVector, vacuum]
  · let head := sites.min' (Finset.nonempty_iff_ne_empty.mpr empty)
    have member : head ∈ sites := Finset.min'_mem _ _
    have absent : head ∉ sites.erase head := Finset.notMem_erase _ _
    have emptyFilter : (sites.erase head).filter (fun site => site < head) = ∅ := by
      apply Finset.filter_false_of_mem
      intro site siteMember
      exact not_lt.mpr (Finset.min'_le sites site (Finset.mem_of_mem_erase siteMember))
    have signOne : sign (K := ℂ) head (sites.erase head) = 1 := by simp [sign, emptyFilter]
    rw [basisWord, dif_neg empty, wordVector, wordVector_basis (sites.erase head)]
    change create head (Finsupp.single (sites.erase head) 1) = Finsupp.single sites 1
    rw [create, Finsupp.linearCombination_single, one_smul, createBasis, if_neg absent,
      signOne, Finset.insert_erase member]
termination_by sites.card
decreasing_by
  simp_wf
  have member := Finset.min'_mem sites (Finset.nonempty_iff_ne_empty.mpr empty)
  have positive : 0 < sites.card := Finset.card_pos.mpr ⟨_, member⟩
  rw [Finset.card_erase_of_mem member]
  omega

theorem word_translation (word : List ℕ) (mode : ℤ) :
    translation * ((wordField word)[[mode]]) - ((wordField word)[[mode]]) * translation =
      -(mode : ℂ) • ((wordField word)[[mode - 1]]) := by
  induction word generalizing mode with
  | nil => exact identity_translation mode
  | cons site tail inductionHypothesis =>
    exact residue_translation ((-1 : ℂ) ^ tail.length) (-1) translation
      (siteField site) (wordField tail) (site_translation site) inductionHypothesis mode

theorem word_mem (word : List ℕ) (mode : ℤ) :
    HomogeneousOperator word.length (((wordField word)[[mode]])) := by
  induction word generalizing mode with
  | nil =>
    intro inputParity vector vectorHomogeneous
    rw [wordField, identity_modes]
    split
    · simpa using vectorHomogeneous
    · exact (homogeneous (0 + inputParity)).zero_mem
  | cons site tail inductionHypothesis =>
    have law := residue_mem 1 tail.length ((-1 : ℂ) ^ tail.length) (-1) mode
      (siteField site) (wordField tail) (site_mem site) inductionHypothesis
    simpa only [List.length_cons, Nat.add_comm 1 tail.length, wordField, normal] using law

def Y : Carrier →ₗ[ℂ] VertexOperator ℂ Carrier :=
  Finsupp.linearCombination ℂ (fun sites => wordField (basisWord sites))

theorem Y_single (sites : Finset ℕ) (scalar : ℂ) :
    Y (Finsupp.single sites scalar) = scalar • wordField (basisWord sites) := by
  simp [Y, Finsupp.linearCombination_single]

theorem stateField_expansion (vector : Carrier) :
    Y vector = ∑ sites ∈ vector.support, vector sites • wordField (basisWord sites) := by
  rw [Y, Finsupp.linearCombination_apply, Finsupp.sum]

theorem stateField_creation (vector : Carrier) : ((Y vector)[[-1]]) (vacuum : Carrier) = vector := by
  induction vector using Finsupp.induction_linear with
  | zero => simp
  | add first second firstLaw secondLaw => simp [firstLaw, secondLaw]
  | single sites scalar =>
    rw [Y_single]
    simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply,
      (word_creation (basisWord sites)).1, wordVector_basis, Finsupp.smul_single,
      smul_eq_mul, mul_one]

theorem stateField_creativity (vector : Carrier) (mode : ℤ) (nonnegative : 0 ≤ mode) :
    ((Y vector)[[mode]]) (vacuum : Carrier) = 0 := by
  induction vector using Finsupp.induction_linear with
  | zero => simp
  | add first second firstLaw secondLaw => simp [firstLaw, secondLaw]
  | single sites scalar =>
    rw [Y_single]
    simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply,
      (word_creation (basisWord sites)).2 mode nonnegative, smul_zero]

theorem stateField_vacuum : Y (vacuum : Carrier) = identityField := by
  rw [vacuum, Y_single]
  simp [wordField, basisWord]

def covarianceDefect (mode : ℤ) : VertexOperator ℂ Carrier →ₗ[ℂ] Module.End ℂ Carrier where
  toFun operator := translation * (operator[[mode]]) - (operator[[mode]]) * translation +
    (mode : ℂ) • (operator[[mode - 1]])
  map_add' left right := by
    simp only [map_add, Pi.add_apply, mul_add, add_mul, smul_add]
    abel
  map_smul' scalar operator := by
    simp only [map_smul, RingHom.id_apply, Pi.smul_apply, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, smul_add, smul_comm (mode : ℂ) scalar]
    rw [smul_sub scalar (translation * (operator[[mode]])) ((operator[[mode]]) * translation)]

theorem stateField_covariance (vector : Carrier) (mode : ℤ) :
    translation * ((Y vector)[[mode]]) - ((Y vector)[[mode]]) * translation =
      -(mode : ℂ) • ((Y vector)[[mode - 1]]) := by
  have defectZero : covarianceDefect mode (Y vector) = 0 := by
    rw [stateField_expansion, map_sum]
    apply Finset.sum_eq_zero
    intro sites member
    rw [map_smul]
    have wordZero : covarianceDefect mode (wordField (basisWord sites)) = 0 := by
      change (translation * ((wordField (basisWord sites))[[mode]]) -
        ((wordField (basisWord sites))[[mode]]) * translation) +
          (mode : ℂ) • ((wordField (basisWord sites))[[mode - 1]]) = 0
      rw [word_translation, neg_smul, neg_add_cancel]
    rw [wordZero, smul_zero]
  change (translation * ((Y vector)[[mode]]) - ((Y vector)[[mode]]) * translation) +
    (mode : ℂ) • ((Y vector)[[mode - 1]]) = 0 at defectZero
  exact (eq_neg_of_add_eq_zero_left defectZero).trans (neg_smul _ _).symm

theorem stateField_lower_truncation (state vector : Carrier) :
    ∃ cutoff : ℤ, ∀ mode : ℤ, cutoff ≤ mode → ((Y state)[[mode]]) vector = 0 := by
  refine ⟨-((HahnModule.of ℂ).symm (Y state vector)).order, ?_⟩
  intro mode high
  apply VertexOperator.ncoeff_eq_zero_of_lt_order
  omega

theorem stateField_translation_as_mode (state : Carrier) :
    translation state = ((Y state)[[-2]]) (vacuum : Carrier) := by
  have law := congrArg (fun operator : Module.End ℂ Carrier => operator (vacuum : Carrier))
    (stateField_covariance state (-1))
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, stateField_creation,
    translation_vacuum, map_zero, sub_zero, Int.cast_neg, Int.cast_one, neg_neg,
    one_smul, show (-1 : ℤ) - 1 = -2 by norm_num] using law

theorem stateField_mem (parity : ℕ) (state : Carrier) (stateHomogeneous : state ∈ homogeneous parity)
    (mode : ℤ) : HomogeneousOperator parity (((Y state)[[mode]])) := by
  classical
  intro inputParity vector vectorHomogeneous
  rw [stateField_expansion, map_sum]
  simp only [Finset.sum_apply, LinearMap.sum_apply]
  apply (homogeneous (parity + inputParity)).sum_mem
  intro sites member
  simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply]
  apply (homogeneous (parity + inputParity)).smul_mem
  have basisGrade := support_parity parity state stateHomogeneous sites member
  have result := word_mem (basisWord sites) mode inputParity vector vectorHomogeneous
  have sortedLength : (basisWord sites).length = sites.card := basisWord_length sites
  rw [sortedLength] at result
  intro support mismatch
  apply result support
  dsimp [subsetParity] at basisGrade mismatch ⊢
  omega

theorem stateField_parity_decomposition (state : Carrier) :
    Y state = Y (parityPart 0 state) + Y (parityPart 1 state) ∧
      parityPart 0 state ∈ homogeneous 0 ∧ parityPart 1 state ∈ homogeneous 1 := by
  refine ⟨?_, parityPart_mem 0 state, parityPart_mem 1 state⟩
  rw [← map_add, parity_decomposition]

def mixedSuperCommutator (left right : Carrier) : ℤ → ℤ → Module.End ℂ Carrier :=
  ∑ leftParity ∈ Finset.range 2, ∑ rightParity ∈ Finset.range 2,
    superCommutator (koszul leftParity rightParity)
      (Y (parityPart leftParity left)) (Y (parityPart rightParity right))

theorem derivative_zero (operator : VertexOperator ℂ Carrier) :
    dividedDerivative 0 operator = operator := by
  apply VertexOperator.ext
  intro vector
  simp [dividedDerivative]

theorem stateField_b_generator :
    Y (b (-2) (vacuum : Carrier)) = currentField .b := by
  have state : b (-2) (vacuum : Carrier) = Finsupp.single {0} 1 := by
    simpa only [currentField_modes, currentMode,
      show (-1 : ℤ) - 1 = -2 by norm_num] using current_creation_b
  rw [state, Y_single]
  simp only [one_smul, basisWord_singleton, wordField, List.length_nil, pow_zero]
  rw [normal_right_identity]
  simp [siteField, kindAt, derivative_zero]

theorem stateField_c_generator :
    Y (c 1 (vacuum : Carrier)) = currentField .c := by
  have state : c 1 (vacuum : Carrier) = Finsupp.single {1} 1 := by
    simpa only [currentField_modes, currentMode,
      show (-1 : ℤ) + 2 = 1 by norm_num] using current_creation_c
  rw [state, Y_single]
  simp only [one_smul, basisWord_singleton, wordField, List.length_nil, pow_zero]
  rw [normal_right_identity]
  simp [siteField, kindAt, derivative_zero]

end
end D5.S3.VertexAlgebra.BcGhostSuperStateField
