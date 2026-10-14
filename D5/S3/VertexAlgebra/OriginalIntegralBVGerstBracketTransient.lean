import D5.S3.VertexAlgebra.OriginalIntegralB0CompatibilityTransient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.TensorConformal.OriginalIntegralBVGerstBracketTransient

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open LatticeBcGhostBrstCharge (State Q B)
open LatticeBcGhostNeutralCohomology (OriginalCycles OriginalBoundaries OriginalCohomology)
open OriginalTopologicalApplications
open OriginalBrstReassembly
open OriginalIntegralB0CompatibilityTransient
open LatticeBcGhostCohomologyModes
open LatticeBcGhostTensorStateField
open BcGhostFockSupport BcGhostSuperGenerators
open BcGhostSuperStateField
open FieldNormalProduct SuperFieldProducts
open VertexOperatorTensorProduct
open scoped TensorProduct VertexOperator

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
  (critical : D.rank = 26)

abbrev delta : Module.End ℂ (OriginalCohomology D H) :=
  originalB0 D H leftInverse rightInverse critical

abbrev productMinusOne : OriginalCohomology D H →ₗ[ℂ]
    OriginalCohomology D H →ₗ[ℂ] OriginalCohomology D H :=
  product D H (-1)

def quotientDefectValue (grade : ℕ) (left right : OriginalCohomology D H) :
    OriginalCohomology D H :=
  quotientDefect D H leftInverse rightInverse critical grade left right

def mixedBracketValue (left right : OriginalCohomology D H) :
    OriginalCohomology D H :=
  quotientDefectValue D H leftInverse rightInverse critical 0
      (parity D H 0 left) right -
    quotientDefectValue D H leftInverse rightInverse critical 1
      (parity D H 1 left) right

theorem quotientDefectValue_add_left (grade : ℕ)
    (first second right : OriginalCohomology D H) :
    quotientDefectValue D H leftInverse rightInverse critical grade (first + second) right =
      quotientDefectValue D H leftInverse rightInverse critical grade first right +
        quotientDefectValue D H leftInverse rightInverse critical grade second right := by
  simp only [quotientDefectValue, quotientDefect, map_add, LinearMap.add_apply,
    smul_add]
  abel

theorem quotientDefectValue_add_right (grade : ℕ)
    (left first second : OriginalCohomology D H) :
    quotientDefectValue D H leftInverse rightInverse critical grade left (first + second) =
      quotientDefectValue D H leftInverse rightInverse critical grade left first +
        quotientDefectValue D H leftInverse rightInverse critical grade left second := by
  simp only [quotientDefectValue, quotientDefect, map_add, LinearMap.add_apply,
    smul_add]
  abel

theorem quotientDefectValue_smul_left (grade : ℕ) (scalar : ℂ)
    (left right : OriginalCohomology D H) :
    quotientDefectValue D H leftInverse rightInverse critical grade (scalar • left) right =
      scalar • quotientDefectValue D H leftInverse rightInverse critical grade left right := by
  simp only [quotientDefectValue, quotientDefect, map_smul, LinearMap.smul_apply,
    smul_smul]
  module

theorem quotientDefectValue_smul_right (grade : ℕ) (scalar : ℂ)
    (left right : OriginalCohomology D H) :
    quotientDefectValue D H leftInverse rightInverse critical grade left (scalar • right) =
      scalar • quotientDefectValue D H leftInverse rightInverse critical grade left right := by
  simp only [quotientDefectValue, quotientDefect, map_smul, LinearMap.smul_apply,
    smul_smul]
  module

theorem quotientDefectValue_zero_left (grade : ℕ) (right : OriginalCohomology D H) :
    quotientDefectValue D H leftInverse rightInverse critical grade 0 right = 0 := by
  simp [quotientDefectValue, quotientDefect]

theorem mixedBracketValue_add_left
    (first second right : OriginalCohomology D H) :
    mixedBracketValue D H leftInverse rightInverse critical (first + second) right =
      mixedBracketValue D H leftInverse rightInverse critical first right +
        mixedBracketValue D H leftInverse rightInverse critical second right := by
  simp only [mixedBracketValue, map_add]
  rw [quotientDefectValue_add_left, quotientDefectValue_add_left]
  abel

theorem mixedBracketValue_add_right
    (left first second : OriginalCohomology D H) :
    mixedBracketValue D H leftInverse rightInverse critical left (first + second) =
      mixedBracketValue D H leftInverse rightInverse critical left first +
        mixedBracketValue D H leftInverse rightInverse critical left second := by
  simp only [mixedBracketValue]
  rw [quotientDefectValue_add_right, quotientDefectValue_add_right]
  abel

theorem mixedBracketValue_smul_left (scalar : ℂ)
    (left right : OriginalCohomology D H) :
    mixedBracketValue D H leftInverse rightInverse critical (scalar • left) right =
      scalar • mixedBracketValue D H leftInverse rightInverse critical left right := by
  simp only [mixedBracketValue, map_smul]
  rw [quotientDefectValue_smul_left, quotientDefectValue_smul_left]
  module

theorem mixedBracketValue_smul_right (scalar : ℂ)
    (left right : OriginalCohomology D H) :
    mixedBracketValue D H leftInverse rightInverse critical left (scalar • right) =
      scalar • mixedBracketValue D H leftInverse rightInverse critical left right := by
  simp only [mixedBracketValue]
  rw [quotientDefectValue_smul_right, quotientDefectValue_smul_right]
  module

def mixedBracket : OriginalCohomology D H →ₗ[ℂ]
    OriginalCohomology D H →ₗ[ℂ] OriginalCohomology D H :=
  LinearMap.mk₂ ℂ (mixedBracketValue D H leftInverse rightInverse critical)
    (fun first second third => mixedBracketValue_add_left D H leftInverse rightInverse critical
      first second third)
    (fun scalar first second => mixedBracketValue_smul_left D H leftInverse rightInverse critical
      scalar first second)
    (fun first second third => mixedBracketValue_add_right D H leftInverse rightInverse critical
      first second third)
    (fun scalar first second => mixedBracketValue_smul_right D H leftInverse rightInverse critical
      scalar first second)

theorem mixedBracket_apply (left right : OriginalCohomology D H) :
    mixedBracket D H leftInverse rightInverse critical left right =
      mixedBracketValue D H leftInverse rightInverse critical left right := rfl

theorem parity_periodic (first second : ℕ) (same : first % 2 = second % 2) :
    (parity D H first : Module.End ℂ (OriginalCohomology D H)) = parity D H second := by
  apply LinearMap.ext
  intro state
  refine Quotient.inductionOn state ?_
  intro representative
  change (OriginalBoundaries D H).mkQ (cycleParity D H first representative) =
    (OriginalBoundaries D H).mkQ (cycleParity D H second representative)
  congr 1
  apply Subtype.ext
  change parityPart first representative.val = parityPart second representative.val
  exact LinearMap.congr_fun
    (LatticeBcGhostCohomologyModes.parityPart_periodic D first second same)
    representative.val

theorem quotientDefectValue_grade_periodic (first second : ℕ)
    (left right : OriginalCohomology D H) (same : first % 2 = second % 2) :
    quotientDefectValue D H leftInverse rightInverse critical first left right =
      quotientDefectValue D H leftInverse rightInverse critical second left right := by
  unfold quotientDefectValue quotientDefect
  rw [SuperFieldProducts.koszul_eq_of_mod 1 first 1 second rfl same]

theorem mixedBracket_homogeneous (leftParity rightParity : ℕ)
    (left right : OriginalCohomology D H)
    (leftFixed : parity D H leftParity left = left) :
    mixedBracket D H leftInverse rightInverse critical left right =
      ((-1 : ℂ) ^ leftParity) •
        quotientDefectValue D H leftInverse rightInverse critical leftParity left right := by
  have leftParityBound : leftParity % 2 = 0 ∨ leftParity % 2 = 1 := by omega
  rcases leftParityBound with leftEven | leftOdd
  · have leftZero : parity D H 0 left = left := by
      have period := LinearMap.congr_fun (parity_periodic D H leftParity 0
        (by omega)) left
      exact period.symm.trans leftFixed
    have leftOne : parity D H 1 left = 0 := by
      have decomposition := parity_decomposition D H left
      rw [leftZero] at decomposition
      have equality : left + parity D H 1 left = left + 0 := by simpa using decomposition
      exact add_left_cancel equality
    have defectGrade := quotientDefectValue_grade_periodic D H leftInverse rightInverse critical
      0 leftParity left right (by omega)
    change quotientDefectValue D H leftInverse rightInverse critical 0
        (parity D H 0 left) right -
      quotientDefectValue D H leftInverse rightInverse critical 1
        (parity D H 1 left) right = _
    rw [leftZero, leftOne, quotientDefectValue_zero_left]
    simp only [sub_zero]
    rw [SuperFieldProducts.sign_power_mod leftParity, leftEven, pow_zero, one_smul]
    exact defectGrade
  · have leftOne : parity D H 1 left = left := by
      have period := LinearMap.congr_fun (parity_periodic D H 1 leftParity
        (by omega)) left
      exact period.trans leftFixed
    have leftZero : parity D H 0 left = 0 := by
      have decomposition := parity_decomposition D H left
      rw [leftOne] at decomposition
      have equality : parity D H 0 left + left = 0 + left := by simpa using decomposition
      exact add_right_cancel equality
    have defectGrade := quotientDefectValue_grade_periodic D H leftInverse rightInverse critical
      1 leftParity left right (by omega)
    change quotientDefectValue D H leftInverse rightInverse critical 0
        (parity D H 0 left) right -
      quotientDefectValue D H leftInverse rightInverse critical 1
        (parity D H 1 left) right = _
    rw [leftZero, leftOne, quotientDefectValue_zero_left]
    simp only [zero_sub]
    rw [SuperFieldProducts.sign_power_mod leftParity, leftOdd]
    simp only [pow_one, neg_one_smul]
    rw [defectGrade]

include leftInverse rightInverse critical in
theorem product_homogeneous (leftParity rightParity : ℕ)
    (left right : OriginalCohomology D H)
    (leftFixed : parity D H leftParity left = left)
    (rightFixed : parity D H rightParity right = right) :
    parity D H (leftParity + rightParity)
        (product D H (-1) left right) = product D H (-1) left right := by
  obtain ⟨leftRepresentative, leftMember, rfl⟩ :=
    zero_homogeneous_representative D H leftInverse rightInverse critical
      leftParity left leftFixed
  obtain ⟨rightRepresentative, rightMember, rfl⟩ :=
    zero_homogeneous_representative D H leftInverse rightInverse critical
      rightParity right rightFixed
  simp only [originalClass]
  rw [product_mk, parity_mk]
  apply congrArg (OriginalBoundaries D H).mkQ
  apply Subtype.ext
  exact (LatticeBcGhostTensorStateField.homogeneous_fixed
    (leftParity + rightParity) _).mp
    (LatticeBcGhostTensorStateField.stateField_mem leftParity rightParity
      leftRepresentative.val rightRepresentative.val leftMember rightMember (-1))

def literalCycleJ : Module.End ℂ (OriginalCycles D H) :=
  ((nativeJ D).comp (OriginalCycles D H).subtype).codRestrict
    (OriginalCycles D H) (fun state => nativeJ_cycle D H state.val state.property)

theorem literalCycleJ_boundary (state : OriginalCycles D H)
    (boundary : state ∈ OriginalBoundaries D H) :
    literalCycleJ D H state ∈ OriginalBoundaries D H := by
  obtain ⟨preimage, equality⟩ := boundary
  refine ⟨nativeJ D preimage + preimage, ?_⟩
  change Q D H (nativeJ D preimage + preimage) = nativeJ D state.val
  rw [← nativeJ_Q, equality]
  rfl

def literalCohomologyJ : Module.End ℂ (OriginalCohomology D H) :=
  (OriginalBoundaries D H).mapQ (OriginalBoundaries D H) (literalCycleJ D H)
    (literalCycleJ_boundary D H)

theorem literalCohomologyJ_mk (state : OriginalCycles D H) :
    literalCohomologyJ D H ((OriginalBoundaries D H).mkQ state) =
      (OriginalBoundaries D H).mkQ (literalCycleJ D H state) := rfl

theorem cohomologyJ_eq_originalJTransport :
    literalCohomologyJ D H =
      originalJTransport D H leftInverse rightInverse critical := by
  apply LinearMap.ext
  intro state
  obtain ⟨representative, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective state
  rw [literalCohomologyJ_mk, originalJTransport_mk]
  rfl

namespace AcceptedGhostCovariance

local notation "ghostJ" => (BcGhostNumber.J (K := ℂ))

private theorem J_product_commutator (left right : Module.End ℂ Carrier)
    (leftDegree rightDegree : ℂ)
    (leftLaw : ghostJ * left - left * ghostJ = leftDegree • left)
    (rightLaw : ghostJ * right - right * ghostJ = rightDegree • right) :
    ghostJ * (left * right) - (left * right) * ghostJ =
      (leftDegree + rightDegree) • (left * right) := by
  calc
    _ = (ghostJ * left - left * ghostJ) * right +
        left * (ghostJ * right - right * ghostJ) := by noncomm_ring
    _ = (leftDegree • left) * right + left * (rightDegree • right) := by
      rw [leftLaw, rightLaw]
    _ = (leftDegree + rightDegree) • (left * right) := by
      simp [smul_mul_assoc, mul_smul_comm, add_smul]

private theorem J_residue_commutator (exchange : ℂ) (parameter mode : ℤ) :
    ∀ (left right : VertexOperator ℂ Carrier) (leftDegree rightDegree : ℂ),
      (∀ index : ℤ, ghostJ * (left[[index]]) -
        (left[[index]]) * ghostJ = leftDegree • (left[[index]])) →
      (∀ index : ℤ, ghostJ * (right[[index]]) -
        (right[[index]]) * ghostJ = rightDegree • (right[[index]])) →
      ghostJ * ((residue exchange parameter left right)[[mode]]) -
        ((residue exchange parameter left right)[[mode]]) * ghostJ =
        (leftDegree + rightDegree) • ((residue exchange parameter left right)[[mode]]) := by
  intro left right leftDegree rightDegree leftLaw rightLaw
  have leftCommute (vector : Carrier) :
      ghostJ (residueLeft parameter mode left right vector) -
          residueLeft parameter mode left right (ghostJ vector) =
        (leftDegree + rightDegree) • residueLeft parameter mode left right vector := by
    have firstFinite := residue_left_finite parameter mode left right vector
    have secondFinite := residue_left_finite parameter mode left right (ghostJ vector)
    have imageFinite := firstFinite.fun_comp (map_zero ghostJ)
    have commute := (ghostJ : Module.End ℂ Carrier).toAddMonoidHom.map_finsum firstFinite
    simp only [LinearMap.toAddMonoidHom_coe] at commute
    change ghostJ (∑ᶠ offset : ℕ, weight parameter offset •
        (left[[parameter - (offset : ℤ)]]) ((right[[mode + offset]]) vector)) -
      (∑ᶠ offset : ℕ, weight parameter offset •
        (left[[parameter - (offset : ℤ)]]) ((right[[mode + offset]]) (ghostJ vector))) = _
    rw [commute, ← finsum_sub_distrib imageFinite secondFinite]
    change (∑ᶠ offset : ℕ,
        (ghostJ (weight parameter offset •
            (left[[parameter - (offset : ℤ)]]) ((right[[mode + offset]]) vector)) -
          weight parameter offset • (left[[parameter - (offset : ℤ)]])
            ((right[[mode + offset]]) (ghostJ vector)))) =
      (leftDegree + rightDegree) • (∑ᶠ offset : ℕ, weight parameter offset •
        (left[[parameter - (offset : ℤ)]]) ((right[[mode + offset]]) vector))
    rw [smul_finsum' (leftDegree + rightDegree) firstFinite]
    apply finsum_congr
    intro offset
    rw [map_smul]
    have product := congrArg (fun operator : Module.End ℂ Carrier => operator vector)
      (J_product_commutator (left[[parameter - (offset : ℤ)]])
        (right[[mode + (offset : ℤ)]]) leftDegree rightDegree
        (leftLaw (parameter - (offset : ℤ))) (rightLaw (mode + (offset : ℤ))))
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at product
    rw [← smul_sub, product]
    simp [smul_smul, mul_comm]
  have rightCommute (vector : Carrier) :
      ghostJ (residueRight parameter mode left right vector) -
          residueRight parameter mode left right (ghostJ vector) =
        (leftDegree + rightDegree) • residueRight parameter mode left right vector := by
    have firstFinite := residue_right_finite parameter mode left right vector
    have secondFinite := residue_right_finite parameter mode left right (ghostJ vector)
    have imageFinite := firstFinite.fun_comp (map_zero ghostJ)
    have commute := (ghostJ : Module.End ℂ Carrier).toAddMonoidHom.map_finsum firstFinite
    simp only [LinearMap.toAddMonoidHom_coe] at commute
    change ghostJ (∑ᶠ offset : ℕ, weight parameter offset •
        (right[[parameter + mode - (offset : ℤ)]]) ((left[[offset]]) vector)) -
      (∑ᶠ offset : ℕ, weight parameter offset •
        (right[[parameter + mode - (offset : ℤ)]]) ((left[[offset]]) (ghostJ vector))) = _
    rw [commute, ← finsum_sub_distrib imageFinite secondFinite]
    change (∑ᶠ offset : ℕ,
        (ghostJ (weight parameter offset •
            (right[[parameter + mode - (offset : ℤ)]]) ((left[[offset]]) vector)) -
          weight parameter offset • (right[[parameter + mode - (offset : ℤ)]])
            ((left[[offset]]) (ghostJ vector)))) =
      (leftDegree + rightDegree) • (∑ᶠ offset : ℕ, weight parameter offset •
        (right[[parameter + mode - (offset : ℤ)]]) ((left[[offset]]) vector))
    rw [smul_finsum' (leftDegree + rightDegree) firstFinite]
    apply finsum_congr
    intro offset
    rw [map_smul]
    have product := congrArg (fun operator : Module.End ℂ Carrier => operator vector)
      (J_product_commutator (right[[parameter + mode - (offset : ℤ)]])
        (left[[offset]]) rightDegree leftDegree
        (rightLaw (parameter + mode - (offset : ℤ))) (leftLaw offset))
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at product
    rw [← smul_sub, product, add_comm rightDegree leftDegree]
    simp [smul_smul, mul_comm]
  apply LinearMap.ext
  intro vector
  rw [residue_modes]
  change ghostJ (residueLeft parameter mode left right vector -
        (epsilon parameter * exchange) • residueRight parameter mode left right vector) -
      (residueLeft parameter mode left right (ghostJ vector) -
        (epsilon parameter * exchange) • residueRight parameter mode left right (ghostJ vector)) =
      (leftDegree + rightDegree) • (residueLeft parameter mode left right vector -
        (epsilon parameter * exchange) • residueRight parameter mode left right vector)
  rw [map_sub, map_smul]
  calc
    _ = (ghostJ (residueLeft parameter mode left right vector) -
        residueLeft parameter mode left right (ghostJ vector)) -
        (epsilon parameter * exchange) •
          (ghostJ (residueRight parameter mode left right vector) -
            residueRight parameter mode left right (ghostJ vector)) := by module
    _ = (leftDegree + rightDegree) • residueLeft parameter mode left right vector -
        (epsilon parameter * exchange) •
          ((leftDegree + rightDegree) • residueRight parameter mode left right vector) := by
      rw [leftCommute, rightCommute]
    _ = _ := by module

private def siteGhostDegree (site : ℕ) : ℤ :=
  if site % 2 = 1 then 1 else -1

private def wordGhostDegree : List ℕ → ℤ
  | [] => 0
  | site :: tail => siteGhostDegree site + wordGhostDegree tail

private theorem J_identity_commutator (mode : ℤ) :
    ghostJ * ((identityField : VertexOperator ℂ Carrier)[[mode]]) -
      ((identityField : VertexOperator ℂ Carrier)[[mode]]) * ghostJ = 0 := by
  rw [identity_modes]
  by_cases distinguished : mode = -1
  · subst mode
    simp [← Module.End.one_eq_id]
  · simp [distinguished]

private theorem J_site_commutator (site : ℕ) (mode : ℤ) :
    ghostJ * ((siteField site)[[mode]]) -
      ((siteField site)[[mode]]) * ghostJ =
        (siteGhostDegree site : ℂ) • ((siteField site)[[mode]]) := by
  rw [siteField, derivative_modes, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, ← smul_sub]
  by_cases even : site % 2 = 0
  · have law := BcGhostNumber.J_b_commutator (K := ℂ)
      (mode - (site / 2 : ℕ) - 1)
    simp only [currentField_modes, kindAt, if_pos even, currentMode]
    rw [law]
    simp [siteGhostDegree, even]
  · have odd : site % 2 = 1 := by omega
    have law := BcGhostNumber.J_c_commutator (K := ℂ)
      (mode - (site / 2 : ℕ) + 2)
    simp only [currentField_modes, kindAt, if_neg even, currentMode]
    rw [law]
    simp [siteGhostDegree, odd]

private theorem J_word_commutator (word : List ℕ) (mode : ℤ) :
    ghostJ * ((wordField word)[[mode]]) -
      ((wordField word)[[mode]]) * ghostJ =
        (wordGhostDegree word : ℂ) • ((wordField word)[[mode]]) := by
  induction word generalizing mode with
  | nil =>
      simpa [wordField, wordGhostDegree] using J_identity_commutator mode
  | cons site tail inductionHypothesis =>
      have law := J_residue_commutator ((-1 : ℂ) ^ tail.length) (-1) mode
        (siteField site) (wordField tail) (siteGhostDegree site : ℂ)
        (wordGhostDegree tail : ℂ) (J_site_commutator site) inductionHypothesis
      simpa [wordField, wordGhostDegree, normal] using law

private theorem basisWord_ghostDegree (sites : Finset ℕ) :
    wordGhostDegree (basisWord sites) = BcGhostNumber.degree sites := by
  classical
  by_cases empty : sites = ∅
  · simp [basisWord, wordGhostDegree, BcGhostNumber.degree, empty]
  · let head := sites.min' (Finset.nonempty_iff_ne_empty.mpr empty)
    have member : head ∈ sites := Finset.min'_mem _ _
    have absent : head ∉ sites.erase head := Finset.notMem_erase _ _
    rw [basisWord, dif_neg empty, wordGhostDegree, basisWord_ghostDegree]
    have inserted : BcGhostNumber.degree (insert head (sites.erase head)) =
        BcGhostNumber.degree (sites.erase head) + siteGhostDegree head := by
      by_cases odd : head % 2 = 1
      · have even : head % 2 ≠ 0 := by omega
        simp [BcGhostNumber.degree, siteGhostDegree, Finset.filter_insert, odd, even, absent]
          <;> omega
      · have even : head % 2 = 0 := by omega
        simp [BcGhostNumber.degree, siteGhostDegree, Finset.filter_insert, odd, even, absent]
          <;> omega
    rw [Finset.insert_erase member] at inserted
    dsimp [head] at inserted
    omega
termination_by sites.card
decreasing_by
  simp_wf
  have member := Finset.min'_mem sites (Finset.nonempty_iff_ne_empty.mpr empty)
  have positive : 0 < sites.card := Finset.card_pos.mpr ⟨_, member⟩
  rw [Finset.card_erase_of_mem member]
  omega

private theorem J_stateField_commutator (state : Carrier) (mode : ℤ) :
    ghostJ * ((Y state)[[mode]]) - ((Y state)[[mode]]) * ghostJ =
      ((Y (ghostJ state))[[mode]]) := by
  induction state using Finsupp.induction_linear with
  | zero => simp
  | add first second firstLaw secondLaw =>
      have ghostAdd : ghostJ (first + second) = ghostJ first + ghostJ second :=
        map_add ghostJ first second
      have fieldAdd (left right : Carrier) : Y (left + right) = Y left + Y right :=
        map_add Y left right
      rw [fieldAdd first second, ghostAdd, fieldAdd]
      simp only [VertexOperator.coeff_eq_ncoeff, map_add, Pi.add_apply,
        LinearMap.add_apply, mul_add, add_mul]
      calc
        _ = (ghostJ * ((Y first)[[mode]]) - ((Y first)[[mode]]) * ghostJ) +
            (ghostJ * ((Y second)[[mode]]) - ((Y second)[[mode]]) * ghostJ) := by abel
        _ = _ := by rw [firstLaw, secondLaw]
  | single sites scalar =>
      have jsingle : ghostJ (Finsupp.single sites scalar) =
          (BcGhostNumber.degree sites : ℂ) • Finsupp.single sites scalar := by
        simp [BcGhostNumber.J, smul_smul, Finsupp.smul_single, mul_comm]
      rw [Y_single, jsingle]
      have yscaled := map_smul Y (BcGhostNumber.degree sites : ℂ)
        (Finsupp.single sites scalar)
      rw [yscaled, Y_single]
      simp only [VertexOperator.coeff_eq_ncoeff, map_smul, Pi.smul_apply,
        LinearMap.smul_apply]
      have law := J_word_commutator (basisWord sites) mode
      rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← smul_sub, law,
        basisWord_ghostDegree]
      simp [smul_smul, mul_comm]

theorem stateField_ghostNumber_covariance (state input : Carrier) (mode : ℤ) :
    ghostJ (((Y state)[[mode]]) input) =
      ((Y (ghostJ state))[[mode]]) input + ((Y state)[[mode]]) (ghostJ input) := by
  apply sub_eq_iff_eq_add.mp
  have law := congrArg (fun operator : Module.End ℂ Carrier => operator input)
    (J_stateField_commutator state mode)
  simpa only [LinearMap.sub_apply, Module.End.mul_apply] using law

private theorem stateField_ghostNumber_covariance_tmul
    (D : LatticeData) (matterState matterInput : Carrier D)
    (ghostState ghostInput : Fock ℂ) (mode : ℤ) :
    LatticeBcGhostBrstGhostNumber.J D
        (((stateField D (matterState ⊗ₜ[ℂ] ghostState))[[mode]])
          (matterInput ⊗ₜ[ℂ] ghostInput)) =
      ((stateField D (LatticeBcGhostBrstGhostNumber.J D
        (matterState ⊗ₜ[ℂ] ghostState))[[mode]])
          (matterInput ⊗ₜ[ℂ] ghostInput)) +
        ((stateField D (matterState ⊗ₜ[ℂ] ghostState))[[mode]])
          (LatticeBcGhostBrstGhostNumber.J D
            (matterInput ⊗ₜ[ℂ] ghostInput)) := by
  have baseFinite := diagonal_finite (LatticeAllStateField.Y D matterState)
    (BcGhostSuperStateField.Y ghostState) mode matterInput ghostInput
  have stateFinite := diagonal_finite (LatticeAllStateField.Y D matterState)
    (BcGhostSuperStateField.Y (BcGhostNumber.J ghostState)) mode matterInput ghostInput
  have inputFinite := diagonal_finite (LatticeAllStateField.Y D matterState)
    (BcGhostSuperStateField.Y ghostState) mode matterInput (BcGhostNumber.J ghostInput)
  have baseFinite' : Function.HasFiniteSupport (fun index : ℤ =>
      ((LatticeAllStateField.Y D matterState)[[index]]) matterInput ⊗ₜ[ℂ]
        ((BcGhostSuperStateField.Y ghostState)[[mode - 1 - index]]) ghostInput) := by
    exact baseFinite
  have stateFinite' : Function.HasFiniteSupport (fun index : ℤ =>
      ((LatticeAllStateField.Y D matterState)[[index]]) matterInput ⊗ₜ[ℂ]
        ((BcGhostSuperStateField.Y (BcGhostNumber.J ghostState))[[mode - 1 - index]])
          ghostInput) := by
    exact stateFinite
  have inputFinite' : Function.HasFiniteSupport (fun index : ℤ =>
      ((LatticeAllStateField.Y D matterState)[[index]]) matterInput ⊗ₜ[ℂ]
        ((BcGhostSuperStateField.Y ghostState)[[mode - 1 - index]])
          (BcGhostNumber.J ghostInput)) := by
    exact inputFinite
  simp only [LatticeBcGhostBrstGhostNumber.J, TensorProduct.map_tmul,
    LinearMap.id_apply]
  rw [LatticeBcGhostTensorStateField.stateField_mode_tmul,
    LatticeBcGhostTensorStateField.stateField_mode_tmul,
    LatticeBcGhostTensorStateField.stateField_mode_tmul]
  have numberSum := (TensorProduct.map (LinearMap.id : Module.End ℂ (Carrier D))
      BcGhostNumber.J).toAddMonoidHom.map_finsum baseFinite'
  simp only [LinearMap.toAddMonoidHom_coe] at numberSum
  rw [numberSum, ← finsum_add_distrib stateFinite' inputFinite']
  apply finsum_congr
  intro index
  have ghostLaw := stateField_ghostNumber_covariance ghostState ghostInput
    (mode - 1 - index)
  simp only [LatticeBcGhostBrstGhostNumber.J, TensorProduct.map_tmul,
    LinearMap.id_apply]
  rw [ghostLaw, TensorProduct.tmul_add]

theorem stateField_ghostNumber_covariance_state
    (D : LatticeData) (state input : LatticeBcGhostBrstCharge.State D) (mode : ℤ) :
    LatticeBcGhostBrstGhostNumber.J D (((stateField D state)[[mode]]) input) =
      ((stateField D (LatticeBcGhostBrstGhostNumber.J D state))[[mode]]) input +
        ((stateField D state)[[mode]])
          (LatticeBcGhostBrstGhostNumber.J D input) := by
  induction state using TensorProduct.induction_on with
  | zero => simp
  | tmul matterState ghostState =>
      induction input using TensorProduct.induction_on with
      | zero => simp
      | tmul matterInput ghostInput =>
          exact stateField_ghostNumber_covariance_tmul D matterState matterInput
            ghostState ghostInput mode
      | add first second firstLaw secondLaw =>
          simp only [map_add, Pi.add_apply, LinearMap.add_apply]
          rw [firstLaw, secondLaw]
          abel
  | add first second firstLaw secondLaw =>
      simp only [map_add, Pi.add_apply, LinearMap.add_apply]
      rw [firstLaw, secondLaw]
      abel

end AcceptedGhostCovariance

theorem literalCohomologyJ_product_covariance (mode : ℤ)
    (left right : OriginalCohomology D H) :
    literalCohomologyJ D H (product D H mode left right) =
      product D H mode (literalCohomologyJ D H left) right +
        product D H mode left (literalCohomologyJ D H right) := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn right ?_
  intro right
  change literalCohomologyJ D H
      (product D H mode ((OriginalBoundaries D H).mkQ left)
        ((OriginalBoundaries D H).mkQ right)) =
    product D H mode (literalCohomologyJ D H ((OriginalBoundaries D H).mkQ left))
      ((OriginalBoundaries D H).mkQ right) +
      product D H mode ((OriginalBoundaries D H).mkQ left)
        (literalCohomologyJ D H ((OriginalBoundaries D H).mkQ right))
  rw [product_mk D H mode left right, literalCohomologyJ_mk D H left,
    product_mk D H mode (literalCycleJ D H left) right,
    literalCohomologyJ_mk D H right,
    product_mk D H mode left (literalCycleJ D H right)]
  rw [← map_add]
  refine congrArg (OriginalBoundaries D H).mkQ ?_
  apply Subtype.ext
  change nativeJ D (((stateField D left.val)[[mode]]) right.val) =
    ((stateField D (nativeJ D left.val))[[mode]]) right.val +
      ((stateField D left.val)[[mode]]) (nativeJ D right.val)
  exact AcceptedGhostCovariance.stateField_ghostNumber_covariance_state D
    left.val right.val mode

theorem original_product_integer_degree (mode leftDegree rightDegree : ℤ)
    (left right : OriginalCohomology D H)
    (leftHomogeneous : originalJTransport D H leftInverse rightInverse critical left =
      (leftDegree : ℂ) • left)
    (rightHomogeneous : originalJTransport D H leftInverse rightInverse critical right =
      (rightDegree : ℂ) • right) :
    originalJTransport D H leftInverse rightInverse critical
        (product D H mode left right) =
      ((leftDegree + rightDegree : ℤ) : ℂ) • product D H mode left right := by
  have leftLiteral : literalCohomologyJ D H left = (leftDegree : ℂ) • left := by
    rw [cohomologyJ_eq_originalJTransport D H leftInverse rightInverse critical]
    exact leftHomogeneous
  have rightLiteral : literalCohomologyJ D H right = (rightDegree : ℂ) • right := by
    rw [cohomologyJ_eq_originalJTransport D H leftInverse rightInverse critical]
    exact rightHomogeneous
  rw [← cohomologyJ_eq_originalJTransport D H leftInverse rightInverse critical,
    literalCohomologyJ_product_covariance, leftLiteral, rightLiteral]
  simp only [map_smul, LinearMap.smul_apply, smul_add, Int.cast_add, add_smul]

theorem original_parity_fixed_of_integer (degree : ℤ)
    (state : OriginalCohomology D H)
    (homogeneous : originalJTransport D H leftInverse rightInverse critical state =
      (degree : ℂ) • state) :
    parity D H (degree % 2).toNat state = state := by
  obtain ⟨representative, member, equation⟩ :=
    original_integer_zero_representative D H leftInverse rightInverse critical degree state
      homogeneous
  rw [← equation]
  change parity D H (degree % 2).toNat
      ((OriginalBoundaries D H).mkQ ⟨representative.val, representative.property.2⟩) = _
  rw [parity_mk]
  apply congrArg (OriginalBoundaries D H).mkQ
  apply Subtype.ext
  exact ghostPart_original_parity D degree representative.val member

theorem quotientDefectValue_integer_degree (parityGrade : ℕ)
    (leftDegree rightDegree : ℤ) (left right : OriginalCohomology D H)
    (leftHomogeneous : originalJTransport D H leftInverse rightInverse critical left =
      (leftDegree : ℂ) • left)
    (rightHomogeneous : originalJTransport D H leftInverse rightInverse critical right =
      (rightDegree : ℂ) • right) :
    originalJTransport D H leftInverse rightInverse critical
        (quotientDefectValue D H leftInverse rightInverse critical parityGrade left right) =
      ((leftDegree + rightDegree - 1 : ℤ) : ℂ) •
        quotientDefectValue D H leftInverse rightInverse critical parityGrade left right := by
  have leftB0Homogeneous := originalB0_integer_degree D H leftInverse rightInverse critical
    leftDegree left leftHomogeneous
  have rightB0Homogeneous := originalB0_integer_degree D H leftInverse rightInverse critical
    rightDegree right rightHomogeneous
  have productHomogeneous := original_product_integer_degree D H leftInverse rightInverse critical
    (-1) leftDegree rightDegree left right leftHomogeneous rightHomogeneous
  have firstHomogeneous := originalB0_integer_degree D H leftInverse rightInverse critical
    (leftDegree + rightDegree) (product D H (-1) left right) productHomogeneous
  have secondHomogeneous := original_product_integer_degree D H leftInverse rightInverse critical
    (-1) (leftDegree - 1) rightDegree
      (originalB0 D H leftInverse rightInverse critical left) right
      leftB0Homogeneous rightHomogeneous
  have thirdHomogeneous := original_product_integer_degree D H leftInverse rightInverse critical
    (-1) leftDegree (rightDegree - 1) left
      (originalB0 D H leftInverse rightInverse critical right)
      leftHomogeneous rightB0Homogeneous
  unfold quotientDefectValue quotientDefect
  simp only [map_sub, map_smul, smul_sub, smul_smul, LinearMap.smul_apply,
    Int.cast_add, Int.cast_sub, Int.cast_one, add_smul, sub_smul]
  rw [firstHomogeneous, secondHomogeneous, thirdHomogeneous]
  module

theorem mixedBracket_integer_degree (leftDegree rightDegree : ℤ)
    (left right : OriginalCohomology D H)
    (leftHomogeneous : originalJTransport D H leftInverse rightInverse critical left =
      (leftDegree : ℂ) • left)
    (rightHomogeneous : originalJTransport D H leftInverse rightInverse critical right =
      (rightDegree : ℂ) • right) :
    originalJTransport D H leftInverse rightInverse critical
        (mixedBracket D H leftInverse rightInverse critical left right) =
      ((leftDegree + rightDegree - 1 : ℤ) : ℂ) •
        mixedBracket D H leftInverse rightInverse critical left right := by
  have leftParity := original_parity_fixed_of_integer D H leftInverse rightInverse critical
    leftDegree left leftHomogeneous
  have rightParity := original_parity_fixed_of_integer D H leftInverse rightInverse critical
    rightDegree right rightHomogeneous
  rw [mixedBracket_homogeneous D H leftInverse rightInverse critical
      (leftDegree % 2).toNat (rightDegree % 2).toNat left right leftParity,
    map_smul]
  rw [quotientDefectValue_integer_degree D H leftInverse rightInverse critical
    (leftDegree % 2).toNat leftDegree rightDegree left right leftHomogeneous rightHomogeneous]
  module


include leftInverse rightInverse critical in
theorem quotientDefectValue_homogeneous (leftParity rightParity : ℕ)
    (left right : OriginalCohomology D H)
    (leftFixed : parity D H leftParity left = left)
    (rightFixed : parity D H rightParity right = right) :
    parity D H (leftParity + rightParity + 1)
        (quotientDefectValue D H leftInverse rightInverse critical leftParity left right) =
      quotientDefectValue D H leftInverse rightInverse critical leftParity left right := by
  have productFixed := product_homogeneous D H leftInverse rightInverse critical
    leftParity rightParity left right leftFixed rightFixed
  have leftB0Fixed := originalB0_odd D H leftInverse rightInverse critical leftParity left
    leftFixed
  have rightB0Fixed := originalB0_odd D H leftInverse rightInverse critical rightParity right
    rightFixed
  have firstFixed := originalB0_odd D H leftInverse rightInverse critical
    (leftParity + rightParity) (product D H (-1) left right) productFixed
  have secondFixed := product_homogeneous D H leftInverse rightInverse critical
    (leftParity + 1) rightParity
    (originalB0 D H leftInverse rightInverse critical left) right leftB0Fixed rightFixed
  have thirdFixed := product_homogeneous D H leftInverse rightInverse critical
    leftParity (rightParity + 1) left
    (originalB0 D H leftInverse rightInverse critical right) leftFixed rightB0Fixed
  have secondFixed' :
      parity D H (leftParity + rightParity + 1)
          (product D H (-1)
            (originalB0 D H leftInverse rightInverse critical left) right) =
        product D H (-1)
          (originalB0 D H leftInverse rightInverse critical left) right := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using secondFixed
  have thirdFixed' :
      parity D H (leftParity + rightParity + 1)
          (product D H (-1) left
            (originalB0 D H leftInverse rightInverse critical right)) =
        product D H (-1) left
          (originalB0 D H leftInverse rightInverse critical right) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using thirdFixed
  unfold quotientDefectValue quotientDefect
  simp only [map_sub, map_smul, smul_sub, smul_smul]
  rw [firstFixed, secondFixed', thirdFixed']

include leftInverse rightInverse critical in
theorem mixedBracket_homogeneous_fixed (leftParity rightParity : ℕ)
    (left right : OriginalCohomology D H)
    (leftFixed : parity D H leftParity left = left)
    (rightFixed : parity D H rightParity right = right) :
    parity D H (leftParity + rightParity + 1)
        (mixedBracket D H leftInverse rightInverse critical left right) =
      mixedBracket D H leftInverse rightInverse critical left right := by
  rw [mixedBracket_homogeneous D H leftInverse rightInverse critical
    leftParity rightParity left right leftFixed, map_smul,
    quotientDefectValue_homogeneous D H leftInverse rightInverse critical
      leftParity rightParity left right leftFixed rightFixed]

private theorem skew_sign_delta (leftParity rightParity : ℕ) :
    ((-1 : ℂ) ^ leftParity) =
      -SuperFieldProducts.koszul (leftParity + 1) (rightParity + 1) *
        ((-1 : ℂ) ^ rightParity) * SuperFieldProducts.koszul leftParity rightParity := by
  symm
  simp only [SuperFieldProducts.koszul]
  have exponent :
      (leftParity + 1) * (rightParity + 1) + rightParity + leftParity * rightParity =
        leftParity + 1 + 2 * (leftParity * rightParity + rightParity) := by ring
  calc
    -((-1 : ℂ) ^ ((leftParity + 1) * (rightParity + 1))) *
        ((-1 : ℂ) ^ rightParity) * (-1 : ℂ) ^ (leftParity * rightParity) =
        -(((-1 : ℂ) ^ ((leftParity + 1) * (rightParity + 1))) *
          ((-1 : ℂ) ^ rightParity) * (-1 : ℂ) ^ (leftParity * rightParity)) := by ring
    _ = -(((-1 : ℂ) ^ ((leftParity + 1) * (rightParity + 1) + rightParity)) *
          (-1 : ℂ) ^ (leftParity * rightParity)) := by rw [← pow_add]
    _ = -((-1 : ℂ) ^ ((leftParity + 1) * (rightParity + 1) + rightParity +
          leftParity * rightParity)) := by rw [← pow_add]
    _ = (-1 : ℂ) ^ leftParity := by
      rw [exponent, pow_add, pow_mul, pow_succ]
      norm_num

private theorem skew_sign_left (leftParity rightParity : ℕ) :
    (-1 : ℂ) =
      SuperFieldProducts.koszul (leftParity + 1) (rightParity + 1) *
        ((-1 : ℂ) ^ rightParity) *
          SuperFieldProducts.koszul leftParity (rightParity + 1) := by
  symm
  simp only [SuperFieldProducts.koszul]
  have exponent :
      (leftParity + 1) * (rightParity + 1) + rightParity +
        leftParity * (rightParity + 1) =
        1 + 2 * (leftParity * rightParity + leftParity + rightParity) := by ring
  calc
    ((-1 : ℂ) ^ ((leftParity + 1) * (rightParity + 1))) *
        ((-1 : ℂ) ^ rightParity) *
        (-1 : ℂ) ^ (leftParity * (rightParity + 1)) =
        (((-1 : ℂ) ^ ((leftParity + 1) * (rightParity + 1))) *
          ((-1 : ℂ) ^ rightParity)) *
          (-1 : ℂ) ^ (leftParity * (rightParity + 1)) := by ring
    _ = (-1 : ℂ) ^ ((leftParity + 1) * (rightParity + 1) + rightParity) *
        (-1 : ℂ) ^ (leftParity * (rightParity + 1)) := by rw [← pow_add]
    _ = (-1 : ℂ) ^ ((leftParity + 1) * (rightParity + 1) + rightParity +
        leftParity * (rightParity + 1)) := by rw [← pow_add]
    _ = (-1 : ℂ) := by
      rw [exponent, pow_add, pow_mul]
      norm_num

private theorem skew_sign_right (leftParity rightParity : ℕ) :
    -((-1 : ℂ) ^ leftParity) =
      SuperFieldProducts.koszul (leftParity + 1) (rightParity + 1) *
        SuperFieldProducts.koszul rightParity (leftParity + 1) := by
  simp only [SuperFieldProducts.koszul]
  rw [← pow_add]
  have exponent :
      (leftParity + 1) * (rightParity + 1) + rightParity * (leftParity + 1) =
        leftParity + 1 + 2 * (leftParity * rightParity + rightParity) := by ring
  rw [exponent, pow_add, pow_mul, pow_succ]
  norm_num

theorem mixedBracket_shifted_skew_homogeneous (leftParity rightParity : ℕ)
    (left right : OriginalCohomology D H)
    (leftFixed : parity D H leftParity left = left)
    (rightFixed : parity D H rightParity right = right) :
    mixedBracket D H leftInverse rightInverse critical left right =
      -SuperFieldProducts.koszul (leftParity + 1) (rightParity + 1) •
        mixedBracket D H leftInverse rightInverse critical right left := by
  have leftB0Fixed := originalB0_odd D H leftInverse rightInverse critical leftParity left
    leftFixed
  have rightB0Fixed := originalB0_odd D H leftInverse rightInverse critical rightParity right
    rightFixed
  have productBA := product_supercommutative D H leftInverse rightInverse
    rightParity leftParity right left rightFixed leftFixed
  have productB0A := product_supercommutative D H leftInverse rightInverse
    (rightParity + 1) leftParity
    (originalB0 D H leftInverse rightInverse critical right) left rightB0Fixed leftFixed
  have productAB0 := product_supercommutative D H leftInverse rightInverse
    rightParity (leftParity + 1) right
    (originalB0 D H leftInverse rightInverse critical left) rightFixed leftB0Fixed
  rw [mixedBracket_homogeneous D H leftInverse rightInverse critical leftParity rightParity
      left right leftFixed,
    mixedBracket_homogeneous D H leftInverse rightInverse critical rightParity leftParity
      right left rightFixed]
  unfold quotientDefectValue quotientDefect
  rw [productBA, map_smul, productB0A, productAB0]
  have koszulStep :
      SuperFieldProducts.koszul rightParity (leftParity + 1) =
        SuperFieldProducts.koszul rightParity leftParity *
          SuperFieldProducts.koszul rightParity 1 := by
    calc
      SuperFieldProducts.koszul rightParity (leftParity + 1) =
          SuperFieldProducts.koszul (leftParity + 1) rightParity :=
        SuperFieldProducts.koszul_symm rightParity (leftParity + 1)
      _ = SuperFieldProducts.koszul leftParity rightParity *
          SuperFieldProducts.koszul 1 rightParity := by
        rw [← SuperFieldProducts.koszul_add_left leftParity 1 rightParity]
      _ = SuperFieldProducts.koszul rightParity leftParity *
          SuperFieldProducts.koszul rightParity 1 := by
        rw [SuperFieldProducts.koszul_symm leftParity rightParity,
          SuperFieldProducts.koszul_symm 1 rightParity]
  have koszulIdentity :
      SuperFieldProducts.koszul rightParity leftParity =
        SuperFieldProducts.koszul 1 rightParity *
          SuperFieldProducts.koszul rightParity (leftParity + 1) := by
    simp only [SuperFieldProducts.koszul]
    change (-1 : ℂ) ^ (rightParity * leftParity) =
      (-1 : ℂ) ^ (1 * rightParity) *
        (-1 : ℂ) ^ (rightParity * (leftParity + 1))
    rw [Nat.one_mul]
    calc
      (-1 : ℂ) ^ (rightParity * leftParity) =
          (-1 : ℂ) ^ (rightParity * leftParity + 2 * rightParity) := by
        rw [pow_add, pow_mul]
        norm_num
      _ = (-1 : ℂ) ^ (rightParity + rightParity * (leftParity + 1)) := by
        congr 1
        ring
      _ = (-1 : ℂ) ^ rightParity *
          (-1 : ℂ) ^ (rightParity * (leftParity + 1)) := by
        rw [pow_add]
  have scalarIdentity :
      ((-1 : ℂ) ^ leftParity) =
        -(SuperFieldProducts.koszul (leftParity + 1) (rightParity + 1) *
          SuperFieldProducts.koszul rightParity leftParity *
            ((-1 : ℂ) ^ rightParity)) := by
    calc
      (-1 : ℂ) ^ leftParity =
          -SuperFieldProducts.koszul (leftParity + 1) (rightParity + 1) *
            ((-1 : ℂ) ^ rightParity) *
              SuperFieldProducts.koszul leftParity rightParity :=
        skew_sign_delta leftParity rightParity
      _ = -(SuperFieldProducts.koszul (leftParity + 1) (rightParity + 1) *
          SuperFieldProducts.koszul rightParity leftParity *
            ((-1 : ℂ) ^ rightParity)) := by
        rw [SuperFieldProducts.koszul_symm leftParity rightParity]
        ring
  rw [scalarIdentity]
  simp only [smul_smul]
  rw [← koszulIdentity]
  rw [SuperFieldProducts.koszul_add_left rightParity 1 leftParity]
  module

theorem mixedBracket_shifted_skew_decomposition (left right : OriginalCohomology D H) :
    mixedBracket D H leftInverse rightInverse critical left right =
      -SuperFieldProducts.koszul 1 1 •
          mixedBracket D H leftInverse rightInverse critical
            (parity D H 0 right) (parity D H 0 left) -
        SuperFieldProducts.koszul 1 2 •
          mixedBracket D H leftInverse rightInverse critical
            (parity D H 1 right) (parity D H 0 left) -
        SuperFieldProducts.koszul 2 1 •
          mixedBracket D H leftInverse rightInverse critical
            (parity D H 0 right) (parity D H 1 left) -
        SuperFieldProducts.koszul 2 2 •
          mixedBracket D H leftInverse rightInverse critical
            (parity D H 1 right) (parity D H 1 left) := by
  have parityFixed (grade : ℕ) (state : OriginalCohomology D H) :
      parity D H grade (parity D H grade state) = parity D H grade state := by
    refine Quotient.inductionOn state ?_
    intro representative
    change (OriginalBoundaries D H).mkQ
        (cycleParity D H grade (cycleParity D H grade representative)) =
      (OriginalBoundaries D H).mkQ (cycleParity D H grade representative)
    congr 1
    apply Subtype.ext
    exact LatticeBcGhostTensorStateField.parityPart_idempotent grade representative.val
  have leftDecomposition := parity_decomposition D H left
  have rightDecomposition := parity_decomposition D H right
  have leftZeroFixed := parityFixed 0 left
  have leftOneFixed := parityFixed 1 left
  have rightZeroFixed := parityFixed 0 right
  have rightOneFixed := parityFixed 1 right
  have expansion := congrArg₂
    (fun first second => mixedBracket D H leftInverse rightInverse critical first second)
    leftDecomposition rightDecomposition
  simp only [map_add, LinearMap.add_apply] at expansion
  rw [← expansion]
  rw [mixedBracket_shifted_skew_homogeneous D H leftInverse rightInverse critical
      0 0 (parity D H 0 left) (parity D H 0 right) leftZeroFixed rightZeroFixed,
    mixedBracket_shifted_skew_homogeneous D H leftInverse rightInverse critical
      0 1 (parity D H 0 left) (parity D H 1 right) leftZeroFixed rightOneFixed,
    mixedBracket_shifted_skew_homogeneous D H leftInverse rightInverse critical
      1 0 (parity D H 1 left) (parity D H 0 right) leftOneFixed rightZeroFixed,
    mixedBracket_shifted_skew_homogeneous D H leftInverse rightInverse critical
      1 1 (parity D H 1 left) (parity D H 1 right) leftOneFixed rightOneFixed]
  simp [SuperFieldProducts.koszul]
  module

theorem mixedBracket_leibniz_homogeneous (leftParity rightParity : ℕ)
    (left right vector : OriginalCohomology D H)
    (leftFixed : parity D H leftParity left = left)
    (rightFixed : parity D H rightParity right = right) :
    mixedBracket D H leftInverse rightInverse critical left
        (product D H (-1) right vector) =
      product D H (-1)
          (mixedBracket D H leftInverse rightInverse critical left right) vector +
        SuperFieldProducts.koszul (leftParity + 1) rightParity •
          product D H (-1) right
            (mixedBracket D H leftInverse rightInverse critical left vector) := by
  have law := quotient_B0_second_order D H leftInverse rightInverse critical
    leftParity rightParity left right vector leftFixed rightFixed
  rw [mixedBracket_homogeneous D H leftInverse rightInverse critical
      leftParity 0 left (product D H (-1) right vector) leftFixed,
    mixedBracket_homogeneous D H leftInverse rightInverse critical
      leftParity rightParity left right leftFixed,
    mixedBracket_homogeneous D H leftInverse rightInverse critical
      leftParity 0 left vector leftFixed]
  have lawValue :
      quotientDefectValue D H leftInverse rightInverse critical leftParity left
          (product D H (-1) right vector) =
        product D H (-1)
            (quotientDefectValue D H leftInverse rightInverse critical leftParity left right)
            vector +
          SuperFieldProducts.koszul (leftParity + 1) rightParity •
            product D H (-1) right
              (quotientDefectValue D H leftInverse rightInverse critical leftParity left vector) :=
    law
  rw [lawValue]
  simp only [map_add, map_smul, smul_add, smul_smul]
  simp only [LinearMap.smul_apply]
  module

theorem mixedBracket_delta_homogeneous (leftParity rightParity : ℕ)
    (left right : OriginalCohomology D H)
    (leftFixed : parity D H leftParity left = left) :
    originalB0 D H leftInverse rightInverse critical
        (mixedBracket D H leftInverse rightInverse critical left right) =
      mixedBracket D H leftInverse rightInverse critical
          (originalB0 D H leftInverse rightInverse critical left) right +
        ((-1 : ℂ) ^ (leftParity + 1)) •
          mixedBracket D H leftInverse rightInverse critical left
            (originalB0 D H leftInverse rightInverse critical right) := by
  have leftB0Fixed := originalB0_odd D H leftInverse rightInverse critical leftParity left
    leftFixed
  rw [mixedBracket_homogeneous D H leftInverse rightInverse critical
      leftParity rightParity left right leftFixed,
    mixedBracket_homogeneous D H leftInverse rightInverse critical
      (leftParity + 1) rightParity
      (originalB0 D H leftInverse rightInverse critical left) right leftB0Fixed,
    mixedBracket_homogeneous D H leftInverse rightInverse critical
      leftParity (rightParity + 1) left
      (originalB0 D H leftInverse rightInverse critical right) leftFixed]
  unfold quotientDefectValue quotientDefect
  simp only [map_sub, map_smul, originalB0_square, map_zero, LinearMap.zero_apply,
    smul_sub, smul_smul]
  have sign :
      ((-1 : ℂ) ^ leftParity) * SuperFieldProducts.koszul 1 leftParity =
        (-1 : ℂ) ^ (leftParity * 2) := by
    simp only [SuperFieldProducts.koszul]
    rw [← pow_add]
    congr 1
    ring
  have shiftedSign :
      ((-1 : ℂ) ^ (leftParity + 1)) *
          SuperFieldProducts.koszul 1 (leftParity + 1) =
        (-1 : ℂ) ^ ((leftParity + 1) * 2) := by
    simp only [SuperFieldProducts.koszul]
    rw [← pow_add]
    congr 1
    ring
  rw [sign, shiftedSign]
  module

theorem mixedBracket_delta_right_homogeneous (leftParity rightParity : ℕ)
    (left right : OriginalCohomology D H)
    (leftFixed : parity D H leftParity left = left) :
    mixedBracket D H leftInverse rightInverse critical left
        (originalB0 D H leftInverse rightInverse critical right) =
      ((-1 : ℂ) ^ (leftParity + 1)) •
        (originalB0 D H leftInverse rightInverse critical
            (mixedBracket D H leftInverse rightInverse critical left right) -
          mixedBracket D H leftInverse rightInverse critical
            (originalB0 D H leftInverse rightInverse critical left) right) := by
  have law := mixedBracket_delta_homogeneous D H leftInverse rightInverse critical
    leftParity rightParity left right leftFixed
  rw [law]
  simp only [smul_sub, smul_add, smul_smul]
  have shiftedSquare :
      ((-1 : ℂ) ^ (leftParity + 1)) * ((-1 : ℂ) ^ (leftParity + 1)) = 1 := by
    rw [← pow_add]
    have exponent : (leftParity + 1) + (leftParity + 1) = 2 * (leftParity + 1) := by ring
    rw [exponent, pow_mul]
    norm_num
  rw [shiftedSquare]
  module

theorem mixedBracket_jacobi_homogeneous (leftParity rightParity : ℕ)
    (left right vector : OriginalCohomology D H)
    (leftFixed : parity D H leftParity left = left)
    (rightFixed : parity D H rightParity right = right) :
    mixedBracket D H leftInverse rightInverse critical left
        (mixedBracket D H leftInverse rightInverse critical right vector) =
      mixedBracket D H leftInverse rightInverse critical
          (mixedBracket D H leftInverse rightInverse critical left right) vector +
        SuperFieldProducts.koszul (leftParity + 1) (rightParity + 1) •
          mixedBracket D H leftInverse rightInverse critical right
            (mixedBracket D H leftInverse rightInverse critical left vector) := by
  have leftB0Fixed := originalB0_odd D H leftInverse rightInverse critical leftParity left
    leftFixed
  have rightB0Fixed := originalB0_odd D H leftInverse rightInverse critical rightParity right
    rightFixed
  have innerFixed := mixedBracket_homogeneous_fixed D H leftInverse rightInverse critical
    leftParity rightParity left right leftFixed rightFixed
  rw [mixedBracket_homogeneous D H leftInverse rightInverse critical
      rightParity 0 right vector rightFixed]
  unfold quotientDefectValue quotientDefect
  simp only [map_sub, map_add, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply]
  rw [mixedBracket_delta_right_homogeneous D H leftInverse rightInverse critical
      leftParity 0 left (product D H (-1) right vector) leftFixed,
    mixedBracket_leibniz_homogeneous D H leftInverse rightInverse critical
      leftParity (rightParity + 1) left
      (originalB0 D H leftInverse rightInverse critical right) vector
      leftFixed rightB0Fixed,
    mixedBracket_leibniz_homogeneous D H leftInverse rightInverse critical
      leftParity rightParity left right
      (originalB0 D H leftInverse rightInverse critical vector)
      leftFixed rightFixed,
    mixedBracket_leibniz_homogeneous D H leftInverse rightInverse critical
      leftParity rightParity left right vector
      leftFixed rightFixed,
    mixedBracket_leibniz_homogeneous D H leftInverse rightInverse critical
      (leftParity + 1) rightParity
      (originalB0 D H leftInverse rightInverse critical left) right vector
      leftB0Fixed rightFixed,
    mixedBracket_delta_right_homogeneous D H leftInverse rightInverse critical
      leftParity rightParity left right leftFixed,
    mixedBracket_delta_right_homogeneous D H leftInverse rightInverse critical
      leftParity 0 left vector leftFixed,
    mixedBracket_homogeneous D H leftInverse rightInverse critical
      (leftParity + rightParity + 1) 0
      (mixedBracket D H leftInverse rightInverse critical left right) vector innerFixed,
    mixedBracket_homogeneous D H leftInverse rightInverse critical
      rightParity 0 right
      (mixedBracket D H leftInverse rightInverse critical left vector) rightFixed]
  unfold quotientDefectValue quotientDefect
  rcases Nat.mod_two_eq_zero_or_one leftParity with leftEven | leftOdd
  · rcases Nat.mod_two_eq_zero_or_one rightParity with rightEven | rightOdd
    · simp [SuperFieldProducts.koszul, SuperFieldProducts.sign_power_mod,
        Nat.add_mod, Nat.mul_mod, leftEven, rightEven] <;> abel
    · simp [SuperFieldProducts.koszul, SuperFieldProducts.sign_power_mod,
        Nat.add_mod, Nat.mul_mod, leftEven, rightOdd] <;> abel
  · rcases Nat.mod_two_eq_zero_or_one rightParity with rightEven | rightOdd
    · simp [SuperFieldProducts.koszul, SuperFieldProducts.sign_power_mod,
        Nat.add_mod, Nat.mul_mod, leftOdd, rightEven] <;> abel
    · simp [SuperFieldProducts.koszul, SuperFieldProducts.sign_power_mod,
        Nat.add_mod, Nat.mul_mod, leftOdd, rightOdd] <;> abel

theorem parity_projection_fixed (grade : ℕ) (state : OriginalCohomology D H) :
    parity D H grade (parity D H grade state) = parity D H grade state := by
  refine Quotient.inductionOn state ?_
  intro representative
  change (OriginalBoundaries D H).mkQ
      (cycleParity D H grade (cycleParity D H grade representative)) =
    (OriginalBoundaries D H).mkQ (cycleParity D H grade representative)
  congr 1
  apply Subtype.ext
  exact LatticeBcGhostTensorStateField.parityPart_idempotent grade representative.val

theorem mixedBracket_jacobi_decomposition
    (left right vector : OriginalCohomology D H) :
    mixedBracket D H leftInverse rightInverse critical left
        (mixedBracket D H leftInverse rightInverse critical right vector) =
      (mixedBracket D H leftInverse rightInverse critical
          (mixedBracket D H leftInverse rightInverse critical
            (parity D H 0 left) (parity D H 0 right)) vector +
        SuperFieldProducts.koszul 1 1 •
          mixedBracket D H leftInverse rightInverse critical (parity D H 0 right)
            (mixedBracket D H leftInverse rightInverse critical (parity D H 0 left) vector)) +
      (mixedBracket D H leftInverse rightInverse critical
          (mixedBracket D H leftInverse rightInverse critical
            (parity D H 0 left) (parity D H 1 right)) vector +
        SuperFieldProducts.koszul 1 2 •
          mixedBracket D H leftInverse rightInverse critical (parity D H 1 right)
            (mixedBracket D H leftInverse rightInverse critical (parity D H 0 left) vector)) +
      (mixedBracket D H leftInverse rightInverse critical
          (mixedBracket D H leftInverse rightInverse critical
            (parity D H 1 left) (parity D H 0 right)) vector +
        SuperFieldProducts.koszul 2 1 •
          mixedBracket D H leftInverse rightInverse critical (parity D H 0 right)
            (mixedBracket D H leftInverse rightInverse critical (parity D H 1 left) vector)) +
      (mixedBracket D H leftInverse rightInverse critical
          (mixedBracket D H leftInverse rightInverse critical
            (parity D H 1 left) (parity D H 1 right)) vector +
        SuperFieldProducts.koszul 2 2 •
          mixedBracket D H leftInverse rightInverse critical (parity D H 1 right)
            (mixedBracket D H leftInverse rightInverse critical (parity D H 1 left) vector)) := by
  have leftDecomposition := parity_decomposition D H left
  have rightDecomposition := parity_decomposition D H right
  have leftZeroFixed := parity_projection_fixed D H 0 left
  have leftOneFixed := parity_projection_fixed D H 1 left
  have rightZeroFixed := parity_projection_fixed D H 0 right
  have rightOneFixed := parity_projection_fixed D H 1 right
  have expansion :
      mixedBracket D H leftInverse rightInverse critical left
          (mixedBracket D H leftInverse rightInverse critical right vector) =
        mixedBracket D H leftInverse rightInverse critical
          (parity D H 0 left + parity D H 1 left)
          (mixedBracket D H leftInverse rightInverse critical
            (parity D H 0 right + parity D H 1 right) vector) := by
    rw [leftDecomposition, rightDecomposition]
  rw [expansion]
  simp only [map_add, LinearMap.add_apply]
  rw [mixedBracket_jacobi_homogeneous D H leftInverse rightInverse critical
      0 0 (parity D H 0 left) (parity D H 0 right) vector
      leftZeroFixed rightZeroFixed,
    mixedBracket_jacobi_homogeneous D H leftInverse rightInverse critical
      0 1 (parity D H 0 left) (parity D H 1 right) vector
      leftZeroFixed rightOneFixed,
    mixedBracket_jacobi_homogeneous D H leftInverse rightInverse critical
      1 0 (parity D H 1 left) (parity D H 0 right) vector
      leftOneFixed rightZeroFixed,
    mixedBracket_jacobi_homogeneous D H leftInverse rightInverse critical
      1 1 (parity D H 1 left) (parity D H 1 right) vector
      leftOneFixed rightOneFixed]
  simp [SuperFieldProducts.koszul]
  module

theorem mixedBracket_leibniz_decomposition
    (left right vector : OriginalCohomology D H) :
    mixedBracket D H leftInverse rightInverse critical left
        (product D H (-1) right vector) =
      (product D H (-1)
          (mixedBracket D H leftInverse rightInverse critical
            (parity D H 0 left) (parity D H 0 right)) vector +
        SuperFieldProducts.koszul 1 0 •
          product D H (-1) (parity D H 0 right)
            (mixedBracket D H leftInverse rightInverse critical (parity D H 0 left) vector)) +
      (product D H (-1)
          (mixedBracket D H leftInverse rightInverse critical
            (parity D H 0 left) (parity D H 1 right)) vector +
        SuperFieldProducts.koszul 1 1 •
          product D H (-1) (parity D H 1 right)
            (mixedBracket D H leftInverse rightInverse critical (parity D H 0 left) vector)) +
      (product D H (-1)
          (mixedBracket D H leftInverse rightInverse critical
            (parity D H 1 left) (parity D H 0 right)) vector +
        SuperFieldProducts.koszul 2 0 •
          product D H (-1) (parity D H 0 right)
            (mixedBracket D H leftInverse rightInverse critical (parity D H 1 left) vector)) +
      (product D H (-1)
          (mixedBracket D H leftInverse rightInverse critical
            (parity D H 1 left) (parity D H 1 right)) vector +
        SuperFieldProducts.koszul 2 1 •
          product D H (-1) (parity D H 1 right)
            (mixedBracket D H leftInverse rightInverse critical (parity D H 1 left) vector)) := by
  have leftDecomposition := parity_decomposition D H left
  have rightDecomposition := parity_decomposition D H right
  have leftZeroFixed := parity_projection_fixed D H 0 left
  have leftOneFixed := parity_projection_fixed D H 1 left
  have rightZeroFixed := parity_projection_fixed D H 0 right
  have rightOneFixed := parity_projection_fixed D H 1 right
  have expansion :
      mixedBracket D H leftInverse rightInverse critical left
          (product D H (-1) right vector) =
        mixedBracket D H leftInverse rightInverse critical
          (parity D H 0 left + parity D H 1 left)
          (product D H (-1)
            (parity D H 0 right + parity D H 1 right) vector) := by
    rw [leftDecomposition, rightDecomposition]
  rw [expansion]
  simp only [map_add, LinearMap.add_apply]
  rw [mixedBracket_leibniz_homogeneous D H leftInverse rightInverse critical
      0 0 (parity D H 0 left) (parity D H 0 right) vector
      leftZeroFixed rightZeroFixed,
    mixedBracket_leibniz_homogeneous D H leftInverse rightInverse critical
      0 1 (parity D H 0 left) (parity D H 1 right) vector
      leftZeroFixed rightOneFixed,
    mixedBracket_leibniz_homogeneous D H leftInverse rightInverse critical
      1 0 (parity D H 1 left) (parity D H 0 right) vector
      leftOneFixed rightZeroFixed,
    mixedBracket_leibniz_homogeneous D H leftInverse rightInverse critical
      1 1 (parity D H 1 left) (parity D H 1 right) vector
      leftOneFixed rightOneFixed]
  norm_num [SuperFieldProducts.koszul]
  abel_nf

#print axioms mixedBracket
#print axioms mixedBracket_homogeneous

end D5.S3.VertexAlgebra.TensorConformal.OriginalIntegralBVGerstBracketTransient
