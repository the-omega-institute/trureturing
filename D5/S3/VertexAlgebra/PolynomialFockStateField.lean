/- GID: D5/S3/VertexAlgebra/PolynomialFockStateField
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/PolynomialFockStateField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary polynomial Fock states give creative local translated fields. -/

/-
proof_shape: stateField_creation: content; stateField_translation: content;
stateField_locality: content
escape_witness: Arbitrary sorted monomial words have pointwise finite creative
fields. The vacuum coefficient is their actual polynomial product. The two
normal-product halves coincide with the actual quadratic Sugawara sum, and
the actual L(-1) covariance propagates through every word and the monomial basis.
Finite residue cancellation preserves locality through the ordered products;
finite polynomial supports yield an operator-uniform order before either mode index.
admission_basis: escape-witness
Direct frozen dependencies:
  D5/S3/VertexAlgebra/PolynomialFockSugawaraSupport.normalPair_support_interval
  (sha256:4965c0130d0dbcb3bc99ea25c46d318f4523b7b32c7450986791b3fb99994f7c).
  D5/S3/VertexAlgebra/PolynomialFockSugawaraCommutators.mode_heisenberg
  (sha256:70348f27aba9962d3e7e1069a03392b19973770fa93026cf488d6119d17860b5).
  D5/S3/VertexAlgebra/PolynomialFockSugawaraCommutators.L_mode_commutator
  (sha256:70348f27aba9962d3e7e1069a03392b19973770fa93026cf488d6119d17860b5).
Classical construction: Matsuo–Nagatomo, Theorem 5.4.1. The formal field
conditions do not assert a Monster realization or a physical spacetime bridge.
-/

import D5.S3.VertexAlgebra.FieldNormalProduct
import D5.S3.VertexAlgebra.FieldNormalProductLocality
import D5.S3.VertexAlgebra.PolynomialFockSugawaraCommutators
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Sort
import Mathlib.RingTheory.MvPolynomial.Basic

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.PolynomialFockStateField

open MvPolynomial
open D5.S3.VertexAlgebra.FieldNormalProduct
open D5.S3.VertexAlgebra.FieldNormalProductLocality
open D5.S3.VertexAlgebra.PolynomialFockSugawaraSupport
open D5.S3.VertexAlgebra.PolynomialFockSugawaraCommutators
open scoped VertexOperator

noncomputable def wordField : List ℕ → VertexOperator ℂ Fock
  | [] => identityField
  | slot :: tail => (normalMinusOne (dividedDerivative slot current) (wordField tail)).1

noncomputable def occurrences (exponents : ℕ →₀ ℕ) : List ℕ :=
  exponents.toMultiset.sort

noncomputable def Y : Fock →ₗ[ℂ] VertexOperator ℂ Fock :=
  (basisMonomials ℕ ℂ).constr ℂ (fun exponents => wordField (occurrences exponents))

set_option backward.isDefEq.respectTransparency false in
theorem stateField_creation :
    Y (1 : Fock) = identityField ∧ Y (X 0) = current ∧
    (∀ polynomial : Fock, ((Y polynomial) [[-1]]) (1 : Fock) = polynomial) ∧
    (∀ (polynomial : Fock) (index : ℤ), 0 ≤ index →
      ((Y polynomial) [[index]]) (1 : Fock) = 0) ∧
    (∀ index : ℤ, (Y ((2 : ℂ)⁻¹ • (X 0 : Fock) ^ 2)) [[index]] = L (index - 1)) := by
  classical
  have identityModes (index : ℤ) :
      ((identityField : VertexOperator ℂ Fock) [[index]]) =
        if index = -1 then LinearMap.id else 0 := by
    rw [identityField, VertexOperator.ncoeff_of_coeff]
    have equivalent : -index - 1 = 0 ↔ index = -1 := by omega
    simp only [equivalent]
  have currentModes (index : ℤ) : (current [[index]]) = mode index := by
    rw [current, VertexOperator.ncoeff_of_coeff]
    rw [show -(-index - 1) - 1 = index by omega]
  have derivativeModes (slot : ℕ) (index : ℤ) :
      ((dividedDerivative slot current) [[index]]) =
        ((Ring.choose (-index - 1 + slot) slot : ℤ) : ℂ) • mode (index - slot) := by
    apply LinearMap.ext
    intro vector
    change Ring.choose (-index - 1 + slot) slot •
      HVertexOperator.coeff current (-index - 1 + slot) vector = _
    rw [VertexOperator.coeff_eq_ncoeff, currentModes]
    rw [show -(-index - 1 + slot) - 1 = index - slot by omega]
    simp only [LinearMap.smul_apply, Int.cast_smul_eq_zsmul]
  have currentVacuum (index : ℤ) (nonnegative : 0 ≤ index) : mode index (1 : Fock) = 0 := by
    obtain ⟨number, rfl⟩ := Int.eq_ofNat_of_zero_le nonnegative
    cases number with
    | zero => simp [mode]
    | succ slot => simp [mode, annihilate]
  have derivativeVacuum (slot : ℕ) (index : ℤ) (nonnegative : 0 ≤ index) :
      ((dividedDerivative slot current) [[index]]) (1 : Fock) = 0 := by
    rw [derivativeModes, LinearMap.smul_apply]
    by_cases large : (slot : ℤ) ≤ index
    · rw [currentVacuum (index - slot) (by omega), smul_zero]
    · have positive : 0 ≤ -index - 1 + (slot : ℤ) := by omega
      obtain ⟨number, equality⟩ := Int.eq_ofNat_of_zero_le positive
      have smaller : number < slot := by omega
      rw [equality, Ring.choose_natCast, Nat.choose_eq_zero_of_lt smaller]
      simp
  have derivativeCreate (slot : ℕ) (vector : Fock) :
      ((dividedDerivative slot current) [[-1]]) vector = (X slot : Fock) * vector := by
    rw [derivativeModes]
    have integerIndex : (-1 : ℤ) - slot = Int.negSucc slot := by omega
    simp [integerIndex, Ring.choose_natCast, mode, create]
  have wordVacuum : ∀ word : List ℕ,
      ((wordField word) [[-1]]) (1 : Fock) = (word.map (fun slot => (X slot : Fock))).prod ∧
      ∀ index : ℤ, 0 ≤ index → ((wordField word) [[index]]) (1 : Fock) = 0 := by
    intro word
    induction word with
    | nil =>
      constructor
      · simp [wordField, identityModes]
      · intro index nonnegative
        simp [wordField, identityModes, show index ≠ -1 by omega]
    | cons slot tail inductionHypothesis =>
      have coefficient (index : ℤ) :=
        (normalMinusOne (dividedDerivative slot current) (wordField tail)).2 index (1 : Fock)
      constructor
      · rw [wordField, coefficient]
        have secondZero : ∀ offset : ℕ,
            ((wordField tail) [[-1 - offset - 1]])
              (((dividedDerivative slot current) [[offset]]) (1 : Fock)) = 0 := by
          intro offset
          rw [derivativeVacuum slot offset (by omega), map_zero]
        simp only [secondZero, finsum_zero, add_zero]
        rw [finsum_eq_single _ 0]
        · simpa [inductionHypothesis.1] using
            derivativeCreate slot (((wordField tail) [[-1]]) (1 : Fock))
        · intro offset nonzero
          rw [inductionHypothesis.2 (-1 + offset) (by omega), map_zero]
      · intro index nonnegative
        rw [wordField, coefficient]
        have firstZero : ∀ offset : ℕ,
            ((dividedDerivative slot current) [[-(offset : ℤ) - 1]])
              (((wordField tail) [[index + offset]]) (1 : Fock)) = 0 := by
          intro offset
          rw [inductionHypothesis.2 (index + offset) (by omega), map_zero]
        have secondZero : ∀ offset : ℕ,
            ((wordField tail) [[index - offset - 1]])
              (((dividedDerivative slot current) [[offset]]) (1 : Fock)) = 0 := by
          intro offset
          rw [derivativeVacuum slot offset (by omega), map_zero]
        simp [firstZero, secondZero]
  have monomialVacuum (exponents : ℕ →₀ ℕ) :
      ((Y (monomial exponents (1 : ℂ))) [[-1]]) (1 : Fock) = monomial exponents 1 ∧
      ∀ index : ℤ, 0 ≤ index →
        ((Y (monomial exponents (1 : ℂ))) [[index]]) (1 : Fock) = 0 := by
    have fieldEquality : Y (monomial exponents (1 : ℂ)) = wordField (occurrences exponents) :=
      (basisMonomials ℕ ℂ).constr_basis ℂ _ exponents
    rw [fieldEquality]
    refine ⟨?_, (wordVacuum (occurrences exponents)).2⟩
    rw [(wordVacuum (occurrences exponents)).1]
    have product : ∀ exponents : ℕ →₀ ℕ,
        (exponents.toMultiset.map (fun slot => (X slot : Fock))).prod = monomial exponents 1 := by
      intro exponents
      induction exponents using Finsupp.induction with
      | zero => simp
      | single_add slot exponent tail absent nonzero inductionHypothesis =>
        rw [Finsupp.toMultiset_add, Multiset.map_add, Multiset.prod_add,
          Finsupp.toMultiset_single, Multiset.map_nsmul, Multiset.prod_nsmul,
          Multiset.map_singleton, Multiset.prod_singleton, inductionHypothesis,
          monomial_single_add]
    change ((occurrences exponents : Multiset ℕ).map (fun slot => (X slot : Fock))).prod = _
    rw [occurrences, Multiset.sort_eq, product]
  have rightIdentity (operator : VertexOperator ℂ Fock) :
      (normalMinusOne operator identityField).1 = operator := by
    apply HVertexOperator.coeff_inj
    funext power
    apply LinearMap.ext
    intro vector
    rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff,
      (normalMinusOne operator identityField).2]
    let index : ℤ := -power - 1
    change (∑ᶠ offset : ℕ, (operator [[-(offset : ℤ) - 1]])
        (((identityField : VertexOperator ℂ Fock) [[index + offset]]) vector)) +
      (∑ᶠ offset : ℕ, ((identityField : VertexOperator ℂ Fock) [[index - offset - 1]])
        ((operator [[offset]]) vector)) = (operator [[index]]) vector
    by_cases positive : 0 ≤ index
    · have firstZero : ∀ offset : ℕ,
          (operator [[-(offset : ℤ) - 1]])
            (((identityField : VertexOperator ℂ Fock) [[index + offset]]) vector) = 0 := by
        intro offset
        simp [identityModes, show index + offset ≠ -1 by omega]
      simp only [firstZero, finsum_zero, zero_add]
      rw [finsum_eq_single _ index.toNat]
      · simp [identityModes, Int.toNat_of_nonneg positive]
      · intro offset distinct
        have different : index - (offset : ℤ) - 1 ≠ -1 := by omega
        simp [identityModes, different]
    · have secondZero : ∀ offset : ℕ,
          ((identityField : VertexOperator ℂ Fock) [[index - offset - 1]])
            ((operator [[offset]]) vector) = 0 := by
        intro offset
        simp [identityModes, show index - offset - 1 ≠ -1 by omega]
      simp only [secondZero, finsum_zero, add_zero]
      rw [finsum_eq_single _ (-index - 1).toNat]
      · have nonnegative : 0 ≤ -index - 1 := by omega
        rw [identityModes, Int.toNat_of_nonneg nonnegative,
          if_pos (by omega)]
        simp only [LinearMap.id_apply]
        rw [show -(-index - 1) - 1 = index by omega]
      · intro offset distinct
        have different : index + (offset : ℤ) ≠ -1 := by omega
        simp [identityModes, different]
  have derivativeZero : dividedDerivative 0 current = current := by
    apply VertexOperator.ext
    intro vector
    simp [dividedDerivative]
  have oneWord : wordField [0] = current := by
    rw [wordField, wordField, rightIdentity, derivativeZero]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have basisValue := (basisMonomials ℕ ℂ).constr_basis ℂ
      (fun exponents => wordField (occurrences exponents)) 0
    simpa [Y, occurrences, wordField] using basisValue
  · have basisValue := (basisMonomials ℕ ℂ).constr_basis ℂ
      (fun exponents => wordField (occurrences exponents)) (Finsupp.single 0 1)
    simpa [Y, occurrences, oneWord, X] using basisValue
  · intro polynomial
    let evaluation : VertexOperator ℂ Fock →ₗ[ℂ] Fock := {
      toFun operator := (operator [[-1]]) (1 : Fock)
      map_add' first second := by simp
      map_smul' scalar operator := by simp }
    have equality : evaluation.comp Y = (LinearMap.id : Module.End ℂ Fock) := by
      apply (basisMonomials ℕ ℂ).ext
      intro exponents
      exact (monomialVacuum exponents).1
    exact congrArg (fun operator : Module.End ℂ Fock => operator polynomial) equality
  · intro polynomial index nonnegative
    let evaluation : VertexOperator ℂ Fock →ₗ[ℂ] Fock := {
      toFun operator := (operator [[index]]) (1 : Fock)
      map_add' first second := by simp
      map_smul' scalar operator := by simp }
    have equality : evaluation.comp Y = (0 : Module.End ℂ Fock) := by
      apply (basisMonomials ℕ ℂ).ext
      intro exponents
      exact (monomialVacuum exponents).2 index nonnegative
    exact congrArg (fun operator : Module.End ℂ Fock => operator polynomial) equality
  · intro index
    have twice : occurrences (Finsupp.single 0 2) = [0, 0] := by
      rw [occurrences, Finsupp.toMultiset_single, two_nsmul]
      change (0 ::ₘ ({0} : Multiset ℕ)).sort = [0, 0]
      simpa only [Multiset.sort_singleton] using
        (Multiset.sort_cons (a := 0) (s := ({0} : Multiset ℕ)) (r := (· ≤ ·)) (by simp))
    have quadratic : Y ((X 0 : Fock) ^ 2) = (normalMinusOne current current).1 := by
      rw [X_pow_eq_monomial]
      have basisValue := (basisMonomials ℕ ℂ).constr_basis ℂ
        (fun exponents => wordField (occurrences exponents)) (Finsupp.single 0 2)
      have equality : Y (monomial (Finsupp.single 0 2) 1) = wordField [0, 0] := by
        simpa only [Y, coe_basisMonomials, twice] using basisValue
      rw [equality, wordField, derivativeZero, oneWord]
    have positivePair (offset : ℕ) :
        normalPair (index - 1 - offset) offset = mode (index - offset - 1) * mode offset := by
      unfold normalPair
      split_ifs with ordered
      · by_cases zero : offset = 0
        · subst offset
          simp [mode]
        · have different : index - 1 - (offset : ℤ) + offset ≠ 0 := by omega
          have commutator := mode_heisenberg (index - 1 - offset) offset
          rw [if_neg different] at commutator
          rw [← Module.End.mul_eq_comp]
          rw [show index - 1 - (offset : ℤ) = index - offset - 1 by omega] at commutator ⊢
          exact (sub_eq_zero.mp commutator).symm
      · rw [← Module.End.mul_eq_comp,
          show index - 1 - (offset : ℤ) = index - offset - 1 by omega]
    have negativePair (offset : ℕ) :
        normalPair (index - 1 - Int.negSucc offset) (Int.negSucc offset) =
          mode (-(offset : ℤ) - 1) * mode (index + offset) := by
      have firstIndex : index - 1 - Int.negSucc offset = index + offset := by omega
      have secondIndex : Int.negSucc offset = -(offset : ℤ) - 1 := by omega
      unfold normalPair
      split_ifs with ordered
      · rw [← Module.End.mul_eq_comp, firstIndex, secondIndex]
      · have different : (index - 1 - Int.negSucc offset) + Int.negSucc offset ≠ 0 := by omega
        have commutator := mode_heisenberg (index - 1 - Int.negSucc offset) (Int.negSucc offset)
        rw [if_neg different] at commutator
        rw [← Module.End.mul_eq_comp]
        rw [firstIndex, secondIndex] at commutator ⊢
        exact sub_eq_zero.mp commutator
    apply LinearMap.ext
    intro vector
    rw [map_smul]
    change (2 : ℂ)⁻¹ • ((Y ((X 0 : Fock) ^ 2)) [[index]]) vector = _
    rw [quadratic, (normalMinusOne current current).2]
    simp_rw [currentModes]
    change (2 : ℂ)⁻¹ • _ = (2 : ℂ)⁻¹ •
      (∑ᶠ offset : ℤ, normalPair (index - 1 - offset) offset vector)
    congr 1
    let summand (offset : ℤ) := normalPair (index - 1 - offset) offset vector
    have finite : Function.HasFiniteSupport summand :=
      (Set.finite_Ioo _ _).subset (normalPair_support_interval (index - 1) vector)
    have union : Set.range Int.ofNat ∪ Set.range Int.negSucc = Set.univ := by
      ext integer
      constructor
      · intro member; trivial
      · intro member
        cases integer with
        | ofNat offset => exact Or.inl ⟨offset, rfl⟩
        | negSucc offset => exact Or.inr ⟨offset, rfl⟩
    have disjoint : Disjoint (Set.range Int.ofNat) (Set.range Int.negSucc) := by
      apply Set.disjoint_left.mpr
      rintro integer ⟨positive, rfl⟩ ⟨negative, equality⟩
      simp only [Int.negSucc_eq, Int.ofNat_eq_natCast] at equality
      omega
    have split : (∑ᶠ offset : ℤ, summand offset) =
        (∑ᶠ offset : ℕ, summand (Int.ofNat offset)) +
        (∑ᶠ offset : ℕ, summand (Int.negSucc offset)) := by
      rw [← finsum_mem_univ, ← union,
        finsum_mem_union' disjoint (finite.subset Set.inter_subset_right)
          (finite.subset Set.inter_subset_right),
        finsum_mem_range (fun first second equality => Int.ofNat.inj equality),
        finsum_mem_range (fun first second equality => Int.negSucc.inj equality)]
    rw [split]
    simp only [summand, positivePair, negativePair, Module.End.mul_apply, Int.ofNat_eq_natCast]
    exact add_comm _ _

set_option backward.isDefEq.respectTransparency false in
theorem stateField_translation :
    L (-1) (1 : Fock) = 0 ∧ ∀ (polynomial : Fock) (index : ℤ),
      L (-1) * ((Y polynomial) [[index]]) - ((Y polynomial) [[index]]) * L (-1) =
        -(index : ℂ) • ((Y polynomial) [[index - 1]]) := by
  constructor
  · have termZero (offset : ℤ) : normalPair (-1 - offset) offset (1 : Fock) = 0 := by
      have nonnegativeZero (modeIndex : ℤ) (nonnegative : 0 ≤ modeIndex) :
          mode modeIndex (1 : Fock) = 0 := by
        obtain ⟨number, rfl⟩ := Int.eq_ofNat_of_zero_le nonnegative
        cases number with
        | zero => simp [mode]
        | succ slot => simp [mode, annihilate]
      by_cases ordered : offset ≤ -1 - offset
      · have nonnegative : 0 ≤ -1 - offset := by omega
        simp [normalPair, ordered, nonnegativeZero (-1 - offset) nonnegative]
      · have nonnegative : 0 ≤ offset := by omega
        simp [normalPair, ordered, nonnegativeZero offset nonnegative]
    change (2 : ℂ)⁻¹ • ∑ᶠ offset : ℤ, normalPair (-1 - offset) offset (1 : Fock) = 0
    simp [termZero]
  · intro polynomial index
    classical
    have currentModes (index : ℤ) : (current [[index]]) = mode index := by
      rw [current, VertexOperator.ncoeff_of_coeff]
      rw [show -(-index - 1) - 1 = index by omega]
    have derivativeModes (slot : ℕ) (index : ℤ) :
        ((dividedDerivative slot current) [[index]]) =
          ((Ring.choose (-index - 1 + slot) slot : ℤ) : ℂ) • mode (index - slot) := by
      apply LinearMap.ext
      intro vector
      change Ring.choose (-index - 1 + slot) slot •
        HVertexOperator.coeff current (-index - 1 + slot) vector = _
      rw [VertexOperator.coeff_eq_ncoeff, currentModes]
      rw [show -(-index - 1 + slot) - 1 = index - slot by omega]
      simp only [LinearMap.smul_apply, Int.cast_smul_eq_zsmul]
    have binomialShift (argument : ℤ) (order : ℕ) :
        Ring.choose argument order * (argument - order) =
          argument * Ring.choose (argument - 1) order := by
      have first := Ring.choose_smul_choose argument (n := order + 1) (k := order) (by omega)
      have second := Ring.choose_smul_choose argument (n := order + 1) (k := 1) (by omega)
      rw [Nat.choose_succ_self_right, Nat.add_sub_cancel_left, Ring.choose_one_right] at first
      rw [Nat.choose_one_right, Ring.choose_one_right, Nat.add_sub_cancel] at second
      exact first.symm.trans second
    have derivativeLaw (slot : ℕ) (index : ℤ) :
        L (-1) * ((dividedDerivative slot current) [[index]]) -
            ((dividedDerivative slot current) [[index]]) * L (-1) =
          -(index : ℂ) • ((dividedDerivative slot current) [[index - 1]]) := by
      rw [derivativeModes, derivativeModes, Algebra.mul_smul_comm,
        Algebra.smul_mul_assoc, ← smul_sub, L_mode_commutator, smul_smul]
      rw [show (-1 : ℤ) + (index - slot) = index - 1 - slot by omega, smul_smul]
      have integerEquality := binomialShift (-index + slot) slot
      have complexEquality := congrArg (fun integer : ℤ => (integer : ℂ)) integerEquality
      push_cast at complexEquality
      have firstIndex : -index + (slot : ℤ) - 1 = -index - 1 + slot := by omega
      have secondIndex : -(index - 1) - 1 + (slot : ℤ) = -index + slot := by omega
      rw [firstIndex] at complexEquality
      rw [secondIndex]
      congr 1
      push_cast
      linear_combination -complexEquality
    have wordLaw : ∀ (word : List ℕ) (index : ℤ),
        L (-1) * ((wordField word) [[index]]) -
            ((wordField word) [[index]]) * L (-1) =
          -(index : ℂ) • ((wordField word) [[index - 1]]) := by
      intro word
      induction word with
      | nil =>
        intro index
        have identityModes (index : ℤ) : (identityField : VertexOperator ℂ Fock) [[index]] =
            if index = -1 then LinearMap.id else 0 := by
          rw [identityField, VertexOperator.ncoeff_of_coeff]
          have equivalent : -index - 1 = 0 ↔ index = -1 := by omega
          simp only [equivalent]
        simp only [wordField, identityModes]
        by_cases atZero : index = 0
        · subst index
          simp
        · have different : index - 1 ≠ -1 := by omega
          simp only [if_neg different, smul_zero]
          split_ifs <;> simp only [Module.End.mul_eq_comp, LinearMap.comp_id,
            LinearMap.id_comp, mul_zero, zero_mul, sub_self]
      | cons slot tail inductionHypothesis =>
        intro index
        exact normalMinusOne_translation (L (-1)) (dividedDerivative slot current)
          (wordField tail) (derivativeLaw slot) inductionHypothesis index
    let defect : VertexOperator ℂ Fock →ₗ[ℂ] Module.End ℂ Fock := {
      toFun operator := L (-1) * (operator [[index]]) - (operator [[index]]) * L (-1) +
        (index : ℂ) • (operator [[index - 1]])
      map_add' first second := by
        simp only [map_add, Pi.add_apply, mul_add, add_mul, smul_add]
        abel
      map_smul' scalar operator := by
        simp only [map_smul, RingHom.id_apply, Pi.smul_apply, Algebra.mul_smul_comm,
          Algebra.smul_mul_assoc, ← smul_sub, ← smul_add, smul_comm (index : ℂ) scalar] }
    have equality : defect.comp Y = 0 := by
      apply (basisMonomials ℕ ℂ).ext
      intro exponents
      change defect (Y ((basisMonomials ℕ ℂ) exponents)) = 0
      rw [Y, (basisMonomials ℕ ℂ).constr_basis]
      change (L (-1) * ((wordField (occurrences exponents)) [[index]]) -
        ((wordField (occurrences exponents)) [[index]]) * L (-1)) +
        (index : ℂ) • ((wordField (occurrences exponents)) [[index - 1]]) = 0
      rw [wordLaw]
      simp
    have result := congrArg
      (fun operator => (operator : Fock →ₗ[ℂ] Module.End ℂ Fock) polynomial) equality
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at result
    change (L (-1) * ((Y polynomial) [[index]]) - ((Y polynomial) [[index]]) * L (-1)) +
      (index : ℂ) • ((Y polynomial) [[index - 1]]) = 0 at result
    simpa only [neg_smul] using eq_neg_iff_add_eq_zero.mpr result

set_option backward.isDefEq.respectTransparency false in
theorem stateField_locality :
    (Y (1 : Fock) = identityField ∧ Y (X 0) = current ∧
      (∀ polynomial : Fock, ((Y polynomial) [[-1]]) (1 : Fock) = polynomial) ∧
      (∀ (polynomial : Fock) (index : ℤ), 0 ≤ index →
        ((Y polynomial) [[index]]) (1 : Fock) = 0) ∧
      (∀ index : ℤ, (Y ((2 : ℂ)⁻¹ • (X 0 : Fock) ^ 2)) [[index]] = L (index - 1))) ∧
    (L (-1) (1 : Fock) = 0 ∧ ∀ (polynomial : Fock) (index : ℤ),
      L (-1) * ((Y polynomial) [[index]]) - ((Y polynomial) [[index]]) * L (-1) =
        -(index : ℂ) • ((Y polynomial) [[index - 1]])) ∧
    ∀ polynomial other : Fock, ∃ order : ℕ, ∀ left right : ℤ,
      (∑ offset ∈ Finset.range (order + 1),
        (((-1 : ℂ) ^ offset) * (order.choose offset : ℂ)) •
          FieldNormalProductLocality.commutator (Y polynomial) (Y other)
            (left + (order : ℤ) - offset) (right + offset)) = 0 := by
  refine ⟨stateField_creation, stateField_translation, ?_⟩
  intro polynomial other
  classical
  let shiftLeft : Module.End ℂ ((ℤ → ℤ → Module.End ℂ Fock)) := {
    toFun value := fun first second => value (first + 1) second
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
  }
  let shiftRight : Module.End ℂ ((ℤ → ℤ → Module.End ℂ Fock)) := {
    toFun value := fun first second => value first (second + 1)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
  }
  have binomial (value : (ℤ → ℤ → Module.End ℂ Fock)) (order : ℕ) (first second : ℤ) :
      ((((shiftLeft - shiftRight) ^ order : Module.End ℂ ((ℤ → ℤ → Module.End ℂ Fock)))) value)
        first second =
        ∑ offset ∈ Finset.range (order + 1),
          (((-1 : ℂ) ^ offset) * (order.choose offset : ℂ)) •
            value (first + (order : ℤ) - offset) (second + offset) := by
    have commute : Commute (-shiftRight : Module.End ℂ ((ℤ → ℤ → Module.End ℂ Fock))) shiftLeft
      := by
      apply LinearMap.ext
      intro distribution
      funext left right
      simp [shiftLeft, shiftRight]
    have leftPower (degree : ℕ) (distribution : (ℤ → ℤ → Module.End ℂ Fock)) :
        (shiftLeft ^ degree) distribution = fun left right => distribution (left + degree)
          right := by
      induction degree with
      | zero => simp
      | succ degree inductionHypothesis =>
        rw [pow_succ', Module.End.mul_apply, inductionHypothesis]
        funext left right
        change distribution (left + 1 + degree) right = distribution (left + (degree + 1 : ℕ)) right
        congr 1
        push_cast
        omega
    have rightPower (degree : ℕ) (distribution : (ℤ → ℤ → Module.End ℂ Fock)) :
        ((-shiftRight) ^ degree) distribution = fun left right =>
          ((-1 : ℂ) ^ degree) • distribution left (right + degree) := by
      induction degree with
      | zero => simp
      | succ degree inductionHypothesis =>
        rw [pow_succ', Module.End.mul_apply, inductionHypothesis]
        funext left right
        change -(((-1 : ℂ) ^ degree) • distribution left (right + 1 + degree)) =
          ((-1 : ℂ) ^ (degree + 1)) • distribution left (right + (degree + 1 : ℕ))
        rw [pow_succ', mul_smul, neg_one_smul]
        have indices : right + 1 + (degree : ℤ) = right + (degree + 1 : ℕ) := by
          push_cast
          omega
        rw [indices]
    have equation : (shiftLeft - shiftRight : Module.End ℂ ((ℤ → ℤ → Module.End ℂ Fock))) =
        -shiftRight + shiftLeft := by abel
    rw [equation, commute.add_pow, LinearMap.sum_apply]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro offset member
    have within : offset ≤ order := by simpa using Finset.mem_range.mp member
    simp only [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul,
      rightPower, leftPower, Pi.smul_apply]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_comm]
    congr 2
    push_cast [Int.natCast_sub within]
    omega
  have symmetry (first second : VertexOperator ℂ Fock) (order : ℕ)
      (killed : delta^[order] (FieldNormalProductLocality.commutator first second) = 0) :
      delta^[order] (FieldNormalProductLocality.commutator second first) = 0 := by
    have flipDelta (distribution : ℤ → ℤ → Module.End ℂ Fock) :
        delta (flipDistribution distribution) = -flipDistribution (delta distribution) := by
      funext left right
      dsimp [delta, flipDistribution]
      abel
    have scaledDelta (scalar : ℂ) (distribution : ℤ → ℤ → Module.End ℂ Fock) :
        delta (scalar • distribution) = scalar • delta distribution := by
      funext left right
      simp [delta, smul_sub]
    have flipIterate (distribution : ℤ → ℤ → Module.End ℂ Fock) (degree : ℕ) :
        delta^[degree] (flipDistribution distribution) =
          ((-1 : ℂ) ^ degree) • flipDistribution (delta^[degree] distribution) := by
      induction degree with
      | zero => simp
      | succ degree inductionHypothesis =>
        rw [Function.iterate_succ_apply', inductionHypothesis, scaledDelta, flipDelta]
        rw [← Function.iterate_succ_apply' (f := delta) degree distribution]
        rw [pow_succ]
        funext left right
        simp only [Pi.smul_apply, Pi.neg_apply]
        module
    have reversed : FieldNormalProductLocality.commutator second first = -flipDistribution
      (FieldNormalProductLocality.commutator first second) := by
      funext left right
      dsimp [FieldNormalProductLocality.commutator, flipDistribution]
      abel
    rw [reversed]
    have negDelta (distribution : ℤ → ℤ → Module.End ℂ Fock) :
        delta^[order] (-distribution) = -delta^[order] distribution := by
      change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Fock))^[order] (-distribution) =
        -(deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Fock))^[order] distribution
      rw [← Module.End.pow_apply, ← Module.End.pow_apply, map_neg]
    rw [negDelta, flipIterate, killed, map_zero, smul_zero, neg_zero]
  have currentLocal : delta^[2] (FieldNormalProductLocality.commutator current current) = 0 := by
    have currentModes (index : ℤ) : (current [[index]]) = mode index := by
      rw [current, VertexOperator.ncoeff_of_coeff]
      rw [show -(-index - 1) - 1 = index by omega]
    funext left right
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, delta]
    simp only [FieldNormalProductLocality.commutator, currentModes]
    simp_rw [mode_heisenberg]
    rw [show left + 1 + 1 + right = left + right + 2 by omega,
      show left + 1 + (right + 1) = left + right + 2 by omega,
      show left + (right + 1 + 1) = left + right + 2 by omega]
    by_cases condition : left + right + 2 = 0
    · simp only [if_pos condition]
      simp only [Pi.zero_apply]
      push_cast
      module
    · simp [condition]
  let Local (first second : VertexOperator ℂ Fock) : Prop :=
    ∃ order : ℕ, delta^[order] (FieldNormalProductLocality.commutator first second) = 0
  have localSymm (first second : VertexOperator ℂ Fock) (locality : Local first second) : Local
    second first := by
    obtain ⟨order, killed⟩ := locality
    exact ⟨order, symmetry first second order killed⟩
  have identityModes (index : ℤ) :
      ((identityField : VertexOperator ℂ Fock) [[index]]) =
        if index = -1 then LinearMap.id else 0 := by
    rw [identityField, VertexOperator.ncoeff_of_coeff]
    have equivalent : -index - 1 = 0 ↔ index = -1 := by omega
    simp only [equivalent]
  have identityLocal (operator : VertexOperator ℂ Fock) : Local identityField operator := by
    refine ⟨0, ?_⟩
    funext left right
    simp only [Function.iterate_zero_apply, FieldNormalProductLocality.commutator, identityModes]
    split_ifs <;> simp [Module.End.mul_eq_comp]
  have normalLocal (first second third : VertexOperator ℂ Fock)
      (firstThird : Local first third) (secondThird : Local second third)
      (firstSecond : Local first second) : Local (normalMinusOne first second).val third := by
    obtain ⟨firstOrder, firstKilled⟩ := firstThird
    obtain ⟨secondOrder, secondKilled⟩ := secondThird
    obtain ⟨thirdOrder, thirdKilled⟩ := firstSecond
    exact ⟨firstOrder + secondOrder + thirdOrder,
      normalMinusOne_locality first second third firstOrder secondOrder thirdOrder
        firstKilled secondKilled thirdKilled⟩
  have generatorsLocal (firstDegree secondDegree : ℕ) :
      Local (dividedDerivative firstDegree current) (dividedDerivative secondDegree current) := by
    have first := dividedDerivative_locality current current 2 firstDegree currentLocal
    have reversed := symmetry (dividedDerivative firstDegree current) current (2 + firstDegree)
      first
    have second := dividedDerivative_locality current (dividedDerivative firstDegree current)
      (2 + firstDegree) secondDegree reversed
    exact ⟨2 + firstDegree + secondDegree,
      symmetry (dividedDerivative secondDegree current) (dividedDerivative firstDegree current)
        (2 + firstDegree + secondDegree) second⟩
  have generatorWord : ∀ (word : List ℕ) (degree : ℕ),
      Local (dividedDerivative degree current) (wordField word) := by
    intro word
    induction word with
    | nil =>
      intro degree
      exact localSymm _ _ (identityLocal _)
    | cons slot tail inductionHypothesis =>
      intro degree
      apply localSymm
      exact normalLocal (dividedDerivative slot current) (wordField tail)
        (dividedDerivative degree current) (generatorsLocal slot degree)
        (localSymm _ _ (inductionHypothesis degree)) (inductionHypothesis slot)
  have wordsLocal : ∀ (word otherWord : List ℕ), Local (wordField word) (wordField otherWord) := by
    intro word
    induction word with
    | nil => intro otherWord; exact identityLocal _
    | cons slot tail inductionHypothesis =>
      intro otherWord
      exact normalLocal (dividedDerivative slot current) (wordField tail) (wordField otherWord)
        (generatorWord otherWord slot) (inductionHypothesis otherWord) (generatorWord tail slot)
  have monotone (distribution : ℤ → ℤ → Module.End ℂ Fock) (small large : ℕ)
      (less : small ≤ large) (killed : delta^[small] distribution = 0) : delta^[large]
        distribution = 0 := by
    have original : (deltaEnd ^ small) distribution = 0 := by
      rw [Module.End.pow_apply]
      exact killed
    have result := Module.End.pow_map_zero_of_le less original
    rw [Module.End.pow_apply] at result
    exact result
  have localAdd (first second third : VertexOperator ℂ Fock)
      (firstLocal : Local first third) (secondLocal : Local second third) : Local (first +
        second) third := by
    obtain ⟨firstOrder, firstKilled⟩ := firstLocal
    obtain ⟨secondOrder, secondKilled⟩ := secondLocal
    let order := max firstOrder secondOrder
    have firstBound := monotone (FieldNormalProductLocality.commutator first third) firstOrder
      order (le_max_left _ _) firstKilled
    have secondBound := monotone (FieldNormalProductLocality.commutator second third)
      secondOrder order (le_max_right _ _) secondKilled
    refine ⟨order, ?_⟩
    have split : FieldNormalProductLocality.commutator (first + second) third =
      FieldNormalProductLocality.commutator first third + FieldNormalProductLocality.commutator
      second third := by
      funext left right
      simp only [FieldNormalProductLocality.commutator, map_add, Pi.add_apply]
      noncomm_ring
    rw [split]
    change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Fock))^[order] _ = 0
    rw [← Module.End.pow_apply, map_add]
    simp only [Module.End.pow_apply]
    change delta^[order] (FieldNormalProductLocality.commutator first third) +
      delta^[order] (FieldNormalProductLocality.commutator second third) = 0
    rw [firstBound, secondBound, add_zero]
  have localSmul (scalar : ℂ) (first second : VertexOperator ℂ Fock)
      (locality : Local first second) : Local (scalar • first) second := by
    obtain ⟨order, killed⟩ := locality
    refine ⟨order, ?_⟩
    have split : FieldNormalProductLocality.commutator (scalar • first) second = scalar •
      FieldNormalProductLocality.commutator first second := by
      funext left right
      simp only [FieldNormalProductLocality.commutator, map_smul, Pi.smul_apply,
        Algebra.smul_mul_assoc,
        Algebra.mul_smul_comm, ← smul_sub]
    rw [split]
    change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Fock))^[order] _ = 0
    rw [← Module.End.pow_apply, map_smul]
    simp only [Module.End.pow_apply]
    change scalar • delta^[order] (FieldNormalProductLocality.commutator first second) = 0
    rw [killed, smul_zero]
  have localSum {Index : Type} (indices : Finset Index) (fields : Index → VertexOperator ℂ Fock)
      (operator : VertexOperator ℂ Fock) (locality : ∀ index ∈ indices, Local (fields index)
        operator) :
      Local (∑ index ∈ indices, fields index) operator := by
    induction indices using Finset.induction_on with
    | empty =>
      refine ⟨0, ?_⟩
      funext left right
      simp [FieldNormalProductLocality.commutator]
    | @insert index indices absent inductionHypothesis =>
      rw [Finset.sum_insert absent]
      exact localAdd _ _ _ (locality index (Finset.mem_insert_self _ _))
        (inductionHypothesis (fun other member => locality other (Finset.mem_insert_of_mem member)))
  have expansion (value : Fock) : Y value =
      ∑ exponent ∈ ((basisMonomials ℕ ℂ).repr value).support,
        ((basisMonomials ℕ ℂ).repr value exponent) • wordField (occurrences exponent) := by
    change (basisMonomials ℕ ℂ).constr ℂ _ value = _
    rw [(basisMonomials ℕ ℂ).constr_apply, Finsupp.sum]
  have polynomialWord (value : Fock) (word : List ℕ) : Local (Y value) (wordField word) := by
    rw [expansion]
    apply localSum
    intro exponent member
    exact localSmul _ _ _ (wordsLocal _ _)
  have polynomialsLocal : Local (Y polynomial) (Y other) := by
    apply localSymm
    rw [expansion other]
    apply localSum
    intro exponent member
    exact localSmul _ _ _ (localSymm _ _ (polynomialWord polynomial _))
  obtain ⟨order, killed⟩ := polynomialsLocal
  refine ⟨order, ?_⟩
  intro left right
  rw [← binomial, show (shiftLeft - shiftRight : Module.End ℂ (ℤ → ℤ → Module.End ℂ Fock)) =
    deltaEnd by rfl, Module.End.pow_apply]
  exact congrFun (congrFun killed left) right

end D5.S3.VertexAlgebra.PolynomialFockStateField
