/- GID: D5/S3/Quantum/Fermionic/BcGhostStateField
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostStateField
   mirror-E: none(waiver:algebraic-ghost-state-fields)
   anchors: []
   utility: none
   digest: Signed ordered fields on every actual finite occupation ghost state. -/

/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
The signed normal product and its translation covariance are supplied by
SignedFieldNormalProductLocality and SignedFieldResidueLocality. Their generic
finite-support calculus retains the attributed ScottCarnahan/vertexAlg source.
The occupation-word construction uses the original countable Fock carrier.
-/

/-
proof_shape: stateField_creation, stateField_translation, stateField_parity: content
escape_witness: Sorted actual occupation creators construct all word coefficients.
Creation and the original Ward identities connect this construction to the actual
vacuum and translation; actual CAR parity extends to arbitrary finite state sums.
admission_basis: escape-witness
-/

import D5.S3.Quantum.Fermionic.BcGhostVirasoro
import D5.S3.VertexAlgebra.FieldNormalProduct
import D5.S3.VertexAlgebra.SignedFields.SignedFieldResidueLocality
import Mathlib.Data.Finset.Sort

/-! Actual ghost fields, signed normal ordering and the occupation basis. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators VertexOperator
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.VertexAlgebra.FieldNormalProduct

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostStateField

private noncomputable def signedNormalMinusOne (sign : ℂ) (left right : VertexOperator ℂ Fock) :
    {operator : VertexOperator ℂ Fock // ∀ index vector,
      (operator [[index]]) vector =
        (∑ᶠ offset : ℕ, (left [[-(offset : ℤ) - 1]]) ((right [[index + offset]]) vector)) +
        sign • (∑ᶠ offset : ℕ, (right [[index - offset - 1]]) ((left [[offset]]) vector))} :=
  D5.S3.VertexAlgebra.SignedFieldNormalProductLocality.signedNormalMinusOne sign left right

private theorem signedNormal_translation (sign : ℂ) (translation : Module.End ℂ Fock)
    (left right : VertexOperator ℂ Fock)
    (leftLaw : ∀ index : ℤ,
      translation * (left [[index]]) - (left [[index]]) * translation =
        -(index : ℂ) • (left [[index - 1]]))
    (rightLaw : ∀ index : ℤ,
      translation * (right [[index]]) - (right [[index]]) * translation =
        -(index : ℂ) • (right [[index - 1]])) (index : ℤ) :
    translation * ((signedNormalMinusOne sign left right).1 [[index]]) -
        ((signedNormalMinusOne sign left right).1 [[index]]) * translation =
      -(index : ℂ) • ((signedNormalMinusOne sign left right).1 [[index - 1]]) := by
  have zeroDerivative : dividedDerivative 0 left = left := by
    apply LinearMap.ext
    intro vector
    simp [dividedDerivative, LaurentSeries.hasseDeriv_zero]
  have normal : (D5.S3.VertexAlgebra.SignedFieldResidueLocality.residueField
      sign (-1) left right).operator =
      (signedNormalMinusOne sign left right).1 := by
    have result :=
      D5.S3.VertexAlgebra.SignedFieldResidueLocality.negativeResidue
      sign left right 0
    change (D5.S3.VertexAlgebra.SignedFieldResidueLocality.residueField
      sign (-1) left right).operator =
        (D5.S3.VertexAlgebra.SignedFieldNormalProductLocality.signedNormalMinusOne
          sign (dividedDerivative 0 left) right).1 at result
    rw [zeroDerivative] at result
    exact result
  simpa only [normal] using
    D5.S3.VertexAlgebra.SignedFieldResidueLocality.residue_translation
      sign (-1) left right translation leftLaw rightLaw index

private def generatingMode (species : Bool) (n : ℤ) : Module.End ℂ Fock :=
  if species then c (n + 2) else b (n - 1)

private theorem generating_ket_tail (species : Bool) (S : Finset ℕ) (n : ℤ)
    (hn : ((S.sup id : ℕ) : ℤ) + 3 ≤ n) : generatingMode species n (ket S) = 0 := by
  have hbound (j : ℕ) (hj : j ∈ S) : j ≤ S.sup id := Finset.le_sup (f := id) hj
  cases species
  · have hcut : ¬n - 1 ≤ -2 := by omega
    have hsite : 2 * n.toNat + 1 ∉ S := by
      intro h
      have := hbound _ h
      omega
    simp [generatingMode, b, hcut, annihilate_ket, hsite]
  · have hcut : ¬n + 2 ≤ 1 := by omega
    have hsite : 2 * n.toNat ∉ S := by
      intro h
      have := hbound _ h
      omega
    simp [generatingMode, c, hcut, annihilate_ket, hsite]

private theorem generating_tail (species : Bool) (v : Fock) :
    ∃ N : ℕ, ∀ n : ℤ, (N : ℤ) ≤ n → generatingMode species n v = 0 := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add v w hv hw =>
    obtain ⟨Nv, hv⟩ := hv
    obtain ⟨Nw, hw⟩ := hw
    exact ⟨max Nv Nw, fun n hn => by
      rw [map_add, hv n (by omega), hw n (by omega), add_zero]⟩
  | single S a =>
    refine ⟨S.sup id + 3, ?_⟩
    intro n hn
    have hs : Finsupp.single S a = a • ket S := by simp [ket]
    rw [hs, map_smul, generating_ket_tail species S n (by exact_mod_cast hn), smul_zero]

private def generatingField (species : Bool) : VertexOperator ℂ Fock :=
  VertexOperator.of_coeff (fun power => generatingMode species (-power - 1)) (by
    intro v
    obtain ⟨N, hN⟩ := generating_tail species v
    refine ⟨-(N : ℤ) - 1, ?_⟩
    intro power member
    by_contra h
    exact member (hN (-power - 1) (by omega)))

private theorem generating_modes (species : Bool) (n : ℤ) :
    ((generatingField species) [[n]]) = generatingMode species n := by
  rw [generatingField, VertexOperator.ncoeff_of_coeff]
  congr 1
  omega

/-- Sorted occupation sites are physical divided derivatives: even sites are b,
odd sites are c. Each step has the sign of two odd homogeneous factors exactly
when the tail contains an odd number of sites. -/
private def wordField : List ℕ → VertexOperator ℂ Fock
  | [] => identityField
  | j :: tail =>
    (signedNormalMinusOne ((-1 : ℂ) ^ tail.length)
      (dividedDerivative (j / 2) (generatingField (j % 2 == 1))) (wordField tail)).1

/-- The actual linear state-field map on the entire finite-occupation carrier. -/
def Y : Fock →ₗ[ℂ] VertexOperator ℂ Fock :=
  Finsupp.lsum ℂ fun S => (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (wordField S.sort)

private theorem Y_ket (S : Finset ℕ) : Y (ket S) = wordField S.sort := by
  simp [Y, ket]

private theorem derivative_modes (species : Bool) (order : ℕ) (n : ℤ) :
    ((dividedDerivative order (generatingField species)) [[n]]) =
      ((Ring.choose (-n - 1 + order) order : ℤ) : ℂ) • generatingMode species (n - order) := by
  apply LinearMap.ext
  intro v
  change Ring.choose (-n - 1 + order) order •
    HVertexOperator.coeff (generatingField species) (-n - 1 + order) v = _
  rw [VertexOperator.coeff_eq_ncoeff, generating_modes]
  rw [show -(-n - 1 + order) - 1 = n - order by omega]
  simp only [LinearMap.smul_apply, Int.cast_smul_eq_zsmul]

private theorem derivative_creative (species : Bool) (order : ℕ) (n : ℤ)
    (hn : 0 ≤ n) :
    ((dividedDerivative order (generatingField species)) [[n]]) vacuum = 0 := by
  rw [derivative_modes, LinearMap.smul_apply]
  by_cases large : (order : ℤ) ≤ n
  · have hvac : generatingMode species (n - order) vacuum = 0 := by
      cases species
      · exact ghost_vacuum.1 _ (by omega)
      · exact ghost_vacuum.2.1 _ (by omega)
    rw [hvac, smul_zero]
  · have positive : 0 ≤ -n - 1 + (order : ℤ) := by omega
    obtain ⟨number, equality⟩ := Int.eq_ofNat_of_zero_le positive
    have smaller : number < order := by omega
    rw [equality, Ring.choose_natCast, Nat.choose_eq_zero_of_lt smaller]
    simp

private theorem site_creation (j : ℕ) :
    ((dividedDerivative (j / 2) (generatingField (j % 2 == 1))) [[-1]]) = create j := by
  rw [derivative_modes]
  norm_num only [neg_neg, sub_self, zero_add, Ring.choose_natCast, Nat.choose_self,
    Int.cast_one, one_smul]
  by_cases he : j % 2 = 0
  · have hj : j = 2 * (j / 2) := by omega
    have hspecies : (j % 2 == 1) = false := by simp [he]
    simp only [hspecies, generatingMode, Bool.false_eq_true, ite_false]
    have hindex : (-1 : ℤ) - (j / 2 : ℕ) - 1 = -(j / 2 : ℕ) - 2 := by omega
    rw [hindex, (mode_correspondence (j / 2)).1, ← hj]
  · have hj : j = 2 * (j / 2) + 1 := by omega
    have hspecies : (j % 2 == 1) = true := by simp [show j % 2 = 1 by omega]
    simp only [hspecies, generatingMode, ite_true]
    have hindex : (-1 : ℤ) - (j / 2 : ℕ) + 2 = 1 - (j / 2 : ℕ) := by omega
    rw [hindex, (mode_correspondence (j / 2)).2.2.1, ← hj]

private theorem word_vacuum (w : List ℕ) :
    ((wordField w) [[-1]]) vacuum = word (w.map (fun j => (j, true))) vacuum ∧
    ∀ n : ℤ, 0 ≤ n → ((wordField w) [[n]]) vacuum = 0 := by
  have identityModes (n : ℤ) : ((identityField : VertexOperator ℂ Fock) [[n]]) =
      if n = -1 then LinearMap.id else 0 := by
    rw [identityField, VertexOperator.ncoeff_of_coeff]
    simp only [show -n - 1 = 0 ↔ n = -1 by omega]
  induction w with
  | nil =>
    constructor
    · simp [wordField, identityModes, word]
    · intro n hn
      simp [wordField, identityModes, show n ≠ -1 by omega]
  | cons j tail ih =>
    have coefficient (n : ℤ) := (signedNormalMinusOne ((-1 : ℂ) ^ tail.length)
      (dividedDerivative (j / 2) (generatingField (j % 2 == 1))) (wordField tail)).2 n vacuum
    constructor
    · rw [wordField, coefficient]
      have secondZero : ∀ i : ℕ,
          ((wordField tail) [[-1 - i - 1]])
            (((dividedDerivative (j / 2) (generatingField (j % 2 == 1))) [[i]]) vacuum) = 0 := by
        intro i
        rw [derivative_creative _ _ _ (by omega), map_zero]
      simp only [secondZero, finsum_zero, smul_zero, add_zero]
      rw [finsum_eq_single _ 0]
      · simp only [Nat.cast_zero, neg_zero, zero_sub, add_zero, site_creation, ih.1,
          List.map_cons, word, mode, ite_true, Module.End.mul_apply]
      · intro i hi
        rw [ih.2 (-1 + i) (by omega), map_zero]
    · intro n hn
      rw [wordField, coefficient]
      have firstZero : ∀ i : ℕ,
          ((dividedDerivative (j / 2) (generatingField (j % 2 == 1))) [[-(i : ℤ) - 1]])
            (((wordField tail) [[n + i]]) vacuum) = 0 := by
        intro i
        rw [ih.2 _ (by omega), map_zero]
      have secondZero : ∀ i : ℕ,
          ((wordField tail) [[n - i - 1]])
            (((dividedDerivative (j / 2) (generatingField (j % 2 == 1))) [[i]]) vacuum) = 0 := by
        intro i
        rw [derivative_creative _ _ _ (by omega), map_zero]
      simp [firstZero, secondZero]

private theorem sorted_creator_vacuum (S : Finset ℕ) :
    word (S.sort.map (fun j => (j, true))) vacuum = ket S := by
  classical
  induction S using Finset.eraseInduction with
  | H S ih =>
    by_cases empty : S = ∅
    · subst S
      simp [word, vacuum]
    · have hS := Finset.nonempty_iff_ne_empty.mpr empty
      let j := S.min' hS
      have hj : j ∈ S := Finset.min'_mem S hS
      have hnot : j ∉ S.erase j := Finset.notMem_erase j S
      have hbound : ∀ k ∈ S.erase j, j ≤ k := by
        intro k hk
        exact Finset.min'_le S k (Finset.mem_of_mem_erase hk)
      have hsort : S.sort = j :: (S.erase j).sort := by
        conv_lhs => rw [← Finset.insert_erase hj]
        exact Finset.sort_insert (· ≤ ·) hbound hnot
      have hphase : phase j (S.erase j) = 1 := by
        have hz : (S.erase j).filter (· < j) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro k hk
          obtain ⟨hk, hkj⟩ := Finset.mem_filter.mp hk
          exact (not_lt_of_ge (hbound k hk)) hkj
        simp [phase, lowerCount, hz]
      rw [hsort, List.map_cons, word, Module.End.mul_apply, mode, if_pos rfl,
        ih j hj, create_ket, if_neg hnot, hphase, one_smul, Finset.insert_erase hj]

/-- Every actual finite occupation is created, and all nonnegative modes kill
its vacuum. The generating states use the original physical mode shifts. -/
theorem stateField_creation :
    Y vacuum = identityField ∧
    (∀ a : Fock, ((Y a) [[-1]]) vacuum = a) ∧
    (∀ (a : Fock) (n : ℤ), 0 ≤ n → ((Y a) [[n]]) vacuum = 0) ∧
    (∀ n : ℤ, ((Y (ket {0})) [[n]]) = b (n - 1)) ∧
    (∀ n : ℤ, ((Y (ket {1})) [[n]]) = c (n + 2)) := by
  classical
  have hcreation (a : Fock) : ((Y a) [[-1]]) vacuum = a := by
    induction a using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simpa [map_add, ha, hb]
    | single S z =>
      have hs : Finsupp.single S z = z • ket S := by simp [ket]
      rw [hs, map_smul]
      simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply, Y_ket, (word_vacuum S.sort).1,
        sorted_creator_vacuum]
  have hcreative (a : Fock) (n : ℤ) (hn : 0 ≤ n) : ((Y a) [[n]]) vacuum = 0 := by
    induction a using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simpa [map_add, ha, hb]
    | single S z =>
      have hs : Finsupp.single S z = z • ket S := by simp [ket]
      rw [hs, map_smul]
      simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply, Y_ket, (word_vacuum S.sort).2 n hn,
        smul_zero]
  have rightIdentity (A : VertexOperator ℂ Fock) :
      (signedNormalMinusOne 1 A identityField).1 = A := by
    apply HVertexOperator.coeff_inj
    funext power
    apply LinearMap.ext
    intro v
    rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff,
      (signedNormalMinusOne 1 A identityField).2]
    simp only [one_smul]
    have identityModes (n : ℤ) : ((identityField : VertexOperator ℂ Fock) [[n]]) =
        if n = -1 then LinearMap.id else 0 := by
      rw [identityField, VertexOperator.ncoeff_of_coeff]
      simp only [show -n - 1 = 0 ↔ n = -1 by omega]
    let index : ℤ := -power - 1
    change (∑ᶠ offset : ℕ, (A [[-(offset : ℤ) - 1]])
        (((identityField : VertexOperator ℂ Fock) [[index + offset]]) v)) +
      (∑ᶠ offset : ℕ, ((identityField : VertexOperator ℂ Fock) [[index - offset - 1]])
        ((A [[offset]]) v)) = (A [[index]]) v
    by_cases positive : 0 ≤ index
    · have firstZero : ∀ offset : ℕ,
          (A [[-(offset : ℤ) - 1]])
            (((identityField : VertexOperator ℂ Fock) [[index + offset]]) v) = 0 := by
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
            ((A [[offset]]) v) = 0 := by
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
  refine ⟨by simp [vacuum, Y_ket, wordField], hcreation, hcreative, ?_, ?_⟩
  · intro n
    have hY : Y (ket {0}) = generatingField false := by
      rw [Y_ket]
      simp only [Finset.sort_singleton, wordField, List.length_nil, pow_zero]
      change (signedNormalMinusOne 1 (dividedDerivative 0 (generatingField _)) identityField).1 = _
      rw [rightIdentity]
      apply VertexOperator.ext
      intro v
      simp [dividedDerivative]
    rw [hY, generating_modes]
    rfl
  · intro n
    have hY : Y (ket {1}) = generatingField true := by
      rw [Y_ket]
      simp only [Finset.sort_singleton, wordField, List.length_nil, pow_zero]
      change (signedNormalMinusOne 1 (dividedDerivative 0 (generatingField _)) identityField).1 = _
      rw [rightIdentity]
      apply VertexOperator.ext
      intro v
      simp [dividedDerivative]
    rw [hY, generating_modes]
    rfl

open private L_vacuum from D5.S3.Quantum.Fermionic.BcGhostVirasoro

set_option maxHeartbeats 800000 in
-- The finite-sum telescope and linear extension share this declaration's budget.
/-- The translation is the original ghost Virasoro minus-one mode. -/
theorem stateField_translation :
    BcGhostVirasoro.L (-1) vacuum = 0 ∧ ∀ (a : Fock) (n : ℤ),
      BcGhostVirasoro.L (-1) * ((Y a) [[n]]) -
          ((Y a) [[n]]) * BcGhostVirasoro.L (-1) =
        -(n : ℂ) • ((Y a) [[n - 1]]) := by
  classical
  have generatorLaw (species : Bool) (n : ℤ) :
      BcGhostVirasoro.L (-1) * generatingMode species n -
          generatingMode species n * BcGhostVirasoro.L (-1) =
        -(n : ℂ) • generatingMode species (n - 1) := by
    cases species
    · have hi : (-1 : ℤ) - (n - 1) = -n := by omega
      have hj : (-1 : ℤ) + (n - 1) = n - 1 - 1 := by omega
      simpa only [generatingMode, Bool.false_eq_true, ite_false, hi, hj, Int.cast_neg] using
        BcGhostVirasoro.ward_b (-1) (n - 1)
    · have hi : (-2 : ℤ) * (-1) - (n + 2) = -n := by omega
      have hj : (-1 : ℤ) + (n + 2) = n - 1 + 2 := by omega
      simpa only [generatingMode, ite_true, hi, hj, Int.cast_neg] using
        BcGhostVirasoro.ward_c (-1) (n + 2)
  have binomialShift (argument : ℤ) (order : ℕ) :
      Ring.choose argument order * (argument - order) =
        argument * Ring.choose (argument - 1) order := by
    have first := Ring.choose_smul_choose argument (n := order + 1) (k := order) (by omega)
    have second := Ring.choose_smul_choose argument (n := order + 1) (k := 1) (by omega)
    rw [Nat.choose_succ_self_right, Nat.add_sub_cancel_left, Ring.choose_one_right] at first
    rw [Nat.choose_one_right, Ring.choose_one_right, Nat.add_sub_cancel] at second
    exact first.symm.trans second
  have derivativeLaw (species : Bool) (order : ℕ) (n : ℤ) :
      BcGhostVirasoro.L (-1) * ((dividedDerivative order (generatingField species)) [[n]]) -
          ((dividedDerivative order (generatingField species)) [[n]]) * BcGhostVirasoro.L (-1) =
        -(n : ℂ) • ((dividedDerivative order (generatingField species)) [[n - 1]]) := by
    rw [derivative_modes, derivative_modes, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, ← smul_sub, generatorLaw, smul_smul]
    rw [show n - order - 1 = n - 1 - order by omega, smul_smul]
    have integerEquality := binomialShift (-n + order) order
    have complexEquality := congrArg (fun integer : ℤ => (integer : ℂ)) integerEquality
    push_cast at complexEquality
    have firstIndex : -n + (order : ℤ) - 1 = -n - 1 + order := by omega
    have secondIndex : -(n - 1) - 1 + (order : ℤ) = -n + order := by omega
    rw [firstIndex] at complexEquality
    rw [secondIndex]
    congr 1
    push_cast
    linear_combination -complexEquality
  have wordLaw : ∀ (w : List ℕ) (n : ℤ),
      BcGhostVirasoro.L (-1) * ((wordField w) [[n]]) -
          ((wordField w) [[n]]) * BcGhostVirasoro.L (-1) =
        -(n : ℂ) • ((wordField w) [[n - 1]]) := by
    intro w
    induction w with
    | nil =>
      intro n
      have identityModes (n : ℤ) : (identityField : VertexOperator ℂ Fock) [[n]] =
          if n = -1 then LinearMap.id else 0 := by
        rw [identityField, VertexOperator.ncoeff_of_coeff]
        simp only [show -n - 1 = 0 ↔ n = -1 by omega]
      simp only [wordField, identityModes]
      by_cases hz : n = 0
      · subst n
        simp
      · simp only [if_neg (show n - 1 ≠ -1 by omega), smul_zero]
        split_ifs <;> simp only [Module.End.mul_eq_comp, LinearMap.comp_id,
          LinearMap.id_comp, mul_zero, zero_mul, sub_self]
    | cons j tail ih =>
      intro n
      exact signedNormal_translation _ (BcGhostVirasoro.L (-1))
        (dividedDerivative (j / 2) (generatingField (j % 2 == 1)))
        (wordField tail) (derivativeLaw _ _) ih n
  refine ⟨?_, ?_⟩
  · rw [L_vacuum]
    norm_num
  · intro a n
    let defect : VertexOperator ℂ Fock →ₗ[ℂ] Module.End ℂ Fock := {
      toFun A := BcGhostVirasoro.L (-1) * (A [[n]]) - (A [[n]]) * BcGhostVirasoro.L (-1) +
        (n : ℂ) • (A [[n - 1]])
      map_add' A B := by
        simp only [map_add, Pi.add_apply, mul_add, add_mul, smul_add]
        abel
      map_smul' z A := by
        simp only [map_smul, RingHom.id_apply, Pi.smul_apply, Algebra.mul_smul_comm,
          Algebra.smul_mul_assoc, ← smul_sub, ← smul_add, smul_comm (n : ℂ) z] }
    have defect_apply (A : VertexOperator ℂ Fock) : defect A =
        BcGhostVirasoro.L (-1) * (A [[n]]) - (A [[n]]) * BcGhostVirasoro.L (-1) +
          (n : ℂ) • (A [[n - 1]]) := rfl
    have heq : defect.comp Y = 0 := by
      apply Finsupp.lhom_ext
      intro S z
      have hs : Finsupp.single S z = z • ket S := by simp [ket]
      simp only [LinearMap.comp_apply, hs, map_smul, Y_ket, LinearMap.zero_apply]
      suffices hzero : defect (wordField S.sort) = 0 by rw [hzero, smul_zero]
      rw [defect_apply, wordLaw]
      simp only [neg_smul, neg_add_cancel]
    have hd (v : Fock) : defect (Y v) = 0 := LinearMap.congr_fun heq v
    have h := hd a
    rw [defect_apply] at h
    simpa only [neg_smul] using eq_neg_iff_add_eq_zero.mpr h

private theorem forward_finite (A B : VertexOperator ℂ Fock) (start finish : ℤ) (v : Fock) :
    Function.HasFiniteSupport (fun i : ℕ => (A [[start - i]]) ((B [[finish + i]]) v)) := by
  exact D5.S3.VertexAlgebra.SignedFieldNormalProductLocality.forward_finite A B start finish v

private theorem reverse_finite (A B : VertexOperator ℂ Fock) (start : ℤ) (v : Fock) :
    Function.HasFiniteSupport (fun i : ℕ => (A [[start - i]]) ((B [[i]]) v)) := by
  exact D5.S3.VertexAlgebra.SignedFieldNormalProductLocality.reverse_finite A B start v

private theorem signedNormal_parity (sign x y : ℂ) (A B : VertexOperator ℂ Fock)
    (hA : ∀ n : ℤ, parity * (A [[n]]) = x • ((A [[n]]) * parity))
    (hB : ∀ n : ℤ, parity * (B [[n]]) = y • ((B [[n]]) * parity)) (n : ℤ) :
    parity * ((signedNormalMinusOne sign A B).1 [[n]]) =
      (x * y) • (((signedNormalMinusOne sign A B).1 [[n]]) * parity) := by
  have hA' (m : ℤ) (w : Fock) : parity ((A [[m]]) w) = x • (A [[m]]) (parity w) :=
    LinearMap.congr_fun (hA m) w
  have hB' (m : ℤ) (w : Fock) : parity ((B [[m]]) w) = y • (B [[m]]) (parity w) :=
    LinearMap.congr_fun (hB m) w
  apply LinearMap.ext
  intro v
  change parity (((signedNormalMinusOne sign A B).1 [[n]]) v) =
    (x * y) • ((signedNormalMinusOne sign A B).1 [[n]]) (parity v)
  rw [(signedNormalMinusOne sign A B).2, (signedNormalMinusOne sign A B).2,
    map_add, map_smul]
  have hf (w : Fock) : Function.HasFiniteSupport
      (fun i : ℕ => (A [[-(i : ℤ) - 1]]) ((B [[n + i]]) w)) := by
    simpa only [show ∀ i : ℕ, (-1 : ℤ) - i = -(i : ℤ) - 1 by intro i; omega] using
      forward_finite A B (-1) n w
  have hr (w : Fock) : Function.HasFiniteSupport
      (fun i : ℕ => (B [[n - i - 1]]) ((A [[i]]) w)) := by
    simpa only [show ∀ i : ℕ, n - 1 - i = n - i - 1 by intro i; omega] using
      reverse_finite B A (n - 1) w
  rw [map_finsum parity (hf v), map_finsum parity (hr v)]
  simp_rw [hA', hB', hA', map_smul, smul_smul]
  rw [show y * x = x * y by ring,
    ← smul_finsum' (x * y) (hf (parity v)), ← smul_finsum' (x * y) (hr (parity v))]
  module

open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock

/-- Parity compatibility holds on every state, including inhomogeneous sums. -/
theorem stateField_parity (a : Fock) (n : ℤ) :
    parity * ((Y a) [[n]]) = ((Y (parity a)) [[n]]) * parity := by
  classical
  have derivativeParity (species : Bool) (order : ℕ) (n : ℤ) :
      parity * ((dividedDerivative order (generatingField species)) [[n]]) =
        (-1 : ℂ) • (((dividedDerivative order (generatingField species)) [[n]]) * parity) := by
    have ho : parity * generatingMode species (n - order) =
        -(generatingMode species (n - order) * parity) := by
      cases species
      · exact eq_neg_of_add_eq_zero_left (ghost_parity (n - order - 1)).1
      · exact eq_neg_of_add_eq_zero_left (ghost_parity (n - order + 2)).2
    rw [derivative_modes, Algebra.mul_smul_comm, ho, Algebra.smul_mul_assoc]
    simp only [smul_neg, neg_one_smul]
  have wordParity : ∀ (w : List ℕ) (n : ℤ),
      parity * ((wordField w) [[n]]) =
        ((-1 : ℂ) ^ w.length) • (((wordField w) [[n]]) * parity) := by
    intro w
    induction w with
    | nil =>
      intro n
      have identityModes (n : ℤ) : (identityField : VertexOperator ℂ Fock) [[n]] =
          if n = -1 then LinearMap.id else 0 := by
        rw [identityField, VertexOperator.ncoeff_of_coeff]
        simp only [show -n - 1 = 0 ↔ n = -1 by omega]
      simp only [wordField, List.length_nil, pow_zero, one_smul, identityModes]
      split_ifs <;> simp only [Module.End.mul_eq_comp, LinearMap.comp_id,
        LinearMap.id_comp, mul_zero, zero_mul]
    | cons j tail ih =>
      intro n
      have h := signedNormal_parity ((-1 : ℂ) ^ tail.length) (-1)
        ((-1 : ℂ) ^ tail.length)
        (dividedDerivative (j / 2) (generatingField (j % 2 == 1)))
        (wordField tail) (derivativeParity _ _) ih n
      simpa only [wordField, List.length_cons, pow_succ, mul_comm (-1 : ℂ)] using h
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, Pi.add_apply, mul_add, add_mul, ha, hb]
  | single S z =>
    have hs : Finsupp.single S z = z • ket S := by simp [ket]
    simp only [hs, map_smul, Pi.smul_apply, parity_ket, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, Y_ket, wordParity, Finset.length_sort, smul_smul]

end D5.S3.Quantum.Fermionic.BcGhostStateField
