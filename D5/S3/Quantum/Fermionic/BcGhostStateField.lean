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
The pointwise finite normal-product construction below adapts
D5.S3.VertexAlgebra.FieldNormalProduct (ScottCarnahan/vertexAlg,
revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea), with a scalar in the
reverse-ordered half. The ghost word construction uses the original occupation
carrier, not a transported vertex algebra. The intended all-state locality and
signed iterate theorem remain separate obligations until proved below.
-/

import D5.S3.Quantum.Fermionic.BcGhostVirasoro
import D5.S3.VertexAlgebra.FieldNormalProduct
import Mathlib.Data.Finset.Sort

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
        sign • (∑ᶠ offset : ℕ, (right [[index - offset - 1]]) ((left [[offset]]) vector))} := by
  classical
  have leftFinite (index : ℤ) (vector : Fock) : Function.HasFiniteSupport
      (fun offset : ℕ => (left [[-(offset : ℤ) - 1]]) ((right [[index + offset]]) vector)) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_)
    refine ⟨(-((HahnModule.of ℂ).symm (right vector)).order - index).toNat, ?_⟩
    intro offset member
    contrapose! member
    have vanish : (right [[index + offset]]) vector = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    simp [vanish]
  have rightFinite (index : ℤ) (vector : Fock) : Function.HasFiniteSupport
      (fun offset : ℕ => (right [[index - offset - 1]]) ((left [[offset]]) vector)) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_)
    refine ⟨(-((HahnModule.of ℂ).symm (left vector)).order - 1).toNat, ?_⟩
    intro offset member
    contrapose! member
    have vanish : (left [[offset]]) vector = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    simp [vanish]
  let coefficient (index : ℤ) : Module.End ℂ Fock := {
    toFun vector :=
      (∑ᶠ offset : ℕ, (left [[-(offset : ℤ) - 1]]) ((right [[index + offset]]) vector)) +
      sign • (∑ᶠ offset : ℕ, (right [[index - offset - 1]]) ((left [[offset]]) vector))
    map_add' first second := by
      simp only [map_add]
      rw [finsum_add_distrib (leftFinite index first) (leftFinite index second),
        finsum_add_distrib (rightFinite index first) (rightFinite index second)]
      module
    map_smul' scalar vector := by
      simp only [map_smul]
      rw [← smul_finsum' scalar (leftFinite index vector),
        ← smul_finsum' scalar (rightFinite index vector)]
      simp [smul_add, smul_comm] }
  have bounded (vector : Fock) :
      BddBelow (Function.support (fun power : ℤ => coefficient (-power - 1) vector)) := by
    let cutoff : ℕ := (-((HahnModule.of ℂ).symm (left vector)).order - 1).toNat
    let orders : Finset ℤ := (Finset.range (cutoff + 1)).image
      (fun offset : ℕ => ((HahnModule.of ℂ).symm
        (right ((left [[(offset : ℤ)]]) vector))).order - (offset : ℤ) - 1)
    let lower : ℤ := min ((HahnModule.of ℂ).symm (right vector)).order
      (orders.min' (by
        apply Finset.image_nonempty.mpr
        exact ⟨0, Finset.mem_range.mpr (by omega)⟩))
    refine ⟨lower, ?_⟩
    intro power member
    by_contra notLower
    have small : power < lower := lt_of_not_ge notLower
    have firstZero : ∀ offset : ℕ,
        (left [[-(offset : ℤ) - 1]]) ((right [[-power - 1 + offset]]) vector) = 0 := by
      intro offset
      have vanish : (right [[-power - 1 + offset]]) vector = 0 := by
        apply VertexOperator.ncoeff_eq_zero_of_lt_order
        dsimp [lower] at small
        omega
      simp [vanish]
    have secondZero : ∀ offset : ℕ,
        (right [[-power - 1 - offset - 1]]) ((left [[offset]]) vector) = 0 := by
      intro offset
      by_cases within : offset ≤ cutoff
      · have inOrders : ((HahnModule.of ℂ).symm
            (right ((left [[offset]]) vector))).order - offset - 1 ∈ orders := by
          exact Finset.mem_image.mpr ⟨offset, Finset.mem_range.mpr (by omega), rfl⟩
        have bound := Finset.min'_le orders _ inOrders
        apply VertexOperator.ncoeff_eq_zero_of_lt_order
        dsimp [lower] at small
        omega
      · have vanish : (left [[offset]]) vector = 0 := by
          apply VertexOperator.ncoeff_eq_zero_of_lt_order
          dsimp [cutoff] at within
          omega
        simp [vanish]
    exact member (by simp [coefficient, firstZero, secondZero])
  refine ⟨VertexOperator.of_coeff (fun power => coefficient (-power - 1)) bounded, ?_⟩
  intro index vector
  rw [VertexOperator.ncoeff_of_coeff]
  rw [show -(-index - 1) - 1 = index by omega]
  rfl

private def generatingMode (species : Bool) (n : ℤ) : Module.End ℂ Fock :=
  if species then c (n + 2) else b (n - 1)

private theorem generating_ket_tail (species : Bool) (S : Finset ℕ) (n : ℤ)
    (hn : (S.sup id : ℤ) + 3 ≤ n) : generatingMode species n (ket S) = 0 := by
  have hbound (j : ℕ) (hj : j ∈ S) : j ≤ S.sup id := Finset.le_sup (f := id) hj
  cases species
  · have hcut : ¬n - 1 ≤ -2 := by omega
    have hsite : 2 * (n - 1 + 1).toNat + 1 ∉ S := by
      intro h
      have := hbound _ h
      omega
    simp [generatingMode, b, hcut, annihilate_ket, hsite]
  · have hcut : ¬n + 2 ≤ 1 := by omega
    have hsite : 2 * (n + 2 - 2).toNat ∉ S := by
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
    have hindex : (-1 : ℤ) - j / 2 - 1 = -(j / 2 : ℕ) - 2 := by omega
    rw [hindex, (mode_correspondence (j / 2)).1, ← hj]
  · have hj : j = 2 * (j / 2) + 1 := by omega
    have hspecies : (j % 2 == 1) = true := by simp [show j % 2 = 1 by omega]
    simp only [hspecies, generatingMode, ite_true]
    have hindex : (-1 : ℤ) - j / 2 + 2 = 1 - (j / 2 : ℕ) := by omega
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
      simp only [map_smul, LinearMap.smul_apply, Y_ket, (word_vacuum S.sort).1,
        sorted_creator_vacuum]
  have hcreative (a : Fock) (n : ℤ) (hn : 0 ≤ n) : ((Y a) [[n]]) vacuum = 0 := by
    induction a using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simpa [map_add, ha, hb]
    | single S z =>
      have hs : Finsupp.single S z = z • ket S := by simp [ket]
      rw [hs, map_smul]
      simp only [map_smul, LinearMap.smul_apply, Y_ket, (word_vacuum S.sort).2 n hn,
        smul_zero]
  have rightIdentity (A : VertexOperator ℂ Fock) :
      (signedNormalMinusOne 1 A identityField).1 = A := by
    apply HVertexOperator.coeff_inj
    funext power
    apply LinearMap.ext
    intro v
    rw [VertexOperator.coeff_eq_ncoeff, (signedNormalMinusOne 1 A identityField).2]
    have identityModes (n : ℤ) : ((identityField : VertexOperator ℂ Fock) [[n]]) =
        if n = -1 then LinearMap.id else 0 := by
      rw [identityField, VertexOperator.ncoeff_of_coeff]
      simp only [show -n - 1 = 0 ↔ n = -1 by omega]
    simp only [identityModes, one_smul]
    by_cases hp : 0 ≤ power
    · rw [finsum_eq_single _ power.toNat]
      · simp [show -(power : ℤ) - 1 + power.toNat = -1 by omega,
          show (power.toNat : ℤ) = power by omega]
      · intro i hi
        simp [show -(power : ℤ) - 1 + i ≠ -1 by omega]
    · have firstZero : ∀ i : ℕ, (-power - 1 + i : ℤ) ≠ -1 := by intro i; omega
      simp only [firstZero, ite_false, LinearMap.zero_apply, map_zero, finsum_zero, zero_add]
      rw [finsum_eq_single _ (-power - 1).toNat]
      · simp [show ((-power - 1).toNat : ℤ) = -power - 1 by omega]
      · intro i hi
        simp [show (-power - 1 - i - 1 : ℤ) ≠ -1 by omega]
  refine ⟨by simp [vacuum, Y_ket, wordField], hcreation, hcreative, ?_, ?_⟩
  · intro n
    have hY : Y (ket {0}) = generatingField false := by
      rw [Y_ket]
      simp only [Finset.sort_singleton, wordField, List.length_nil, pow_zero]
      rw [rightIdentity]
      rfl
    rw [hY, generating_modes]
    rfl
  · intro n
    have hY : Y (ket {1}) = generatingField true := by
      rw [Y_ket]
      simp only [Finset.sort_singleton, wordField, List.length_nil, pow_zero]
      rw [rightIdentity]
      rfl
    rw [hY, generating_modes]
    rfl

end D5.S3.Quantum.Fermionic.BcGhostStateField
