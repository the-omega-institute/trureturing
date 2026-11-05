/-
SOURCE-ONLY candidate against the thirteen fixed suppliers in inputs.json.
No native elaboration, kernel check, or official acceptance is claimed.
Native adaptation of the fixed Field/Product/P0/integer drafts remains pending.

The original occupation Fock, ghostNumber, and sorted wordField are unchanged.
The signed pointwise normal-product and finite-support proof pattern are the
ones of BcGhostStateField. That supplier retains Scott Carnahan's copyright
(c) 2025 and Apache-2.0 attribution and adapts ScottCarnahan/vertexAlg revision
4453e34ec390e82a0c789c731ada8f9a6e86bdea. Original repository and Mathlib
attributions are retained. This is a consumer of those constructions, with
no literature novelty claim and no new BV or Jacobi structure.
-/

import D5.S3.Quantum.Fermionic.BcGhostStateField
import D5.S3.Quantum.Fermionic.BcGhostCharge

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators VertexOperator

namespace D5.S3.Quantum.Fermionic.BcGhostStateFieldGhostNumber

open CountableOccupationFock BcGhostFock BcGhostCharge
open BcGhostStateField (Y)
open D5.S3.VertexAlgebra.FieldNormalProduct
open private signedNormalMinusOne wordField generatingField generatingMode
  derivative_modes Y_ket forward_finite reverse_finite from
  D5.S3.Quantum.Fermionic.BcGhostStateField
open private charge_sum number_ket from D5.S3.Quantum.Fermionic.BcGhostCharge

noncomputable section

/-- Charge commutes through the actual two pointwise finite halves. No support
condition on an infinite family of endomorphisms is used. -/
private theorem signedNormal_number (sign x y : ℂ) (A B : VertexOperator ℂ Fock)
    (hA : ∀ m : ℤ, ghostNumber * (A[[m]]) - (A[[m]]) * ghostNumber = x • (A[[m]]))
    (hB : ∀ m : ℤ, ghostNumber * (B[[m]]) - (B[[m]]) * ghostNumber = y • (B[[m]]))
    (n : ℤ) :
    ghostNumber * ((signedNormalMinusOne sign A B).1[[n]]) -
        ((signedNormalMinusOne sign A B).1[[n]]) * ghostNumber =
      (x + y) • ((signedNormalMinusOne sign A B).1[[n]]) := by
  have pair (U V : Module.End ℂ Fock) (r s : ℂ)
      (hU : ghostNumber * U - U * ghostNumber = r • U)
      (hV : ghostNumber * V - V * ghostNumber = s • V) :
      ghostNumber * (U * V) - (U * V) * ghostNumber = (r + s) • (U * V) := by
    calc
      _ = (ghostNumber * U - U * ghostNumber) * V +
          U * (ghostNumber * V - V * ghostNumber) := by noncomm_ring
      _ = _ := by
        rw [hU, hV, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, add_smul]
  have forwardLaw (i j : ℤ) :
      ghostNumber * ((A[[i]]) * (B[[j]])) -
          ((A[[i]]) * (B[[j]])) * ghostNumber = (x + y) • ((A[[i]]) * (B[[j]])) :=
    pair _ _ x y (hA i) (hB j)
  have reverseLaw (i j : ℤ) :
      ghostNumber * ((B[[i]]) * (A[[j]])) -
          ((B[[i]]) * (A[[j]])) * ghostNumber = (x + y) • ((B[[i]]) * (A[[j]])) := by
    simpa only [add_comm y x] using pair _ _ y x (hB i) (hA j)
  apply LinearMap.ext
  intro v
  have hf (w : Fock) : Function.HasFiniteSupport
      (fun i : ℕ => (A[[ -(i : ℤ) - 1]]) ((B[[n + i]]) w)) := by
    simpa only [show ∀ i : ℕ, (-1 : ℤ) - i = -(i : ℤ) - 1 by intro i; omega] using
      forward_finite A B (-1) n w
  have hr (w : Fock) : Function.HasFiniteSupport
      (fun i : ℕ => (B[[n - i - 1]]) ((A[[i]]) w)) := by
    simpa only [show ∀ i : ℕ, n - 1 - i = n - i - 1 by intro i; omega] using
      reverse_finite B A (n - 1) w
  have commuteSum (terms : ℕ → Module.End ℂ Fock)
      (finite : ∀ w, Function.HasFiniteSupport (fun i => terms i w)) :
      ghostNumber (∑ᶠ i, terms i v) - (∑ᶠ i, terms i (ghostNumber v)) =
        ∑ᶠ i, (ghostNumber * terms i - terms i * ghostNumber) v := by
    rw [map_finsum ghostNumber (finite v),
      ← finsum_sub_distrib ((finite v).fun_comp (map_zero ghostNumber))
        (finite (ghostNumber v))]
    rfl
  have ef := commuteSum (fun i => (A[[ -(i : ℤ) - 1]]) * (B[[n + i]])) hf
  have er := commuteSum (fun i => (B[[n - i - 1]]) * (A[[i]])) hr
  change ghostNumber (((signedNormalMinusOne sign A B).1[[n]]) v) -
      ((signedNormalMinusOne sign A B).1[[n]]) (ghostNumber v) =
    (x + y) • ((signedNormalMinusOne sign A B).1[[n]]) v
  simp only [(signedNormalMinusOne sign A B).2]
  rw [map_add, map_smul]
  rw [show ∀ a b c d : Fock, (a + sign • b) - (c + sign • d) =
    (a - c) + sign • (b - d) by intros; module]
  change ghostNumber (∑ᶠ i : ℕ, (A[[ -(i : ℤ) - 1]]) ((B[[n + i]]) v)) -
      (∑ᶠ i : ℕ, (A[[ -(i : ℤ) - 1]]) ((B[[n + i]]) (ghostNumber v))) = _ at ef
  change ghostNumber (∑ᶠ i : ℕ, (B[[n - i - 1]]) ((A[[i]]) v)) -
      (∑ᶠ i : ℕ, (B[[n - i - 1]]) ((A[[i]]) (ghostNumber v))) = _ at er
  rw [ef, er]
  simp_rw [forwardLaw, reverseLaw, LinearMap.smul_apply, Module.End.mul_apply]
  rw [← smul_finsum' (x + y) (hf v), ← smul_finsum' (x + y) (hr v)]
  module

/-- The mode derivation identity on EVERY original ghost state and EVERY
integer mode, including arbitrary finite sums of different ghost numbers. -/
theorem stateField_ghostNumber (a : Fock) (n : ℤ) :
    ghostNumber * ((Y a)[[n]]) - ((Y a)[[n]]) * ghostNumber =
      ((Y (ghostNumber a))[[n]]) := by
  classical
  have generatorLaw (species : Bool) (m : ℤ) :
      ghostNumber * generatingMode species m - generatingMode species m * ghostNumber =
        (if species then (1 : ℂ) else -1) • generatingMode species m := by
    cases species
    · simpa only [generatingMode, Bool.false_eq_true, ite_false, neg_one_smul] using
        ghost_number_relations.2.1 (m - 1)
    · simpa only [generatingMode, ite_true, one_smul] using
        ghost_number_relations.2.2 (m + 2)
  have derivativeLaw (j : ℕ) (m : ℤ) :
      ghostNumber * ((dividedDerivative (j / 2) (generatingField (j % 2 == 1)))[[m]]) -
          ((dividedDerivative (j / 2) (generatingField (j % 2 == 1)))[[m]]) * ghostNumber =
        (siteSign j : ℂ) •
          ((dividedDerivative (j / 2) (generatingField (j % 2 == 1)))[[m]]) := by
    have speciesDegree : (if j % 2 == 1 then (1 : ℂ) else -1) = (siteSign j : ℂ) := by
      by_cases he : j % 2 = 0
      · simp [siteSign, he]
      · have ho : j % 2 = 1 := by omega
        simp [siteSign, he, ho]
    simp only [derivative_modes]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
      ← smul_sub, generatorLaw, speciesDegree]
    exact smul_comm _ _ _
  have wordLaw : ∀ (w : List ℕ) (m : ℤ),
      ghostNumber * ((wordField w)[[m]]) - ((wordField w)[[m]]) * ghostNumber =
        (((w.map siteSign).sum : ℤ) : ℂ) • ((wordField w)[[m]]) := by
    intro w
    induction w with
    | nil =>
      intro m
      have identityModes : (identityField : VertexOperator ℂ Fock)[[m]] =
          if m = -1 then LinearMap.id else 0 := by
        rw [identityField, VertexOperator.ncoeff_of_coeff]
        simp only [show -m - 1 = 0 ↔ m = -1 by omega]
      simp only [wordField, List.map_nil, List.sum_nil, Int.cast_zero, zero_smul,
        identityModes]
      split_ifs <;> simp only [Module.End.mul_eq_comp, LinearMap.comp_id,
        LinearMap.id_comp, mul_zero, zero_mul, sub_self]
    | cons j tail ih =>
      intro m
      have h := signedNormal_number ((-1 : ℂ)^tail.length) (siteSign j : ℂ)
        (((tail.map siteSign).sum : ℤ) : ℂ)
        (dividedDerivative (j / 2) (generatingField (j % 2 == 1)))
        (wordField tail) (derivativeLaw j) ih m
      simpa only [wordField, List.map_cons, List.sum_cons, Int.cast_add] using h
  have sortedCharge (S : Finset ℕ) : (S.sort.map siteSign).sum = charge S := by
    induction S using Finset.eraseInduction with
    | H S ih =>
      by_cases empty : S = ∅
      · subst S
        simp [charge]
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
        calc
          (S.sort.map siteSign).sum = siteSign j + charge (S.erase j) := by
            rw [hsort, List.map_cons, List.sum_cons, ih j hj]
          _ = charge S := by
            rw [charge_sum S, charge_sum (S.erase j)]
            conv_rhs => rw [← Finset.insert_erase hj, Finset.sum_insert hnot]
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, Pi.add_apply, mul_add, add_mul]
    rw [show ∀ A B C E : Module.End ℂ Fock,
      (A + B) - (C + E) = (A - C) + (B - E) by intros; abel, ha, hb]
  | single S z =>
    have hs : Finsupp.single S z = z • ket S := by simp [ket]
    simp only [hs, map_smul, Pi.smul_apply, number_ket, Y_ket,
      Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← smul_sub,
      wordLaw, sortedCharge, smul_smul]

end
end D5.S3.Quantum.Fermionic.BcGhostStateFieldGhostNumber
