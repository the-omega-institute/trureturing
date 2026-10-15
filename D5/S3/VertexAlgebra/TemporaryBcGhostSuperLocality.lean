import D5.S3.VertexAlgebra.TemporaryBcGhostSuperStateField
import D5.S3.VertexAlgebra.TemporarySuperFieldLocality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.BcGhostSuperLocality

open BcGhostFockSupport BcGhostSuperGenerators BcGhostSuperStateField
open FieldNormalProduct SuperFieldProducts SuperFieldLocality
open scoped VertexOperator

noncomputable section

theorem identity_superLocal (parity : ℕ) (operator : VertexOperator ℂ Carrier) :
    SuperLocal 0 parity identityField operator := by
  refine ⟨0, ?_⟩
  funext left right
  change superCommutator (koszul 0 parity) identityField operator left right = 0
  by_cases identityMode : left = -1 <;>
    simp [superCommutator, koszul, identity_modes, identityMode, ← Module.End.one_eq_id]

theorem site_superLocal (leftSite rightSite : ℕ) :
    SuperLocal 1 1 (siteField leftSite) (siteField rightSite) := by
  have currentLocal := current_super_locality (kindAt leftSite) (kindAt rightSite)
  have firstDerived := dividedDerivative_superLocal 1 1 (leftSite / 2)
    (currentField (kindAt leftSite)) (currentField (kindAt rightSite)) currentLocal
  have reversed := superLocal_symm 1 1 _ _ firstDerived
  have secondDerived := dividedDerivative_superLocal 1 1 (rightSite / 2)
    (currentField (kindAt rightSite)) (siteField leftSite) reversed
  exact superLocal_symm 1 1 _ _ secondDerived

theorem word_site_superLocal (word : List ℕ) (site : ℕ) :
    SuperLocal word.length 1 (wordField word) (siteField site) := by
  induction word generalizing site with
  | nil => exact identity_superLocal 1 (siteField site)
  | cons head tail inductionHypothesis =>
    have pairLocal := superLocal_symm tail.length 1 _ _ (inductionHypothesis head)
    have composite := normal_superLocal 1 tail.length 1 (siteField head) (wordField tail)
      (siteField site) (site_superLocal head site) (inductionHypothesis site) pairLocal
    simpa only [wordField, List.length_cons, koszul, Nat.one_mul,
      Nat.add_comm 1 tail.length] using composite

theorem word_word_superLocal (firstWord secondWord : List ℕ) :
    SuperLocal firstWord.length secondWord.length (wordField firstWord) (wordField secondWord) := by
  induction secondWord generalizing firstWord with
  | nil =>
    exact superLocal_symm 0 firstWord.length (identityField : VertexOperator ℂ Carrier)
      (wordField firstWord) (identity_superLocal firstWord.length (wordField firstWord))
  | cons head tail inductionHypothesis =>
    have headLocal := superLocal_symm firstWord.length 1 _ _
      (word_site_superLocal firstWord head)
    have tailLocal := superLocal_symm firstWord.length tail.length _ _
      (inductionHypothesis firstWord)
    have pairLocal := superLocal_symm tail.length 1 _ _ (word_site_superLocal tail head)
    have composite := normal_superLocal 1 tail.length firstWord.length (siteField head)
      (wordField tail) (wordField firstWord) headLocal tailLocal pairLocal
    have reversed := superLocal_symm (1 + tail.length) firstWord.length _ _ composite
    simpa only [wordField, List.length_cons, koszul, Nat.one_mul,
      Nat.add_comm 1 tail.length] using reversed

theorem stateField_superLocal (leftParity rightParity : ℕ) (left right : Carrier)
    (leftHomogeneous : left ∈ homogeneous leftParity)
    (rightHomogeneous : right ∈ homogeneous rightParity) :
    SuperLocal leftParity rightParity (Y left) (Y right) := by
  classical
  rw [stateField_expansion, stateField_expansion]
  apply superLocal_sum_left
  intro leftSites leftMember
  apply superLocal_smul_left
  apply superLocal_sum_right
  intro rightSites rightMember
  apply superLocal_smul_right
  rcases word_word_superLocal (basisWord leftSites) (basisWord rightSites) with ⟨order, killed⟩
  refine ⟨order, ?_⟩
  have leftGrade : (basisWord leftSites).length % 2 = leftParity % 2 := by
    simpa only [basisWord_length, subsetParity] using
      support_parity leftParity left leftHomogeneous leftSites leftMember
  have rightGrade : (basisWord rightSites).length % 2 = rightParity % 2 := by
    simpa only [basisWord_length, subsetParity] using
      support_parity rightParity right rightHomogeneous rightSites rightMember
  rw [← koszul_eq_of_mod (basisWord leftSites).length (basisWord rightSites).length
    leftParity rightParity leftGrade rightGrade]
  exact killed

theorem stateField_mixed_locality (left right : Carrier) :
    ∃ order : ℕ, SuperFieldProducts.delta^[order] (mixedSuperCommutator left right) = 0 := by
  classical
  have componentLocal (leftParity rightParity : ℕ) :
      SuperLocal leftParity rightParity (Y (parityPart leftParity left))
        (Y (parityPart rightParity right)) :=
    stateField_superLocal leftParity rightParity _ _
      (parityPart_mem leftParity left) (parityPart_mem rightParity right)
  let orders (leftParity rightParity : ℕ) : ℕ :=
    Classical.choose (componentLocal leftParity rightParity)
  let common : ℕ := ∑ leftParity ∈ Finset.range 2,
    ∑ rightParity ∈ Finset.range 2, orders leftParity rightParity
  refine ⟨common, ?_⟩
  rw [mixedSuperCommutator]
  change FieldNormalProductLocality.delta^[common] (∑ leftParity ∈ Finset.range 2,
    ∑ rightParity ∈ Finset.range 2, superCommutator (koszul leftParity rightParity)
      (Y (parityPart leftParity left)) (Y (parityPart rightParity right))) = 0
  rw [delta_iterate_eq_pow]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro leftParity leftMember
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro rightParity rightMember
  have innerBound : orders leftParity rightParity ≤
      ∑ grade ∈ Finset.range 2, orders leftParity grade :=
    Finset.single_le_sum (fun grade _ => Nat.zero_le (orders leftParity grade)) rightMember
  have outerBound : (∑ grade ∈ Finset.range 2, orders leftParity grade) ≤ common :=
    Finset.single_le_sum (fun grade _ => Nat.zero_le
      (∑ other ∈ Finset.range 2, orders grade other)) leftMember
  rw [← delta_iterate_eq_pow]
  exact locality_raise _ _ _ (orders leftParity rightParity) common
    (innerBound.trans outerBound) (Classical.choose_spec (componentLocal leftParity rightParity))

end
end D5.S3.VertexAlgebra.BcGhostSuperLocality
