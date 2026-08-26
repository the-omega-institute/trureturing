/- GID: D5/S3/ConceptDynamics/ResidueCoding/ArbitraryCoordinateErasureCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ResidueCoding/ArbitraryCoordinateErasureCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Erasure faithfulness is controlled by the smallest retained product. -/

import D5.S3.Arith.Coding.ResidueCodeDynamicRange
import D5.S3.ConceptDynamics.ResidueCoding.RetainedResidueRecoveryCriterion

/- Library-search audit trail (2026-08-26):
   * Exact family hit `retained_residue_recovery_iff_product_capacity` proves
     recovery for one chosen retained coordinate set and is applied directly.
   * Exact family hit `prefixProduct` is the canonical product of the first
     sorted moduli; no parallel prefix-product definition is introduced.
   * `coordinate_deletion_robustness` is only a sufficient abstract distance
     condition and does not state the residue-capacity iff or worst survivor.
   * Pinned Mathlib hits `Finset.orderEmbOfFin`,
     `Finset.map_orderEmbOfFin_univ`, `Finset.prod_le_prod`, and
     `Finset.prod_coe_sort` prove the minimum-product survivor clause. No exact
     whole-theorem hit was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ResidueCoding.ArbitraryCoordinateErasureCriterion

open D5.S3.Arith.Coding.ResidueCodeDynamicRange
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.ResidueCoding.RetainedResidueRecoveryCriterion

/-- In an ascending pairwise-coprime residue system, every survivor set after
`s` coordinate erasures remains faithful exactly when the product of the first
`n - s` moduli covers the message range. That prefix is publicly certified as
the minimum-product survivor among all sets of the required size. -/
theorem arbitrary_coordinate_erasure_criterion
    (m : Nat -> Nat) (n : Nat) (s : Fin (n + 1)) (K : Nat)
    (hgreater : forall i, i < n -> 2 <= m i)
    (hstrict : forall i j, i < j -> j < n -> m i < m j)
    (hcoprime : forall i j, i < n -> j < n -> i ≠ j ->
      Nat.Coprime (m i) (m j)) :
    ((forall retained : Finset (Fin n), retained.card = n - s.val ->
        Function.Injective
          (jointReadout (fun i : retained =>
            fun x : Fin K => (x.val : ZMod (m i.1.val))))) <->
      K <= prefixProduct m (n - s.val)) /\
    forall retained : Finset (Fin n), retained.card = n - s.val ->
      prefixProduct m (n - s.val) <= ∏ i ∈ retained, m i.val := by
  classical
  have hprefixLength : n - s.val <= n := Nat.sub_le n s.val
  have hpositive : forall i, i < n -> 0 < m i := by
    intro i hi
    exact lt_of_lt_of_le (by omega) (hgreater i hi)
  have hmonotone : forall i j, i <= j -> j < n -> m i <= m j := by
    intro i j hij hj
    rcases hij.eq_or_lt with rfl | hij
    · exact le_rfl
    · exact (hstrict i j hij hj).le
  have minimumRetainedProduct : forall retained : Finset (Fin n),
      retained.card = n - s.val ->
        prefixProduct m (n - s.val) <= ∏ i ∈ retained, m i.val := by
    intro retained hcard
    let selection : Fin (n - s.val) ↪o Fin n := retained.orderEmbOfFin hcard
    have hprefixLeSelected :
        prefixProduct m (n - s.val) <= ∏ i : Fin (n - s.val), m (selection i) := by
      simp only [prefixProduct]
      apply Finset.prod_le_prod
      · intro i _
        exact Nat.zero_le _
      · intro i _
        exact hmonotone i (selection i)
          (fin_index_le_strict_mono selection selection.strictMono i)
          (selection i).isLt
    have hselectedProduct :
        (∏ i : Fin (n - s.val), m (selection i)) =
          ∏ i ∈ retained, m i.val := by
      rw [← Finset.map_orderEmbOfFin_univ retained hcard]
      rw [Finset.prod_map]
      rfl
    exact hprefixLeSelected.trans_eq hselectedProduct
  refine ⟨?_, minimumRetainedProduct⟩
  constructor
  · intro robust
    let prefixEmbedding : Fin (n - s.val) ↪ Fin n := Fin.castLEEmb hprefixLength
    let prefixPositions : Finset (Fin n) := Finset.univ.map prefixEmbedding
    have hprefixCard : prefixPositions.card = n - s.val := by
      simp only [prefixPositions, Finset.card_map, Finset.card_univ,
        Fintype.card_fin]
    have hprefixInjective := robust prefixPositions hprefixCard
    have hprefixPositive : forall i : prefixPositions, 0 < m i.1.val := by
      intro i
      exact hpositive i.1.val i.1.isLt
    have hprefixCoprime : Pairwise
        (fun i j : prefixPositions => Nat.Coprime (m i.1.val) (m j.1.val)) := by
      intro i j hij
      apply hcoprime i.1.val j.1.val i.1.isLt j.1.isLt
      intro hval
      apply hij
      apply Subtype.ext
      apply Fin.ext
      exact hval
    have hcapacity :=
      (retained_residue_recovery_iff_product_capacity
        (fun i : prefixPositions => m i.1.val) K
        hprefixPositive hprefixCoprime).mp hprefixInjective
    have hprefixProduct :
        (∏ i : prefixPositions, m i.1.val) = prefixProduct m (n - s.val) := by
      rw [Finset.prod_coe_sort prefixPositions (fun i : Fin n => m i.val)]
      simp only [prefixPositions, Finset.prod_map, prefixEmbedding, prefixProduct]
      apply Finset.prod_congr rfl
      intro i _
      rfl
    rwa [hprefixProduct] at hcapacity
  · intro hcapacity retained hcard
    have hretainedCapacity : K <= ∏ i ∈ retained, m i.val :=
      hcapacity.trans (minimumRetainedProduct retained hcard)
    have hretainedPositive : forall i : retained, 0 < m i.1.val := by
      intro i
      exact hpositive i.1.val i.1.isLt
    have hretainedCoprime : Pairwise
        (fun i j : retained => Nat.Coprime (m i.1.val) (m j.1.val)) := by
      intro i j hij
      apply hcoprime i.1.val j.1.val i.1.isLt j.1.isLt
      intro hval
      apply hij
      apply Subtype.ext
      apply Fin.ext
      exact hval
    apply (retained_residue_recovery_iff_product_capacity
      (fun i : retained => m i.1.val) K
      hretainedPositive hretainedCoprime).mpr
    rw [Finset.prod_coe_sort retained (fun i : Fin n => m i.val)]
    exact hretainedCapacity

#print axioms arbitrary_coordinate_erasure_criterion

end D5.S3.ConceptDynamics.ResidueCoding.ArbitraryCoordinateErasureCriterion
