/- GID: D5/S3/ConceptDynamics/ResidueCoding/RetainedResidueRecoveryCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ResidueCoding/RetainedResidueRecoveryCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Retained coprime residues recover a bounded state exactly at product capacity. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import Mathlib.Data.ZMod.QuotientRing

/- Library-search audit trail (2026-08-25):
   * Exact current-tree hit `jointReadout` is the canonical dependent product
     readout and is used directly in the public statement below.
   * `ResidueCodeDynamicRange.maximum_dynamic_range_iff_min_distance` treats
     ascending prefix moduli and Hamming distance, while
     `HorizontalCompletenessDepth.residue_reading_injOn_iff_primorial_gt`
     treats only the first primes. Neither states arbitrary retained recovery.
   * Exact pinned-Mathlib hit `ZMod.prodEquivPi` supplies the finite-family
     Chinese remainder equivalence and is applied directly in the reverse proof.
   * Searches for retained coordinates, dependent residue readouts, and an
     injectivity/product-cardinality iff found no exact covering theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ResidueCoding.RetainedResidueRecoveryCriterion

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open scoped Function

/-- For any finite retained family of positive pairwise-coprime moduli, the
joint residue observation on states `0, ..., K - 1` is injective exactly when
the retained modulus product has capacity at least `K`. -/
theorem retained_residue_recovery_iff_product_capacity
    {ι : Type*} [Fintype ι] (m : ι -> Nat) (K : Nat)
    (hpositive : forall i, 0 < m i)
    (hcoprime : Pairwise (Nat.Coprime on m)) :
    Function.Injective
        (jointReadout (fun i : ι => fun x : Fin K => (x.val : ZMod (m i)))) ↔
      K ≤ ∏ i, m i := by
  classical
  letI (i : ι) : NeZero (m i) := ⟨Nat.ne_of_gt (hpositive i)⟩
  constructor
  · intro hinjective
    have hcard := Fintype.card_le_of_injective _ hinjective
    simpa using hcard
  · intro hcapacity x y hsame
    apply Fin.ext
    have hmod :
        (x.val : ZMod (∏ i, m i)) = (y.val : ZMod (∏ i, m i)) := by
      apply (ZMod.prodEquivPi m hcoprime).injective
      funext i
      simpa [jointReadout] using congrFun hsame i
    have hmodeq : x.val ≡ y.val [MOD ∏ i, m i] :=
      (ZMod.natCast_eq_natCast_iff x.val y.val (∏ i, m i)).mp hmod
    exact hmodeq.eq_of_lt_of_lt
      (x.isLt.trans_le hcapacity) (y.isLt.trans_le hcapacity)

#print axioms retained_residue_recovery_iff_product_capacity

end D5.S3.ConceptDynamics.ResidueCoding.RetainedResidueRecoveryCriterion
