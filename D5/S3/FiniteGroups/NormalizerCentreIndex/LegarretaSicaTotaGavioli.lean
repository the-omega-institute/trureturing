/- GID: D5/S3/FiniteGroups/NormalizerCentreIndex/LegarretaSicaTotaGavioli
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NormalizerCentreIndex/LegarretaSicaTotaGavioli
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/FiniteGroups/NormalizerCentreIndex/LegarretaSicaTotaGavioli.claim; result=D5/S3/FiniteGroups/NormalizerCentreIndex/LegarretaSicaTotaGavioli.result; claim=D5/S3/FiniteGroups/NormalizerCentreIndex/LegarretaSicaTotaGavioli.claim
   digest: No natural bound on centre index follows from normalizer-class count. -/

/-
admission_basis: open-problem-resolution (#27021; Refuted)
Direct frozen dependencies: D1 = D5/S3/FiniteGroups/SubgroupConjugacyRatio.subgroupProductEquiv; declaration statement_id = sha256:32ffffd6be6c7a8d7827155d004325c4e8a17f38b1e9b410d2449f8d60db56cd.
Per-declaration rows inherit the module admission basis; D1 refers to the identity above.
The claim inlines the source normalizer condition; proofs use the existing Mathlib predicate.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
Small.S | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Small.card_S, Small.card_center, Small.center_eq, Small.center_membership, Small.classEquiv, Small.classMap, Small.conjugacy_table, Small.el, Small.el_encode, Small.el_surjective, Small.encode, Small.eq_table_of_membership, Small.instDecidableMaskMem, Small.instDecidableMemSSubgroupNormTable, Small.instDecidableMemSSubgroupTable, Small.instFintypeS, Small.maskMem, Small.mask_closed, Small.normTable, Small.normTable_injective, Small.normTable_injective_aux, Small.normalizerWitness, Small.normalizer_table, Small.normalizer_table_eq, Small.omega_card, Small.s_card, Small.table, Small.table_exhaustive, Small.witnessEquiv, Small.witness_relation, coprime_orders, family_center_card, family_center_index, family_center_index_nat, family_finite_classes, family_nc, family_omega, family_s_card, family_strict, result
Small.action | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Small.S, Small.card_center, Small.center_eq, Small.center_membership, Small.classEquiv, Small.classMap, Small.conjugacy_table, Small.el, Small.el_encode, Small.encode, Small.eq_table_of_membership, Small.instDecidableMaskMem, Small.instDecidableMemSSubgroupNormTable, Small.instDecidableMemSSubgroupTable, Small.instFintypeS, Small.maskMem, Small.mask_closed, Small.normTable, Small.normTable_injective, Small.normTable_injective_aux, Small.normalizerWitness, Small.normalizer_table, Small.normalizer_table_eq, Small.omega_card, Small.s_card, Small.table, Small.table_exhaustive, Small.witnessEquiv, Small.witness_relation, family_center_card, family_center_index, family_center_index_nat, family_finite_classes, family_nc, family_omega, family_s_card, family_strict, result
Small.alpha | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Small.action
Small.card_S | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: coprime_orders, family_center_index_nat, family_nc
Small.card_center | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: family_center_card
Small.center_eq | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Small.card_center
Small.center_membership | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Small.center_eq
Small.classEquiv | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Small.omega_card, family_finite_classes
Small.classLabel | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Small.classEquiv, Small.classMap, Small.conjugacy_table, Small.witness_relation
Small.classMap | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Small.classEquiv
Small.conjugacy_table | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Small.witness_relation
Small.el | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Small.el_encode, Small.el_surjective, Small.eq_table_of_membership, Small.table_exhaustive
Small.el_encode | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Small.el_surjective
Small.el_surjective | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Small.eq_table_of_membership
Small.encode | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Small.el_encode, Small.el_surjective
Small.eq_table_of_membership | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Small.table_exhaustive
Small.instDecidableMaskMem | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Small.instDecidableMemSSubgroupTable, Small.mask_closed
Small.instDecidableMemSSubgroupNormTable | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Small.conjugacy_table, Small.normTable_injective_aux, Small.normalizer_table
Small.instDecidableMemSSubgroupTable | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Small.card_center, Small.center_membership, Small.instDecidableMemSSubgroupNormTable, Small.normalizer_table, Small.table_exhaustive
Small.instFintypeS | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Small.card_S, Small.card_center, Small.center_membership, Small.conjugacy_table, Small.el_encode, Small.mask_closed, Small.normTable_injective_aux, Small.normalizer_table, family_center_index, family_finite_classes, family_nc, family_omega, family_s_card
Small.mask | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Small.instDecidableMemSSubgroupTable, Small.mask_closed, Small.table
Small.maskMem | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Small.instDecidableMaskMem, Small.mask_closed, Small.table
Small.mask_closed | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Small.table
Small.normIndex | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Small.normPreimage_eq, Small.normalizerWitness, Small.normalizer_table, Small.normalizer_table_eq, Small.witnessEquiv
Small.normPreimage | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Small.normPreimage_eq, Small.normalizerWitness
Small.normPreimage_eq | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Small.normalizerWitness
Small.normTable | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Small.conjugacy_table, Small.instDecidableMemSSubgroupNormTable, Small.normTable_injective, Small.normTable_injective_aux, Small.normalizerWitness, Small.normalizer_table, Small.normalizer_table_eq, Small.witnessEquiv
Small.normTable_injective | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Small.witnessEquiv
Small.normTable_injective_aux | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Small.normTable_injective
Small.normalizerWitness | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Small.classEquiv, Small.witnessEquiv
Small.normalizer_table | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Small.normalizer_table_eq
Small.normalizer_table_eq | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Small.normalizerWitness, Small.witnessEquiv
Small.omega_card | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: family_omega
Small.s_card | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: family_s_card
Small.table | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Small.card_center, Small.center_eq, Small.center_membership, Small.eq_table_of_membership, Small.instDecidableMemSSubgroupTable, Small.normTable, Small.normalizerWitness, Small.normalizer_table, Small.normalizer_table_eq, Small.table_exhaustive, Small.witnessEquiv
Small.table_exhaustive | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Small.witnessEquiv
Small.witnessEquiv | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Small.classEquiv, Small.classMap, Small.s_card, Small.witness_relation
Small.witness_relation | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Small.classEquiv, Small.classMap
claim | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: result
coprime_orders | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: family_finite_classes, family_omega, family_s_card
family_center_card | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: family_center_index_nat
family_center_index | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: result
family_center_index_nat | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: family_center_index
family_finite_classes | proof_shape: content | escape_witness: ModularNormalizerFactors.Modular.pow_elt | Direct frozen dependencies: D1 | consumers: result
family_nc | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: result
family_omega | proof_shape: content | escape_witness: ModularNormalizerFactors.Modular.pow_elt | Direct frozen dependencies: D1 | consumers: family_strict, result
family_s_card | proof_shape: content | escape_witness: ModularNormalizerFactors.Modular.pow_elt | Direct frozen dependencies: D1 | consumers: family_strict
family_strict | proof_shape: content | escape_witness: ModularNormalizerFactors.Modular.pow_elt | Direct frozen dependencies: D1 | consumers: result
result | proof_shape: content | escape_witness: ModularNormalizerFactors.Modular.pow_elt | Direct frozen dependencies: D1 | consumers: terminal result
-/

import D5.S3.FiniteGroups.NormalizerCentreIndex.ModularNormalizerFactors
import Mathlib.GroupTheory.Nilpotent

open D5.S3.FiniteGroups.NormalizerCentreIndex.ModularNormalizerFactors


namespace D5.S3.FiniteGroups.NormalizerCentreIndex.LegarretaSicaTotaGavioli.Small

private def alpha : MulAut (Multiplicative (ZMod 8)) :=
  AddEquiv.toMultiplicative ((AddAut.mulLeft (⟨3, 3, by decide, by decide⟩ : (ZMod 8)ˣ)).toAdd)

private def action : Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod 8)) where
  toFun b := if b.toAdd=0 then 1 else alpha
  map_one' := rfl
  map_mul' b c := by
    ext x
    fin_cases b <;> fin_cases c <;> fin_cases x <;> decide

private abbrev S := Multiplicative (ZMod 8) ⋊[action] Multiplicative (ZMod 2)

private instance : Fintype S := Fintype.ofEquiv
  (Multiplicative (ZMod 8) × Multiplicative (ZMod 2)) SemidirectProduct.equivProd.symm

private def el (n : Fin 16) : S :=
  ⟨Multiplicative.ofAdd ((n.val/2 : ℕ) : ZMod 8),Multiplicative.ofAdd ((n.val%2 : ℕ) : ZMod 2)⟩

private def encode (g : S) : Fin 16 :=
  ⟨2*g.left.toAdd.val+g.right.toAdd.val,by
    have ha := ZMod.val_lt g.left.toAdd
    have hb := ZMod.val_lt g.right.toAdd
    omega⟩

private theorem el_encode : ∀ g : S, el (encode g) = g := by decide

private theorem el_surjective : Function.Surjective el := Function.RightInverse.surjective el_encode

private def mask (i : Fin 15) : ℕ :=
  ![1,3,33,257,513,8193,771,2313,4369,8481,33153,13107,21845,39321,65535] i

private def maskMem (n : ℕ) (g : S) : Prop := n.testBit (2*g.left.toAdd.val+g.right.toAdd.val) = true
private instance (n : ℕ) (g : S) : Decidable (maskMem n g) := inferInstanceAs (Decidable (_ = _))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem mask_closed : ∀ i : Fin 15,
    maskMem (mask i) 1 ∧
    (∀ x y : S, maskMem (mask i) x → maskMem (mask i) y → maskMem (mask i) (x*y)) ∧
    (∀ x : S, maskMem (mask i) x → maskMem (mask i) x⁻¹) := by decide

private def table (i : Fin 15) : Subgroup S where
  carrier := {g | maskMem (mask i) g}
  one_mem' := (mask_closed i).1
  mul_mem' := (mask_closed i).2.1 _ _
  inv_mem' := (mask_closed i).2.2 _

private instance (i : Fin 15) (g : S) : Decidable (g ∈ table i) :=
  inferInstanceAs (Decidable (maskMem (mask i) g))

private theorem eq_table_of_membership (H : Subgroup S) (i : Fin 15)
    (h : ∀ j : Fin 16, el j ∈ H ↔ el j ∈ table i) : H = table i := by
  ext g
  obtain ⟨j,rfl⟩ := el_surjective g
  exact h j

set_option maxHeartbeats 4000000 in
private theorem table_exhaustive (H : Subgroup S) : ∃ i : Fin 15, H = table i := by
  classical
  have h0 : el 0 ∈ H := H.one_mem
  by_cases h4 : el 4 ∈ H
  ·
    have h8 : el 8 ∈ H := by simpa only [show el 4 * el 4 = el 8 from SemidirectProduct.ext rfl rfl] using H.mul_mem h4 h4
    have h12 : el 12 ∈ H := by exact (Subgroup.inv_mem_iff H).mp h4
    by_cases h1 : el 1 ∈ H
    ·
      have h13 : el 13 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h12).mp h1
      have h9 : el 9 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h8).mp h1
      have h5 : el 5 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h4).mp h1
      by_cases h2 : el 2 ∈ H
      ·
        have h7 : el 7 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h5).mp h2
        have h3 : el 3 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h12).mp h7
        have h6 : el 6 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h12).mp h2
        have h10 : el 10 ∈ H := by exact (Subgroup.inv_mem_iff H).mp h6
        have h15 : el 15 ∈ H := by exact (Subgroup.inv_mem_iff H).mp h7
        have h11 : el 11 ∈ H := by exact (Subgroup.inv_mem_iff H).mp h3
        have h14 : el 14 ∈ H := by exact (Subgroup.inv_mem_iff H).mp h2
        refine ⟨14, eq_table_of_membership H 14 ?_⟩
        intro j
        fin_cases j
        · exact iff_of_true h0 (by decide)
        · exact iff_of_true h1 (by decide)
        · exact iff_of_true h2 (by decide)
        · exact iff_of_true h3 (by decide)
        · exact iff_of_true h4 (by decide)
        · exact iff_of_true h5 (by decide)
        · exact iff_of_true h6 (by decide)
        · exact iff_of_true h7 (by decide)
        · exact iff_of_true h8 (by decide)
        · exact iff_of_true h9 (by decide)
        · exact iff_of_true h10 (by decide)
        · exact iff_of_true h11 (by decide)
        · exact iff_of_true h12 (by decide)
        · exact iff_of_true h13 (by decide)
        · exact iff_of_true h14 (by decide)
        · exact iff_of_true h15 (by decide)
      · have h2n : el 2 ∉ H := h2
        have h7n : el 7 ∉ H := fun hj => h2n (by simpa only [show el 1 * el 7 = el 2 from SemidirectProduct.ext rfl rfl] using H.mul_mem h1 hj)
        have h3n : el 3 ∉ H := fun hj => h7n (by simpa only [show el 4 * el 3 = el 7 from SemidirectProduct.ext rfl rfl] using H.mul_mem h4 hj)
        have h6n : el 6 ∉ H := fun hj => h3n (by simpa only [show el 1 * el 6 = el 3 from SemidirectProduct.ext rfl rfl] using H.mul_mem h1 hj)
        have h14n : el 14 ∉ H := fun hj => h2n (by simpa only [show el 4 * el 14 = el 2 from SemidirectProduct.ext rfl rfl] using H.mul_mem h4 hj)
        have h11n : el 11 ∉ H := fun hj => h14n (by simpa only [show el 1 * el 11 = el 14 from SemidirectProduct.ext rfl rfl] using H.mul_mem h1 hj)
        have h10n : el 10 ∉ H := fun hj => h14n (by simpa only [show el 4 * el 10 = el 14 from SemidirectProduct.ext rfl rfl] using H.mul_mem h4 hj)
        have h15n : el 15 ∉ H := fun hj => h10n (by simpa only [show el 1 * el 15 = el 10 from SemidirectProduct.ext rfl rfl] using H.mul_mem h1 hj)
        refine ⟨11, eq_table_of_membership H 11 ?_⟩
        intro j
        fin_cases j
        · exact iff_of_true h0 (by decide)
        · exact iff_of_true h1 (by decide)
        · exact iff_of_false h2n (by decide)
        · exact iff_of_false h3n (by decide)
        · exact iff_of_true h4 (by decide)
        · exact iff_of_true h5 (by decide)
        · exact iff_of_false h6n (by decide)
        · exact iff_of_false h7n (by decide)
        · exact iff_of_true h8 (by decide)
        · exact iff_of_true h9 (by decide)
        · exact iff_of_false h10n (by decide)
        · exact iff_of_false h11n (by decide)
        · exact iff_of_true h12 (by decide)
        · exact iff_of_true h13 (by decide)
        · exact iff_of_false h14n (by decide)
        · exact iff_of_false h15n (by decide)
    · have h1n : el 1 ∉ H := h1
      have h13n : el 13 ∉ H := fun hj => h1n (by simpa only [show el 4 * el 13 = el 1 from SemidirectProduct.ext rfl rfl] using H.mul_mem h4 hj)
      have h9n : el 9 ∉ H := fun hj => h13n (by simpa only [show el 4 * el 9 = el 13 from SemidirectProduct.ext rfl rfl] using H.mul_mem h4 hj)
      have h5n : el 5 ∉ H := fun hj => h9n (by simpa only [show el 4 * el 5 = el 9 from SemidirectProduct.ext rfl rfl] using H.mul_mem h4 hj)
      by_cases h2 : el 2 ∈ H
      ·
        have h6 : el 6 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h12).mp h2
        have h10 : el 10 ∈ H := by exact (Subgroup.inv_mem_iff H).mp h6
        have h14 : el 14 ∈ H := by exact (Subgroup.inv_mem_iff H).mp h2
        have h3n : el 3 ∉ H := fun hj => h5n (by simpa only [show el 2 * el 3 = el 5 from SemidirectProduct.ext rfl rfl] using H.mul_mem h2 hj)
        have h7n : el 7 ∉ H := fun hj => h9n (by simpa only [show el 2 * el 7 = el 9 from SemidirectProduct.ext rfl rfl] using H.mul_mem h2 hj)
        have h11n : el 11 ∉ H := fun hj => h13n (by simpa only [show el 2 * el 11 = el 13 from SemidirectProduct.ext rfl rfl] using H.mul_mem h2 hj)
        have h15n : el 15 ∉ H := fun hj => h1n (by simpa only [show el 2 * el 15 = el 1 from SemidirectProduct.ext rfl rfl] using H.mul_mem h2 hj)
        refine ⟨12, eq_table_of_membership H 12 ?_⟩
        intro j
        fin_cases j
        · exact iff_of_true h0 (by decide)
        · exact iff_of_false h1n (by decide)
        · exact iff_of_true h2 (by decide)
        · exact iff_of_false h3n (by decide)
        · exact iff_of_true h4 (by decide)
        · exact iff_of_false h5n (by decide)
        · exact iff_of_true h6 (by decide)
        · exact iff_of_false h7n (by decide)
        · exact iff_of_true h8 (by decide)
        · exact iff_of_false h9n (by decide)
        · exact iff_of_true h10 (by decide)
        · exact iff_of_false h11n (by decide)
        · exact iff_of_true h12 (by decide)
        · exact iff_of_false h13n (by decide)
        · exact iff_of_true h14 (by decide)
        · exact iff_of_false h15n (by decide)
      · have h2n : el 2 ∉ H := h2
        have h14n : el 14 ∉ H := fun hj => h2n (by simpa only [show el 4 * el 14 = el 2 from SemidirectProduct.ext rfl rfl] using H.mul_mem h4 hj)
        have h10n : el 10 ∉ H := fun hj => h14n (by simpa only [show el 4 * el 10 = el 14 from SemidirectProduct.ext rfl rfl] using H.mul_mem h4 hj)
        have h6n : el 6 ∉ H := fun hj => h10n (by simpa only [show el 4 * el 6 = el 10 from SemidirectProduct.ext rfl rfl] using H.mul_mem h4 hj)
        by_cases h11 : el 11 ∈ H
        ·
          have h15 : el 15 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h4).mp h11
          have h3 : el 3 ∈ H := by exact (Subgroup.inv_mem_iff H).mp h11
          have h7 : el 7 ∈ H := by exact (Subgroup.inv_mem_iff H).mp h15
          refine ⟨13, eq_table_of_membership H 13 ?_⟩
          intro j
          fin_cases j
          · exact iff_of_true h0 (by decide)
          · exact iff_of_false h1n (by decide)
          · exact iff_of_false h2n (by decide)
          · exact iff_of_true h3 (by decide)
          · exact iff_of_true h4 (by decide)
          · exact iff_of_false h5n (by decide)
          · exact iff_of_false h6n (by decide)
          · exact iff_of_true h7 (by decide)
          · exact iff_of_true h8 (by decide)
          · exact iff_of_false h9n (by decide)
          · exact iff_of_false h10n (by decide)
          · exact iff_of_true h11 (by decide)
          · exact iff_of_true h12 (by decide)
          · exact iff_of_false h13n (by decide)
          · exact iff_of_false h14n (by decide)
          · exact iff_of_true h15 (by decide)
        · have h11n : el 11 ∉ H := h11
          have h7n : el 7 ∉ H := fun hj => h11n (by simpa only [show el 4 * el 7 = el 11 from SemidirectProduct.ext rfl rfl] using H.mul_mem h4 hj)
          have h3n : el 3 ∉ H := fun hj => h7n (by simpa only [show el 4 * el 3 = el 7 from SemidirectProduct.ext rfl rfl] using H.mul_mem h4 hj)
          have h15n : el 15 ∉ H := fun hj => h3n (by simpa only [show el 4 * el 15 = el 3 from SemidirectProduct.ext rfl rfl] using H.mul_mem h4 hj)
          refine ⟨8, eq_table_of_membership H 8 ?_⟩
          intro j
          fin_cases j
          · exact iff_of_true h0 (by decide)
          · exact iff_of_false h1n (by decide)
          · exact iff_of_false h2n (by decide)
          · exact iff_of_false h3n (by decide)
          · exact iff_of_true h4 (by decide)
          · exact iff_of_false h5n (by decide)
          · exact iff_of_false h6n (by decide)
          · exact iff_of_false h7n (by decide)
          · exact iff_of_true h8 (by decide)
          · exact iff_of_false h9n (by decide)
          · exact iff_of_false h10n (by decide)
          · exact iff_of_false h11n (by decide)
          · exact iff_of_true h12 (by decide)
          · exact iff_of_false h13n (by decide)
          · exact iff_of_false h14n (by decide)
          · exact iff_of_false h15n (by decide)
  · have h4n : el 4 ∉ H := h4
    by_cases h8 : el 8 ∈ H
    ·
      have h12n : el 12 ∉ H := fun hj => h4n (by simpa only [show el 8 * el 12 = el 4 from SemidirectProduct.ext rfl rfl] using H.mul_mem h8 hj)
      by_cases h1 : el 1 ∈ H
      ·
        have h9 : el 9 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h8).mp h1
        have h5n : el 5 ∉ H := fun hj => h12n (by simpa only [show el 1 * el 5 = el 12 from SemidirectProduct.ext rfl rfl] using H.mul_mem h1 hj)
        have h13n : el 13 ∉ H := fun hj => h4n (by simpa only [show el 1 * el 13 = el 4 from SemidirectProduct.ext rfl rfl] using H.mul_mem h1 hj)
        by_cases h2 : el 2 ∈ H
        ·
          have h7 : el 7 ∈ H := by exact (Subgroup.mul_mem_cancel_left H h1).mp h2
          have h3 : el 3 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h1).mp h2
          have h6 : el 6 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h1).mp h7
          have h4 : el 4 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h2).mp h6
          exact False.elim (h4n h4)
        · have h2n : el 2 ∉ H := h2
          have h7n : el 7 ∉ H := fun hj => h2n (by simpa only [show el 1 * el 7 = el 2 from SemidirectProduct.ext rfl rfl] using H.mul_mem h1 hj)
          have h10n : el 10 ∉ H := fun hj => h2n (by simpa only [show el 8 * el 10 = el 2 from SemidirectProduct.ext rfl rfl] using H.mul_mem h8 hj)
          have h15n : el 15 ∉ H := fun hj => h10n (by simpa only [show el 1 * el 15 = el 10 from SemidirectProduct.ext rfl rfl] using H.mul_mem h1 hj)
          by_cases h11 : el 11 ∈ H
          ·
            have h14 : el 14 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h11).mp h9
            have h3 : el 3 ∈ H := by exact (Subgroup.inv_mem_iff H).mp h11
            have h6 : el 6 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h8).mp h14
            have h2 : el 2 ∈ H := by exact (Subgroup.inv_mem_iff H).mp h14
            exact False.elim (h2n h2)
          · have h11n : el 11 ∉ H := h11
            have h14n : el 14 ∉ H := fun hj => h11n (by simpa only [show el 1 * el 14 = el 11 from SemidirectProduct.ext rfl rfl] using H.mul_mem h1 hj)
            have h3n : el 3 ∉ H := fun hj => h11n (by simpa only [show el 8 * el 3 = el 11 from SemidirectProduct.ext rfl rfl] using H.mul_mem h8 hj)
            have h6n : el 6 ∉ H := fun hj => h3n (by simpa only [show el 1 * el 6 = el 3 from SemidirectProduct.ext rfl rfl] using H.mul_mem h1 hj)
            refine ⟨6, eq_table_of_membership H 6 ?_⟩
            intro j
            fin_cases j
            · exact iff_of_true h0 (by decide)
            · exact iff_of_true h1 (by decide)
            · exact iff_of_false h2n (by decide)
            · exact iff_of_false h3n (by decide)
            · exact iff_of_false h4n (by decide)
            · exact iff_of_false h5n (by decide)
            · exact iff_of_false h6n (by decide)
            · exact iff_of_false h7n (by decide)
            · exact iff_of_true h8 (by decide)
            · exact iff_of_true h9 (by decide)
            · exact iff_of_false h10n (by decide)
            · exact iff_of_false h11n (by decide)
            · exact iff_of_false h12n (by decide)
            · exact iff_of_false h13n (by decide)
            · exact iff_of_false h14n (by decide)
            · exact iff_of_false h15n (by decide)
      · have h1n : el 1 ∉ H := h1
        have h9n : el 9 ∉ H := fun hj => h1n (by simpa only [show el 8 * el 9 = el 1 from SemidirectProduct.ext rfl rfl] using H.mul_mem h8 hj)
        by_cases h3 : el 3 ∈ H
        ·
          have h11 : el 11 ∈ H := by exact (Subgroup.inv_mem_iff H).mp h3
          have h2n : el 2 ∉ H := fun hj => h9n (by simpa only [show el 3 * el 2 = el 9 from SemidirectProduct.ext rfl rfl] using H.mul_mem h3 hj)
          have h7n : el 7 ∉ H := fun hj => h4n (by simpa only [show el 3 * el 7 = el 4 from SemidirectProduct.ext rfl rfl] using H.mul_mem h3 hj)
          have h10n : el 10 ∉ H := fun hj => h1n (by simpa only [show el 3 * el 10 = el 1 from SemidirectProduct.ext rfl rfl] using H.mul_mem h3 hj)
          have h15n : el 15 ∉ H := fun hj => h12n (by simpa only [show el 3 * el 15 = el 12 from SemidirectProduct.ext rfl rfl] using H.mul_mem h3 hj)
          by_cases h13 : el 13 ∈ H
          ·
            have h6 : el 6 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h13).mp h3
            have h5 : el 5 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h8).mp h13
            have h14 : el 14 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h8).mp h6
            have h10 : el 10 ∈ H := by exact (Subgroup.inv_mem_iff H).mp h6
            exact False.elim (h10n h10)
          · have h13n : el 13 ∉ H := h13
            have h14n : el 14 ∉ H := fun hj => h13n (by simpa only [show el 3 * el 14 = el 13 from SemidirectProduct.ext rfl rfl] using H.mul_mem h3 hj)
            have h5n : el 5 ∉ H := fun hj => h14n (by simpa only [show el 3 * el 5 = el 14 from SemidirectProduct.ext rfl rfl] using H.mul_mem h3 hj)
            have h6n : el 6 ∉ H := fun hj => h5n (by simpa only [show el 3 * el 6 = el 5 from SemidirectProduct.ext rfl rfl] using H.mul_mem h3 hj)
            refine ⟨7, eq_table_of_membership H 7 ?_⟩
            intro j
            fin_cases j
            · exact iff_of_true h0 (by decide)
            · exact iff_of_false h1n (by decide)
            · exact iff_of_false h2n (by decide)
            · exact iff_of_true h3 (by decide)
            · exact iff_of_false h4n (by decide)
            · exact iff_of_false h5n (by decide)
            · exact iff_of_false h6n (by decide)
            · exact iff_of_false h7n (by decide)
            · exact iff_of_true h8 (by decide)
            · exact iff_of_false h9n (by decide)
            · exact iff_of_false h10n (by decide)
            · exact iff_of_true h11 (by decide)
            · exact iff_of_false h12n (by decide)
            · exact iff_of_false h13n (by decide)
            · exact iff_of_false h14n (by decide)
            · exact iff_of_false h15n (by decide)
        · have h3n : el 3 ∉ H := h3
          have h11n : el 11 ∉ H := fun hj => h3n (by simpa only [show el 8 * el 11 = el 3 from SemidirectProduct.ext rfl rfl] using H.mul_mem h8 hj)
          by_cases h5 : el 5 ∈ H
          ·
            have h13 : el 13 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h8).mp h5
            have h2n : el 2 ∉ H := fun hj => h11n (by simpa only [show el 5 * el 2 = el 11 from SemidirectProduct.ext rfl rfl] using H.mul_mem h5 hj)
            have h10n : el 10 ∉ H := fun hj => h3n (by simpa only [show el 5 * el 10 = el 3 from SemidirectProduct.ext rfl rfl] using H.mul_mem h5 hj)
            by_cases h14 : el 14 ∈ H
            ·
              have h15 : el 15 ∈ H := by exact (Subgroup.mul_mem_cancel_left H h5).mp h14
              have h6 : el 6 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h8).mp h14
              have h7 : el 7 ∈ H := by exact (Subgroup.inv_mem_iff H).mp h15
              have h11 : el 11 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h5).mp h6
              exact False.elim (h11n h11)
            · have h14n : el 14 ∉ H := h14
              have h15n : el 15 ∉ H := fun hj => h14n (by simpa only [show el 5 * el 15 = el 14 from SemidirectProduct.ext rfl rfl] using H.mul_mem h5 hj)
              have h6n : el 6 ∉ H := fun hj => h14n (by simpa only [show el 8 * el 6 = el 14 from SemidirectProduct.ext rfl rfl] using H.mul_mem h8 hj)
              have h7n : el 7 ∉ H := fun hj => h6n (by simpa only [show el 5 * el 7 = el 6 from SemidirectProduct.ext rfl rfl] using H.mul_mem h5 hj)
              refine ⟨9, eq_table_of_membership H 9 ?_⟩
              intro j
              fin_cases j
              · exact iff_of_true h0 (by decide)
              · exact iff_of_false h1n (by decide)
              · exact iff_of_false h2n (by decide)
              · exact iff_of_false h3n (by decide)
              · exact iff_of_false h4n (by decide)
              · exact iff_of_true h5 (by decide)
              · exact iff_of_false h6n (by decide)
              · exact iff_of_false h7n (by decide)
              · exact iff_of_true h8 (by decide)
              · exact iff_of_false h9n (by decide)
              · exact iff_of_false h10n (by decide)
              · exact iff_of_false h11n (by decide)
              · exact iff_of_false h12n (by decide)
              · exact iff_of_true h13 (by decide)
              · exact iff_of_false h14n (by decide)
              · exact iff_of_false h15n (by decide)
          · have h5n : el 5 ∉ H := h5
            have h13n : el 13 ∉ H := fun hj => h5n (by simpa only [show el 8 * el 13 = el 5 from SemidirectProduct.ext rfl rfl] using H.mul_mem h8 hj)
            by_cases h7 : el 7 ∈ H
            ·
              have h15 : el 15 ∈ H := by exact (Subgroup.inv_mem_iff H).mp h7
              have h2n : el 2 ∉ H := fun hj => h13n (by simpa only [show el 7 * el 2 = el 13 from SemidirectProduct.ext rfl rfl] using H.mul_mem h7 hj)
              have h6n : el 6 ∉ H := fun hj => h9n (by simpa only [show el 7 * el 6 = el 9 from SemidirectProduct.ext rfl rfl] using H.mul_mem h7 hj)
              have h10n : el 10 ∉ H := fun hj => h5n (by simpa only [show el 7 * el 10 = el 5 from SemidirectProduct.ext rfl rfl] using H.mul_mem h7 hj)
              have h14n : el 14 ∉ H := fun hj => h1n (by simpa only [show el 7 * el 14 = el 1 from SemidirectProduct.ext rfl rfl] using H.mul_mem h7 hj)
              refine ⟨10, eq_table_of_membership H 10 ?_⟩
              intro j
              fin_cases j
              · exact iff_of_true h0 (by decide)
              · exact iff_of_false h1n (by decide)
              · exact iff_of_false h2n (by decide)
              · exact iff_of_false h3n (by decide)
              · exact iff_of_false h4n (by decide)
              · exact iff_of_false h5n (by decide)
              · exact iff_of_false h6n (by decide)
              · exact iff_of_true h7 (by decide)
              · exact iff_of_true h8 (by decide)
              · exact iff_of_false h9n (by decide)
              · exact iff_of_false h10n (by decide)
              · exact iff_of_false h11n (by decide)
              · exact iff_of_false h12n (by decide)
              · exact iff_of_false h13n (by decide)
              · exact iff_of_false h14n (by decide)
              · exact iff_of_true h15 (by decide)
            · have h7n : el 7 ∉ H := h7
              have h15n : el 15 ∉ H := fun hj => h7n (by simpa only [show el 8 * el 15 = el 7 from SemidirectProduct.ext rfl rfl] using H.mul_mem h8 hj)
              by_cases h2 : el 2 ∈ H
              ·
                have h4 : el 4 ∈ H := by simpa only [show el 2 * el 2 = el 4 from SemidirectProduct.ext rfl rfl] using H.mul_mem h2 h2
                exact False.elim (h4n h4)
              · have h2n : el 2 ∉ H := h2
                have h10n : el 10 ∉ H := fun hj => h2n (by simpa only [show el 8 * el 10 = el 2 from SemidirectProduct.ext rfl rfl] using H.mul_mem h8 hj)
                by_cases h6 : el 6 ∈ H
                ·
                  have h12 : el 12 ∈ H := by simpa only [show el 6 * el 6 = el 12 from SemidirectProduct.ext rfl rfl] using H.mul_mem h6 h6
                  exact False.elim (h12n h12)
                · have h6n : el 6 ∉ H := h6
                  have h14n : el 14 ∉ H := fun hj => h6n (by simpa only [show el 8 * el 14 = el 6 from SemidirectProduct.ext rfl rfl] using H.mul_mem h8 hj)
                  refine ⟨3, eq_table_of_membership H 3 ?_⟩
                  intro j
                  fin_cases j
                  · exact iff_of_true h0 (by decide)
                  · exact iff_of_false h1n (by decide)
                  · exact iff_of_false h2n (by decide)
                  · exact iff_of_false h3n (by decide)
                  · exact iff_of_false h4n (by decide)
                  · exact iff_of_false h5n (by decide)
                  · exact iff_of_false h6n (by decide)
                  · exact iff_of_false h7n (by decide)
                  · exact iff_of_true h8 (by decide)
                  · exact iff_of_false h9n (by decide)
                  · exact iff_of_false h10n (by decide)
                  · exact iff_of_false h11n (by decide)
                  · exact iff_of_false h12n (by decide)
                  · exact iff_of_false h13n (by decide)
                  · exact iff_of_false h14n (by decide)
                  · exact iff_of_false h15n (by decide)
    · have h8n : el 8 ∉ H := h8
      by_cases h1 : el 1 ∈ H
      ·
        have h9n : el 9 ∉ H := fun hj => h8n (by simpa only [show el 1 * el 9 = el 8 from SemidirectProduct.ext rfl rfl] using H.mul_mem h1 hj)
        have h13n : el 13 ∉ H := fun hj => h4n (by simpa only [show el 1 * el 13 = el 4 from SemidirectProduct.ext rfl rfl] using H.mul_mem h1 hj)
        by_cases h2 : el 2 ∈ H
        ·
          have h7 : el 7 ∈ H := by exact (Subgroup.mul_mem_cancel_left H h1).mp h2
          have h3 : el 3 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h1).mp h2
          have h6 : el 6 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h1).mp h7
          have h4 : el 4 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h2).mp h6
          exact False.elim (h4n h4)
        · have h2n : el 2 ∉ H := h2
          have h7n : el 7 ∉ H := fun hj => h2n (by simpa only [show el 1 * el 7 = el 2 from SemidirectProduct.ext rfl rfl] using H.mul_mem h1 hj)
          by_cases h3 : el 3 ∈ H
          ·
            have h6 : el 6 ∈ H := by exact (Subgroup.mul_mem_cancel_left H h1).mp h3
            have h2 : el 2 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h1).mp h3
            exact False.elim (h2n h2)
          · have h3n : el 3 ∉ H := h3
            have h6n : el 6 ∉ H := fun hj => h3n (by simpa only [show el 1 * el 6 = el 3 from SemidirectProduct.ext rfl rfl] using H.mul_mem h1 hj)
            by_cases h5 : el 5 ∈ H
            ·
              have h12 : el 12 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h5).mp h1
              have h4 : el 4 ∈ H := by exact (Subgroup.inv_mem_iff H).mp h12
              exact False.elim (h4n h4)
            · have h5n : el 5 ∉ H := h5
              have h12n : el 12 ∉ H := fun hj => h5n (by simpa only [show el 1 * el 12 = el 5 from SemidirectProduct.ext rfl rfl] using H.mul_mem h1 hj)
              by_cases h10 : el 10 ∈ H
              ·
                have h15 : el 15 ∈ H := by exact (Subgroup.mul_mem_cancel_left H h1).mp h10
                have h11 : el 11 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h1).mp h10
                have h14 : el 14 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h1).mp h15
                have h4 : el 4 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h10).mp h14
                exact False.elim (h4n h4)
              · have h10n : el 10 ∉ H := h10
                have h15n : el 15 ∉ H := fun hj => h10n (by simpa only [show el 1 * el 15 = el 10 from SemidirectProduct.ext rfl rfl] using H.mul_mem h1 hj)
                by_cases h11 : el 11 ∈ H
                ·
                  have h14 : el 14 ∈ H := by exact (Subgroup.mul_mem_cancel_left H h1).mp h11
                  have h10 : el 10 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h1).mp h11
                  exact False.elim (h10n h10)
                · have h11n : el 11 ∉ H := h11
                  have h14n : el 14 ∉ H := fun hj => h11n (by simpa only [show el 1 * el 14 = el 11 from SemidirectProduct.ext rfl rfl] using H.mul_mem h1 hj)
                  refine ⟨1, eq_table_of_membership H 1 ?_⟩
                  intro j
                  fin_cases j
                  · exact iff_of_true h0 (by decide)
                  · exact iff_of_true h1 (by decide)
                  · exact iff_of_false h2n (by decide)
                  · exact iff_of_false h3n (by decide)
                  · exact iff_of_false h4n (by decide)
                  · exact iff_of_false h5n (by decide)
                  · exact iff_of_false h6n (by decide)
                  · exact iff_of_false h7n (by decide)
                  · exact iff_of_false h8n (by decide)
                  · exact iff_of_false h9n (by decide)
                  · exact iff_of_false h10n (by decide)
                  · exact iff_of_false h11n (by decide)
                  · exact iff_of_false h12n (by decide)
                  · exact iff_of_false h13n (by decide)
                  · exact iff_of_false h14n (by decide)
                  · exact iff_of_false h15n (by decide)
      · have h1n : el 1 ∉ H := h1
        by_cases h5 : el 5 ∈ H
        ·
          have h13n : el 13 ∉ H := fun hj => h8n (by simpa only [show el 5 * el 13 = el 8 from SemidirectProduct.ext rfl rfl] using H.mul_mem h5 hj)
          by_cases h2 : el 2 ∈ H
          ·
            have h4 : el 4 ∈ H := by simpa only [show el 2 * el 2 = el 4 from SemidirectProduct.ext rfl rfl] using H.mul_mem h2 h2
            exact False.elim (h4n h4)
          · have h2n : el 2 ∉ H := h2
            have h11n : el 11 ∉ H := fun hj => h2n (by simpa only [show el 5 * el 11 = el 2 from SemidirectProduct.ext rfl rfl] using H.mul_mem h5 hj)
            by_cases h3 : el 3 ∈ H
            ·
              have h8 : el 8 ∈ H := by simpa only [show el 3 * el 3 = el 8 from SemidirectProduct.ext rfl rfl] using H.mul_mem h3 h3
              exact False.elim (h8n h8)
            · have h3n : el 3 ∉ H := h3
              have h10n : el 10 ∉ H := fun hj => h3n (by simpa only [show el 5 * el 10 = el 3 from SemidirectProduct.ext rfl rfl] using H.mul_mem h5 hj)
              by_cases h6 : el 6 ∈ H
              ·
                have h7 : el 7 ∈ H := by exact (Subgroup.mul_mem_cancel_left H h5).mp h6
                have h11 : el 11 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h5).mp h6
                exact False.elim (h11n h11)
              · have h6n : el 6 ∉ H := h6
                have h7n : el 7 ∉ H := fun hj => h6n (by simpa only [show el 5 * el 7 = el 6 from SemidirectProduct.ext rfl rfl] using H.mul_mem h5 hj)
                by_cases h9 : el 9 ∈ H
                ·
                  have h12 : el 12 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h9).mp h5
                  have h4 : el 4 ∈ H := by exact (Subgroup.inv_mem_iff H).mp h12
                  exact False.elim (h4n h4)
                · have h9n : el 9 ∉ H := h9
                  have h12n : el 12 ∉ H := fun hj => h9n (by simpa only [show el 5 * el 12 = el 9 from SemidirectProduct.ext rfl rfl] using H.mul_mem h5 hj)
                  by_cases h14 : el 14 ∈ H
                  ·
                    have h15 : el 15 ∈ H := by exact (Subgroup.mul_mem_cancel_left H h5).mp h14
                    have h3 : el 3 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h5).mp h14
                    exact False.elim (h3n h3)
                  · have h14n : el 14 ∉ H := h14
                    have h15n : el 15 ∉ H := fun hj => h14n (by simpa only [show el 5 * el 15 = el 14 from SemidirectProduct.ext rfl rfl] using H.mul_mem h5 hj)
                    refine ⟨2, eq_table_of_membership H 2 ?_⟩
                    intro j
                    fin_cases j
                    · exact iff_of_true h0 (by decide)
                    · exact iff_of_false h1n (by decide)
                    · exact iff_of_false h2n (by decide)
                    · exact iff_of_false h3n (by decide)
                    · exact iff_of_false h4n (by decide)
                    · exact iff_of_true h5 (by decide)
                    · exact iff_of_false h6n (by decide)
                    · exact iff_of_false h7n (by decide)
                    · exact iff_of_false h8n (by decide)
                    · exact iff_of_false h9n (by decide)
                    · exact iff_of_false h10n (by decide)
                    · exact iff_of_false h11n (by decide)
                    · exact iff_of_false h12n (by decide)
                    · exact iff_of_false h13n (by decide)
                    · exact iff_of_false h14n (by decide)
                    · exact iff_of_false h15n (by decide)
        · have h5n : el 5 ∉ H := h5
          by_cases h9 : el 9 ∈ H
          ·
            by_cases h2 : el 2 ∈ H
            ·
              have h4 : el 4 ∈ H := by simpa only [show el 2 * el 2 = el 4 from SemidirectProduct.ext rfl rfl] using H.mul_mem h2 h2
              exact False.elim (h4n h4)
            · have h2n : el 2 ∉ H := h2
              have h15n : el 15 ∉ H := fun hj => h2n (by simpa only [show el 9 * el 15 = el 2 from SemidirectProduct.ext rfl rfl] using H.mul_mem h9 hj)
              by_cases h3 : el 3 ∈ H
              ·
                have h8 : el 8 ∈ H := by simpa only [show el 3 * el 3 = el 8 from SemidirectProduct.ext rfl rfl] using H.mul_mem h3 h3
                exact False.elim (h8n h8)
              · have h3n : el 3 ∉ H := h3
                have h14n : el 14 ∉ H := fun hj => h3n (by simpa only [show el 9 * el 14 = el 3 from SemidirectProduct.ext rfl rfl] using H.mul_mem h9 hj)
                by_cases h6 : el 6 ∈ H
                ·
                  have h12 : el 12 ∈ H := by simpa only [show el 6 * el 6 = el 12 from SemidirectProduct.ext rfl rfl] using H.mul_mem h6 h6
                  have h15 : el 15 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h9).mp h6
                  exact False.elim (h15n h15)
                · have h6n : el 6 ∉ H := h6
                  have h11n : el 11 ∉ H := fun hj => h6n (by simpa only [show el 9 * el 11 = el 6 from SemidirectProduct.ext rfl rfl] using H.mul_mem h9 hj)
                  by_cases h10 : el 10 ∈ H
                  ·
                    have h7 : el 7 ∈ H := by exact (Subgroup.mul_mem_cancel_left H h9).mp h10
                    have h8 : el 8 ∈ H := by simpa only [show el 7 * el 7 = el 8 from SemidirectProduct.ext rfl rfl] using H.mul_mem h7 h7
                    exact False.elim (h8n h8)
                  · have h10n : el 10 ∉ H := h10
                    have h7n : el 7 ∉ H := fun hj => h10n (by simpa only [show el 9 * el 7 = el 10 from SemidirectProduct.ext rfl rfl] using H.mul_mem h9 hj)
                    by_cases h12 : el 12 ∈ H
                    ·
                      have h13 : el 13 ∈ H := by exact (Subgroup.mul_mem_cancel_left H h9).mp h12
                      have h5 : el 5 ∈ H := by exact (Subgroup.mul_mem_cancel_right H h9).mp h12
                      exact False.elim (h5n h5)
                    · have h12n : el 12 ∉ H := h12
                      have h13n : el 13 ∉ H := fun hj => h12n (by simpa only [show el 9 * el 13 = el 12 from SemidirectProduct.ext rfl rfl] using H.mul_mem h9 hj)
                      refine ⟨4, eq_table_of_membership H 4 ?_⟩
                      intro j
                      fin_cases j
                      · exact iff_of_true h0 (by decide)
                      · exact iff_of_false h1n (by decide)
                      · exact iff_of_false h2n (by decide)
                      · exact iff_of_false h3n (by decide)
                      · exact iff_of_false h4n (by decide)
                      · exact iff_of_false h5n (by decide)
                      · exact iff_of_false h6n (by decide)
                      · exact iff_of_false h7n (by decide)
                      · exact iff_of_false h8n (by decide)
                      · exact iff_of_true h9 (by decide)
                      · exact iff_of_false h10n (by decide)
                      · exact iff_of_false h11n (by decide)
                      · exact iff_of_false h12n (by decide)
                      · exact iff_of_false h13n (by decide)
                      · exact iff_of_false h14n (by decide)
                      · exact iff_of_false h15n (by decide)
          · have h9n : el 9 ∉ H := h9
            by_cases h13 : el 13 ∈ H
            ·
              have h12n : el 12 ∉ H := fun hj => h1n (by simpa only [show el 13 * el 12 = el 1 from SemidirectProduct.ext rfl rfl] using H.mul_mem h13 hj)
              by_cases h2 : el 2 ∈ H
              ·
                have h4 : el 4 ∈ H := by simpa only [show el 2 * el 2 = el 4 from SemidirectProduct.ext rfl rfl] using H.mul_mem h2 h2
                exact False.elim (h4n h4)
              · have h2n : el 2 ∉ H := h2
                have h3n : el 3 ∉ H := fun hj => h2n (by simpa only [show el 13 * el 3 = el 2 from SemidirectProduct.ext rfl rfl] using H.mul_mem h13 hj)
                by_cases h6 : el 6 ∈ H
                ·
                  have h12 : el 12 ∈ H := by simpa only [show el 6 * el 6 = el 12 from SemidirectProduct.ext rfl rfl] using H.mul_mem h6 h6
                  exact False.elim (h12n h12)
                · have h6n : el 6 ∉ H := h6
                  have h15n : el 15 ∉ H := fun hj => h6n (by simpa only [show el 13 * el 15 = el 6 from SemidirectProduct.ext rfl rfl] using H.mul_mem h13 hj)
                  by_cases h10 : el 10 ∈ H
                  ·
                    have h4 : el 4 ∈ H := by simpa only [show el 10 * el 10 = el 4 from SemidirectProduct.ext rfl rfl] using H.mul_mem h10 h10
                    exact False.elim (h4n h4)
                  · have h10n : el 10 ∉ H := h10
                    have h11n : el 11 ∉ H := fun hj => h10n (by simpa only [show el 13 * el 11 = el 10 from SemidirectProduct.ext rfl rfl] using H.mul_mem h13 hj)
                    by_cases h14 : el 14 ∈ H
                    ·
                      have h7 : el 7 ∈ H := by exact (Subgroup.mul_mem_cancel_left H h13).mp h14
                      have h8 : el 8 ∈ H := by simpa only [show el 7 * el 7 = el 8 from SemidirectProduct.ext rfl rfl] using H.mul_mem h7 h7
                      exact False.elim (h8n h8)
                    · have h14n : el 14 ∉ H := h14
                      have h7n : el 7 ∉ H := fun hj => h14n (by simpa only [show el 13 * el 7 = el 14 from SemidirectProduct.ext rfl rfl] using H.mul_mem h13 hj)
                      refine ⟨5, eq_table_of_membership H 5 ?_⟩
                      intro j
                      fin_cases j
                      · exact iff_of_true h0 (by decide)
                      · exact iff_of_false h1n (by decide)
                      · exact iff_of_false h2n (by decide)
                      · exact iff_of_false h3n (by decide)
                      · exact iff_of_false h4n (by decide)
                      · exact iff_of_false h5n (by decide)
                      · exact iff_of_false h6n (by decide)
                      · exact iff_of_false h7n (by decide)
                      · exact iff_of_false h8n (by decide)
                      · exact iff_of_false h9n (by decide)
                      · exact iff_of_false h10n (by decide)
                      · exact iff_of_false h11n (by decide)
                      · exact iff_of_false h12n (by decide)
                      · exact iff_of_true h13 (by decide)
                      · exact iff_of_false h14n (by decide)
                      · exact iff_of_false h15n (by decide)
            · have h13n : el 13 ∉ H := h13
              by_cases h2 : el 2 ∈ H
              ·
                have h4 : el 4 ∈ H := by simpa only [show el 2 * el 2 = el 4 from SemidirectProduct.ext rfl rfl] using H.mul_mem h2 h2
                exact False.elim (h4n h4)
              · have h2n : el 2 ∉ H := h2
                by_cases h3 : el 3 ∈ H
                ·
                  have h8 : el 8 ∈ H := by simpa only [show el 3 * el 3 = el 8 from SemidirectProduct.ext rfl rfl] using H.mul_mem h3 h3
                  exact False.elim (h8n h8)
                · have h3n : el 3 ∉ H := h3
                  by_cases h6 : el 6 ∈ H
                  ·
                    have h12 : el 12 ∈ H := by simpa only [show el 6 * el 6 = el 12 from SemidirectProduct.ext rfl rfl] using H.mul_mem h6 h6
                    have h2 : el 2 ∈ H := by simpa only [show el 6 * el 12 = el 2 from SemidirectProduct.ext rfl rfl] using H.mul_mem h6 h12
                    exact False.elim (h2n h2)
                  · have h6n : el 6 ∉ H := h6
                    by_cases h7 : el 7 ∈ H
                    ·
                      have h8 : el 8 ∈ H := by simpa only [show el 7 * el 7 = el 8 from SemidirectProduct.ext rfl rfl] using H.mul_mem h7 h7
                      exact False.elim (h8n h8)
                    · have h7n : el 7 ∉ H := h7
                      by_cases h10 : el 10 ∈ H
                      ·
                        have h4 : el 4 ∈ H := by simpa only [show el 10 * el 10 = el 4 from SemidirectProduct.ext rfl rfl] using H.mul_mem h10 h10
                        exact False.elim (h4n h4)
                      · have h10n : el 10 ∉ H := h10
                        by_cases h11 : el 11 ∈ H
                        ·
                          have h8 : el 8 ∈ H := by simpa only [show el 11 * el 11 = el 8 from SemidirectProduct.ext rfl rfl] using H.mul_mem h11 h11
                          exact False.elim (h8n h8)
                        · have h11n : el 11 ∉ H := h11
                          by_cases h12 : el 12 ∈ H
                          ·
                            have h8 : el 8 ∈ H := by simpa only [show el 12 * el 12 = el 8 from SemidirectProduct.ext rfl rfl] using H.mul_mem h12 h12
                            exact False.elim (h8n h8)
                          · have h12n : el 12 ∉ H := h12
                            by_cases h14 : el 14 ∈ H
                            ·
                              have h12 : el 12 ∈ H := by simpa only [show el 14 * el 14 = el 12 from SemidirectProduct.ext rfl rfl] using H.mul_mem h14 h14
                              exact False.elim (h12n h12)
                            · have h14n : el 14 ∉ H := h14
                              by_cases h15 : el 15 ∈ H
                              ·
                                have h8 : el 8 ∈ H := by simpa only [show el 15 * el 15 = el 8 from SemidirectProduct.ext rfl rfl] using H.mul_mem h15 h15
                                exact False.elim (h8n h8)
                              · have h15n : el 15 ∉ H := h15
                                refine ⟨0, eq_table_of_membership H 0 ?_⟩
                                intro j
                                fin_cases j
                                · exact iff_of_true h0 (by decide)
                                · exact iff_of_false h1n (by decide)
                                · exact iff_of_false h2n (by decide)
                                · exact iff_of_false h3n (by decide)
                                · exact iff_of_false h4n (by decide)
                                · exact iff_of_false h5n (by decide)
                                · exact iff_of_false h6n (by decide)
                                · exact iff_of_false h7n (by decide)
                                · exact iff_of_false h8n (by decide)
                                · exact iff_of_false h9n (by decide)
                                · exact iff_of_false h10n (by decide)
                                · exact iff_of_false h11n (by decide)
                                · exact iff_of_false h12n (by decide)
                                · exact iff_of_false h13n (by decide)
                                · exact iff_of_false h14n (by decide)
                                · exact iff_of_false h15n (by decide)



private def normTable (i : Fin 5) : Subgroup S := table (![14,11,13,6,9] i)
private instance (i : Fin 5) (g : S) : Decidable (g ∈ normTable i) :=
  inferInstanceAs (Decidable (g ∈ table (![14,11,13,6,9] i)))

private def normIndex (i : Fin 15) : Fin 5 := ![0,3,4,0,3,4,1,2,0,1,2,0,0,0,0] i

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem normalizer_table : ∀ i : Fin 15, ∀ g : S,
    g ∈ Subgroup.normalizer (table i) ↔ g ∈ normTable (normIndex i) := by
  simp only [Subgroup.mem_normalizer_iff]
  decide

private theorem normalizer_table_eq (i : Fin 15) :
    Subgroup.normalizer (table i) = normTable (normIndex i) :=
  Subgroup.ext (normalizer_table i)

set_option maxRecDepth 10000 in
private theorem normTable_injective_aux : ∀ i j : Fin 5,
    (∀ g : S, g ∈ normTable i ↔ g ∈ normTable j) → i=j := by decide

private theorem normTable_injective : Function.Injective normTable := by
  intro i j h
  exact normTable_injective_aux i j (fun g => by rw [h])

private def normPreimage (i : Fin 5) : Fin 15 := ![0,6,7,1,2] i

private theorem normPreimage_eq (i : Fin 5) : normIndex (normPreimage i) = i := by
  fin_cases i <;> rfl

private def normalizerWitness (i : Fin 5) : NormalizerWitness S :=
  ⟨normTable i, table (normPreimage i), by rw [normalizer_table_eq,normPreimage_eq]⟩

private noncomputable def witnessEquiv : Fin 5 ≃ NormalizerWitness S :=
  Equiv.ofBijective normalizerWitness ⟨by
    intro i j h
    exact normTable_injective (congrArg Subtype.val h),by
    rintro ⟨N,H,hH⟩
    obtain ⟨i,rfl⟩ := table_exhaustive H
    refine ⟨normIndex i,Subtype.ext ?_⟩
    change normTable (normIndex i) = N
    rw [← normalizer_table_eq,← hH]⟩

private def classLabel (i : Fin 5) : Fin 4 := ![0,1,2,3,3] i

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem conjugacy_table : ∀ i j : Fin 5,
    ConjEquivalent (normTable i) (normTable j) ↔ classLabel i = classLabel j := by
  unfold ConjEquivalent
  decide

private theorem witness_relation (a b : NormalizerWitness S) :
    ConjEquivalent a.1 b.1 ↔ classLabel (witnessEquiv.symm a) = classLabel (witnessEquiv.symm b) := by
  obtain ⟨i,rfl⟩ := witnessEquiv.surjective a
  obtain ⟨j,rfl⟩ := witnessEquiv.surjective b
  simp only [Equiv.symm_apply_apply]
  change ConjEquivalent (normTable i) (normTable j) ↔ _
  exact conjugacy_table i j

private noncomputable def classMap : NormalizerClass S → Fin 4 :=
  Quotient.lift (fun a => classLabel (witnessEquiv.symm a))
    (fun a b h => (witness_relation a b).mp h)

private noncomputable def classEquiv : NormalizerClass S ≃ Fin 4 :=
  Equiv.ofBijective classMap ⟨by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro H J h
    exact Quotient.sound ((witness_relation H J).mpr h),by
    intro i
    fin_cases i
    · exact ⟨Quotient.mk _ (normalizerWitness 0),by change classLabel (witnessEquiv.symm (witnessEquiv 0)) = 0; rw [Equiv.symm_apply_apply]; rfl⟩
    · exact ⟨Quotient.mk _ (normalizerWitness 1),by change classLabel (witnessEquiv.symm (witnessEquiv 1)) = 1; rw [Equiv.symm_apply_apply]; rfl⟩
    · exact ⟨Quotient.mk _ (normalizerWitness 2),by change classLabel (witnessEquiv.symm (witnessEquiv 2)) = 2; rw [Equiv.symm_apply_apply]; rfl⟩
    · exact ⟨Quotient.mk _ (normalizerWitness 3),by change classLabel (witnessEquiv.symm (witnessEquiv 3)) = 3; rw [Equiv.symm_apply_apply]; rfl⟩⟩

private theorem s_card : sCard S = 5 := by
  exact (Cardinal.mk_congr witnessEquiv.symm).trans (by simp)

private theorem omega_card : omega S = 4 := by
  exact (Nat.card_congr classEquiv).trans (by simp)

private theorem card_S : Nat.card S = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide

set_option maxRecDepth 10000 in
private theorem center_membership : ∀ g : S, g ∈ Subgroup.center S ↔ g ∈ table 3 := by
  simp only [Subgroup.mem_center_iff]
  decide

private theorem center_eq : Subgroup.center S = table 3 := Subgroup.ext center_membership

private theorem card_center : Nat.card (Subgroup.center S) = 2 := by
  rw [center_eq,Nat.card_eq_fintype_card]
  decide

end D5.S3.FiniteGroups.NormalizerCentreIndex.LegarretaSicaTotaGavioli.Small


namespace D5.S3.FiniteGroups.NormalizerCentreIndex.LegarretaSicaTotaGavioli

def claim : Prop :=
  ∃ B : ℕ → ℕ,
    ∀ (G : Type) [Group G],
      (∀ H : Subgroup G, H ≠ ⊤ → H < Subgroup.normalizer (H : Set G)) →
      Finite (NormalizerClass G) →
      ((omega G : ℕ) : Cardinal) < sCard G →
      centreIndex G ≤ ((B (omega G) : ℕ) : Cardinal)



variable (p : ℕ) [Fact p.Prime]

private theorem coprime_orders (ho : p ≠ 2) :
    (Nat.card Small.S).Coprime (Nat.card (Modular.P p)) := by
  rw [Small.card_S,Modular.card_p]
  have hc : Nat.Coprime 2 p := (Nat.prime_two.coprime_iff_not_dvd).mpr (by
    intro h
    exact ho ((Nat.prime_dvd_prime_iff_eq Nat.prime_two Fact.out).mp h).symm)
  simpa using hc.pow 4 3

private theorem family_s_card (ho : p ≠ 2) : sCard (Small.S × Modular.P p) = 10 := by
  have h := (counts_prod (coprime_orders p ho)).1
  rw [Small.s_card,Modular.s_card p ho] at h
  exact h.trans (by norm_num)

private theorem family_omega (ho : p ≠ 2) : omega (Small.S × Modular.P p) = 8 := by
  have h := (counts_prod (coprime_orders p ho)).2
  rw [Small.omega_card,Modular.omega_card p ho] at h
  exact h

private theorem family_center_card : Nat.card (Subgroup.center (Small.S × Modular.P p)) = 2*p := by
  rw [Subgroup.center_prod]
  rw [Nat.card_congr (Subgroup.prodEquiv (Subgroup.center Small.S)
    (Subgroup.center (Modular.P p))).toEquiv,Nat.card_prod]
  rw [Small.card_center,Modular.center_card]

private theorem family_center_index_nat : Nat.card ((Small.S × Modular.P p) ⧸ Subgroup.center (Small.S × Modular.P p)) = 8*p^2 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (Small.S × Modular.P p))
  rw [Nat.card_prod,Small.card_S,Modular.card_p,family_center_card] at h
  have hp : 0 < 2*p := Nat.mul_pos (by decide) (Fact.out : p.Prime).pos
  apply Nat.eq_of_mul_eq_mul_right hp
  calc
    Nat.card ((Small.S × Modular.P p) ⧸ Subgroup.center (Small.S × Modular.P p)) * (2*p) = 16*p^3 := h.symm
    _ = (8*p^2)*(2*p) := by ring

private theorem family_center_index : centreIndex (Small.S × Modular.P p) = ((8*p^2 : ℕ) : Cardinal) := by
  rw [centreIndex,← Nat.cast_card,family_center_index_nat]

private theorem family_nc : (∀ H : Subgroup (Small.S × Modular.P p), H ≠ ⊤ → H < Subgroup.normalizer (H : Set (Small.S × Modular.P p))) := by
  have hS : IsPGroup 2 Small.S :=
    IsPGroup.of_card_dvd_pow (n := 4) (by rw [Small.card_S]; decide)
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Group.IsNilpotent Small.S := hS.isNilpotent
  have hP : IsPGroup p (Modular.P p) :=
    IsPGroup.of_card_dvd_pow (n := 3) (by rw [Modular.card_p])
  letI : Group.IsNilpotent (Modular.P p) := hP.isNilpotent
  intro H hH
  exact Group.normalizerCondition_of_isNilpotent (G := (Small.S × Modular.P p)) H (lt_top_iff_ne_top.mpr hH)

private theorem family_finite_classes (ho : p ≠ 2) : Finite (NormalizerClass (Small.S × Modular.P p)) := by
  letI : Finite (NormalizerClass Small.S) := Finite.of_equiv (Fin 4) Small.classEquiv.symm
  letI : Finite (NormalizerClass (Modular.P p)) := Modular.finite_classes p ho
  exact finite_product_classes (coprime_orders p ho)

private theorem family_strict (ho : p ≠ 2) : ((omega (Small.S × Modular.P p) : ℕ) : Cardinal) < sCard (Small.S × Modular.P p) := by
  rw [family_s_card p ho,family_omega p ho]
  norm_num


theorem result : ¬ claim := by
  rintro ⟨B,hB⟩
  obtain ⟨p,hp,hprime⟩ := Nat.exists_infinite_primes (B 8 + 3)
  letI : Fact p.Prime := ⟨hprime⟩
  have ho : p ≠ 2 := by omega
  have h := hB (Small.S × Modular.P p) (family_nc p) (family_finite_classes p ho) (family_strict p ho)
  rw [family_center_index,family_omega p ho] at h
  have hnat : 8*p^2 ≤ B 8 := by exact_mod_cast h
  have hlt : B 8 < p := by exact Nat.lt_of_add_right_lt hp
  nlinarith

end D5.S3.FiniteGroups.NormalizerCentreIndex.LegarretaSicaTotaGavioli
