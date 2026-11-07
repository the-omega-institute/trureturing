/- GID: D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalizer counts of odd-prime modular groups and coprime products. -/

/-
admission_basis: escape-witness
Direct frozen dependencies: D1 = D5/S3/FiniteGroups/SubgroupConjugacyRatio.subgroupProductEquiv; declaration statement_id = sha256:32ffffd6be6c7a8d7827155d004325c4e8a17f38b1e9b410d2449f8d60db56cd.
Per-declaration rows inherit the module admission basis; D1 refers to the identity above.
The uniform power formula Modular.pow_elt is used in the normalizer classification.
The source normalizer operation is Subgroup.normalizer; no forwarding definition is added.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27333.
ConjEquivalent | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: LegarretaSicaTotaGavioli.Small.classEquiv, LegarretaSicaTotaGavioli.Small.classMap, LegarretaSicaTotaGavioli.Small.conjugacy_table, LegarretaSicaTotaGavioli.Small.witness_relation, classProd, classProd_injective, conjEquivalent_eq_of_normal, conjEquivalent_refl, conjEquivalent_symm, conjEquivalent_trans, conj_prod_iff, normalizerSetoid
Modular.C | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.c_le_of_nonzero, Modular.card_C, Modular.center_card, Modular.center_eq_C, Modular.le_E_of_not_C_le, Modular.mem_C, Modular.normalizer_cases, Modular.normalizer_of_C_le, Modular.normalizer_of_le_C, Modular.normalizer_of_neither, Modular.not_C_le_Y, Modular.not_Y_le_C
Modular.E | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.E_le_normalizer, Modular.E_ne_top, Modular.all_witness_normal, Modular.le_E_of_not_C_le, Modular.mem_E, Modular.normalizer_Y, Modular.normalizer_cases, Modular.normalizer_of_neither, Modular.twoTable, Modular.twoWitness, Modular.witnessEquiv
Modular.E_le_normalizer | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.normalizer_of_neither
Modular.E_ne_top | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.witnessEquiv
Modular.P | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: LegarretaSicaTotaGavioli.coprime_orders, LegarretaSicaTotaGavioli.family_center_card, LegarretaSicaTotaGavioli.family_center_index, LegarretaSicaTotaGavioli.family_center_index_nat, LegarretaSicaTotaGavioli.family_finite_classes, LegarretaSicaTotaGavioli.family_nc, LegarretaSicaTotaGavioli.family_omega, LegarretaSicaTotaGavioli.family_s_card, LegarretaSicaTotaGavioli.family_strict, LegarretaSicaTotaGavioli.result, Modular.C, Modular.E, Modular.E_le_normalizer, Modular.E_ne_top, Modular.Y, Modular.all_witness_normal, Modular.c, Modular.c_injective, Modular.c_le_of_nonzero, Modular.card_C, Modular.card_p, Modular.center_card, Modular.center_eq_C, Modular.classEquiv, Modular.conj_as_c, Modular.finiteP, Modular.finite_classes, Modular.le_E_of_not_C_le, Modular.mem_C, Modular.mem_E, Modular.normalizer_Y, Modular.normalizer_cases, Modular.normalizer_of_C_le, Modular.normalizer_of_le_C, Modular.normalizer_of_neither, Modular.not_C_le_Y, Modular.not_Y_le_C, Modular.omega_card, Modular.redLeft, Modular.s_card, Modular.twoTable, Modular.twoWitness, Modular.witnessEquiv
Modular.Y | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.normalizer_Y, Modular.not_C_le_Y, Modular.not_Y_le_C, Modular.twoWitness
Modular.action | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: LegarretaSicaTotaGavioli.family_center_card, LegarretaSicaTotaGavioli.family_center_index, LegarretaSicaTotaGavioli.family_center_index_nat, LegarretaSicaTotaGavioli.family_finite_classes, LegarretaSicaTotaGavioli.family_nc, LegarretaSicaTotaGavioli.family_omega, LegarretaSicaTotaGavioli.family_s_card, LegarretaSicaTotaGavioli.family_strict, LegarretaSicaTotaGavioli.result, Modular.C, Modular.E, Modular.E_le_normalizer, Modular.E_ne_top, Modular.P, Modular.Y, Modular.all_witness_normal, Modular.c, Modular.c_injective, Modular.c_le_of_nonzero, Modular.card_C, Modular.card_p, Modular.center_card, Modular.center_eq_C, Modular.classEquiv, Modular.conj_as_c, Modular.conj_elt, Modular.elt_eq, Modular.finiteP, Modular.finite_classes, Modular.inv_elt, Modular.le_E_of_not_C_le, Modular.mem_C, Modular.mem_E, Modular.mul_elt, Modular.normalizer_Y, Modular.normalizer_cases, Modular.normalizer_of_C_le, Modular.normalizer_of_le_C, Modular.normalizer_of_neither, Modular.not_C_le_Y, Modular.not_Y_le_C, Modular.omega_card, Modular.pow_elt, Modular.pow_p, Modular.redLeft, Modular.s_card, Modular.twoTable, Modular.twoWitness, Modular.witnessEquiv
Modular.all_witness_normal | proof_shape: content | escape_witness: Modular.pow_elt | Direct frozen dependencies: none | consumers: Modular.classEquiv
Modular.aut | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.action
Modular.c | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.C, Modular.E_le_normalizer, Modular.c_injective, Modular.c_le_of_nonzero, Modular.card_C, Modular.conj_as_c, Modular.mem_C, Modular.normalizer_of_C_le, Modular.normalizer_of_le_C, Modular.normalizer_of_neither, Modular.not_C_le_Y
Modular.c_injective | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.card_C
Modular.c_le_of_nonzero | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.le_E_of_not_C_le, Modular.normalizer_of_neither
Modular.card_C | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.center_card
Modular.card_p | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: LegarretaSicaTotaGavioli.coprime_orders, LegarretaSicaTotaGavioli.family_center_index_nat, LegarretaSicaTotaGavioli.family_nc
Modular.center_card | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: LegarretaSicaTotaGavioli.family_center_card
Modular.center_eq_C | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.center_card
Modular.classEquiv | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.finite_classes, Modular.omega_card
Modular.conj_as_c | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.E_le_normalizer, Modular.normalizer_of_C_le, Modular.normalizer_of_le_C, Modular.normalizer_of_neither
Modular.conj_elt | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.conj_as_c
Modular.elt_eq | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.c_injective, Modular.mem_C, Modular.pow_elt, Modular.pow_p
Modular.finiteP | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: LegarretaSicaTotaGavioli.family_center_index, LegarretaSicaTotaGavioli.family_finite_classes, LegarretaSicaTotaGavioli.family_nc, LegarretaSicaTotaGavioli.family_omega, LegarretaSicaTotaGavioli.family_s_card
Modular.finite_classes | proof_shape: content | escape_witness: Modular.pow_elt | Direct frozen dependencies: none | consumers: LegarretaSicaTotaGavioli.family_finite_classes
Modular.inv_elt | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.conj_elt
Modular.le_E_of_not_C_le | proof_shape: content | escape_witness: Modular.pow_elt | Direct frozen dependencies: none | consumers: Modular.normalizer_of_neither
Modular.mem_C | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.center_eq_C, Modular.normalizer_of_le_C, Modular.normalizer_of_neither, Modular.not_Y_le_C
Modular.mem_E | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.E_le_normalizer, Modular.E_ne_top, Modular.le_E_of_not_C_le, Modular.normalizer_of_neither
Modular.mul_elt | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.conj_as_c, Modular.conj_elt, Modular.pow_elt
Modular.normalizer_Y | proof_shape: content | escape_witness: Modular.pow_elt | Direct frozen dependencies: none | consumers: Modular.twoWitness
Modular.normalizer_cases | proof_shape: content | escape_witness: Modular.pow_elt | Direct frozen dependencies: none | consumers: Modular.all_witness_normal, Modular.witnessEquiv
Modular.normalizer_of_C_le | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.normalizer_cases
Modular.normalizer_of_le_C | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.normalizer_cases
Modular.normalizer_of_neither | proof_shape: content | escape_witness: Modular.pow_elt | Direct frozen dependencies: none | consumers: Modular.normalizer_Y, Modular.normalizer_cases
Modular.not_C_le_Y | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.normalizer_Y
Modular.not_Y_le_C | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.normalizer_Y
Modular.omega_card | proof_shape: content | escape_witness: Modular.pow_elt | Direct frozen dependencies: none | consumers: LegarretaSicaTotaGavioli.family_omega
Modular.pow_elt | proof_shape: content | escape_witness: Modular.pow_elt | Direct frozen dependencies: none | consumers: Modular.pow_p
Modular.pow_p | proof_shape: content | escape_witness: Modular.pow_elt | Direct frozen dependencies: none | consumers: Modular.le_E_of_not_C_le
Modular.pp_zero | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.t, Modular.t_int, Modular.t_mul_t
Modular.redLeft | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.E, Modular.all_witness_normal
Modular.red_eq_zero_iff | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.center_eq_C
Modular.red_t | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.mem_C, Modular.redLeft, Modular.red_zero_iff_exists
Modular.red_zero_iff_exists | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.mem_C
Modular.s_card | proof_shape: content | escape_witness: Modular.pow_elt | Direct frozen dependencies: none | consumers: LegarretaSicaTotaGavioli.family_s_card
Modular.t | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.action, Modular.aut, Modular.c, Modular.c_injective, Modular.center_eq_C, Modular.conj_as_c, Modular.conj_elt, Modular.inv_elt, Modular.le_E_of_not_C_le, Modular.mem_C, Modular.mul_elt, Modular.not_C_le_Y, Modular.pow_elt, Modular.pow_p, Modular.redLeft, Modular.red_eq_zero_iff, Modular.red_t, Modular.red_zero_iff_exists, Modular.t_eq_zero, Modular.t_injective, Modular.t_int, Modular.t_mul, Modular.t_mul_t, Modular.t_red
Modular.t_eq_zero | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.center_eq_C, Modular.not_C_le_Y, Modular.red_eq_zero_iff
Modular.t_injective | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.c_injective, Modular.t_eq_zero
Modular.t_int | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.center_eq_C, Modular.pow_p, Modular.red_t, Modular.red_zero_iff_exists, Modular.t_injective, Modular.t_mul, Modular.t_mul_t, Modular.t_red
Modular.t_mul | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.center_eq_C, Modular.conj_as_c
Modular.t_mul_t | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.action, Modular.aut, Modular.conj_elt, Modular.pow_p
Modular.t_red | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.pow_p, Modular.red_eq_zero_iff
Modular.twoTable | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.twoWitness, Modular.witnessEquiv
Modular.twoWitness | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.witnessEquiv
Modular.witnessEquiv | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.classEquiv, Modular.s_card
NormalizerClass | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: LegarretaSicaTotaGavioli.Small.classEquiv, LegarretaSicaTotaGavioli.Small.classMap, LegarretaSicaTotaGavioli.Small.omega_card, LegarretaSicaTotaGavioli.claim, LegarretaSicaTotaGavioli.family_finite_classes, LegarretaSicaTotaGavioli.result, Modular.classEquiv, Modular.finite_classes, Modular.omega_card, classProd, classProd_injective, classesEquivOfNormal, counts_prod, finite_product_classes, normalizerClassesProductEquiv, omega
NormalizerWitness | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: LegarretaSicaTotaGavioli.Small.classEquiv, LegarretaSicaTotaGavioli.Small.classMap, LegarretaSicaTotaGavioli.Small.normalizerWitness, LegarretaSicaTotaGavioli.Small.s_card, LegarretaSicaTotaGavioli.Small.witnessEquiv, LegarretaSicaTotaGavioli.Small.witness_relation, Modular.all_witness_normal, Modular.classEquiv, Modular.s_card, Modular.twoWitness, Modular.witnessEquiv, NormalizerClass, classProd, classProd_injective, classesEquivOfNormal, counts_prod, normalizerClassesProductEquiv, normalizerProductEquiv, normalizerSetoid, sCard, witnessProd, witnessProd_injective
centreIndex | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: LegarretaSicaTotaGavioli.claim, LegarretaSicaTotaGavioli.family_center_index, LegarretaSicaTotaGavioli.result
classProd | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: classProd_injective, normalizerClassesProductEquiv
classProd_injective | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: normalizerClassesProductEquiv
classesEquivOfNormal | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: Modular.classEquiv
conjEquivalent_eq_of_normal | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: classesEquivOfNormal
conjEquivalent_refl | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: normalizerSetoid
conjEquivalent_symm | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: normalizerSetoid
conjEquivalent_trans | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: normalizerSetoid
conj_prod_iff | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: classProd, classProd_injective
counts_prod | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: D1 | consumers: LegarretaSicaTotaGavioli.family_omega, LegarretaSicaTotaGavioli.family_s_card
finite_product_classes | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: D1 | consumers: LegarretaSicaTotaGavioli.family_finite_classes
normalizerClassesProductEquiv | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: D1 | consumers: counts_prod, finite_product_classes
normalizerProductEquiv | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: D1 | consumers: counts_prod, normalizerClassesProductEquiv
normalizerSetoid | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: LegarretaSicaTotaGavioli.Small.classEquiv, LegarretaSicaTotaGavioli.Small.classMap, NormalizerClass, classProd, classProd_injective, classesEquivOfNormal, normalizerClassesProductEquiv
normalizer_prod | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: normalizerProductEquiv, witnessProd
omega | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: LegarretaSicaTotaGavioli.Small.omega_card, LegarretaSicaTotaGavioli.claim, LegarretaSicaTotaGavioli.family_omega, LegarretaSicaTotaGavioli.family_s_card, LegarretaSicaTotaGavioli.family_strict, LegarretaSicaTotaGavioli.result, Modular.omega_card, counts_prod
sCard | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: LegarretaSicaTotaGavioli.Small.s_card, LegarretaSicaTotaGavioli.claim, LegarretaSicaTotaGavioli.family_omega, LegarretaSicaTotaGavioli.family_s_card, LegarretaSicaTotaGavioli.family_strict, LegarretaSicaTotaGavioli.result, Modular.s_card, counts_prod
witnessProd | proof_shape: bind-only (definition) | escape_witness: none | Direct frozen dependencies: none | consumers: classProd, classProd_injective, normalizerClassesProductEquiv, normalizerProductEquiv, witnessProd_injective
witnessProd_injective | proof_shape: bind-only | escape_witness: none | Direct frozen dependencies: none | consumers: normalizerProductEquiv
-/

import D5.S3.FiniteGroups.SubgroupConjugacyRatio
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Tactic.LinearCombination


namespace D5.S3.FiniteGroups.NormalizerCentreIndex.ModularNormalizerFactors

/-- The type of distinct normalizer subgroups of `G`. -/
def NormalizerWitness (G : Type) [Group G] :=
  {N : Subgroup G // ∃ H : Subgroup G, N = Subgroup.normalizer H}

/-- Conjugacy of subgroups, written with the source's `g H g⁻¹` action. -/
def ConjEquivalent {G : Type} [Group G] (A B : Subgroup G) : Prop :=
  ∃ g : G, ∀ x : G, x ∈ A ↔ g * x * g⁻¹ ∈ B

private theorem conjEquivalent_refl {G : Type} [Group G] (A : Subgroup G) :
    ConjEquivalent A A := by
  refine ⟨1, ?_⟩
  intro x
  simp

private theorem conjEquivalent_symm {G : Type} [Group G] {A B : Subgroup G}
    (h : ConjEquivalent A B) : ConjEquivalent B A := by
  rcases h with ⟨g, hg⟩
  refine ⟨g⁻¹, ?_⟩
  intro x
  constructor
  · intro hx
    have h' := (hg (g⁻¹ * x * g)).mpr ?_
    · simpa [mul_assoc] using h'
    · simpa [mul_assoc] using hx
  · intro hx
    have h' := (hg (g⁻¹ * x * g)).mp ?_
    · simpa [mul_assoc] using h'
    · simpa [mul_assoc] using hx

private theorem conjEquivalent_trans {G : Type} [Group G] {A B C : Subgroup G}
    (hAB : ConjEquivalent A B) (hBC : ConjEquivalent B C) :
    ConjEquivalent A C := by
  rcases hAB with ⟨g, hg⟩
  rcases hBC with ⟨h, hh⟩
  refine ⟨h * g, ?_⟩
  intro x
  rw [show (h * g) * x * (h * g)⁻¹ = h * (g * x * g⁻¹) * h⁻¹ by simp [mul_assoc]]
  exact (hg x).trans (hh (g * x * g⁻¹))

def normalizerSetoid (G : Type) [Group G] : Setoid (NormalizerWitness G) where
  r A B := ConjEquivalent A.1 B.1
  iseqv := {
    refl := fun A => conjEquivalent_refl A.1
    symm := fun h => conjEquivalent_symm h
    trans := fun h₁ h₂ => conjEquivalent_trans h₁ h₂
  }

/-- The conjugacy-class quotient of the source's normalizer subgroups. -/
def NormalizerClass (G : Type) [Group G] := Quotient (normalizerSetoid G)

/-- `s(G)`: the cardinal of the distinct normalizer subgroups. -/
def sCard (G : Type) [Group G] : Cardinal := Cardinal.mk (NormalizerWitness G)

/-- `ω(G)`: the number of conjugacy classes of normalizers, when finite. -/
noncomputable def omega (G : Type) [Group G] : ℕ := Nat.card (NormalizerClass G)

/-- The centre-index cardinal `|G : Z(G)|`. -/
def centreIndex (G : Type) [Group G] : Cardinal :=
  Cardinal.mk (G ⧸ Subgroup.center G)

open Subgroup
variable {G K : Type} [Group G] [Group K]

private theorem normalizer_prod (H : Subgroup G) (J : Subgroup K) :
    Subgroup.normalizer (H.prod J : Set (G × K)) =
      (Subgroup.normalizer (H : Set G)).prod (Subgroup.normalizer (J : Set K)) := by
  ext x
  simp only [ Subgroup.mem_normalizer_iff, Subgroup.mem_prod]
  constructor
  · intro h
    constructor
    · intro g
      have hh := h (g, 1)
      simpa using hh
    · intro k
      have hh := h (1, k)
      simpa using hh
  · rintro ⟨h, j⟩ ⟨g,k⟩
    exact and_congr (h g) (j k)

private theorem conj_prod_iff (H H' : Subgroup G) (J J' : Subgroup K) :
    ConjEquivalent (H.prod J) (H'.prod J') ↔
      ConjEquivalent H H' ∧ ConjEquivalent J J' := by
  constructor
  · rintro ⟨⟨g,k⟩,h⟩
    refine ⟨⟨g,fun x => ?_⟩,⟨k,fun y => ?_⟩⟩
    · simpa [Subgroup.mem_prod] using h (x,1)
    · simpa [Subgroup.mem_prod] using h (1,y)
  · rintro ⟨⟨g,hg⟩,⟨k,hk⟩⟩
    exact ⟨(g,k),fun x => and_congr (hg x.1) (hk x.2)⟩

private def witnessProd (a : NormalizerWitness G) (b : NormalizerWitness K) :
    NormalizerWitness (G × K) :=
  ⟨a.1.prod b.1, by
    rcases a.2 with ⟨H,hH⟩
    rcases b.2 with ⟨J,hJ⟩
    exact ⟨H.prod J, by rw [normalizer_prod, ← hH, ← hJ]⟩⟩

private theorem witnessProd_injective : Function.Injective
    (fun q : NormalizerWitness G × NormalizerWitness K => witnessProd q.1 q.2) := by
  rintro ⟨a,b⟩ ⟨a',b'⟩ h
  have hval : a.1.prod b.1 = a'.1.prod b'.1 := congrArg Subtype.val h
  apply Prod.ext
  · apply Subtype.ext
    apply le_antisymm
    · intro x hx
      have hh : (x,1) ∈ a.1.prod b.1 := ⟨hx,b.1.one_mem⟩
      rw [hval] at hh
      exact hh.1
    · intro x hx
      have hh : (x,1) ∈ a'.1.prod b'.1 := ⟨hx,b'.1.one_mem⟩
      rw [← hval] at hh
      exact hh.1
  · apply Subtype.ext
    apply le_antisymm
    · intro x hx
      have hh : (1,x) ∈ a.1.prod b.1 := ⟨a.1.one_mem,hx⟩
      rw [hval] at hh
      exact hh.2
    · intro x hx
      have hh : (1,x) ∈ a'.1.prod b'.1 := ⟨a'.1.one_mem,hx⟩
      rw [← hval] at hh
      exact hh.2

private noncomputable def normalizerProductEquiv [Finite G] [Finite K]
    (hc : (Nat.card G).Coprime (Nat.card K)) :
    NormalizerWitness (G × K) ≃ NormalizerWitness G × NormalizerWitness K :=
  (Equiv.ofBijective (fun q => witnessProd q.1 q.2)
    ⟨witnessProd_injective, by
      rintro ⟨N,H,hH⟩
      let e := D5.S3.FiniteGroups.SubgroupConjugacyRatio.subgroupProductEquiv
        (G := G) (K := K) hc
      let a := (e H).1
      let b := (e H).2
      have hsplit : a.prod b = H := e.symm_apply_apply H
      refine ⟨(⟨Subgroup.normalizer a,a,rfl⟩,⟨Subgroup.normalizer b,b,rfl⟩), ?_⟩
      apply Subtype.ext
      change (Subgroup.normalizer a).prod (Subgroup.normalizer b) = N
      rw [← normalizer_prod, hsplit, ← hH]⟩).symm

private def classProd (a : NormalizerClass G) (b : NormalizerClass K) :
    NormalizerClass (G × K) :=
  Quotient.map₂' witnessProd
    (fun _ _ ha _ _ hb => (conj_prod_iff _ _ _ _).mpr ⟨ha,hb⟩) a b

private theorem classProd_injective : Function.Injective
    (fun q : NormalizerClass G × NormalizerClass K => classProd q.1 q.2) := by
  rintro ⟨a,b⟩ ⟨a',b'⟩
  refine Quotient.inductionOn₂ a a' ?_ b b'
  intro H H' b b'
  refine Quotient.inductionOn₂ b b' ?_
  intro J J' h
  have hh := (conj_prod_iff H.1 H'.1 J.1 J'.1).mp (Quotient.exact h)
  exact Prod.ext (Quotient.sound hh.1) (Quotient.sound hh.2)

private noncomputable def normalizerClassesProductEquiv [Finite G] [Finite K]
    (hc : (Nat.card G).Coprime (Nat.card K)) :
    NormalizerClass (G × K) ≃ NormalizerClass G × NormalizerClass K :=
  (Equiv.ofBijective (fun q => classProd q.1 q.2)
    ⟨classProd_injective, by
      intro q
      refine Quotient.inductionOn q ?_
      intro N
      let e := normalizerProductEquiv (G := G) (K := K) hc
      refine ⟨(Quotient.mk _ (e N).1,Quotient.mk _ (e N).2), ?_⟩
      change Quotient.mk _ (witnessProd (e N).1 (e N).2) = Quotient.mk _ N
      exact congrArg (Quotient.mk _) (e.symm_apply_apply N)⟩).symm

theorem counts_prod [Finite G] [Finite K]
    (hc : (Nat.card G).Coprime (Nat.card K)) :
    sCard (G × K) = sCard G * sCard K ∧ omega (G × K) = omega G * omega K := by
  constructor
  · simpa only [sCard, Cardinal.lift_id] using
      (Cardinal.mk_congr (normalizerProductEquiv hc)).trans
        (Cardinal.mk_prod (NormalizerWitness G) (NormalizerWitness K))
  · exact (Nat.card_congr (normalizerClassesProductEquiv hc)).trans (Nat.card_prod _ _)

theorem finite_product_classes [Finite G] [Finite K]
    (hc : (Nat.card G).Coprime (Nat.card K))
    [Finite (NormalizerClass G)] [Finite (NormalizerClass K)] :
    Finite (NormalizerClass (G × K)) :=
  Finite.of_equiv (NormalizerClass G × NormalizerClass K)
    (normalizerClassesProductEquiv hc).symm

end D5.S3.FiniteGroups.NormalizerCentreIndex.ModularNormalizerFactors


namespace D5.S3.FiniteGroups.NormalizerCentreIndex.ModularNormalizerFactors.Modular
variable (p : ℕ)

private theorem pp_zero : (p : ZMod (p ^ 2)) * p = 0 := by
  rw [← Nat.cast_mul, ← pow_two]
  exact ZMod.natCast_self (p ^ 2)


def t : ZMod p →+ ZMod (p ^ 2) :=
  ZMod.lift p ⟨(AddMonoidHom.mulLeft (p : ZMod (p ^ 2))).comp (Int.castAddHom (ZMod (p ^ 2))), by
    change (p : ZMod (p ^ 2)) * (p : ℤ) = 0
    simpa using pp_zero p⟩

private theorem t_int (z : ℤ) : t p (z : ZMod p) = (p : ZMod (p ^ 2)) * (z : ZMod (p ^ 2)) := by
  exact ZMod.lift_coe p _ z

private theorem t_mul_t (a b : ZMod p) : t p a * t p b = 0 := by
  obtain ⟨x,rfl⟩ := ZMod.intCast_surjective a
  obtain ⟨y,rfl⟩ := ZMod.intCast_surjective b
  rw [t_int,t_int]
  calc
    _ = ((p : ZMod (p ^ 2)) * p) * ((x : ZMod (p ^ 2)) * y) := by ring
    _ = 0 := by rw [pp_zero]; ring


private theorem t_red (a : ZMod (p ^ 2)) : t p ((ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)) a) = (p : ZMod (p ^ 2)) * a := by
  obtain ⟨x,rfl⟩ := ZMod.intCast_surjective a
  rw [map_intCast,t_int]

private theorem red_t (a : ZMod p) : (ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)) (t p a) = 0 := by
  obtain ⟨x,rfl⟩ := ZMod.intCast_surjective a
  rw [t_int,map_mul,map_natCast,ZMod.natCast_self,zero_mul]

def aut (a : ZMod p) : MulAut (Multiplicative (ZMod (p ^ 2))) :=
  AddEquiv.toMultiplicative ((AddAut.mulLeft (⟨1 + t p a, 1 - t p a, by
    have h := t_mul_t p a a
    linear_combination -h, by
    have h := t_mul_t p a a
    linear_combination -h⟩ : (ZMod (p ^ 2))ˣ)).toAdd)

def action : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (p ^ 2))) where
  toFun a := aut p a.toAdd
  map_one' := by
    ext x
    change (1 + t p 0) * x.toAdd = x.toAdd
    simp
  map_mul' a b := by
    ext x
    change (1 + t p (a.toAdd + b.toAdd)) * x.toAdd =
      (1 + t p a.toAdd) * ((1 + t p b.toAdd) * x.toAdd)
    rw [map_add]
    have h := t_mul_t p a.toAdd b.toAdd
    linear_combination -x.toAdd * h

abbrev P := Multiplicative (ZMod (p ^ 2)) ⋊[action p] Multiplicative (ZMod p)


private theorem mul_elt (a c : ZMod (p ^ 2)) (b d : ZMod p) :
    (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) a b * (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) c d = (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) (a + c + t p b * c) (b+d) := by
  apply SemidirectProduct.ext
  · change a + (1 + t p b) * c = a + c + t p b * c
    ring
  · rfl

private theorem inv_elt (a : ZMod (p ^ 2)) (b : ZMod p) :
    ((fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) a b)⁻¹ = (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) (-a + t p b * a) (-b) := by
  apply SemidirectProduct.ext
  · change (1 + t p (-b)) * (-a) = -a + t p b * a
    rw [map_neg]
    ring
  · rfl

private theorem conj_elt (a c : ZMod (p ^ 2)) (b d : ZMod p) :
    (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) a b * (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) c d * ((fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) a b)⁻¹ =
      (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) (c + t p b * c - t p d * a) d := by
  rw [inv_elt,mul_elt,mul_elt,map_add]
  apply SemidirectProduct.ext
  · change a + c + t p b * c + (-a + t p b * a) +
      (t p b + t p d) * (-a + t p b * a) = c + t p b * c - t p d * a
    have hbb := t_mul_t p b b
    have hdb := t_mul_t p d b
    linear_combination a * hbb + a * hdb
  · change b + d + -b = d
    abel

theorem finiteP [NeZero p] : Finite (P p) :=
  Finite.of_equiv (Multiplicative (ZMod (p ^ 2)) × Multiplicative (ZMod p))
    SemidirectProduct.equivProd.symm

attribute [instance] finiteP

theorem card_p [NeZero p] : Nat.card (P p) = p ^ 3 := by
  rw [Nat.card_congr SemidirectProduct.equivProd,Nat.card_prod]
  simp only [Nat.card_eq_fintype_card,Fintype.card_multiplicative,ZMod.card]
  ring



variable [Fact p.Prime]

private theorem t_injective : Function.Injective (t p) := by
  apply (t p).ker_eq_bot_iff.mp
  apply bot_unique
  intro a ha
  obtain ⟨z,rfl⟩ := ZMod.intCast_surjective a
  change t p (z : ZMod p) = 0 at ha
  rw [t_int] at ha
  have hz : ((p : ℤ) ^ 2) ∣ (p : ℤ) * z := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd ((p : ℤ)*z) (p^2)).mp
    simpa using ha
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hz' : (p : ℤ) ∣ z := by
    apply (mul_dvd_mul_iff_left hp).mp
    simpa [pow_two] using hz
  change (z : ZMod p) = 0
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mpr hz'

private theorem t_eq_zero (a : ZMod p) : t p a = 0 ↔ a = 0 := by
  rw [← map_zero (t p)]
  exact (t_injective p).eq_iff

private theorem t_mul (b : ZMod p) (a : ZMod (p ^ 2)) : t p (b * (ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)) a) = t p b * a := by
  obtain ⟨x,rfl⟩ := ZMod.intCast_surjective b
  obtain ⟨y,rfl⟩ := ZMod.intCast_surjective a
  rw [map_intCast,← Int.cast_mul,t_int,t_int]
  push_cast
  ring

private theorem red_eq_zero_iff (a : ZMod (p ^ 2)) : (ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)) a = 0 ↔ (p : ZMod (p ^ 2)) * a = 0 := by
  rw [← t_red,t_eq_zero]

omit [Fact p.Prime] in
@[simp] private theorem elt_eq (a c : ZMod (p ^ 2)) (b d : ZMod p) :
    (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) a b = (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) c d ↔ a=c ∧ b=d := by
  exact SemidirectProduct.ext_iff

private theorem pow_elt (a : ZMod (p ^ 2)) (b : ZMod p) (n : ℕ) :
    ((fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) a b)^n = (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) ((n : ZMod (p ^ 2))*a + (n.choose 2 : ZMod (p ^ 2))*t p b*a) ((n : ZMod p)*b) := by
  induction n with
  | zero => simp [pow_zero]
  | succ n hn =>
    rw [pow_succ _ n,hn,mul_elt]
    have ht : t p ((n : ZMod p)*b) = (n : ZMod (p ^ 2))*t p b := by
      simpa only [nsmul_eq_mul] using (t p).map_nsmul n b
    rw [ht]
    apply (elt_eq p _ _ _ _).mpr
    constructor
    · rw [Nat.choose_succ_succ, Nat.choose_one_right]
      push_cast
      ring
    · push_cast
      ring

private theorem pow_p (a : ZMod (p ^ 2)) (b : ZMod p) (ho : p ≠ 2) :
    ((fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) a b)^p = (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) (t p ((ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)) a)) 0 := by
  have hp : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm ho)
  obtain ⟨k,hk⟩ := (Fact.out : p.Prime).dvd_choose_self (by decide : 2 ≠ 0) hp
  rw [pow_elt,t_red,ZMod.natCast_self,zero_mul,hk,Nat.cast_mul]
  have ht : (p : ZMod (p ^ 2))*t p b = 0 := by
    have h := t_mul_t p (1 : ZMod p) b
    rw [show t p (1 : ZMod p) = (p : ZMod (p ^ 2)) by simpa using t_int p 1] at h
    exact h
  apply (elt_eq p _ _ _ _).mpr
  constructor
  · linear_combination (k : ZMod (p ^ 2))*a*ht
  · rfl



private theorem red_zero_iff_exists (a : ZMod (p ^ 2)) : (ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)) a = 0 ↔ ∃ u : ZMod p, t p u = a := by
  constructor
  · obtain ⟨z,rfl⟩ := ZMod.intCast_surjective a
    intro ha
    rw [map_intCast] at ha
    obtain ⟨k,hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp ha
    refine ⟨(k : ZMod p),?_⟩
    rw [t_int,hk]
    push_cast
    rfl
  · rintro ⟨u,rfl⟩
    exact red_t p u

private def c : Multiplicative (ZMod p) →* P p :=
  SemidirectProduct.inl.comp (t p).toMultiplicative

private theorem c_injective : Function.Injective (c p) := by
  intro u v h
  apply Multiplicative.toAdd.injective
  apply t_injective p
  exact ((elt_eq p _ _ _ _).mp h).1

private def C : Subgroup (P p) := (c p).range

private def redLeft : P p →* Multiplicative (ZMod p) where
  toFun g := Multiplicative.ofAdd ((ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)) g.left.toAdd)
  map_one' := by change (ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)) 0 = 0; simp
  map_mul' g h := by
    change (ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)) (g.left.toAdd + (1+t p g.right.toAdd)*h.left.toAdd) =
      (ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)) g.left.toAdd + (ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)) h.left.toAdd
    simp only [map_add, map_mul, map_one, red_t, add_zero, one_mul]

private def E : Subgroup (P p) := (redLeft p).ker

@[simp] private theorem mem_E (a : ZMod (p ^ 2)) (b : ZMod p) : (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) a b ∈ E p ↔ (ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)) a = 0 := by exact Eq.to_iff rfl

private theorem mem_C (a : ZMod (p ^ 2)) (b : ZMod p) : (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) a b ∈ C p ↔ (ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)) a = 0 ∧ b = 0 := by
  constructor
  · rintro ⟨u,hu⟩
    have hh := (elt_eq p _ _ _ _).mp hu
    exact ⟨hh.1 ▸ red_t p u.toAdd,hh.2.symm⟩
  · rintro ⟨ha,rfl⟩
    obtain ⟨u,hu⟩ := (red_zero_iff_exists p a).mp ha
    exact ⟨Multiplicative.ofAdd u,by change (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) (t p u) 0 = (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) a 0; rw [hu]⟩

private theorem conj_as_c (a x : ZMod (p ^ 2)) (b y : ZMod p) :
    (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) a b * (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) x y * ((fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) a b)⁻¹ =
      c p (Multiplicative.ofAdd (b * (ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)) x - y * (ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)) a)) * (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) x y := by
  rw [conj_elt]
  change (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) (x + t p b*x - t p y*a) y =
    (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) (t p (b*(ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)) x-y*(ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)) a)) 0 * (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) x y
  rw [mul_elt,map_sub,t_mul,t_mul]
  simp only [map_zero,zero_mul,add_zero,zero_add]
  congr 1
  ring

private theorem c_le_of_nonzero (H : Subgroup (P p)) {u : ZMod p} (hu : u ≠ 0)
    (hmem : c p (Multiplicative.ofAdd u) ∈ H) : C p ≤ H := by
  rintro g ⟨v,rfl⟩
  obtain ⟨n,hn⟩ := ZMod.natCast_zmod_surjective (v.toAdd / u)
  have he : (Multiplicative.ofAdd u : Multiplicative (ZMod p)) ^ n = v := by
    apply Multiplicative.toAdd.injective
    change n • u = v.toAdd
    rw [nsmul_eq_mul,hn,div_mul_cancel₀ _ hu]
  rw [← he,map_pow]
  exact H.pow_mem hmem n

private theorem normalizer_of_C_le (H : Subgroup (P p)) (hC : C p ≤ H) :
    Subgroup.normalizer (H : Set (P p)) = ⊤ := by
  apply top_unique
  apply Subgroup.le_normalizer_iff.mpr
  intro g _ h hh
  rcases g with ⟨a,b⟩
  rcases h with ⟨x,y⟩
  rw [show (⟨a,b⟩ : P p) = (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) a.toAdd b.toAdd from rfl,
    show (⟨x,y⟩ : P p) = (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) x.toAdd y.toAdd from rfl,conj_as_c]
  exact H.mul_mem (hC ⟨_,rfl⟩) hh

private theorem normalizer_of_le_C (H : Subgroup (P p)) (hC : H ≤ C p) :
    Subgroup.normalizer (H : Set (P p)) = ⊤ := by
  apply top_unique
  apply Subgroup.le_normalizer_iff.mpr
  intro g _ h hh
  rcases g with ⟨a,b⟩
  rcases h with ⟨x,y⟩
  have he := (mem_C p x.toAdd y.toAdd).mp (hC hh)
  rw [show (⟨a,b⟩ : P p) = (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) a.toAdd b.toAdd from rfl,
    show (⟨x,y⟩ : P p) = (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) x.toAdd y.toAdd from rfl,conj_as_c]
  rw [he.1,he.2,mul_zero,zero_mul,sub_zero]
  change c p 1 * (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) x.toAdd 0 ∈ H
  rw [map_one,one_mul]
  change (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) x.toAdd y.toAdd ∈ H at hh
  rwa [he.2] at hh

private theorem le_E_of_not_C_le (H : Subgroup (P p)) (ho : p ≠ 2) (hC : ¬ C p ≤ H) : H ≤ E p := by
  rintro ⟨a,b⟩ hh
  apply (mem_E p a.toAdd b.toAdd).mpr
  by_contra ha
  apply hC
  apply c_le_of_nonzero p H ha
  have hp := H.pow_mem hh p
  rw [show (⟨a,b⟩ : P p) = (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) a.toAdd b.toAdd from rfl,pow_p p _ _ ho] at hp
  exact hp

private theorem E_le_normalizer (H : Subgroup (P p)) (hE : H ≤ E p) :
    E p ≤ Subgroup.normalizer (H : Set (P p)) := by
  apply Subgroup.le_normalizer_iff.mpr
  rintro ⟨a,b⟩ hg ⟨x,y⟩ hh
  have ha := (mem_E p a.toAdd b.toAdd).mp hg
  have hx := (mem_E p x.toAdd y.toAdd).mp (hE hh)
  rw [show (⟨a,b⟩ : P p) = (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) a.toAdd b.toAdd from rfl,
    show (⟨x,y⟩ : P p) = (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) x.toAdd y.toAdd from rfl,conj_as_c]
  simp only [ha,hx,mul_zero,sub_zero]
  change c p 1 * (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) x.toAdd y.toAdd ∈ H
  rw [map_one,one_mul]
  exact hh

private theorem normalizer_of_neither (H : Subgroup (P p)) (ho : p ≠ 2)
    (hC : ¬ C p ≤ H) (hH : ¬ H ≤ C p) :
    Subgroup.normalizer (H : Set (P p)) = E p := by
  have hE := le_E_of_not_C_le p H ho hC
  apply le_antisymm _ (E_le_normalizer p H hE)
  obtain ⟨h,hh,hnot⟩ := SetLike.not_le_iff_exists.mp hH
  rcases h with ⟨x,y⟩
  have hx := (mem_E p x.toAdd y.toAdd).mp (hE hh)
  have hy : y.toAdd ≠ 0 := by
    intro he
    exact hnot ((mem_C p _ _).mpr ⟨hx,he⟩)
  rintro ⟨a,b⟩ hg
  apply (mem_E p _ _).mpr
  by_contra ha
  apply hC
  apply c_le_of_nonzero p H (u := -(y.toAdd * (ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)) a.toAdd)) (neg_ne_zero.mpr (mul_ne_zero hy ha))
  have hconj := (Subgroup.mem_normalizer_iff.mp hg _).mp hh
  rw [show (⟨a,b⟩ : P p) = (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) a.toAdd b.toAdd from rfl,
    show (⟨x,y⟩ : P p) = (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) x.toAdd y.toAdd from rfl,conj_as_c] at hconj
  have hc := H.mul_mem hconj (H.inv_mem hh)
  change (c p) (Multiplicative.ofAdd (b.toAdd*(ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)) x.toAdd-y.toAdd*(ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)) a.toAdd)) *
    (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) x.toAdd y.toAdd * ((fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) x.toAdd y.toAdd)⁻¹ ∈ H at hc
  simpa only [hx,mul_zero,zero_sub,mul_inv_cancel_right] using hc

private theorem normalizer_cases (H : Subgroup (P p)) (ho : p ≠ 2) :
    Subgroup.normalizer (H : Set (P p)) = ⊤ ∨
    Subgroup.normalizer (H : Set (P p)) = E p := by
  by_cases hC : C p ≤ H
  · exact Or.inl (normalizer_of_C_le p H hC)
  by_cases hH : H ≤ C p
  · exact Or.inl (normalizer_of_le_C p H hH)
  exact Or.inr (normalizer_of_neither p H ho hC hH)



private theorem center_eq_C : Subgroup.center (P p) = C p := by
  ext g
  rcases g with ⟨a,b⟩
  change (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) a.toAdd b.toAdd ∈ Subgroup.center (P p) ↔ (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) a.toAdd b.toAdd ∈ C p
  rw [mem_C,Subgroup.mem_center_iff]
  constructor
  · intro h
    have h1 := congrArg (fun g : P p => g.left.toAdd) (h ((fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) 1 0))
    change 1+(1+t p 0)*a.toAdd = a.toAdd+(1+t p b.toAdd)*1 at h1
    rw [map_zero] at h1
    have hb : t p b.toAdd = 0 := by linear_combination -h1
    have hb0 := (t_eq_zero p b.toAdd).mp hb
    refine ⟨?_,hb0⟩
    have h2 := congrArg (fun g : P p => g.left.toAdd) (h ((fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) 0 1))
    change 0+(1+t p 1)*a.toAdd = a.toAdd+(1+t p b.toAdd)*0 at h2
    apply (red_eq_zero_iff p a.toAdd).mpr
    rw [show t p (1 : ZMod p) = (p : ZMod (p ^ 2)) by simpa using t_int p 1] at h2
    linear_combination h2
  · rintro ⟨ha,hb⟩ ⟨x,y⟩
    apply SemidirectProduct.ext
    · change x.toAdd+(1+t p y.toAdd)*a.toAdd = a.toAdd+(1+t p b.toAdd)*x.toAdd
      rw [hb,map_zero]
      have hz : t p y.toAdd*a.toAdd = 0 := by rw [← t_mul,ha,mul_zero,map_zero]
      linear_combination hz
    · change y.toAdd+b.toAdd = b.toAdd+y.toAdd
      abel

private theorem card_C : Nat.card (C p) = p := by
  have h := Nat.card_congr (MonoidHom.ofInjective (c_injective p)).toEquiv
  change Nat.card (Multiplicative (ZMod p)) = Nat.card (C p) at h
  rw [← h,Nat.card_eq_fintype_card,Fintype.card_multiplicative,ZMod.card]

theorem center_card : Nat.card (Subgroup.center (P p)) = p := by
  rw [center_eq_C,card_C]

end D5.S3.FiniteGroups.NormalizerCentreIndex.ModularNormalizerFactors.Modular


namespace D5.S3.FiniteGroups.NormalizerCentreIndex.ModularNormalizerFactors
open Subgroup

private theorem conjEquivalent_eq_of_normal {G : Type} [Group G] {A B : Subgroup G}
    [B.Normal] (h : ConjEquivalent A B) : A=B := by
  rcases h with ⟨g,hg⟩
  have hn : g ∈ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    trivial
  exact Subgroup.ext (fun x => (hg x).trans ((Subgroup.mem_normalizer_iff.mp hn) x).symm)

private noncomputable def classesEquivOfNormal {G : Type} [Group G]
    (hn : ∀ w : NormalizerWitness G, w.1.Normal) :
    NormalizerClass G ≃ NormalizerWitness G :=
  (Equiv.ofBijective (Quotient.mk (normalizerSetoid G)) ⟨by
    intro a b h
    letI := hn b
    exact Subtype.ext (conjEquivalent_eq_of_normal (Quotient.exact h)),
    Quotient.mk_surjective⟩).symm

namespace Modular
variable (p : ℕ) [Fact p.Prime]

private def Y : Subgroup (P p) :=
  (SemidirectProduct.inr : Multiplicative (ZMod p) →* P p).range

private theorem not_C_le_Y : ¬ C p ≤ Y p := by
  intro h
  have hc : c p (Multiplicative.ofAdd (1 : ZMod p)) ∈ C p := ⟨_,rfl⟩
  obtain ⟨u,hu⟩ := h hc
  have he := congrArg (fun g : P p => g.left.toAdd) hu
  change 0=t p 1 at he
  exact one_ne_zero ((t_eq_zero p (1 : ZMod p)).mp he.symm)

private theorem not_Y_le_C : ¬ Y p ≤ C p := by
  intro h
  have hy : (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) 0 1 ∈ Y p := ⟨Multiplicative.ofAdd (1 : ZMod p),rfl⟩
  exact one_ne_zero ((mem_C p 0 1).mp (h hy)).2

private theorem normalizer_Y (ho : p ≠ 2) :
    Subgroup.normalizer (Y p) = E p :=
  normalizer_of_neither p (Y p) ho (not_C_le_Y p) (not_Y_le_C p)

private theorem E_ne_top : E p ≠ ⊤ := by
  intro h
  have he : (fun (a : ZMod (p ^ 2)) (b : ZMod p) => (⟨Multiplicative.ofAdd a, Multiplicative.ofAdd b⟩ : P p)) 1 0 ∈ E p := h ▸ Subgroup.mem_top _
  have hz := (mem_E p 1 0).mp he
  rw [map_one] at hz
  exact one_ne_zero hz

private def twoTable (i : Fin 2) : Subgroup (P p) := if i=0 then ⊤ else E p

private def twoWitness (ho : p ≠ 2) (i : Fin 2) : NormalizerWitness (P p) :=
  ⟨twoTable p i, by
    by_cases hi : i=0
    · refine ⟨⊤,?_⟩
      simp only [twoTable,hi,if_pos rfl]
      exact (Subgroup.normalizer_eq_top (⊤ : Subgroup (P p))).symm
    · refine ⟨Y p,?_⟩
      simp only [twoTable,hi,if_false]
      exact (normalizer_Y p ho).symm⟩

private noncomputable def witnessEquiv (ho : p ≠ 2) : Fin 2 ≃ NormalizerWitness (P p) :=
  Equiv.ofBijective (twoWitness p ho) ⟨by
    intro i j h
    have hh : twoTable p i = twoTable p j := congrArg Subtype.val h
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (E_ne_top p (by simpa [twoTable] using hh.symm))
    · exact False.elim (E_ne_top p (by simpa [twoTable] using hh))
    · rfl,by
    rintro ⟨N,H,hH⟩
    rcases normalizer_cases p H ho with ht | he
    · refine ⟨0,Subtype.ext ?_⟩
      change twoTable p 0=N
      simp only [twoTable,if_pos rfl]
      exact ht.symm.trans hH.symm
    · refine ⟨1,Subtype.ext ?_⟩
      change twoTable p 1=N
      change E p = N
      exact he.symm.trans hH.symm⟩

private theorem all_witness_normal (ho : p ≠ 2) (w : NormalizerWitness (P p)) : w.1.Normal := by
  obtain ⟨H,hH⟩ := w.2
  rcases normalizer_cases p H ho with ht | he
  · have : w.1=⊤ := hH.trans ht
    rw [this]
    infer_instance
  · have : w.1=E p := hH.trans he
    rw [this]
    exact (redLeft p).normal_ker

private noncomputable def classEquiv (ho : p ≠ 2) : NormalizerClass (P p) ≃ Fin 2 :=
  (classesEquivOfNormal (all_witness_normal p ho)).trans (witnessEquiv p ho).symm

theorem s_card (ho : p ≠ 2) : sCard (P p) = 2 := by
  exact (Cardinal.mk_congr (witnessEquiv p ho).symm).trans (by simp)

theorem omega_card (ho : p ≠ 2) : omega (P p) = 2 := by
  exact (Nat.card_congr (classEquiv p ho)).trans (by simp)

theorem finite_classes (ho : p ≠ 2) : Finite (NormalizerClass (P p)) :=
  Finite.of_equiv (Fin 2) (classEquiv p ho).symm

end Modular
end D5.S3.FiniteGroups.NormalizerCentreIndex.ModularNormalizerFactors
