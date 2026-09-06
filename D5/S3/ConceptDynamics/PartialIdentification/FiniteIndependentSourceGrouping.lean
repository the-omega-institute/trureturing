/- GID: D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite independent rational disturbance laws regroup across any source partition without changing the full law; local queries admit exact marginal elimination and are invariant under changes to unused disturbance laws. -/

import D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Function.DependsOn

/- Library audit (2026-09-06): reuse FiniteResponseLaw and
   pushforwardSignatureMass. Pinned Mathlib supplies Fintype.prod_sum,
   Fintype.prod_subtype_mul_prod_subtype, Equiv.sum_comp,
   Equiv.piEquivPiSubtypeProd, and dependsOn_iff_exists_comp.
   The source carrier is the entire dependent product, including empty blocks.
   Each index denotes one independent disturbance, which may itself encode a
   complete response type with unrestricted internal coupling. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.PartialIdentification.FiniteIndependentSourceGrouping

open scoped BigOperators
open D5.S3.ConceptDynamics.PartialIdentification.CanonicalResponseSignature
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization

variable {Source : Type*} [Fintype Source] [DecidableEq Source]
variable {Noise : Source → Type*} [∀ i, Fintype (Noise i)]

/-- The normalized law of a finite mutually independent disturbance family.
The carrier and mass do not depend on any later choice of source partition. -/
def independentSourceLaw (laws : ∀ i, FiniteResponseLaw (Noise i)) :
    FiniteResponseLaw (∀ i, Noise i) where
  mass := fun u => ∏ i, (laws i).mass (u i)
  nonnegative := fun u => Finset.prod_nonneg (fun i _ => (laws i).nonnegative (u i))
  total := by
    classical
    rw [← Fintype.prod_sum]
    simp only [FiniteResponseLaw.total, Finset.prod_const_one]

/-- Regroup the full mass across any supported block and its complement.
This is an equality derived from the elementary laws, not a block-independence premise. -/
theorem independentSource_mass_split
    (laws : ∀ i, FiniteResponseLaw (Noise i)) (support : Finset Source)
    (u : ∀ i, Noise i) :
    (independentSourceLaw laws).mass u =
      productResponseMass
        (independentSourceLaw (fun i : {i : Source // i ∈ support} => laws i.1)).mass
        (independentSourceLaw (fun i : {i : Source // i ∉ support} => laws i.1)).mass
        ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ support) Noise) u) := by
  exact (Fintype.prod_subtype_mul_prod_subtype
    (fun i => i ∈ support) (fun i => (laws i).mass (u i))).symm

/-- Every finite readout has the same law before and after regrouping the
source coordinates. Both sums range over the full source carrier via an equivalence. -/
theorem independentSource_pushforward_regroup
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (laws : ∀ i, FiniteResponseLaw (Noise i)) (support : Finset Source)
    (readout : (∀ i, Noise i) → Response) :
    pushforwardSignatureMass (independentSourceLaw laws).mass readout =
      pushforwardSignatureMass
        (productResponseMass
          (independentSourceLaw (fun i : {i : Source // i ∈ support} => laws i.1)).mass
          (independentSourceLaw (fun i : {i : Source // i ∉ support} => laws i.1)).mass)
        (fun z => readout
          ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ support) Noise).symm z)) := by
  classical
  let split := Equiv.piEquivPiSubtypeProd (fun i => i ∈ support) Noise
  let left := independentSourceLaw (fun i : {i : Source // i ∈ support} => laws i.1)
  let right := independentSourceLaw (fun i : {i : Source // i ∉ support} => laws i.1)
  have at_merge : ∀ z, (independentSourceLaw laws).mass (split.symm z) =
      productResponseMass left.mass right.mass z := by
    intro z
    simpa only [Equiv.apply_symm_apply] using
      independentSource_mass_split laws support (split.symm z)
  funext response
  change (∑ u, if readout u = response then (independentSourceLaw laws).mass u else 0) =
    ∑ z, if readout (split.symm z) = response then productResponseMass left.mass right.mass z else 0
  calc
    (∑ u, if readout u = response then (independentSourceLaw laws).mass u else 0) =
        ∑ z, if readout (split.symm z) = response then
          (independentSourceLaw laws).mass (split.symm z) else 0 :=
      (split.symm.sum_comp
        (fun u => if readout u = response then (independentSourceLaw laws).mass u else 0)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      rw [at_merge]

/-- The actual distribution of the two coordinate blocks is their product law. -/
theorem independentSource_split_law [∀ i, DecidableEq (Noise i)]
    (laws : ∀ i, FiniteResponseLaw (Noise i)) (support : Finset Source) :
    pushforwardSignatureMass (independentSourceLaw laws).mass
        (Equiv.piEquivPiSubtypeProd (fun i => i ∈ support) Noise) =
      productResponseMass
        (independentSourceLaw (fun i : {i : Source // i ∈ support} => laws i.1)).mass
        (independentSourceLaw (fun i : {i : Source // i ∉ support} => laws i.1)).mass := by
  classical
  have regroup := independentSource_pushforward_regroup laws support
    (Equiv.piEquivPiSubtypeProd (fun i => i ∈ support) Noise)
  simpa only [Equiv.apply_symm_apply, pushforwardSignatureMass_id] using regroup

/-- A readout that factors through a supported block has exactly the law
computed from that block alone. The complementary source law sums to one. -/
theorem independentSource_pushforward_restrict
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (laws : ∀ i, FiniteResponseLaw (Noise i)) (support : Finset Source)
    (readout : (∀ i, Noise i) → Response)
    (reduced : (∀ i : {i : Source // i ∈ support}, Noise i.1) → Response)
    (factor : ∀ u, readout u = reduced (fun i => u i.1)) :
    pushforwardSignatureMass (independentSourceLaw laws).mass readout =
      pushforwardSignatureMass
        (independentSourceLaw (fun i : {i : Source // i ∈ support} => laws i.1)).mass reduced := by
  classical
  let split := Equiv.piEquivPiSubtypeProd (fun i => i ∈ support) Noise
  let left := independentSourceLaw (fun i : {i : Source // i ∈ support} => laws i.1)
  let right := independentSourceLaw (fun i : {i : Source // i ∉ support} => laws i.1)
  have factor_merge : ∀ z, readout (split.symm z) = reduced z.1 := by
    intro z
    rw [factor]
    change reduced ((split (split.symm z)).1) = reduced z.1
    rw [split.apply_symm_apply]
  rw [independentSource_pushforward_regroup laws support readout]
  funext response
  change (∑ z, if readout (split.symm z) = response then
      productResponseMass left.mass right.mass z else 0) =
    ∑ x, if reduced x = response then left.mass x else 0
  simp_rw [factor_merge]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  by_cases selected : reduced x = response
  · simp only [selected, if_true, productResponseMass]
    rw [← Finset.mul_sum, right.total, mul_one]
  · simp only [selected, if_false, Finset.sum_const_zero]

/-- Restricting the full source law gives the product of exactly the retained
coordinate laws, including the unit law when the retained set is empty. -/
theorem independentSource_restriction_marginal [∀ i, DecidableEq (Noise i)]
    (laws : ∀ i, FiniteResponseLaw (Noise i)) (support : Finset Source) :
    pushforwardSignatureMass (independentSourceLaw laws).mass
        (fun u => fun i : {i : Source // i ∈ support} => u i.1) =
      (independentSourceLaw (fun i : {i : Source // i ∈ support} => laws i.1)).mass := by
  classical
  have restriction := independentSource_pushforward_restrict laws support
    (fun u => fun i : {i : Source // i ∈ support} => u i.1) id (fun _ => rfl)
  simpa only [pushforwardSignatureMass_id] using restriction

/-- With the readout fixed, changing elementary source laws outside its support
cannot change its entire output distribution. Data constraints are not discarded. -/
theorem independentSource_readout_law_invariant
    {Response : Type*} [Fintype Response] [DecidableEq Response] [Nonempty Response]
    (first second : ∀ i, FiniteResponseLaw (Noise i)) (support : Finset Source)
    (readout : (∀ i, Noise i) → Response)
    (locality : DependsOn readout (support : Set Source))
    (agree : ∀ i ∈ support, (first i).mass = (second i).mass) :
    pushforwardSignatureMass (independentSourceLaw first).mass readout =
      pushforwardSignatureMass (independentSourceLaw second).mass readout := by
  classical
  rcases dependsOn_iff_exists_comp.mp locality with ⟨reduced, readout_eq⟩
  have factor : ∀ u, readout u = reduced (fun i => u i.1) :=
    fun u => congrFun readout_eq u
  rw [independentSource_pushforward_restrict first support readout reduced factor,
    independentSource_pushforward_restrict second support readout reduced factor]
  apply congrArg (fun mass => pushforwardSignatureMass mass reduced)
  funext x
  change (∏ i : {i : Source // i ∈ support}, (first i.1).mass (x i)) =
    ∏ i : {i : Source // i ∈ support}, (second i.1).mass (x i)
  apply Finset.prod_congr rfl
  intro i _
  exact congrFun (agree i.1 i.2) (x i)

/-- Project a joint-event constraint for two independent Bernoulli parameters.
A query can ignore the second source while a supplied data constraint still
restricts its attainable range. This is parameter projection, not data deletion. -/
theorem joint_event_constraint_projection_iff
    (observed target : ℚ) (observed_nonnegative : 0 ≤ observed) :
    (observed ≤ target ∧ target ≤ 1) ↔
      (0 ≤ target ∧ target ≤ 1 ∧
        ∃ nuisance : ℚ, 0 ≤ nuisance ∧ nuisance ≤ 1 ∧ target * nuisance = observed) := by
  constructor
  · rintro ⟨lower, upper⟩
    have nonnegative : 0 ≤ target := observed_nonnegative.trans lower
    refine ⟨nonnegative, upper, ?_⟩
    by_cases zero : target = 0
    · have observed_zero : observed = 0 := by
        rw [zero] at lower
        exact le_antisymm lower observed_nonnegative
      exact ⟨0, le_rfl, by norm_num, by simp [observed_zero]⟩
    · have positive : 0 < target := lt_of_le_of_ne nonnegative (Ne.symm zero)
      refine ⟨observed / target, div_nonneg observed_nonnegative nonnegative, ?_, ?_⟩
      · apply (div_le_iff₀ positive).2
        simpa only [one_mul] using lower
      · field_simp [zero] <;> ring
  · rintro ⟨nonnegative, upper, nuisance, _, at_most_one, product⟩
    refine ⟨?_, upper⟩
    calc
      observed = target * nuisance := product.symm
      _ ≤ target * 1 := mul_le_mul_of_nonneg_left at_most_one nonnegative
      _ = target := mul_one target

#print axioms independentSource_mass_split
#print axioms independentSource_split_law
#print axioms independentSource_pushforward_restrict
#print axioms independentSource_readout_law_invariant
#print axioms joint_event_constraint_projection_iff

end D5.S3.ConceptDynamics.PartialIdentification.FiniteIndependentSourceGrouping
