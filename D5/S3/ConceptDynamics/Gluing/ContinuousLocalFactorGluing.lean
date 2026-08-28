/- GID: D5/S3/ConceptDynamics/Gluing/ContinuousLocalFactorGluing
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Gluing/ContinuousLocalFactorGluing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compatible continuous local factors glue uniquely and factor the target globally. -/

import D5.S3.ConceptDynamics.Gluing.LocalFactorOverlapCompatibility
import Mathlib.Topology.ContinuousMap.Basic

/- Library-search audit trail (2026-08-27):
   * Exact D5 hit `local_factor_overlap_compatibility` proves the atom's first
     public clause on the source's subtype-domain carrier and is applied
     directly. It does not state unique global gluing, target factorization, or
     continuity, so it is not an exact whole-atom bind target.
   * Repository and body-shape searches for `ContinuousMap.liftCover`, a unique
     continuous global factor, and `target = globalFactor ∘ q` found no D5
     declaration combining the remaining clauses.
   * Pinned Mathlib exact hits `ContinuousMap.liftCover` and
     `ContinuousMap.liftCover_coe` construct the continuous glue and give its
     local computation rule. They are applied rather than reproved.
   * No new `def` or `abbrev` is introduced; the local factor, cover, readout,
     target, and canonical Mathlib glue remain independent source objects. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Gluing.ContinuousLocalFactorGluing

open D5.S3.ConceptDynamics.Gluing.LocalFactorOverlapCompatibility
open Filter Topology

/-- Continuous local factors of one target through a surjective readout agree
on every overlap and uniquely glue to a continuous global factor through which
the target factors. -/
theorem continuous_local_factors_glue_uniquely
    {Index X B Y : Type*} [TopologicalSpace B] [TopologicalSpace Y]
    (q : X -> B) (target : X -> Y)
    (domain : Index -> Set B)
    (openDomain : ∀ i, IsOpen (domain i))
    (cover : ⋃ i, domain i = Set.univ)
    (localFactor : (i : Index) -> C(domain i, Y))
    (surjective : Function.Surjective q)
    (factors : ∀ i x (membership : q x ∈ domain i),
      target x = localFactor i ⟨q x, membership⟩) :
    (∀ i j b (inFirst : b ∈ domain i) (inSecond : b ∈ domain j),
      localFactor i ⟨b, inFirst⟩ = localFactor j ⟨b, inSecond⟩) ∧
      ∃! globalFactor : C(B, Y),
        (∀ i (b : {value : B // value ∈ domain i}),
          globalFactor b = localFactor i b) ∧
        target = globalFactor ∘ q := by
  have overlap :
      ∀ i j b (inFirst : b ∈ domain i) (inSecond : b ∈ domain j),
        localFactor i ⟨b, inFirst⟩ = localFactor j ⟨b, inSecond⟩ :=
    local_factor_overlap_compatibility q target domain
      (fun i b => localFactor i b)
      surjective factors
  have neighborhoodCover : ∀ b : B, ∃ i, domain i ∈ 𝓝 b := by
    intro b
    have bInCover : b ∈ ⋃ i, domain i := by
      rw [cover]
      exact Set.mem_univ b
    obtain ⟨i, bInDomain⟩ := Set.mem_iUnion.mp bInCover
    exact ⟨i, (openDomain i).mem_nhds bInDomain⟩
  let globalFactor : C(B, Y) :=
    ContinuousMap.liftCover domain localFactor overlap neighborhoodCover
  have globalRestricts :
      ∀ i (b : {value : B // value ∈ domain i}),
        globalFactor b = localFactor i b := by
    intro i b
    simpa only [globalFactor] using
      (ContinuousMap.liftCover_coe
        (S := domain) (φ := localFactor)
        (hφ := overlap) (hS := neighborhoodCover) b)
  have targetFactors : target = globalFactor ∘ q := by
    funext x
    have qInCover : q x ∈ ⋃ i, domain i := by
      rw [cover]
      exact Set.mem_univ (q x)
    obtain ⟨i, qInDomain⟩ := Set.mem_iUnion.mp qInCover
    calc
      target x = localFactor i ⟨q x, qInDomain⟩ :=
        factors i x qInDomain
      _ = globalFactor (q x) :=
        (globalRestricts i ⟨q x, qInDomain⟩).symm
      _ = (globalFactor ∘ q) x := rfl
  refine ⟨overlap, globalFactor, ⟨globalRestricts, targetFactors⟩, ?_⟩
  intro candidate candidateProperties
  apply ContinuousMap.ext
  intro b
  have bInCover : b ∈ ⋃ i, domain i := by
    rw [cover]
    exact Set.mem_univ b
  obtain ⟨i, bInDomain⟩ := Set.mem_iUnion.mp bInCover
  calc
    candidate b = localFactor i ⟨b, bInDomain⟩ :=
      candidateProperties.1 i ⟨b, bInDomain⟩
    _ = globalFactor b :=
      (globalRestricts i ⟨b, bInDomain⟩).symm

example :
    let domain : Unit -> Set Unit := fun _ => Set.univ
    let localFactor : (i : Unit) -> C(domain i, Unit) :=
      fun _ => ContinuousMap.const _ ()
    (∀ i j b (inFirst : b ∈ domain i) (inSecond : b ∈ domain j),
      localFactor i ⟨b, inFirst⟩ = localFactor j ⟨b, inSecond⟩) ∧
      ∃! globalFactor : C(Unit, Unit),
        (∀ i (b : {value : Unit // value ∈ domain i}),
          globalFactor b = localFactor i b) ∧
        id = globalFactor ∘ id := by
  dsimp only
  apply continuous_local_factors_glue_uniquely
  · intro _
    exact isOpen_univ
  · ext b
    simp
  · exact Function.surjective_id
  · intro _ _ _
    rfl

#print axioms continuous_local_factors_glue_uniquely

end D5.S3.ConceptDynamics.Gluing.ContinuousLocalFactorGluing
