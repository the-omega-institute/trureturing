/- GID: D5/S3/Fourier/CharacterSelection/BinaryCharacterSubfamilyCriterion
   generality: G
   mirror-B: D5/B/S3/Fourier/CharacterSelection/BinaryCharacterSubfamilyCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A binary-character subfamily is complete exactly when it spans the full role space. -/

import D5.S3.Fourier.BinaryCharacterRedundancyCriterion
import D5.S3.ConceptDynamics.DefinitionEscape.QuestionAlgebraDuality
import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/- Library-search audit trail (2026-08-25):
   * `BinaryCharacterBasisMinimality` proves minimum-cardinality consequences,
     while `BinaryCharacterRedundancyCriterion` treats one added character;
     neither states the arbitrary-subfamily three-way equivalence below.
   * Exact repository hits `jointReadout`, `effectiveReadout`, and `Refines`
     provide the canonical profile, effective image, and expressibility
     relation. They are imported rather than redeclared.
   * Exact pinned-Mathlib hits `mem_span_of_iInf_ker_le_ker`, `Setoid.ker`,
     `Submodule.span_le`, and `List.TFAE` supply the linear duality proof and
     the public three-clause equivalence. No exact whole-theorem hit exists. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.CharacterSelection.BinaryCharacterSubfamilyCriterion

open Module Set
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.DefinitionEscape.QuestionAlgebraDuality

universe u z

set_option maxHeartbeats 2000000 in
-- The kernel-to-span direction needs more elaboration time than the default.
/-- Let `E` be a family of binary characters on a finite abelian group and
`B ⊆ E`. The following are equivalent: `B` and `E` have the same observation
kernel; after effective-image normalization they express exactly the same
targets of every fixed universe; and `B` spans the full character space
`H = span(E)`. All profiles evaluate on the original group through its
canonical quotient by doubles. -/
theorem binary_character_subfamily_sufficiency_tfae
    {G : Type u} [AddCommGroup G] [Finite G]
    (E B : Set (Module.Dual (ZMod 2) (ModN G 2)))
    (subset : B ⊆ E) :
    let profile (roles : Set (Module.Dual (ZMod 2) (ModN G 2))) :
        G → (roles → ZMod 2) :=
      jointReadout (fun role : roles => fun g => role.1 (ModN.mkQ 2 g))
    let H := Submodule.span (ZMod 2) E
    List.TFAE [
      Setoid.ker (profile B) = Setoid.ker (profile E),
      ∀ (Y : Type z),
        {target : Concept G Y |
            Refines target (effectiveReadout (profile B))} =
          {target : Concept G Y |
            Refines target (effectiveReadout (profile E))},
      Submodule.span (ZMod 2) B = H] := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have mkQSurjective : Function.Surjective (ModN.mkQ (G := G) 2) := by
    change Function.Surjective
      (LinearMap.range
        (LinearMap.lsmul ℤ G (↑(2 : Nat) : ℤ))).mkQ
    exact (LinearMap.range
      (LinearMap.lsmul ℤ G (↑(2 : Nat) : ℤ))).mkQ_surjective
  letI : Finite (ModN G 2) :=
    Finite.of_surjective (ModN.mkQ (G := G) 2) mkQSurjective
  letI : Finite (Module.Dual (ZMod 2) (ModN G 2)) :=
    Finite.of_injective
      (fun character : Module.Dual (ZMod 2) (ModN G 2) =>
        (character : ModN G 2 → ZMod 2)) LinearMap.coe_injective
  dsimp only
  let profile (roles : Set (Module.Dual (ZMod 2) (ModN G 2))) :
      G → (roles → ZMod 2) :=
    jointReadout (fun role : roles => fun g => role.1 (ModN.mkQ 2 g))
  change List.TFAE [
    Setoid.ker (profile B) = Setoid.ker (profile E),
    ∀ (Y : Type z),
      {target : Concept G Y |
          Refines target (effectiveReadout (profile B))} =
        {target : Concept G Y |
          Refines target (effectiveReadout (profile E))},
    Submodule.span (ZMod 2) B = Submodule.span (ZMod 2) E]
  have recoveryCriterion
      (roles : Set (Module.Dual (ZMod 2) (ModN G 2)))
      {Y : Type z} (target : Concept G Y) :
      Refines target (effectiveReadout (profile roles)) ↔
        Setoid.ker (profile roles) ≤ Setoid.ker target := by
    constructor
    · rintro ⟨factor, factorization⟩ x y sameProfile
      have sameEffective :
          effectiveReadout (profile roles) x =
            effectiveReadout (profile roles) y :=
        (effectiveReadout_eq_iff (profile roles) x y).2 sameProfile
      calc
        target x = factor (effectiveReadout (profile roles) x) :=
          congrFun factorization x
        _ = factor (effectiveReadout (profile roles) y) :=
          congrArg factor sameEffective
        _ = target y := (congrFun factorization y).symm
    · intro kernelInclusion
      refine ⟨fun value => target (Set.rangeSplitting (profile roles) value), ?_⟩
      funext g
      change target g =
        target (Set.rangeSplitting (profile roles)
          (effectiveReadout (profile roles) g))
      apply kernelInclusion
      exact (Set.apply_rangeSplitting
        (profile roles) (effectiveReadout (profile roles) g)).symm
  tfae_have 1 ↔ 2 := by
    constructor
    · intro sameKernel Y
      ext target
      simp only [Set.mem_setOf_eq]
      rw [recoveryCriterion B target, recoveryCriterion E target, sameKernel]
    · intro sameTargets
      apply le_antisymm
      · intro x y sameB
        funext role
        let target : Concept G (ULift.{z} (ZMod 2)) :=
          fun g => ULift.up (role.1 (ModN.mkQ 2 g))
        have expressibleFromE :
            Refines target (effectiveReadout (profile E)) := by
          refine ⟨fun observed => ULift.up (observed.1 role), ?_⟩
          funext g
          rfl
        have expressibleFromB :
            Refines target (effectiveReadout (profile B)) := by
          have memberRight : target ∈
              {candidate : Concept G (ULift.{z} (ZMod 2)) |
                Refines candidate (effectiveReadout (profile E))} :=
            expressibleFromE
          have memberLeft : target ∈
              {candidate : Concept G (ULift.{z} (ZMod 2)) |
                Refines candidate (effectiveReadout (profile B))} := by
            rw [sameTargets (ULift.{z} (ZMod 2))]
            exact memberRight
          exact memberLeft
        have targetEqual : target x = target y := by
          change Setoid.ker target x y
          exact (recoveryCriterion B target).1 expressibleFromB sameB
        simpa only [target, profile, jointReadout] using
          congrArg ULift.down targetEqual
      · intro x y sameE
        funext role
        simpa only [profile, jointReadout] using
          congrFun sameE ⟨role.1, subset role.2⟩
  tfae_have 1 ↔ 3 := by
    constructor
    · intro sameKernel
      apply le_antisymm
      · exact Submodule.span_mono subset
      · apply Submodule.span_le.2
        intro character characterInE
        have rangeSubtype :
            Set.range (fun role : B => role.1) = B := by
          ext candidate
          constructor
          · rintro ⟨role, rfl⟩
            exact role.2
          · intro candidateInB
            exact ⟨⟨candidate, candidateInB⟩, rfl⟩
        rw [← rangeSubtype]
        apply mem_span_of_iInf_ker_le_ker
          (L := fun role : B => role.1) (K := character)
        intro quotientState jointlyZero
        simp only [Submodule.mem_iInf, LinearMap.mem_ker] at jointlyZero ⊢
        obtain ⟨g, rfl⟩ := mkQSurjective quotientState
        have sameB : profile B g = profile B 0 := by
          funext role
          change role.1 (ModN.mkQ 2 g) =
            role.1 (ModN.mkQ 2 (0 : G))
          simpa using jointlyZero role
        have sameE : profile E g = profile E 0 := by
          change Setoid.ker (profile E) g 0
          rw [← sameKernel]
          exact sameB
        have characterEqual := congrFun sameE ⟨character, characterInE⟩
        change character (ModN.mkQ 2 g) =
          character (ModN.mkQ 2 (0 : G)) at characterEqual
        simpa using characterEqual
    · intro sameSpan
      apply le_antisymm
      · intro x y sameB
        funext role
        have spanInEvaluationKernel :
            Submodule.span (ZMod 2) B ≤
              LinearMap.ker
                (Module.Dual.eval (ZMod 2) (ModN G 2)
                  (ModN.mkQ 2 x - ModN.mkQ 2 y)) := by
          rw [Submodule.span_le]
          intro character characterInB
          apply LinearMap.mem_ker.mpr
          have characterEqual :
              character (ModN.mkQ 2 x) = character (ModN.mkQ 2 y) := by
            simpa only [profile, jointReadout] using
              congrFun sameB ⟨character, characterInB⟩
          simpa only [map_sub, LinearMap.sub_apply, Module.Dual.eval_apply] using
            sub_eq_zero.mpr characterEqual
        have roleInSpan : role.1 ∈ Submodule.span (ZMod 2) B := by
          rw [sameSpan]
          exact Submodule.subset_span role.2
        have zeroDifference :
            role.1 (ModN.mkQ 2 x - ModN.mkQ 2 y) = 0 := by
          simpa only [LinearMap.mem_ker, Module.Dual.eval_apply] using
            spanInEvaluationKernel roleInSpan
        have valueDifference :
            role.1 (ModN.mkQ 2 x) - role.1 (ModN.mkQ 2 y) = 0 := by
          simpa only [map_sub] using zeroDifference
        simpa only [profile, jointReadout] using
          sub_eq_zero.mp valueDifference
      · intro x y sameE
        funext role
        simpa only [profile, jointReadout] using
          congrFun sameE ⟨role.1, subset role.2⟩
  tfae_finish

#print axioms binary_character_subfamily_sufficiency_tfae

end D5.S3.Fourier.CharacterSelection.BinaryCharacterSubfamilyCriterion
