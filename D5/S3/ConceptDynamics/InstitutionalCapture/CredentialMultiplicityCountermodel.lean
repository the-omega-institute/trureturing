/- GID: D5/S3/ConceptDynamics/InstitutionalCapture/CredentialMultiplicityCountermodel
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InstitutionalCapture/CredentialMultiplicityCountermodel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Credential transcripts cannot recover person vote counts without owner multiplicity. -/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-22):
   * Repository searches for credential/person vote factorization, owner
     multiplicity, and equal voting transcripts found no exact theorem.
   * Pinned Mathlib supplies `Finset.filter`, `Finset.image`, and their finite
     cardinalities; these construct the source's credential and distinct-owner
     counts directly from owner maps and Boolean votes.
   * Pinned Mathlib's `Function.Injective` is used directly for the owner-map
     multiplicity constraint. No library theorem packages the two-world
     factorization obstruction, which is proved from the displayed collision. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InstitutionalCapture.CredentialMultiplicityCountermodel

/-- A voting world consists only of the source owner map and public Boolean
credential votes, specialized to the source's two-credential countermodel. -/
structure CredentialWorld where
  owner : Fin 2 -> Fin 2
  votes : Fin 2 -> Bool

/-- The public interface omits ownership and exposes only credential votes. -/
def publicTranscript (world : CredentialWorld) : Fin 2 -> Bool :=
  world.votes

/-- One-credential-one-vote counts affirmative credentials. -/
def credentialVoteCount (world : CredentialWorld) : Nat :=
  (Finset.univ.filter fun credential => world.votes credential = true).card

/-- One-person-one-vote counts the distinct owners of affirmative credentials. -/
def personVoteCount (world : CredentialWorld) : Nat :=
  ((Finset.univ.filter fun credential => world.votes credential = true).image
    world.owner).card

/-- Both credentials belong to the same person and both vote affirmatively. -/
def commonOwnerWorld : CredentialWorld where
  owner := fun _ => 0
  votes := fun _ => true

/-- The two credentials belong to distinct persons and both vote affirmatively. -/
def distinctOwnerWorld : CredentialWorld where
  owner := id
  votes := fun _ => true

/-- The source's two worlds have the same credential transcript and credential
count, but different owner multiplicity and person vote counts. Consequently
the person count does not factor through the public transcript. -/
theorem credential_transcript_cannot_recover_person_vote_count :
    publicTranscript commonOwnerWorld = publicTranscript distinctOwnerWorld ∧
      commonOwnerWorld.owner 0 = commonOwnerWorld.owner 1 ∧
      distinctOwnerWorld.owner 0 ≠ distinctOwnerWorld.owner 1 ∧
      credentialVoteCount commonOwnerWorld = 2 ∧
      credentialVoteCount distinctOwnerWorld = 2 ∧
      personVoteCount commonOwnerWorld = 1 ∧
      personVoteCount distinctOwnerWorld = 2 ∧
      (¬∃ recover : (Fin 2 -> Bool) -> Nat,
        personVoteCount = recover ∘ publicTranscript) ∧
      ¬Function.Injective commonOwnerWorld.owner ∧
      Function.Injective distinctOwnerWorld.owner := by
  have transcriptSame :
      publicTranscript commonOwnerWorld = publicTranscript distinctOwnerWorld := rfl
  have commonCount : personVoteCount commonOwnerWorld = 1 := by
    decide
  have distinctCount : personVoteCount distinctOwnerWorld = 2 := by
    decide
  refine ⟨transcriptSame, rfl, by decide, by decide, by decide,
    commonCount, distinctCount, ?_, ?_, ?_⟩
  · rintro ⟨recover, recovery⟩
    have recoveredCommon := congrFun recovery commonOwnerWorld
    have recoveredDistinct := congrFun recovery distinctOwnerWorld
    have countSame :
        personVoteCount commonOwnerWorld = personVoteCount distinctOwnerWorld := by
      calc
        personVoteCount commonOwnerWorld =
            recover (publicTranscript commonOwnerWorld) := by
          simpa only [Function.comp_apply] using recoveredCommon
        _ = recover (publicTranscript distinctOwnerWorld) :=
          congrArg recover transcriptSame
        _ = personVoteCount distinctOwnerWorld := by
          simpa only [Function.comp_apply] using recoveredDistinct.symm
    omega
  · intro injective
    have impossible : (0 : Fin 2) = 1 := injective rfl
    exact Fin.zero_ne_one impossible
  · intro x y equality
    exact equality

/- The public world carrier is inhabited by the common-owner construction. -/
example : CredentialWorld := commonOwnerWorld

/- The checked two-world construction witnesses every public conclusion. -/
example :
    publicTranscript commonOwnerWorld = publicTranscript distinctOwnerWorld ∧
      personVoteCount commonOwnerWorld ≠ personVoteCount distinctOwnerWorld := by
  exact ⟨rfl, by decide⟩

#print axioms credential_transcript_cannot_recover_person_vote_count

end D5.S3.ConceptDynamics.InstitutionalCapture.CredentialMultiplicityCountermodel
