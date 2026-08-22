# Credential Multiplicity Countermodel

## Abstract

Credential transcripts cannot recover person vote counts without owner multiplicity.

**Theorem 1.1 (Credential transcripts do not determine person vote counts).**

$$\begin{gathered}\operatorname{publicTranscript}\left(commonOwnerWorld\right) = \operatorname{publicTranscript}\left(distinctOwnerWorld\right) \land\\{}\operatorname{owner}\left(commonOwnerWorld\right)(0) = \operatorname{owner}\left(commonOwnerWorld\right)(1) \land\\{}\operatorname{owner}\left(distinctOwnerWorld\right)(0) \neq \operatorname{owner}\left(distinctOwnerWorld\right)(1) \land\\{}\operatorname{credentialVoteCount}\left(commonOwnerWorld\right) = 2 \land \operatorname{credentialVoteCount}\left(distinctOwnerWorld\right) = 2 \land\\{}\operatorname{personVoteCount}\left(commonOwnerWorld\right) = 1 \land \operatorname{personVoteCount}\left(distinctOwnerWorld\right) = 2 \land\\{}\neg (\exists recover: (\operatorname{Fin}\left(2\right) \to Bool) \to Nat, personVoteCount = recover \circ publicTranscript) \land\\{}\neg \operatorname{Injective}\left(\operatorname{owner}\left(commonOwnerWorld\right)\right) \land \operatorname{Injective}\left(\operatorname{owner}\left(distinctOwnerWorld\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InstitutionalCapture/CredentialMultiplicityCountermodel.credential_transcript_cannot_recover_person_vote_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A credential world contains an owner map and Boolean credential votes. Its public transcript exposes only the votes. Credential vote count counts affirmative credentials, while person vote count takes the finite image of their owners before counting.

The common-owner world assigns both affirmative credentials to one person. The distinct-owner world uses the identity owner map. Their public transcripts and credential counts agree, but their person counts are one and two.

Any recovery function on public transcripts must return the same value on these two worlds, contradicting their distinct person counts. The display also records the failed and satisfied injectivity conditions on the two owner maps.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InstitutionalCapture/CredentialMultiplicityCountermodel.credential_transcript_cannot_recover_person_vote_count`
