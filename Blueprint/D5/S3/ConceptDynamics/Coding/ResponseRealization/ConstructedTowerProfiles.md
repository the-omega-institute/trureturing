# Profiles of the towers actually constructed by reduction

## Abstract

The existing two-sided reduction has paired split kinds and exact incoming and outgoing counts on both constructed towers.

TwoSidedFiniteInduction.Presentation bundles actual finite essential graphs, decidable equality and a discrete edge topology; empty carriers are permitted. Given F,H, a graph Code c, a history homeomorphism P with its one-block equation hP, and a total inverse table Q with radii M,N and exact all-history recovery hQ, reduce k F H c P hP M N Q hQ hk constructs the two towers, where hk states M+N=k. The radii need not be minimal.

kinds records true for outgoing and false for incoming in traversal order. Profile records five separate facts: left incoming=M, left outgoing=N, right incoming=M, right outgoing=N, and equality of the complete kind lists. Strong induction follows the existing recursion: an outgoing step decreases N, an incoming step at N=0 decreases M, and the zero case is the existing finite relabeling. Thus the matching profiles are conclusions about these towers, rather than a pairing premise.

SplitTowerPositiveAccounting.terminal_literal has correction minus left incoming count minus right outgoing count. The first and fourth Profile fields turn that correction into -(M+N)=-k. Equal total lengths alone do not justify that substitution. The response terminal includes a first outgoing split before its reduce tail; response_profile therefore has M=a+c and N=b+d+1, retaining that extra one.

The output time correction uses the left incoming and right outgoing counts. The full profile also retains both complementary counts and equality of the split-kind lists; equality of total lengths alone does not determine the correction.

**Remark 1.1 (kinds).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseRealization/ConstructedTowerProfiles.kinds`

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/ConstructedTowerProfiles.kinds` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This recursively reads the actual Tower constructors into a List Bool. It is consumed in Profile and in each induction branch of reduce_profile and response_profile; it introduces no alternative tower syntax.

**Remark 1.2 (Profile).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseRealization/ConstructedTowerProfiles.Profile`

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/ConstructedTowerProfiles.Profile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the five-clause proposition about one constructed Terminal and two natural radii. Keep all four count equalities and the kind-list equality. The response arithmetic later projects only its first and fourth clauses.

**Theorem 1.3 (reduce_profile).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseRealization/ConstructedTowerProfiles.reduce_profile`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseRealization/ConstructedTowerProfiles.reduce_profile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Follow the outgoing, incoming and zero branches of the same reduce recursion to obtain both tower profiles and equality of their split-kind lists. The response profile then includes its first outgoing step.

**Theorem 1.4 (response_profile).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseRealization/ConstructedTowerProfiles.response_profile`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseRealization/ConstructedTowerProfiles.response_profile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the actual response terminal, both towers have incoming count a+c and outgoing count b+d+1 and the same split-kind list. It explicitly prepends the completed first outgoing stage to the tail profile. output_literal consumes the incoming-left and outgoing-right equalities.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/ConstructedTowerProfiles.Profile`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/ConstructedTowerProfiles.kinds`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/ConstructedTowerProfiles.reduce_profile`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/ConstructedTowerProfiles.response_profile`
- Dependency: [D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting](../PositiveRecoding/SplitTowerPositiveAccounting.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResponseRealization/ResponseTwoSidedConsumer](ResponseTwoSidedConsumer.md)
