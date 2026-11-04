# Peng Question 5.1: the free-fibre obstruction

## Abstract

A generic binary-shift source refutes the unrestricted compact Hausdorff zero-dimensional shadowing-cover assertion.

**Theorem 1.1 (Finite initial graph presentation).**

Lean statement: `D5/S1/Dynamics/Shadowing/FreeFibreBoundary.finite_initial_presentation_to_graphLanguage`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/FreeFibreBoundary.finite_initial_presentation_to_graphLanguage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dekui Peng (2026). *Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse Limits*. URL: <https://arxiv.org/abs/2606.14435v3>.

*Commentary.*

Every set of binary names presented by a finite directed graph, a vertex label, and an arbitrary initial vertex set is exactly a finite graph language with Boolean coded edge, label, and initial data.

**Theorem 1.2 (Marked clopen image language).**

Lean statement: `D5/S1/Dynamics/Shadowing/FreeFibreBoundary.semiconj_clopen_image_is_finiteGraphLanguage`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/FreeFibreBoundary.semiconj_clopen_image_is_finiteGraphLanguage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dekui Peng (2026). *Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse Limits*. URL: <https://arxiv.org/abs/2606.14435v3>.

*Commentary.*

If T shadows and phi is a continuous shift semiconjugacy into binary names, then the image phi(W) of every clopen W is exactly a finite initial graph language. The initial graph vertices are restricted by the marker at time zero, so the statement covers all natural times including zero and does not assume T is onto.

**Theorem 1.3 (Convergent section restriction).**

Lean statement: `D5/S1/Dynamics/Shadowing/FreeFibreBoundary.finiteGraphLanguage_section_isClopen`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/FreeFibreBoundary.finiteGraphLanguage_section_isClopen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dekui Peng (2026). *Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse Limits*. URL: <https://arxiv.org/abs/2606.14435v3>.

*Commentary.*

For the first-disagreement convergent section S0 consisting of the generic name and one selected name in each finite fibre, the restriction of every finite graph language is clopen in S0 whenever the generic name locally decides that language.

**Theorem 1.4 (Free-fibre source shadowing).**

Lean statement: `D5/S1/Dynamics/Shadowing/FreeFibreBoundary.freeFibreSource_hasShadowing`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/FreeFibreBoundary.freeFibreSource_hasShadowing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dekui Peng (2026). *Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse Limits*. URL: <https://arxiv.org/abs/2606.14435v3>.

*Commentary.*

Given a compact Hausdorff continuous open onto map p:T to the one-point compactification of the naturals and a generic binary name a, the disjoint source consisting of the pullback of p along firstDifference a and a binary shift copy has a continuous forward map with finite-open-cover shadowing. The proof fixes finite control before the pseudo-orbit and pays the time-zero lift explicitly.

**Theorem 1.5 (A hypothetical cover forces an open resolution).**

Lean statement: `D5/S1/Dynamics/Shadowing/FreeFibreBoundary.freeFibre_cover_forces_resolution`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/FreeFibreBoundary.freeFibre_cover_forces_resolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dekui Peng (2026). *Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse Limits*. URL: <https://arxiv.org/abs/2606.14435v3>.

*Commentary.*

For every compact Hausdorff zero-dimensional shadowing system (Y,tau), every continuous onto q from Y to the free-fibre source, and every equivariant semiconjugacy, the restriction over the convergent section yields a continuous onto map r to T whose composite p composed r is open on the whole one-point base. No shadowing or invariance is assumed of the restriction Y0; no injectivity, global openness, or fibre restriction is imposed on the upstairs cover.

**Definition 1.6 (Peng's unrestricted Question 5.1).**

Lean statement: `D5/S1/Dynamics/Shadowing/FreeFibreBoundary.claim`

*Formalization.* `D5/S1/Dynamics/Shadowing/FreeFibreBoundary.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dekui Peng (2026). *Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse Limits*. URL: <https://arxiv.org/abs/2606.14435v3>.

*Commentary.*

For every compact Hausdorff space X with a continuous forward map f and finite-open-cover shadowing, there should exist a compact Hausdorff zero-dimensional space Y with a continuous forward map tau and shadowing, together with a continuous onto q:Y to X satisfying q composed tau equals f composed q. The statement retains arbitrary fibres, transients, dynamics, and natural time zero.

**Theorem 1.7 (Question 5.1 is refuted).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/FreeFibreBoundary.result` (`✓ std3`). ∎

*Resolves.* `Problems/peng-2026-zero-dimensional-shadowing-extension` (refuted) by `D5/S1/Dynamics/Shadowing/FreeFibreBoundary.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"peng-2026-zero-dimensional-shadowing-extension","declaration_gid":"D5/S1/Dynamics/Shadowing/FreeFibreBoundary.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Dekui Peng (2026). *Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse Limits*. URL: <https://arxiv.org/abs/2606.14435v3>.

*Commentary.*

Use the supplied compact Hausdorff continuous open surjection p:T to the one-point compactification of the naturals with no compact Hausdorff zero-dimensional open resolution. Choose the locally deciding generic binary name, form the first-disagreement pullback, and append the binary full shift as the core. The source is compact Hausdorff and shadows. Any cover permitted by claim produces, by the marked finite-language lemma and the clopen convergent section, an open zero-dimensional resolution of p, contradicting the supplied static witness. The construction has no metrizability, countability, onto-dynamics, invertibility, prescribed fibre, core, or transient restriction. The result establishes kernel status and repository attribution only; it makes no priority, uniqueness, publication, or official-acceptance claim.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/FreeFibreBoundary.claim`
- Truth anchor: `D5/S1/Dynamics/Shadowing/FreeFibreBoundary.finiteGraphLanguage_section_isClopen`
- Truth anchor: `D5/S1/Dynamics/Shadowing/FreeFibreBoundary.finite_initial_presentation_to_graphLanguage`
- Truth anchor: `D5/S1/Dynamics/Shadowing/FreeFibreBoundary.freeFibreSource_hasShadowing`
- Truth anchor: `D5/S1/Dynamics/Shadowing/FreeFibreBoundary.freeFibre_cover_forces_resolution`
- Truth anchor: `D5/S1/Dynamics/Shadowing/FreeFibreBoundary.result`
- Truth anchor: `D5/S1/Dynamics/Shadowing/FreeFibreBoundary.semiconj_clopen_image_is_finiteGraphLanguage`
- Dependency: [D5/S1/Dynamics/Shadowing/FiniteObservationSofic](FiniteObservationSofic.md)
- Dependency: [D5/S1/Dynamics/Shadowing/OpenCoreShadowing](OpenCoreShadowing.md)
- Dependency: [D5/S3/Topology/AlmostDisjoint/AdaptiveRefinementCounterexample](../../../S3/Topology/AlmostDisjoint/AdaptiveRefinementCounterexample.md)
