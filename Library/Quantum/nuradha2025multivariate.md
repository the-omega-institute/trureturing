---
bibkey: nuradha2025multivariate
authors: Theshani Nuradha; Hemant K. Mishra; Felix Leditzky; Mark M. Wilde
year: 2025
title: Multivariate Fidelities
doi: 10.1088/1751-8121/adc645
url: https://arxiv.org/abs/2404.16101v3
claim: Multivariate SDP fidelity maximizes jointly positive block coherences and is bounded by average pairwise root fidelity; Remark 5.45 asks for a strict measured-versus-Uhlmann gap, and Section 6 item 2 asks for operational interpretations.
strata_touched:
  - D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator
  - D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation
license: citation-only
triage: anchor
---

# Joint fidelity and the explicit operational research question

## Verified source

Journal of Physics A 58(16), 165304 (2025); arXiv v3 is dated 16 June 2025. The PDF has 101 pages. Proposition 5.10, equation (5.27), gives the positive block formulation with prescribed diagonal states and the sum of real traces of off-diagonal blocks. Theorem 5.33, equation (5.80), compares the SDP fidelity with average pairwise fidelities. Both the latter theorem on printed page 29 and Section 6 item 2 on printed page 46 were visually checked in PDF screenshots. The screenshot of the page containing (5.27) failed; its parsed formula was read.

Section 6 item 2 asks for information-theoretic operational interpretations of multivariate fidelities, including the SDP version. The paper separately studies secrecy-based fidelity and unitary purification formulations; these variants must not be conflated.

## Relation to the repository task

The positive block in (5.27) directly parametrizes one population-preserving, conditional-state-calibrated recovery channel. The normalized mean of real coherences is its SDP objective. Allowing an independently measured phase for each pair gives a modulus objective, which is generally different. Both quantities are bounded by pairwise root fidelities.

The new paper derivation refines this comparison with a projective-cycle obstruction and, for three orthogonal thermal qubit states, a matching fourth-order high-temperature gap. The basic SDP-to-channel correspondence is standard and is not presented as the sole research contribution. The external operational question is used as a precise research anchor; this note does not register its full resolution, assert that no later interpretation exists, or establish global priority.

## Verified locator

DOI: 10.1088/1751-8121/adc645

Source: https://arxiv.org/abs/2404.16101v3

## Source statements

Proposition 3.1, page 9: “F(ρ, σ) := ‖√ρ √σ‖₁”.

Equation (5.13), page 18: “F_U(ρ_1, …, ρ_r) := (2/(r(r−1))) Σ_{i<j} F(ρ_i, ρ_j).”

Definition 5.40, page 32: “F_M(ρ_1, …, ρ_r) := (2/(r(r−1))) inf_{(Λ_x)_x} Σ_{i<j} F(Λ(ρ_i), Λ(ρ_j)), where Λ(ρ_i) := Σ_x Tr[Λ_x ρ_i]|x⟩⟨x| is the measurement channel induced by applying the POVM (Λ_x)_x on the state ρ_i.”

Remark 5.45, page 34: “Furthermore, it is interesting to determine whether there exists a tuple of states for which F_M(ρ_1, …, ρ_r) > F_U(ρ_1, …, ρ_r)—we leave this as an open question.”

## Scope

The affirmative answer uses three qubit density matrices: I/2, diag(3/4, 1/4), and the matrix with diagonal entries 1/2 and off-diagonal entries 1/4. The measured infimum ranges over the dependent sum of all finite POVMs, including every outcome size. The analytic estimate gives F_U < 24/25 ≤ F_M; it does not compute the exact measured fidelity or classify equality for arbitrary tuples.

The literature screen in issue #19068 found no later answer within the works it examined. Completeness of the citation census is ASSUMED-UNVERIFIED.
