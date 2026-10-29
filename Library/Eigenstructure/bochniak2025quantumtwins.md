---
bibkey: bochniak2025quantumtwins
authors: Arkadiusz Bochniak; Igor Chełstowski; Paweł Kasprzak; Piotr M. Sołtan
year: 2025
title: "Quantum Mycielskians: symmetries, twin vertices and distinguishing labelings"
doi: 10.48550/arXiv.2502.10521
url: https://arxiv.org/abs/2502.10521v2
claim: "Definition 3.8 defines quantum twin vertices through two distinct actions agreeing after adjacency; Question 3.17 asks whether K₂ □ K₅, C₄ □ C₃ and the tesseract possess them."
strata_touched:
  - D5/S3/Quantum/BochniakChelstowskiKasprzakSoltanQuantumTwins
license: citation-only
triage: anchor
---

# Quantum Mycielskians and quantum twin vertices

## Verified locator

DOI: 10.48550/arXiv.2502.10521

Source: https://arxiv.org/abs/2502.10521v2

## Source statements

Definition 3.8, p. 10:

> Let G = (V_G, ψ_G, A_G) be a quantum graph and H be a compact quantum group. We say that G has H-twin vertices, or simply H-twins, if there exists a pair of different actions of H on G ρ₁, ρ₂ : C(G) → C(G) ⊗ C(H) such that ρ₁ ∘ A_G = ρ₂ ∘ A_G. (4) We say that G has quantum twin vertices if there exists a quantum group H such that G has H-twins.

Question 3.17, p. 13:

> Do the above-mentioned graphs possess quantum twin vertices?

The graphs preceding the question are K₂ □ K₅, C₄ □ C₃ and the tesseract. The same question is numbered 3.16 in version 1. For a classical finite graph the function algebra is V → ℂ, with pointwise operations, and its adjacency operator is the adjacency matrix acting on functions.

## Algebraic interpretation

The repository theorem excludes two distinct unital complex algebra homomorphisms agreeing after adjacency, for every complex target algebra B. This strengthens the negative answer: a compact quantum group action is such a homomorphism into C(G) ⊗ C(H). The compact quantum group axioms and this action-to-homomorphism passage are not formalized in the module.

The tesseract graph is the graph on Fin 4 → Bool with adjacency hammingDist u v = 1. Its expression is inlined in the claim and identified with the existing Boolean hypercube in the proof. The other two graphs use SimpleGraph.completeGraph, SimpleGraph.cycleGraph and SimpleGraph.boxProd directly.

Remark 3.9 gives ordinary twins ⇒ quantum twins. Combined mathematically with the module's finite twin-free rigidity theorem, this gives equivalence for finite classical graphs; the converse action construction remains outside the Lean formalization.

## Evidence boundary

The exact finite graph experiment belongs to the private repository the-omega-institute/trureturing-experiments, commit 9f3dcb3baf7b3b158f03f978e2374438ab86873f, at docs/reports/bochniak-chelstowski-kasprzak-soltan-2025-quantum-twin-vertices/check.py. Its source SHA-256 is ac23852c0ba3c73e653eb13498b478dca8b75a4e91d3ea1b12395e56d153fed0; its exit-0 output SHA-256 is 7649c10a9c8149e0f95ab4d1091a090e0bde0255facd9414e396e84b998f6069. The experiment is supporting computation, not the kernel proof.

The source and the literature screen are recorded in issue #19959. Completeness of that screen is ASSUMED-UNVERIFIED; no exhaustive novelty claim is made.
