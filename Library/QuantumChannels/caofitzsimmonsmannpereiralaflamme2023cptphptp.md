---
bibkey: caofitzsimmonsmannpereiralaflamme2023cptphptp
authors: Ningping Cao; Maxwell Fitzsimmons; Zachary Mann; Rajesh Pereira; Raymond Laflamme
year: 2023
title: "Quantum Maps Between CPTP and HPTP"
doi: null
url: https://arxiv.org/abs/2308.01894v1
claim: "A Hermiticity-preserving trace-preserving map is semi-positive (SP) if some invertible density has an invertible density image, and semi-nonnegative (SN) if some density has a density image (Definitions 1–2); SN is equivalent to Ψ ∘ Φ = Ξ for CPTP Φ, Ξ (Theorem 2). The authors conjecture that non-SP SNTP maps still signal no information backflow in higher dimensions (Outlook)."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation
license: citation-only
triage: anchor
---

# Cao, Fitzsimmons, Mann, Pereira and Laflamme, quantum maps between CPTP and HPTP

N. Cao, M. Fitzsimmons, Z. Mann, R. Pereira and R. Laflamme, *Quantum Maps Between CPTP and HPTP*, arXiv:2308.01894 [quant-ph] (v1 3 August 2023, the only version). The arXiv record lists no DOI or journal reference.

## Verified locator

Primary version read: https://arxiv.org/abs/2308.01894v1; the text was read from the PDF.
- page 3: Definition 1 (SP and SPR);
- page 4: Definition 2 (SN) and Theorem 2;
- page 5: Example 2;
- pages 6–7: the Outlook, with the conjecture;
- the supplementary material on Example 2.

## Source statements

Definition 1: "Let H and K be finite-dimensional Hilbert spaces. An HP map Ψ : B(H) → B(K) is said to be semi-positive (SP) if there exists an invertible density matrix ρ such that Ψ(ρ) is also an invertible density matrix. The map Ψ is said to be semi-positive after reduction (SPR) if Ψ as a map into B(K_Ψ) is SP, where K_Ψ = Span(⋃_{a∈B(H)} Range(Ψ(a)))."

Definition 2: "A HPTP map Ψ : B(H) → B(K) is said to be semi-nonnegative (SN) if there exists a density matrix ρ such that Ψ(ρ) is also a density matrix."

Theorem 2: "Let H and K be finite dimensional Hilbert spaces and let Ψ be an HPTP map from B(H) to B(K). Then TFAE 1. Ψ is semi-nonnegative. 2. There exist CPTP maps Φ : B(H) → B(H) and Ξ : B(H) → B(K) such that Ψ ∘ Φ = Ξ."

Outlook: "The single qubit non-SP SNTP maps only send one pure state to a pure state … For the physical scenarios that these maps can characterize, information backflow would not happen, and these maps are not uniquely defined. … Non-pure, not full-rank states comprise flat facets on the surface of D. A non-SP SNTP map can map one of those facets (or part of it) to valid quantum states. We conjecture that non-SP SNTP maps still signal no information backflow and are not uniquely defined even for higher dimensional H."

The source cites for information backflow [11] H.-P. Breuer, E.-M. Laine, J. Piilo and B. Vacchini, Rev. Mod. Phys. 88, 021002 (2016), and [20] S. Chakraborty and D. Chruściński, Phys. Rev. A 99, 042105 (2019).

## Reading used by the repository

Information backflow is the increase of the trace distance D(ρ, σ) = ‖ρ − σ‖₁/2 between two states under the intermediate map Ψ of a context Ψ ∘ Φ = Ξ (Theorem 2), with Φ and Ξ given by finite Kraus families. The repository addresses the first conjunct of the conjecture, "signal no information backflow"; a counterexample to it refutes the conjunction.
