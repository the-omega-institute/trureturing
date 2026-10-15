---
bibkey: czartowski2019tradeoff
authors: Jakub Czartowski; Daniel Braun; Karol Życzkowski
year: 2019
title: "Trade-off relations for operation entropy of complementary quantum channels"
doi: 10.1142/S0219749919500461
url: https://arxiv.org/abs/1908.03492v1
claim: "The map entropy S_map(Φ) of a channel is the von Neumann entropy of its normalized Choi–Jamiołkowski state, and S_map(Φ) = S(Φ̃(ρ*)), S_map(Φ̃) = S(Φ(ρ*)) for the complementary channel Φ̃ and ρ* = I/N (Proposition 1). For qutrit channels with a qutrit environment the authors conjecture that the lower boundary of the allowed set A_3 of pairs (S_map(Φ), S_map(Φ̃)) is the curve p(a) of Eq. (20), a ∈ (0, 1/3), together with its reflection through S = S̃."
strata_touched:
  - D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier
license: citation-only
triage: anchor
---

# Czartowski–Braun–Życzkowski, trade-off relations for the entropy of complementary channels

J. Czartowski, D. Braun and K. Życzkowski, *Trade-off relations for operation entropy of complementary quantum channels*, Int. J. Quantum Inf. **17**, 1950046 (2019), DOI 10.1142/S0219749919500461; arXiv:1908.03492 [quant-ph] (v1, the only version).

## Verified locator

DOI: 10.1142/S0219749919500461 (as listed on the arXiv abstract page).
Primary version read: https://arxiv.org/abs/1908.03492v1.
Source: https://arxiv.org/pdf/1908.03492v1 (text read from the PDF):
- §II, the Stinespring form of a channel and its complementary channel, and the map entropy;
- §III, Proposition 1, Eq. (8);
- §V, printed page 5, Conjecture 1, Eq. (20), and the attaining channels.

## Source statements

§III: "PROPOSITION 1. Consider a channel Φ acting on an N dimensional system by coupling it with the environment of dimension M. The entropy of the channel is equal to the entropy of the image of the maximally mixed state ρ* = I/N under the complementary channel Φ̃. An analogous relation holds for the complementary channel, S_map(Φ) = S(Φ̃(ρ*)), S_map(Φ̃) = S(Φ(ρ*)) (8)".

§V, page 5: "CONJECTURE 1. For qutrit channels with qutrit environment the lower boundary of the allowed set A_3 is given by the parametric curve p(a) = (−a log a − (1 − a) log(1 − a), log 3/3 − (a + 1/3) log(a + 1/3) − (a − 1/3) log(a − 1/3)) (20) with a ∈ (0, 1/3), together with reflection through line S = S̃, which contains all selfcomplementary channels Φ = Φ̃."

## Reading used by the repository

A qutrit channel with a qutrit environment is given by a Stinespring isometry V : ℂ³ → ℂ³ ⊗ ℂ³. The complementary channel exchanges the roles of the system and the environment. The map entropy is the von Neumann entropy of the normalized Choi state.

The last term of Eq. (20) is read as −(1/3 − a) log(1/3 − a). The source's attaining channels, with Kraus pair K_1 = diag(1, √(1 − 3a), 1) and K_2 = √(3a)|1⟩⟨2|, have complementary map entropy H(1/3 + a, 1/3, 1/3 − a) = log 3/3 − (a + 1/3) log(a + 1/3) − (1/3 − a) log(1/3 − a), while the printed term is not real for a < 1/3.

The conjecture is read as two statements:
- the trade-off: for every admissible V and every a ∈ [0, 1/3], S_map(Φ) ≤ h(a) implies S_map(Φ̃) ≥ g(a), and symmetrically with Φ and Φ̃ exchanged, where (h(a), g(a)) = p(a);
- attainment: the attaining family realizes (h(a), g(a)), and its complement the reflected point.
