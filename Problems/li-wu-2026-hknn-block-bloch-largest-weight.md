---
slug: li-wu-2026-hknn-block-bloch-largest-weight
bibkey: liwu2026j1j2rings
doi: 10.48550/arXiv.2604.23149
url: https://arxiv.org/abs/2604.23149v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight.result
---

# The largest Bloch weight in the HKNN state

## Problem

Zimeng Li and Ning Wu, *Exact momentum-space analysis of small spin-1/2
J1-J2 rings*, arXiv:2604.23149v1, conjecture after Eq. (47), p. 12:

> Thus, we conjecture that this property holds for arbitrary even number N,
> i.e., the Bloch state |ξ1,1,...,1(−π)⟩ (there are N/2 − 1 1’s) should have
> the largest weight in |ψHKNN(N)⟩.

Eq. (6), p. 4, defines the unnormalized HKNN vector by summing the products
of singlets over every pair partition, with each pair's smaller endpoint
first and no permutation sign. The singlet is
[i,j] = |↑⟩i|↓⟩j − |↓⟩i|↑⟩j. The normalized Bloch states are the nonzero
translation sums of computational-basis configurations, divided by their
Hilbert norms; Eq. (7) gives the N=6 examples.

## Motivation

The conjecture identifies the configuration with all down spins consecutive
as the largest component of the HKNN singlet in the momentum basis. The
frozen declaration D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight.result
establishes the strict comparison for every positive even size and all
momenta, excluding only the same block ray up to translation phase.

## Gap

Issue #12736 preregisters the quantified statement as Tier 1. Its literature
check reports the explicit conjecture in arXiv v1, no forward citation at
Semantic Scholar, no INSPIRE entry and no proof among MathDB searches for
HKNN, Hamada-Kane-Nakagawa-Natsume, small spin-1/2 J1-J2 rings, J1-J2 ring
Bloch state, momentum-space J1-J2 rings and HKNN ground state largest weight.
Those readings are attributed to the Claude Code orchestrator on Anthropic
Claude Opus 5.5. They establish not-found-in-searched-scope, not worldwide
priority. The implementation checks the v1 source and repository ownership.

## Route

Crossing pairings correspond to bijections from down sites to up sites.
The supported coefficients are signed counts of these bijections. On the
block every supported term has the same sign. Transporting the bijections
makes their count independent of the balanced configuration. A prescribed
interleaving of two down and two up sites allows an image swap that reverses
one sign. Cyclic convexity shows that a balanced non-arc contains one of the
two complementary interleavings, so its coefficient has a strict deficit.

Translation changes every coefficient's sign because exactly one pair
crosses the cyclic cut. The finite Fourier sum therefore selects momentum
π, equivalent to −π. The block has N distinct translates. Cauchy-Schwarz
against the HKNN vector truncated to the competitor's orbit, whose size is
at most N, promotes the strict coefficient deficit to a strict normalized
weight deficit. This also covers shorter translation orbits.

## Falsifier

For every natural m≥1, let N=2m and let middle be the Fin N constructor with
value m. The block Bloch vector at middle is nonzero. For every Boolean
configuration σ on Fin N and every t in Fin N, if its Bloch vector is
nonzero and σ is not a translate of the block at t.value=m, then its weight
is strictly smaller than the block's weight at middle.

False means up and true means down; site i represents paper site i+1.
Pairings use the existing fixed-point-free involution carrier. Translation
uses the predecessor modulo N. The weight is the squared complex overlap
divided by both squared Hilbert norms. There is no balanced-sector
hypothesis on the rival. A counterexample to this exact statement would
contradict the kernel-checked result in its stated axiom system.

## Evidence

The Lean chain consists of PairingCoefficients.pairing_data,
ArcCoefficients.strict_coefficient_non_arc and
SpectralComparison.spectral_comparison, followed by result : claim in the
settling module. The foundations construct the coefficient, cyclic-order
and finite-support facts; the result applies them. The public theorem
closures use only propext, Classical.choice and Quot.sound.

Exact enumeration uses rational arithmetic:
`python3 /tmp/op-lit/r40/hknn.py`. It enumerates balanced down sets and
bijections to their complements, and compares translation-orbit weights
for N=4,6,8,10,12. These are computations, not Lean proof inputs.

| N | Block weight | Runner-up weight | Gap |
| --- | --- | --- | --- |
| 4 | 1 | 0 | 1 |
| 6 | 27/34 | 3/34 | 12/17 |
| 8 | 18/31 | 9/62 | 27/62 |
| 10 | 1125/2764 | 405/2764 | 180/691 |
| 12 | 6075/21844 | 675/5461 | 3375/21844 |

## Triage

Tier 1. Resolution: Proved by the settling result, under
admission_basis: open-problem-resolution (#12736). Its proof_shape is
bind-only and its escape_witness is none. Each foundation's public theorem
has proof_shape: content and admission_basis: escape-witness. Utility:
none; the proof is uniform in m and uses no finite positive certificate.
Information-escape registration is paused under CLAUDE.md §3.9.

### What the settlement shows

- **Proved in the chain:** the decisive signed-count mechanism uses a
  down-to-up bijection for each crossing pairing. Balanced-sector counts
  are equal; block terms have one sign. Translation transports maximal
  modulus to every cyclic arc. Every non-arc has strictly smaller modulus
  than K, including the unbalanced configurations whose coefficient is
  zero. The interleaving sign exchange requires prescribed partners; it
  does not assert that every arbitrary partner swap reverses the sign.
- **Proved in the chain:** the block Bloch norm squared is N, the block
  weight is N K²/‖psiVector‖², and all other momenta have zero weight.
  The strict comparison includes every nonzero full-period Bloch sum,
  without a full-orbit-length or balanced-sector assumption on the rival.
- **Open here (not separately kernel-checked):** the sharper integer
  estimate |c_D|≤K−2 for non-arcs and the explicit identity K=m!. The
  chain states |c_D|<K and defines K as a crossing-pairing cardinality.
  Neither stronger formula is an additional theorem of this delivery.
- **Computed:** the table above gives the block and runner-up weights and
  their gap for N≤12. Each enumerated orbit obeys c_(TD)=−c_D and the top
  orbit is the block. Large-N behavior of the weight gap is open.
- **Open:** the analogous largest-weight statement for the
  Majumdar-Ghosh dimer states and the identity of the second-largest
  Bloch state for all N. These are follow-up candidates.
- **Source consequence:** the all-even-N largest-component assertion
  stated as a conjecture in the Introduction, after Eq. (47) and in the
  concluding discussion is established for the explicit Eq. (6) vector.
  The paper's N=6 and N=8 calculations are consistent with this result.
  Its Hamiltonian ground-state identification, the other spectral
  calculations and the bound-state interpretation are supplied by the
  source and are not new theorems of this chain.

## ASSUMED-UNVERIFIED

Worldwide priority is not established by the searched literature scope.
Lean verifies the explicitly defined vector and comparison, not its
identification as a Hamiltonian ground state. The full-period Bloch sum is
interpreted through the paper's normalized ray convention; the paper's
orbit-period sum and overall phases give the same nonzero ray. The
quantitative sharpening and the neighboring questions above remain
unformalized in this delivery.
