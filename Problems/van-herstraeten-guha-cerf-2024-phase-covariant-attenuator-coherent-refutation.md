---
slug: van-herstraeten-guha-cerf-2024-phase-covariant-attenuator-coherent-refutation
bibkey: vanherstraeten2024nongaussian
doi: 10.1142/S0219749924400033
url: https://arxiv.org/abs/2312.15623v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/PhaseCovariantAttenuatorCoherentRefutation.result
---

# Van Herstraeten–Guha–Cerf Conjecture 2: coherent inputs for phase-covariant attenuators

## Problem

Conjecture 2 (Phase-covariant attenuator), section IV.B, arXiv:2312.15623v2, PDF p. 12, states: “The minimum output entropy of a phase-covariant attenuator channel ℳη,𝐩 is achieved by coherent states, ∀η,𝐩.” The domain is every transmissivity η in [0,1] and every probability vector p on the natural occupations. The assertion is that some complex coherent amplitude α minimizes the output entropy over all density operators on the full one-mode Fock space. Preregistration #11681 gives this quantifier order and the counterexample.

## Motivation

`D5/S3/Quantum/QuantumChannels/PhaseCovariantAttenuatorCoherentRefutation.result : ¬ claim` refutes the universal assertion using η=1/2, p=(7/8)δ₁+(1/8)δ₅, and the one-photon input. The model uses lp (fun _ : ℕ => ℂ) 2, with unrestricted states, amplitudes and environment support, a global two-mode beam-splitter unitary, and its square-root Kraus realization of the partial trace.

## Gap

The source supports Conjecture 2 by numerical minimization. The bounded literature check in #11681 found no settlement in the paper, Crossref, OpenAlex and the searched MathDB records; Semantic Scholar was rate-limited. This is not an exhaustive priority claim. The general equivalence of the basis-infimum entropy with spectral von Neumann entropy is literature-attested in the Wehrl note; the full Wehrl text has not been inspected and that infinite-dimensional equivalence is not kernel-proved here.

## Route

Totalness of the exponential family constructs the global displacements and beam splitter on the Hilbert completion. The beam splitter has the normalized binomial Fock action. A contraction-vector identity cancels the discarded-mode displacement, and summable rank-one ensembles establish coherent-output covariance for every probability vector. Fixed-total-occupation partial traces give the two finite output diagonals. Jensen row bounds and Parseval column sums identify their basis-infimum entropies with finite Shannon entropies. The settling proof transports all complete Hilbert bases to prove the required unitary invariance locally and certifies the strict logarithmic comparison.

## Falsifier

A mismatch between the source channel, state domain or entropy and their formal counterparts would invalidate source fidelity. Dropping coherent vectors, cutting off the ambient space, or restricting competing density operators would not settle the source assertion. A published prior settlement would change the bounded provenance conclusion. An argument for the conjecture at these parameters would contradict the formal counterexample under the stated correspondence.

## Evidence

The vacuum output has occupation probabilities (113,117,10,10,5,1)/256. The one-photon output has probabilities (115,8,117,0,5,8,3)/256. Every coherent input has the vacuum-output entropy. The exact certificate 115²·8¹⁶·3³=100507677308957491200>10²⁰, together with log(115)>log(113), gives strictly smaller entropy for the one-photon input. The chain and result are kernel-checked with only propext, Classical.choice and Quot.sound. The definition of entropy admits infinite values and arbitrary complete countable bases.

## Triage

Tier 1: an externally published conjecture whose preregistered bounded literature check found no settlement. The recorded resolution is Refuted for Conjecture 2, with no claim that the competitor is globally optimal.

### What the settlement shows

- **Proved in this module:** phase-invariant diagonal environments and displacement covariance do not suffice to make coherent inputs entropy minimizers. The explicit mixture of occupations 1 and 5 admits a lower-entropy one-photon input even though all coherent amplitudes share the same output entropy.
- **Proved in this chain and used in the module:** coherent-output covariance survives for every transmissivity in [0,1] and every probability vector. The failed step is the minimum-entropy conclusion, not that covariance identity.
- **Proved in this module:** for the pure occupation-1 environment at η=1/2, the vacuum and one-photon outputs are (1,1)/2 and (1,0,1)/2. These have the same nonzero spectrum; that equality supplies no universal minimization theorem for pure Fock environments.
- **Computed:** The exact witness distributions and integer certificate have the floating entropy values S(A)=1.0706928143706431 and S(B)=1.0629288654632991 nats, a gap of 0.007763948907343998. A finite numerical scan covers 504 floating comparisons for pure Fock environments, η in {0.1,…,0.9}, n in {0,…,7}, and m in {1,…,7}, with no violation beyond 10⁻¹²; probabilities below 10⁻¹⁵ are omitted in its entropy sum. This finite floating computation does not prove Conjecture 1.
- **Open:** Conjecture 1 for pure Fock environments, the global minimizer for this mixed environment, and a characterization of the diagonal environments admitting coherent minimizers. The source states the thermal geometric-distribution case as a known Gaussian optimizer result; that special case is literature-attested and not proved in this module.
- **Open in Lean:** the source's capacity bounds and Conjecture 3 on optimizer symmetries are not formalized here. This refutation does not settle Conjecture 3 because global minimality of the competitor is not asserted. Substitution of vacuum-output entropy for the minimum output entropy is invalid for this mixed channel. The source's capacity-bound statement with the actual minimum entropy is not refuted by this result, and its plots conditional on the separate pure-Fock Conjecture 1 are not settled by this mixed-environment counterexample.

## ASSUMED-UNVERIFIED

Citation-index completeness, exhaustive worldwide novelty, the sentence-by-sentence journal/arXiv correspondence, and the general infinite-dimensional spectral entropy equivalence are not kernel-verified. Wehrl's full text has not been inspected. The standard axiom boundary and the exact source/model correspondence remain distinct from these bibliographic boundaries. Information-escape registration is paused under CLAUDE.md §3.9 「信息逃逸登记暂缓」.
