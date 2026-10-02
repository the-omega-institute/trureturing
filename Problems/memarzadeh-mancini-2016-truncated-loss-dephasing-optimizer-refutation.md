---
slug: memarzadeh-mancini-2016-truncated-loss-dephasing-optimizer-refutation
bibkey: memarzadeh2016minimum
doi: 10.1103/PhysRevA.94.022341
url: https://arxiv.org/abs/1605.04525v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.result
---

# Binomial and kappa states do not exhaust truncated entropy minimizers

## Problem

Laleh Memarzadeh and Stefano Mancini, *Minimum output entropy of a
non-Gaussian quantum channel*, arXiv:1605.04525v1, Phys. Rev. A 94,
022341 (2016), section IV, Conjecture 1, state:

> In a truncated Hilbert space of dimension K+1, the minimal output entropy
> of the quantum channel (3) is achieved either by binomial states of
> Eq.(14) or by states |κ_α⟩ of Eq. (11), depending on the values of ε and t.

Issue #11680 specifies the fixed-energy reading: for every K ≥ 1,
N ∈ [0,K], ε ∈ [0,1] and t ≥ 0, some binomial or κ candidate minimizes
output entropy among positive semidefinite trace-one inputs whose number
expectation is N. Binomial candidates satisfy 1 ≤ M ≤ K, μ ∈ [0,1] and
Mμ=N; κ candidates allow every real phase α.

## Motivation

The frozen declaration
`D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.result`
proves the negation of this reading. The witness is a qutrit input of energy
3/2 outside both candidate families; its output entropy is strictly smaller
than that of every candidate at the same channel parameters and energy.

## Gap

Issue #11680 records the source version and the bounded literature search:
15 OpenAlex citing records, arXiv searches and MathDB queries. No settlement
was found in that searched scope. Not all 15 citing full texts were read.
This is not an exhaustive literature or priority claim.

## Route

1. Define the channel using the source's Kraus operators A_j P_k. The
   amplitude index is finite in the truncation; the phase index remains an
   infinite natural-number series. Sum the exponential series to derive
   the dephasing factor exp(−εt(m−n)²).
2. Take K=2, N=3/2, ε=6/7, t=(7/2)log(2) and
   ψ=(|1⟩+|2⟩)/√2. Derive the exact output matrices from those operators.
   The binomial restrictions force M=2 and μ=3/4. Diagonal unitary
   conjugation covers all real κ phases.
3. Construct strict Rayleigh bounds for the ψ output: an eigenvalue above
   1/2 and another below 1/8. Exact positive-definiteness certificates put
   every candidate eigenvalue strictly between 1/8 and 1/2. All spectra
   have total mass one. Two convex transfers and strict concavity of
   −x log(x) give the strict entropy inequalities.
4. Prove that the ψ input is admissible and contradict both candidate
   branches of the proposed minimum.

## Falsifier

The refutation concerns the Kraus-defined channel, the fixed-energy input
constraint and the two families stated in the source. It does not assert
that ψ itself is a global minimizer. The source's section-III displayed κ
output uses (1−f)^K for its off-diagonal coefficient, whereas its defining
Kraus equations give (1−f)^(K/2). At this witness the Kraus-defined
coefficient is √3/32768. Changing the channel to the displayed coefficient
would change the mathematical problem.

## Evidence

The canonical source is
`D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.lean`.
Its only public theorem is `result : ¬ claim`; the other public declarations
are the channel, observables, entropy, input constraint and candidate
families needed by that statement. It reuses
`D5/S3/Entropy/MaxEntropy.shannonEntropy` and
`D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity`.

The compiled result uses `propext`, `Classical.choice` and `Quot.sound`;
there is no `sorry`, `native_decide` or new axiom.

## Triage

Tier 1 externally named conjecture, preregistered in issue #11680.
Resolution: Refuted. `proof_shape: bind-only` for `result`;
`escape_witness: none`;
`admission_basis: open-problem-resolution (#11680; Refuted)`. Utility:
`kind=certified-instance; basis=refutes`, with typed `claim` and `result`.

### What the settlement shows

- **Proved in this module:** the energy-constrained qutrit instance admits
  an input whose output entropy is strictly below both candidate families,
  including every κ phase. The failure is the exhaustiveness of the
  proposed optimizer families; their allowed parameter ranges do not
  prevent this instance.
- **Proved in this module:** a Hermitian trace-one qutrit matrix strictly
  between (1/8)I and (1/2)I has greater entropy than the explicit ψ output.
  This is the sufficient spectral criterion used for both families.
  The Kraus series, exact outputs, strict spectral bounds and admissibility
  facts are established in the proof rather than assumed numerical data.
- **Open:** global optimality of ψ, the actual minimizers at these
  parameters, the parameter region where the two candidate families do
  minimize entropy, and the analogous conclusion for K=1.
- **Open beyond this settlement:** global optimization conclusions that
  use Conjecture 1 require independent justification. Comparisons restricted
  to the two families, including the source's ε,t crossing curve and t_*
  comparison, do not establish a minimum over all admissible inputs. The
  source's pure-state reduction lemmas and its infinite-dimensional
  low-entropy construction are not formalized or settled by this module.

## ASSUMED-UNVERIFIED

The literature absence is bounded to the search in issue #11680; the
unread citing full texts remain unverified. The Lean kernel authenticates
neither the external publication nor its version history. The spectral
entropy uses natural logarithms; the source uses base two, whose common
positive scale preserves the ordering. No separate base-conversion or
all-parameter complete-positivity theorem is exported.

Information-escape registration is paused under CLAUDE.md §3.9
「信息逃逸登记暂缓」; no `Reg` source or `declared_validated` record is part of
this delivery.
