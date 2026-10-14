---
slug: chiribella-aurell-zyczkowski-2021-channel-time-reversal
bibkey: chiribella2021symmetries
doi: 10.1103/PhysRevResearch.3.033028
url: https://arxiv.org/abs/2101.04962
triage: theorem
motivation_gids:
  - D5/S3/QuantumChannels/ChannelTimeReversalNoGo.result
---

# No randomisation-consistent time reversal on the full channel set

## Problem

Chiribella, Aurell and Życzkowski, “Symmetries of quantum evolutions”,
arXiv:2101.04962v5, Section V.B, conjecture that the no-go theorem for time
reversal continues to hold for symmetries of the full set of quantum channels:

> We conjecture that this assumption can be lifted, and that the no-go theorem
> to time reversal applies also to symmetries of the set of quantum channels.

For every natural dimension `d ≥ 2`, `IsChannelSymmetry S` is the existing
predicate saying that `S` is a bijection of the completely positive
trace-preserving maps on `d × d` complex matrices and preserves every binary
randomisation. The claim requires that no such `S` sends every unitary channel
`Ad_U` to `Ad_{U†}`, and that none sends every `Ad_U` to `Ad_{Uᵀ}`.

## Motivation

The source proves the corresponding obstruction under a bistochastic
assumption and asks whether that assumption can be removed. The result settles
the question for the full channel set and leaves the source’s positive
bistochastic result as the boundary of the argument.

## Gap

Section V.B of the cited 2021 paper states this as a conjecture. The formal
settlement is `D5/S3/QuantumChannels/ChannelTimeReversalNoGo.result : claim`.
The literature status of Aw, *Int. J. Quantum Inf.* (2026), DOI
10.1142/S0219749925300049, is `ASSUMED-UNVERIFIED`: the available Firecrawl
request returned HTTP 402, so that work was not read.

## Route

For dimensions at least three, unitary mixtures realise the classical
dephased permutation channels. A randomisation-preserving symmetry therefore
transposes the associated stochastic matrices. Averaging the four-sign and
twelve-unitary mixtures forces the transpose on all doubly stochastic matrices;
the explicit three-coordinate channel then has a negative matrix entry after
the forced reversal, contradicting positivity.

For dimension two, the proof uses the Bloch linear form. The symmetry forces the
shear terms to vanish, and an amplitude-damping channel then violates the
resulting positivity bound. Double transposition preserves complete positivity,
trace preservation, randomisations, and involution, and converts the transpose
target into the adjoint target. Thus both targets are impossible.

## Falsifier

The result would be falsified by a compiled `IsChannelSymmetry` on some
dimension `d ≥ 2` satisfying either universal unitary target, or by a failure of
the positivity contradiction in the stated finite mixtures. The proof keeps
the full channel set, binary randomisations for every real probability in
`[0,1]`, and both target quantifiers on its live Lean path.

## Evidence

The kernel-checked module is
`D5/S3/QuantumChannels/ChannelTimeReversalNoGo.lean`. Its public declarations
are the literal `IsChannelSymmetry`, `claim`, and `result`; the supporting
lemmas are consumed internally by `result`. The module imports the existing
`IsCPTP` owner and the published channel, matrix, Pauli, Kraus, and positivity
owners recorded in its dependency block. The experiment report is
`docs/reports/chiribella-aurell-zyczkowski-2021-channel-time-reversal/check.py`
in `the-omega-institute/trureturing-experiments` at commit
`6a407664a24c54c1992ebf59d6b4ba8b9146d845`; its SHA-256 is
`ddebc31101db2f2706ee1be8f9d1c082847f5e4a2d69097f29f56be0aed8b3d8` and its
recorded result is exit 0, `ALL_OK`.

## Triage

### What the settlement shows

- **Proved (kernel-checked):** no randomisation-consistent bijection of the
  full CPTP channel set sends every unitary channel to its adjoint channel.
- **Proved (kernel-checked):** no such bijection sends every unitary channel to
  the channel induced by matrix transpose.
- **Proved (kernel-checked):** the mechanism is the classical dephased
  permutation-mixture contradiction for `d ≥ 3`, together with the Bloch and
  amplitude-damping contradiction for `d = 2`; the double-transpose reduction
  covers the second target.
- **Published consequence:** the order-reversal axiom used by Chiribella–Liu
  (arXiv:2012.03859) is redundant for this no-go statement.
- **Boundary open:** the source’s positive result for bistochastic channels in
  Section V.A remains outside this settlement; only the full channel set is
  settled here.
- **Literature open:** the completeness of the post-2021 literature remains
  `ASSUMED-UNVERIFIED` because Aw (2026) was unread.

The Scribe attaches one `OpenProblemResolutionClaim` with resolution
`Proved` to the settling declaration `result`.

## ASSUMED-UNVERIFIED

Aw (2026), DOI 10.1142/S0219749925300049, was not read because the available
Firecrawl request returned HTTP 402. No claim about that paper’s contents is
used by the Lean proof.

