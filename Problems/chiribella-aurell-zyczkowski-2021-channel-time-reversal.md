---
slug: chiribella-aurell-zyczkowski-2021-channel-time-reversal
bibkey: chiribellaaurellzyczkowski2021symmetries
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

For every natural dimension $d \ge 2$, `IsChannelSymmetry S` is the
predicate saying that `S` is a bijection of the completely positive
trace-preserving maps on $d\times d$ complex matrices and preserves every binary
randomisation. The claim requires that no such `S` sends every unitary channel
`Ad_U` to `Ad_{U†}`, and that none sends every `Ad_U` to `Ad_{Uᵀ}`.

## Motivation

Section V.B, PDF page 7, identifies the extra hypothesis in the prior channel
no-go theorem of Chiribella–Liu (Ref. [56]):

> An interesting open question is whether our no-go theorem remains valid for the subset of quantum channels. A no-go theorem for time reversal symmetries of quantum channels has been recently proven in Ref. [56], under the additional assumption that time reversal should reverse the order in which processes take place in any time sequence. We conjecture that this assumption can be lifted, and that the no-go theorem to time reversal applies also to symmetries of the set of quantum channels.

The settlement removes the assumption that time reversal reverses composition
order. The positive result for bistochastic channels in Section V.A is a
separate boundary of the source's full-channel question.

## Gap

Section V.B of the cited 2021 paper states this as a conjecture. The formal
settlement is `D5/S3/QuantumChannels/ChannelTimeReversalNoGo.result : claim`.
The literature status of Aw, *Int. J. Quantum Inf.* (2026), DOI
10.1142/S0219749925300049, is `ASSUMED-UNVERIFIED`: the available Firecrawl
request returned HTTP 402, so that work was not read.

## Route

For $d \ge 3$, `Part1Finish.Bi_basic` supplies the finite-block identities
forced by the unitary mixtures. Applied to positive outputs of the full
channel set, `Part1Finite.diagonal_contradiction` forces every diagonal entry
of a block of trace $1$ to vanish, so that its trace is $0$.
`Part1NoGo.inverse_unitary_no_go` obtains the contradiction without using
bijectivity in its derivation.

For $d=2$, `QubitUnitalAction.finite_pauli_identity` and
`QubitUnitalAction.unital_reversed` determine the action on unital channels.
Unitalisation and `QubitPreimage.pure_preimage` give a pure replacement
preimage, and `QubitRotation.pure_density_rotation` represents its density
matrix as a unitary rotation of a rank-one projector.
`QubitNoGo.forced_witness_output` forces an amplitude-damping output to equal
$\operatorname{diag}(9/8,-1/8)$. Its negative diagonal entry contradicts
positivity in `QubitNoGo.inverse_unitary_no_go`.

`transpose_target_reduces_to_star` uses double transposition, which preserves
complete positivity, trace preservation and randomisations and is involutive,
to reduce the transpose target to the adjoint target. The theorem `result`
combines the two dimension cases and the two targets.

## Falsifier

The result would be falsified by a compiled `IsChannelSymmetry` on some
dimension $d \ge 2$ satisfying either universal unitary target, or by a failure of
the positivity contradiction in the stated finite mixtures. The proof keeps
the full channel set, binary randomisations for every real probability in
$[0,1]$, and both target quantifiers on its live Lean path.

## Evidence

The kernel-checked module is
`D5/S3/QuantumChannels/ChannelTimeReversalNoGo.lean`. Its public declarations
are `IsChannelSymmetry`, `unitaryChannel`, `claim`, and `result`; the supporting
lemmas are consumed internally by `result`. The module imports the existing
`IsCPTP` owner and the published channel, matrix, Pauli, Kraus, and positivity
owners recorded in its dependency block. The public definition
`unitaryChannel` is the composition of left multiplication by $U$ and right
multiplication by $U^\dagger$ specified in #16378, and `claim` uses it in both
targets. The consumed private lemma `unitary_channel_eq` identifies this
composition with Mathlib's `LinearMap.mulLeftRight`. The permutation argument
uses `HaarTwoCopyTwirl.permutationUnitary`; the qubit positivity argument uses
`RenyiInformationCombiningOrderThree.unit_psd`. The finite-block positivity argument
uses `D5.S3.Quantum.Fibers.RankOneFeedbackProtocol.projector_positive`.

The escape audit is unfinished under [#16722](https://github.com/the-omega-institute/trureturing/issues/16722).
The unregistered targets are `ChannelTimeReversalNoGo.result`,
`ChannelTimeReversalNoGo.unitaryChannel`, `IptPptSquaredEquivalence.cp_comp`,
`IptPptSquaredEquivalence.cp_double_tau`,
`SeparableStateLocalUnitaryStabilizerObstruction.pauli_square`,
`SeparableStateLocalUnitaryStabilizerObstruction.pauli_projector_trace`,
`RenyiInformationCombiningOrderThree.unit_psd`,
`HaarTwoCopyTwirl.permutationUnitary`, and
`D5.S3.Quantum.Fibers.RankOneFeedbackProtocol.projector_positive`.
No `declared_validated` registration is claimed. The result proves the
conjecture and is not a designated refutation-result exemption.

The experiment entry is
[the pinned check directory](https://github.com/the-omega-institute/trureturing-experiments/tree/6a407664a24c54c1992ebf59d6b4ba8b9146d845/docs/reports/chiribella-aurell-zyczkowski-2021-channel-time-reversal).
Command (with `set -o pipefail`): `git -C /Users/auric/trureturing-experiments show 6a407664a24c54c1992ebf59d6b4ba8b9146d845:docs/reports/chiribella-aurell-zyczkowski-2021-channel-time-reversal/check.py | python3 -`, exit $0$, `ALL_OK`;
script SHA-256 `ddebc31101db2f2706ee1be8f9d1c082847f5e4a2d69097f29f56be0aed8b3d8`.
The exact checks cover the forced stochastic-matrix entry $-1/d$ at
$d=3,4,5,6,7,8$ and the amplitude-damping Bloch arithmetic
$3(3/16)^2=27/256<9/16$. The floating-point check covers the
transpose-conjugation identity on five random $3\times3$ unitaries with seed
$1$ and tolerance $10^{-12}$. These computations concern an alternative
explanation and do not establish a uniform extension or a kernel-checked
Bloch-shear argument.

## Triage

### What the settlement shows

- **Proved (kernel-checked):** no randomisation-consistent bijection of the
  full CPTP channel set sends every unitary channel to its adjoint channel
  (`result`, first conjunct).
- **Proved (kernel-checked):** no such bijection sends every unitary channel to
  the channel induced by matrix transpose (`result`, second conjunct).
- **Proved (kernel-checked mechanism):** `Part1Finish.Bi_basic` and
  `Part1Finite.diagonal_contradiction` give the finite-block trace contradiction
  for $d \ge 3$. `QubitUnitalAction.finite_pauli_identity`,
  `QubitUnitalAction.unital_reversed`, `QubitPreimage.pure_preimage`,
  `QubitRotation.pure_density_rotation`, and `QubitNoGo.forced_witness_output`
  give the qubit positivity contradiction. `transpose_target_reduces_to_star`
  reduces the second target; `result` combines them.
- **Computed:** the pinned experiment entry in Evidence runs
  `docs/reports/chiribella-aurell-zyczkowski-2021-channel-time-reversal/check.py`
  at commit `6a407664a24c54c1992ebf59d6b4ba8b9146d845`; it exits 0 with
  `ALL_OK`, has SHA-256
  `ddebc31101db2f2706ee1be8f9d1c082847f5e4a2d69097f29f56be0aed8b3d8`, and
  tests $d=3,4,5,6,7,8$, the exact amplitude-damping calculation, and
  five seeded random $3\times3$ unitaries.
- **Proved in prose (scope of the statement):** Part I uses preservation of
  randomisations and positive trace-one outputs, without invoking bijectivity;
  the qubit argument uses surjectivity in `QubitNoGo.inverse_unitary_no_go`.
  The hypotheses of `claim` contain neither composition reversal nor a
  bipositive extension, so `result` proves the no-go statement without either
  additional assumption. This is the consequence for the prior
  Chiribella–Liu result (arXiv:2012.03859) identified by Section V.B.
- **Open (scope of this formalization):** the source’s positive result for
  bistochastic channels in Section V.A is not formalized here. It is a
  published positive boundary; the theorem concerns the full channel set.
- **Literature open:** the completeness of the post-2021 literature remains
  `ASSUMED-UNVERIFIED` because Aw (2026) was unread.

The Scribe attaches one `OpenProblemResolutionClaim` with resolution
`Proved` to the settling declaration `result`.

## ASSUMED-UNVERIFIED

Escape registration is unfinished under [#16722](https://github.com/the-omega-institute/trureturing/issues/16722)
for `result`, `unitaryChannel`, `cp_comp`, `cp_double_tau`, `pauli_square`,
`pauli_projector_trace`, `unit_psd`, `permutationUnitary`, and
`projector_positive`, with the owners
listed in Evidence. The source reconstruction, lawful interventions and
variation/sensitivity/dependence evidence remain unregistered. No
`declared_validated` registration is claimed.

Aw (2026), DOI 10.1142/S0219749925300049, was not read because the available
Firecrawl request returned HTTP 402. No claim about that paper’s contents is
used by the Lean proof.
