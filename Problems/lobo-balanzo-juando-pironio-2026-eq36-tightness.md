---
slug: lobo-balanzo-juando-pironio-2026-eq36-tightness
bibkey: lobo2026generalized
doi: 10.48550/arXiv.2605.16151
url: https://arxiv.org/abs/2605.16151v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/LossyQubitPartialJMTightness.result
---

# Tightness of the lossy-qubit partial joint-measurability bound η ≤ 2/(2 + sin θ)

## Problem

E. P. Lobo, M. Balanzó-Juandó and S. Pironio, *Generalized measurement incompatibility*,
arXiv:2605.16151v1, call measurements $G$-jointly measurable when a common parent reproduces
them while deterministically fixing only the outcomes in the subsets $G_y$ (Definition 2). For two
lossy projective qubit measurements (Eqs. (13), (18)–(19)) with detection efficiency $\eta$, whose
axes are separated by an angle $\theta\in[0,\pi/2]$, and $G=(\{+,-\},\emptyset)$ (case (d) of
§IV.B), the paper proves $G$-joint measurability for $\eta\le 2/(2+\sin\theta)$ (Eq. (36)) and
reports that "up to machine precision, this bound is tight", from numerical solutions of the
$G$-JM semidefinite program. The verbatim statements are in
[the literature note](../Library/QuantumContext/lobo2026generalized.md).

Issue [#15638](https://github.com/the-omega-institute/trureturing/issues/15638) fixes the
reading: for all unit Bloch vectors $r_1,r_2$ and every $\eta\in[0,1]$, $G$-joint measurability
implies $\eta\,(2+\lVert r_1\times r_2\rVert)\le2$, where $\lVert r_1\times r_2\rVert=\sin\theta$.

## Motivation

Partial joint measurability bounds the detection efficiency below which lossy measurements are
useless for device-independent and semi-device-independent protocols: an eavesdropper who
learns the guessed outcomes can simulate the device. The exact threshold for case (d) decides
how much loss the protocol tolerates when only the conclusive outcomes of one input are guessed.

## Gap

Issue #15638 records the literature check before any Lean:
- arXiv lists only v1;
- the only citing work found (arXiv 2607.08709) cites the paper in its bibliography and does not
  treat case (d);
- Zenodo ("partial joint measurability", "generalized measurement incompatibility"), Crossref,
  google-deepmind/formal-conjectures and web searches return no settlement;
- earlier partial-JM work (Masini–Ioannou–Brunner–Pironio–Sekatski, Quantum 8, 1574 (2024))
  proves no such threshold;
- the repository had no partial or $G$-joint measurability result.

`not-found-in-searched-scope`.

## Route

Write $\delta=1-\eta$. For a Hermitian $2\times2$ matrix $A=a_0I+\mathbf a\cdot\sigma$ write
$\mathbf a$ for its Bloch vector; $A\ge0$ forces $\lVert\mathbf a\rVert\le a_0$.

1. **Rank-one domination.** If $0\le H\le c\,P_{r}$ for a rank-one projector $P_r$, then
   $H$ is a nonnegative multiple of $P_r$. Input 2 carries no guessing constraint, so each of its
   conclusive pieces is a multiple of $P_{\pm r_2}$, and their Bloch vectors are parallel to $r_2$.
2. **Loss pieces.** If $F,F'\ge0$ and $F+F'=\delta I$, then the Bloch vector of $F-F'$ has norm at
   most $\delta$.
3. **Two representations.** Let $D=E_+-E_-$, where $E_\beta=\sum_bE_{\beta,b|y}$; no-signalling
   makes it independent of $y$, and let $\perp$ denote the component orthogonal to $r_2$.
   - Through input 2 (steps 1–2), $\lVert D^\perp\rVert\le\delta$.
   - Through input 1, partial joint measurability gives $E_{\pm,\pm|1}=\eta P_{\pm r_1}$, so the
     Bloch vector of $D$ is $\eta r_1$ plus a loss difference. Hence
     $\lVert D^\perp\rVert\ge\eta\lVert r_1\times r_2\rVert-\delta$.
4. Therefore $\eta\lVert r_1\times r_2\rVert\le2(1-\eta)$.

## Falsifier

The statement would fail if $E_{\beta,\star|y}$ in Definition 2 subtracted the sum over $G_y$
rather than over its complement; the rendered PDF (p. 3) shows the complement.

## Evidence

The canonical source is `D5/S3/Quantum/Measurement/LossyQubitPartialJMTightness.lean` (298 lines).
- Public declarations: the model definitions `effects`, `G`, `starPart` and `GJointMeasurable`, then `claim` and `result`.
- It reuses:
  - the canonical Bloch API of `D5/S3/Quantum/Information/ActualPureQubitGeometry.lean` (`blochMatrix`, `bloch`, `blochLinear`, `blochMatrix_trace`, `bloch_blochMatrix`, `bloch_geometry_of_isHermitian`, `norm_bloch_le_trace_of_posSemidef`);
  - `FourQubitParentConstruction.hermitian_decomposition`;
  - `ConcealmentKernelNecessityRefutation.IsPOVM`;
  - `FiniteDimensional.QubitMatrix`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurement/LossyQubitPartialJMTightness.lean.json`, statement `sha256:4f33465eb90d3d1f392efa233e3190095f12d2c6efe8b34f34112aa3fe3cf33f`.

Declaration statements:
- `result`: `sha256:d5f9217ab72b99de65996ba5936dbfb685a23b711b3c625e9ee030d68c85687c`;
- `claim`: `sha256:1346121a22eb6436c53317eeeba81e2a77faf9cf98f57bf14e47a73efed0d37a`.

## Triage

Tier 1 numerical claim of a 2026 paper, preregistered in issue #15638 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |

Every other declaration is bind-only and lies on the proof path of `result` (CLAUDE.md §3.2 「有消费的辅助声明」). Utility is `none`: the module proves a universal bound, not a computational instance. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every pair of unit axes and every $\eta\in[0,1]$, $G$-joint
measurability with $G=(\{+,-\},\emptyset)$ forces $\eta\le2/(2+\lVert r_1\times r_2\rVert)$.
Together with the paper's construction (Eq. (36)), the threshold is exactly $2/(2+\sin\theta)$.

**Established inside the proof.** A positive $2\times2$ matrix dominated by a multiple of a
rank-one projector is a multiple of that projector; the Bloch vector of a difference of two
positive matrices summing to $\delta I$ has norm at most $\delta$.

**Argued, not formalized.**
- The argument uses only the conclusive pieces of input 2 and the conclusive pieces of input 1,
  so it extends verbatim to $n$ inputs with $G_1=\{+,-\}$ and $G_y=\emptyset$ for $y\ge2$: every
  $G$-JM family satisfies $\eta\,(2+\max_{y\ge2}\lVert r_1\times r_y\rVert)\le2$, that is
  $\eta\le2/(2+\sin\theta)$ with $\theta$ the largest angle of Eq. (38). This is weaker than the
  paper's Eq. (37), $\eta\le(1+\sin\theta)/(1+2\sin\theta)$, which the paper reports as tight with
  three axes; the two agree at $\theta=0$ and at $\theta=\pi/2$.

**Open.** Tightness of Eq. (37) for $n\ge3$ and of Eq. (20) for $\theta>\pi/2$ (which the paper
leaves open) is not addressed.

**Effect on the paper.** The numerical tightness claim of case (d) for $n=2$ is now a theorem.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority.
