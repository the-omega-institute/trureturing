---
slug: torii-takakura-imamura-2025-proposition-7-generalization
bibkey: torii2025comparing
doi: 10.1103/s6mc-lnvl
url: https://arxiv.org/abs/2509.08284v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.result
---

# Operational comparison of qubit incompatibility without equal lengths

## Problem

K. Torii, R. Takakura and R. Imamura, *Comparing quantum incompatibility of device sets from an
operational perspective*, Phys. Rev. A **112**, 062228 (2025), arXiv:2509.08284v2, §V:

> Future work will also address the generalization of Proposition 7, as it remains an open problem whether
> the result holds without the constraints of |a₁|=|a₂| and |b₁|=|b₂|.

Two pairs of unbiased qubit observables are operationally equivalent when, for every set $S$ of states, one
pair is $S$-compatible exactly when the other is; $S$-compatibility means that some four-outcome POVM has
both margins with the same Born probabilities as the pair on every state of $S$. Proposition 7 proves that,
for $|a_1|=|a_2|$ and $|b_1|=|b_2|$ in $(1/\sqrt2,1]$, equivalence forces equality up to signs and exchange.
The verbatim texts are in [the literature note](../Library/QuantumContext/torii2025comparing.md). Issue
[#15522](https://github.com/the-omega-institute/trureturing/issues/15522) preregisters the general statement
and the route.

## Motivation

The operational ordering compares incompatibility by the state sets on which it can be detected. If
restricted-state tests determine a pair of qubit observables up to relabelling, the ordering is as fine as
the observables themselves for unbiased qubit pairs, and the question "which incompatible pairs are
operationally interchangeable" has the trivial answer.

## Gap

The source proves coplanarity (Proposition 6, by a symmetry sketch), the equal-length case (Proposition 7)
and the mutually unbiased case (Theorem 1), and leaves arbitrary lengths open. The literature check in
#15522 found no settlement; `not-found-in-searched-scope`.

## Route

1. Two unbiased binary effects with Bloch vectors $a,b$ are jointly measurable iff
   $|a+b|+|a-b|\le2$; both directions are proved in the module.
2. Equality of all restricted compatibility relations forces the four vectors into one plane.
3. Tests with sets of states on central planes turn the region of compatible planes into the negative set
   of a quartic $f(x,y)$; equality of the regions makes every boundary zero of $f$ a zero of the second
   quartic $g$, at infinitely many points.
4. Write $b_1=u\,a_1+v\,a_2$ and $b_2=w\,a_1+z\,a_2$ in the common plane. Eliminating the two roots in
   $y$ at each such $x$ gives a polynomial in $x$ that vanishes identically; its coefficient of degree 12
   is $(uw)^2$, and the same elimination with $a_1,a_2$ exchanged gives $vz=0$. Each $b_i$ is therefore a
   multiple of a different $a_j$. A second residue, compared in degrees 6, 4 and 0, forces both
   multipliers to be $\pm1$, which is a signed permutation.
5. Relabelling outcomes and exchanging the two observables preserve $S$-compatibility for every $S$.

## Falsifier

A reading of $S$-compatibility narrower than Definition 4 (for example unbiased joint POVMs only, or the
same state set not used on both sides), an excluded sharp or boundary case, or an error in the elimination.

## Evidence

`D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.lean` defines the effects, four-outcome POVMs,
$S$-compatibility, incompatibility of a pair and `claim` (for all incompatible pairs, equality of
$S$-compatibility for every $S\subseteq D(\mathbb C^2)$ holds iff the pairs agree up to signs and exchange),
and proves `result : claim`. The axiom closure of `result` is exactly `propext`, `Classical.choice` and
`Quot.sound`; there is no `sorry` or `native_decide`.

## Triage

Tier 1: an explicitly posed open question of a 2025 journal paper, preregistered in #15522 before any Lean.
`theorem`; resolution `proved`. Admission basis `open-problem-resolution`; utility `none`. There is no
digestion atom.

### What the proof shows

- **Proved by `result`:** for unbiased qubit observables, restricted-state compatibility determines every
  incompatible pair up to signs and exchange, with no constraint on the lengths and sharp observables
  included.
- **Mechanism:** compatibility with respect to the states of one central plane depends only on the
  projections of the Bloch vectors to that plane, and the boundary of the set of compatible planes is the
  zero set of a quartic whose coefficients encode the lengths and the angle. Equality of these boundaries
  identifies the quartic up to a positive scale, and the coefficient pattern leaves no freedom beyond signs
  and exchange.
- **Correction to the source:** in the source's Eq. (16) the cross coefficient appears as
  $\cos\alpha_1\cos\alpha_2$; derivation from the projected inner products gives $\cos(\alpha_1-\alpha_2)$.
  For $a_1=(1,1,0)/\sqrt2$, $a_2=(-1,1,0)/\sqrt2$ and the plane normal $(1,0,0)$ the printed form gives
  $-1/4$, the derived one $+1/4$ (reported by the design seat of #15522; the module derives the quartic
  from the joint-measurability criterion and does not use Eq. (16)).
- **Open:** biased qubit observables, more than two observables, and higher-dimensional systems, where
  the joint-measurability region has no closed form of this kind.

## ASSUMED-UNVERIFIED

The literature check in #15522 is bounded and does not establish worldwide novelty or priority. The
numerical illustration of the Eq. (16) correction is a design-seat report, not an orchestrator reading.
