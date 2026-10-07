---
slug: erew-goldstein-2025-sic-clifford-stabilizer
bibkey: erewgoldstein2025magic
doi: 10.48550/arXiv.2512.19657
url: https://arxiv.org/abs/2512.19657v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.result
---

# A qutrit SIC fiducial that is not a Clifford-stabilizer state

## Problem

M. Erew and M. Goldstein, *Extremizing Measures of Magic on Pure States by Clifford-stabilizer
States*, arXiv:2512.19657v2, prove that states uniquely stabilized by a subgroup of the finite
eigenphase-extended Clifford group extremize several magic measures, and state:

> **Conjecture 1** (Stabilizer nature of SIC fiducials). Every SIC-POVM fiducial state is a
> Clifford-stabilizer state.

The verbatim definitions are in [the literature note](../Library/Quantum/erewgoldstein2025magic.md).
Issue [#14173](https://github.com/the-omega-institute/trureturing/issues/14173) reads it for every
prime $d$ and every normalized single-qudit fiducial.

## Motivation

The conjecture would explain the extremality of SIC fiducials for $L^p$-norm magic and stabilizer
Rényi entropies as a consequence of a stabilizer symmetry, placing them among the Clifford-stabilizer
states covered by the paper's main theorem.

## Gap

Issue #14173 records the literature check before any Lean: two arXiv versions; the only citing work
found (arXiv:2607.07197) does not discuss the conjecture; arXiv, web and Zenodo searches found no
settlement. `not-found-in-searched-scope`.

## Route

The eigenphase-extended Clifford group $\mathcal C'_{1,3}$ is finite, so there are only finitely
many Clifford-stabilizer states modulo phase. The qutrit fiducials $\psi_z=(0,1,-z)/\sqrt2$,
$|z|=1$, form a continuum of pairwise non-proportional states. This is the classical continuous
family of qutrit SIC fiducials ([Tabia and Appleby 2013](../Library/QuantumStates/tabiaappleby2013qutrit.md)
state it for $z=e^{2it}$, $t\in[0,\pi/6]$); the module proves the SIC condition for every unit $z$
directly. Hence some fiducial is not a Clifford-stabilizer state.

## Falsifier

The refutation is for the paper's definitions (single qudit, the eigenphase-extended Clifford group,
uniqueness of the stabilized line); a weaker reading, for example "an eigenstate of some Clifford
unitary", is not addressed by `result`.

## Evidence

The canonical source is `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.lean`, with public
`zeta`, `pauliGroup`, `cliffordGroup`, `specialClifford`, `Lambda`, `eigenphaseClifford`,
`invariantSubspace`, `IsNormalized`, `IsCliffordStabilizerState`, `IsSICFiducial`, `qutritFiducial`,
`claim` and `result : ¬ claim`. It reuses the frozen Weyl words `WeylDisplacement.displacement` and the
frozen commutant theorem `WindowRegister.window_commutant_eq_scalars` (the clock and shift commute only
with scalars). The axiom closure of `result` is exactly `propext`, `Classical.choice` and `Quot.sound`;
there is no `sorry`, `native_decide`, or new axiom.
The module statement is `sha256:97d15233dd8ee9b1ac6ddc959dc2a90dc9177583ce8197b03aa278178cd50c78`,
the `result` statement `sha256:c45352b51f54bba6cd4e2556959b8debb0b0fc32d95f87ee5295dedd4acb7624` and the
`claim` statement `sha256:fc36430abb9941ca4716ffe380ddde4ac06a4d1f7a5f5db9cdfb41e74403d232`. The Freeze
event is `sha256:5dea10ff83cd1d3917616e488df413626188ddb09e2c0f65ffd46b8933d33fc2`; its project-level
prerequisite is the frozen `WeylDisplacement` module.

## Triage

Tier 1 conjecture of a December 2025 paper, preregistered in issue #14173 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |

The other theorems of the module (finiteness of the special and eigenphase-extended Clifford groups
and of the stabilizer projectors at $d=3$, the fiducial property and injectivity of the qutrit
family) lie on the proof path of `result` (CLAUDE.md §3.2 「有消费的辅助声明」). Utility is
`kind=certified-instance; basis=refutes` (the claim and its refutation). There is no digestion atom.

### What the refutation shows

**Proved by `result`:** the universal claim fails at $d=3$: there is a normalized qutrit SIC fiducial
that spans no one-dimensional invariant subspace of any subset of the eigenphase-extended Clifford
group $\mathcal C'_{1,3}$.

**Established inside the proof, for general data.** $\tilde{\mathcal C}_{1,3}$, $\Lambda$ and
$\mathcal C'_{1,3}$ are finite; hence the set of rank-one projectors of Clifford-stabilizer states is
finite. Every $\psi_z=(0,1,-z)/\sqrt2$ with $|z|=1$ is a SIC fiducial, and $z\mapsto\psi_z\psi_z^\dagger$ is
injective.

**Argued and checked numerically, not formalized.**

- *Mechanism.* For three sampled values of $z$, a numerical enumeration of the 216-element
  projective Clifford group finds exactly three elements fixing the ray of $\psi_z$, and after
  rescaling to fix $\psi_z$ their common invariant space is two-dimensional; for those samples the
  fiducial is an eigenvector of Clifford elements but not the unique invariant line. That the same
  holds for every generic $z$ is `ASSUMED-UNVERIFIED`. Independently of the samples, the fiducials
  that are Clifford-stabilizer states form a finite set of rays inside the continuous family (the
  finiteness proved inside `result`).
- *What survives.* The argument says nothing about dimensions in which the fiducials are isolated
  (finitely many up to Clifford equivalence); there the conjecture may still hold, and the weaker
  statement "every SIC fiducial is an eigenvector of some Clifford unitary" is not addressed.

**Open.** Whether every SIC fiducial in a prime dimension $d\ne3$ is a Clifford-stabilizer state,
and which members of the qutrit family are, are not settled here.

**Effect on the paper.** Conjecture 1 is false as stated; the explanation it proposes for the
extremality of SIC fiducials does not cover the continuous qutrit family.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty, priority, or the
absence of an independent proof.
