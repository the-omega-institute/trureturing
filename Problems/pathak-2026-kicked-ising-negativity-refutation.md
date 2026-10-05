---
slug: pathak-2026-kicked-ising-negativity-refutation
bibkey: pathak2026mixedstate
doi: 10.48550/arXiv.2603.14292
url: https://arxiv.org/abs/2603.14292v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.result
---

# Pathak's generic-state negativity conjecture

## Problem

T. Pathak, *Mixed-State Entanglement in a Minimal Model of Quantum Chaos*,
arXiv:2603.14292v1, Conjecture 1, p. 3, states:

> 2𝓔(t) = I_{A:B}^{(α)}(t), hold for generic states at all times t.

The periodic kicked Ising chain has $J=π/4$, $b=-π/4$ and arbitrary real
longitudinal fields, with $U=\exp(-iH_K)\exp(-iH_I)$.
Its initial state is the source's product of Bloch-angle qubit states.
“Generic” excludes both the all-transverse class and the all-longitudinal class.
The target in #13296 is the exact finite-chain equality at $α=1/2$ for every
chain length, field, generic product state, contiguous nonempty tripartition
and integer time. Refuting this specialization refutes the equality asserted
for all Rényi orders; it does not refute each order separately.

## Motivation

`D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.result` proves
`¬ claim`. Its definitions retain the literal Hamiltonians, matrix exponentials,
product state, partial trace, partial transpose and trace norm.
The result separates an exact finite-chain assertion from an asymptotic or
approximate relation.

## Gap

Tier 1: the source states a named conjecture. Issue #13296 reports inspection
of the three citing papers arXiv:2606.02207, arXiv:2606.11311v3 and
arXiv:2608.09695 without a settlement, and no MathDB or formal-conjectures
record. These are preregistration-reported literature readings,
`not-found-in-searched-scope`, rather than an exhaustive novelty certificate.
The source statement and literal model are independently checked against the
primary v1 source. Repository name and conclusion-shape searches do not find
a frozen owner of this model-level refutation.

## Route

Inside the settling theorem, take $L=4$, $A=\{0\}$, $B=\{1\}$, $C=\{2,3\}$,
$t=1$, every field equal to one and every phase zero.
The angles are $(π/2,π/2,2\arctan(1/2),2\arctan(1/2))$, giving
$|+⟩|+⟩|r⟩|r⟩$, where $|r⟩=(2|0⟩+|1⟩)/\sqrt5$.
The literal Floquet operator factors as $-W^{\otimes4}G$, where $W$ is unitary
and $G$ is the periodic controlled-Z product. Subsystem local unitaries
preserve both entanglement measures. Finite matrix certificates determine
the spectra before those unitaries, and injectivity of the real logarithm
on positive arguments gives the contradiction.

## Falsifier

The reduced state's spectrum is $\{16/25,4/25,4/25,1/25\}$.
Its partial transpose has spectrum $\{23/50,17/50,17/50,-7/50\}$;
both marginals are half the identity. Consequently
$2𝓔(1)=\log(1024/625)$ while $I^{(1/2)}_{A:B}(1)=\log(100/81)$.
The rational arguments differ. The witness is a legal contiguous partition
and a generic state at positive integer time.

## Evidence

The frozen settling declaration is
`D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.result`.
All spectral identities, the Floquet reduction and local-unitary invariance
used here occur on its live proof path. The module has fourteen public
definitions and one public theorem; no private theorem or lemma is exported.
Its axiom closure is contained in `{propext, Classical.choice, Quot.sound}`.
The Blueprint carries a `Refuted` open-problem resolution claim referencing
this dossier and the settling declaration. The literature locator is
`Library/QuantumStates/pathak2026mixedstate.md`.

## Triage

Refuted through the external named open-problem admission basis of
CLAUDE.md §3.2, preregistered in #13296. The settling `result` has
`proof_shape: bind-only`, `escape_witness: none` and
`admission_basis: open-problem-resolution (#13296; Refuted)`.
Its certified-instance utility is the refutation of `claim`.
Information-escape registration is paused under CLAUDE.md §3.9.

### What the settlement shows

**Proved inside `result`:** genericity alone does not enforce equality of
negativity and half-order Rényi mutual information. In this legal four-site
state, the negative partial-transpose eigenvalue gives trace norm $32/25$,
while the reduced-state square-root trace is $9/5$. The two logarithmic
expressions therefore differ despite maximally mixed marginals.
The final local kick and field unitaries preserve this discrepancy.

**Proved inside `result`:** the witness lies outside both solvable classes,
so it supplies no counterexample to assertions restricted to either class.
The source's solvable-class early-time derivations retain their stated hypotheses;
those derivations are literature results, not additional conclusions of this module.

**Open in this module:** the nearest unresolved extension is the half-order
relation for generic states in the thermodynamic early-time regime.
No claim about that relation follows from this finite-chain witness.
No inference in the source relying on the unrestricted Conjecture 1 can
use that exact equality universally. Its separate approximate, typical-state,
Haar-limit and early-time claims require their own hypotheses and evidence.

## ASSUMED-UNVERIFIED

The bounded literature search does not establish worldwide priority.
The interpretation of the source's tensor-product notation as the finite
matrix model is explained by the public literal definitions and reviewed
for fidelity; no separate infinite-chain or thermodynamic-limit construction
is formalized. The result refutes the exact finite-chain half-order identity,
not an asymptotic, approximate, large-block or typical-state reformulation.
