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

**Computed, general-order obstruction:** for the periodic chain at $L=6$,
$A=\{0,1\}$, $B=\{2,3\}$, $C=\{4,5\}$, $t=1$, every field one,
every phase zero and initial state $|r⟩^{\otimes6}$, exact arithmetic gives
$2𝓔(1)=2\log(41/25)=0.98939248367221410933\ldots$ and
$I^{(2)}_{A:B}(1)=2\log(625/497)=0.45832324727954554394\ldots$.
Their difference is $2\log(20377/15625)>0$, so the general-$α$ equality
fails at $α=2$ in this one-kick early-regime instance.
The computed reduced-state and marginal purities are all $247009/390625$;
the partial-transpose trace norm is $41/25$.
**Open:** extending this discrepancy to every block size $\ge2$ is not
established by this $2/2/2$ computation.

**Computed, product-of-pairs coincidence:** at $t=1$ the same $L=6$ state
has $2𝓔(1)=I^{(1/2)}_{A:B}(1)=2\log(41/25)$ exactly. The square-root
traces of both marginals and the joint reduced state are all $41/25$.
For the second tested instance, $L=9$, blocks $3/3/3$, every field one
and the source's generic parameters $θ_i=φ_i=1$, the two measures both give
$1.07073215876048042531\ldots$ at $t=1$.
After removing block-local kick, field and internal controlled-Z gates,
these one-kick instances are products of three boundary pairs; tracing $C$
leaves two local mixed factors and one pure pair shared by $A$ and $B$.
The $L=9$ numerical difference is below $5\times10^{-80}$ at 80 decimal
digits of working precision. These are the two tested product-of-pairs
instances; a uniform statement for untested states or block sizes remains open.

**Computed, source-parameter late-time obstruction:** for the periodic chain
at $L=9$, $A=\{0,1,2\}$, $B=\{3,4,5\}$, $C=\{6,7,8\}$,
every field one and $θ_i=φ_i=1$, literal $U_KU_I$ evolution gives:

| $t$ | $2𝓔(t)$ | $I^{(1/2)}_{A:B}(t)$ | $2𝓔-I^{(1/2)}$ |
| --- | --- | --- | --- |
| 2 | 1.90965474035335934242 | 1.87948241846317954029 | 0.03017232189017980213 |
| 3 | 1.79478990018210113283 | 2.05114059682648315862 | −0.25635069664438202579 |

Thus equality fails at the two computed times $t=2,3$.
**Open:** “every $t\ge2$” is not established by this table.

These three computed items were independently recomputed by the codex-cli
implementation seat. Their candidate setups are attributed to the search
seat and Claude Code orchestrator in #13296. The checks use SymPy 1.14.0
for exact $L=6$ spectra, and mpmath 1.3.0 at 60 and 80 decimal digits for
$L=9$; the displayed 50-significant-digit outputs agree between precisions.
The half-order numerical entropy treats eigenvalues of magnitude at most
$10^{-\mathrm{dps}+8}$ as zero; normalization errors are below $2\times10^{-80}$
at 80 digits. The calculations are computed evidence, not additional Lean proofs.
The script computes partial traces and partial-transpose spectra from the
states; the exact one-kick check uses their periodic controlled-Z representative,
whose omitted field and kick factors are local unitaries.

Script: `/Users/auric/.sshx/6655bf963c7b2d7d963c5f20/attempt-1/triage-compute.py`; SHA-256:
`61cf4809591718e2ab448bde137ba261c20c85da78b2f8cb98c226add7b3fa66`.

| Computation command | Exit |
| --- | --- |
| `python3 /Users/auric/.sshx/6655bf963c7b2d7d963c5f20/attempt-1/triage-compute.py alpha2` | 0 |
| `python3 /Users/auric/.sshx/6655bf963c7b2d7d963c5f20/attempt-1/triage-compute.py pairs-half` | 0 |
| `python3 /Users/auric/.sshx/6655bf963c7b2d7d963c5f20/attempt-1/triage-compute.py generic-half` | 0 |

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
