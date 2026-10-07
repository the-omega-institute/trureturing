---
slug: garcia-fernandez-2026-open-circuit-integrability
bibkey: garciafernandez2026openqc
doi: 10.48550/arXiv.2607.02093
url: https://arxiv.org/abs/2607.02093v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.result
---

# Every gate ordering in an open-boundary integrable quantum circuit

## Problem

García Fernández, Paletta and Retore, arXiv:2607.02093v1,
§3.1.2, “From the circuit to $\vec{n}$”, state:

> For the open-boundary case, similarly to the periodic setting \cite{Paletta:2025sap}, we conjecture that any circuit in which each gate $U_{i,i+1}$ (constructed from an $\check{R}$-matrix) appears exactly once per period to every nearest-neighbor pair of spins, and where each boundary gate is constructed from a $K$-matrix, is integrable.

Section 5 restates the conjecture and says that an analytic proof remains
open. The bulk gate is $\check R(\kappa,-\kappa)$, where
$\check R(u,v)=P R(u,v)$; the boundary gates are $K^R_1(\kappa)$ and
$\widetilde K^L_L(\kappa)=\operatorname{tr}_a(K^L_a(\kappa)
\check R_{La}(\kappa,-\kappa))$.

The formulation in [issue #13232](https://github.com/the-omega-institute/trureturing/issues/13232#issuecomment-5987481348)
uses the explicit double-row product and states mutual commutation of its
transfer matrices as the hypothesis of the commutation conclusion.
For every length $L\ge2$ and permutation of the $L+1$ gate labels, there
are signed inhomogeneities $\theta_i\in\{\kappa,-\kappa\}$ and $c\ne0$
such that $M_\pi=c\,t(\kappa;\theta)$. Whenever the transfer matrices
$t(u;\theta)$ commute pairwise, $M_\pi$ commutes with every $t(u;\theta)$.
The hypotheses of the identity are $R(u,u)=g(u)P$ and
$g(\kappa)\ne0$, $g(-\kappa)\ne0$.

## Motivation

The frozen declaration
`D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.result`
proves this universal operator identity and its conditional commutation
conclusion. It identifies every once-per-bond ordering with a transfer-matrix
circuit of the source, including both boundary gates.

## Gap

Issue #13232 preregisters this tier-1 published conjecture and its literature
check. Its recorded search distinguishes the minimum-depth conjectures
already settled in the repository and the classified periodic circuits of
arXiv:2503.04673. The issue reports no resolution in the searched author
records, citation search, web search or MathDB. These external search
readings are attributed to their producers in the issue; they establish
`not-found-in-searched-scope`, rather than an exhaustive novelty claim.

## Route

Let $S$ contain label $i$ exactly when $i$ precedes $i-1$ in the operator
word. The signed key sorts labels into decreasing members of $S$, then
zero, then increasing nonmembers. Every inversion that this sort exchanges
has disjoint physical support, so the operator product is preserved.
The auxiliary permutation train converts the explicit double-row product
into the operator-product order obtained by reversing the existing gate
word `OpenIntegrableCircuitDepthRefutation.circuit (N + 1) S`. Its `K1`,
`U j` and `KN` gates represent labels `0`, `j` and `N + 1`. The partial
word used by induction is the same circuit with the terminal `KN` removed.
Regularity turns each diagonal checked matrix
into a nonzero scalar identity. Both terminal signs are handled, giving the
nonzero proportionality constant. Pairwise transfer commutation then gives
the conditional commutation conclusion by scalar multiplication.

The Lean parameter `N` encodes $L=N+1$ physical sites and `N+2` gates.
All proof lemmas are local to `result`; the public surface contains the
operator definitions, `claim`, and this one settling theorem.

## Falsifier

An ordering with no signed transfer realization would refute the identity.
The equality proved in the operator algebra rules this out under the
regularity and nonzero-scalar hypotheses. Noncommuting transfer matrices
are outside the antecedent of the second conclusion and do not refute it.

## Evidence

The Lean kernel checks `result : claim`, uniformly in chain length, local
dimension, matrix-valued spectral functions and gate ordering, with the
axioms `propext`, `Classical.choice`, and `Quot.sound`.

Computed by `python3 /tmp/op-lit/openqcint/calc/traces.py`: for source lengths
1 through 7, the permutation counts are 2, 6, 24, 120, 720, 5040 and 40320;
the canonical-class counts are 2, 4, 8, 16, 32, 64 and 128; each uncovered
count is zero. This finite computation checks the word correspondence;
the unbounded operator statement is proved by Lean.

## Triage

Tier 1; resolution `proved` for the formulation fixed in #13232.
`utility: none`: the result is a uniform theorem, rather than a certified
finite instance or bounded enumeration. There is no digestion atom or
coverage edge. Information-escape registration is paused under CLAUDE.md
section 3.9.

### What the settlement shows

- **Proved in this module** (`OpenIntegrableCircuitIntegrability.result`):
  every ordering has a signed transfer realization. The decisive mechanisms
  are adjacent-order-preserving word sorting and the auxiliary permutation
  train, followed by regularity scalar collapse.
- **Proved in this module** (the same `result`): the identity requires
  regularity and the two nonzero scalar values, without Yang–Baxter or
  reflection hypotheses. The commutation conclusion retains pairwise
  transfer commutation as an explicit hypothesis. No invertibility of the
  boundary gates or positive lower bound on the local dimension is needed.
- **Computed** (`python3 /tmp/op-lit/openqcint/calc/traces.py`): the finite
  word checks above agree with both terminal-sign branches. They do not
  replace the uniform operator proof.
- **Computed** (`python3 /tmp/op-lit/openqcint/calc/rho_depth.py 3 10`,
  exit 0): for the source's Conjectures 3a–3c at $3 \le N \le 10$, all
  15 parameter groups have the conjectured configuration at depth equal to
  the minimum, namely 4. Minimisers are not unique: there are 4 to 246
  minimisers per group. This verifies the stated finite range only.
- **Open in this delivery**: deriving transfer commutation from Yang–Baxter,
  boundary Yang–Baxter, unitarity and crossing, the periodic-chain analogue,
  and the unbounded statements of the source's Conjectures 3a–3c.
- **Proved consequence of this module's result**: in a model with commuting
  transfer matrices, every once-per-bond ordering meets the source's
  definition of an integrable circuit. The source's transfer constructions
  therefore apply to these orderings. Its distinct minimum-depth formulas
  and their repository settlements are separate assertions.

## ASSUMED-UNVERIFIED

The bounded external literature searches recorded in #13232 are
producer-reported and do not establish worldwide priority. The kernel
checks the formal operator model; it does not authenticate the source,
literature-search completeness, or the derivation of mutual transfer
commutation from physical integrability conditions.
