---
slug: marquez-gonzalez-2026-cp-filter-transpose-refutation
bibkey: marquezgonzalez2026feasibility
doi: 10.48550/arXiv.2609.18803
url: https://arxiv.org/abs/2609.18803v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/CPFilterTransposeRefutation.result
---

# A qutrit obstruction to strong CP-filter equivalence

## Problem

Samuel A. Márquez González, *Feasibility Ordering of Entanglement-Source
Placement for Qubit Channels*, arXiv:2609.18803v1, printed PDF p. 5,
Section VI, Eq. (47), asks:

> This separates the higher-dimensional problem into two levels. The strong
> question is whether every unital qudit channel $\Upsilon$ is CP-filter
> equivalent to its transpose, i.e., whether there exist invertible CP maps
> $\mathcal L$ and $\mathcal R$, with CP inverses, such that
> $\Upsilon^T=\mathcal L\circ\Upsilon\circ\mathcal R$.

Issue #13180 preregisters the universal question for every dimension
$d\geq2$ and the refutation at $d=3$. A channel is completely positive
and trace preserving, with unitality $F(I)=I$. Both filters have two-sided
completely positive inverses; neither filter must preserve trace.
The channel transpose is the source's Eqs. (15)–(16): a finite Kraus
family $K_i$ gives $F^T(X)=\sum_i K_i^T X\overline{K_i}$ in the fixed basis.

## Motivation

The frozen declaration
`D5/S3/Quantum/QuantumChannels/CPFilterTransposeRefutation.result`
proves the negation of the dimension-three strong question. A counterexample
at this dimension refutes the universal-dimensional assertion.

## Gap

Issue #13180 records the literature check against the source, the author's
later arXiv papers and OpenAlex citing records. No settlement was found in
that searched scope. This bounded absence is not an exhaustive priority
claim. The source distinguishes the strong condition from the weaker
positive/CP factorization in Eq. (48).

## Route

The proof constructs $F(X)=\sum_j X_{jj}\rho_j$, where

$$\rho_0=\operatorname{diag}(1/2,1/3,1/6),\qquad
\rho_1=\begin{pmatrix}1/6&1/12&0\\1/12&1/3&0\\0&0&1/2\end{pmatrix},\qquad
\rho_2=\begin{pmatrix}1/3&-1/12&0\\-1/12&1/3&0\\0&0&1/3\end{pmatrix}.$$

Exact positive semidefinite factorizations, trace identities and
$\sum_j\rho_j=I$ establish that $F$ is a unital channel. Its Choi matrix
has a positive semidefinite decomposition; spectral decomposition supplies
a finite Kraus family. Trace duality and nondegeneracy of the trace pairing identify the
Heisenberg map for any two finite Kraus representations of the same channel.
Transposing its value on $X^T$ proves that the channel transpose is independent
of the Kraus family. The Kraus-transposed map has diagonal range and
equals $X\mapsto\operatorname{diag}(\operatorname{Tr}(\rho_j^T X))$.

For arbitrary completely positive $L$ with a completely positive left
inverse, the proof-local Choi/Kraus construction and the frozen identity
Kraus scalarity theorem give $L(X)=AXA^\dagger$ for invertible $A$.
Surjectivity of $R$ would make every $AF(Y)A^\dagger$ diagonal. Diagonal
commutation and cancellation, also using $F(I)=I$, would force
$\rho_0\rho_1=\rho_1\rho_0$. Their commutator has entry $(0,1)$ equal to
$1/72$, giving the contradiction.

## Falsifier

The refutation excludes every pair of filters satisfying the literal
two-sided CP-inverse conditions. It assumes neither a preferred Kraus
family nor trace-preserving filters. The public claim quantifies over every
finite family representing the channel. No sampled-state condition replaces
equality on all complex matrices.

## Evidence

The canonical source is
`D5/S3/Quantum/QuantumChannels/CPFilterTransposeRefutation.lean`.
Its public declarations are `CPInvertible`, `UnitalChannel`, `claim` and
the sole settling theorem `result : ¬ claim`. All auxiliary constructions
and estimates are local to that proof. The axiom closure of every public declaration is contained in
{`propext`, `Classical.choice`, `Quot.sound`}.

## Triage

Tier 1 externally named question, preregistered in issue #13180.
Resolution: Refuted. `proof_shape: result: content`;
`admission_basis: open-problem-resolution (#13180; Refuted)`.
The form-2 escape witness is the live proof-local CP-inverse congruence
construction. Utility is `kind=certified-instance; basis=refutes`, with
typed `claim` and `result`.

### What the settlement shows

- **Proved in this module, inside `result`:** the explicit measure-and-prepare
  channel is completely positive, trace preserving and unital; its transpose
  has diagonal range, while its range contains the noncommuting pair
  $\rho_0,\rho_1$. This breaks strong CP-filter equivalence.
- **Proved in this module, inside `result`:** an arbitrary qutrit CP map with
  a CP left inverse is an invertible congruence. Combining this with
  surjectivity of the right filter and the image of the identity gives the
  commutation obstruction. These are proof-local facts, not separately
  exported general theorems.
- **Open in this delivery:** formal verification of the source's surviving
  qubit strong condition. The source attests it for dimension two; the
  dimension-three counterexample does not refute that restricted statement
  or the published qubit feasibility conclusions.
- **Open:** Eq. (48), which asks for positive/CP factorization without the
  two-sided CP-inverse requirement. The strong-condition counterexample
  supplies no verdict on this weaker condition. The source identifies the
  weaker condition as sufficient for its higher-dimensional extension;
  that extension is not disproved by the present settlement.
- **Open:** strong CP-filter equivalence for the commuting-Choi-block
  class. The present noncommuting-range obstruction does not settle that class.
- **Open:** strong CP-filter equivalence for other dimension-three channel
  classes beyond the explicit measure-and-prepare counterexample.
- **Open:** sufficient hypotheses for strong equivalence in higher
  dimensions and the range of dimensions admitting this obstruction.

## ASSUMED-UNVERIFIED

The bounded literature absence and external publication metadata are
literature evidence, not Lean-kernel conclusions. Source results outside
Eq. (47), including the qubit theorems and Eq. (48), are not formalized here.
The kernel checks the dimension-three negation and its stated definitions.

Information-escape registration is paused under CLAUDE.md §3.9.
