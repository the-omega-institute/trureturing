---
slug: rajaei-qubit-generalized-fidelity-dpi
bibkey: rajaei2026generalized
doi: null
url: https://arxiv.org/html/2609.09753v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/GeneralizedFidelity.claim
  - D5/S3/Quantum/FiniteDimensional
  - D5/S3/Quantum/PointerBasis
  - D5/S3/Quantum/Foundation/FiniteKrausChannel
---

# Unrestricted qubit generalized-fidelity data processing

## Problem

Rajaei's abstract says: "In dimension two, although we do not settle the DPI
in full generality,". The exact residual assertion is that every trace-one
positive semidefinite $P,Q\in M_2(\mathbb C)$, every positive-definite
trace-one $R$, and every completely positive trace-preserving channel
$\Phi:M_2(\mathbb C)\to M_2(\mathbb C)$ with positive-definite $\Phi(R)$ obey

$$B_{\Phi(R)}(\Phi(P),\Phi(Q))\le B_R(P,Q).$$

Here $F_R(P,Q)$ is the ordered matrix-root trace in the source, and
$B_R(P,Q)=\operatorname{Re}\operatorname{tr}(P+Q)-2\operatorname{Re}F_R(P,Q)$.
Singular input states are permitted. Positivity only on three chosen states
does not establish complete positivity.

## Motivation

This is the paper's residual dimension-two yes-or-no question, rather than
its already refuted dimension-at-least-three statement or classification of
all reference bases. It is a Tier-1 family target preregistered in
<https://github.com/the-omega-institute/trureturing/issues/13116>.

## Gap

[`GeneralizedFidelity.result`](../D5/S3/Quantum/GeneralizedFidelity.lean)
is the closed negation of the full universal assertion, with no term
premises. Its proof establishes a counterexample for every real
$0<\varepsilon\le1/1000$ before choosing $\varepsilon=1/1000$ for the final
contradiction. The whole interval certificate is proof-local, not a
separately exported family theorem or family GID. The source definitions
use actual complex matrices, PSD roots, matrix inverses and the existing
all-amplification completely positive channel.

## Route

Use

$$P=\frac1{10}\begin{pmatrix}1&3\\3&9\end{pmatrix},\quad
Q=\frac15\begin{pmatrix}4&2\\2&1\end{pmatrix},\quad
R_\varepsilon=\operatorname{diag}(1-\varepsilon,\varepsilon),\quad
\Phi(M)=\frac{31}{32}M+\frac1{32}XMX.$$

The channel is independent of $\varepsilon$. Its Kraus matrices are
$\sqrt{31/32}\,I$ and $\sqrt{1/32}\,X$; their normalization feeds the
existing all-amplification CPTP theorem. Its action equals the existing
Fourier phase-damping map at retention $15/16$ for all complex matrices.
The transported reference is
$\operatorname{diag}((31-30\varepsilon)/32,(1+30\varepsilon)/32)$.

Direct positive-root certificates for both references and all four
sandwiches recover the actual source trace. Each candidate is positive
semidefinite and has the required square, so `CFC.sqrt_unique` identifies
the actual matrix root. Positive diagonal entries certify reference
invertibility and the displayed diagonal inverse. The sandwich determinant
roots are zero at the input, and $S/1280$ and $3S/5120$ at the output. The
root denominators have positive squared values $p=(1+8\varepsilon)/10$,
$q=(4-3\varepsilon)/5$ at the input and $A,B$ at the output.
The input formula is

$$F_{\rm in}=\frac{2+\varepsilon}{\sqrt{2(4+29\varepsilon-24\varepsilon^2)}}>7/10.$$

For the output put

$$S=\sqrt{961+27900\varepsilon-27900\varepsilon^2},\quad
A=(95+450\varepsilon+S)/640,\quad
B=(1955-1350\varepsilon+3S)/2560.$$

The bounds $31\le S<32$ and $S\le31+450\varepsilon$ imply
$63/320\le A\le1/4$ and $3/4\le B\le4/5$. With
$C=893/1600$, the exact rectangle certificate is

$$(A+B-707/1600)^2-49AB/25\le-27/40000.$$

The positive numerator and denominators give $F_{\rm out}<7/10$.
Trace-one proofs for the actual input and transported states justify
reducing the source trace term to two, and imply
$B_{\rm in}<3/5<B_{\rm out}$ throughout the interval.
The final negation uses $\varepsilon=1/1000$ only after this whole-interval
certificate. No scalar proxy replaces the ordered matrix-root definition.

## Falsifier

A root, inverse, positivity, normalization, channel-representation or
interval gap prevents settlement. A scalar replacement for the source
fidelity, one numerical witness alone, or hidden premises in the result
would change the target. An equivalent earlier solution or current exact
owner retires the candidate without a solved-problem increment.

## Evidence

The closed Lean theorem `GeneralizedFidelity.result` negates the complete
universal qubit assertion. Its proof-local quantified certificate covers
every real $0<\varepsilon\le1/1000$ using actual PSD-root uniqueness,
the normalized finite-Kraus channel and the strict source inequalities
$B_{\rm in}<3/5<B_{\rm out}$. The rectangle bound is an exact real
polynomial inequality; no finite numerical scan substitutes for the
interval proof. The canonical Blueprint describes the four source
definitions and this single authored theorem. Its `Refuted` resolution
claim binds this dossier to the exact frozen `result`, whose type is the
closed negation of the source-faithful `claim`.

## Triage

Tier 1; resolution **Refuted** by
`D5/S3/Quantum/GeneralizedFidelity.result`. The declaration retains
`proof_shape: bind-only` and `escape_witness: bind-only`;
`admission_basis: open-problem-resolution` is the published-problem
exception under preregistration
[#13116](https://github.com/the-omega-institute/trureturing/issues/13116).
The computational utility is `certified-instance` with `basis: refutes`,
and the typed result is `Not claim`. No companion theorem or additional
mathematical declaration is part of this resolution.

The inherited bounded qualification inspected Rajaei v1, Afham--Ferrie v2,
Vuong v1 and the indexed Afham citing work arXiv:2608.15833, together with
2017 GitHub issue titles/bodies, 623 problem records and obtainable public
formal-library sources. It found no equivalent resolution or exact owner.

The proved mechanism is a strict reversal of the source's normalized
three-state quantity under a fixed, unital bit-flip channel. The source
expresses this quantity through three pairwise Uhlmann fidelities; their
ordinary data processing does not imply monotonicity of this normalization.
The source's two sufficient qubit conditions and its higher-dimensional
results are separate assertions. Reference-base classification remains
outside this target. Registration is paused; no completed
information-escape audit is claimed.

## ASSUMED-UNVERIFIED

Complete multi-index and global prior-solution exclusion remain
unverified. Semantic Scholar and OpenAlex returned HTTP 429, and the
bounded qualification cannot exclude unavailable or undiscoverable
solutions. No worldwide priority claim follows.
