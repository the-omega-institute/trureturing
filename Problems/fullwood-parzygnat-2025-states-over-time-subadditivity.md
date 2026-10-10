---
slug: fullwood-parzygnat-2025-states-over-time-subadditivity
bibkey: fullwood2025dynamical
doi: 10.3390/e27040331
url: https://doi.org/10.3390/e27040331
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation.result
---

# Subadditivity of the entropy of quantum states over time

## Problem

J. Fullwood and A. J. Parzygnat, *On Dynamical Measures of Quantum Information*, Entropy **27**(4), 331
(2025), Remark 1:

> At present, we do not know of any examples of quantum states over time that violate subadditivity,
> which leads us to conjecture that the entropy functional S restricted to quantum states over time
> does in fact satisfy subadditivity.

A quantum state over time is $\varrho=\tfrac12\{\rho\otimes I,\mathscr J[\mathcal E]\}$ for a density
matrix $\rho$ and a CPTP map $\mathcal E$, with the Jamiołkowski matrix
$\mathscr J[\mathcal E]=\sum_{i,j}|i\rangle\langle j|\otimes\mathcal E(|j\rangle\langle i|)$, and
$S(X)=-\mathrm{tr}(X\log|X|)$. The verbatim texts, including the restatement in J. Fullwood and B. Yang,
arXiv:2608.28946 §6, are in [the literature note](../Library/QuantumChannels/fullwood2025dynamical.md).
Issue [#14994](https://github.com/the-omega-institute/trureturing/issues/14994) preregisters the reading
over finite Kraus channels and the refutation.

## Motivation

The conjecture is equivalent to non-negativity of the dynamical mutual information
$S(\rho)+S(\mathcal E(\rho))-S(\varrho)$, the quantity the authors propose as the mutual information
between the input and output of a process. Subadditivity fails for general unit-trace Hermitian
matrices with positive marginals; the conjecture asserts that the matrices arising from processes are
an exception.

## Gap

Fullwood and Yang prove subadditivity when the input is a single qubit (any output dimension,
Theorem 4.1) and report that numerical examples suggest failure in higher dimensions, without an example.
The literature check in #14994 found no settlement; `not-found-in-searched-scope`.

## Route

Take $d=5$, $\rho=I/5$ and the Werner–Holevo channel $\mathcal E(X)=(\mathrm{tr}X\,I-X^T)/4$, with the ten
Kraus operators $(E_{ij}-E_{ji})/2$, $i<j$.

1. $\mathcal E(\rho)=\rho$ and $\mathscr J[\mathcal E]=(I-|\Omega\rangle\langle\Omega|)/4$ with
   $\Omega=\sum_i|ii\rangle$, so $\varrho=(I-|\Omega\rangle\langle\Omega|)/20$.
2. With the Hermitian idempotent $P=|\Omega\rangle\langle\Omega|/5$ of trace one,
   $\varrho=\tfrac1{20}(I-P)-\tfrac15P$: eigenvalues $-1/5$ once and $1/20$ with multiplicity 24.
3. $S(\varrho)=\log5+\tfrac65\log4$ and $S(\rho)=S(\mathcal E(\rho))=\log5$, so
   $S(\varrho)-S(\rho)-S(\mathcal E(\rho))=\tfrac15\log\tfrac{4096}{3125}>0$.

## Falsifier

A convention different from the sources (the Choi instead of the Jamiołkowski matrix, another ordering of
the factors, or another extension of the entropy), or an error in the spectrum. Positive control in
#14994: 300 random qubit-input channels satisfy the inequality, consistently with Theorem 4.1.

## Evidence

`D5/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation.lean` defines `jamio`, `pdm`, `S`
(through the real functional calculus of $x\mapsto -x\log|x|$) and `claim` over finite Kraus channels
(`FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus`), and proves `result : ¬ claim`. The axiom closure of
`result` is exactly `propext`, `Classical.choice` and `Quot.sound`; there is no `sorry` or
`native_decide`.

## Triage

Tier 1: a named conjecture of a 2025 journal paper, restated open in an August 2026 preprint, preregistered
in #14994 before any Lean. `theorem`; resolution `refuted`. `result` is bind-only (the fixed
counterexample combines the frozen Kraus interface with pinned spectral, functional-calculus and logarithm
facts); admission basis `open-problem-resolution`; utility `kind=certified-instance; basis=refutes`. There
is no digestion atom.

### What the refutation shows

- **Proved by `result`:** the dynamical mutual information of a quantum process can be negative: the
  Werner–Holevo channel on the maximally mixed state of $\mathbb C^5$ gives
  $-\tfrac15\log\tfrac{4096}{3125}$.
- **Mechanism:** the Jamiołkowski matrix of the Werner–Holevo channel is the partial transpose of its
  Choi matrix $(I-F)/(d-1)$, namely $(I-|\Omega\rangle\langle\Omega|)/(d-1)$, so the state over time
  has one negative eigenvalue $-1/d$ and the flat positive spectrum $1/(d(d-1))$ of multiplicity $d^2-1$.
  The positive part carries total weight $1+1/d$ spread over $d^2-1$ levels and contributes
  $\tfrac{d+1}{d}\log(d(d-1))$; the negative eigenvalue contributes $-\tfrac1d\log d$. The excess of the
  positive part over the $2\log d$ of the two maximally mixed marginals outweighs that loss exactly when
  $d\ge5$.
- **Computed, not formalized (#14994):** for the same family in dimension $d$ the gap is
  $\tfrac{d+1}{d}\log(d-1)-\log d$: negative for $d=3,4$ ($-0.1744$, $-0.0130$) and positive for every
  $d\ge5$ ($+0.0541$ at $d=5$, $+0.0859$ at $d=6$), and it equals $\log(1-\tfrac1d)+\tfrac1d\log(d-1)\sim(\log d-1)/d$, so it tends to $0$.
- **Open:** the smallest input dimension with a violation (qubit inputs never violate, by Theorem 4.1;
  qutrit and four-level inputs are not decided by this family), and whether the multi-time
  generalization of the entropy admits a modified mutual information that is non-negative.

## ASSUMED-UNVERIFIED

The literature check in #14994 is bounded and does not establish worldwide novelty or priority.
