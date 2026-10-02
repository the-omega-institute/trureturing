---
slug: bhattacharya-2015-relaxed-hardy-no-signalling-optimum
bibkey: bhattacharya2015hardy
doi: 10.48550/arXiv.1507.07327
url: https://arxiv.org/abs/1507.07327v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/RelaxedHardyNoSignallingOptimum.result
---

# The no-signalling optimum of the relaxed multipartite Hardy test

## Problem

S. S. Bhattacharya, A. Roy, A. Mukherjee and R. Rahaman, *Witnessing
Genuine Mutipartite Non-locality*, arXiv:1507.07327v1, Section 3,
conjecture:

> The optimal value of the probability of success, $q$ in(\ref{relH}) is $\frac{1}{3}$ for any arbitrary dimension for any number of parties in GNST.

Here (relH) are the relaxed Hardy conditions for $N$ parties with inputs
$u$, $v$ and outcomes $1,\dots,d$: $P(1\dots1|u\dots u)=q>0$; for every $r$,
with $v$ at $r$ only, every outcome string with $1$ elsewhere and a value
other than $d$ at $r$ has probability $0$; and for a fixed $j$ and every
$i\ne j$, with $v$ at $i$ and $j$, the string with $d$ at $i$ and $j$ and $1$
elsewhere has probability $0$. GNST is the theory of no-signalling boxes.
The paper's Observation reports the value $1/3$ for $n=3,4$ and
$d=2,\dots,5$.

## Motivation

The paper extends the qubit test of Chen, Yu, Zhang, Lai and Oh for genuine
multipartite nonlocality to arbitrary dimension and compares its optimal
paradoxical probability under no-signalling with the value $1/2$ of the
conventional multipartite Hardy argument. The frozen declaration
`D5/S3/Quantum/Entanglement/RelaxedHardyNoSignallingOptimum.result` refutes
the conjecture.

## Gap

Issue #12033 classifies the conjecture as Tier 1 and records the bounded
literature check before any Lean:

- arXiv v1 is the only version, with no journal version;
- INSPIRE lists no citations and Semantic Scholar returns an empty citation
  list;
- the 2016 experiment of Zhang et al. (Sci. Rep. 6, 39327) and
  arXiv:2505.10035 do not revisit the value;
- web searches return nothing that revisits the value $1/3$.

These are orchestrator-reported literature readings,
`not-found-in-searched-scope`; they do not establish exhaustive worldwide
novelty or exclude an independent answer.

## Route

Let $S_r$ be the input string with $v$ at $r$ only, $S_{ij}$ the one with
$v$ at $i$ and $j$, and $m_r$ the probability of outcome $1$ at all parties
other than $r$ under $u\dots u$.

1. No-signalling at $r$ and the second condition give the outcome $d$ at
   $r$ and $1$ elsewhere probability $m_r$ under $S_r$.
2. For $i\ne j$, no-signalling at $j$, the third condition and
   nonnegativity give the event $\{x_i=d,\ x_j\ne d,\ \text{others }1\}$
   probability at least $m_i$ under $S_{ij}$; symmetrically the event
   $\{x_i\ne d,\ x_j=d,\ \text{others }1\}$ has probability at least $m_j$.
   These events are disjoint, so under $S_{ij}$ the parties other than $i$
   and $j$ all give $1$ with probability at least $m_i+m_j$.
3. No-signalling at $i$ and at $j$ moves this marginal back to $u\dots u$.
   Since $m_i=q+P(x_i\ne1,\text{others }1\mid u\dots u)$ and likewise for
   $m_j$, the event $\{x_i\ne1,\ x_j\ne1,\ \text{others }1\}$ has
   probability at least $q$ under $u\dots u$.
4. These $N-1$ events and the all-$1$ event are disjoint, so $Nq\le1$.

The module carries out steps 1–4 for $N=4$, $d=2$ and each fixed $j$, so
every admissible $q$ satisfies $4q\le1$ and none exceeds
$1/3-1/12=1/4$.

## Falsifier

The kernel-checked `result` excludes success probabilities above $1/4$ for
four parties with two outcomes, hence the conjecture (read as a maximum or
a supremum) and the paper's Observation for $n=4$. Changing the
no-signalling condition, the normalization, or the third condition (for
example imposing it for all pairs, or for a single pair) changes the
question.

## Evidence

An independent SciPy/HiGHS linear program over all no-signalling boxes,
solved for every fixed $j$, gives the optimum $1/2$, $1/3$, $1/3$, $1/4$,
$1/4$ and $1/5$ for $(N,d)=(2,2)$, $(3,2)$, $(3,3)$, $(4,2)$, $(4,3)$,
$(5,2)$; the values at $N=2$ (Hardy) and $N=3$ (the paper) serve as
positive controls. An exact rational box for $N=4$, $d=2$ attains
$q=1/4$, and raising its success probability by $1/48$ breaks feasibility
(issue #12033).

The canonical source is
`D5/S3/Quantum/Entanglement/RelaxedHardyNoSignallingOptimum.lean`. Its public
declarations are `IsNSBox`, `RelaxedHardy`, `claim` and `result`. The frozen
module state has statement identity `sha256:8a58e4dbc53a7b468818763671b6499902ce328c4112413c29356d63d5917782`. The result declaration has
statement identity `sha256:03e1ccb3bd627872c77b76d062d918e9c60bae692cedd2dd1f13c1add54f2047`. The Freeze event is `sha256:439982eecd95b434385a6edf6abc6faac88b8f4f2197f929b1922b925ead94ed`. It has no
project-level frozen prerequisites (pinned Mathlib only). The proof uses
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no
`sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 published conjecture; resolution `Refuted` by
`D5/S3/Quantum/Entanglement/RelaxedHardyNoSignallingOptimum.result`.
`proof_shape: bind-only` (instantiation of the hypotheses and linear
arithmetic); `admission_basis: open-problem-resolution` (issue #12033).
Utility `certified-instance`, refuting `claim`.

### What the refutation shows

- **Proved in this module:** for four parties with two outcomes each,
  every no-signalling box satisfying the relaxed Hardy conditions has
  success probability at most $1/4$.
- **Where the conjecture fails:** the third condition is imposed only for
  pairs containing the fixed party $j$, so each of the $N-1$ parties
  $i\ne j$ forces a separate event $\{x_i\ne1,\ x_j\ne1,\ \text{others }1\}$
  of probability at least $q$ under $u\dots u$. These events and the all-$1$
  string are disjoint, so the bound decreases like $1/N$. At $N=3$ it
  equals $1/3$, which is the value the paper computed and extrapolated.
- **Model derivation, not formalized (steps 1–4 above):** $Nq\le1$ for every
  $N\ge2$, every $d\ge2$ and every fixed $j$; the same argument works with
  different outcome numbers $d_i$.
- **Computed, not formalized (orchestrator):** the optimum equals $1/N$ for
  $(N,d)=(2,2)$, $(3,2)$, $(3,3)$, $(4,2)$, $(4,3)$, $(5,2)$, and the
  optimal $N=4$ box puts $1/4$ on each of $1111$, $1122$, $1212$, $2112$
  under $u\dots u$.
- **Computed, not formalized (scout reading):** optima $1/5$ at $(5,3)$ and
  $1/6$ at $(6,2)$; other readings of the third condition give $1/7$ (all
  pairs), $1/2$ (a single pair) and $1$ (none) at $N=4$.
- **Open here:** whether the optimum equals $1/N$ for every $N$ and $d$
  (attainability beyond the computed cases), and the optimal quantum
  success probability of the test.
- **Unchanged:** the paper's theorem that every quantum state satisfying
  (relH) is genuinely nonlocal does not depend on the conjecture. Its
  comparison with the conventional argument (value $1/2$) holds more
  strongly, since the relaxed test's no-signalling optimum is at most $1/N$
  (model derivation above), a bound that decreases with $N$.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish worldwide priority or
absence of an independent answer. The Lean kernel verifies the encoded
statement and its axiom closure; correspondence to the external paper,
including the encoding of outcomes by $0,\dots,d-1$, the reading of "the
optimal value is $1/3$" through its consequence that success probabilities
approach $1/3$, and the restriction to $N\ge3$ and a common $d$ as a
weakening, is checked by reading the source and the definitions.
