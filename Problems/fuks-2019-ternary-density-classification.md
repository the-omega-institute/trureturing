---
slug: fuks-2019-ternary-density-classification
bibkey: fuks2019ternary
doi: 10.5506/APhysPolBSupp.12.75
url: https://arxiv.org/abs/2002.08924v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation.result
---

# A misclassified configuration for a ternary two-rule density classifier

## Problem

Henryk Fukś and Roman Procyk, *Explorations of Ternary Cellular Automata and
Ternary Density Classification Problems*, arXiv:2002.08924v1 (Conjecture 1 of
Acta Phys. Pol. B Proc. Suppl. 12(1) (2019) 75–89), write:

> Let $F$ be the ternary nearest-neighbour rule with Wolfram number 6478767664173, and $G$ be the rule with Wolfram number 7580606234490. For any finite ternary string $\mathbf{x}$ of length $L$, containing at least one zero, let $\displaystyle \rho=\frac{1}{2L}\sum_{i=0}^{L-1} x_i$. Then $G^LF^L(\mathbf{x})=0^L$ if $\rho(\mathbf{x}) \in [0, 2/3)$, $G^LF^L(\mathbf{x})=1^L$ if $\rho(\mathbf{x}) \in (2/3, 3/4)$, $G^LF^L(\mathbf{x})=2^L$ if $\rho(\mathbf{x}) \in (3/4, 1)$.

Configurations are periodic, $(F(\mathbf{x}))_i=f(x_{i-1},x_i,x_{i+1})$ with
indices in $\mathbb{Z}/L$, and the rule with Wolfram number $N$ has
$f(a,b,c)=\lfloor N/3^{9a+3b+c}\rfloor \bmod 3$. The precise question,
preregistered in issue #11845, is whether the three implications hold for
every $L$ and every configuration containing a zero.

## Motivation

Density classification asks a cellular automaton to decide, from a random
initial configuration, which density interval it belongs to; two-rule
solutions are known in the binary case (rules 184 and 232). The paper's
abstract presents the pair $(F,G)$ as a solution of the non-symmetric
interval-wise problem for configurations containing a zero. The frozen
declaration
`D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation.result`
shows that the pair does not have this property.

## Gap

Issue #11845 classifies the question as Tier 1 and records the bounded
literature check before any Lean: arXiv:2002.08924 has one version; of the
five citing works listed by Semantic Scholar, the four with arXiv sources
(2601.00486, 2404.05461, 2308.00060, 2106.13591) and two later
density-classification papers (2409.06536, 2510.06947) do not mention the
conjecture or the rule numbers; the fifth (Inform. Sci. 2020, on reversible
rules) was not read. `google-deepmind/formal-conjectures` and the
`Horace-Maxwell/ai4math-results` attempt list have no entry.

These are orchestrator-reported literature readings,
`not-found-in-searched-scope`; they do not establish exhaustive worldwide
novelty or exclude an independent answer.

## Route

1. Take $L=3$ and $\mathbf{x}=(2,1,0)$: it contains a zero and
   $\rho(\mathbf{x})=3/6=1/2\in[0,2/3)$.
2. From the Wolfram number of $F$,
   $F(0,2,1)=F(2,1,0)=F(1,0,2)=1$, so the global map of $F$ sends
   $\mathbf{x}$ to $(1,1,1)$.
3. $F(1,1,1)=G(1,1,1)=1$, so $(1,1,1)$ is fixed by both rules and
   $G^3F^3(\mathbf{x})=(1,1,1)$, not $0^3$.

## Falsifier

The conjecture would survive only if $G^3F^3(2,1,0)=000$. The kernel
evaluates $G^3F^3(2,1,0)=111$ from the two Wolfram numbers. Reading the rule
numbers with another digit order, or changing the hypothesis on the initial
configuration, changes the question; the theorem makes no assertion about
those variants.

## Evidence

Integer arithmetic (issue #11845) decodes the two rules and gives
$F(2,1,0)=(1,1,1)$ and $G^3F^3(2,1,0)=(1,1,1)$. As controls, the same code
reproduces the authors' example $1^5\mapsto1^5$ and classifies $0001$,
$0220222$, $001122$ and $0112222222$ as the conjecture says; the decoded $F$
conserves $\sum_i x_i$ on every configuration of length at most $6$.

The canonical source is
`D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation.lean`.
Its public declarations are `wolfram`, `ruleF`, `ruleG`, `step`, `rho`,
`claim` and `result`. The frozen module state has statement identity
`sha256:80836ba63c9819ff1b9990fa22fe3bd9c44a117fc15793937fbefa604d56833b`. The result declaration has statement identity `sha256:453b1c3c4a2a504d38478544dfebb093405ccfcfb4d6d153976f6ba7731f37e2`. The Freeze
event is `sha256:5aac2b559635d3cf48e4209b778dd44e9d41a031fdab5e9256271c426a44c5ba`. It has no project-level frozen prerequisites (pinned
Mathlib only). The proof uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new
axiom.

## Triage

Tier 1 published conjecture; resolution `Refuted` by
`D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation.result`.
`proof_shape: bind-only`; `admission_basis: open-problem-resolution`
(issue #11845). Utility `certified-instance`, `basis=refutes`: the instance
refutes the named assertion.

### What the settlement shows

- **Proved in this module:** the configuration $(2,1,0)$, which contains a
  zero and has density $1/2$, is sent by $G^3F^3$ to $(1,1,1)$ instead of
  $(0,0,0)$.
- **Mechanism, computed:** $F$ conserves $\sum_i x_i$ and maps each of the
  local patterns $(0,2,0)$, $(2,0,2)$, $(0,2,1)$, $(2,1,0)$, $(1,0,2)$ to $1$.
  Every cyclic concatenation of the blocks $20$ and $210$ (one for each
  $L\ge2$) is therefore sent to $1^L$ in one step, destroying all zeros, and
  $1^L$ is the fixed point the authors already excluded. The hypothesis
  "containing at least one zero" constrains the initial configuration, while
  the failure uses zeros that $F$ removes (scout readings, issue #11845).
- **Second failure, computed:** configurations whose zeros survive $F^L$ also
  fail: $122200$ (density $7/12$) gives $220000$, and $2222222000$
  (density $7/10$) gives $1111022222$. By exhaustive search up to $L=13$ the
  class $[0,2/3)$ fails for every $L\ge2$ and $(2/3,3/4)$ fails from $L=10$,
  while $(3/4,1)$ has no failure up to $L=13$ (scout readings).
- **Repairs, computed:** more iterations ($2L$ or $4L$), requiring a pair
  $00$, requiring at least $L/3$ zeros, or requiring that $F^L(\mathbf{x})$
  keeps a zero do not repair the statement; requiring that zeros survive all
  $4L$ steps of $F$ and iterating $4L$ times has no failure for $L\le12$
  (scout readings). That hypothesis is on the dynamics, not on the initial
  configuration, and is open here.
- **Open:** whether the class $(3/4,1)$ is classified correctly for every
  $L$, and whether some pair of ternary rules solves the non-symmetric
  interval-wise problem for configurations containing a zero. No additional
  theorem is included in this settlement.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish worldwide priority or
absence of an independent solution. The Lean kernel verifies the encoded
statement and its axiom closure; correspondence to the external paper is
checked by reading the source, the definitions and the mirror. The decoding
convention is the paper's coefficient indexing; that the decoded $F$ matches
the published rule table in all 27 entries, and that the published $G$ table
differs from the number at one entry not used by the counterexample, are
scout readings.
