---
slug: horodecki-2022-rank-of-contextuality-non-power-of-two
bibkey: horodecki2022rank
doi: 10.1088/1367-2630/acdf78
url: https://arxiv.org/abs/2205.10307
triage: theorem
motivation_gids:
  - D5/S3/QuantumContext/RankOfContextualityNonPowerTwo.result
---

# A quantum behavior with rank of contextuality three

## Problem

K. Horodecki et al., *The rank of contextuality*, arXiv:2205.10307v1,
New Journal of Physics 25 (2023), 073003, Section IX (Section 9 in the journal):

> Finally, it would be interesting to construct a quantum behavior having the rank of contextuality different from the power of 2 (the power of 2 is achieved by a tensor product of the Peres-Mermin behaviors).

The question asks for an example. The quantum behavior $Q=P\otimes P$ formed
from two Peres–Mermin squares has rank $3$.

### Statement echo

| Source clause or representation choice | Lean counterpart | Scope |
| --- | --- | --- |
| An ordered list of observable outcomes | `restrict C x g` | Boolean outcomes on finite ordered contexts |
| A family of conditional distributions | `Behavior C`, constrained by `IsQuantum C P` | `Behavior` is the repository's unrestricted real-table carrier; the quantum predicate imposes the Born rule |
| Mixtures of deterministic assignments, equation (2) | `NonContextual C N` | Nonnegative real weights with total mass one and every restriction-fiber sum |
| Minimum number of distinct noncontextual behaviors covering every context, equation (3) | `coverSizes` and `IsRankOfContextuality` | One member agrees on all outcomes at each context; the member can depend on that context |
| Quantum observables and state | `IsQuantum` | Positive semidefinite trace-one state; Hermitian involutions; within-context commutation; ordered spectral-projection products |
| Construct a quantum behavior | `claim`, proved by `result` | Existential observable count, context count, context lists, table and rank |
| Rank different from every power of two | Final conjunct of `claim` | All natural exponents, including zero |

The witness has $18$ observable labels, $36$ contexts, state $I_{16}/16$ and
rank $3$. Finite labels, ordered contexts and binary outcomes restrict the
construction to a subclass of quantum behaviors; existence in that subclass
answers the source's existence question. No hypothesis is added to the question.

## Motivation

The settling declaration is
`D5/S3/QuantumContext/RankOfContextualityNonPowerTwo.result : claim`.
It provides the requested example. Its proof uses the private statements
`Product.quantum` and `Product.rank_three` in the same module.

The Library attestation is `Library/QuantumContext/horodecki2022rank.md`.
The source's table carrier and this encoding are distinguished explicitly:
`Behavior` supplies a real table, while the target and covering models are
constrained by `IsQuantum` and `NonContextual`, respectively.

## Gap

Preregistration: https://github.com/the-omega-institute/trureturing/issues/15370.
Its source and literature screen reports no answer in the searched scope;
that screen is not an exhaustive absence theorem.

The source's Theorem V.1 (journal Theorem 5.1) asserts tensor additivity of
log-rank and motivates the parenthetical power-of-two examples. The construction
below gives a three-model cover of two contextual squares and a matching lower
bound; full marginal identity is stronger than agreement at a single context.

## Route

Each square has five positive parity contexts and one negative parity context.
Every global assignment violates one of the six target parities, proving
contextuality. Flipping exactly one context parity gives a support of $16$
assignments. Its uniform distribution reproduces the square at all other contexts.

For the upper bound, take three products $N_{R_j}\otimes N_{R_j}$ with row
parity defects $R_1,R_2,R_3$. A paired context uses at most two of these rows,
so at least one product reproduces all of its outcomes. These are noncontextual
models and give a cover of size $3$.

For the lower bound, each noncontextual model in the product scenario has
noncontextual copy marginals. For one model choose a first-copy context at which
its marginal differs from $P$; for another choose a second-copy context at which
its marginal differs. At the paired context the first model fails the first
marginal and the second model fails the second marginal. Covers with fewer
members fail as well. Thus every cover has at least $3$ members.

The observables are the two-qubit Peres–Mermin matrices on each factor, embedded
as $A\otimes I_4$ and $I_4\otimes B$, with the maximally mixed four-qubit state.
The ordered Born products equal the product probabilities, establishing
`IsQuantum`. Rank $3$ is odd and greater than one, hence differs from $2^n$
for every natural $n$.

## Falsifier

A mismatch with equations (2)–(3) or the quantum Born rule would invalidate the
source correspondence. A noncontextual cover with at most two members would
contradict `Product.cover_lower`. Failure of the explicit cover or of its
quantum realization would invalidate this witness. These properties are
checked by the named declarations below.

## Evidence

The kernel-checked statements, all under namespace
`D5.S3.QuantumContext.RankOfContextualityNonPowerTwo`, are:

- `Product.cover_nc` and `Product.cover_agrees` (private): noncontextuality and
  contextwise agreement of the explicit three-model cover.
- `Lower.no_two_cover` and `Product.cover_lower` (private): the abstract marginal
  obstruction and the bound $3\leq |S|$ for every cover of the constructed product.
- `Product.cover_card` and `Product.rank_three` (private): the explicit cover has
  cardinality $3$ and that cardinality is least.
- `Product.quantum` (private): the constructed behavior admits the specified
  quantum realization.
- `result` (public): the existential source question with every power of two excluded.

The axiom closure of every public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
The content declarations are `Lower.no_two_cover`, `Square.parity_miss`,
`Square.support_card`, `Square.muTable`, `Square.fiber_sum`,
`Square.fiber_card`, `Square.defect_agrees`, `Square.contextual`,
`Product.law_agrees`, `Product.model_agrees`,
`Product.marginal1_bad`, `Product.marginal2_bad`, `Product.cover_lower`,
`Product.cover_agrees`, `Product.cover_card`,
`Product.rank_three`, `Matrices.born_probability`, `Product.quantum` and
`result`. Their witnesses are the generic cover obstruction, the parity and
cardinality results, the Born calculation and their stated consequences.
`Square.mu_mass` is bind-only, consumed by `Product.model_nc`;
`Product.model_nc` is bind-only, consumed by `Product.cover_nc`;
`Product.cover_nc` is bind-only, consumed by `Product.cover_card` and
`Product.rank_three`. The remaining helpers are bind-only with consumers
named in the module.
Admission is the external open-problem resolution of #15370 (Proved), with
no atom and no cover operation.

### Experiment

[Exact numerical check](https://github.com/the-omega-institute/trureturing-experiments/tree/dde970c02782127a497db47345cedddaa6bd01aa/docs/reports/horodecki-2022-rank-of-contextuality-non-power-of-two).
Command: `python3 check.py` in that pinned directory; exit $0$, final reading
`bad= 0`. Script SHA-256:
`7712fb6a2d23c748431f4855ed5e6538fefd136c7f983bf35a4dd03917ab9e1b`.
The pinned Git object exists and its script hash matches this value.

Exact integer and Fraction arithmetic checks all $2^9$ square assignments,
all six defect supports of cardinality $16$, the two-row cover of $P$, all
$36\times64$ Born probabilities of $Q$ and its three-model cover. It checks
product upper covers for tensor exponents $k=2,3,4,5$, over respectively
$36,216,1296,7776$ contexts. It does not search all noncontextual covers or prove
minimum cardinality for arbitrary distributions.

## Triage

| Target item | Status and evidence kind | Evidence |
| --- | --- | --- |
| The mechanism | Proved, kernel-checked | `Product.quantum` gives the explicit quantum behavior and `Product.cover_nc`, `Product.cover_agrees`, `Product.cover_card` give its noncontextual cover of size $3$; `Lower.no_two_cover`, `Product.cover_lower` and `Product.rank_three` prove that no cover of size $2$ exists. |
| Readings | Computed | The pinned experiment entry above runs its exact finite checks and reports `bad= 0`; its tested scope is the six Peres–Mermin contexts, $2^9$ assignments, all $36\times64$ product Born probabilities and the three-model cover, plus tensor-product covers for $k=2,3,4,5$ over $36,216,1296,7776$ contexts. |
| Open | Open | Which ranks occur for quantum behaviors in general, ranks for $k\geq6$, single-system non-power-of-two constructions, and the source's other questions remain open. |

### What the settlement shows

**Proved, kernel-checked:** two Peres–Mermin squares have a quantum realization
with rank exactly $3$, via the private `Product.quantum` and `Product.rank_three`.
The decisive mechanism is a three-row defect cover together with the marginal
diagonal obstruction. The bound is sharp for this construction. The public
`result` exports existence, rather than a classification or a general tensor law.

**Proved in prose:** universal tensor additivity of log-rank fails. The parity
obstruction rules out rank $1$ for a single square, while $N_{R_1},N_{R_2}$
cover it: any context differs from at least one of $R_1,R_2$. Thus $RC(P)=2$.
Together with $RC(P\otimes P)=3$, this gives
$\log_2 RC(P\otimes P)=\log_2 3\neq2=2\log_2 RC(P)$.
This is a consequence stated and derived here, not a separate public Lean theorem.
The grouping step in Theorem V.1 assumes that covering models agreeing at one
input have globally identical second marginals; the defect models agree locally
while their other context marginals differ. The parenthetical construction in
the question therefore does not supply a valid general tensor-rank formula.

**Proved in prose:** the diagonal marginal argument gives
$RC(P^{\otimes k})\geq k+1$ for every positive integer $k$.
If a cover has at most $k$ models, assign a distinct factor to each model.
That model's marginal on its assigned factor is noncontextual, hence differs
from $P$ at some context. Use these contexts simultaneously, filling unused
factors arbitrarily. Agreement at that product context would imply agreement
of each selected marginal, a contradiction. This argument uses normalized
product probabilities and marginal preservation of noncontextuality.
It is not a uniform Lean theorem in this module.

**Computed:** defect product covers give upper bounds $3,4,5,6$ for
$k=2,3,4,5$ on the finite scopes in the experiment entry. The preceding prose
lower bound and these verified covers give exact ranks $k+1$ in that range;
this deduction is proved in prose, not a claim that the experiment minimized
rank or that Lean proved all four cases.

**Open formalization:** a separately addressable single-square rank-$2$ theorem
and a tensor-additivity refutation theorem; kernel proofs of the upper covers
for the third, fourth and fifth powers. These are follow-up candidates, not
additional settling claims in this delivery.

**Open:** ranks for $k\geq6$; a construction without tensor products with a
non-power-of-two rank; classification of all quantum ranks and general
constructions or sharper tensor-cover methods. The source's questions about
memory of contextuality and probabilistic databases also remain open here.
No other result of the source is revalidated by this example.

### Escape audit

The escape audit for public `result` is unfinished under
https://github.com/the-omega-institute/trureturing/issues/15745.
The compiled typed Reg metadata fails scoped decoding with
`contract.cannot_decode:metadata:computation_required`, so no Reg mirror is
retained. Source-occurrence/scope validation, source-reconstruction and E1–E8
binding evidence are missing. The target has DTR-Unregistered status; that
observation does not certify four-slot completion.

The public owner `D5.S3.Arith.FibonacciAtomic.NativeContinuation.JointLaw.push_sum`
also has an unfinished escape audit under #15745. Its typed `Contract.Registration`
compiles, but scoped decoding reports `contract.discovery:rigid_universes`.
Source reconstruction, source-occurrence/scope validation and E1–E8 binding
evidence are missing; no Reg mirror is retained.

## ASSUMED-UNVERIFIED

Literature absence is limited to the preregistration's searched sources.
The general tensor lower bound and tensor-additivity consequence above are
prose arguments, not public kernel-checked declarations of this module.
The escape audit is unfinished as specified in #15745.
