---
slug: kmv27-evobalance
bibkey: kaygorodov2026evolution
doi: 10.48550/arXiv.2610.22248
url: https://arxiv.org/abs/2610.22248v1
triage: theorem
motivation_gids:
  - D5/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation
---

# Natural-basis dependence of balance in degenerate evolution algebras

## Problem

Kaygorodov, Martín González and Viruel, *Evolution algebras: a survey of
results and a list of open problems*, arXiv:2610.22248v1, Question 27,
page 24, ask:

> Is the balance independent of the natural basis for arbitrary (possibly degenerate) evolution algebras?

The source's section 1.1 states: “Unless stated otherwise, algebras are
finite-dimensional.” The assertion concerns every field, bilinear evolution
multiplication and pair of natural bases. It adds no nondegeneracy,
perfectness, characteristic or connectedness assumption. The other two
questions about a complete system of graph invariants are outside this
settlement. Preregistration: [#21625](https://github.com/the-omega-institute/trureturing/issues/21625).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| A field and a finite-dimensional algebra | `claim` quantifies `k`, `V`, field, additive-group, module and finite-dimensional instances, and bilinear `μ` | No associativity or unit assumption |
| Evolution algebra | Existing `DerivationAnnihilatorObstruction.IsEvolutionAlgebra` | The arbitrary-field natural-basis predicate is reused |
| Every two natural bases | `ι`, `κ`, their `Fintype` instances, `B`, `F`, and both zero mixed-product laws in `claim` | Different index types are allowed |
| Row square coefficient gives an arrow | `associatedGraph` | Basis coordinates of the square, with the source's row order |
| A path retains actual arrows traversed forwards or backwards | `Path.vertex`, `Path.edge`, `Path.isEdge`, `Path.traverses` | Opposing arrows remain distinct choices |
| A cycle has equal first and last vertices | `IsCycle` | All finite lengths, including zero |
| Forward cardinality minus backward cardinality | `pathBalance` | Both counts are cast to integers; loops enter both sets |
| Gcd of all absolute cycle balances | `graphBalance` | Absolute integer ideal generator; no length cutoff |
| The balances agree | Equality in `claim`; `result` proves its negation | The rational four-dimensional instance refutes the universal assertion |

The graph definitions also accept infinite vertex types and the height
lemma arbitrary moduli; these stronger helper domains do not restrict the
finite-basis assertion. Closing universes at `Type` supplies a closed
proposition and includes the rational counterexample. The zero gcd is zero.

## Motivation

An annihilator direction permits a shear of a natural basis without changing
any mixed product. Square-support coordinates can nevertheless change.
Balance therefore detects information that this freedom need not preserve.

## Gap

Alshatnawi, Costoya and Viruel, arXiv:2607.15154v1, Definitions 2.1, 2.2
and 2.4, supply the directed-path and all-cycle balance definitions.
Their Theorem 6.1 assumes a nonzero nondegenerate evolution algebra. The
survey's perfect-algebra rigidity theorem has a separate stronger
hypothesis. Neither assertion covers the degenerate example.
The literature screen in #21625 located no exact settlement within its
inspected scope; completeness and priority are `ASSUMED-UNVERIFIED`.
The two source DOIs have distinct canonical notes:
`Library/QuadraticForms/kaygorodov2026evolution.md` and
`Library/QuadraticForms/alshatnawicostoyaviruel2026grothendieck.md`.

## Route

Over any field take a basis $(a,b,u,z)$ with
$a^2=b$, $b^2=a+u$, $u^2=z$, $z^2=0$, and zero mixed products.
The new basis $(a+z,b,u,z)$ is obtained by a transvection. Its only changed
square row is $b^2=(a+z)+u-z$. The coefficient $-1$ stays nonzero in
characteristic two.

The old graph has arrows $0\to1$, $1\to0$, $1\to2$, $2\to3$.
Heights $(0,1,0,1)$ in $\mathbb Z/2\mathbb Z$ increase along every arrow.
On any closed signed path the height increments telescope, so every balance
is even. The directed two-cycle has balance two, proving that the all-cycle
gcd is two. The new graph adds $1\to3$; the path
$1\to2\to3\leftarrow1$ has balance one, so the new gcd is one.
The private arbitrary-field helpers `old_natural`, `new_natural`, `evolution`,
`old_graph` and `new_graph` verify the algebra and coordinate transport.
`old_balance` and `new_balance` supply the two gcd values. The public
`result` specializes to $\mathbb Q$ and contradicts the universal equality.

## Falsifier

The assertion would not be refuted if either displayed family failed to be
a basis, had a nonzero mixed product, used column rather than row support,
or replaced the all-cycle gcd by a bounded-length calculation. The kernel
proof checks basis transport, naturality, exact support and the all-length
balance argument. The loop ambiguity in the source's informal wording has
no effect on these loop-free graphs.

## Evidence

The settling declaration is
`D5/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation.result`,
with literal type `Not claim`. Its module contains no other authored public
theorem. The public result is the designated refutation result (`basis=refutes`)
and is exempt from four-slot escape registration (CLAUDE.md §3.9).
The module's admission basis is `open-problem-resolution (#21625; Refuted)`;
all theorem proof shapes are conservatively `bind-only`, with every private
helper consumed. No escape-witness admission is claimed.

### Exact finite computation

[Experiment directory at commit 229beb623231963298f417d3dec1bbb44b3eeab0](https://github.com/the-omega-institute/trureturing-experiments/tree/229beb623231963298f417d3dec1bbb44b3eeab0/docs/reports/kmv-q27-balance).
The pinned `check.py` was extracted from that commit and executed with
`python3 docs/reports/kmv-q27-balance/check.py`, exit 0;
SHA-256 `a8d0058590501bd93df3cc66c236eb1f3f603cc87d56fa66c2507ad8fccb6663`.
The final result is `ALL_CHECKS_OK`. Exact rational and modular arithmetic
checks 95 cases: $m=2,\ldots,20$ over
$\mathbb Q,\mathbb F_2,\mathbb F_3,\mathbb F_5,\mathbb F_7$.
It checks all basis products, determinant one, annihilator dimension one,
exact support, connectedness, absence of loops, height increments and balances
$m,1$. A spanning-forest potential calculation gives the all-cycle gcd for
each tested graph. A separate enumeration cross-checks lengths at most seven
for $m=2,\ldots,6$; that bounded enumeration does not establish an unbounded
statement. These are computed readings, separate from the kernel proof.

## Triage

### Coverage

| Item | Status and evidence |
| --- | --- |
| The final yes/no assertion in Question 27 is false with the exact binding definitions | **Proved, kernel-checked:** public `result : Not claim` |
| The four-dimensional witness, naturality and support transport work over every field, including characteristic two | **Proved, kernel-checked:** private `old_natural`, `new_natural`, `evolution`, `old_graph`, `new_graph`; their field binders have no characteristic restriction or division by two |
| An arrow-incrementing $\mathbb Z/d\mathbb Z$ height on a loop-free graph forces every closed signed-path balance to be divisible by $d$, including graphs with sinks | **Proved, kernel-checked:** private `cycle_balance_dvd_of_height`, arbitrary vertex type, modulus and path length; no no-sink hypothesis |
| Basis transport, determinant one, annihilator dimension one, connected loop-free graphs and balances $m,1$ for the stated finite family | **Computed:** the pinned experiment above, all 95 cases for $m=2,\ldots,20$ over the five named fields |
| Lean formalization of the entire $m\ge2$ algebra family | **Open formalization:** the kernel proof covers the four-dimensional instance over every field and the generic height lemma; the mathematical family has the prose proof below |
| Classification of degenerate evolution algebras whose balance is basis-independent | **Open:** this counterexample gives no necessary-and-sufficient classification |
| New proofs of nondegenerate balance invariance or perfect-algebra basis rigidity | **Open in this delivery:** those literature-attested theorems retain their source hypotheses and are not refuted by this witness |

### What the settlement shows

**Proved in prose, uniform family.** For every field and integer $m\ge2$,
use a basis $(c_0,\ldots,c_{m-1},u,z)$ with
$c_i^2=c_{i+1}$ for $i<m-1$, $c_{m-1}^2=c_0+u$, $u^2=z$, $z^2=0$,
and zero mixed products. If a vector annihilates this algebra, multiplying
it by each $c_i$ forces every $c_i$ coefficient to vanish, since each
$c_i^2$ is nonzero; multiplying it by $u$ forces the $u$ coefficient to
vanish. Conversely $z$ annihilates every basis vector. Thus the annihilator
is exactly the line spanned by $z$.

Replacing $c_0$ by $c_0+z$ has inverse obtained by subtraction of $z$, and
preserves naturality. In the changed coordinates
$c_{m-1}^2=(c_0+z)+u-z$, so exactly the arrow $c_{m-1}\to z$ is added.
For the old graph assign $h(c_i)=i$, $h(u)=0$, $h(z)=1$ in
$\mathbb Z/m\mathbb Z$. Every arrow raises height by one. The sum of
signed height differences on a closed path is zero, so $m$ divides every
cycle balance. The core directed cycle has balance $m$, hence the gcd is
$m$. In the new graph $c_{m-1}\to u\to z\leftarrow c_{m-1}$ has balance
one, hence the gcd is one. This proves the uniform mathematical family in
prose, without claiming a uniform Lean formalization.

**Mechanism and boundary.** The annihilator shear preserves all mixed-product
relations but changes square support. The same algebra can therefore have
arbitrarily large balance in one natural basis and balance one in another.
Nondegenerate balance invariance and perfect-algebra basis rigidity keep
their original hypotheses. No consequence requiring the degenerate
extension can use that extension as a universal invariant. The other
questions in Question 27, including a complete invariant system for
nondegenerate algebras, remain open here.

## ASSUMED-UNVERIFIED

The literature screen's completeness and absence of another published
settlement are `ASSUMED-UNVERIFIED`. The screen reported in #21625 inspected
both v1 sources, related papers and author searches; citation enumeration
was limited by OpenAlex and Semantic Scholar HTTP 429 responses, and broad
issue searches reached their caps. No exhaustive priority claim is made.
The entire $m\ge2$ family has a prose proof but no Lean proof in this module.
