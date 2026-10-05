---
slug: kulhandjian-hanzo-2026-q2-distance-ceiling
bibkey: kulhandjian2026singer
doi: 10.48550/arXiv.2610.02392
url: https://arxiv.org/abs/2610.02392v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.result
---

# The q = 2 Singer-quadric qubit codes have minimum distance 2 for every d ≥ 2

## Problem

M. Kulhandjian and L. Hanzo, *Singer-Difference-Set Qudit Stabilizer Codes
from Non-Degenerate Quadrics in PG(d,q)*, arXiv:2610.02392v1, construct for a
prime power $q$ and $d\ge2$ a stabilizer code $\mathcal Q(q,d)$ with
$H=(A\mid M_QA)$: $A=\mathrm{circ}(\boldsymbol\tau_H)$ is the Singer incidence
matrix of $\mathrm{PG}(d,q)$ and $M_Q=\mathrm{circ}(\boldsymbol\tau_Q)$ the
quadric circulant. Proposition 23 (Section VII.E) states for $q=2$ and
$d\in\{2,\dots,6\}$ that $u=M_Q\boldsymbol\tau_H\equiv\mathbf 1$, that every
$Z_iZ_j$ lies in the centralizer, and, by exhaustive search for $d\le4$, that
$Z_0Z_1$ is not a stabilizer, so $d_{\min}=2$. Conjecture 24 asserts the
proposition for every $d\ge2$, and the paper's list of open problems asks to
settle it analytically. The verbatim statements are in
[the literature note](../Library/QuantumStates/kulhandjian2026singer.md).

Issue [#13470](https://github.com/the-omega-institute/trureturing/issues/13470)
fixes the reading. At $q=2$: $K=\mathrm{GF}(2^{d+1})$, $n=2^{d+1}-1$,
$(\boldsymbol\tau_H)_i=1$ iff $\operatorname{Tr}(\alpha^i)=0$,
$(\boldsymbol\tau_Q)_i=1$ iff $\operatorname{Tr}(\alpha^{3i})=0$, circulants
have entries $v_{(i-j)\bmod n}$, the centralizer is
$\{(\mathbf a,\mathbf b):\mathbf aH_x^\top=\mathbf bH_z^\top\}$ and the
stabilizers are the row space of $H$. `claim` asserts, for every $d\ge2$ and
every primitive $\alpha$ (the paper fixes one): $u=\mathbf 1$; for $i\ne j$,
$(e_i+e_j,\mathbf 0)$ is in the centralizer and not a stabilizer; every
centralizer element outside the stabilizers has symplectic weight $\ge2$. The
witness has weight 2 also as a Hamming weight, so $d_{\min}=2$ under either
reading of the paper's weight.

## Motivation

The construction is offered as a family of qudit stabilizer codes, and the
paper's discussion of the useful parameter regime rests on the $q=2$ case
being limited to distance 2 for every $d$; the numerical evidence covered
$d\le6$ for $u$ and $d\le4$ for the distance.
`D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.result` proves
the conjecture for every $d\ge2$.

## Gap

Issue #13470 records the literature check before any Lean. The paper has a
single version (2026-10-01, accepted for IEEE Open Journal of the
Communications Society); its remark gives a structural argument only for $d$
even and calls $d$ odd open, and its conclusions list the conjecture as an
open problem. No settlement was found in the repository or in the search
seat's bounded checks; the Semantic Scholar citation API was rate limited.
`not-found-in-searched-scope`.

## Route

Let $m=d+1\ge3$ and $n=2^m-1\ge7$.

1. **Power sums.** $\sum_{x\in K^*}x^e$ is $-1$ if $n\mid e$ and $0$
   otherwise. No exponent $2^r$, $3\cdot2^s$ or $3\cdot2^s-2^r$ with
   $0\le r,s<m$ is divisible by $n$: the last would give $2^t\equiv3\pmod n$
   with $t<m$, impossible as $2^t,3<n$.
2. **$u=\mathbf 1$.** Over $\mathbb F_2$, $[\operatorname{Tr}y=0]=1+\operatorname{Tr}y$.
   Writing $\operatorname{Tr}x=\sum_{i<m}x^{2^i}$,
   $u_k=\sum_{x\in K^*}(1+\operatorname{Tr}x)(1+\operatorname{Tr}(\alpha^{3k}x^{-3}))$
   expands into $n\equiv1$ plus multiples of vanishing power sums. Hence
   $H_x=M_QA$ is the all-ones matrix and every $(e_i+e_j,\mathbf 0)$ is in the
   centralizer.
3. **Trace fibers.** For $b\ne0$, $x\mapsto\operatorname{Tr}(bx)$ is a nonzero
   linear functional, so each fiber has $2^{m-1}$ elements. A row combination
   of $A$ has entries $c+\operatorname{Tr}(b\alpha^{-j})$, hence weight $0$,
   $n$, $2^{m-1}$ or $2^{m-1}-1$, never 2: $(e_i+e_j,\mathbf 0)$ is not a
   stabilizer.
4. **No weight 1.** A weight-1 vector in the centralizer would make the
   all-ones vector, a column of $A$ or its complement zero; every column of $A$
   has weight $2^{m-1}-1\notin\{0,n\}$.

## Falsifier

The proof would fail if $3$ were congruent to a power of $2$ modulo $n$, or if
some trace functional $x\mapsto\operatorname{Tr}(bx)$ with $b\ne0$ vanished
identically.

## Evidence

The canonical source is
`D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.lean`. Its public
declarations are `K`, `n`, `tr`, `tauH`, `tauQ`, `Hz`, `Hx`, `centralizer`,
`stabilizers`, `wt`, `claim` and `result`; circulants are Mathlib's
`Matrix.circulant`. The proof applies `FiniteField.sum_pow_units`,
`FiniteField.algebraMap_trace_eq_sum_pow`, `traceForm_nondegenerate`,
`AddMonoidHom.card_fiber_eq_of_mem_range`, `GaloisField.card`,
`GaloisField.finrank` and `Matrix.circulant_mul`. It uses
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no
`sorry`, `native_decide`, or new axiom. The frozen module state has statement identity
`sha256:9fa8b8b18f3e77936d5e984b004288ada6e8995b2577454001d6c55398e7de6b`.
The result declaration has statement identity
`sha256:cb2e7d43c3fa24263af085336d911223ae6568ea0c88ab654232d0dc36e3b6b6`.
The Freeze event is
`sha256:9b04903278e72a2f79453fd9acbf0144910ba3d26d7787fd32baa06370b856f8`; it
has no project-level frozen prerequisite.

Numerical check (exact $\mathrm{GF}(2^m)$ arithmetic): $u\equiv\mathbf1$ for
$d=2,\dots,10$; the row-space weights of $A$ are exactly $\{0,3,4,7\}$,
$\{0,7,8,15\}$, $\{0,15,16,31\}$ at $d=2,3,4$. Negative controls: with
$\xi=2$ in place of $3$, or with a random $\boldsymbol\tau_Q$, $u$ is not
all-ones at $d=2,\dots,5$.

## Triage

Tier 1 explicit conjecture of a 2026 paper, preregistered in issue #13470
before any Lean. `theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | content | `exponent_exclusions` | open-problem-resolution |

The escape witness `exponent_exclusions` is the arithmetic fact of Route step 1; it is on the proof path of `result` through `correlation_units` and `cross_correlation`. The private theorems whose proof path uses it (`correlation_units`, `cross_correlation`, `hx_ones`, `pair_centralizer`, `small_centralizer_zero`, `distance_lower_bound`) are content; every other private theorem, including `inverse_power_sum_zero` (which uses only the first conjunct $n\nmid2^r$), is bind-only and is used on the proof path of `result` (CLAUDE.md §3.2 「有消费的辅助声明」). Utility is `none`: the module proves a universal statement and
contains no finite enumeration, checker, numeric reduction or certified
instance. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $d\ge2$ and every primitive element, the
cross-correlation is all-ones, every $Z_iZ_j$ is a non-stabilizer element of
the centralizer, and the minimum distance is 2.

**Established inside the proof.** The decisive fact is arithmetic: $3$ is not
congruent to a power of 2 modulo $2^m-1$ (`exponent_exclusions`), so the
exponents of the expanded correlation avoid $0$ modulo $n$. The row space of
$A$ consists of the vectors $c+\operatorname{Tr}(b\alpha^{-j})$ (`row_formula`),
whose weights are $0$, $n$, $2^{m-1}$ and $2^{m-1}-1$ (`row_weights`).

**Argued, not formalized.**

- The same argument gives $u\equiv\mathbf1$ for every exponent $\xi$ in place
  of 3 with $\xi\not\equiv0$ and $\xi\not\equiv2^t\pmod n$, for both
  parities of $d$; the paper's structural remark needs $\gcd(3,n)=1$ and covers
  only $d$ even. Both conditions are needed: for $\xi\equiv0$ the quadric
  indicator is constant (at $d=2$, $\xi=7$, $\operatorname{Tr}(1)=1$ makes it
  zero and $u\ne\mathbf1$), and for $\xi\equiv2^t$,
  $\operatorname{Tr}(x^\xi)=\operatorname{Tr}(x)$ (with $\xi=2$, $u$ is not
  all-ones for $d\le5$). Computed: for $\xi=5$ and $\xi=7$, every
  $d=2,\dots,10$ satisfying both conditions gives $u\equiv\mathbf1$, including
  the cases where $\xi$ divides $n$ ($d=3,7$ for $\xi=5$; $d=5,8$ for
  $\xi=7$); the only excluded pair, $d=2$ with $\xi=7$, gives
  $u\ne\mathbf1$.
- The map $(c,b)\mapsto(c+\operatorname{Tr}(b\alpha^{-j}))_j$ is injective, so
  the row space of $A$, and of $H=(A\mid J)$, has dimension $m+1=d+2$. The code
  is therefore $[[2^{d+1}-1,\,2^{d+1}-d-3,\,2]]_2$ for every $d\ge2$, matching
  the paper's computed $k=3,10,25$ at $d=2,3,4$.

**Open.** The paper's distance conjecture for odd $q$ (its flagship family)
and the Hamada-type rank formula for $q=p^t$ with $t>1$ are not addressed.

**Effect on the paper.** Conjecture 24 holds. The paper's conclusion that
the $q=2$ family is limited to distance 2 (error detection only) holds for all
$d$, not only for the computed range; its other results and conjectures are
unaffected.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof. The search seat's database
readings are seat-reported.
