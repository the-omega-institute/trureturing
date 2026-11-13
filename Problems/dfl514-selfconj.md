---
slug: dfl514-selfconj
bibkey: dietzflowerslockard2026cmp
doi: 10.13069/jacodesmath.v13i3.393
url: https://jacodesmath.com/index.php/jacodesmath/article/download/393/304
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Partitions/OddPowerSelfConjugateCMP.result
---

# No self-conjugate CMP has odd-power size at an odd base

## Problem

Dietz, Flowers and Lockard, *A study of m-ary partitions whose conjugates are q-ary*, J. Algebra Comb. Discrete Struct. Appl. 13(3) (2026), 385–407, Question 5.14 on printed page 404 (publisher PDF page 20 of 23), asks:

> When $m$ is odd, are there any self-conjugate CMPs of odd powers of $m$?

Publisher PDF: <https://jacodesmath.com/index.php/jacodesmath/article/download/393/304> (SHA-256 `8cfd13c27c0efe648465ae9cfa871008125649d5fd4bb6ac6dacdbd284be9511`). The HTML version is arXiv:2609.08799v1, where the same question is labelled `V.20`.

The answer is no. For every odd natural base $m\ge2$, every natural $s$, and every finite Ferrers diagram $\mu$ with $|\mu|=m^{2s+1}$, if $\mu$ and its transpose are both $m$-ary, then $\mu^\mathsf T\ne\mu$. No primality assumption or finite cutoff is imposed. The source's introductory scope is bases at least two. The exponent $s=0$ is included.

### Statement echo

All unqualified declaration names below belong to `D5.S3.Combinatorics.Partitions.OddPowerSelfConjugateCMP`.

| Source clause | Formal counterpart | Fidelity |
| --- | --- | --- |
| Definition 1.1(2): “If all of the parts of λ are powers of m, then we say λ is m-ary.” | `IsMAry` | Every positive `YoungDiagram.rowLen` is $m^j$ for a natural $j$; zero rows are absent parts. |
| Definition 1.1(2): “Let a_i denote the number of times that the part m^i appears in λ.” | `multiplicity` | The count of $m^j$ in `YoungDiagram.rowLens`. |
| Definition 1.1(3): “If λ and λ' are both m-ary, then λ is a conjugate m-ary partition (or CMP).” | `IsCMP` | Both literal $m$-ary conditions. |
| Odd $m$ in the source's $m\ge2$ scope | `claim`, `result` | Arbitrary natural $m$, with $2\le m$ and `Odd m`. |
| Odd powers of $m$ | `claim`, `result` | Arbitrary natural $s$, size $m^{2s+1}$. |
| Self-conjugate CMP | `claim`, `result` | Literal equality with `YoungDiagram.transpose`, excluded by the theorem. |
| Negative answer to the interrogative | `result` | Universal nonexistence; the negative proposition is not attributed to the authors as a conjecture. |

## Motivation

The single public endpoint `D5/S3/Combinatorics/Partitions/OddPowerSelfConjugateCMP.result` settles the whole quoted question with admission basis `open-problem-resolution (#21691; Proved)`. The module has `generality: G` and `utility: none`. Its argument is symbolic over arbitrary diagrams, bases and exponents. The public definitions are the literal preregistered conventions; the proof reuses the existing Ferrers carrier and its operations.

The source and its versioned locator are recorded in [the Library note](../Library/FiniteGeometry/dietzflowerslockard2026cmp.md). The named problem is preregistered in [#21691](https://github.com/the-omega-institute/trureturing/issues/21691).

## Gap

The obstruction must use actual row and column geometry. Replacing self-conjugacy by an abstract congruence hypothesis would omit the connection to the source's partitions. The proof establishes that connection from finite row fibers and the transpose.

## Route

Write $N=|\mu|$ and $L=\mu.\operatorname{rowLen}(0)$. For a positive row width $w$, the rows having exactly that width form the difference of the initial ranges of lengths $\mu.\operatorname{colLen}(w-1)$ and $\mu.\operatorname{colLen}(w)$. The private `row_fiber` and `row_count` establish this equality and its cardinality. The original owner declarations `D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts.height_bounds` and `rowLen_zero` supply the positive-height bounds and the zero-row boundary, respectively, through transpose in `square_modulus`.

For a nonempty self-conjugate CMP, let $C_w$ be the number of rows of width $w$ and let $S$ be the finite set of positive row widths. Every positive column height and every $w\in S$ is a power of $m$. Hence, with all differences interpreted in $\mathbb Z$,

$$
(m-1)\mid C_w-\mathbf1_{w=L},\qquad (m-1)\mid w-1.
$$

The finite fiber identities give $\sum_{w\in S}C_w=L$ and $\sum_{w\in S}C_ww=N$. Therefore

$$
\sum_{w\in S}(C_w-\mathbf1_{w=L})(w-1)=N-(2L-1),
\qquad (m-1)^2\mid N-(2L-1).
$$

These steps are the private `square_modulus`. Its statement assumes only a natural $m$, the two $m$-ary conditions, a positive largest row, and self-conjugacy. It assumes neither $m\ge2$ nor primality.

For odd $m$, the private `odd_modulus` uses $2\mid m-1$ and $(m-1)\mid L-1$ to obtain $2(m-1)\mid N-1$. On the other hand, $2(m-1)\mid m^2-1$, so $2(m-1)\mid m^{2s+1}-m$. For $N=m^{2s+1}$ these two divisibilities force $2(m-1)\mid m-1$, contradicting $m\ge2$. This is `result`.

The five private helpers and the endpoint are classified `bind-only` after expansion into existing finite-fiber, divisibility and normalization owners. No independent escape witness or new-content claim is made; the endpoint uses the separately allowed named open-problem resolution basis. The owner publications retain their original statements and proofs.

## Falsifier

A self-conjugate CMP of size $m^{2s+1}$ at any odd natural base $m\ge2$ would falsify the conclusion. Altering the meaning of parts, transpose or self-conjugacy would change the question. The binary example below shows why the odd-base condition cannot simply be deleted.

## Evidence

The formal source is [OddPowerSelfConjugateCMP.lean](../D5/S3/Combinatorics/Partitions/OddPowerSelfConjugateCMP.lean), with its [Blueprint](../Blueprint/D5/S3/Combinatorics/Partitions/OddPowerSelfConjugateCMP.md). Its public endpoint is `D5.S3.Combinatorics.Partitions.OddPowerSelfConjugateCMP.result`. Exact kernel and axiom checks are required for this formal evidence; finite experiments do not establish its unbounded quantifiers.

The escape audit is unfinished for this endpoint and for the two published owner theorems `height_bounds` and `rowLen_zero`: [#26781](https://github.com/the-omega-institute/trureturing/issues/26781). The existing owner's registration of `height_mem_iff` does not register these statements. Target-specific realization, reconstruction, variation, sensitivity and source-selection evidence is missing. No `declared_validated` status is asserted.

### Exact finite experiment

[Experiment directory at commit 9d9a1f1e46aa774f54567133c9453a0455da9eb0](https://github.com/the-omega-institute/trureturing-experiments/tree/9d9a1f1e46aa774f54567133c9453a0455da9eb0/docs/reports/dfl-q514-selfconj). The verified blob is `docs/reports/dfl-q514-selfconj/check.py`, SHA-256 `28ce7d9d5ebb7eb410fb39f7888ec27bcc7177f4722ab4ffb06d54a3aa6fa90c`. Executing its extracted bytes with `python3 /tmp/op-dfl514/check.py` exits 0 with `ALL_CHECKS_OK`.

The exact integer computation checks 24,992 nonzero multiplicity tuples at bases 2 through 9; transposition on all 81,155 partitions of sizes 1 through 35, with CMP tests at bases 2 through 35; 10,731 block diagrams from nonempty subsets of exponents 0 through 8 at bases 2 through 22, including 5,110 odd-base cases; and the 189 square-family pairs $2\le m\le22$, $0\le t\le8$. It checks that binary rows $(4,2,1,1)$ have size $8=2^3$ and are self-conjugate. No uniform classification follows from these finite tests.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Scope and boundary |
| --- | --- | --- |
| Square-modulus obstruction | Proved, kernel-checked: private `square_modulus`. | Every nonempty self-conjugate CMP satisfies $(m-1)^2\mid N-(2L-1)$. The row-multiplicity identities in Route explain its proof. |
| Generality of the modulus statements | Proved, kernel-checked: private `square_modulus` and `odd_modulus`. | The square statement permits every natural $m$ under its explicit diagram hypotheses, without primality or $m\ge2$. For odd $m$, the latter gives $2(m-1)\mid N-1$. |
| Universal answer to Question 5.14 | Proved, kernel-checked: `result`. | Every odd natural $m\ge2$ and every odd exponent $2s+1$. |
| Source definitions and partial-sum criterion | Computed: the exact experiment above, exit 0, with the stated script SHA-256. | The source example has rows $(9,3,3)$ and its stated transpose; 24,992 nonzero multiplicity tuples in $\{0,1,2,3,4\}^5$ are checked at bases 2 through 9. |
| Explicit geometric transposition | Computed: the same exact experiment, exit 0, with the stated script SHA-256. | All 81,155 partitions of sizes 1 through 35 are checked; 303 are self-conjugate and 70 base/diagram pairs satisfy the CMP hypotheses within bases 2 through 35. |
| Larger block family | Computed: the same exact experiment, exit 0, with the stated script SHA-256. | 10,731 nonempty exponent-subset diagrams at bases 2 through 22, with exponents 0 through 8; the odd-base obstruction is checked on 5,110 cases. No uniform classification follows from this enumeration. |
| Necessity of the odd-base restriction | Computed: the exact experiment above, exit 0, with the stated script SHA-256. | Rows $(4,2,1,1)$ give a binary self-conjugate CMP of size $8=2^3$. |
| Known square construction | Computed: the same exact experiment, exit 0, with the stated script SHA-256. | All 189 pairs $2\le m\le22$, $0\le t\le8$ check $m^t$ rows of length $m^t$ and size $m^{2t}$. The general family is already in source Discussion 5.11; it is not a new Lean theorem here. |
| Classification and neighboring questions | Open. | No full classification of self-conjugate CMP sizes is supplied. Questions 5.12 and 5.13 about smallest odd-power and nonsquare examples are not settled. |

The decisive invariant is the modulus-square divisibility and its odd-base consequence. The square family remains compatible with it; the even-base boundary lies outside the endpoint's hypotheses. No change to the source's other results is claimed, and no further question is counted as settled.

### Literature status

The source and literature screen are recorded in #21691. That bounded screen identified no prior settlement of Question 5.14. It covered the source's journal and arXiv versions, author and full-text arXiv searches, the successfully returned Crossref and MathOverflow results, and repository searches. Rate-limited citation services, ineffective queries and unavailable general-web results do not establish absence of prior art.

## ASSUMED-UNVERIFIED

Literature completeness, worldwide priority and absence of every equivalent prior settlement are `ASSUMED-UNVERIFIED`. The finite experiment establishes only its stated range. The escape registration remains unfinished under #26781; its linked issue is not a proof or a validated registration.
