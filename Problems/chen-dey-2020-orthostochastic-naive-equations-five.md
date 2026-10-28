---
slug: chen-dey-2020-orthostochastic-naive-equations-five
bibkey: chendey2023orthostochastic
doi: 10.1080/10586458.2021.1982427
url: https://arxiv.org/abs/2001.10691
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive.result
---

# The naive orthostochastic equations are insufficient at order five

## Problem

J. Chen and P. Dey, *The 4 × 4 orthostochastic variety*, arXiv:2001.10691v1, Experimental Mathematics 32(4) (2023), 692–700, DOI 10.1080/10586458.2021.1982427, Question 5 (cf. Chterental–Đoković, Remark 3.4), asks:

> Do the naive equations define the orthostochastic variety inside B_n? In other words, if a doubly stochastic matrix satisfies C_{i,j}, R_{i,j} = 0 for all i < j, must it be orthostochastic?

Section 5 states:

> Next, for n = 4, 5 it remains open whether the naive equations cut out the orthostochastic variety inside the Birkhoff polytope set-theoretically.

The order-five clause is **Refuted** by $B=(4J_5-3I_5)/17$. [Preregistration #17606](https://github.com/the-omega-institute/trureturing/issues/17606) fixes the source, quantifiers and conventions. The [Library note](../Library/QuantumBounds/chendey2023orthostochastic.md) contains the source locators and quotations.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| A real orthostochastic matrix is the entrywise square of an orthogonal matrix | `IsOrthostochastic` quantifies over every real orthogonal matrix and uses `RHLinalg.normSqMatrix` | For real entries, the squared norm is the square |
| The equivalent sign condition after Definition 4 for $C_{i,j}=0$ | `ColumnNaive` quantifies over all real signs equal to $1$ or $-1$ and requires the signed radical sum to vanish | A sign on every term is equivalent to fixing the first sign to $1$, by reversing all signs together |
| Row equations are obtained “by transposing indices” | `RowNaive` exchanges the row and column positions in that sum | No symmetry assumption on the quantified matrix |
| Every pair $i<j$, both $C_{i,j}=0$ and $R_{i,j}=0$ | `SatisfiesNaive` requires both conditions for every such pair | Zero-based `Fin n` replaces the source's one-based indices |
| Every doubly stochastic matrix at $n=5$ | `claim` quantifies over every real five by five matrix in Mathlib's `doublyStochastic` set | The only restriction is the order-five clause being settled |
| The naive equations imply orthostochasticity | The final implication in `claim` | No restriction on an orthogonal lift or its signs |
| A negative answer | `result` proves the literal negation of `claim` | The witness `B` has diagonal $1/17$ and off-diagonal $4/17$ |

These are all binders and conjuncts in the public predicates. The concrete witness is additional data used to refute the universal assertion, not an additional hypothesis.

## Motivation

Pairwise orthogonality can choose different signs for different pairs. A single orthogonal lift requires all those choices to come from one matrix. The example separates these two requirements using an integer determinant obstruction.

## Gap

The signed radical equations do not characterize orthostochasticity at order five. Chen–Dey's Proposition 6 already provides counterexamples at every order at least six. Their order-four question is not settled here.

The literature screen supplied with #17606 and the independent search input includes the full arXiv v1 source, Chterental–Đoković arXiv:0708.4051, Turek–Cheon arXiv:1104.0408, and accessible text screens of arXiv:1708.09559, 1807.03295, 1804.10715, 1905.07035, 2310.03436 and 1301.2537. No prior order-five answer was located in that scope. These are attributed literature readings; completeness and priority remain `ASSUMED-UNVERIFIED`.

## Route

Every entry of $B$ is positive and every row and column sums to one. For distinct columns $i,j$, the radical terms are $2/17,2/17,4/17,4/17,4/17$. Put positive signs at $i,j$ and at one other index, and negative signs at the remaining two indices. The sum is zero. Symmetry of $B$ gives the row conditions.

The private lemmas `b_doubly_stochastic` and `b_naive` supply the two hypotheses used by `result`. The row and column sign choices need not be mutually compatible.

## Falsifier

An orthogonal lift $U$ would give $M=\sqrt{17}\,U$ with integer entries: $\pm1$ on the diagonal and $\pm2$ elsewhere. Orthogonality gives $MM^{\mathsf T}=17I_5$, hence $(\det M)^2=17^5$. The right-hand side is not an integer square. The private `lift_entry_integer`, `scaled_mul_transpose`, `seventeen_pow_five_not_square` and `b_not_orthostochastic` implement this contradiction.

## Evidence

The settling declaration is `D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive.result` in [the Lean module](../D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive.lean). The public surface consists of six definitions and `result`; all twelve theorem helpers and the two sign-selection definitions are private. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The module has `admission_basis: open-problem-resolution (#17606; Refuted)`, `generality: I`, and certified-instance utility with `basis=refutes`. Its theorem steps are classified `proof_shape: bind-only`, with the consumed private helpers listed in the module comment. There is no claim of a separate escape witness.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Experiment

The experiment is [docs/reports/chen-dey-2020-orthostochastic-naive-equations-five/](https://github.com/the-omega-institute/trureturing-experiments/tree/2840cb18888954b7c04dcf3f3327e4832f0ec6d6/docs/reports/chen-dey-2020-orthostochastic-naive-equations-five) at commit `2840cb18888954b7c04dcf3f3327e4832f0ec6d6`. Command: `python3 check.py` in that directory; exit 0, `ALL_OK`. The script's SHA-256 is `32f9dd1289589cc8e0720386b843321258465c4b9bdc88556d56b3488c8381fd`.

Exact rational arithmetic checks positivity and stochasticity of the order-five witness. The pairwise radical checks at that witness use floating square roots with tolerance $10^{-12}$; the Lean proof independently establishes the exact sign identities. The integer-square test checks that $17^5$ is not a square. Exhaustive sign backtracking finds no lift at $(n,k)=(5,1),(7,1),(7,3)$ and finds a lift at $(5,3),(7,5)$. Those are the complete tested parameter pairs; the experiment supplies no uniform classification.

## Triage

### What the settlement shows

1. **Kernel-checked — arithmetic obstruction.** `b_doubly_stochastic` and `b_naive` establish the order-five instance's hypotheses. `lift_entry_integer` and `scaled_mul_transpose` turn any global lift into the integer determinant contradiction used by `b_not_orthostochastic`; `result` refutes Question 5 at order five. Local pairwise sign choices exist, but no common lift exists.

2. **Proved in prose — odd-order constant-ratio family.** Assume odd $n\ge3$, diagonal entry $a\ge0$, off-diagonal entry $b>0$, and $a+(n-1)b=1$. Write $t=\sqrt{a/b}$. The pairwise radical equation, divided by $b$, has two terms of size $t$ and $n-2$ terms of size one. Opposite signs on the two $t$ terms leave an odd sum of unit signs, which cannot vanish. Equal signs require $2t=k$ to be an odd integer with $1\le k\le n-2$; every such $k$ is attainable by choosing the unit signs. Thus these and only these parameters satisfy all naive equations. Equivalently,

   $$B_{n,k}=\frac{4J_n+(k^2-4)I_n}{k^2+4(n-1)},\qquad k=1,3,\ldots,n-2.$$

   If a lift exists, normalize its diagonal signs by multiplying rows by $-1$ as needed and scale it to $X=(k/2)I+S$, where $S$ has zero diagonal and off-diagonal entries $\pm1$. Orthogonality of distinct rows gives

   $$\frac{k}{2}(S_{ij}+S_{ji})+\sum_{\ell\ne i,j}S_{i\ell}S_{j\ell}=0.$$

   The sum is odd, so $S_{ij}=-S_{ji}$ is impossible. Hence $S$ is symmetric and $S^2+kS=(n-1)I$. Conjugate by a diagonal sign matrix so that the first row of $S$ has all off-diagonal signs positive. On the remaining $n-1$ vertices let $A$ join positive signs. The first-row equations imply that this graph is regular of degree $d=(n-2-k)/2$. For two remaining vertices with adjacency indicator $e$ and $c$ common neighbours, the same matrix identity gives

   $$2c=d-(k+2)e.$$

   If $k\le n-4$, then $d\ge1$, so an edge exists. Also $d<n-2$, so a nonedge exists. A nonedge forces $d$ even, whereas an edge forces $d-k-2$ even, hence $d$ odd. This contradiction excludes every $k\le n-4$. At $k=n-2$, the orthogonal matrix $I-(2/n)J$ realizes $B_{n,k}$. Consequently every odd $n\ge5$ has $(n-3)/2$ spurious points on this line. The symmetric constant-ratio obstruction is credited to Turek–Cheon, [arXiv:1104.0408](https://arxiv.org/abs/1104.0408), Theorem 6.5 and Remark 6.6. This family argument is not formalized in the module.

3. **Proved in prose using a source result — all orders $n\ge5$.** The kernel-checked order-five refutation and Chen–Dey's Proposition 6 for every $n\ge6$ give a negative answer at every order at least five. Proposition 6 is a literature premise, not an imported Lean theorem. No other source theorem is invalidated by refuting the question; the source's established order-at-least-six result remains applicable.

4. **Open — order four.** Whether the naive octics cut out the four by four orthostochastic variety inside the Birkhoff polytope remains outside this settlement.

5. **Computed — finite experiment.** The pinned experiment above checks exactly the order-five witness and the five listed $(n,k)$ pairs, with exit 0 and `ALL_OK`. The uniform family statement in item 2 rests on its prose derivation, not on that finite computation.

6. **Literature reading — bounded screen.** The source v1 is reported read in full in the supplied search input. No prior order-five answer was located in the stated screen. The journal versions of record, Seberry–Lam (1982) and Lam (1983) are unread; completeness is `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

Literature completeness, priority, the journal versions of record, Seberry–Lam (1982), Lam (1983), and a complete later-author/citing-work inventory are unverified. The family proof is prose only. The order-four problem remains open. The refutation does not claim that all orthostochastic matrices, or all spurious naive solutions, have the displayed constant-ratio form.
