---
slug: rajchel-korzekwa-puchala-zyczkowski-2021-circulant-bracelet-sufficiency
bibkey: rajchelkorzekwapuchalazyczkowski2021birkhoff
doi: 10.1063/5.0046581
url: https://arxiv.org/abs/2101.11288
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic.result
---

# Circulant bracelet sufficiency fails in dimension twelve

## Problem

G. Rajchel-Mieldzioć, K. Korzekwa, Z. Puchała and K. Życzkowski, *Algebraic and geometric structures inside the Birkhoff polytope*, arXiv:2101.11288, Section V, asks:

> Another observation that holds for d ≤ 4, and should be further investigated for d > 4, is whether the bracelet condition is sufficient for unistochasticity if we restrict the analysis to the set of circulant matrices.

The universal sufficiency assertion is refuted. Preregistration: [#16299](https://github.com/the-omega-institute/trureturing/issues/16299). The source locator and quoted definitions are in [the Library note](../Library/QuantumBounds/rajchelkorzekwapuchalazyczkowski2021birkhoff.md).

### Statement echo

| Source clause | Formal counterpart | Fidelity |
| --- | --- | --- |
| Definition 5: circulant, with indices modulo $d$ | `IsCirculant` expresses existence of a vector whose Mathlib circulant is the matrix | Mathlib uses $v(i-j)$; reversing the first row gives the source's class |
| Definition 4: entries are squared moduli of a complex unitary matrix | `IsUnistochastic` uses `Matrix.unitaryGroup` and the frozen `RHLinalg.normSqMatrix` | The unitary may be arbitrary; no circulant-unitary restriction is imposed |
| Definition 7: bistochasticity and column and row bracelet inequalities | `IsBracelet` uses `doublyStochastic` and both quantified inequalities | Pairs are distinct: $k\ne l$ for columns, $j\ne k$ for rows. The source counts $d(d-1)$ conditions; ordered pairs repeat the same inequalities |
| Section V: all $d>4$, all circulant bracelet matrices | `claim` quantifies over natural $d$, $4<d$, and all real square matrices | Finite real suprema represent the source's maxima; $d>4$ ensures nonempty index sets |
| A negative answer to the universal assertion | `result` proves the literal negation of `claim` | A counterexample at $d=12$ suffices |

All parameters and conjuncts in these definitions implement the source clauses. There is no additional hypothesis on a unitary realizing the matrix.

## Motivation

Theorem 17 identifies circulant bracelet and circulant unistochastic matrices in dimension four. Bracelet conditions constrain pairwise lengths, whereas unitarity constrains compatible phases across several pairs simultaneously. The higher-dimensional question tests whether the length conditions retain enough of those joint constraints.

## Gap

The source's dimension-four result does not imply its proposed higher-dimensional extension. The matrix below satisfies every bracelet inequality but admits no compatible unitary phases. No published resolution was found in the literature scope recorded in #16299; completeness of that search is not established.

## Route

Put $S=\{0,1,3,4,6,9\}\subset\mathbb Z_{12}$ and

$$
B_{ij}=\begin{cases}1/6&j-i\in S,\\0&j-i\notin S.\end{cases}
$$

Every row and column has six nonzero entries. Every bracelet length is zero or $1/6$. The overlap counts for nonzero shifts $1,\ldots,11$ are $2,2,5,2,2,4,2,2,5,2,2$, so no pair has exactly one positive length. The private lemmas `b_doubly_stochastic`, `sqrt_product`, `constant_bracelet` and `b_bracelet` establish the corresponding claims inside the settling module.

## Falsifier

Assume a unitary $U$ has squared moduli $B$. Its support equals that of $B$. Let $T=\{0,3,6,9\}$. Row 11 meets every row in $T$ exactly in columns $\{0,3\}$, and row 2 meets them exactly in $\{3,6\}$. Row orthogonality forces nonzero constants $\lambda,\mu$ with

$$
U_{r3}=\lambda U_{r0},\qquad U_{r6}=\mu U_{r3}\quad(r\in T).
$$

Columns 0 and 6 overlap exactly in $T$. Their inner product is therefore

$$
\sum_r\overline{U_{r0}}U_{r6}=\mu\lambda\sum_{r\in T}|U_{r0}|^2=\mu\lambda\frac46\ne0,
$$

contradicting column orthogonality. This is the argument in the private `b_not_unistochastic` proof used by `result`.

## Evidence

The settling declaration is `D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic.result` in [the Lean module](../D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic.lean). Its public surface consists of the four source definitions and this single theorem. Its axiom closure is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$. The squared-norm construction is reused from `D5/S3/Weil/ZetaLinear/VonNeumann`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Experiment

[Exact support checks](https://github.com/the-omega-institute/trureturing-experiments/tree/98efcb129b93e9f4e36e0e125779890dc87cf61f/docs/reports/rajchel-korzekwa-puchala-zyczkowski-2021-circulant-bracelet-sufficiency), pinned to commit `98efcb129b93e9f4e36e0e125779890dc87cf61f`, contain `check.py`, SHA-256 `f20cb05f9c88d735be27b8846916e380c431526c703bf6f4b32673ae37b02ee6`. Running `python3 check.py` in that directory exits 0 and reports `ALL_OK`.

The exact-rational checks verify the dimension-twelve matrix and its support chain, the dimension-fifteen CRT pattern, and scaled supports at base dimensions $12,14,15$ with multipliers $m=2,3$. The exhaustive search tests supports containing zero, with sizes $2,\ldots,d-1$, in dimensions $3,\ldots,15$; among supports with no singleton overlap it finds certificate counts 12 at $d=12$, 36 at $d=14$, 28 at $d=15$, and zero at the other tested dimensions. Translation normalizes every nonempty support to contain zero. Singleton and full supports cannot carry this certificate: singleton supports have disjoint distinct columns; full supports leave no row outside their intersection.

## Triage

### What the settlement shows

1. **Proved in Lean — failure mechanism.** `result`, through private `b_bracelet` and `b_not_unistochastic`, proves that bracelet lengths only detect overlap counts for this constant-weight support, while row orthogonality forces parallel column restrictions and contradicts orthogonality of columns 0 and 6. The kernel-checked instance is exactly dimension twelve with the displayed support.

2. **Computed — supports at dimensions 12, 14 and 15.** The experiment entry supplies the exact command, exit code and script identity. Certificate counts in its stated search scope are 12, 36 and 28 respectively. Explicit supports include $S_{14}=\{0,1,2,3,6,7\}$ and $S_{15}=\{1,4,6,7,10,12,13\}$. These additional dimensions are not formalized here.

3. **Proved in prose — every positive multiple of 12, 14 and 15.** Given any certified base support $S\subset\mathbb Z_d$, use $mS\subset\mathbb Z_{md}$. Ordering rows and columns by residues modulo $m$ makes its matrix a direct sum of $m$ base matrices. Cross-block bracelet overlaps vanish and within-block overlaps equal the base overlaps. Any unitary with that support must be block diagonal and would supply a unitary for the base matrix, a contradiction. The experiment verifies $m=2,3$ only; the all-multiples assertion rests on this argument and is not a Lean theorem of this delivery.

4. **Computed — dimension-fifteen CRT relabelling.** The script checks that $S_{15}$ equals the residues with $(s\bmod3=0\text{ and }s\bmod5\in\{1,2\})$ or $s\bmod3=1$. This is the CRT description of the Lundgren–Reid–Severini–Stewart block pattern identified in arXiv:math/0409474, Section 3. The computation verifies the relabelling and support certificate; the historical identification is a literature attribution, not a separate Lean assertion.

5. **Computed — no such certificate at dimensions at most eleven.** The exhaustive search gives zero for $3\le d\le11$ in the scope above. At $d=1,2$, a nonempty column intersection either leaves no outside row or comes from singleton support with disjoint distinct columns, so this particular certificate is impossible by direct inspection. Absence of this certificate is not sufficiency of bracelet conditions.

6. **Proved in prose — positive-entry counterexamples.** The unistochastic set is compact, as the continuous squared-modulus image of the compact unitary group, hence closed. A counterexample $B$ therefore has a neighbourhood disjoint from that set. Let $J/d$ be the uniform matrix and $B_t=(1-t)B+tJ/d$. This is positive and circulant bistochastic for $0<t<1$. For a uniform support of size $k$, put $a=(1-t)/k+t/d$ and $b=t/d$, so $a\ge b>0$. A row or column pair with overlap $q\ge2$ has $q$ lengths equal to $a$, giving sum at least twice the maximum. If $q=0$, there are $2k\ge2$ lengths equal to $\sqrt{ab}$, each at least every remaining length $b$. Thus every bracelet inequality persists. Taking sufficiently small $t>0$ keeps $B_t$ outside the unistochastic set. This argument is not formalized and supplies no numerical neighbourhood radius.

7. **Open — dimensions five through eleven.** The source's sufficiency question in these dimensions is not decided by the theorem or the absence-of-certificate computation.

8. **Open — Conjectures 19 and 9.** The relation between $C_d\cap U_d$ and doubly circulant realizations in Conjecture 19, and the monoid assertion for bracelet matrices in Conjecture 9, are not resolved here.

9. **Literature boundary — surviving source results.** Theorem 17 and the source's statements at dimensions at most four remain applicable. The higher-dimensional universal extension is false; this refutation does not invalidate the source's proved results or decide the two other conjectures.

## ASSUMED-UNVERIFIED

The literature screen and source quotations recorded in #16299 are orchestrator-reported; the pinned support computation is independently rerun by the implementation seat. Literature completeness and priority are `ASSUMED-UNVERIFIED`. The CRT pattern attribution uses the source identified by the search seat. Only the dimension-twelve assertion is kernel-checked here; the family and positive-entry arguments above are explicitly prose arguments. No uniform sufficiency or minimal-counterexample dimension is claimed.
