---
slug: hastings-2017-small-majorana-fourteen-mode-distance-four
bibkey: hastings2017smallmajorana
doi: 10.26421/QIC17.13-14-7
url: https://arxiv.org/abs/1703.00612v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Codes/MajoranaFourteenModeDistanceFour.result
---

# No parity Majorana code on at most fourteen modes has distance four and a logical qubit

## Problem

M. B. Hastings, *Small Majorana Fermion Codes*, Quantum Inf. Comput. 17(13–14), 1191–1205 (2017), arXiv:1703.00612v1, Section II.B, PDF p. 5 (`c.tex`, line 272):

> For $N_{\rm maj}=14$, we performed a numerical search (described in the next section) for a code with $N_{\rm stab}=6$ and did not succeed. Hence, we believe that no such code exists, i.e., we believe that $N_{\rm maj}=16$ is the minimum number of modes to have $d=4,K>0$.

The paper uses $N_{\rm maj}$ for the number of Majorana modes, $N_{\rm stab}$ for the number of independent stabilizers, and $K=N_{\rm maj}/2-N_{\rm stab}$ for the number of logical qubits. Its stabilizer bit strings form a self-orthogonal binary subspace $C$, meaning $x\cdot y=0$ for every $x,y\in C$, including $x=y$ (`c.tex`, lines 85–105). Logical operators correspond to $C^\perp\setminus C$, and distance is their minimum Hamming weight (lines 108–113). The paper requires the all-ones fermion-parity vector $\mathbf1$ to belong to $C$ (lines 115–118). These definitions and the quotation are also recorded in [the literature note](../Library/Hamming/hastings2017smallmajorana.md).

Issue [#23984](https://github.com/the-omega-institute/trureturing/issues/23984) fixes the statement: for every natural number $n\le14$ and every binary linear subspace $C\le\mathbb F_2^n$, if $C$ is self-orthogonal, $\mathbf1\in C$, and $2\dim C<n$, then

$\exists v\in C^\perp\setminus C,\quad \operatorname{wt}(v)<4.$

This is `claim`, and `result : claim` proves it. The conclusion supplies a logical operator directly; it does not define distance through an infimum. The sixteen-mode existence statement is outside `claim`.

## Motivation

The source's distance-four codes target correction of errors on a single Majorana mode (`c.tex`, lines 121–124). Determining the smallest mode count with a positive logical-qubit count settles the lower endpoint of this construction problem. Distinct error syndromes alone allow fourteen columns with six independent stabilizers; commutation imposes additional constraints. Hastings constructs a sixteen-mode Hamming Majorana code with three logical qubits and distance four (Section II.B, lines 219–253), so excluding smaller codes is the missing nonexistence half of the stated minimum.

## Gap

The bounded literature check recorded in #23984 covers:

- the arXiv source, reported there as having only v1, which retains the quoted belief;
- searches for the title with “14”, “minimum modes”, “distance 4” and “classification”, and for optimal Majorana-code tables, reported to return the source, patent US10574268 and the journal record without a settlement;
- abstracts of citing preprints arXiv:1704.01589, arXiv:1708.05012 and arXiv:1812.08477, reported there to concern hardware, braiding and surface-code scaling;
- repository issue searches for “1703.00612”, “Majorana fermion code” and “Hastings Majorana”, reported to find no prior work.

`not-found-in-searched-scope`. The source quotation is checked against the fetched v1 TeX and PDF; the reported searches and citing-preprint readings are not independently reproduced. In particular, the check does not exclude an existing classical classification of binary self-orthogonal codes that implies this bound.

## Route

Write $I$ for a finite coordinate type with decidable equality, $N=|I|$, $C\le\mathbb F_2^I$, and $r=\dim C$. All dot products and Boolean moments below are over $\mathbb F_2$.

1. **Parity and reduction.** For self-orthogonal $C$ containing $\mathbf1$, `parity_card` gives even $N$. If additionally $i\ne j$ and $e_i+e_j\in C$, `remove_pair` produces a self-orthogonal space $D$ on $I\setminus\{i,j\}$ containing its all-ones vector, with $\dim D+1=r$ and $|I\setminus\{i,j\}|+2=N$. For every $v\in D^\perp\setminus D$ with $\operatorname{wt}(v)<4$, it supplies a $w\in C^\perp\setminus C$ with $\operatorname{wt}(w)<4$. Thus, when $N\le14$ and $2r<N$, the reduced space retains both inequalities needed for induction.

2. **Injective columns and moments.** Suppose $C$ is self-orthogonal, contains $\mathbf1$, satisfies $N\le14$ and $2r<N$, and contains no $e_i+e_j$ with $i\ne j$. If the desired logical vector does not exist, every such pair is outside $C^\perp$: `pair_weight` gives weight two for distinct $i,j$, and the pair is already outside $C$. With $\mathbf1\in C$, $N>0$, and this exclusion of every distinct pair from $C^\perp$, `column_encoding` gives $k+1=r$ and vectors $r_a\in C$, indexed by $a\in\mathrm{Fin}\,k$, whose column map $i\mapsto(r_a(i))_a$ is injective. For self-orthogonal $C$ containing $\mathbf1$ and any such injective column map, `column_moments` says its image $S\subseteq\mathbb F_2^k$ has $|S|=N$ and, for every $A\subseteq\mathrm{Fin}\,k$ with $|A|\le2$,

   $\sum_{x\in\mathbb F_2^k}1_S(x)\prod_{a\in A}x_a=0.$

3. **Low-degree expansion.** For $k\ge3$ and any $f:\mathbb F_2^k\to\mathbb F_2$ satisfying these moments with $f$ in place of $1_S$, `moment_degree` supplies coefficients $q_A$ with $q_A=0$ whenever $|A|>k-3$ and

   $f(x)=\sum_{A\subseteq\mathrm{Fin}\,k}q_A\prod_{a\in A}(x_a+1).$

4. **Weight restrictions.** For any $k,f,q$ satisfying this displayed expansion and $q_A=0$ for $|A|>1$, `affine_weight` gives $\operatorname{wt}(f)=0$, $2\operatorname{wt}(f)=2^k$, or $\operatorname{wt}(f)=2^k$. For the same expansion with $q_A=0$ for $|A|>2$, `quadratic_polarization` makes $b(u,x)=f(x+u)+f(x)+f(u)+f(0)$ additive in $x$. For any $k,f$ with $b(u,x+y)=b(u,x)+b(u,y)$ for every $u,x,y$, `walsh_square` proves $2^k\mid W^2$, where $W$ is the integer sum with summand $1$ when $f(x)=0$ and $-1$ otherwise. When $k=5$ and the expansion has $q_A=0$ for $|A|>2$, `quadratic_weight` uses $32\mid W^2$, hence $8\mid W$, and $W=32-2\operatorname{wt}(f)$ to prove $4\mid\operatorname{wt}(f)$.

5. **Contradiction and induction.** For a finite set $S\subseteq\mathbb F_2^k$ with $k\le5$, $|S|\le14$, $2(k+1)<|S|$, even $|S|$, and all the degree-at-most-two moments above, `moments_obstruction` proves a contradiction. Under these hypotheses, $|S|\le2^k$ leaves only $k=4$ or $k=5$. At $k=4$ the affine alternatives are $0,8,16$, incompatible with $10<|S|\le14$; at $k=5$ evenness forces $|S|=14$, incompatible with divisibility by four. The column construction supplies precisely these hypotheses in `nondegenerate`, whose assumptions are self-orthogonality, parity, $N\le14$, $2r<N$, and the absence of every distinct pair $e_i+e_j$ from $C$. For arbitrary finite $I$ and self-orthogonal $C$ containing parity with $N\le14$ and $2r<N$, `general_result` combines this case with `remove_pair` by strong induction on $N$. `result` specializes the coordinate type to $\mathrm{Fin}\,n$.

## Falsifier

A counterexample to the formal statement would be an $n\le14$ and a self-orthogonal $C\le\mathbb F_2^n$ containing $\mathbf1$, with $2\dim C<n$, for which every $v\in C^\perp\setminus C$ has weight at least four. Degenerate stabilizer spaces are included in this quantifier.

The source correspondence uses exactly these identifications:

- `IsSelfOrthogonal` requires zero dot product for all pairs of vectors in $C$;
- `characterOrthogonalComplement (ZMod 2) C` is orthogonality for `standardCoordinatePairing`, which is the usual dot-product bilinear form;
- `hammingNorm` counts nonzero coordinates;
- parity membership is literal membership of the constant-one vector, and the logical-qubit condition is the strict inequality $2\dim C<n$.

The physical interpretation follows the source's stabilizer-bit-string convention; `result` is a theorem about binary subspaces, not a Hilbert-space construction or a hardware realization.

## Evidence

The canonical source is `D5/S3/Quantum/Codes/MajoranaFourteenModeDistanceFour.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Codes/MajoranaFourteenModeDistanceFour.lean.json`.

Declaration statements:

- `result`: `sha256:715adfebeff3aced873ddf1bbc079edd7098edc86aac0d03815c7c93203aab16`;
- `claim`: `sha256:574f22695a7bbe013153d0cc5bc9dec622ee587b7e2d40dea46280f8e9d296d4`.

## Triage

Tier 1 belief of a 2017 paper following a non-exhaustive numerical search, preregistered in issue #23984 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural number $n\le14$ and every self-orthogonal binary subspace $C\le\mathbb F_2^n$ containing the all-ones vector, if $2\dim C<n$, some vector of $C^\perp\setminus C$ has Hamming weight below four.

**Computed, not formalized:** none.

**Argued, not formalized.**

- *Mechanism.* Distinct columns alone do not resolve the fourteen-mode case: fourteen points fit in a five-dimensional binary cube. For $S\subseteq\mathbb F_2^k$ with $k\le5$, $|S|\le14$, $2(k+1)<|S|$, even $|S|$, and all degree-at-most-two moments zero, `moments_obstruction` excludes $S$. It is the joint moment constraint from commuting stabilizers that closes the gap left by syndrome counting.
- *Exact distance and range.* Under all hypotheses of `result`, its witness is nonzero because $0\in C$. Orthogonality to $\mathbf1\in C$ makes its weight even, so its weight below four must be two. Every other vector of $C^\perp\setminus C$ is likewise nonzero and even-weight, giving exact distance two. Self-orthogonality and parity also force even $n$, since $\mathbf1\cdot\mathbf1=n\bmod2$; this is the content of `parity_card` for a finite coordinate type and a self-orthogonal space containing $\mathbf1$. Consequently all admissible lengths below sixteen lie in the range of `result`.
- *Sharpness from the source's construction.* Index sixteen coordinates by $\mathbb F_2^4$ and span the constant-one function and the four coordinate functions, as in Hastings, Section II.B. Evaluation at zero and at the four unit vectors shows that these five generators are independent. Their weights are sixteen or eight, and intersections of distinct coordinate supports have size four, so the span is self-orthogonal and contains parity. The distinct columns exclude weight-two vectors from its orthogonal complement, and parity excludes odd weights. The indicator of a two-dimensional affine plane has weight four and is orthogonal to every generator, since the restriction of each coordinate function to the plane has weight zero, two or four. It is outside the span: a nonconstant affine function is balanced by translation along a direction where its linear part is one, so every nonzero function in the span has weight eight or sixteen. Thus this construction has distance four and $K=16/2-5=3$. Together with the exclusion below sixteen, it establishes sharpness in the source's binary stabilizer convention; the sixteen-mode construction is not formalized by `result`.
- *Effect on the paper and neighbouring questions.* The quoted minimum-mode belief is settled through its nonexistence half, with the source's explicit sixteen-mode construction supplying existence. The source's other numerical optimality claims, including the larger distance-four entries and the distance-six tables, do not follow from this result. Their optimality remains open here, as do extensions that remove the parity convention; no classification or uniqueness of sixteen-mode codes is established.

## ASSUMED-UNVERIFIED

The bounded literature check in #23984 does not establish exhaustive worldwide novelty or priority. Its web-search outcomes, arXiv-version enumeration, repository-search outcomes, and characterization of the three citing-preprint abstracts are not independently reproduced. No classical self-orthogonal-code classification excluding these parameters has been ruled out.

The Majorana-operator and Hilbert-space interpretation is taken from Hastings (2017), arXiv:1703.00612v1; it is not constructed in Lean here. The exact-distance and below-sixteen reformulations, the sixteen-mode sharpness construction, and the consequences discussed under “Argued, not formalized” are not additional conclusions stated by `result`. The source's random searches and numerical tables are not reproduced. Optimality at larger lengths, distance-six optimality, absence of the parity assumption, and classification or uniqueness at sixteen modes are outside this settlement.
