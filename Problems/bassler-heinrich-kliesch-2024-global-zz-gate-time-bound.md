---
slug: bassler-heinrich-kliesch-2024-global-zz-gate-time-bound
bibkey: basslerheinrichkliesch2024gzz
doi: 10.22331/q-2024-03-13-1279
url: https://arxiv.org/abs/2307.11160v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Optimization/GlobalZZGateTimeBound.result
---

# Global ZZ gates admit schedules within the parity bound

## Problem

P. Baßler, M. Heinrich and M. Kliesch, *Time-optimal multi-qubit gates: Complexity, efficient heuristic and gate-time bounds*, arXiv:2307.11160v2 [quant-ph]; Quantum 8, 1279 (2024), Conjecture 16 (`conj:gate-time`), TeX source `J_shaping.tex`, lines 919–927:

> The optimal gate time of $\operatorname{\mathsf{GZZ}}(A)$ with $A \in \mathrm{Sym}_0 (\mathbb{R}^n)$ is tightly upper bounded by
>
> $\vec 1^T \vec \lambda^* \leq \|M\|_{\ell_\infty} \cdot \begin{cases} n\,, &\text{for odd } n\,,\\ n-1\,, &\text{for even } n\,. \end{cases}$

The wording and equation are quoted from the downloaded v2 source (`J_shaping.tex`, md5 `3c751c31a7a40505b6013390b841878a`); its macros for the gate, $\mathrm{Sym}_0$, $\mathbb R$ and the norm are expanded for rendering. The source also states, at line 349:

> Unfortunately, we were not able to prove this result and state the challenges in \cref{app:proof_problems}.

Here $\mathrm{Sym}_0(\mathbb R^n)$ consists of real symmetric matrices with zero diagonal (line 240). The effective coupling is $M=A\oslash J$, with $M_{ij}=A_{ij}/J_{ij}$ when $i\ne j$ and $J_{ij}\ne0$, and zero otherwise; the physical interpretation assumes $\operatorname{nz}(A)\subseteq\operatorname{nz}(J)$ (lines 250–263). The source's LP minimizes $T=\sum_m\lambda_m$ over $\lambda_m\ge0$ with

$M_{ij}=\sum_{m\in\{-1,+1\}^n,\ m_n=+1}\lambda_m m_i m_j\quad(i<j)$.

Only strictly upper triangular entries enter these constraints (lines 265–291 and 355–362). The norm is $d=\max_{i<j}|M_{ij}|$ (line 448).

Issue [#21288](https://github.com/the-omega-institute/trureturing/issues/21288) fixes the settlement: for every $n\ge2$ and every such $M$, there is a feasible schedule with $T\le Kd$, where $K=n$ for odd $n$ and $K=n-1$ for even $n$. This existence statement is proved. The passage to an optimal LP value and the sharpness argument are distinguished below.

## Motivation

The bound controls the entangling time needed to synthesize a global ZZ gate from the physical coupling matrix $J$. It replaces the source's $\ell_1$ upper estimate by a bound depending on the largest effective coupling and a linear factor in the number of qubits. This improves that estimate when $Kd<\sum_{i<j}|M_{ij}|$, while retaining a separate bound suited to sparse matrices. Hardware dependence remains in $d=\|A\oslash J\|_{\ell_\infty}$.

## Gap

The bounded literature check recorded in #21288 comprises:

- the orchestrator's reading of the v2 source, which retains the conjecture and proves an extremal-family result separately;
- the search seat's check of OpenAlex W4392775620, reporting three citations, and the Quantum citation list, with no settlement of the uniform $\ell_\infty$ bound found;
- the search seat's report of no MathDB or google-deepmind/formal-conjectures entry, and the orchestrator's report of no existing repository issue, module or dossier at preregistration.
- the orchestrator's reading of the citing work arXiv:2512.11619v2 (TeX `main.tex`, md5 `154e3475b61b2328a9a061ba3d09dcc0`). Line 104 states that the conjectured bound "is actually not optimal", that the paper provides "a counter-example", and that it proves $\lVert t_\text{opt}\rVert_1\le T\sqrt3\,\lVert h_\text{P}\oslash h_\text{S}\rVert_2$ (Theorem `thm:Thm1`, l. 113–119); l. 170 calls this an answer to the open question. The text (240 lines) exhibits no coupling matrix whose LP optimum exceeds $K\,d$. The two bounds are incomparable. When every $|M_{ij}|=d$, the $2$-norm bound is $\sqrt{3n(n-1)/2}\,d$, which equals $K\,d$ at $n=3$ and exceeds it for every other $n\ge2$. For a matrix supported on one triangle it is $3d$, which is below $K\,d$ for $n\ge5$. Within the conjecture's model, `result` rules out any matrix whose optimum exceeds $K\,d$.

`not-found-in-searched-scope`. These attributed search findings are not an exhaustive literature census.

## Route

Write $\sigma_i(s)=(-1)^{s_i}$ for a Boolean sign assignment, and $K=n-1$ for even $n$, $K=n$ for odd $n$.

1. **Partition the pairs.** For every natural $n\ge2$, `round_robin_partition` partitions every pair $i<j$ into exactly one of $K$ matchings. Here `IsMatching R` requires every edge $(i,j)\in R$ to satisfy $i<j$ and distinct edges to have disjoint endpoint sets. For odd $n$, vertices and colors are identified with $\mathbb Z/n\mathbb Z$, and an edge has color $x+y$. For even $n$, the vertices are an extra point and $\mathbb Z/(n-1)\mathbb Z$; colors are $x+y$ on finite pairs and $2x$ on pairs containing the extra point. The odd modulus makes doubling injective in the even-$n$ construction.
2. **Realize one matching.** For any natural $n$, any `IsMatching R`, and any real coefficients $c_{ij}$ satisfying $|c_{ij}|\le1$ for every $i<j$, `matching_law` supplies a nonnegative probability law with pair moment $c_{ij}$ when $(i,j)\in R$ and zero otherwise, for every $i<j$. Its weights are $p_R(s)=2^{-n}\prod_{(i,j)\in R}(1+c_{ij}\sigma_i(s)\sigma_j(s))$. The absent-pair cancellation in `matchingWeight_pair_zero` requires `IsMatching R`, $i<j$ and $(i,j)\notin R$; it applies also when one or both vertices are unmatched.
3. **Fix the final sign.** For $n\ge2$ and any nonnegative real weight function $p$ on all Boolean assignments, `fold_law` supplies weights on `SignVec n`, preserving total mass and every pair moment. No normalization of $p$ is assumed. Complementing all bits when the final bit is true fixes the final sign to $+1$ and preserves sign products.
4. **Assemble the schedule.** For $n\ge2$, any real matrix $M$, and $K$ matchings covering each $i<j$ exactly once, `assemble_schedule` gives feasibility and the bound $T\le\operatorname{gateBound}(n)\operatorname{offDiagSup}(M)$. The lemmas `offDiagSup_nonneg` and `entry_le_offDiagSup` give $d\ge0$ and $|M_{ij}|\le d$ for $i<j$, without symmetry assumptions. If $d=0$, the zero schedule is used. If $d>0$, take $c_{ij}=M_{ij}/d$, scale the sum of the matching laws by $d$, and apply `fold_law`. `result` applies this construction to every symmetric zero-diagonal $M$ in `claim`.

## Falsifier

The proof would not settle the registered statement if its sign convention, feasible schedules or norm differed from the source's. The definitions make these correspondences explicit:

- `SignVec n` is a Boolean function whose final coordinate is false, representing the real sign $+1$; Boolean true represents $-1$.
- `IsFeasible M lam` requires all weights to be nonnegative and reproduces exactly the entries $M_{ij}$ for $i<j$. It does not impose equality on the diagonal of a sum of sign outer products.
- `offDiagSup M` is the finite maximum of zero and the absolute strictly upper triangular entries. The extra zero ensures a nonempty maximum; for $n\ge2$ it equals the source's $d$.
- `gateBound n` casts the natural number $n-1$ for even $n$, or $n$ for odd $n$, to $\mathbb R$.

`claim` requires $n\ge2$, symmetry and zero diagonal. It includes the zero matrix, but makes no assertion at $n=0$ or $n=1$. It asserts existence of a bounded feasible schedule, without defining an infimum or an optimal schedule.

## Evidence

The canonical source is `D5/S3/Quantum/Optimization/GlobalZZGateTimeBound.lean` (468 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** `#print axioms D5.S3.Quantum.Optimization.GlobalZZGateTimeBound.result` reports only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom. The source scan for those constructs has no matches.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Optimization/GlobalZZGateTimeBound.lean.json`, statement `sha256:8caf5713ca74033973f649e3890a1f5602b738c6c8315bbdfcdaa09d8a54c85c`.

Declaration statements:

- `result`: `sha256:8a158b21e19d8015eb9bbbed0023df060fe52767242047a037c3f9213e4f1281`;
- `claim`: `sha256:c2c702517616135b7b9c5e3703d931a6c0114fb77aa99ea91c0665367f8a7d15`.

## Triage

Tier 1 conjecture of a 2024 journal paper, preregistered in issue #21288 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $n\ge2$ and every real symmetric $n\times n$ matrix $M$ with zero diagonal, there are nonnegative weights on sign vectors with final sign $+1$ that reproduce every $M_{ij}$ for $i<j$, with total weight at most $\operatorname{gateBound}(n)\operatorname{offDiagSup}(M)$.

**Argued, not formalized.**

- *Decisive mechanism and extension.* For a matching with $|c_{ij}|\le1$ on every $i<j$, the law in `matching_law` realizes all its desired correlations simultaneously and cancels every other pair. Consequently, for $n\ge2$ and a symmetric zero-diagonal $M$ whose nonzero upper entries are partitioned into $q$ matchings, the same construction gives time at most $qd$: in each matching use $c_{ij}=M_{ij}/d$ when $d>0$, multiply its law by $d$, sum the $q$ laws and fold using `fold_law`. Each nonzero pair occurs once, every other contribution is zero, and each law has mass one. When $d=0$, use zero weights. This $q$-dependent conclusion is not stated by `result`; optimizing the matching decomposition and obtaining small encoding support are separate questions.
- *Optimal LP interpretation.* A feasible schedule supplied by `result` makes the finite-dimensional LP nonempty. If its total weight is $T_0$, restrict to feasible schedules of total weight at most $T_0$. This is a nonempty closed set with every coordinate in $[0,T_0]$, hence compact. The continuous total-weight objective attains a minimum there; schedules outside it cannot improve that minimum. Thus an LP optimum exists and is at most $Kd$. Neither optimum attainment nor an optimum-valued function is formalized in this module.
- *Sharpness.* Fix $n\ge2$, $C\ge0$ and $u\in\{-1,+1\}^n$, and put $M_{ij}=-Cu_i u_j$ for $i<j$, with symmetric completion and zero diagonal. For any sign assignment $m$, put $t_i=u_i m_i$. The identity $\sum_{i<j}t_it_j=((\sum_i t_i)^2-n)/2$ gives $\sum_{i<j}t_it_j\ge-\lfloor n/2\rfloor$, since the sum of $n$ signs is odd for odd $n$. Multiplying by feasible nonnegative weights and summing yields $-C\binom n2\ge-\lfloor n/2\rfloor T$, so $T\ge C\binom n2/\lfloor n/2\rfloor=CK$. Here $d=C$, so the upper bound is attained. This argument agrees with Baßler, Heinrich and Kliesch (2024), arXiv:2307.11160v2, Theorem `prop:worst_case_sol`, lines 1121–1130; that sharpness theorem is cited, not formalized here. Whether this family exhausts all extremizers is not settled by `result`.
- *Effect on the paper.* The conjectured upper bound used as the benchmark in Figure `fig:eff_GZZ` (lines 1193–1208) has a uniform schedule-existence proof, and the preceding sharpness argument identifies its worst-case constant. The global optimization objective discussed in `eq:upper_bound_LP` and Appendix `app:proof_problems` also has value $K$: for any $y$ with $V^Ty\le\mathbf1$, choose a symmetric zero-diagonal $M$ with upper entries $\operatorname{sign}(y_{ij})$. Its bounded schedule gives $\|y\|_1=\langle M,y\rangle=\lambda^TV^Ty\le T\le K$. Conversely, $y_{ij}=-1/\lfloor n/2\rfloor$ is feasible by the sign-sum inequality above and has $\ell_1$ norm $K$. This deduction does not establish the appendix's proposed invexity conditions. The module supplies no guarantee for the paper's restricted heuristic LPs, no efficient exact optimizer and no physical error or pulse-overhead analysis. The estimate gives a uniform $O(n)$ bound when $\|A\oslash J_n\|_{\ell_\infty}$ is uniformly bounded; source line 934 explicitly notes this hardware dependence.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The preregistration's search-seat readings of the arXiv version history, OpenAlex citation count, Quantum citing works (arXiv:2410.19903v3, 2511.11404v3 and 2512.11619v2), MathDB and google-deepmind/formal-conjectures were not independently reproduced. Neither was the orchestrator's repository-absence search at preregistration. The search seat's reported rational checks for $n=2,\dots,9$ in #21288 were not reproduced; their original scripts were not read.

All deductions under “Argued, not formalized” are outside the type of `result`. In particular, optimum attainment, sharpness, the $q$-matching extension, the dual-objective conclusion, extremizer classification, efficient synthesis and the physical interpretation are not formalized by this module. The source's numerical LP studies and heuristic benchmarks were read as source reports, not reproduced. The correspondence from physical gates to the LP assumes the source's support condition and physical model.
