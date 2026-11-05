---
slug: evans-francis-jones-2025-katz-cutoff-limit
bibkey: evansfrancisjones2025katz
doi: 10.48550/arXiv.2509.02874
url: https://arxiv.org/abs/2509.02874v1
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/KatzCutoff/Result
---

# The Katz cut-off limit for path graphs

## Problem

Evans, Francis and Jones, *Katz similarity index comparisons*, arXiv:2509.02874v1, Conjecture 4:

> The cut-off values α_n converge to 1/√5 from above.

The source defines the Katz matrix by $K_{P_n}(\alpha)=(I-\alpha A_n)^{-1}-I$ and the cut-off values as roots of
$p_{n,1}(\alpha)=\min_i K_{i,i+1}-\max_i K_{i,i+2}$, with each extremum restricted to existing vertex pairs.
Theorem 19 locates a root between $1/\sqrt5$ and $1/2$ for every $n\ge6$.
The preregistration is [#20122](https://github.com/the-omega-institute/trureturing/issues/20122).

### Statement echo

| Source clause or convention | Lean counterpart | Scope |
| --- | --- | --- |
| The path $P_n$ and its adjacency matrix | `SimpleGraph.pathGraph n`, in `Reduction.katz` | Vertices are `Fin n`, indexed from zero. |
| $(I-\alpha A_n)^{-1}-I$ and its entries | `Reduction.katz`, `Reduction.katzEntry` | The matrix inverse is Mathlib's inverse. Out-of-range natural indices are extended by zero and excluded from both extrema. |
| The minimum for separation one and maximum for separation two | `Reduction.p1` | The ranges are `Fin (n-1)` and `Fin (n-2)`. |
| Theorem 19's existence | First conjunct of `Result.claim` | Every $n\ge6$ has a root in $(1/\sqrt5,1/2)$. |
| Convergence from above | Second conjunct of `Result.claim`, proved by `Result.result` | Every sequence choosing roots in $(0,1/2)$ for $n\ge6$ lies above $1/\sqrt5$ there and tends to it. The first six values are unrestricted. |

All abbreviated declaration names in this dossier have prefix `D5.S1.Recurrence.KatzCutoff.`.

## Motivation

The cut-off separates the Katz and resistance orderings of pairs of path vertices.
The universal root-selection statement establishes convergence without assuming the root sequence is monotone.
Its explicit existence conjunct supplies such choices for all relevant path sizes.

## Gap

The source's finite root-location theorem does not establish the limiting value.
The settling theorem proves existence and convergence for the literal matrix and finite-extremum definitions.
It does not assert a convergence rate.

## Route

Write $d_0=d_1=1$ and $d_{k+2}=d_{k+1}-\alpha^2d_k$, using Mathlib's `LinearRecurrence.mkSol` directly.
For $a=\lfloor n/2\rfloor$ and $b=\lfloor(n-1)/2\rfloor$, put
$R_n(\alpha)=\alpha d_{a-1}d_{b-1}/d_{a+b-1}$.
`ProductExtrema.path_inverse_entry` gives the finite path inverse entries;
`ProductExtrema.product_min` and `ProductExtrema.product_center` determine their relevant extrema.
`Reduction.p1_reduction` yields

$$p_{n,1}(\alpha)=\frac{\alpha d_{n-2}}{d_n}\bigl(1-R_n(\alpha)\bigr).$$

For $0<\alpha<1/2$ the prefactor is positive. The private lemma `Result.p1_zero_iff` therefore identifies roots with level-one crossings.
The positive continued-fraction recursion in `Monotone` proves `Monotone.RAB_strictMonoOn` and `Monotone.R_strict_succ`.
At $c=1/\sqrt5$, `ProductExtrema.RAB_lt_one_c` gives $R_n(c)<1$.
`ProductExtrema.RAB_half_gt_one_for_indices` supplies the opposite endpoint inequality.
Continuity and induction give a crossing in $(c,1/2)$.

With $s=\sqrt{1-4\alpha^2}$ and $t=(1-s)/(1+s)\in(0,1)$, the private lemma `Result.RAB_t` gives

$$R_n(\alpha)=\frac{\alpha}{s}\frac{(1-t^a)(1-t^b)}{1-t^{a+b}}.$$

Consequently, for each fixed $0<\alpha<1/2$, the private lemma `Result.R_limit` proves
$R_n(\alpha)\to\alpha/\sqrt{1-4\alpha^2}$.
For each fixed $c<\beta<1/2$, this limit exceeds one, so strict monotonicity traps every root below $\beta$ eventually.
`Result.result` concludes convergence to $c$ from above.

## Falsifier

The formal claim would fail if a path size $n\ge6$ lacked the specified root, or if a sequence of roots in $(0,1/2)$ failed the stated lower bound or convergence.
The Lean theorem concerns the literal Katz definition; a counterexample to a different scalar model would not refute it.
Finite numerical sampling alone cannot establish existence, uniqueness or convergence for unbounded $n$.

## Evidence

The settling GID is `D5/S1/Recurrence/KatzCutoff/Result.result`.
Its canonical module state record is `Golden/Frozen/state/D5/S1/Recurrence/KatzCutoff/Result.lean.json`.
The theorem's axiom closure is contained in $\{\mathtt{propext},\mathtt{Classical.choice},\mathtt{Quot.sound}\}$.
The Scribe attaches one `OpenProblemResolutionClaim` with outcome `Proved` to this declaration.

### Numerical scope

The independent definition-based calculation is published in
[the experiments repository at `f01c358ef1463e7dd02c2e2ec39e5d7e459b9729`](https://github.com/the-omega-institute/trureturing-experiments/tree/f01c358ef1463e7dd02c2e2ec39e5d7e459b9729/docs/reports/evans-francis-jones-2025-katz-cutoff-limit).
The script is `check.py`, SHA-256 `49abd3e7aa8754ac57e5fe8a2c55aadeb6a34c872afb4987126323b3693fca3e`.
The verified bytes were run with `python3 /tmp/op-efj2509/experiment-check.py`, exit 0.
It evaluates 30-digit matrix inverses on a 60-point grid and refines sign changes by bisection, for exactly $n=6,\ldots,30,36,40$.
It detects one root for each tested size, with positive gaps above $1/\sqrt5$ and decreasing roots across the tested sizes.
The gaps at $n=30$ and $n=40$ are approximately $1.7394\cdot10^{-7}$ and $1.4142\cdot10^{-9}$.
These are numerical readings on the stated grid, not exhaustive root certificates.

### Escape audit

The four-slot escape audit for the public theorem targets is unfinished under
[#20795](https://github.com/the-omega-institute/trureturing/issues/20795).
No valid Reg registration is retained or claimed.
The missing evidence is a source-faithful typed realization bridge and the associated whole-family variation, sensitivity and observational-dependence proofs.

## Triage

| Item | Status and evidence |
| --- | --- |
| Literal Katz matrix entries | Proved, kernel-checked: `ProductExtrema.path_inverse_entry`, used by `Reduction.p1_reduction`. |
| Reduction of the finite extrema to $1-R_n$ | Proved, kernel-checked: `Reduction.p1_reduction`. |
| Fixed-parameter geometric-power limit | Proved, kernel-checked: private `Result.R_limit`, on the path to `Result.result`; this is a fixed-$\alpha$ assertion, not uniform convergence in $\alpha$. |
| Parameter and size monotonicity | Proved, kernel-checked: `Monotone.RAB_strictMonoOn` and `Monotone.R_strict_succ`, using positive continued fractions. |
| Existence and Conjecture 4 | Proved, kernel-checked: `Result.result`, for every $n\ge6$ and every root-selecting sequence in the claim. |
| Root uniqueness and strict decrease | Proved in prose from the compiled crossing equivalence, parameter monotonicity, size monotonicity and the endpoint calculation below; these are not additional public Lean conclusions. |
| Convergence rate | Open: no asymptotic constant or uniform quantitative rate is proved. |
| Definition-based experiment | Computed: the experiment entry above, on exactly $n=6,\ldots,30,36,40$; exit 0 and the script SHA-256 are given there. |
| Four-slot registrations | Open: the missing evidence and all public theorem targets are listed in #20795. |
| Literature screen | The source version, title and author searches, the Hu–O'Connell tridiagonal-inverse reference and related papers are the literature readings recorded in #20122; completeness is `ASSUMED-UNVERIFIED`. |

### What the settlement shows

**Proved in this module.** The decisive limiting mechanism is the exact geometric-power factorization of $R_n$, together with its strict increase in $\alpha$.
The finite factors tend to one at every fixed $0<\alpha<1/2$; the level-one limiting crossing is $c=1/\sqrt5$.
`Result.result` proves that $c$ is approached strictly from above for every admissible root sequence.
**Proved in prose from the kernel-checked statements.** No larger constant is a uniform lower bound for all tail values of a root sequence: such a bound would contradict convergence.
Roots in $(0,1/2)$ are unique: `Result.p1_zero_iff` turns two roots into two level-one values of the strictly increasing function in `Monotone.RAB_strictMonoOn`, forcing equality.
For consecutive path sizes, `Monotone.R_strict_succ` makes the next crossing function greater than one at the preceding root; strict monotonicity and existence put the next root strictly below it.
These conclusions are consequences described here; the public statement of `Result.result` itself states existence, the lower bound and convergence.

**Proved in prose, endpoint calculation.** At $\alpha=1/2$ the inverse has entries $2(\min(i,j)+1)(n-\max(i,j))/(n+1)$. To verify it, fix a column: its entries are affine on each side of the diagonal, vanish at the two external boundary indices $-1$ and $n$, and applying the tridiagonal row $( -1/2,1,-1/2)$ gives zero away from the diagonal and one on it. Thus this matrix is a right inverse and hence the inverse. The minimum adjacent entry is $2(n-1)/(n+1)$, and the maximum separation-two entry is $2ab/(n+1)$, since $a+b=n-1$ and the product of two positive integers with this sum is largest when they differ by at most one. Therefore $p_{n,1}(1/2)=2(a+b-ab)/(n+1)<0$ for $n\ge6$: here $a\ge3$, $b\ge2$, and $(a-1)(b-1)>1$. The endpoint is not a root, completing uniqueness on $(0,1/2]$. This calculation is a prose proof, not an additional Lean theorem.

**Open boundary.** The geometric rate $\alpha_n-c\sim C((\sqrt5-1)/(\sqrt5+1))^{n/2}$ is not proved here.
The finite positive gaps above are computed evidence only; they do not establish an asymptotic constant or a uniform rate.

**Source consequences.** Theorem 19's existence statement for $j=1$ is included in the settling claim.
Conjecture 4 is established for the stated path cut-offs. No other source theorem or open question is asserted to be settled by this declaration, and no additional dependency consequence for the source's other results is proved here.

## ASSUMED-UNVERIFIED

Completeness of the literature screen is `ASSUMED-UNVERIFIED`.
The numerical experiment covers only its specified finite grid and path sizes.
The convergence-rate problem identified in Triage remains open in this delivery; the endpoint calculation is proved in prose only.
The four-slot escape registration is unfinished under #20795; this does not alter the kernel-checked statement or its axiom boundary.
