---
slug: ayyer-mallick-2010-annihilation-maximal-degeneracy
bibkey: ayyermallick2010annihilation
doi: 10.1088/1751-8113/43/4/045003
url: https://arxiv.org/abs/0910.0693v2
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation.result
---

# Ayyer–Mallick maximal degeneracy of the annihilation-process generator

## Problem

A. Ayyer and K. Mallick, *Exact results for an asymmetric annihilation process
with open boundaries*, J. Phys. A 43, 045003 (2010), arXiv:0910.0693v2,
after Eq. (79), p. 14:

> We also conjecture that the Markov matrices are maximally undiagonalizable in
> the sense that each eigenvalue seems to have exactly one eigenvector independent
> of the number of times the eigenvalue appears (this implies that the Jordan
> blocks are of the maximum possible size). In other words, the degeneracy seems
> to be so strong that the Markov matrix M_L which is of size 2^L has only 2L
> eigenvectors.

A. Ayyer and V. Strehl, *The spectrum of an asymmetric annihilation process*,
arXiv:1008.2134v1, FPSAC 2010, DMTCS Proc. AN, 461–472,
DOI 10.46298/dmtcs.2884, Conjecture 1, p. 466:

> The matrix M_L is maximally degenerate in the sense that it has exactly 2L
> eigenvectors.

The model has $L$ Boolean sites, bulk transitions $10\to01$ and $11\to00$
at rate $1$, a symmetric left-site flip at rate $\alpha$, and right-site
removal at rate $\beta$. This is the papers' specialization $\lambda=1$.
The matrix entry $M_L(t,s)$ is the rate from $s$ to $t$ off the diagonal;
each diagonal entry is the negative sum of the other entries in its column.

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| $L$ sites, empty or occupied | `Fin L → Bool` | `true` denotes a particle; index $0$ is site $1$. |
| $10\to01$, $11\to00$, rate $1$ | `bulkMove`, `bulkCount` | Clear the occupied site and toggle its right neighbour; sum over all bonds. |
| Left-site $0\leftrightarrow1$, rate $\alpha$ | `leftCount`, `offRate` | Both directions have the same rate at $\lambda=1$. |
| Right-site $1\to0$, rate $\beta$ | `rightCount`, `offRate` | Removal requires an occupied last site. |
| Target-row/source-column matrix, columns sum to zero | `genMat` | Diagonal is the negative sum of all off-diagonal outgoing rates. |
| One independent eigenvector at each eigenvalue | `claim` | Every $L\ge1$, positive real $\alpha,\beta$, and real $\mu$ has $\dim\ker(M_L-\mu I)\le1$. |
| Negative answer | `result : ¬ claim` | $L=5$, $\alpha=1/3$, $\beta=2/5$, $\mu=-2$. |

The source assertion includes eigenvalues without restricting their scalar
field. A two-dimensional real eigenspace already refutes it. Quantifying over
all real $\mu$ also includes numbers outside the spectrum, whose kernels have
dimension zero. The definitions at $L=0$ are total extensions; `claim` requires
$L\ge1$. The extension of `bulkMove` to coinciding indices is never used by a
bulk transition. None of these conventions weakens the counterexample.

## Motivation

The settling declaration is
`D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation.result`.
It refutes the geometric-multiplicity conjecture using positive rates and a
real eigenvalue. The source's characteristic-polynomial theorem concerns
algebraic multiplicity, which does not determine the number of eigenvectors.

## Gap

Preregistration [#16707](https://github.com/the-omega-institute/trureturing/issues/16707)
classifies the published conjecture as Tier 1 and records source and literature
checks. The Ayyer–Strehl paper proves its characteristic-polynomial result but
explicitly leaves Conjecture 1 unexplained. The citation screen reported in
that issue found no settlement in the checked works. These source and citation
readings are orchestrator-reported; they do not prove literature completeness.

## Route

The proof constructs two integer-valued functions on the $32$ configurations.
For prefix signs $\xi_i(s)=\prod_{k<i}(1-2s_k)$ in zero-based indexing, they are

$$
v_1=\xi_1\xi_2-3\xi_2+9\xi_1-5,
$$

$$
v_2=\xi_1\xi_4-\xi_2\xi_3-3\xi_4+9\xi_3-27\xi_2+81\xi_1-40.
$$

Exact rational evaluation proves that both lie in the left kernel of
$M_5+2I$. Casting transfers the equalities to the real matrix. At the empty
state their values are $(2,20)$; at the state occupied only at index $3$ they
are $(2,24)$. The determinant of this evaluation minor is $8$, so they are
independent. Rank equality with the transpose and rank–nullity transfer the
left-nullity bound to the right eigenspace. These are the mathematical steps
in the proof of `result`; the uniform family below is a separate prose proof.

## Falsifier

The settled claim is the literal geometric-multiplicity statement of #16707.
The kernel-checked negation has no additional hypotheses. The witness satisfies
$L\ge1$, $\alpha>0$, and $\beta>0$, with $\dim\ker(M_5+2I)\ge2$.
Changing the transition rates, matrix orientation or source claim would change
the question. The result does not assert an exact multiplicity or a general
classification of Jordan blocks.

## Evidence

**Kernel-checked.** `AnnihilationMaximalDegeneracyRefutation.result` proves
$\neg\mathrm{claim}$. Its consumed private proof components `qkernel1`,
`qkernel2`, `vectors_independent`, `left_nullity`, and `right_nullity` establish
the two-vector witness and the lower bound at the stated parameters. The axiom
closure of every public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

**Experiment.** [Pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/96a48410fbb456cb48cf2881370f6dbcb098f449/docs/reports/ayyer-mallick-2010-annihilation-maximal-degeneracy)
contains `check.py`, SHA-256
`9e1372b44346fc2fd3b639eb16745510836ba3b1a7c691371569f88b853d13d0`.
The commands
`python3 /Users/auric/trureturing-experiments/docs/reports/ayyer-mallick-2010-annihilation-maximal-degeneracy/check.py`
and the same command with `--exact-totals` both return exit $0$, `ALL_OK`.
The local script bytes equal the script at the cited commit.

At each $(\alpha,\beta)\in\{(1/3,2/5),(2/3,7/4),(3/8,5/6)\}$, the default
run checks exact rational eigenfunction equations and independence for
$L=5,6,7$, and checks that $-2$ is distinct from the other roots in Theorem 4.
The `--exact-totals` run computes rational ranks at every root for $L=4,5,6,7,8$:

| $L$ | $\dim\ker(M_L+2I)$ | Total eigenspace dimension | $2L$ |
| --- | --- | --- | --- |
| $4$ | $1$ | $8$ | $8$ |
| $5$ | $2$ | $12$ | $10$ |
| $6$ | $2$ | $16$ | $12$ |
| $7$ | $3$ | $26$ | $14$ |
| $8$ | $3$ | $40$ | $16$ |

These readings have exactly the listed lengths and three parameter pairs.
Float SVD totals at $L=7,8$ overcount near large Jordan blocks and are not used
as exact multiplicities. The float control at $\alpha=1/2$ does not settle the
resonant case.

## Triage

### What the settlement shows

**Kernel-checked at the witness: the mechanism.** Two independent left
eigenvectors at $-2$ exist for $L=5$, $\alpha=1/3$, $\beta=2/5$; the consumed
private declarations named in Evidence establish this within the proof of
`result`. The vectors are quadratic polynomials in prefix signs. The
two-dimensional eigenspace prevents one Jordan block from accounting for
this eigenvalue. The general Walsh-action identities in the following
paragraph are proved in prose, not formalized in this module.

**Proved in prose: the uniform family.** For $L\ge5$, $\alpha>0$,
$\alpha\ne1/2$, and $\beta>0$, set $\delta=1-2\alpha$ and
$\xi_i(\eta)=\prod_{k=1}^i(1-2\eta_k)$, with $\xi_0=1$.
For $i<L$, the backward generator $G=M_L^T$ satisfies

$$
G\xi_i=-(1+2\alpha)\xi_i+\xi_{i-1}.
$$

The left flip changes the sign, contributing $-2\alpha\xi_i$.
Only the bulk bond $i$ changes the prefix product; its contribution is
$-2\eta_i\xi_i=-\xi_i+\xi_{i-1}$. Right-boundary removal has no effect
for $i<L$. For $1\le i<j<L$, the left flip changes both signs and cancels;
only bonds $i$ and $j$ contribute, giving

$$
G(\xi_i\xi_j)=-2\xi_i\xi_j+\xi_{i-1}\xi_j+\xi_i\xi_{j-1}.
$$

For $1\le r\le\lfloor(L-1)/2\rfloor$, define

$$
g_r=\sum_{j=1}^{r}(-1)^{j-1}\xi_j\xi_{2r+1-j},\qquad
h_r=\sum_{k=1}^{2r}(-1)^k\delta^{2r-k}\xi_{2r+1-k}.
$$

The adjacent terms telescope, using $\xi_i^2=1$:

$$
(G+2)g_r=\xi_{2r}+(-1)^{r-1},\qquad
(G+2)h_r=1-\delta^{2r}\xi_{2r}.
$$

Thus

$$
P_r=2\delta^{2r}g_r+2h_r+(-1)^r\delta^{2r}-1
\quad\text{satisfies}\quad (G+2)P_r=0.
$$

The prefix-sign transformation is a bijection of the Boolean cube: each
original sign is $\xi_{i-1}\xi_i$. Its distinct Walsh monomials are linearly
independent. The monomial $\xi_1\xi_{2r}$ occurs in $P_r$ with nonzero
coefficient $2\delta^{2r}$ and in no other $P_s$, proving independence.
Transpose-rank equality then gives
$\dim\ker(M_L+2I)\ge\lfloor(L-1)/2\rfloor$.
At $\alpha=1/3$, the formal vectors are $v_1=(9/2)P_1$ and
$v_2=(81/2)P_2$. This uniform argument is not a Lean theorem in the delivery.

**Computed: sampled family and exact totals.** The experiment entry verifies
the $P_r$ equations and their ranks for $L=5,6,7$ at the three listed rate
pairs, and computes the exact totals $8,12,16,26,40$ for $L=4,\ldots,8$ at
each pair. These totals exceed $2L$ from $L=5$ in this tested scope.

**Literature result: what survives.** Ayyer–Strehl Theorem 4 proves the
characteristic polynomial independently of Conjecture 1. Its eigenvalues and
algebraic multiplicities are unaffected by this geometric-multiplicity
refutation. Neither paper's proved eigenvalue or stationary-state results
are refuted by this witness.

**Computed: the length-four special case.** At $L=4$ and each of the three
listed rate pairs, all $8$ distinct roots have geometric multiplicity $1$.
The conjecture holds at those instances. A uniform statement over all
positive rates at $L=4$ is open here; the finite computation is not that
statement.

**Open: remaining degeneracy questions.** The resonant case $\alpha=1/2$
has $\delta=0$ and the displayed independence argument does not apply.
Exact geometric multiplicities of all eigenvalues for general $L$, including
colliding roots, remain open here. The lower-bound family does not supply
an exact classification.

**Literature reading.** Strehl's 2020 Sém. Lothar. Combin. B81a concerns
eigenvalues and partition functions, not an eigenvector-count settlement;
this is a reported literature reading from the source checks accompanying
#16707. The subscription chapter DOI 10.1007/978-3-030-44559-1_17 is unread.
No settlement was found in the checked scope; completeness is
`ASSUMED-UNVERIFIED`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`, including the unread
subscription chapter. The source and citation screen is attributed to the
orchestrator in #16707. The uniform family is proved in prose above and is
not kernel-checked. The exact-total computation settles only its stated
lengths and rate pairs. General multiplicities and the resonant case are open.
