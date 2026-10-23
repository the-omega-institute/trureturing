---
slug: zhang-zhao-2024-speyer-g-uniform-normality
bibkey: zhangzhao2024speyer
doi: 10.1007/s10114-026-4502-5
url: https://arxiv.org/abs/2408.15506v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.result
---

# Normal limits for Speyer g-polynomials of growing uniform-matroid rank

## Problem

Rong Zhang and James Jing Yu Zhao, *Analytic properties of Speyer’s g-polynomial of uniform matroids*, arXiv:2408.15506v1, Conjecture 4.8:

> If $d=d(n)$ is a real function of $n$ such that $d(n)\to+\infty$ as $n\to+\infty$, then the coefficient of Speyer’s g-polynomial $g_{n,d(n)}(t)$, namely $S_i(n,d(n))$, is asymptotically normal by local and central limit theorems.

The source defines $g_{n,d}$ for integer ranks and uses the standing restriction $1\le d\le\lfloor n/2\rfloor$ after its rank-complement symmetry. The formal claim quantifies $d:\mathbb N\to\mathbb N$, imposes that restriction eventually, and assumes $d(n)\to\infty$. It does not extend the polynomial to arbitrary real-valued rank functions. Both limits are uniform in every real threshold and use the source's derivative-ratio mean and variance.

### Statement echo

| Source clause or convention | Lean counterpart | Scope |
| --- | --- | --- |
| Proposition 1.1 factorial sum | `SpeyerUniformNormality.g` | Natural subtraction occurs before casting, on the prescribed finite summation range. |
| Integer matroid rank under the standing half-rank restriction | `d : ℕ → ℕ` and eventual `1 ≤ d n ∧ d n ≤ n / 2` | The source's wording “real function” is interpreted within its integer rank domain; eventual validity allows arbitrary finitely many initial values. |
| Rank tends to positive infinity | `Tendsto d atTop atTop` | No monotonicity or growth-rate hypothesis is added. |
| Theorem 4.2 mean and variance | `BernoulliTriangularLimits.mu`, `sigmaSq`, `sigma` | The same derivative ratios and nonnegative square root. |
| Coefficient probability | `BernoulliTriangularLimits.prob` | Coefficient divided by evaluation at one, and zero at negative integer indices. |
| Standard normal distribution and density | `StatLean.HypothesisTesting.stdNormalCDF` and `stdNormalPDF` | Reused Gaussian owners inside `CLT` and `LLT`; `claim` is their conjunction for the Speyer polynomial sequence. Their integral and density correspondences are established inside the consuming proofs. |
| Central limit theorem, uniform over real thresholds | `BernoulliTriangularLimits.CLT` | The epsilon form uses the finite coefficient support. |
| Local limit theorem, with integer floor | `BernoulliTriangularLimits.LLT` | The epsilon form retains the literal integer floor. |
| Both limits | `SpeyerUniformNormality.result : claim` | The conclusion is their conjunction for every admissible divergent rank sequence. |

## Motivation

`D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.result` proves the registered conjecture in its integer-rank domain. The underlying probability estimates also apply to polynomial arrays whose normalized law is a one-step shift of a Bernoulli product and whose variance diverges.

## Gap

Preregistration [#15111](https://github.com/the-omega-institute/trureturing/issues/15111) identifies Conjecture 4.8 in arXiv:2408.15506v1 and records the source and literature screen. The screen found no settlement in its searched scope; it does not establish exhaustive absence. The journal article associated with DOI 10.1007/s10114-026-4502-5 has not been read in full for this delivery, so the persistence of the conjecture in that full text is ASSUMED-UNVERIFIED.

## Route

Write $a=d-1$, $b=n-d-1$, and $q(t)=g_{n,d}(t)/t$. The polynomial identity

$$q(t)=\sum_{j=0}^{a}\binom aj\binom bj(1+t)^j$$

is established by the private `SpeyerUniformNormality.g_eq_X_mul_q` and its coefficient identities. A Rodrigues identity, repeated Rolle, reflection and reversal establish that $q$ splits and has roots strictly below $-1$ (`q_splits_roots`). Normalizing these linear factors gives the shifted Bernoulli factorization in `g_bernoulli_factorization`.

For roots $-r_j$ with $r_j>1$, the variance estimate is

$$\sigma^2=\sum_j\frac{r_j}{(1+r_j)^2}\ge\frac14\sum_j\frac1{r_j}
=\frac{(d-1)(n-d-1)}{4(n-2)}\ge\frac{d-1}{8}.$$

The estimate is represented by `speyer_variance_eighth_unconditional`, with $2\le d$ and $2d\le n$. These bounds hold eventually for every sequence in the claim. `speyer_variance_tendsto` then supplies variance divergence.

The Fourier estimates control the centered Bernoulli characteristic function and its integrable Gaussian envelope. Lattice inversion and dominated convergence yield the uniform lattice limit, and `uniform_lattice_limit_to_floor` transfers it to the source's floor convention. The uniform CDF upgrade supplies the central limit. `bernoulli_polynomial_uniform_limits` assembles the two limits for the normalized product law, and `SpeyerUniformNormality.result` applies it to $g_{n,d(n)}$.

## Falsifier

The formal conclusion requires both uniform epsilon estimates for the literal coefficient law. A sequence with eventual integer half-rank admissibility and divergent rank that violates either estimate would refute the conjecture. Neither a bounded-rank sequence nor a numerical discrepancy outside the admissible domain meets these hypotheses.

## Evidence

The three modules are `UniformCDFConvergence`, `BernoulliTriangularLimits`, and `SpeyerUniformNormality`, under `D5/S3/Analytic/Probability/` and `D5/S3/Combinatorics/Matroids/`. Their proofs are checked by Lean; the axiom closure of each public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The experiment is [the pinned Speyer check](https://github.com/the-omega-institute/trureturing-experiments/tree/d99f6b428f727df85bcfdab18993c07c5f55c792/docs/reports/zhang-zhao-2024-speyer-g-polynomial-normality). Command: `python3 check.py 40` in that directory; exit 0; `check.py` SHA-256 `feb006d2479fcbb34f21df4ddb093c6fc053dde9fccb32f700570b709eab15d9`. It checks 361 pairs with $4\le n\le40$ and $2\le d\le\lfloor n/2\rfloor$: the coefficient identity and variance bound in exact arithmetic. Its Sturm test checks the root count and location for $n\le24$. The failed-check count is 0, and the smallest variance-to-bound ratio is 1.026844. These finite computations do not establish the asymptotic limits or sharpness of the bound.

The escape audit is unfinished under [#15743](https://github.com/the-omega-institute/trureturing/issues/15743). No Reg mirror is delivered; no validated four-slot registration is asserted. Missing evidence consists of source-specific arenas, observation/readout maps, exact source reconstruction and realization bridges, E1–E8, whole-family variation and sensitivity, and actual observational dependence. This boundary concerns escape registration and does not change the Lean statements.

## Triage

### What the settlement shows

- **Proved, kernel-checked mechanism:** `SpeyerUniformNormality.g_bernoulli_factorization` gives the normalized polynomial as $X$ times a product of Bernoulli probability-generating polynomials. The private `q_splits_roots` supplies real splitting and root location on its derivation path. `speyer_variance_eighth_unconditional` proves the bound $(d-1)/8$ for every $2\le d$ and $2d\le n$; `speyer_variance_tendsto` proves divergence for the claim's rank sequences. `BernoulliTriangularLimits.bernoulli_polynomial_uniform_limits` supplies both limits, and `SpeyerUniformNormality.result` proves their conjunction for Speyer polynomials.
- **Proved, kernel-checked scope:** `SpeyerUniformNormality.result` needs only eventual half-rank bounds and $d(n)\to\infty$. It assumes neither monotonicity nor a prescribed rate.
- **Source scope:** Section 4 of the read arXiv v1 text proves the balanced case $d=\lfloor n/2\rfloor$ in Theorem 4.1 and ends with the divergent-rank Conjecture 4.8. It makes no bounded-rank claim in that conjecture.
- **Open bounded-rank boundary:** bounded ranks lie outside the conjecture; their limiting laws are not settled in this delivery.
- **Open literature boundary:** the conjecture is present in the read arXiv v1 source. Its persistence in the unread 2026 journal full text is ASSUMED-UNVERIFIED; no exhaustive literature-absence assertion is made.
- **Computed finite check:** the pinned experiment covers exactly the 361 admissible pairs through $n=40$, and the root test covers only $n\le24$. No larger numerical scope is claimed.
- **Proved, kernel-checked extension:** `bernoulli_polynomial_uniform_limits` applies to any eventually normalized one-step shifted Bernoulli polynomial array with variance divergence. It does not assert the criterion for every possible polynomial family without that factorization hypothesis.
- **Open sharpness and neighbouring questions:** optimality of the constant $1/8$, bounded-rank limit laws, quantitative rates, and a general real-rooted polynomial criterion beyond the displayed factorization domain are not settled here.
- **Proved in prose, source consequence:** for $d(n)=\lfloor n/2\rfloor$, the half-rank conditions hold for $n\ge2$, and for any integer $K$, $n\ge2K$ implies $d(n)\ge K$. Hence this sequence satisfies the hypotheses of `SpeyerUniformNormality.result`, so the result includes the source's balanced-rank normality and extends its normal-limit conclusion to the registered divergent-rank domain. It supplies no new recurrence or interlacing conclusion.

## ASSUMED-UNVERIFIED

The journal full text has not been read, and its retention of Conjecture 4.8 is unverified. The recorded literature screen is bounded. Four-slot escape registration remains unfinished under #15743 and supplies no validated registration evidence. No unrestricted real-valued-rank extension is claimed.
