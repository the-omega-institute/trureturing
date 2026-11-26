---
slug: ta-hoang-nguyen-2026-ferrers-question-4-1
bibkey: tahoangnguyen2026ferrers
doi: null
url: https://arxiv.org/abs/2611.26962v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/HardCore/FerrersResultant.result
---

# Ta–Hoang–Nguyen Question 4.1 on Ferrers graph stability

## Problem

Question 4.1 asks which partitions $m=\lambda_1\ge\cdots\ge\lambda_n\ge1$
give a stable independence polynomial. The vertex classes are the rows and
columns, and row $i$ meets column $j$ exactly when $j\le\lambda_i$.
Stability in Definition 1.1 puts all roots in $\operatorname{Re}z\le0$.
[Question 4.1](https://arxiv.org/html/2611.26962v1#S4.Thmthm1)

### Statement echo

Lean uses $n=k+1$ and takes $m$ to be the zeroth row length. Antitonicity
and pointwise positivity supply the partition bounds. The graph is a
Mathlib simple graph on $\mathrm{Fin}(n)\oplus\mathrm{Fin}(m)$. Its native
independence polynomial is taken over the full vertex set.

## Motivation

Lemma 3.2 gives a formula for the independence polynomial. Theorem 3.5
establishes strict stability for well-covered Ferrers graphs. The coefficient
criterion gives a finite test across the complete quantified family.
[Versioned paper](https://arxiv.org/abs/2611.26962v1)

## Gap

The source asks for an exact classification at every permitted partition.
The preregistration records the scope and the bounded literature search.
Composed addition supplies the pair-sum construction over the roots.
[#34459](https://github.com/the-omega-institute/trureturing/issues/34459)
· [Composed addition](https://doi.org/10.1016/0012-365X(87)90135-X)

## Route

With one-based indices set $e_i=(n-i)+(m-\lambda_i)$. The actual
polynomial is $p(X)=(1+X)^m+X\sum_i(1+X)^{e_i}$. For $j\ge0$ there are
$\binom m{j+1}+\sum_i\binom{e_i}{j}$ independent sets of size $j+1$.
Its degree is $d=\max(m,\max_i(e_i+1))$ and its leading coefficient $a$
is positive.

Compute $r(T)=\operatorname{Res}_Y(p(Y),p(T-Y))$ over the integers using
degree $d$ for both arguments. Its degree is $d^2$ and its leading
coefficient is $a^{2d}$. The necessary and sufficient test is
$[T^j]r\ge0$ for every $0\le j\le d^2$. The product formula for the
resultant gives all ordered pair sums of roots, including repeated roots.
If $p$ is closed stable, real linear factors and conjugate quadratic
factors of $r$ give the coefficient signs. Conversely, a root with positive
real part would produce a positive real root of $r$ by pairing it with its
conjugate. The leading coefficient and the scan exclude such a root.

The empty independent set gives $p(0)=1$. Once the scan passes, $r(0)=0$
is equivalent to a root of $p$ on the imaginary axis. Two roots whose
sum is zero must then each have real part zero. A root on the imaginary
axis and its conjugate provide the converse.

## Falsifier

A partition with a positive-real-part independence root and a passing
coefficient scan, or a closed-stable partition whose scan fails, would
contradict the main equivalence. An imaginary-axis root with $r(0)>0$
after a passing scan would contradict the boundary equivalence.

## Evidence

FerrersResultant.result proves the universal claim over the actual graph.
FerrersGraphCount.independencePolynomial_ferrers proves the partition
formula and PairSumStability.eval2_sumResultant_eq_zero_iff proves the
pair-sum root correspondence. The typed resolution is Proved.

## Triage

- **Kernel-checked.** FerrersResultant.result proves actual enumeration,
  the finite integer test in both directions, degree and leading coefficient,
  and the origin and imaginary-axis statements for all permitted partitions.
- **Kernel-checked.** PairSumStability.eval2_sumResultant_eq_zero_iff gives
  the pair-sum root correspondence. The proof uses Mathlib's root multiset
  and resultant product formula, which retain repeated roots.

## ASSUMED-UNVERIFIED

Priority for the coefficient test or this Ferrers application is undetermined.
