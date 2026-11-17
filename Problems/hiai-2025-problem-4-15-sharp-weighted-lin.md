---
slug: hiai-2025-problem-4-15-sharp-weighted-lin
bibkey: hiai2025quasiarithmetic
doi: null
url: https://arxiv.org/abs/2508.20309
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/SharpWeightedLin/Settlement.result
---

# Sharp weighted Lin comparison at Hiai's endpoint

## Problem

Fumio Hiai, *Various inequalities between quasi-arithmetic mean and
quasi-geometric type means for matrices*, arXiv:2508.20309v2 (2025-09-25),
Section 4.3, Problem 4.15, asks:

> There is a gap between the sufficient condition and the necessary condition for Rα,p ≤λ Aα,q , Rα,p ≺w Aα,q and Rα,p ≤Tr Aα,q . It is also unknown whether Rα,p ≤λ Aα,q is strictly stronger than Rα,p ≺w Aα,q , or they are equivalent.

For $0<\alpha<1$, $p,q>0$, and positive definite matrices, write

$$
R_{\alpha,p}(A,B)=\left(A^{(1-\alpha)p/2}B^{\alpha p}
A^{(1-\alpha)p/2}\right)^{1/p},
\qquad
\mathcal A_{\alpha,q}(A,B)=\left((1-\alpha)A^q+\alpha B^q\right)^{1/q}.
$$

The symbol $\le_\lambda$ compares every descending eigenvalue,
$\prec_w$ is weak majorization of the descending eigenvalue vectors, and
$\le_{\rm Tr}$ is the trace comparison.

## Motivation

The question asks whether the sufficient and necessary exponent ranges can be
made sharp. The endpoint $q=\alpha(1-\alpha)p$ is the smallest exponent
allowed by the universal eigenvalue comparison and is therefore the relevant
weighted Lin endpoint.

## Gap

Preregistration: [#31169](https://github.com/the-omega-institute/trureturing/issues/31169).
The source gives Proposition 4.9 ($p/2\le q$ implies the eigenvalue
comparison), Theorem 4.10 (the eigenvalue comparison on every positive definite
$2\times2$ pair implies
$\alpha(1-\alpha)p\le q$), Proposition 4.11 (the trace comparison follows
from $\min\{1,p/2\}\le q$), and Theorem 4.12 (the universal trace comparison
implies $\min\{1,\alpha(1-\alpha)p\}\le q$). The source also gives Example
4.13: for $\alpha=1/2$, $p=1$, the trace comparison is equivalent to
$q\ge1/4$.

## Route

Set $a=1-\alpha$ and $b=\alpha$. The proof of Sra's Theorem 1.1 uses an
inertia identity to reduce the endpoint to a scalar spectral-measure estimate.
The only scalar change needed for arbitrary weights is

$$
 x^{a/b}(1-ax)\le b,
 \qquad x\ge0,\quad ax<1,
$$

with equality at $x=1$. Its exponent is the sharp value $2ab$ after the
Gram/singular-value square-root normalization. The finite spectral measure
bound, compression Birman–Schwinger nonpositivity, endpoint count, and
homogenization then give the endpoint inequality. At $t=1/2$, this recovers
the Sra/Drury midpoint argument.

## Falsifier

A test is outside the settled statement if the weights are outside $0<\alpha<1$,
if $p\le0$, if the matrices are not positive definite, if the comparison is
entrywise rather than by descending eigenvalues, or if the endpoint exponent is
changed from $\alpha(1-\alpha)p$. The source also
contains singular positive semidefinite inputs; the Lean theorem addresses
positive definite inputs, and the singular extension is recorded separately.

## Evidence

**Proved in Lean:** `D5/S3/Quantum/Matrix/SharpWeightedLin/Settlement.result`
proves, for every $n$, every $0<\alpha<1$, $p>0$, and
$q\ge\alpha(1-\alpha)p$, every positive definite complex pair $A,B$, and
every descending index $j$,

$$
\lambda_j(R_{\alpha,p}(A,B))
\le \lambda_j(\mathcal A_{\alpha,q}(A,B)).
$$

The formal means are the definitions `hiaiRMean` and
`hiaiArithmeticMean`; their positive-semidefinite wrappers supply the
Hermitian eigenvalue representatives.

**Proved in the source, not formalized:** Sra's Theorem 1.1 proves the family
$\sigma_j(A^{(1-t)/q}B^{t/q})^q\le\lambda_j((1-t)A+tB)$ for all
$0\le t\le1$ and $q\ge1/2$. Hiai's Proposition 4.9 proves the sufficient
condition $p/2\le q$ for the eigenvalue comparison. Hiai's Proposition 4.11
proves the sufficient trace condition $\min\{1,p/2\}\le q$.

**Derived on paper, not formalized:** The Lean endpoint and Hiai's
Theorem 4.10 give the universal eigenvalue condition
$R_{\alpha,p}\le_\lambda\mathcal A_{\alpha,q}$ exactly when
$q\ge\alpha(1-\alpha)p$. Partial sums of the eigenvalue inequalities give weak majorization, and the
full sum gives the trace comparison in this range. Conversely, when
$q<\alpha(1-\alpha)p$, Theorem 4.10 supplies a positive-definite $2\times2$
pair with a violated largest-eigenvalue inequality; its first partial sum
therefore violates weak majorization. Thus the weak-majorization condition has
the same universal threshold.
Combining the trace sufficiency obtained by summation with Proposition
4.11's $q\ge1$ region and Theorem 4.12's necessity gives the exact trace
threshold $q\ge\min\{1,\alpha(1-\alpha)p\}$.

**Derived on paper, not formalized:** Positive semidefinite inputs follow from
positive definite approximation and continuity of the functional calculus.
The same endpoint specializes at $t=1/2$ to Sra's/Drury's midpoint case.

## Triage

**Proved in Lean:** The eigenvalue comparison is valid at and above the sharp
weighted endpoint $q=\alpha(1-\alpha)p$ for positive definite complex matrices
in every finite dimension. The decisive change in Sra's inertia argument is
the scalar barrier $x^{a/b}(1-ax)\le b$, which is an equality at $x=1$.
With $a=1-t$, $b=t$, it yields the sharp exponent $2ab$ in Sra's family.
At $t=1/2$ the endpoint is $1/2$, recovering Sra's/Drury's midpoint.

**Proved in the source, not formalized:** Sra's sufficient family at
$q\ge1/2$ and Hiai's sufficient trace region are as stated in Evidence.

**Derived on paper, not formalized:** The eigenvalue and weak-majorization
thresholds coincide at $\alpha(1-\alpha)p$, while the trace threshold is
$\min\{1,\alpha(1-\alpha)p\}$. The necessity in the eigenvalue and trace
statements and the region $q\ge1$ for the trace inequality are source results;
weak majorization follows by summing the eigenvalue comparison.

**Proved in the source, not formalized:** Hiai's Theorem 4.10 gives a
positive-definite $2\times2$ family showing that the Sra family fails when
its exponent is below $2t(1-t)$; this is the source's sharp two-dimensional
obstruction. The trace necessity and the $q\ge1$ trace region are likewise
source results.

**Derived on paper, not formalized:** Replacing $A,B$ by
$A+\varepsilon I,B+\varepsilon I$ and taking $\varepsilon\downarrow0$
extends the eigenvalue, weak-majorization, and trace comparisons to
positive semidefinite inputs. Positive spectral powers and ordered
eigenvalues are continuous in finite dimension.

**Open:** Formalization of singular-input continuity, the full
trace characterization, and the weak-majorization converse remains outside
this module. These are formalization boundaries for the recorded paper
consequences, not unresolved versions of the settled eigenvalue endpoint.

## ASSUMED-UNVERIFIED

Later-literature completeness and worldwide priority are unverified. The Hiai
locator is https://arxiv.org/abs/2508.20309 and the Sra locator is
https://suvrit.github.io/papers/linconj/linconj-v1.pdf; both notes retain
`DOI: null.` and the checked version identifiers.
