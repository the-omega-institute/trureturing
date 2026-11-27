---
slug: cooper-du-2025-reflected-steiner-h-eigenvalue-positivity
bibkey: cooperdu2025steinerdistancehypermatrices
doi: 10.48550/arXiv.2505.10501
url: https://arxiv.org/abs/2505.10501v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner.result
  - D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner.star_negative
---

# A fixed star refutes reflected Steiner H-eigenvalue positivity

## Problem

The questions are from Joshua Cooper and Zhibin Du’s *Determinants of
Steiner Distance Hypermatrices* (arXiv:2505.10501v1), Section 4, printed
page 10, following Proposition 4.5. [Author PDF](https://arxiv.org/pdf/2505.10501v1#page=10)

> Thus, we ask: is it true that the H-eigenvalues of C₁ are all positive? Does this generalize to all even k?

For a finite tree $T$, the entry of $M$ at an ordered $k$-tuple is the
edge count of the minimal subtree containing all its vertices.
Repeated indices are allowed. Let $A$ be reflection through the
all-ones line, so $(Ax)_i=2\sum_j x_j/n-x_i$ for $n=|V(T)|$.
The authors place $A$ in the last slot at order four. At general
order $k$, the same placement gives
$C_1(z_1,\ldots,z_k)=M(z_1,\ldots,z_{k-1},Az_k)$.

The formal claim asks whether for every finite simple tree on $n\ge3$
vertices and every even $k\ge4$, every real $\lambda$ with a nonzero
real vector $x$ satisfying $M(e_i,x,\ldots,x,Ax)=\lambda x_i^{k-1}$
at every vertex is strictly positive. This covers the quartic question
and the extension to higher even orders.

## Motivation

The paper gives computational evidence for positivity at order four.
The 48-vertex star $K_{1,47}$ gives a strictly negative first-slot
H-eigenvalue at every even order $k\ge4$, with the same tree and an
order-dependent eigenpair.

## Gap

A negative diagonal value gives information about the homogeneous
polynomial of the reflected form. The H-eigenpair in this problem
must satisfy the first-slot equations for the literal last-reflected
tensor. The bounded literature screen recorded in issue #34722
found no settlement of that question in the sources it checked.
[Preregistration](https://github.com/the-omega-institute/trureturing/issues/34722)

## Route

A star edge belongs to the minimal subtree exactly when the tuple
meets both sides of the corresponding leaf cut. Its contribution to
the multilinear form is the product of the whole-vertex slot sums
minus the products restricted to either side. For the vector with
centre coordinate $s+47$ and every leaf coordinate $-1$, let $U$
and $V$ denote the contributions of a cut to a row at a vertex outside
and inside its isolated leaf, respectively. The centre row is $47U$
and each leaf row is $46U+V$.

With $m=k-2$ and reflected leaf coordinate $y=1+s/24$, the cut
contributions are $U=s^{m+1}-(s+1)^m(s-y)$ and $V=s^{m+1}-y$.
Eliminating the eigenvalue gives the balance polynomial
$47U+(s+47)^{m+1}(46U+V)$. At $s=24/23$ we have $s=y$ and both
cut contributions are positive. At $s=2$, the inequality
$3^{m-2}\ge 2^{m-2}$ gives $U\le-2^{m-2}/4$ and
$46U+V\le-(7/2)2^{m-2}-13/12<0$. The intermediate value theorem gives a zero between them.
Since $V>0$ there, the balance forces $U<0$. Thus
$\lambda=47U/(s+47)^{m+1}<0$. The balance gives the leaf equation
because $m+1$ is odd.

## Falsifier

The counterexample must use the tuple minimum for the original tree,
the reflection in the final slot, a nonzero real vector and the
first-slot eigenvalue equation at every vertex. The centre coordinate
$s+47$ is positive, and the centre and common leaf equations both
hold. The order-four instance already contradicts strict positivity.

## Evidence

The public theorem
`D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner.star_negative`
supplies, for each natural even $k\ge4$, a nonzero vector
$x:\mathrm{Fin}\,48\to\mathbb R$ and a real $\lambda<0$ satisfying
the first-slot H-eigenpair equations at order $k$. The tree is the
same labelled star $K_{1,47}$ centred at $0$ for every order. The
eigenpair may depend on $k$.

The designated refutation
`D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner.result`
has literal Lean type `¬ claim`. It applies `star_negative` at
$k=4$, where the negative eigenvalue contradicts the strict positivity
required by `claim`.

The Reg mirror
`Reg.D5.S3.Combinatorics.Graph.Steiner.CooperDuReflectedSteiner.registration`
uses $k$ and $x$ as its parameters and $\lambda$ as its real state.
The Boolean readout decides the same H-eigenpair predicate, and the
registration law retains the order premises and strict negativity.
[Statement revision in issue #34722](https://github.com/the-omega-institute/trureturing/issues/34722#issuecomment-7210074969)

## Triage

- **Proved in Lean.** The uniform star family supplies a negative
  first-slot H-eigenvalue at each even order $k\ge4$. The cut formula
  and the signs of the balance polynomial explain why the same tree
  works throughout this range.
- **Computed separately.** For $K_{1,8}$ at order four,
  $x=(12,-1,\ldots,-1)$ gives $C_1(x,x,x,x)=-48$. An exact sum over
  all $9^4=6561$ ordered tuples agrees with the cut evaluation.
- **Prose consequence for the symmetric tensor.** The quartic
  polynomial attains a negative minimum on $\sum_i x_i^4=1$, after
  rescaling the displayed vector. At a minimizer the Lagrange
  multiplier equations, contracted with that vector, give an
  H-eigenvalue equal to the negative minimum for the symmetric tensor
  associated with the polynomial. The Lean endpoint uses the
  first-slot equations for the literal reflected tensor.
- **Source scope.** Proposition 4.5 on printed page 9 concerns
  diagonal positivity of $C_1+C_3$. Conjecture 1 on printed page 8
  concerns the sign of the unreflected Steiner hyperdeterminant.
  References follow the two positivity questions, with no later
  result in v1 invoking them. [Author PDF, printed pp. 8–10](https://arxiv.org/pdf/2505.10501v1#page=8)
- **Open here.** The smallest star admitting a negative first-slot
  H-eigenvalue at order four and the dependence of that threshold on
  the order remain undetermined by this construction.

## ASSUMED-UNVERIFIED

The literature screen does not establish exhaustive coverage or
priority. The symmetric-tensor eigenvalue bridge and any minimal star
size are outside the formal endpoint.
