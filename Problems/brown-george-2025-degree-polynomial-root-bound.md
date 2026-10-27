---
slug: brown-george-2025-degree-polynomial-root-bound
bibkey: browngeorge2025degree
doi: 10.48550/arXiv.2505.04882
url: https://arxiv.org/abs/2505.04882v1
triage: theorem
motivation_gids:
  - D5/S3/Zeros/DegreeRoots/Result.result
---

# Brown–George's argument-dependent degree-root bound

## Problem

J. I. Brown and I. C. George, *On the roots of degree polynomials*,
Australasian Journal of Combinatorics 92(2), 164–183, Conjecture 4.1, p. 180,
states:

> If z is a nonzero degree root of a graph of order n with argument arg(z) ∈ (−π, π], then |z| ≤ (n − 1)^{|arg(z)/π|}.

Section 1 defines $D(G;x)=\sum_{v\in V(G)}x^{\deg(v)}$.
The arXiv version is *The Degree Polynomial*, arXiv:2505.04882v1.
The settled proposition is

$$
\forall n\ge1\;\forall G\text{ simple on }\operatorname{Fin}(n)\;\forall z\in\mathbb C,
\quad z\ne0\land D(G;z)=0\Longrightarrow
|z|\le(n-1)^{|\arg z|/\pi}.
$$

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Graph of positive order $n$ | Natural `n`, `1 ≤ n`, `SimpleGraph (Fin n)` in `claim` | The preregistered simple-graph convention; empty graphs are excluded |
| Degree polynomial | `degreePolynomial`, the sum of `Polynomial.X ^ G.degree v` over every vertex | Includes degree-zero vertices |
| Nonzero degree root | Complex `z`, `z ≠ 0`, polynomial evaluation equal to zero | Both hypotheses retained |
| $\arg z\in(-\pi,\pi]$ | `Complex.arg z` | Pinned Mathlib branch convention |
| Modulus and power | Complex norm and real power | $\pi>0$ gives $|\arg(z)/\pi|=|\arg z|/\pi$ |
| All nonzero roots | `result : claim` | Universal inequality; no extra root hypothesis |

The public definitions `degreePolynomial` and `claim` reproduce the two
preregistered expressions literally. Positive order is explicit: at order
zero the vertex sum is the zero polynomial, so a universal root bound
would have a different meaning.

## Motivation

[Preregistration #19987](https://github.com/the-omega-institute/trureturing/issues/19987)
selects Conjecture 4.1. The settling declaration is
`D5.S3.Zeros.DegreeRoots.Result.result`, with admission basis
`open-problem-resolution (#19987; Proved)`. Its proof uses the general
`D5.S3.Zeros.DegreeRoots.EscapeWitness.normalized_escape_bound`.

## Gap

The source's Theorem 3.2 gives the real-root bound $n-1$ and Proposition
3.5 gives the imaginary-root bound $\sqrt{n-1}$. Conjecture 4.1 interpolates
these bounds through the root's argument. The published version retains
the conjecture. The source and literature checks recorded in #19987 cover
the article, arXiv version, George's thesis, and title/identifier searches;
no settlement was located in that searched scope. Literature completeness
is `ASSUMED-UNVERIFIED`.

## Route

For $\lambda>0$ and $t\ge0$, put
$F_\lambda(t)=e^{-\lambda t}(\cos t+\lambda\sin t)$.
The private `damped_trig_bound` proves
$F_\lambda(t)\ge-e^{-\lambda\pi}$.
On $0\le t\le\pi$, the proof uses the derivative of
$q(u)=e^{\lambda u}(\cos u-\lambda\sin u)$:
$q'(u)=-(1+\lambda^2)e^{\lambda u}\sin u\le0$ on $[0,\pi]$,
with $u=\pi-t$. For $t\ge\pi$, put $u=t-\pi$; the estimates
$\cos u\le1$, $\sin u\le u$, and $1+\lambda u\le e^{\lambda u}$
give the same lower bound.

Suppose $a_i\ge0$, $a_0>0$, $k_i\in\mathbb N$, $r=|z|>1$, and
$a_0+\sum_i a_i z^{-k_i}=0$. For $\theta=\arg z>0$, take
$\lambda=\log r/\theta$. Multiplication by $1+i\lambda$ and real
parts give

$$
0=a_0+\sum_i a_i F_\lambda(k_i\theta)
\ge a_0-e^{-\lambda\pi}\sum_i a_i.
$$

Thus $e^{\lambda\pi}\le(\sum_i a_i)/a_0$ and
$r\le((\sum_i a_i)/a_0)^{\theta/\pi}$. Nonnegativity excludes
argument zero; conjugation handles negative argument. This is the public
`normalized_escape_bound` over an arbitrary finite index type, with no
fixed cardinality or exponent bound.

For a graph, let $d$ be its maximum degree, $m$ the number of vertices
of degree $d$, and $S$ the remaining vertices. Dividing $D(G;z)=0$
by $z^d$ gives $m+\sum_{v\in S}z^{-(d-\deg v)}=0$.
Here $m\ge1$ and $m+|S|=n$, so $|S|/m\le n-1$.
The general estimate proves the exterior-root case. For $n\ge2$,
the right-hand side of the conjectured bound is at least one; this handles
$|z|\le1$. For $n=1$, the polynomial is one and has no roots.

## Falsifier

A mismatch in the vertex sum, positive-order restriction, argument branch,
real-power convention, or universal quantifiers invalidates source
fidelity. A graph, nonzero root, and strict violation would refute the
encoded conjecture. Numerical checks provide finite evidence only.

## Evidence

The kernel-checked settling theorem is
`D5.S3.Zeros.DegreeRoots.Result.result`. The supporting general estimate
is `D5.S3.Zeros.DegreeRoots.EscapeWitness.normalized_escape_bound`.
The axiom closure of every public declaration is contained in
{`propext`, `Classical.choice`, `Quot.sound`}.

### Experiment

The program is in
[the experiments repository at `fa30318aef455ef7e0ce6e6dc2fd3ff06391a669`](https://github.com/the-omega-institute/trureturing-experiments/tree/fa30318aef455ef7e0ce6e6dc2fd3ff06391a669/docs/reports/brown-george-2025-degree-polynomial-root-bound),
file `check.py`. The pinned blob exists (`git cat-file -e`, exit 0).
Its SHA-256 is `8758cc1cdc8b1fd6cd469277528e9390a64a25b6485a696145a0a31380d19f1e`.
The command
`python3 /Users/auric/.sshx/3725ce750c618c117ba5ef82/attempt-1/experiment-check.py`
executes that blob extracted without changes, with exit 0.
It tests all labelled simple graphs on 2–6 vertices and 20,000 seeded
random graphs on 7 vertices, counting 142,065 nonzero numerical roots.
The largest bound ratio is 1.000000000000; the largest real-root ratio
against $n-1$ is 1.000000000000. For stars of orders 3–11 the displayed
candidate roots have residual at most $6.47\times10^{-15}$ and ratio
1.000000000000. These are floating-point results with the script's
$10^{-9}$ acceptance tolerance, not exact certificates or exhaustive
results for order seven or larger.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Conjecture 4.1 | Proved; kernel-checked `Result.result` | All positive orders, simple graphs, and nonzero degree roots |
| Decisive rotated-real-part mechanism | Proved; kernel-checked `EscapeWitness.normalized_escape_bound`, using its private `damped_trig_bound` | The uniform damped-trigonometric lower bound yields the argument-dependent estimate |
| Nominated Lemma 2 in normalized finite-sum form | Proved; kernel-checked `EscapeWitness.normalized_escape_bound` | Arbitrary finite nonnegative real weights and natural exponents, positive constant, root norm greater than one |
| Nonnegative-coefficient polynomial form of Lemma 2 | Proved in prose below | No new public polynomial wrapper theorem |
| Loopless multigraph extension | Proved in prose below | A mathematical consequence for finite degree sequences; no multigraph Lean theorem |
| Star equality | Proved in prose below; not formalized as an equality theorem | All star orders at least three |
| Uniqueness of extremal graphs | Open | No classification of equality cases |
| Source's real and imaginary bounds | Proved in prose below as consequences | No additional public corollary theorem |
| Canonical Scribe, registration and admission follow-up | Open for the four-slot audit; canonical source, Scribe and freeze delivered | One Proved resolution claim on `Result.result`; remaining audit obligations are in #20929 |
| Four-slot escape registration | Open; missing registration evidence | Both public theorem targets remain in [#20929](https://github.com/the-omega-institute/trureturing/issues/20929); no Reg mirror or validated registration is asserted |
| Graph and star numerical checks | Computed; the experiment above, exit 0 and recorded script SHA-256 | Exactly its finite sample and numerical tolerances |
| Literature screen | Open; literature reading recorded in #19987 | No settlement located in the checked sources; completeness `ASSUMED-UNVERIFIED` |

**Polynomial consequence (proved in prose).** Write
$P(X)=\sum_{j=0}^d a_jX^j$ with $a_j\ge0$, $a_d>0$, and
$A=\sum_{j<d}a_j$. If $P(z)=0$ and $|z|>1$, then $z\ne0$ and
$a_d+\sum_{j<d}a_j z^{-(d-j)}=0$ after division by $z^d$.
The general finite-sum estimate gives $|z|\le(A/a_d)^{|\arg z|/\pi}$.
For the remaining nonzero roots $|z|\le1$, this implies the uniform form
$|z|\le\max(1,(A/a_d)^{|\arg z|/\pi})$ by the unit-disk branch.
A constant positive polynomial has no roots, so the empty lower-degree
sum creates no exception.

**Multigraph consequence (proved in prose).** For a nonempty finite
loopless multigraph, choose the largest vertex degree $d$, let $m\ge1$
count its occurrences, and let $S$ contain the other vertices. Degrees
remain natural numbers even when edges have multiplicity. The same
normalized equation and $|S|/m\le n-1$ hold because each vertex contributes
one monomial. Neither adjacency simplicity nor an upper bound on $d$ is
used in this argument. Order one has constant degree polynomial one.
This establishes the stated multigraph bound mathematically; the delivered
Lean result retains the preregistered simple-graph domain.

**Stars (proved in prose).** For $n\ge3$,
$D(K_{1,n-1};X)=X^{n-1}+(n-1)X$. Put
$r=(n-1)^{1/(n-2)}$ and $z=r\exp(i\pi/(n-2))$.
Then $z^{n-2}=-(n-1)$, hence $D(K_{1,n-1};z)=0$ and $z\ne0$.
Its principal argument is $\pi/(n-2)$ and
$(n-1)^{|\arg z|/\pi}=r=|z|$. The numerical experiment checks orders
3–11 separately. This derivation neither classifies other extremizers
nor adds a kernel-checked equality theorem.

**Source consequences (proved in prose).** A nonzero negative real root
has $|\arg z|=\pi$; substituting gives $|z|\le n-1$.
A positive real number cannot be a root of the nonzero nonnegative
coefficient sum. A nonzero purely imaginary root has
$|\arg z|=\pi/2$, yielding $|z|\le\sqrt{n-1}$.
These recover the source's two directional bounds. The settlement does
not supply an equality classification or strengthen unrelated source
statements.

## ASSUMED-UNVERIFIED

Literature completeness and absence of every possible dominating external
theorem are unverified. The numerical experiment has floating-point
accuracy and its stated finite scope. Uniqueness of extremizers and both
four-slot registrations are open. The prose polynomial, multigraph and
star consequences are distinguished from the delivered kernel statements.
