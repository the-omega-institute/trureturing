---
slug: nayak-strong-hyperlattice-birkhoff
bibkey: nayaketal2026convexsubhyperlattices
doi: 10.48550/arXiv.2611.10526
url: https://arxiv.org/abs/2611.10526v1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.result
---

# Convex subhyperlattices need not form a lattice in Birkhoff order

## Problem

N Aishwarya Nayak, Bhargava K, Pallavi Panjarike, Kuncham Syam Prasad, Tapatee Sahoo,
and Harikrishnan Panackal ask in §5, printed p. 20 of *On the structural aspects of
Convex Subhyperlattices under different orders*, arXiv:2611.10526v1:

> Based on our observations, we have conjectured that (CS(𝔏), ≤_b) is a lattice for every strong hyperlattice.

The quotation uses plain-text mathematical notation. The source is licensed under
Creative Commons Attribution 4.0 International. [Versioned conjecture](https://arxiv.org/html/2611.10526v1#S5.p1.1) ·
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)

### Statement echo

The carrier is nonempty. The meet is a binary operation and the hyperjoin takes
nonempty set values. The set extension of hyperjoin unions all outputs over
input pairs. Meet extends to sets by pointwise image. The three meet laws are
idempotence, commutativity and associativity. Hyperjoin contains its input on
the diagonal, is commutative and is associative under the set extension. Both
absorption laws are required, and membership of the second input in a hyperjoin
implies that the meet equals the first input.

The carrier order is meet equality, equivalently membership of the second input
in the hyperjoin. The convex subhyperlattices are the nonempty order-convex
subsets closed under meet and the entire hyperjoin. Birkhoff comparison
$A\le_b B$ means that every member of $A$ is below a member of $B$ and every
member of $B$ is above a member of $A$. The positive conjecture requires
both a greatest common lower bound and a least common upper bound for every
pair, with extremality quantified over all convex subhyperlattices.
[Definitions 1.1–1.3 and 1.10](https://arxiv.org/html/2611.10526v1#S1) ·
[Proposition 3.1](https://arxiv.org/html/2611.10526v1#S3.Thmtheorem1)

## Motivation

Corollary 3.10 proves the lattice property for the restricted class of
P-hyperlattices. The conjecture asks whether the strong axioms alone suffice.
[Corollary 3.10](https://arxiv.org/html/2611.10526v1#S3.Thmtheorem10)

## Gap

Common lower bounds must be closed under the whole hyperjoin. An operation
can add an output above the ordinary join, even though all outputs are above
both inputs and the ordinary absorption laws still apply.

## Route

Adjoin a fresh top $t$ to the Boolean square $0<a,b<c$, with incomparable atoms
$a,b$. Use ordinary meet. The hyperjoin contains the ordinary join $s$ and also
$t$ exactly when $s=c$ and the two inputs differ. In either association of a
triple, the ordinary branch gives the total ordinary join. An extra output
occurs exactly when that total join is $c$ and some input differs from $c$.
This describes the two set unions by the same rule. Ordinary join and meet
give the two absorptions, and every hyperjoin output is above both inputs.

The convex subhyperlattices $\{c\}$ and the whole carrier have common lower
bounds $[0,a]$ and $[0,b]$. A greatest lower bound would contain $0$ by the
second Birkhoff clause against the whole carrier. By the first Birkhoff clause,
domination of the two intervals supplies an element above each atom. Convexity
with $0$ forces both atoms into the bound. Their hyperjoin contains $t$.

## Falsifier

The first Birkhoff clause against $\{c\}$ would put $t$ below $c$. The fresh top
lies strictly above $c$, so the indicated pair has no greatest lower bound.

## Evidence

The Lean countermodel uses `ULift (WithTop (Bool × Bool))`. It refutes the
conjecture at each carrier universe. The `Type 0` certificate has literal form
`result : ¬ claim` and includes both required bounds in the positive proposition.
The proof uses the two atom intervals and the exclusion of their common
greatest lower bound. [Lean probe and original attribution](https://github.com/the-omega-institute/trureturing/issues/33303#issuecomment-7082391764)

## Triage

### What the settlement shows

- **Proved in Lean.** The five-element construction satisfies the strong axioms and excludes a greatest lower bound for the actual pair. The public refutation is `D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.result`.
- **Proved from the source's characterization.** In a P-hyperlattice the hyperjoin depends on the ordinary join through a fixed parameter set. In this witness $a\lor b=c\lor c=c$, while the hyperjoin gives $\{c,t\}$ on the first pair and $\{c\}$ on the second. Thus the witness lies outside the P-hyperlattice class, and its exclusion of a greatest lower bound leaves Corollary 3.10 applicable to that class. [Theorem 1.6](https://arxiv.org/html/2611.10526v1#S1.Thmtheorem6) · [Corollary 3.10](https://arxiv.org/html/2611.10526v1#S3.Thmtheorem10)
- **Open here.** Minimum counterexample size, a characterization of the strong hyperlattices with the lattice property, and the separate finite-product question about strongly convex sets are outside this result. [Section 5](https://arxiv.org/html/2611.10526v1#S5.p1.1)

## ASSUMED-UNVERIFIED

The bounded arXiv, Crossref, OpenAlex and formal-library searches located no
prior exact settlement. The 2025 antecedent was checked at abstract and
citation level. Worldwide priority, unpublished results and completeness of
the indexes are unverified. [Source qualification and preregistration](https://github.com/the-omega-institute/trureturing/issues/33303)
