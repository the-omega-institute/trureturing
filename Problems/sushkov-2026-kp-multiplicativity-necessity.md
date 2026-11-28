---
slug: sushkov-2026-kp-multiplicativity-necessity
bibkey: sushkov2026jacobihurwitz
doi: 10.48550/arXiv.2611.02795
url: https://arxiv.org/abs/2611.02795v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2
---

# Sushkov’s KP multiplicativity necessity question

## Problem

Matvey Sushkov, arXiv:2611.02795v1, §6 item 1, printed p. 29, asks
whether multiplicativity is necessary.

> For which coefficients $a_\nu$, not necessarily multiplicative, is $\mathrm{ch}\,[(6.1)]$ a tau function of the KP hierarchy in $u$? Multiplicativity of $a_\nu$ is sufficient, but we do not know whether it is necessary.

The target is the necessity implication for arbitrary complex families
indexed by every integer partition. At H(x) ≡ 1 and N = 1, require constant
term one and vanishing of the KP bilinear residue in every output time
weight. Necessity would require a single family $(b_j)_{j\ge1}$ with
$a_\nu=\prod_{r\in\nu}b_r$ for every partition, counting repeated parts
and using one for the empty product. An example at these admissible
parameters also refutes necessity without the normalization hypothesis.
[Pinned source](https://arxiv.org/pdf/2611.02795v1#page=29)

## Motivation

The frozen DeformedJucysMurphyC2 module uses power-sum monomials of weight
equal to the partition size and the centralizer factor $z_\nu$. These
supply the degreewise coordinates needed to ask whether the KP condition
restricts the class-sum coefficients to a product over parts.

## Gap

This is the tier-1 necessity clause of §6 item 1. The bounded literature
screen found no explicit settlement of that clause. The shifted Schur
tau and the bilinear criterion are classical. [Preregistration](https://github.com/the-omega-institute/trureturing/issues/35289)

## Route

In (6.1) the Jucys–Murphy product becomes the unit in every degree,
including degree zero. The unscaled class sum $C_\nu$ maps by (2.15)
to $p_\nu/z_\nu$. With $a_\varnothing=a_{(1)}=1$ and all higher degrees
zero, the Frobenius image is $1+p_1=1+t_1$ under $p_j=j t_j$.

For independent times $t,s$, put $A=1+t_1$ and $B=1+s_1$. Clearing
$z^{-2}$ gives $(Az-1)(Bz+1)$. The constant and linear terms of the
full exponential are $1$ and $(t_1-s_1)z$. Thus the Laurent residue
is $A-B-(t_1-s_1)=0$. The weight-zero contributions cancel, weight one
uses the pair of input weights $(1,1)$, and every higher weight has
a zero input in each pair. The partition $(1)$ forces $b_1=1$, and
the partition $(1,1)$ then forces $0=b_1^2=1$.

## Falsifier

A nonzero residue at any output weight, a multiplicative representation
of the displayed family, or a failure of the class-sum and time
normalizations at the stated parameters would invalidate the
counterexample. The Lean proof establishes the normalization and
every residue weight in the specialized formulation and derives the
repeated-part contradiction.

## Evidence

The Lean theorem `D5/S3/Combinatorics/PerfectMatchings/SushkovKPMultiplicativityRefutation.result` has type `¬ claim`.
The Frobenius image equality holds at every weight. The formal residue
uses both independent time sequences and the finite antidiagonal
$m+n=d+1$ for output weight $d$. The bridge from the source group algebra
and the classical KP identity to these definitions is mathematical
exposition.

## Triage

`theorem` under the `open-problem-resolution` admission basis.
The `Refuted` claim concerns the necessity clause. The full classification,
the sufficient construction and §6 items 2 and 3 lie outside its scope.

## ASSUMED-UNVERIFIED

Bibliographic priority and MathDB coverage remain unverified. The source
identification with the group-algebra construction and the classical
Laurent residue has no separate Lean equivalence theorem.
