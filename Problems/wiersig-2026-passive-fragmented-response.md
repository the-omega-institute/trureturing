---
slug: wiersig-2026-passive-fragmented-response
bibkey: wiersig2026fragmentedresponse
doi: 10.1103/5451-5wd1
url: https://arxiv.org/pdf/2610.31268v1#page=6
triage: theorem
motivation_gids:
  - D5/S1/Eigenstructure/WiersigFragmentedResponse.sharp_passive_fragmented_response
---

# Sharp passive fragmented response at a sole eigenvalue

## Problem

Jan Wiersig asks in the closing paragraph of §VII, p. 6, of *Rank-One Loss
Maximizes the Spectral Response Strength of Passive Full-Order Exceptional
Points* whether analogous passive response bounds exist for fragmented
exceptional points and whether rank-one loss remains optimal.
[Versioned paper](https://arxiv.org/pdf/2610.31268v1#page=6) · [Version of record](https://doi.org/10.1103/5451-5wd1) · [Library note](../Library/Eigenstructure/wiersig2026fragmentedresponse.md)

Prescribe any $E\in\mathbb C$ with $\beta=-2\operatorname{Im}E>0$ and any
partition $(m_1,\ldots,m_b)$ with $b\ge 2$, all $m_j\ge 1$, and
$p=\max_j m_j\ge 2$. Put $n=\sum_j m_j$. Consider all complex $n\times n$
matrices $H$ whose sole eigenvalue is $E$, with exactly that multiset of
Jordan block sizes and positive semidefinite loss
$\Gamma(H)=i(H-H^*)$. The adjoint uses the orthonormal coordinates of
$\mathbb C^n$. Let $C_{-p}(H)$ be the coefficient of $(z-E)^{-p}$ in
$(zI-H)^{-1}$. Its Euclidean operator norm is denoted
$\xi(H)=\|C_{-p}(H)\|_2$.

Every such $H$ satisfies $\xi(H)\le\beta^{p-1}$ and
$\operatorname{rank}_{\mathbb C}\Gamma(H)\ge b$. For every prescribed
$E$ and partition, a single admissible $H$ satisfies both equalities.
In particular the maximum response remains $\beta^{p-1}$ when attention
is restricted to matrices with the minimum feasible loss rank $b$.

## Motivation

Wiersig's single-chain bound depends on the linewidth and the chain
length. In a fragmented collision the maximum chain length fixes the
Laurent pole order while the number of chains determines the geometric
multiplicity of $E$. The problem asks how these two quantities constrain
response and dissipation simultaneously.

## Gap

The Tier 1 preregistration specializes the published direction to a
collision spanning the whole space. Wiersig's equations (49) and (53)
treat a single chain. Bid and Schomerus identify the leading coefficient
and distinguish the spectral and physical response norms in equations
(19) and (20). Szehr's contraction estimate and the
Arlinskii–Tsekanovskii rank-one block model give classical ingredients.
The bounded literature and repository screen found no explicit treatment
combining the sharp response with simultaneous attainment of the minimum
loss rank for every prescribed partition in this scope.
[Preregistration and search scope](https://github.com/the-omega-institute/trureturing/issues/35071) · [Bid–Schomerus](https://arxiv.org/abs/2507.22158v1) · [Szehr](https://arxiv.org/abs/1305.7208v2) · [Arlinskii–Tsekanovskii](https://arxiv.org/abs/math/0602033)

## Route

Write $N=H-EI$. The chain basis gives $N^p=0$ and $N^{p-1}\ne 0$.
The finite geometric sum gives the resolvent at every $z\ne E$ and
identifies $C_{-p}=N^{p-1}$. For $A=N/(-i\beta)$, set
$B=I+A$ and $T=AB^{-1}$. The identity
$B^*B-A^*A=\Gamma/\beta$ gives $I-T^*T\succeq 0$ by congruence.
Nilpotence gives $T^{p-1}=A^{p-1}$, so taking the power of this contraction
gives the response bound. On $\ker N$, the quadratic form of $\Gamma$
equals $\beta\|x\|^2$. Thus $\Gamma$ is injective on the $b$-dimensional
eigenspace and has rank at least $b$.

For attainment let $S$ be the orthogonal sum of the lower unit shifts on
the prescribed blocks and set $H=EI-i\beta((I-S)^{-1}-I)$. The loss
on each block is $\beta$ times the all-ones matrix, giving a positive
semidefinite loss of rank $b$. The top power of the normalized shift sum
sends a coordinate unit vector in a largest block to another coordinate
unit vector. The ranks of all powers agree with the prescribed rank
profile $\sum_j\max(m_j-k,0)$ at power $k$. Taking second differences and
applying the frozen nilpotent Jordan-chain theorem gives a full basis
with the prescribed multiplicities, including the size-one blocks.

## Falsifier

An admissible matrix with response greater than $\beta^{p-1}$ or loss
rank below $b$ would refute a universal bound. A prescribed positive
linewidth and fragmented partition for which no single admissible
matrix attains both equalities would refute the existence clause.

## Evidence

The theorem encodes the prescribed partition by a full complex linear
basis with the block-shift action for every iterate. Its spectral clause
characterizes noninvertibility of $zI-H$ by $z=E$, and the displayed
resolvent sum identifies the leading coefficient in the same Euclidean
operator norm used in the bound and equality. The witness existential
returns one matrix with that partition and both equalities. The compiled
axiom closure on the pinned Mathlib backend is `Classical.choice`,
`Quot.sound` and `propext`.
[Lean theorem](../D5/S1/Eigenstructure/WiersigFragmentedResponse.lean) · [Blueprint](../Blueprint/D5/S1/Eigenstructure/WiersigFragmentedResponse.md) · [Canonical freeze record](../Golden/Frozen/state/D5/S1/Eigenstructure/WiersigFragmentedResponse.lean.json)

The typed Reg source compiles the full source-equivalence bridge, a
strict-rank intervention using an admissible rank-two witness, and
observational dependence of the Boolean rank readout. The binding remains
`declared_unresolved`. The inspector rejects `Nat.decLt` in the
dependent comparison of the original Jordan-chain premise with
`IE-C050` under `source.unsafe_or_external`. The source-owner binding
certificate is outstanding under the linked-issue exception.
[Reg source](../Reg/D5/S1/Eigenstructure/WiersigFragmentedResponse.lean) · [Audit disclosure](https://github.com/the-omega-institute/trureturing/issues/35071#source-bound-escape-audit)

## Triage

### What the settlement shows

**Proved.** The normalized Cayley transform and the orthogonal block
construction give the sharp Euclidean spectral response for every
prescribed fragmented partition at a sole eigenvalue. Eigenspace
compression gives minimum feasible loss rank $b$, so rank-one loss is
infeasible in this scope. The joint witness resolves both parts of the
whole-space question.
[`sharp_passive_fragmented_response`](../D5/S1/Eigenstructure/WiersigFragmentedResponse.lean)

**Scope.** Embedded collisions with spectator eigenvalues, the physical
response measured by the Frobenius norm, and classification of all
maximizers are outside this result. The positive-linewidth condition and
the prescribed partition are part of the claim.

## ASSUMED-UNVERIFIED

The bounded source screen leaves historical priority and independent
resolutions outside the searched literature unverified. The exact
source-owner binding certificate remains unverified for the reason
recorded above.
