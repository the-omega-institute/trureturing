---
slug: yaqubi-mirzavaziri-2026-designated-summands-conjecture-6-1
bibkey: yaqubi2026designatedsummands
doi: 10.48550/arXiv.2611.05623
url: https://arxiv.org/abs/2611.05623v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/ModularForms/DesignatedSummandCongruence.result
---

# Exact 2-adic divisibility for partitions with designated summands

## Problem

> For every $k \ge 1$, the largest power of $2$ dividing all $A_k(4n + 3)$ is $2^{v_2(A_k(3))}$ if $k \not\equiv 2 \pmod{16}$, and exactly $2^3$ if $k \equiv 2 \pmod{16}$.

Here $A_k(m)$ counts ordered $k$-tuples of total size $m$. In each component,
one actual occurrence is distinguished for every size present. Components of
size zero are allowed. The formal statement quantifies all $k\in\mathbb N$
with $0<k$, all exponents $e\in\mathbb N$, and all progression indices
$n\in\mathbb N$. [Conjecture 6.1](https://arxiv.org/html/2611.05623v1#S6.Thmtheorem1)

## Motivation

The first coefficient of an arithmetic progression supplies an upper bound for
the common power of two. The problem asks when that bound is attained, and
which coefficient gives the sharp bound when the first coefficient has extra
divisibility. The source reports numerical checks for $k\le96$ and initial
progression indices. [Source, §6](https://arxiv.org/html/2611.05623v1#S6)

## Gap

Theorem 3.12 proves lower bounds for $k\equiv3\pmod4$,
$k\equiv2\pmod4$, and $k\equiv2\pmod8$. Proposition 3.13 supplies
the degree-three formula and exactness for $k\equiv6\pmod8$.
The conjecture requires uniform sharpness for every positive $k$.
[Theorem 3.12](https://arxiv.org/html/2611.05623v1#S3.Thmtheorem12) · [Proposition 3.13](https://arxiv.org/html/2611.05623v1#S3.Thmtheorem13)

## Route

Write $f_d=\prod_{i\ge1}(1-q^{di})$ and $F=f_6/(f_1f_2f_3)$.
For each part size, the multiplicity $m>0$ contributes $m$ choices.
The weighted partition product and convolution over the component
degrees give $A_k(m)=[q^m]F^k$. The complete Jacobi products and a
degree- and sign-preserving parity bijection give the integral dissections
$$
H=1/F=H_0(q^2)-qT(q^4),\qquad
F^2=E(q^2)+2qW(q^2).
$$
The reciprocal has zero coefficient at $4n+3$. The odd coefficients of
$W=f_2^4 f_6^4/(f_1^8 f_3^4)$ are divisible by four.

Dyadic lifting compares $P(q)^{2^{j+1}}$ with $P(q^2)^{2^j}$ coefficientwise
modulo $2^{j+1}$. For odd $k$, use the reciprocal with the lifted power
$F^{k+1}$ and the missing residue of $H$. For $4\mid k$, one dilation
kills the odd degrees. For $k\equiv2\pmod4$, apply the square
dissection and the odd-coefficient bound on $W$.

The coefficient formula $6A_k(3)=k(k+1)(k+14)$ gives sharpness at
$n=0$ in the nonexceptional classes. Modulo $16$, $F^{64}$ has constant
coefficient one and zero coefficients in degrees one through seven.
Thus for every natural $k$, the degree-seven coefficient
$[q^7]F^k$ modulo $16$ depends only on $k$ modulo $64$.
Convolution modulo $16$ through degree seven gives residue $8$ for each
of the four representatives $2,18,34,50$. This gives sharpness at $n=1$ for
the whole exceptional class.

## Falsifier

A positive $k$ and a progression index with valuation below the asserted
exponent would disprove the common divisibility direction. For the
upper bound, outside the exception the index $3$ determines the valuation.
Within the exception the proof must establish that the coefficient at $7$
is $8\pmod{16}$ for every $k\equiv2\pmod{16}$.

## Evidence

The settling Lean declaration is
`D5/S3/Arith/ModularForms/DesignatedSummandCongruence.result`.
`DesignatedSummands.marked_count_coeff` identifies the generating function
with the cardinality of the actual marked tuples.
`DesignatedSummandThetaDissection.U_dissection` reindexes the complete
Jacobi product. `DesignatedSummandEtaDissection.H_dissection`,
`F_square`, `H_support` and `W_support` are integral identities and
coefficient statements. In the same module, `reduce_lift` and
`reduce_lift_mul` give the all-degree congruences. In the settling module,
`exceptional_sharp` uses `coeff_seven_period` and checks the four modular
convolutions inside its proof. It supplies the upper bound in `result`. [Preregistration](https://github.com/the-omega-institute/trureturing/issues/33469)

Four-slot escape registration remains open. [Registration issue](https://github.com/the-omega-institute/trureturing/issues/33480)

## Triage

- **Proved, kernel-checked.** The common exponent is exactly the value in
  Conjecture 6.1, by `result`. For odd $k$ the value is $v_2(k+1)-1$;
  for $4\mid k$ it is $v_2(k)$; for $k\equiv6\pmod8$ it is $2$;
  for $k\equiv10\pmod{16}$ it is $3$. These are the cases in the proof
  of `full_lower` using `A3_valuation`, with the upper bound at
  $n=0$ in `result`.
- **Proved, kernel-checked.** For $k\equiv2\pmod{16}$ the common
  exponent is $3$ even though $A_k(3)$ is divisible by $16$.
  The degree-three divisibility follows from the product formula
  `A3_formula` and $16\mid k+14$, $2\mid k$.
  The degree-seven sharpness is `exceptional_sharp`.
- **Source scope.** Conjecture 6.2 concerns $B_k$, the odd-parts model.
  Conjectures 6.3 and 6.4 concern different progression and prime-power
  conditions. They are separate from the conclusion established here.
  [Source, §6](https://arxiv.org/html/2611.05623v1#S6)

## ASSUMED-UNVERIFIED

The bounded literature search tied to the preregistration found no exact
prior settlement. arXiv search and Semantic Scholar returned HTTP 429
during that search. Exhaustiveness and global priority remain unverified.
[Preregistration](https://github.com/the-omega-institute/trureturing/issues/33469)
