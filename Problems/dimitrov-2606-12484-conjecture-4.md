---
slug: dimitrov-2606-12484-conjecture-4
bibkey: dimitrov2026c4c5
doi: null
url: https://arxiv.org/abs/2606.12484v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5.result4
---

# Dimitrov's Conjecture 4

## Problem

S. I. Dimitrov, *Lower bounds on expressions depending on the functions
φ(n), ψ(n) and σ(n), III*, arXiv:2606.12484v1, §2, PDF page 4,
Conjecture 4, asks whether the following inequality holds for every integer
$n\ge2$ and every integer $k\ge1$:

$$
\begin{aligned}
&\bigl(\varphi(n)^k(\psi(n)+\sigma(n))
 +\psi(n)^k(\varphi(n)+\sigma(n))
 +\sigma(n)^k(\varphi(n)+\psi(n))\bigr)\\
&\quad\cdot\left(
 \frac1{\varphi(n)^k(\psi(n)+\sigma(n))}
 +\frac1{\psi(n)^k(\varphi(n)+\sigma(n))}
 +\frac1{\sigma(n)^k(\varphi(n)+\psi(n))}\right)\\
&\qquad\ge
 \frac{5n(n+1)^{k-1}(n-1)^k+2(n-1)^{2k}+2n^2(n+1)^{2k-2}}
 {n(n+1)^{k-1}(n-1)^k}.
\end{aligned}
$$

Here $\varphi$ is Euler's totient,
$\psi(n)=\prod_{p^e\parallel n}p^{e-1}(p+1)$ is Dedekind's function,
and $\sigma(n)=\sum_{d\mid n}d$ is the positive-divisor sum. All powers
are pointwise powers of function values. The preregistered source event is
[#30196](https://github.com/the-omega-institute/trureturing/issues/30196).

## Motivation

The settling declaration is
`D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5.result4`, whose source claim is
`claim4`. `Nat.totient`, the local Dedekind `psi`, and
`ArithmeticFunction.sigma 1` represent the three source functions.
The question compares their mixed-power terms through the full reciprocal
product, uniformly over the unrestricted source range.

## Gap

The cited source states this exact lower bound as Conjecture 4. The bounded
literature and repository screen recorded in #30196 found no exact settlement
in its checked scope, including the fixed prior Dimitrov formalization
repository. That screen establishes no worldwide absence or priority claim.

## Route

Use $0<\varphi(n)\le n-1<n+1\le\psi(n)\le\sigma(n)$.
For positive ordered $X\le Y\le Z$, the ordered reciprocal-product bound
gives

$$
(X+Y+Z)(X^{-1}+Y^{-1}+Z^{-1})\ge5+2(R+R^{-1})
\quad\text{when }1\le R\le Y/X.
$$

The three mixed-power terms in Problem have this ordering. The mixed-power
comparison supplies $R=n(n+1)^{k-1}/(n-1)^k$. Substitution and exact field
normalization give the displayed source numerator and denominator.

## Falsifier

An exact integer pair $n\ge2$, $k\ge1$ violating the displayed inequality
would refute the source conjecture. No bounded prefix or restricted exponent
range is substituted for the universal claim.

## Evidence

The complete Lean statement is `claim4`, and `result4 : claim4` supplies its
proof in `D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5`.
The live consumer edges, written consumer → prerequisite, are
`result4 → prove4`,
`prove4 → ordered_reciprocal_bound, psi_ge, sigma_ge_psi, mixed_bound`, and
`ordered_reciprocal_bound → h_mono`.
The private auxiliaries organize the proof and have actual consumers.

The faithful Reg escape audit remains unfinished under
[#30221](https://github.com/the-omega-institute/trureturing/issues/30221);
no `declared_validated` mirror is claimed.

## Triage

### What the settlement shows

Conjecture 4 is proved over its full $n\ge2$, $k\ge1$ range, with every
source term, pointwise power, and reciprocal denominator retained. The
mechanism is the native arithmetic ordering, the mixed-power ratio lower
bound $n(n+1)^{k-1}/(n-1)^k$, and the ordered reciprocal-product comparison.

Every theorem in this derivation has `proof_shape: bind-only` after all
same-delivery helpers are inlined; `escape_witness: none`.
The endpoint's `admission_basis: open-problem-resolution` is the complete
externally named event preregistered in #30196. Consumed auxiliaries provide
proof organization, not an escape witness. This dossier addresses Conjecture 4
alone; it asserts no settlement of other conjectures in Part III and no
worldwide literature priority.

## ASSUMED-UNVERIFIED

The literature screen is bounded to the sources and repository states named
in #30196. Exhaustive coverage and global priority are unverified. The linked
Reg audit is unfinished and is separate from the exact mathematical theorem.
