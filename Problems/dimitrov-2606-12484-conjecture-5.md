---
slug: dimitrov-2606-12484-conjecture-5
bibkey: dimitrov2026c4c5
doi: null
url: https://arxiv.org/abs/2606.12484v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5.result5
---

# Dimitrov's Conjecture 5

## Problem

S. I. Dimitrov, *Lower bounds on expressions depending on the functions
φ(n), ψ(n) and σ(n), III*, arXiv:2606.12484v1, §2, PDF page 4,
Conjecture 5, asks whether the following inequality holds for every integer
$n\ge2$ and every integer $k\ge1$:

$$
\begin{aligned}
&\bigl(\varphi(n)^k(\psi(n)^k+\sigma(n)^k)
 +\psi(n)^k(\varphi(n)^k+\sigma(n)^k)
 +\sigma(n)^k(\varphi(n)^k+\psi(n)^k)\bigr)\\
&\quad\cdot\left(
 \frac1{\varphi(n)^k(\psi(n)^k+\sigma(n)^k)}
 +\frac1{\psi(n)^k(\varphi(n)^k+\sigma(n)^k)}
 +\frac1{\sigma(n)^k(\varphi(n)^k+\psi(n)^k)}\right)\\
&\qquad\ge
 \frac{10(n-1)^{2k}+7(n^2-1)^k+(n+1)^{2k}}
 {(n-1)^{2k}+(n^2-1)^k}.
\end{aligned}
$$

Here $\varphi$ is Euler's totient,
$\psi(n)=\prod_{p^e\parallel n}p^{e-1}(p+1)$ is Dedekind's function,
and $\sigma(n)=\sum_{d\mid n}d$ is the positive-divisor sum. Every power,
including those inside mixed sums and reciprocal denominators, is a
pointwise power of a function value. The preregistered source event is
[#30197](https://github.com/the-omega-institute/trureturing/issues/30197).

## Motivation

The settling declaration is
`D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5.result5`, whose source claim is
`claim5`. `Nat.totient`, the local Dedekind `psi`, and
`ArithmeticFunction.sigma 1` represent the three source functions.
The question compares the reciprocal product formed from all three
pointwise-power mixed terms over the unrestricted source range.

## Gap

The cited source states this exact lower bound as Conjecture 5. The bounded
literature and repository screen recorded in #30197 found no exact settlement
in its checked scope, including the fixed prior Dimitrov formalization
repository. That screen establishes no worldwide absence or priority claim.

## Route

Use $0<\varphi(n)\le n-1<n+1\le\psi(n)\le\sigma(n)$.
Apply the mixed-power comparison with exponent one to
$a=\varphi(n)^k$, $b=\psi(n)^k$, and $c=\sigma(n)^k$.
With $q=((n+1)/(n-1))^k$, the three source terms are ordered and the
second-to-first ratio is at least $R=(1+q)/2\ge1$.
The ordered reciprocal-product bound gives

$$
5+2(R+R^{-1})=\frac{q^2+7q+10}{q+1}.
$$

Clearing positive denominators and using
$(n^2-1)^k=(n-1)^k(n+1)^k$ yields exactly the displayed source bound.

## Falsifier

An exact integer pair $n\ge2$, $k\ge1$ violating the displayed inequality
would refute the source conjecture. No finite prefix, restricted exponent
range, or change in the pointwise-power convention replaces the original.

## Evidence

The complete Lean statement is `claim5`, and `result5 : claim5` supplies its
proof in `D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5`.
The live consumer edges, written consumer → prerequisite, are
`result5 → prove5`,
`prove5 → ordered_reciprocal_bound, psi_ge, sigma_ge_psi, mixed_bound`, and
`ordered_reciprocal_bound → h_mono`.
The private auxiliaries organize the proof and have actual consumers.

The faithful Reg escape audit remains unfinished under
[#30221](https://github.com/the-omega-institute/trureturing/issues/30221);
no `declared_validated` mirror is claimed.

## Triage

### What the settlement shows

Conjecture 5 is proved over its full $n\ge2$, $k\ge1$ range, with all
pointwise powers, reciprocal denominators, and the factor $(n^2-1)^k$
retained. The mechanism is the native arithmetic ordering followed by the
ordered mixed terms and the exact expression $(q^2+7q+10)/(q+1)$.

Every theorem in this derivation has `proof_shape: bind-only` after all
same-delivery helpers are inlined; `escape_witness: none`.
The endpoint's `admission_basis: open-problem-resolution` is the complete
externally named event preregistered in #30197. Consumed auxiliaries provide
proof organization, not an escape witness. This dossier addresses Conjecture 5
alone; it asserts no settlement of other conjectures in Part III and no
worldwide literature priority.

## ASSUMED-UNVERIFIED

The literature screen is bounded to the sources and repository states named
in #30197. Exhaustive coverage and global priority are unverified. The linked
Reg audit is unfinished and is separate from the exact mathematical theorem.
