---
bibkey: alaoglu1944highly
authors: Leonidas Alaoglu and Paul Erdos
year: 1944
title: On highly composite and similar numbers
doi: 10.2307/1990319
claim: The classical exchange argument assigns larger exponents to smaller primes in the factorization of a superabundant number; its local reciprocal geometric sum comparison is formalized here for arbitrary real bases greater than one.
strata_touched:
  - D5/S3/Arith/RobinExponentSwap
license: citation-only
triage: anchor
---

# On highly composite and similar numbers

Transactions of the American Mathematical Society 56 (3), 448-469.

The literature source is the classical nonincreasing-exponent argument for
superabundant numbers. The local exchange inequality compares products of
reciprocal geometric sums when two prime exponents are exchanged. The Lean
statement isolates this inequality and states its algebraic argument for all
real bases greater than one, without requiring primality. This real-base
formulation is an explicit generality choice, not a claim that the paper
states a separate theorem with precisely those real quantifiers.

This note attests the classical argument and its local factors. It does not
claim that this module proves the existence of a Robin counterexample, the
structure of every superabundant integer, or the Riemann hypothesis criterion.

Verified bibliographic locator: https://doi.org/10.2307/1990319.
Primary text: https://www.renyi.hu/~p_erdos/1944-03.pdf, section 2,
Theorem 1 and its proof, checked on 2026-09-06. That theorem states the
nonincreasing order of the prime exponents. Its proof compares a
superabundant number with the smaller number obtained by transferring one
prime factor, and uses the decrease of `(x^n - 1) / (x^n - x)` in the base
and exponent. This is the provenance of the exchange argument, rather than
a verbatim statement of the real-base full-swap inequality proved here.

## Verified locator

- DOI: https://doi.org/10.2307/1990319

## Initial prime support and a complete Fibonacci residue cover

The classical CA factorization and tied-price conventions are recalled in [Nicolas 2025, §3, (3.8) and Remark 3.1](../ArithSums/nicolas2025comparison.md), printed pp.10–11 of the inspected manuscript. The initial-prime support in the classical superabundant factorization also applies to every colossally abundant (CA) integer, including tied maximizers. For a price $\epsilon>0$, a CA integer $C$ maximizes $Z(n)n^{-\epsilon}$, where $Z(n)=\sigma(n)/n$. Any smaller integer with at least as large a value of $Z$ would strictly improve that objective. Thus $C$ is superabundant, and, writing $p=P^+(C)$,

$$
\prod_{q\le p,\ q\text{ prime}}q\mid C,
\qquad \vartheta(p)\le\log C.
$$

This uses the classical prime support, not an asymptotic formula for all CA exponents. It also follows directly by replacing an included larger prime with a missing smaller prime: the first local gain $1+1/q$ exceeds the removed marginal gain, which is at most $1+1/p$, and the size decreases.

Here is an application to the coverage obligation in the [FIB theory, §§205.2, 232.4 and 233.3](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md). Put $\phi=(1+\sqrt5)/2$ and, for all sufficiently large real $A$, choose one modulus for the whole band:

$$
r(A)=\max\{r\text{ prime}:r\le\log A/(2\log\phi)\},
\qquad m(A)=F_{r(A)}.
$$

The prime number theorem and Binet's formula give

$$
r(A)\sim\frac{\log A}{2\log\phi},
\qquad m(A)=A^{1/2-o(1)}.
$$

For every CA integer $C\in[A,2A]$, initial prime support gives $\vartheta(P^+(C))\le\log(2A)$. Ordinary PNT therefore gives, uniformly over those integers,

$$
P^+(C)\le(1+o(1))\log A
<2r(A)-1\sim\frac{\log A}{\log\phi}.
$$

The strict comparison holds eventually because $\log\phi<1$. By the already established rough-support fact in §205.2, every prime factor of $F_{r(A)}$ is at least $2r(A)-1$. Hence

$$
\gcd(C,m(A))=1
\qquad\text{for every CA }C\in[A,2A].
$$

For any fixed $0<\beta<1/2$, the modulus eventually satisfies $m(A)\ge A^\beta$. The existing §232.4 concentration result consequently applies, under its stated analytic inputs, simultaneously to all its reduced residues: its threshold is independent of the particular residue. Every CA integer in the band is included in its actual class $c\equiv C\pmod {m(A)}$. This covers the whole CA portion of the band; it does **not** place those integers in the special class $c=1$, or in the original fixed multiplier range for $1+F_r g$.

This is a classical-source application that clarifies coverage, not a new Robin estimate. A prime modulus of size comparable to $\sqrt A$ would give the same coprimality cover. Allowing every reduced residue introduces no additional restriction on these CA integers. Even if each class has at most one possible Robin violation, the union can retain every possible violation in the band.

In particular, choosing a residue after choosing a CA integer cannot by itself force that integer to lose relative to its own optimizing price. For every price $\epsilon$ at which $C$ is a global maximizer, the classical benefit

$$
\operatorname{Ben}_{C,\epsilon}(n)
=\log Z(C)-\epsilon\log C-\log Z(n)+\epsilon\log n
$$

is zero at $n=C$, and $C$ belongs to its own allowed residue. This observation does not identify that price with the prescribed moment price $1/(\log A\log\log A)$; the same-price comparison in §234 keeps that separate hypothesis. What remains necessary is a bound for the actual candidate in every relevant class, strong enough to cross its Robin budget. The residue cover supplies no such bound. No new formal declaration, Lean verification, or originality is claimed for this application.

There is also an exact restriction on the optional actual-envelope deficit in the [Nicolas comparison note](../ArithSums/nicolas2025comparison.md). For every CA integer $C$, including a tied maximizer at a positive price, the strict superabundant property above gives $\Sigma(C)=Z(C)$ for $\Sigma(x)=\max_{1\le n\le x}Z(n)$. Hence $D_C=\log(\Sigma(C)/Z(C))=0$. Restricting the maximum to the actual residue $n\equiv C\pmod m$ while retaining the cutoff $n\le C$ does not change this equality: the set still contains $C$ and is contained in the global comparison set. Thus a positive self-cutoff envelope deficit cannot provide the missing budget on the full CA test set. Such a deficit remains possible for other FIB candidates, but is not supplied by choosing a residue.

This conclusion depends on truncating at $C$; the larger-cutoff quantity $\log(\Sigma(2A)/Z(C))$ for $C\in[A,2A]$ is different and need not vanish. It also leaves the signed prime-error route in the Nicolas note intact: that sufficient comparison uses the available bound $d_C=0$ and still requires an independent estimate strong enough to cross Robin's budget. The equality here is a consequence of the already cited classical record property, not a new estimate, a Lean result or a proof of RH.
