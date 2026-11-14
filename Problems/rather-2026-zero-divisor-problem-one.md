---
slug: rather-2026-zero-divisor-problem-one
bibkey: rather2026zerodivisor
doi: 10.48550/arXiv.2606.04789
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.rather_problem_one
url: https://arxiv.org/abs/2606.04789v1
---

# Rather Problem 1: three-prime zero divisor independence polynomials

## Problem

Bilal Ahmad Rather, *Combinatorial and analytic aspects of independence
polynomials of zero divisor graphs*, arXiv:2606.04789v1, Problem 1,
printed page 24, asks:

> Problem 1. Let $I(\Gamma(\mathbb{Z}_{pqr}),x)$ be the independence polynomial of $\Gamma(\mathbb{Z}_{pqr})$, with primes $p<q<r$. Then prove that $I(\Gamma(\mathbb{Z}_{pqr}),x)$ is a unimodal and log-concave polynomial.

The settlement is **Proved** for every prime triple in that statement,
including $p=2$. The graph has the actual nonzero zero divisors of
$\mathbb Z/(pqr)$ as vertices; distinct vertices are adjacent exactly when
their product is zero. Its integer independence polynomial counts all
independent subsets of the entire vertex set.

Put $a=p-1$, $b=q-1$, $c=r-1$ and
$N=\max(ab+ac+bc,c+ac+bc)$. The theorem establishes $14\le N$,
independence number exactly $N$, an independent set attaining $N$,
positive coefficients at every index through $N$, zero coefficients above
$N$, log concavity at every natural index $k\ge1$, and a mode $m\le N$
with weak increase on all natural indices at most $m$ and weak decrease
on all natural indices at least $m$. Ties and the zero tail are included.
There is no cutoff on the primes, support size or coefficient index.

### Statement echo

| Source clause | Formal counterpart |
| --- | --- |
| Primes $p<q<r$, including 2 | Natural prime hypotheses and the two strict inequalities in `rather_problem_one`. |
| The actual residue ring graph | `Support.Vertex`, `Support.graph`, and `Support.crt` for `ZMod (p*q*r)`. |
| All independent vertex subsets | The native `IndependentPartitionDeletion.independencePolynomial` on `Finset.univ`; `coefficient_card` counts every independent subset of each cardinality. |
| Log concavity | The terminal inequality for every natural $k\ge1$, including the endpoint and tail. |
| Unimodality | A single natural mode with `MonotoneOn` on `Iic` and `AntitoneOn` on `Ici`, both in all natural indices. |
| Finite support | Attained independence number $N$, positive prefix and zero tail in the same terminal theorem. |

## Motivation

Problem 1 asks for both coefficient properties for an unbounded family of
native ring graphs. Theorem 4.1, printed pages 18–20, supplies the
three-prime support classification and counting formula. The result joins
that classification to uniform coefficient bounds, rather than to a
finite list of prime examples.

## Gap

The full problem and its conventions are preregistered in
[#29545](https://github.com/the-omega-institute/trureturing/issues/29545).
The bounded literature screen recorded there found no prior complete
settlement. It inspected the versioned source, related zero divisor and
independence-polynomial papers, and relevant general log-concavity and
unimodality results. Pure quasi-forest hypotheses do not cover all four
maximal independent-set sizes here; independent-domination polynomials
count a different family of sets. Literature-screen completeness and
publication priority remain **ASSUMED-UNVERIFIED**.

The paper's arbitrary-modulus Conjecture 1 is a separate open question;
this delivery settles only the complete original Problem 1.

## Route

The settling module is
`D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne`, with terminal
`D5.S3.Combinatorics.Graph.ZeroDivisor.RatherProblemOne.rather_problem_one`.
The support definitions identify the actual vertices and four disjoint
families of independent subsets after the Chinese remainder equivalence.
`independencePolynomial_three_coordinates` gives their native polynomial.
`nine_restriction_bound` and `normalized_second_difference_bound` feed
`coefficients_three_domains`; the terminal transports that result back to
the actual residue ring and applies the original `LogConcave` peak lemmas.

The admission basis is `open-problem-resolution (#29545; Proved)`.
All 22 authored propositions have `proof_shape: bind-only` after the
prescribed inlining, with no independent escape witness. All helpers
have actual consumers leading to the terminal; the other 11 retained
commands define the required objects. The two exposed original peak
lemmas retain their types and proofs.

## Falsifier

A prime triple $p<q<r$ whose actual zero divisor independence polynomial
violates a terminal coefficient inequality or has no such weak mode
would contradict the claimed result. Counting only maximal or dominating
independent sets, substituting a free support graph without a native
bridge, dropping $p=2$, or imposing a finite cutoff would fail the stated
correspondence.

## Evidence

The kernel-checked theorem is
`D5.S3.Combinatorics.Graph.ZeroDivisor.RatherProblemOne.rather_problem_one`.
Its axiom closure is contained in
`{Classical.choice, Quot.sound, propext}`. Its Scribe node carries one
`OpenProblemResolutionClaim` of kind `Proved`.

The 13-target escape audit remains unfinished under
[the linked issue disclosure](https://github.com/the-omega-institute/trureturing/issues/29545#issuecomment-6833325157).
The targets are the 11 public host theorems and the two exposed original
`LogConcave` lemmas. Faithful compiled original-source reconstruction,
lawful enrolled readout, whole-family variation/sensitivity and actual
observational dependence remain unfinished. No `declared_validated`
claim is made; this does not replace kernel or frozen-state validation.

## Triage

1. **Kernel-checked:** `rather_problem_one` settles both properties for
   every prime triple, including 2, with all independent subsets and no
   rank or prime cutoff. Its mode permits adjacent equal maxima and
   covers the whole zero tail.
2. **Kernel-checked:** the same terminal proves the exact attained
   independence number $N=\max(ab+ac+bc,c+ac+bc)\ge14$, not merely a
   support upper bound. The alternative singleton-family size is part of
   that maximum; replacing it uniformly by $ab+ac+bc$ loses the stated
   endpoint.
3. **Kernel-checked:** `configurations_four_families` and
   `independencePolynomial_three_coordinates` describe the support split
   and native counting identity. `coefficients_three_domains` proves the
   positive prefix, zero tail and strict interior log concavity used by
   the terminal. These statements explain how the source's counting
   formula supports its closing coefficient question.
4. **Kernel-checked:** `rather_problem_one` uses the original
   `increasing_before_max` and `decreasing_after_max` lemmas to obtain
   weak global unimodality. The boundary steps are handled by maximality;
   strict interior coefficient inequalities do not assert a unique mode.
5. **Open:** arbitrary moduli in Conjecture 1, repeated prime factors,
   and larger prime-support families have no settlement in this module.
   No earlier theorem of the source is invalidated or assumed false by
   this result; its Theorem 4.1 remains the counting input.
6. **ASSUMED-UNVERIFIED:** the bounded literature search in #29545 does
   not certify exhaustive coverage or publication priority. No new
   experimental or numerical evidence is claimed in this delivery.

## ASSUMED-UNVERIFIED

Literature-screen completeness and publication priority are unverified.
The escape audit is unfinished as specified above. The theorem does not
settle the source's arbitrary-modulus Conjecture 1.
