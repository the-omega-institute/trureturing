---
bibkey: bogartjimenezsalazar2026twolevel
authors: Tristram Bogart and Santiago Jiménez-Salazar
year: 2026
title: Strongly regular graphs, strongly polynomial sequences, and two-level polynomials
doi: 10.48550/arXiv.2609.32077
url: https://arxiv.org/abs/2609.32077v1
claim: "Question 3.19 asks for strongly polynomial graph families with constant depth and a degree function of positive degree."
strata_touched:
  - D5/S3/Combinatorics/ExtremalDensity/BogartJimenezSalazarConstantDepthHom
license: citation-only
triage: anchor
---

# Bogart–Jiménez-Salazar: two-level homomorphism polynomials

## Verified locator

DOI: 10.48550/arXiv.2609.32077

Source: https://arxiv.org/abs/2609.32077v1

The source is arXiv v1. Definition 1.1 and Definition 1.2 are on p. 2, Definition 3.2 on p. 9, and Question 3.19 on p. 14. The TeX title uses “graphs”; the arXiv metadata uses “graph”.

Question 3.19 states verbatim:

> More dramatically, do there exist strongly polynomial families G_q, H_n such that the depth function of hom(G_q, H_n) is constant while the degree function is a polynomial of positive degree?

Definition 1.1 states:

> A numerical polynomial is a polynomial g(x) ∈ ℚ[x] such that g(q) ∈ ℤ for every q ∈ ℤ.

Definition 1.2 states:

> Let g be an eventually nonnegative numerical polynomial, let S={q∈ℕ: g(q)≥0}, and let e:S → ℕ ∪ {−1,∞}.
>
> (a) A two-level polynomial of degree function g=g(q) and depth function e=e(q) is an infinite sequence of polynomials {f_q}_{q∈S}, with f_q(n) of degree g(q), that has the following property: writing f_q(n) = ∑_{r=0}^{∞}c_r(q)n^{g(q)−r}, where c_r(q)=0 if r>g(q), there exist polynomials {φ_r(q)}_{r≥0} such that, for every q∈S and every r ≤ e(q), we have c_r(q) = φ_r(q).
>
> (b) For q∈ℕ∖S, define f_q(n)=0 and e(q)=−1, extending the definition of f_q(n) to all q∈ℕ.

Definition 3.2 states:

> A sequence {G_n}_{n≥0} of graphs is strongly polynomial if, for every fixed graph F, there exists a polynomial p_F(n) such that hom(F,G_n)=p_F(n).

The formal assertion uses finite simple graphs on Fin-labelled carriers and counts all adjacency-preserving maps. The depth is maximal among uniform integer constants, as specified in [the problem statement](https://github.com/the-omega-institute/trureturing/issues/21296). A pointwise greatest depth function and maximality on every tail are separate statements.

The construction is G_q=K_{q+3,2} and H_n=K_{1,n,n}, with count

$$2n^2(n+1)^{q+3}+4n^{q+4}+2^{q+3}n^{q+3}+2n^2.$$

Its degree is q+5, and its first three codegree coefficients are 2, 2q+10, and (q+3)(q+2)+2^(q+3). The exponential obstructs a polynomial coefficient at codegree 2. Strong polynomiality follows by summing lift counts over proper colourings of each fixed finite source graph. This argument includes the empty source and parameter zero.

The experiment is in `the-omega-institute/trureturing-experiments`, commit `8c0c2a7aedd50a6cb26a93acf5640fb2c8f876ab`, at `docs/reports/bogart-jimenez-salazar-2026-strongly-polynomial-question-3-19/check.py`; SHA-256 `39c7624d5e37cb57b49922429df5a076c420dd2fcace3e80496a3a72b62c3ec2`. The recorded command `python3 check.py` exits 0 with `ALL_CHECKS_OK`; finite experiments are distinct from the universal Lean statement.

Literature completeness is **ASSUMED-UNVERIFIED**. The inspected source and the literature screen in issue #21296 leave the question open. The standard polynomial vertex-blow-up ingredient is literature-attested; no claim of a new general strong-polynomiality method is made.
