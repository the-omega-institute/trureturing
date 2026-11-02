---
slug: bajnok-beatty-original-conjecture-4-1
bibkey: bajnokbeatty2024cayleydiameteroriginal
doi: null
url: https://arxiv.org/abs/2406.04045v1
triage: theorem
motivation_gids:
  - D5/S3/FiniteGroups/BajnokBeattyAllRegimes
---

# The original Bajnok–Beatty Conjecture 4.1

## Problem

B. Bajnok and W. K. Beatty, *On the Diameter of Undirected Cayley Graphs of Finite Abelian Groups*, arXiv:2406.04045v1, Section 4, Conjecture 4.1:

> Let k and s be positive integers. The group Z2 × Z2k has an s-spanning set of size 2 if, and only if, one of the following holds:
>
> - s is odd and k ≤ (s² − 1)/2;
> - s is even and k ≤ (s² − s)/2;
> - s ≡ 0 mod 4, k is even, and (s² − s)/2 < k ≤ s²/2; or
> - s ≡ 2 mod 4, k ≡ 2 mod 4, and (s² − s)/2 < k ≤ s²/2.

The signed span consists of $xa+yb$ for integers $x,y$ with $|x|+|y|\le s$, including the zero coefficients. A set of size two is represented by two distinct elements $a,b$.

## Motivation

The target is the complete original iff under preregistration [#25489](https://github.com/the-omega-institute/trureturing/issues/25489). The low regimes and order bound are known Theorems 4.2–4.4 of the same v1. The top strip requires constraints for arbitrary pairs, together with constructions attaining the permitted parameters.

## Gap

A construction for a chosen pair does not exclude other pairs. The necessity theorem therefore quantifies over arbitrary pairs and uses their full relation lattice. The sufficient family is consumed only after the integer and parity conditions on its parameters have been established.

## Route

The formal endpoint is `D5.S3.FiniteGroups.BajnokBeattyAllRegimes.result`. Its assumptions are exactly positive natural $k,s$; its left side quantifies over two distinct elements of $\mathbb Z_2\times\mathbb Z_{2k}$ and all group elements with signed integer coefficients. The four right-side clauses are the doubled original inequalities, with the strict lower edge preserved in both top-strip cases. The cases $s=1$, $s=2$ and $t=s/2=1$ are included.

## Falsifier

A positive $k,s$ and a genuine two-element signed spanning set outside all four clauses would contradict the forward direction. Parameters inside a clause without such a set would contradict the reverse direction. A finite search alone cannot establish either universal direction.

## Evidence

The mathematical evidence is the compiled Lean declaration and its exact-statement and axiom report. The Blueprint describes the proof. The Reg mirror supplies compiled equivalence, variation, sensitivity and dependence proofs for the full original iff and its observed generating-pair predicate. Its producer assessment remains `declared_unresolved`: `IE-C050 ClosedTruthReadout`, `reason=unclassified_form`, `rule=source.observation_data`, tracked under [#25500](https://github.com/the-omega-institute/trureturing/issues/25500). The three exposed necessity helpers have `declared_validated` registrations. The consumed determinant/index supplier retains its separate unresolved `Int.natAbs` audit under [#25489](https://github.com/the-omega-institute/trureturing/issues/25489).

## Triage

- **Formally proved:** the original four-clause iff holds for every positive $k,s$. Necessity concerns arbitrary pairs, and sufficiency supplies genuine signed covers of the stated finite group.
- **Formally proved:** no positive $k$ admits radius one; the radius-two boundary includes $k=1$ in the low regime and $k=2$ in the top regime.
- **Literature-attested:** Theorems 4.2–4.4 already provide the order bound and low regimes. The quotient and cylinder arguments formalize these known facts rather than supply new literature claims.
- **Unresolved here:** classifications for other invariant-factor types or more generators are not asserted. The full statement addresses this two-generator rank-two family only.
- **Source boundary:** this settles the literal original statement in Lean, without asserting priority or the current status of revised publications.

## ASSUMED-UNVERIFIED

The comparison is to the literal original arXiv v1. Later versions, publications and a complete forward-citation inventory are not assessed. This formal result makes no claim of mathematical priority.
