---
bibkey: biswas2026matchingtriples
authors: Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian
year: 2026
title: "Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples"
doi: 10.48550/arXiv.2609.08562
url: https://arxiv.org/abs/2609.08562v1
claim: "Classifies triples of patterns of length three up to shape-Wilf-equivalence and enumerates the perfect matchings avoiding each triple class except P1 = {123, 132, 213} and P13 = {132, 213, 321}; Section 6, Question 1 asks for these two enumerations."
strata_touched:
  - D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchings
  - D5/S3/Combinatorics/PatternMatchings/P13Correspondence
  - D5/S3/Combinatorics/PatternMatchings/P13Completions
  - D5/S3/Combinatorics/PatternMatchings/P13Counts
  - D5/S3/Combinatorics/PatternMatchings/P13Series
  - D5/S3/Combinatorics/PatternMatchings/P13CatalyticH
  - D5/S3/Combinatorics/PatternMatchings/P13HCoefficients
  - D5/S3/Combinatorics/PatternMatchings/P13Scalar
  - D5/S3/Combinatorics/PatternMatchings/P13Enumeration
  - D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge
license: citation-only
triage: anchor
---

# Biswas, Shankar and Sivasubramanian, matchings avoiding triples of patterns

The paper classifies all triples of permutation patterns of length three up to shape-Wilf-equivalence on Ferrers
boards and, through the Bloom–Elizalde correspondence between Ferrers-board transversals and perfect matchings,
enumerates the perfect matchings of [2n] avoiding each class. In the matching setting three arcs form an occurrence
of a pattern only when their three left endpoints precede their three right endpoints; Section 4, Figure 1 fixes the
labels (321 is the crossing (1,4),(2,5),(3,6), 123 the nesting (1,6),(2,5),(3,4)). The enumeration remained open for
P1 = {123, 132, 213}, with counts 1, 3, 12, 55, 271, 1400, 7471, 40841, and for P13 = {132, 213, 321}; Section 6,
Question 1 asks for both.

The module `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchings` answers the P1 clause with the generating
function (1 − zH)/(1 − z − zH), H = Σ Cat_k F_{k+3} z^k.

The module `D5/S3/Combinatorics/PatternMatchings/P13Correspondence` proves the structural bridge for P13:
for every n ≥ 0, actual P13-avoiding perfect matchings of Fin(2n) are in bijection with complete general-rank scans
accepted by explicit normalized S/T transitions. Post-closure base survivors and pending openings are separate.
Source labels {132, 213, 321} correspond to chronological closing words {231, 312, 123}. The equivalence includes
empty and disconnected matchings. The companion modules `P13Completions` and `P13Counts` now prove finite
continuation carriers, a forced-prefix and first-closure decomposition, and the triangular recurrence
`P13Counts.c_triangular`; `P13Counts.actualCount_continuation` transfers this recurrence to the actual matching
carrier. The explicit P13 enumeration below consumes these structural and continuation results.

The companion module `D5/S3/Combinatorics/PatternMatchings/P13Series` proves `P13.completion_functional_equation`
for the concrete catalytic series `F(u,z) = Σ_{d≥0}(Σ_{m=0}^d c(m,d)u^m)z^d ∈ ℚ[u][[z]]`, where `c(m,d)` counts
literal completions from an old single block of size `m`: `u` marks that size and `z` marks the `d` future closures.
The proved support is `c(m,d)=0` for `m>d`, with `c(m,m)=1`, so `[z^d]F` has `u`-degree at most `d`. Its `u^0`
coefficient is `A(z)=Σ_{n≥0}c(0,n)z^n=Σ_{n≥0}actualCount(n)z^n`, the ordinary series for the original P13-avoiding
perfect matchings of `Fin(2n)`, including empty and disconnected matchings. The finite triangular recurrence yields
`(u-1-z*u^2)*F = u-(1+z*u^2)*A+z*u^2*F(1/(1-z*u),z)`; the transformed marker is evaluated coefficientwise on
finite polynomials, with each resulting `z` coefficient a finite sum. This proves the functional-equation step only:
it does not supply an explicit `G`, prove `A=G`, give a closed all-n coefficient formula, or by itself complete P13. The all-size composition is given below.

## Repository-derived all-size P13 enumeration

Let $a_n=\operatorname{Nat.card}\{m : \mathrm{Matching}(n)\mid\mathrm{Avoids}(m)\}$,
where `Matching n` is the original ordinary perfect-matching carrier on `Fin(2*n)` and `Avoids` is the
source P13 condition. Put $A_{\mathrm{original}}(z)=\sum_{n\ge0}a_nz^n$. Empty and disconnected matchings
remain in this carrier; no connectedness, height or size cutoff is imposed.

All scalar expressions below belong to $\mathbb Q[[X]]$. Define

$$
\begin{aligned}
\delta&=(1-X)^2, & B_r&=\prod_{i=1}^{r}(1-X^i),\\
S_k&=\sum_{r=0}^{k}B_r^{-1}B_{k-r}^{-1}, & c_k&=(-1)^kX^{\binom{k}{2}}S_k,\\
v_j&=X^{j+1}\delta^{-1}, & [X^n]\Phi_j&=\sum_{k=0}^{n}[X^n](c_kv_j^k),\\
P&=\Phi_1, & R&=\Phi_2,\\
D&=\delta(1-2X-X^2)P-X^3(1+X)R, & G&=1+X(1-X)^3PD^{-1}.
\end{aligned}
$$

The empty product is one. Every inverse is a formal unit inverse: $B_r$, $\delta$ and $D$ have proved
constant coefficient one. The coefficient definition of $\Phi_j$ is a finite sum, independent of $a_n$.
Its evaluation representation follows from the term factorization and finite-degree vanishing;
`Phi_difference` is proved from these explicit series, not used to define them.

The actual catalytic transform $H$ has rows $h_k=[t^k]H$ and actual series
$A=A_{\mathrm{original}}(X/(1+X)^2)$. Its proved boundaries are

$$
\begin{aligned}
Xh_0&=(1+X)(A-1),\\
X^2h_1+(\delta-2X)h_0&=(1+X)^2-4XA,\\
X^3h_2+(\delta-2X^2)h_1+X(1-X)h_0&=0.
\end{aligned}
$$

The last term $X(1-X)h_0$ is essential. The actual bulk law at every $j\ge2$ discharges the scalar
`Bulk` contract; the uniformly proved minimal-solution identity at $j=2$ and `Phi_difference` at
$j=1$ complete the boundary elimination. They give $(A-1)D=X(1-X)^3P$ and hence $A=G$, cancelling
only proved units. No boundary law, Bulk premise, recurrence model, tail hypothesis or equality to $G$
is assumed about the matching carrier.

Let $C(z)$ be the rational image of Mathlib's Catalan series. The zero-constant substitutions
$\zeta(X)=X/(1+X)^2$ and $q(z)=C(z)-1$ satisfy the retained inverse direction
$\zeta(q(z))=z$. Lawful formal substitution composition therefore proves

$$
A_{\mathrm{original}}(z)=G(C(z)-1).
$$

The public generic Lagrange proof remains in its original `NonnestingOneThreeTwoTwo` owner and is
consumed both by that owner's original `result` and by `CatalanLagrangeBridge`. The arbitrary-series
coefficient transform then gives the exact unconditional formula

$$
a_0=1,\qquad
\forall n\ge1,\quad (a_n:\mathbb Q)=[X^n](1-X)(1+X)^{2n-1}G(X).
$$

These are repository-derived formal proofs for the P13 clause of Section 6, Question 1, Part I.
The BSS paper supplies the question, pattern convention and reported counts; it is not credited as
the source of this solution. The classical Lagrange identities are attributed to
[Gessel](gessel2016lagrange.md). Local proof verification and repository admission
are distinct from required CI or external acceptance. Required CI for the separate F delivery remains
pending; this all-size candidate has not been frozen, committed or submitted. No worldwide novelty,
unique credit, full-Question-1 resolution or official acceptance is asserted. Information-escape
registration remains suspended and unfinished and is not a premise of the proof.

In Fatima Hessas’s thesis [On generating functions associated to patterns](https://dspace.ummto.dz/server/api/core/bitstreams/776a19a2-c9b8-4af6-898e-46fa091e1c59/content)
(academic year 2023/2024), the inspected Theorems 3.1–3.2 concern ordinary matchings avoiding the single pattern 312
or listed class-I pairs; Theorem 3.3 concerns set partitions. These theorem scopes do not provide an exact ordinary
matching triple theorem for P13 = {132, 213, 321}.

## Verified locator

DOI: 10.48550/arXiv.2609.08562

URL: https://arxiv.org/abs/2609.08562v1

- Locator: Section 4 and Figure 1 (matching patterns); Section 6, Question 1; Table 2 (reported counts).
- Source carrier: `D5/S3/Combinatorics/PatternMatchings/P13Counts.lean`, `D5.S3.Combinatorics.PatternMatchings.P13.actualCount`; `P13Correspondence.lean`, `D5.S3.Combinatorics.PatternMatchings.P13.matchingEquiv`.
- Actual F: `D5/S3/Combinatorics/PatternMatchings/P13Series.lean`, `D5.S3.Combinatorics.PatternMatchings.P13.completion_functional_equation`.
- Actual H: `D5/S3/Combinatorics/PatternMatchings/P13CatalyticH.lean`, `D5.S3.Combinatorics.PatternMatchings.P13.CatalyticH.H` and `catalytic_H_equation`.
- Actual coefficient contracts: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.lean`, `D5.S3.Combinatorics.PatternMatchings.P13.CatalyticH.h_boundary_zero`, `h_boundary_one`, `h_boundary_two`, `actual_Bulk`, `h_minimal_solution`.
- Explicit scalar: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.lean`, `D5.S3.Combinatorics.PatternMatchings.P13Scalar.Phi`, `Phi_difference`, `W_uniform_dvd`, `minimal_solution`, `D`, `G`.
- Original Lagrange owner: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.lean`, `D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwo.lagrange_coefficient` and original `result`.
- Catalan recovery and coefficient transform: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.lean`, `P13CatalanLagrangeBridge.zeta_subst_q`, `q_subst_coefficient_transform`.
- Exact all-size result: `D5/S3/Combinatorics/PatternMatchings/P13Enumeration.lean`, `D5.S3.Combinatorics.PatternMatchings.P13.actual_A_eq_G`, `actualSeries_eq_G_subst_q`, `result`.

The bounded thesis inspection does not exclude an equivalent triple theorem elsewhere in that thesis.
The full text of Hessas, Goubi and Benkhemmou (IJMOR 32(3), 2025) remains unread; it cannot support
a priority or absence claim.
