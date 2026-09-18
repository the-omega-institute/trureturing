---
slug: perrier-mcf-period-one-generating-functions
bibkey: perrier2026periodicgeneratingfunctions
doi: 10.54550/ECA2026V6S4R33
url: https://ecajournal.haifa.ac.il/Volume2026/ECA2026_S4R33.pdf
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/PerrierPeriodicGeneratingFunctions.result
---

# Perrier's period-one generating functions

## Problem

Rachel Perrier, *Multidimensional Continued Fractions and Riordan Arrays*,
Enumerative Combinatorics and Applications 6:4 (2026), Section 5,
printed pp. 14-15, writes:

> The same method extends to higher dimensions.

> Assume period 1, so $m_{j,i}=m_j$ for $1\le j\le k-1$ and $i\ge0$.

With $r_1^{(-1)}=1$ and $r_{j+1}^{(-1)}=a_j$, the coordinate recurrences are

$$
r_1^{(n+1)}=r_k^{(n)},\qquad
r_{j+1}^{(n+1)}=r_j^{(n)}+m_jr_k^{(n)},\qquad 1\le j\le k-1.
$$

> We conjecture that solving these recurrences yields

$$
R_1(t)=\frac{(a_1-m_1)t^{k-1}+(a_2-m_2)t^{k-2}+\cdots+(a_{k-1}-m_{k-1})t+1}
{1-m_{k-1}t-m_{k-2}t^2-\cdots-m_1t^{k-1}-t^k}
$$

> and

$$
R_k(t)=\frac{t^{k-1}+a_1t^{k-2}+\cdots+a_{k-2}t+a_{k-1}}
{1-m_{k-1}t-m_{k-2}t^2-\cdots-m_1t^{k-1}-t^k}.
$$

The shifted convention is $R_j(t)=\sum_{n\ge0}r_j^{(n-1)}t^n$,
printed on pp. 8 and 12. Section 5 does not restate it for general $k$;
its opening sentence is read as retaining that convention.

The exact formal statement quantifies over every field `K`, natural `d`,
parameters `m a : Fin d → K`, and sequence `r : ℕ → Fin (d+1) → K`:
`Recurrence m a r → R r 0 = P m a * (D m)⁻¹ ∧ R r (Fin.last d) = Q a * (D m)⁻¹`.
Here `k=d+1`, Lean time `n` means source time `n-1`, and Lean coordinate
`j` means source coordinate `j+1`. The predicate contains exactly the
initial values and the two coordinate recurrences. The source's real
coefficients and integer period parameters are included by `K=ℝ`;
the additional case `d=0` has empty parameter sums.

## Motivation

The recurrence defines the multidimensional continued-fraction coordinate
sequences independently of the proposed rational expressions. Their
first and last shifted generating functions admit a uniform expression
in every dimension.

## Gap

The article proves its two- and three-dimensional cases and states the
general case as a conjecture. Preregistration #8627 identifies this first
conjectural sentence. The repository and pinned-Mathlib search found no
theorem for this general coordinate recurrence. Literature searches
reported in #8627 cover arXiv and OEIS; they do not establish exhaustive
historical priority. The author's 2023 thesis is an explicit boundary below.

## Route

Translate each coordinate recurrence coefficientwise into formal power
series. Multiply the successor-coordinate equations by `X^(d-1-j.val)`
and sum over `Fin d`. The two finite-sum decompositions telescope to
`R r (Fin.last d) * D m = Q a`. The first-coordinate equation and
`D m + X * Q a = P m a` give the other numerator. Since `D m` has constant
coefficient one, `PowerSeries.eq_mul_inv_iff_mul_eq` gives both quotients.

## Falsifier

A field, dimension, parameter pair, recurrence solution, coordinate
(first or last), and coefficient index where the stated rational series
has a different coefficient would falsify the corresponding identity.
The hypotheses are inhabited, for example with `K=ℚ`, `d=1`,
`m=0`, `a=1`, and `r n j=1`.

## Evidence

The mathematical evidence is the declaration
`D5/S1/Recurrence/Algebraic/PerrierPeriodicGeneratingFunctions.result`.
Its five definitions expose the recurrence, shifted series, denominator,
and two numerators. The Library note gives the source quotations and
verified DOI/PDF locators. The Scribe mirror states all four recurrence
clauses and both identities with the same index and time shifts.

## Triage

`theorem`; a first-tier externally named conjecture, preregistered in
#8627. `proof_shape: bind-only`, `escape_witness: none`,
`admission_basis: open-problem-resolution`. The only public theorem is
`result`; the module has no direct frozen-project prerequisites.
Its arbitrary-field, arbitrary-dimension statement is general algebra,
with no bounded enumeration, checker, numeric reduction, or certified
instance; the Lean utility classification is `none`.

## ASSUMED-UNVERIFIED

The author's 2023 Washington State University thesis was not retrieved —
whether it proves the general case is `ASSUMED-UNVERIFIED`.
Section 5 of the source does not restate the definition of R_j for general k —
the shifted reading is taken from printed pp. 8 and 12 via
"The same method extends".
The source's second sentence ("We further conjecture ... equation (7)")
is out of scope. The PDF footer's S2R33 differs from the DOI and filename's
S4R33; the DOI identifies the cited article.
