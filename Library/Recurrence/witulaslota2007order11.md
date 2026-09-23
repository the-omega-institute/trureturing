---
bibkey: witulaslota2007order11
authors: Roman Wituła; Damian Słota
year: 2007
title: Quasi-Fibonacci Numbers of Order 11
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL10/Slota2/slota99.pdf
claim: "The printed page-19 Problem asks whether all five order-eleven quasi-Fibonacci polynomials have degree n for every n at least 5."
strata_touched:
  - D5/S1/Recurrence/WitulaSlotaQuasiFibonacciOrderElevenDegree
license: citation-only
triage: anchor
---

# Quasi-Fibonacci numbers of order 11

Roman Wituła and Damian Słota define five polynomial sequences in
*Quasi-Fibonacci Numbers of Order 11*, Journal of Integer Sequences 10
(2007), Article 07.8.5. The paper lists no DOI and no arXiv version.

## Verified locator

- Source URL: https://cs.uwaterloo.ca/journals/JIS/VOL10/Slota2/slota99.pdf
- System (3.12) and initial values: printed page 5.
- Corollary 10: printed page 7.
- The substitution `Δ := 1/δ`: printed page 18.
- Problem: printed page 19, immediately after Corollary 20.

## Source statement

System (3.12), printed page 5, is

$$
\begin{aligned}
A_{n+1}(\delta)&=A_n(\delta)+2\delta B_n(\delta)-\delta E_n(\delta),\\
B_{n+1}(\delta)&=\delta A_n(\delta)+B_n(\delta)+\delta C_n(\delta)-\delta E_n(\delta),\\
C_{n+1}(\delta)&=\delta B_n(\delta)+C_n(\delta)+\delta D_n(\delta)-\delta E_n(\delta),\\
D_{n+1}(\delta)&=\delta C_n(\delta)+D_n(\delta),\\
E_{n+1}(\delta)&=\delta D_n(\delta)+(1-\delta)E_n(\delta),
\end{aligned}
$$

where

$$
A_0(\delta)=1,\qquad
B_0(\delta)=C_0(\delta)=D_0(\delta)=E_0(\delta)=0.
$$

Corollary 10, printed page 7, states:

> Since $\deg_\delta(\tau_m^n)=n$ for every $m=1,2,\ldots,5$, by
> $(3.2m)$ for $m=1,2,\ldots,5$ it can be easily deduced the following
> formula

$$
\max\{\deg A_n(\delta),\deg B_n(\delta),\deg C_n(\delta),
\deg D_n(\delta),\deg E_n(\delta)\}=n.
$$

The Problem on printed page 19 asks:

> Problem. Is it true that
> $$
> \deg A_n(\Delta)=\deg B_n(\Delta)=\deg C_n(\Delta)
> =\deg D_n(\Delta)=\deg E_n(\Delta)=n
> $$
> for every $n=5,6,\ldots$?

## Reading

The symbols $A_n(\Delta),\ldots,E_n(\Delta)$ denote the same five polynomial
families as $A_n(\delta),\ldots,E_n(\delta)$; Section 6 changes the variable by
the substitution $\Delta:=1/\delta$. The recurrence and initial values define
the polynomials over $\mathbb Z$. Degree is polynomial degree, with the zero
polynomial excluded by an equality to the natural number $n$. The quantifier is
over every natural $n\ge5$.

## Literature status

The paper leaves the displayed question as a Problem. The OpenAlex record lists
nine citing works. Four accessible full texts cite the paper without mentioning
this degree question. Two later papers could not be retrieved and remain
ASSUMED-UNVERIFIED. OEIS A062883, A189235, and A189236 contain no settlement;
MathDB has no entry for the question. Semantic Scholar returned HTTP 429 and is
ASSUMED-UNVERIFIED. These readings do not establish exhaustive publication
priority.
