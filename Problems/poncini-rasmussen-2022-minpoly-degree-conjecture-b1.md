---
slug: poncini-rasmussen-2022-minpoly-degree-conjecture-b1
bibkey: poncini2023planar
doi: 10.1088/1742-5468/acdce7
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.result
url: https://arxiv.org/abs/2206.14462v2
---

# The minimal-polynomial degree of the dense-polymer Temperley–Lieb Hamiltonian

## Problem

X. Poncini and J. Rasmussen, *Integrability of planar-algebraic models*,
arXiv:2206.14462v2 (J. Stat. Mech. (2023) 073101). In §4.7, $l^{(n)}_{u^*,\beta}$
is the degree of the minimal polynomial of $h_{n,u^*}$ in $TL_n(\beta)$, and
eq. (4.69) chooses $h_0:=-\sum_{i=1}^{n-1}e_i$. Appendix B.1 tabulates
$l^{(n)}_{0,0}=2,3,6,9,18,27$ for $n=2,\ldots,7$ and states:

> **Conjecture B.1.** For n ∈ ℤ≥2, we have l^(n)_{0,0} = ½(3^⌊(n+1)/2⌋ + (−1)^n 3^⌊(n−1)/2⌋). (B.13)

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $TL_n(0)$ over $\mathbb C$ | `TL ℂ n`: the free module on planar perfect matchings of $2n$ boundary points, product by concatenation with each closed loop giving $0$, unit the identity diagram; `Ring` and `Algebra ℂ` instances | Literal diagram algebra; associativity, unit and loop-zero laws are proved |
| $h_0=-\sum_{i=1}^{n-1}e_i$ | `h ℂ n` | Standard cup–cap generators |
| $l^{(n)}_{0,0}$ | `(minpoly ℂ (h ℂ n)).natDegree` | Degree of the minimal polynomial in the algebra |
| (B.13) for all $n\ge2$ | `claim : Prop`, with the right-hand side computed in ℚ | Natural division for the exponents, as in the source |
| refutation | `result : ¬ claim` | At $n=9$: degree $\le57<81$ |

## Motivation

The settling declaration is
`D5.S3.StatisticalMechanics.PonciniRasmussenMinpolyRefutation.result`. The
external assertion and its conventions are preregistered in
[issue #27843](https://github.com/the-omega-institute/trureturing/issues/27843).
The source note is `Library/StatisticalMechanics/poncini2023planar.md`. $h_0$
is the Hamiltonian of the dense-polymer ($\beta=0$) loop model, and the degree
of its minimal polynomial is the number of independent powers of $h_0$, which
the source uses to express transfer matrices as polynomials in the
Hamiltonian.

## Gap

The source checked the formula for $n\le7$. The preregistration's bounded
screen found no proof or refutation.

## Route

1. **Diagram algebra.** Matchings compose by path-following through the glued
   middle boundary; composition is associative, and the internal-loop count
   satisfies a cocycle identity, so the loop-zero product is associative.
   Planarity is preserved, which gives a `Ring` and `Algebra` structure on
   the free module of planar matchings for every $n$.
2. **Certificate.** For $n=9$ (4862 basis diagrams), a monic integer
   polynomial $p$ of degree $57$, odd, with coefficients of at most $59$ bits,
   satisfies $p(h_9)\cdot1=0$ in the regular representation. This is checked
   by the kernel as a split Horner chain over the explicit generator action,
   in fifteen certificate parts.
3. **Bridge.** Since $1$ is the unit, $p(h_9)\cdot1=0$ gives $p(h_9)=0$, so
   `minpoly.min` bounds the degree by $57$, while (B.13) gives $81$ at $n=9$.

## Falsifier

A proof that the minimal polynomial of $h_9$ in $TL_9(0)$ has degree $81$
would contradict `result`.

## Evidence

The kernel declarations are
`D5.S3.StatisticalMechanics.PonciniRasmussenMinpolyRefutation.claim` and
`D5.S3.StatisticalMechanics.PonciniRasmussenMinpolyRefutation.result`; the
axiom closure of `result` is contained in
`{propext, Classical.choice, Quot.sound}`. The certificate modules check in
about 1777 s of kernel time in total, with a peak resident set of 6.6 GB on an
8-core Apple M3 (seat-reported).

## Triage

1. **Refuted (kernel-checked):** Conjecture B.1, by
   `PonciniRasmussenMinpolyRefutation.result`; the formula fails at $n=9$.
2. **Proved (kernel-checked), reusable:** the zero-fugacity Temperley–Lieb
   diagram algebra as a `Ring`/`Algebra` for every $n$, with associativity
   from `FiniteMatchingAssociativity.composite_assoc` and the loop-count
   cocycle.
3. **Computed (not kernel-checked):** $l^{(9)}_{0,0}=57$ exactly. An exact
   $57\times57$ integer Krylov minor of $h_9$ at the unit is nonzero, and the
   degree-57 annihilator is $\prod_E(t-E)$ over the $57$ distinct values
   $E=\sum_{j=1}^{4}\varepsilon_j\,2\cos(\pi j/9)$, $\varepsilon_j\in\{-1,0,1\}$
   (exact cyclotomic arithmetic in $\mathbb Z[z]/(\Phi_{18})$). The Lean result
   proves only the upper bound.
4. **Computed (lower bounds only):** at $n=8$ and $n=10$ the Krylov ranks of
   $h_n$ at the unit, modulo two primes, are $54$ and $162$, equal to the
   values of (B.13). A rank modulo a prime bounds the degree over $\mathbb Q$
   from below only; no annihilator of that degree was computed for these $n$,
   so the equalities there are unverified.
5. **Open:** the all-$n$ classification. The free-fermion picture predicts that
   (B.13) holds exactly when $n$ is a power of two, an odd prime, or twice an
   odd prime, and fails for every other $n\ge9$ because of cyclotomic
   collisions among the energies $2\cos(\pi j/n)$. This is a candidate for a
   separate registration.

### What the settlement shows

- **Proved (kernel-checked):** at $n=9$ the minimal polynomial of $h_9$ has
  degree at most $57$, strictly below the conjectured $81$; this is what
  refutes (B.13).
- **Computed (not kernel-checked):** the $57$ roots of that annihilator are the
  distinct values of the ternary sums $\sum_{j=1}^{4}\varepsilon_j\,2\cos(\pi j/9)$;
  the $81$ sums collapse to $57$ because
  $2\cos(\pi/9)=2\cos(2\pi/9)+2\cos(4\pi/9)$.
- **Open (conditional interpretation):** at $n=9$ the conjectured value $81$
  equals the number $3^4$ of ternary sums of the single-particle energies
  counted with multiplicity; whether the same match holds for every $n$ is
  not checked here. Reading (B.13)
  as a rational-independence criterion for these cosines needs a bridge not
  proved here: that $h_n$ at the unit is diagonalizable on its cyclic subspace
  with exactly these sums as eigenvalues, each occurring, for every $n$. With
  that bridge, (B.13) would hold exactly when the sums are pairwise distinct.
  Whether $n=9$ is the smallest failure is likewise open: for $n\le8$ only the
  values of item 4 and the source's own computations are available, and
  item 4 gives lower bounds only.

## ASSUMED-UNVERIFIED

Literature completeness and worldwide priority are unverified. The bounded
screen in #27843 was reported by the proposer and was not independently
re-run. The information-escape registrations of the 80 new public theorems
are unfinished, recorded in issue #28149. The all-$n$ classification in
Triage item 5 is a prediction, not a result.
