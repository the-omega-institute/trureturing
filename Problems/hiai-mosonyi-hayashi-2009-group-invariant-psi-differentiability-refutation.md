---
slug: hiai-mosonyi-hayashi-2009-group-invariant-psi-differentiability-refutation
bibkey: hiaimosonyihayashi2009groupsymmetry
doi: 10.1063/1.3234186
url: https://arxiv.org/abs/0904.0704v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/GroupInvariantPsi/Result.result
---

# A corner in the group-invariant asymptotic overlap

## Problem

F. Hiai, M. Mosonyi and M. Hayashi, *Quantum hypothesis testing with group
symmetry*, J. Math. Phys. 50 (2009) 103304, Section 7, verbatim excerpt
with the indicated omissions:

> To get a complete solution of the problems of the Chernoff and the Hoeffding bounds and of Stein's lemma, … the key point is to show that (4.5) holds with equality … This can be done, for instance, … [by showing] that the function ψ exists and is differentiable on the interval (0, 1). As the examples of Section 6 suggest, one can expect the differentiability of ψ to hold in our setting of group-invariant state discrimination. The main open question of the present work is to show that this is indeed the case.

| Source object or quantifier | Formal reading |
|---|---|
| Finite-dimensional Hilbert space | Complex coordinate space of arbitrary dimension d |
| Compact group and unitary representation | Finite group G and a homomorphism into unitary complex matrices; finite groups with the discrete topology are compact |
| Faithful states | Positive definite matrices with trace one |
| Equation (2.1), tensor conditional expectation | `Defs.twirlPower`, the uniform finite-group Haar average of tensor conjugates, indexed by words `Fin n → Fin d` |
| Finite logarithmic overlap | `Defs.psiN`, the real logarithm of the real part of the trace of the product of CFC powers |
| Equation (3.1), asymptotic overlap | `Defs.psi`, the selected limit of `psiN / n`, with convergence at every s in (0,1) an explicit premise |
| Differentiability assertion | `Defs.claim`, universal differentiability on (0,1) under these premises |

Refuting this finite-group restriction with faithful states refutes the
compact-group assertion on its faithful domain.

## Motivation

Differentiability would provide a route to matching asymptotic hypothesis
testing bounds. A faithful finite-dimensional example tests this proposed
regularity without singular-state boundary effects.

## Gap

A finite maximum of smooth relative-orbit overlaps can have a corner where
two branches meet. Strict positivity of the density matrices does not remove
this competition between group elements.

## Route

Let G be the two-element group acting on four coordinates by
$\tau=(12)(34)$ and take

$$
p=(16,9,4,1)/30,\qquad q=(4,1,9,16)/30.
$$

Both diagonal matrices are positive definite and have trace one. For any
finite permutation action and positive diagonal inputs, define

$$
C_g(s)=\sum_i p_i^s q_{g i}^{1-s},\qquad M(s)=\max_g C_g(s).
$$

Writing $Z_n(s)$ for the trace overlap of the tensor twirls, the diagonal
mixture calculation and fractional-power subadditivity give

$$
\frac{M(s)^n}{|G|}\le Z_n(s)\le |G|M(s)^n\quad(0<s<1).
$$

Taking logarithms and dividing by n proves convergence to
$\psi(s)=\log M(s)=\max_g\log C_g(s)$. In the displayed example,
$C_\tau(s)=C_e(1-s)$ and $C_e(1/2)=7/10$. Differentiation gives

$$
(\log C_e)'(1/2)=\frac27\log\frac43,
\qquad
(\log C_\tau)'(1/2)=-\frac27\log\frac43.
$$

At a common value, the left slope of the maximum of two differentiable
branches is the smaller derivative and the right slope is the larger.
They therefore differ at 1/2.

For the parameter family $a>b>0$, put $A=a+1$, $B=b+1$,
$D=A^2+a^2+B^2+b^2$ and take
$p=(A^2,a^2,B^2,b^2)/D$, $q=(B^2,b^2,a^2,A^2)/D$.
The same reflection identity holds. At one half,
$C_e=(2a+1)(2b+1)/D$ and
$C_e'=2(h(a)-h(b))/D$, where
$h(x)=(x+1)\log(x+1)-x\log x$.
Since $h'(x)=\log((x+1)/x)>0$, the two slopes are distinct and equal to
$\pm2(h(a)-h(b))/((2a+1)(2b+1))$. This family calculation is a prose proof;
the Lean conclusion uses the explicit instance above.

## Falsifier

Differentiability at 1/2 would force the left and right difference quotients
to have the same limit. Their exact limits are negative and positive,
respectively, because $\log(4/3)>0$.

## Evidence

The endpoint is `D5/S3/Quantum/Information/GroupInvariantPsi/Result.result : ¬ Defs.claim`.
It has no hypotheses. Its principal dependencies are
`Mixture.twirlPower_diag`, `Mixture.trace_pow_diag`,
`Sandwich.sandwich`, `Sandwich.psi_eq_max` and `Result.one_sided_derivs`
in `D5/S3/Quantum/Information/GroupInvariantPsi/`.
The axiom closure is exactly `propext`, `Classical.choice` and `Quot.sound`.
Both convergence and limit identification in `Sandwich.psi_eq_max` and
both one-sided limits in `Result.one_sided_derivs` are used by the endpoint.

The proof route was derived with the assistance of the ChatGPT Pro model.
The source proves differentiability-free bounds and leaves differentiability
open. Mosonyi–Szilágyi–Weiner, arXiv:2011.04645, Remark IV.9 refutes the
separate $\psi=\psi^\circ$ conjecture. No answer to the differentiability
question was found in the searched scope, which includes those works,
Audenaert–Mosonyi arXiv:1401.7658 and Berta–Brandão–Hirche
arXiv:1709.07268. This scope is not an exhaustive citation-index survey.

## Triage

### What the settlement shows

1. **PROVED.** For the explicit four-level faithful pair and G acting by
   (12)(34), $\psi=\max_g\log C_g$ on (0,1) and is not differentiable at
   1/2. The one-sided derivatives are $\pm(2/7)\log(4/3)$.
   The Lean evidence is `Result.result`, `Result.one_sided_derivs` and
   `Sandwich.psi_eq_max`.

2. **PROVED.** For faithful diagonal states and permutation representations
   of a finite group, $\psi=\max_g\log C_g$ on (0,1), by
   `Sandwich.psi_eq_max`. For nonfaithful states, zero coefficients require
   separate boundary conventions; no broader Lean conclusion is asserted.

3. **PROVED in prose.** The full family $a>b>0$ has the two one-sided
   derivatives $\pm2(h(a)-h(b))/((2a+1)(2b+1))$, by the calculation above.

4. **COMPUTED.** The supplied type-class values of $n^{-1}\log Z_n$ at
   n=120 and s=0.3, 0.5, 0.7 are approximately -0.28251, -0.35093,
   -0.28251; the limiting values are approximately -0.28277, -0.35667,
   -0.28277. These numerical values are ancillary to the exact proof.

5. **OPEN.** Whether psi is differentiable for pairs commuting with the
   group action or for connected compact groups; whether the Chernoff and
   Hoeffding exponents nonetheless equal their single-letter formulas in
   this setting. These are boundaries of the Lean conclusion here, not claims that the questions are unresolved in the literature. For two individually invariant states, the twirl leaves every tensor power unchanged, so the usual single-copy overlap supplies differentiability for faithful states; that argument is not an additional Lean theorem here.

## ASSUMED-UNVERIFIED

The parameter-family argument is proved in prose, not as an additional
Lean theorem. The numerical values are supplied type-class computations,
not additional formal conclusions. Literature scope is limited to the
works listed above; completeness of the citation record is unverified.
