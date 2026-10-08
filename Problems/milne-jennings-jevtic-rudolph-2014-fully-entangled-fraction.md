---
slug: milne-jennings-jevtic-rudolph-2014-fully-entangled-fraction
bibkey: milne2014fullyentangledfraction
doi: 10.1103/PhysRevA.90.024302
url: https://arxiv.org/abs/1404.3951v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.result
---

# The fully entangled fraction is at most one minus half the steering-ellipsoid centre

## Problem

A. Milne, D. Jennings, S. Jevtic and T. Rudolph, “Quantum correlations of
two-qubit states with one maximally mixed marginal”, Physical Review A 90,
024302 (2014), arXiv:1404.3951v2, Section V, Conjecture 2:

> Let $\rho$ be a general two-qubit state with $\mathcal{E}$ centred at $\vec c$. The fully entangled fraction is tightly bounded as $f(\rho)\leq 1-c/2$.

Here $f(\rho)=\max_{|\phi\rangle}\langle\phi|\rho|\phi\rangle$ over maximally
entangled $|\phi\rangle$ (Section III), $\mathcal E$ is Alice's steering
ellipsoid, and $c=|\vec c|$. The centre is given in the companion paper
S. Jevtic, M. Pusey, D. Jennings and T. Rudolph, Physical Review Letters 113,
020402 (2014), arXiv:1303.4724v2:
$\vec c=(\boldsymbol a-T\boldsymbol b)/(1-b^2)$, and $\vec c=\boldsymbol a$
when $b=1$.

## Motivation

`D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.result`
proves the conjecture in the strong form: $f(\rho)\le1-|\vec c|/2$ for every
two-qubit density matrix, and for every $t\in[0,1]$ some density matrix has
$|\vec c|=t$ and $f=1-t/2$. The bound comes from the operator inequality
`operator_bound`, $\rho\preceq(2-|\vec c|)(\mathbb 1\otimes\rho_B)$.

## Gap

The paper proves $f(\tilde\rho)\le(1+\sqrt{1-c})^2/4$ only for canonical
states $\tilde\rho$, whose Bob marginal is $\mathbb 1/2$ (Theorem 3), and says
the fully entangled fraction does “not transform straightforwardly under local
filtering operations”, so the canonical bounds “cannot therefore be used to
analytically derive bounds” for general states. The conjecture is restated as
Conjecture 6.5 in A. Milne's thesis “Quantum steering ellipsoids” (Imperial
College London, 2016, doi 10.25560/44111). Preregistration
[#14206](https://github.com/the-omega-institute/trureturing/issues/14206)
records the literature check: 39 distinct citing works (Semantic Scholar and
INSPIRE), the 25 on arXiv read in source and the other 14 by title and
abstract; the only mention is Ducuara, Susa and Skrzypczyk, arXiv:2406.03945
(PRA 110, 022435, 2024), which omits this conjecture. These are seat-reported
readings of a bounded search, not an exhaustive priority verification.

## Route

Write $\rho_B=\begin{pmatrix}p&q\\\bar q&r\end{pmatrix}$ with Bloch vector
$\boldsymbol b$, so $1-|\boldsymbol b|^2=4d$, $d=pr-|q|^2$.

1. **Canonical bound** (`canonical_bound`). If $\sigma\succeq0$ has Bob
   marginal $\mathbb 1/2$ and Alice Bloch vector $\boldsymbol a$, then
   $\sigma\preceq(1-|\boldsymbol a|/2)\mathbb 1$. For a vector $\phi$ with
   $t=\langle\phi|\sigma|\phi\rangle>0$ put $w=\sigma\phi$; Cauchy–Schwarz
   gives $\sigma\succeq ww^\dagger/t$ and $t^2\le\|\phi\|^2\|w\|^2$. With
   $\operatorname{rad}X$ the length of the Bloch vector of a $2\times2$
   Hermitian $X$ (a seminorm with $\operatorname{rad}Z\le\operatorname{tr}Z$
   for $Z\succeq0$), Bob's marginal gives
   $\operatorname{rad}(\operatorname{tr}_A ww^\dagger)/t\le1-\|w\|^2/t$; the
   two marginals of $ww^\dagger$ have equal trace and determinant, hence equal
   rad; Alice's marginal gives
   $|\boldsymbol a|\le2-2\|w\|^2/t\le2-2t/\|\phi\|^2$.
2. **Filtering** (`operator_bound`, case $|\boldsymbol b|<1$). With
   $u=\sqrt d$, $H=\begin{pmatrix}u&0\\-\bar q&p\end{pmatrix}$ and
   $G=\begin{pmatrix}p&0\\\bar q&u\end{pmatrix}$:
   $H\rho_BH^\dagger=pd\,\mathbb 1$, $GH=pu\,\mathbb 1$,
   $GG^\dagger=p\rho_B$, $H^\dagger H=p(\mathbb 1-\rho_B)$. The operator
   $\sigma=(\mathbb 1\otimes H)\rho(\mathbb 1\otimes H)^\dagger/(2pd)$ has Bob
   marginal $\mathbb 1/2$ and Alice Bloch vector $\vec c$, and
   $\rho=(2/p)(\mathbb 1\otimes G)\sigma(\mathbb 1\otimes G)^\dagger$.
3. **Degenerate case** ($|\boldsymbol b|=1$, $\vec c=\boldsymbol a$). The same
   Cauchy–Schwarz step and $\operatorname{rad}\rho_B=\operatorname{tr}\rho_B$
   force $\det W=0$ for the coefficient matrix of $w=\rho x$; then
   $|\operatorname{tr}A|^2\le\sum|A_{ik}|^2$ for the rank-one matrix
   $A=W\bar X^{T}$ gives $\rho\preceq\mathbb 1\otimes\rho_B$, and
   $|\boldsymbol a|\le1$.
4. **Maximally entangled vectors** have
   $\langle e|\mathbb 1\otimes\rho_B|e\rangle=1/2$.
5. **Tightness.** $\rho_t=(|\chi\rangle\langle\chi|+t(1-t)|01\rangle\langle01|)/(2-t)$
   with $\chi=|00\rangle+(1-t)|11\rangle$ has $|\vec c|=t$ and
   $\langle\Phi^+|\rho_t|\Phi^+\rangle=1-t/2$; at $t=1$ it is
   $|00\rangle\langle00|$.

## Falsifier

A two-qubit density matrix with $f(\rho)>1-|\vec c|/2$, or a value
$t\in[0,1]$ not attained, would refute the statement. Replacing the
Euclidean length by another norm, or the convention $\vec c=\boldsymbol a$ at
$|\boldsymbol b|=1$ by another limit, would answer a different question.

## Evidence

The public theorem `result : claim` is in
`D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.lean`, with
the public steps `canonical_bound` and `operator_bound`, the Blueprint Scribe
and the cited Library note. The statement quantifies over all positive
semidefinite trace-one complex $4\times4$ matrices; the fully entangled
fraction is the real supremum over all unit vectors whose two reduced states
are $\mathbb 1/2$; the centre uses the Euclidean length. The axiom closure of
`result` is $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

## Triage

Tier 1; Conjecture 2 is **proved in this module**. Admission basis
`open-problem-resolution` (#14206; Proved); `canonical_bound`,
`operator_bound` and `result` are content; the Cauchy–Schwarz step is Mathlib's
`inner_mul_inner_self_le` for the form of a positive semidefinite matrix, and
the Pauli matrices are the frozen `pauliMatrix`. Information-escape
registration is paused under CLAUDE.md §3.9.

### What the settlement shows

- **Proved** (`D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.operator_bound`):
  the operator inequality $\rho\preceq(2-|\vec c|)(\mathbb 1\otimes\rho_B)$
  for every two-qubit state, stated as
  $\langle x|\rho|x\rangle\le(2-|\vec c|)\langle x|\mathbb 1\otimes\rho_B|x\rangle$
  for every vector $x$. It is stronger than the conjecture, which only
  concerns maximally entangled $x$.
- **Immediate consequence of `operator_bound`** (not a Lean statement; the
  module states it only for maximally entangled vectors, inside the proof of
  `result`): if the Bob marginal $\operatorname{tr}_A|x\rangle\langle x|$ is
  $\mathbb 1/2$, then
  $\langle x|\mathbb 1\otimes\rho_B|x\rangle=\operatorname{tr}(\rho_B)/2=1/2$,
  so $\langle x|\rho|x\rangle\le1-|\vec c|/2$; the Alice marginal of $x$ is
  not used.
- **Proved** (`...SteeringEllipsoidFullyEntangledFraction.canonical_bound`): the
  decisive mechanism is an eigenvalue bound for canonical states,
  $\lambda_{\max}(\sigma)\le1-|\boldsymbol a|/2$. It rests on three facts:
  Cauchy–Schwarz $\sigma\succeq ww^\dagger/t$, the equality of the Bloch
  lengths of the two marginals of a rank-one operator (both are
  $\sqrt{\|w\|^4-4|\det W|^2}$), and $\operatorname{rad}Z\le\operatorname{tr}Z$
  for $Z\succeq0$. Unlike the fully entangled fraction, the largest eigenvalue
  is carried through local filtering exactly, because filtering by
  $\mathbb 1\otimes G$ maps the operator inequality
  $\sigma\preceq s\,\mathbb 1$ to $\rho\preceq 2s(\mathbb 1\otimes\rho_B)$.
- **Computed** (explicit algebra, not a Lean statement): put
  $s=\sqrt{1-c}\in[0,1]$, so that $c=1-s^2$ and $1-c/2=(1+s^2)/2$. Then
  $(1+s^2)/2-(1+s)^2/4=(2+2s^2-1-2s-s^2)/4=(1-s)^2/4\ge0$, with equality
  exactly when $s=1$. Hence the source's Theorem 3 value $(1+\sqrt{1-c})^2/4$
  is at most $1-c/2$, with equality only at $c=0$.
  So the canonical eigenvalue bound is weaker than Theorem 3 on canonical
  states, and by Theorem 3 every state attaining $f=1-c/2$ with $0<c<1$ is
  non-canonical, as for $\rho_t$.
- **Proved** (`...SteeringEllipsoidFullyEntangledFraction.result`): for every
  $t\in[0,1]$ some two-qubit density matrix has $|\vec c|=t$ and
  $f=1-t/2$, so the bound is sharp at every value of $|\vec c|$.
- **Immediate consequences of `result` and its proof** (not Lean statements):
  the witness in the proof is $\rho_t$ of Route step 5, a sum of two rank-one
  terms and so of rank at most two, and the value $1-t/2$ is taken on a phase
  multiple of $(|00\rangle+|11\rangle)/\sqrt2$. Since a bound
  $\rho_t\preceq\kappa(\mathbb 1\otimes\rho_B)$ gives $f(\rho_t)\le\kappa/2$,
  no constant $\kappa<2-t$ is possible: the constant of the operator
  inequality is sharp as well.
- **Open:** a characterization of all states attaining $f=1-|\vec c|/2$. Every
  inequality of the chain in Route step 1 must then be an equality; turning
  those equality cases into a classification is not done here.
- **Open:** the companion CHSH conjecture of the same paper and the
  $F_3$ conjecture discussed in arXiv:2406.03945. The transport step uses that
  the test operator $|e\rangle\langle e|$ is positive with Bob marginal
  $\mathbb 1/2$; CHSH operators are indefinite, so an operator upper bound
  $\rho\preceq X$ does not bound $\operatorname{tr}(\rho B)$, and filtering can
  change the CHSH value. The argument does not decide these conjectures.
- **Open:** qubit–qudit and qudit–qudit analogues. Equality of the spectra of
  the two marginals of a rank-one operator holds in every dimension, but
  $\operatorname{rad}$, its seminorm property and
  $\operatorname{rad}Z\le\operatorname{tr}Z$ are the qubit eigenvalue-gap
  calculus; an analogue of the centre bound beyond qubits is not formulated
  here.
- **Effect on the source:** Conjecture 2 becomes a theorem with the convention
  $\vec c=\boldsymbol a$ for $b=1$; Theorem 3 and the canonical-state analysis
  are unchanged; the “tightly” of the conjecture is witnessed by the explicit
  family $\rho_t$ rather than only by the numerics of Fig. 2.

## ASSUMED-UNVERIFIED

Literature-search completeness outside the scope recorded in #14206 is
unverified. The equality-case characterization and the higher-dimensional
analogues are open.
