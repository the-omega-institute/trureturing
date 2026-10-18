---
slug: zhang-singh-pati-2017-subentropy-strong-subadditivity
bibkey: zhang2017subentropy
doi: 10.1016/j.aop.2016.12.024
url: https://arxiv.org/abs/1510.08859
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState
---

# Zhang–Singh–Pati: strong subadditivity of subentropy

## Problem

The question attributed to arXiv:1510.08859v2, §7.1 is recorded in
[zhang2017subentropy](../Library/Entropy/zhang2017subentropy.md).

> A similarly question can be asked for the strong subadditivity of subentropy: Q(ρ ABC) + Q(ρ B) ⩽ Q(ρ AB) + Q(ρ BC).

For every finite-dimensional tripartite density operator $\rho_{ABC}$, let
$\rho_{AB}=\operatorname{Tr}_C\rho_{ABC}$,
$\rho_{BC}=\operatorname{Tr}_A\rho_{ABC}$ and
$\rho_B=\operatorname{Tr}_{AC}\rho_{ABC}$. The proposed assertion is

$$
Q(\rho_{ABC})+Q(\rho_B)
\le Q(\rho_{AB})+Q(\rho_{BC}).
$$

The intended formal statement quantifies over arbitrary finite coordinate
types and the repository's `DensityState`; changing the parentheses of a
product coordinate type only relabels matrix entries. The original assertion
does not impose commutation, full rank, separability or purity.

## Motivation

Subentropy is a spectral information quantity whose subadditivity properties
are distinct from those of von Neumann entropy. The target is preregistered
in [issue #18958](https://github.com/the-omega-institute/trureturing/issues/18958).
The existing finite density-state interface provides the common state domain.

## Gap

A counterexample must use the paper's subentropy, including its extension to
repeated and zero eigenvalues, and the actual partial traces of one joint
state. A determinant-integral definition must therefore be connected to the
simple-spectrum formula and its continuous extension. The paper-level
counterexample below does not by itself supply these Lean proofs.

## Route

For a positive trace-one matrix $A$, use the proposed representation

$$
Q(A)=\int_0^\infty\left[
\frac{t}{1+t}-\frac{1}{\operatorname{Re}\det(I+t^{-1}A)}
\right]dt.
$$

On probability vectors, the kernel has the proposed bound
$0\le K_t(p)\le(1-p_x)/(1+t)^2$. The integrable dominating function
$(1+t)^{-2}$ supplies convergence and continuity. Partial fractions at
positive distinct eigenvalues give the spectral formula in
[datta2014subentropy](../Library/Entropy/datta2014subentropy.md); continuity
is needed at the counterexample's repeated and zero eigenvalues.

Sylvester's identity $\det(I+VW)=\det(I+WV)$ makes this integral invariant
under rectangular Gram conversion and isometric embedding. In particular,
pure states have value zero. These are required proof obligations of the
integral representation.

Take $A=B=C=\mathbb C^2$ and

$$
|\Phi\rangle=\frac{|00\rangle+|11\rangle}{\sqrt2},\qquad
\rho_{ABC}=|\Phi\rangle\langle\Phi|_{AB}\otimes I_C/2.
$$

Direct partial trace gives
$\rho_{AB}=|\Phi\rangle\langle\Phi|$, $\rho_B=I_2/2$ and
$\rho_{BC}=I_4/4$. The isometry $Jv=\Phi\otimes v$ gives
$Q(\rho_{ABC})=Q(I_2/2)$.

Writing $u_a(t)=(t+a)^{-1}$, the two kernels expand as

$$
K_t(I_2/2)=u_{1/2}(t)-u_1(t)-\tfrac14u_{1/2}(t)^2,
$$

$$
K_t(I_4/4)=u_{1/4}(t)-u_1(t)-\tfrac38u_{1/4}(t)^2
+\tfrac1{16}u_{1/4}(t)^3-\tfrac1{256}u_{1/4}(t)^4.
$$

Integrating reciprocal differences together, with
$\int_0^\infty(u_a-u_b)=\log b-\log a$ and
$\int_0^\infty(t+a)^{-k}dt=a^{1-k}/(k-1)$ for $a>0$, $k>1$, yields

$$
Q(I_2/2)=\log2-\tfrac12,\qquad
Q(I_4/4)=\log4-\tfrac{13}{12}.
$$

Consequently the left side minus the right side of the proposed inequality is

$$
2(\log2-\tfrac12)-(\log4-\tfrac{13}{12})=\boxed{\tfrac1{12}}>0.
$$

## Falsifier

One valid tripartite density state with strictly positive displayed gap
refutes the universal assertion. The Bell-pair product state above is the
specified witness. Failure of any claimed marginal identity, spectral
invariance, exact integral value or identification with the paper's
subentropy would invalidate this proposed certification route.

## Evidence

The explicit witness, kernel expansions and integration calculation above
give a paper-level refutation. They are not a compiled Lean certificate.
No theorem `result : ¬ conjecture` or completed formal faithfulness proof is
asserted by this dossier. The full Lean formalization and its required
checks remain outstanding.

## Triage

**SSA REFUTED at paper level, with exact gap $1/12$; formal certification
outstanding.** The witness is a Bell pair tensored with a maximally mixed
qubit. Its $AB$ marginal is pure; the $B$ and $C$ factors produce a strict
product subadditivity gap.

**Structural implication, proved here in prose and not Lean-certified.**
Let $F$ be invariant under isometric embeddings (hence under adjoining zero
eigenvalues) and vanish on pure states. If $F$ satisfied the displayed SSA
inequality for all finite tripartite states, it would satisfy product
superadditivity
$F(\sigma\otimes\tau)\ge F(\sigma)+F(\tau)$.
Indeed, purify an arbitrary $\sigma_B$ to $|\psi\rangle_{AB}$ and apply SSA
to $|\psi\rangle\langle\psi|_{AB}\otimes\tau_C$. Its $AB$ value is zero,
its global value is $F(\tau)$ by the isometry $v\mapsto\psi\otimes v$,
and its other two relevant values are $F(\sigma)$ and
$F(\sigma\otimes\tau)$. This proves the implication. For subentropy,
$\sigma=\tau=I_2/2$ violates that necessary consequence by $1/12$.
Isometric invariance across dimensions is a needed hypothesis; dependence
on a dimension-specific full spectrum alone does not supply it.

**OPEN — Datta et al. Conjecture 1, bipartite subadditivity**,
$Q(\rho_{AB})\le Q(\rho_A)+Q(\rho_B)$, pending stage 2 of the present
formalization. The counterexample's product spectra satisfy strict
subadditivity, so this refutation gives no counterexample to Conjecture 1.
No assertion about its present literature-wide status follows from this
local open proof obligation.

## ASSUMED-UNVERIFIED

The source quotation, version and section are supplied locators without an
independently available original source. The journal DOI, expanded author
names and bibliographic title have not been independently verified; see the
library note. No network search for subsequent settlements or worldwide
priority has been made. The integral's faithfulness, continuity,
isometric invariance, exact values and full witness-to-refutation bridge
are not claimed as compiled Lean results here.
