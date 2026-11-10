---
slug: changshrock2005honeycomb
bibkey: changshrock2005toroidal
doi: 10.1016/j.physa.2005.08.076
url: https://arxiv.org/abs/cond-mat/0506274v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.result
---

# The degree-(L−1) eigenvalue of the toroidal honeycomb Potts transfer matrix

## Problem

S.-C. Chang and R. Shrock, *Transfer Matrices for the Partition Function of
the Potts Model on Toroidal Lattice Strips*, arXiv:cond-mat/0506274v1
(Physica A 364 (2006) 231–262), §V.C, p. 32:

> For the toroidal honeycomb strip with Ly = 4, one of the eigenvalues for degree d = Ly − 1, say that for j = 1, is given by
> λ_{T,hc,Ly,d=Ly−1,j=1} = x² (5.20)
> as for the corresponding cyclic strip. We conjecture that all of the toroidal strips of the honeycomb lattice have this eigenvalue. In terms of Potts model quantities these results are … λ_{Z,hc,Ly,Ly−1,1} = v^{2(Ly−1)}(v + q)² . (5.21)

Here $x=1+q/v$, and the transfer matrix is the paper's
$T_{Z,hc}=(VH_2)(VH_1)$ of eqs. (2.34)–(2.35), acting on labelled
connectivity states of the $L$ sites of a slice.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Potts weights $q$, $v$ | `Coeff := MvPolynomial (Fin 2) ℤ`, with `q = X 0` and `v = X 1` | Polynomial coefficients; no division |
| degree $d=L-1$ labelled connectivity states | `Space L`: the free module on the native states (arrangements of one unmarked symbol and $L-1$ distinct marks, or one cyclically adjacent marked double block) | Marks are labelled, as in the source |
| join, detach and the products $V$, $H_1$, $H_2$ | `join`, `detach`, `vertical`, `horizontal`, `transfer := (V*H₂)*(V*H₁)` | Literal operators of eqs. (2.34)–(2.35), including the cyclic seam |
| every toroidal honeycomb strip | every even width $L\ge2$ | The strip needs even $L$ |
| eigenvalue $v^{2(L-1)}(v+q)^2$ | `result`: ∃ w ≠ 0, `transfer L w = (v^(2*(L-1))*(v+q)^2) • w` | Eigenvector over ℤ[q,v] |

## Motivation

The settling declaration is
`D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalHoneycomb.result`. The
external assertion and its conventions are preregistered in
[issue #28063](https://github.com/the-omega-institute/trureturing/issues/28063).
The source note is `Library/Eigenstructure/changshrock2005toroidal.md`. The
transfer matrices compute the Potts partition function (equivalently the
Tutte polynomial) of toroidal honeycomb strips; each eigenvalue contributes a
term of the partition function, and this one fixes a factor of the
characteristic polynomial of the degree-$(L-1)$ sector for every width.

## Gap

The source verified the eigenvalue at $L=4$ only and stated the all-width
claim as a conjecture. The preregistration's bounded screen, including the
amplitude analysis of Richard and Jacobsen (math-ph/0608055), found no proof.

## Route

1. **Alternating vector.** In the degree-$(L-1)$ block, let
   $w=\sum_{\sigma\in S_L}\operatorname{sgn}(\sigma)\,e_\sigma$ over the
   all-singleton states. The identity arrangement has coefficient $1$, so
   $w\ne0$.
2. **Joins.** For a bond $(i,j)$, pair $\sigma$ with $\sigma\circ(i\,j)$: the
   two signs are opposite and the two join images coincide or vanish, so
   every join annihilates $w$, including the seam bond.
3. **Detaches.** On an all-singleton state the unmarked site contributes
   $v+q$ to the vertical product and every marked site contributes $v$, so
   $Vw=v^{L-1}(v+q)w$.
4. **Transfer.** Both horizontal layers fix $w$, hence
   $Tw=v^{2(L-1)}(v+q)^2w$.

## Falsifier

An even width $L$ for which the literal operator has no nonzero vector with
this eigenvalue would contradict `result`.

## Evidence

The kernel declaration is
`D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalHoneycomb.result`. Its
axiom closure is contained in `{propext, Classical.choice, Quot.sound}`. The
module imports only pinned Mathlib. The implementation seat reproduced the
source's $L=4$ eigenvalue and the $L=2$ case on the literal operator, and
matched the full $3\times3$ square-lattice matrix of eq. (6.2) at $q=3$,
$v=2$ entry by entry (seat-reported). The module checks in 20.5 s with a
peak resident set of 1.7 GiB including imports (seat-reported).

## Triage

1. **Proved (kernel-checked):** Chang–Shrock's conjecture for every even
   width, by `ChangShrockToroidalHoneycomb.result`.
2. **Proved (kernel-checked), internal:** the alternating vector is
   annihilated by every join and scaled by $v^{L-1}(v+q)$ by the vertical
   product.
3. **Proved (kernel-checked):** the square-lattice companion conjecture
   (5.18), for every width $L\ge2$, by
   `D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalSquare.result`.
   It reuses the same alternating vector and one full cyclic join layer
   per transfer step, with Potts eigenvalue $v^{L-1}(v+q)$.
4. **Open:** the multiplicities and amplitudes of this eigenvalue in the
   partition function.

### What the settlement shows

The eigenvalue comes from a fully antisymmetric vector in the all-singleton
part of the degree-$(L-1)$ block. Antisymmetry kills every bond that would
merge the unmarked site with a marked one, so the honeycomb bonds act as the
identity, and only the detach step, which closes the unmarked site's
component, contributes. The mechanism uses the structure of joins along
bonds and also supplies the square-lattice result in item 3.

## ASSUMED-UNVERIFIED

Literature completeness and worldwide priority are unverified. The bounded
screen in #28063 was carried out by the orchestrator and was not exhaustive.
The information-escape registration of `result` is unfinished
(`declared_unresolved`, IE-C050), recorded in issue #28118. No claim is made
about amplitudes, Klein-bottle strips or physical systems.
