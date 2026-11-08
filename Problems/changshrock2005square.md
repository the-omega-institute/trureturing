---
slug: changshrock2005square
bibkey: changshrock2005toroidal
doi: 10.1016/j.physa.2005.08.076
url: https://arxiv.org/abs/cond-mat/0506274v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalSquare.result
---

# The degree-(L−1) eigenvalue of the toroidal square Potts transfer matrix

## Problem

S.-C. Chang and R. Shrock, *Transfer Matrices for the Partition Function of
the Potts Model on Toroidal Lattice Strips*, arXiv:cond-mat/0506274v1,
§V.C, p. 32, equation (5.18):

> Concerning the λ's for degree d = Ly−1, we find that one of these is the same,
> independent of Ly, for the toroidal square strips we have calculated, namely
> λ_{T,sq,Ly,Ly−1,1} = x.
> This also appears for degree d = Ly − 1 in the case of the cyclic square-lattice
> strips, and we conjecture that all the toroidal square-lattice strips have this
> eigenvalue.

Equation (5.21) gives its Potts form $v^{L-1}(v+q)$. The literal operators
in (2.34)–(2.35) are $H=\prod_{i=1}^L(I+vJ_{i,i+1})$,
$V=\prod_{i=1}^L(vI+D_i)$ and $T=VH$, including $J_{L,1}$.
The coefficient ring is $\mathbb Z[q,v]$ and all $L\ge2$ are included.
At $L=2$ the two transverse bonds coincide and both factors are retained.

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| every width $L\ge2$ | `result (L : ℕ) (hL : 2 ≤ L)` |
| polynomial parameters | owner `Coeff`, `q`, `v`, with no specialization |
| degree $L-1$ labelled connectivities | owner `Native`, `State`, `Space` |
| all cyclic joins, seam included | `horizontal`, with `Fin.ofNat L (i.val + 1)` |
| native longitudinal product | owner `vertical` |
| $T=VH$ | `transfer := vertical L * horizontal L` |
| eigenvalue $v^{L-1}(v+q)$ | `∃ w ≠ 0, transfer L w = (v^(L-1)*(v+q)) • w` |

## Motivation

The declaration
`D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalSquare.result`
settles the assertion preregistered in
[issue #28163](https://github.com/the-omega-institute/trureturing/issues/28163).
The eigenvalue contributes to the degree-resolved transfer spectrum used
to compute the toroidal Potts partition function.

## Gap

The source states the all-width assertion as a conjecture. The bounded
literature screen in the preregistration found no proof; Richard and
Jacobsen, math-ph/0608055, treats amplitudes. Global openness and priority
are `ASSUMED-UNVERIFIED`.

## Route

Use the honeycomb owner's alternating singleton vector. Its identity
coefficient is one. The owner join theorem annihilates this vector for
every two distinct sites, so every square horizontal factor fixes it.
The owner vertical theorem scales it by $v^{L-1}(v+q)$. Thus $T=VH$
has the asserted nonzero eigenvector. No even-width premise is used.
The proof is bind-only reuse; its admission basis is the registered
external open-problem resolution, with no escape witness claimed.

## Falsifier

A width $L\ge2$ whose literal degree-$L-1$ operator lacks a nonzero
eigenvector for $v^{L-1}(v+q)$ contradicts `result`.

## Evidence

The mathematical statement is `ChangShrockToroidalSquare.result` in the
namespace above. It uses the native state space and join/detach maps
directly from `ChangShrockToroidalHoneycomb`; no replacement encoding is
introduced. The accepted kernel axioms are `propext`, `Classical.choice`
and `Quot.sound`.

The Reg proofs compile, but the source-bound audit is `declared_unresolved`:
`IE-C050`, `reason=unclassified_form`, `rule=source.coordinate_dependency`,
`site="missing=1;selected=#[0];scope=3"`. The proof of the width bound occurs
in the expanded `NeZero L` instance. The selected width coordinate alone
does not close that dependency. The same template limitation is recorded
in [issue #28118](https://github.com/the-omega-institute/trureturing/issues/28118).
This audit remains unfinished; the mathematical eigenvector theorem is
kernel-checked.

## Triage

1. **Proved (kernel-checked):** Chang–Shrock's square-lattice conjecture
   (5.18) for every width $L\ge2$, by `ChangShrockToroidalSquare.result`:
   the degree-$(L-1)$ toroidal square transfer matrix has the eigenvalue
   $v^{L-1}(v+q)$ (Tutte form $x$).
2. **Proved (kernel-checked), reused:** the honeycomb module's alternating
   vector, its annihilation by every cyclic join and its scaling by the
   longitudinal product; this lane makes those lemmas public at their owner.
3. **Open:** the second square eigenvalue (5.19), $y$ (Potts form
   $v^{L}(v+1)$), observed for $L=3,4$ only.
4. **Open:** amplitudes of these eigenvalues in the partition function, and
   the Klein-bottle strips.

### What the settlement shows

The square and honeycomb conjectures have one proof. The alternating vector
over the all-singleton states is killed by every join along a cyclic bond,
whatever the bond pattern, so any toroidal strip whose transverse operator is
a product of $(I+vJ_{i,i+1})$ factors fixes it, and the eigenvalue is the
longitudinal factor $v^{L-1}(v+q)$ raised to the number of longitudinal
layers per period: one for the square strip, two for the honeycomb strip.
The triangular strip, whose transfer matrix is built from width-$(L+1)$
operators and an identification, does not have this form, so the argument
does not transfer to it without a separate analysis.

## ASSUMED-UNVERIFIED

Literature completeness and worldwide priority are unverified; the bounded
screen of #28063 and #28163 was carried out by the orchestrator and was not
exhaustive. The information-escape registration of `result` is unfinished
(`declared_unresolved`, IE-C050), recorded in issue #28118. No claim is made
about amplitudes, the eigenvalue $y$, Klein-bottle or triangular strips, or
physical systems.
