---
slug: klobus-2016-chained-monogamy-realizability
bibkey: klobus2016communication
doi: 10.1007/s10701-015-9983-5
url: https://arxiv.org/abs/1408.1223v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.result
---

# Realizability of the correlators of boxes violating chained monogamy

## Problem

W. Kłobus, M. Oszmaniec, R. Augusiak, A. Grudka, *Communication strength
of correlations violating monogamy relations*, Found. Phys. 46 (2016)
620–634, arXiv:1408.1223v2, Section 5:

> Although we cannot prove it as in the case $M=2$, we conjecture that all
> possible values of the correlators in $S_{A\to BE}^i$ and
> $S_{B\to AE}^i$ that satisfy inequalities (\ref{ElPrat}) can always be
> realized with some signaling probability distribution $\vec{p}$ for which
> $R_M(\vec{p})=2M+\Delta$.

A box is a family $p(a,b,e|A_i,B_j)$ of distributions on $a,b,e=\pm1$,
$i,j=0,\dots,M-1$, with one setting $E$ for the third party, all one- and
three-party expectation values zero, and a common value of
$\langle B_0E\rangle_{A_i}$. $R_M=I^M_{AB}+2\langle B_0E\rangle$ with the
chained Bell expression $I^M_{AB}=\sum_k(\langle A_kB_k\rangle+\langle
A_{k+1}B_k\rangle)$, $A_M=-A_0$, and $\Delta\in[0,2]$. The coordinates are
$x_A^i=\langle B_iE\rangle_{A_i}$, $y_A^i=\langle B_iE\rangle_{A_{i+1}}$,
$x_B^i=\langle A_iE\rangle_{B_{i-1}}$, $y_B^i=\langle A_iE\rangle_{B_i}$
($1\le i\le M-1$), $x_B^0=\langle A_0E\rangle_{B_0}$,
$y_B^0=\langle A_0E\rangle_{B_{M-1}}$, and (ElPrat) is
$$\sum_{i=1}^{M-1}(-1)^{a_i}(x_A^i-y_B^i)+\sum_{i=1}^{M-2}(-1)^{b_i}
(x_B^{i+1}-y_A^i)+(-1)^c(y_A^{M-1}+y_B^0)+x_B^1+x_B^0\ge\Delta$$
for all $a_i,b_i,c\in\{0,1\}$.

## Motivation

The paper derives the monogamy relation $|I^M_{AB}|+2|\langle
B_0E\rangle|\le2M$ of nonsignaling boxes from three-variable inequalities
and reads a violation by $\Delta>0$ as forced signaling: the correlators in at
least one pair $S^i_{A\to BE}$, $S^i_{B\to AE}$ must differ, and each pair
defines a binary classical channel. The communication strength of the
violation is the least over violating boxes of the largest capacity of
these channels. The conjecture identifies the set over which this
minimization runs: the correlator vectors cut out by (ElPrat). The frozen
declaration
`D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.result` proves
it.

## Gap

Issue #12401 classifies the conjecture as Tier 1 and records the checks
made before any Lean:

- arXiv:1408.1223 v2 is the latest version and states the conjecture;
  Crossref, OpenAlex and INSPIRE report no citing work;
- results on monogamy of nonsignaling correlations (Toner,
  quant-ph/0601172; Augusiak–Demianowicz–Pawłowski–Tura–Acín,
  arXiv:1307.6390; Ramanathan–Horodecki, arXiv:1402.4453; Augusiak,
  arXiv:1611.00651) and on communication cost (Montina–Wolf,
  arXiv:1312.6290) fix aggregate Bell values of nonsignaling boxes, not
  every coordinate of a signaling box; a later account by W. Kłobus (2023
  summary of professional accomplishments, §4.3.3) gives a lower bound on
  the communication strength and no proof of the conjecture.

These are seat-reported and orchestrator-reported readings,
`not-found-in-searched-scope`; they do not establish exhaustive worldwide
novelty. The realizable correlator triples of three $\pm1$ variables with
zero odd moments form a tetrahedron; this is the $n=3$ case of
Huber–Marić, arXiv:1311.2002v2, Theorem 3, and of the cut polytope of
$K_3$ (arXiv:1706.06182v2, §4), and is used in step 1 of the Route.

## Route

1. For $|v|,|w|\le1$ and $-1+|v+w|\le u\le1-|v-w|$, the function
   $(1+ab\,u+ae\,v+be\,w)/8$ is a probability distribution with
   correlators $\langle AB\rangle=u$, $\langle AE\rangle=v$,
   $\langle BE\rangle=w$ and vanishing one- and three-party means.
2. Let $T=\sum_{i=1}^{M-1}|x_A^i-y_B^i|+\sum_{i=1}^{M-2}|x_B^{i+1}-y_A^i|
   +|y_A^{M-1}+y_B^0|$. Choosing every sign in (ElPrat) against its term
   gives $x_B^0+x_B^1-T\ge\Delta$.
3. Put $t=(2+\Delta+T)/(2+x_B^0+x_B^1)\in(0,1]$. At $(A_0,B_0)$ and
   $(A_1,B_0)$ take $(u,v,w)=(t\,x_B^j,x_B^j,t)$; at the other $(A_i,B_0)$
   take $(0,0,t)$; at $(A_i,B_i)$ and $(A_{i+1},B_i)$, $i\ge1$, the
   prescribed $(v,w)$ with $u=1-|v-w|$; at $(A_0,B_{M-1})$ the prescribed
   $(v,w)=(y_B^0,y_A^{M-1})$ with $u=-1+|v+w|$; and $(0,0,0)$ elsewhere.
4. The box realizes the coordinates, $\langle B_0E\rangle_{A_i}=t$ for all
   $i$, and $R_M=(2M-2-T)+t(x_B^0+x_B^1+2)=2M+\Delta$.

## Falsifier

The kernel-checked `result` states, for every $M\ge2$, every
$\Delta\in[0,2]$ and all coordinate sequences with values in $[-1,1]$ on
their index ranges that satisfy (ElPrat), that some box (indexed by
natural numbers, a probability distribution on `Bool × Bool × Bool` at
every setting pair with $i,j<M$) has vanishing one- and three-party means,
a common $\langle B_0E\rangle_{A_i}$, $R_M=2M+\Delta$, and the prescribed
coordinates. It reads $y_A^{M-1}=\langle B_{M-1}E\rangle_{A_M}$ at the
setting pair $(A_0,B_{M-1})$: $A_M=-A_0$ relabels the outcome of $A_0$,
which does not change a correlator of $B$ and $E$. The case $M\ge3$ is the
conjecture; for $M=2$ (ElPrat) differs from the paper's printed list (see
Triage).

## Evidence

Exact `Fraction` arithmetic (issue #12401): the box of Route step 3
realizes 1440 random admissible coordinate vectors with entries in
$\tfrac1{12}\mathbb Z$ for $M=2,\dots,7$ and
$\Delta\in\{0,\tfrac13,\tfrac12,1,\tfrac32,2\}$, checking nonnegativity,
normalization, the common $\langle B_0E\rangle$, all $4M-2$ correlators and
$R_M$; a box with one entry changed by $1/100$ is rejected by the same
verifier. On 15827 non-admissible samples the construction gives
$R_M<2M+\Delta$.

The canonical source is
`D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.lean`. Its
public declarations are `IsBox`, `OddMomentsVanish`, `corrAB`, `corrAE`,
`corrBE`, `chainR`, `ElPrat`, `CoordinateBounds`, `Realizes`, `claim` and
`result`; the outcome sign is the frozen
`D5/S3/Combinatorics/IsingUniquenessSets.sgn`. The frozen module state has statement identity
`sha256:457daf112b0653b47d2b60cd8593fed7c8f4c0b80f3970f0369a70f48cea1665`. The
result declaration has statement identity
`sha256:189745a8f3608dc5f2cf3c74b97968e0de7b0d9ee8126daa88b6ff6a30963cba`. The
Freeze event is
`sha256:29c7ef363071c78eeee2044226eeba96ec3dc9f0cc8cc7cb0aeffd286a53bf75`; its
project-level frozen prerequisite is the Freeze event of
`D5/S3/Combinatorics/IsingUniquenessSets`. The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 published conjecture; resolution `Proved` by
`D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.result`.
`proof_shape: content`; `admission_basis: open-problem-resolution` (issue
#12401). Utility kind `none` (a statement for every $M$, every $\Delta$ and
every admissible coordinate vector).

### What the settlement shows

- **Proved by `result`:** every coordinate vector in $[-1,1]^{4M-2}$
  satisfying (ElPrat) is realized by a box of the paper's class with a
  common $\langle B_0E\rangle$ and $R_M=2M+\Delta$, for all $M\ge2$ and
  $\Delta\in[0,2]$.
- **Proved inside the proof of `result`:** (ElPrat) implies the single
  inequality $x_B^0+x_B^1-T\ge\Delta$; the realizing box can be taken with
  $\langle B_0E\rangle_{A_i}=t=(2+\Delta+T)/(2+x_B^0+x_B^1)$.
- **Mechanism (read off the proof; not stated in Lean):** the setting pairs
  decouple. Each pair only has to realize a point of the correlator
  tetrahedron, and the only link between pairs is the common
  $\langle B_0E\rangle$. For fixed coordinates the largest $R_M$ is
  $2M+x_B^0+x_B^1-T$, attained with $\langle B_0E\rangle=1$, so (ElPrat) is
  exactly the condition that this maximum reaches $2M+\Delta$; since
  $x_B^0+x_B^1\le2$, also $t\ge\tfrac12$.
- **Follows from it (not stated in Lean):** with the paper's derivation of
  (ElPrat) as a necessary condition (l. 704–716), the set of coordinate
  vectors of $\mathcal P^M_\Delta$ is exactly the (ElPrat) polytope inside
  $[-1,1]^{4M-2}$, so the communication strength $C^M_\Delta$ is a
  minimization over this explicit polytope. At $\Delta=0$ the realizing
  box need not signal; for $\Delta>0$ every realizing box signals.
- **Checked by reading (orchestrator, issue #12401):** the paper's printed
  $M=2$ list (l. 468–471, labels niert1–niert4) has the signs of
  $x_A^1,y_A^1$ reversed in niert2 and niert3; the point
  $(x_A^1,y_A^1,x_B^0,y_B^0,x_B^1,y_B^1)=(1,1,1,1,1,-1)$ satisfies all four
  printed inequalities at $\Delta=2$ but has $x_B^0+x_B^1-T=-2$, so it is
  not realizable. (ElPrat) at $M=2$ is the corrected list.
- **Open here:** the value of $C^M_\Delta$ for $M\ge3$ (the minimization
  of the largest channel capacity over the polytope); whether the paper's
  reported values of $C_\Delta$ for $M=2$ were computed with the printed or
  with the correct inequalities (not checked); and the analogous
  realizability question when the common-value assumption on
  $\langle B_0E\rangle_{A_i}$ is dropped, as the paper does for $M=2$ at
  the end of Section 4.

## ASSUMED-UNVERIFIED

The literature checks do not establish worldwide priority; the 2023
summary by W. Kłobus and the Huber–Marić results are seat-reported
readings. The Lean kernel verifies the encoded statement and its axiom
closure; its correspondence to the paper, including the reading of the
class $\mathcal P$, of $R_M$ and of the setting $A_M=-A_0$, is checked by
reading the source and the definitions.
