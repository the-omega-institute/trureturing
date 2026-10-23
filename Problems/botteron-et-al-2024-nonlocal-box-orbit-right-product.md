---
slug: botteron-et-al-2024-nonlocal-box-orbit-right-product
bibkey: botteron2024nonlocalboxorbit
doi: null
url: https://arxiv.org/abs/2312.00725v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.result
---

# Right multiplication maximizes CHSH over the nonlocal-box orbit

## Problem

P. Botteron, A. Broadbent, R. Chhaibi, I. Nechita and C. Pellegrini,
*Algebra of Nonlocal Boxes and the Collapse of Communication Complexity*,
arXiv:2312.00725v3, Conjecture 15 (Dyck paths), ask:

> We conjecture that the same result actually holds without the tilde, i.e. the right multiplication $P^{\boxtimes k}$ gives the highest CHSH-value of $\mathrm{Orbit}^{(k)}(P)$, as observed numerically.

The source uses the wiring $\mathsf W_{\rm BS}$ and the domain
$\widetilde{\mathcal A}=\{P\in\operatorname{Conv}\{\mathrm{PR},\mathrm{SR},\mathrm I\}:\operatorname{CHSH}(P)\ge3/4\}$.
The orbit includes every full binary parenthesization of $k$ copies of $P$.
The right product multiplies each fresh copy on the right, so its parentheses
are left-nested. Botteron's thesis, arXiv:2510.09457, repeats the question as
Conjecture 6.11. The source definitions and their locators are in
[the Library note](../Library/QuantumBounds/botteron2024nonlocalboxorbit.md).

## Motivation

Theorem 13 bounds the tilted orbit under a distillation hypothesis. Bounding
the full orbit identifies the optimal parenthesization without that
hypothesis. Preregistration: [#15165](https://github.com/the-omega-institute/trureturing/issues/15165).
The settling declaration is
`D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.result`.

## Gap

The full orbit permits arbitrary parenthesizations, including those excluded
by the tilted-orbit restriction. Its comparison requires an order that
survives root rotations and subsequent multiplication.

## Route

Write $P=A(u,a)=a\mathrm{PR}+(u-a)\mathrm{SR}+(1-u)\mathrm I$.
Starting triangle coordinates satisfy $0\le a\le u\le1$. Directly expanding
the literal wiring gives

$$
(u,a)\star(v,b)=\left(uv,av+\frac{(1+u-2a)b}{4}\right),\qquad
\operatorname{CHSH}(A(u,a))=\frac12+\frac{u+a}{4}.
$$

Products preserve the larger region
$K=\{(u,a):0\le u\le1,\ 0\le a\le(1+u)/2\}$;
this does not assert closure of the starting triangle. The first coordinate
is associative. On $K$, rotating $X\star(Y\star Z)$ to
$(X\star Y)\star Z$ does not decrease the second coordinate. Multiplication
on the right by the starting box preserves the second-coordinate order when
the first coordinates agree. Structural induction straightens every tree
into the right product, giving the CHSH bound at the same leaf count.

## Falsifier

A transcription error in the four internal-bit sums or in the decoded
wiring changes the problem. A parenthesization with CHSH exceeding the right
product in the stated triangle would contradict the proved bound. Fin 2
addition implements XOR. The convention `rightPow P 0 = P` does not affect
the theorem because `orbit 0 P` is empty.

## Evidence

The kernel-checked declarations are in
`D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct.lean`.
`whole_triangle_max` bounds every member of the full orbit for every box of
the triangle. `result : claim` specializes it to the source's CHSH threshold
and depth guard. Their axiom closures are contained in
`{propext, Classical.choice, Quot.sound}`. Both have `proof_shape: content`
after same-delivery helpers are inlined, `escape_witness: none`, and module
`admission_basis: open-problem-resolution (#15165; Proved)`; utility is `none`.

Experiment entry:
[nonlocal-box right-product check](https://github.com/the-omega-institute/trureturing-experiments/tree/176b380e9ff17530e14ceb4b896e5cc65fd1f57f/docs/reports/botteron-et-al-2024-nonlocal-box-orbit-right-product).
The entry's `check.py` has SHA-256
`6f31d58efed171fec57acefa680b3d08e2d37f6a97429e9ecdae433a9007e2fc`.
Command: `python3 check.py`; exit 0. The coordinate product, CHSH formula,
associator identity and multiplication table checks return true;
parenthesization violations are 0 and `bad= 0`. The exact-rational tested
scope is every parenthesization for $2\le k\le9$ at 200 sampled triangle boxes,
and for $2\le k\le6$ at 2000 sampled triangle boxes. These finite readings are
computational evidence; the universal conclusion is supplied by Lean.

## Triage

### What the settlement shows

- **Mechanism — proved, kernel-checked declarations.** `prod_A` and `chsh_A`
  establish the polynomial coordinate map and CHSH expression from the
  literal wiring. `K_star` proves closure of the larger invariant region.
  `root_rotation` and `right_mono` supply the rotation inequality and
  right-monotonicity. `root_straighten` and `ceval_max` use structural
  induction to compare every parenthesization with the right product;
  `whole_triangle_max` transfers that comparison to CHSH. These helpers are
  private declarations in the settling module.
- **Strengthening — proved, kernel-checked public declaration.**
  `whole_triangle_max` holds on the whole
  $\operatorname{Conv}\{\mathrm{PR},\mathrm{SR},\mathrm I\}$ without
  $\operatorname{CHSH}(P)\ge3/4$, without the tilted $(k-1)$-orbit
  distillation hypothesis of Theorem 13, and including the one-leaf case.
  It bounds every orbit member; the zero-leaf case is vacuous.
- **Readings — computed, pinned experiment.** The experiment entry in
  Evidence checks the coordinate product, CHSH expression, associator,
  wiring table and every parenthesization in the two stated finite sampling
  scopes, with exit 0 and `bad= 0`. The sampled computation alone gives no
  uniform theorem beyond its scope.
- **Other wirings and boxes outside the triangle — open.** No declaration
  here gives maximality for either extension.
- **Exact maximum as a function of $k$ — open.** The theorem identifies the
  right product as an upper bound and the source's right product belongs to
  the nonempty orbit by its recursive construction. An explicit closed
  expression for its CHSH value is not established here.

For Theorem 13, the maximality conclusion extends from the tilted orbit to
the full orbit and no longer requires distillation. This comparison does not
prove that the CHSH value increases over the initial box, or that
communication complexity collapses; those implications retain their other
assumptions.

## ASSUMED-UNVERIFIED

The literature assessment of still-unsettled status is the source and later
paper search recorded in #15165, rather than a new exhaustive literature
survey. Escape audit unfinished:
[#15358](https://github.com/the-omega-institute/trureturing/issues/15358),
for both `whole_triangle_max` and `result`. Source-bound guarded
reconstruction, equivalence, variation, sensitivity and actual observational
dependence evidence have not been supplied; no Reg file or
`declared_validated` claim is delivered.
