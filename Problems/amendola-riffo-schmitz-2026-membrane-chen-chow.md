---
slug: amendola-riffo-schmitz-2026-membrane-chen-chow
bibkey: amendolariffoschmitz2026membranes
doi: 10.48550/arXiv.2610.16724
url: https://arxiv.org/abs/2610.16724v1
triage: theorem
motivation_gids:
  - D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.refute_conjecture_6_10_v1
---

# The printed Chen–Chow conjecture for membranes

## Problem

Carlos Améndola, Gabriel Riffo and Leonard Schmitz, *Universal Varieties for
Signatures of Membranes*, arXiv:2610.16724v1, Conjecture 6.10, p. 32.

> For every sequence $s\in\bigoplus_{\ell=0}^{k}\bigoplus_{\nu\in\Sigma_{\ell}}(\mathbb{R}^{d})^{\otimes\ell}$ with entries satisfying the two-parameter shuffle identity (Theorem 2.10) there is a piecewise bilinear membrane such that its $k$-truncated signature coincides with $s$.

### Statement echo

- For each $d\ge 2$ and $k\in\mathbb N$, the real array has coordinates at
  all $\ell\le k$, all words on $d$ letters of length $\ell$, and all
  permutations of $\ell$ slots. The source uses one-based notation. Lean
  uses zero-based finite types.
- Theorem 2.10 uses Definition 2.6. For every ordered input pair
  $(u,\alpha),(v,\beta)$ of total degree at most $k$, the product of the
  two coordinates equals the printed sum. In Lean the finite degree
  indices satisfy the natural bound $m.\mathrm{val}+n.\mathrm{val}\le k$.
  At cutoff four the pair of degrees $(3,3)$ is excluded because $6>4$.
  In positive degrees the shuffles $\pi,\lambda$ independently preserve the order within each
  block. The output word is $(uv)\circ\pi^{-1}$ and the output rank is
  $\lambda\circ(\alpha\triangleright\beta)^{-1}\circ\pi^{-1}$. The
  empty basis pair acts as the unit on either side. When both inputs
  are empty, the right-hand side is the empty coordinate itself.
  Repeated summands retain their multiplicity.
- The realization is a single function on $[0,1]^2$, biaffine on every
  closed cell of some positive finite uniform rectangular grid.
  Definition 1.1 pairs $(s_j,t_{\tau(j)})$ in the product of native mixed
  partial derivatives, integrated over the product of two weakly
  ordered unit simplices. The signature has degree-zero coordinate $1$.
  Realization requires equality at every index of the array.

The literal implication is false even with an explicit requirement that
the input degree-zero coordinate equal $1$. [Preregistration #33507](https://github.com/the-omega-institute/trureturing/issues/33507) · [Versioned source](https://arxiv.org/html/2610.16724v1#S6.Thmtheorem10)

## Motivation

The conjecture asks whether the shuffle equations characterize the image
of the truncated signature map on piecewise bilinear membranes. Its
motivation includes Theorem 5.8. At cutoff two it places generic normalized
complex arrays satisfying the degree-two shuffle equations in the
Zariski-closed image of the truncated signature of piecewise bilinear
membranes of order $(d,d)$. Conjecture 6.8 proposes higher-degree
stabilization of signature varieties. [Literature note](../Library/HomologicalAlgebra/amendolariffoschmitz2026membranes.md)

## Gap

The scoped literature screen in #33507 checked arXiv version history,
publication indices, later references, the authors’ supplement, and the
repository issue and PR catalogues. It found v1 and no settlement or
correction of the literal Conjecture 6.10 in that scope. The separate
Conjecture 5.10 concerns complex dimension. [Preregistration #33507](https://github.com/the-omega-institute/trureturing/issues/33507) · [Conjecture 5.10 issue](https://github.com/the-omega-institute/trureturing/issues/26278)

## Route

On each open grid cell the native partial $\partial_s\partial_t X_c$
equals the coefficient of $st$. The sum of the corresponding cell
indicator functions gives a bounded measurable representative for each
component, with equality off the grid lines. The coordinate evaluation
$(s,t)\mapsto(s_j,t_{\tau(j)})$ pulls these null sets back to null sets
on each integration domain.

The product of the one-point and three-point integrals has four
insertion positions on each axis. The sixteen resulting chambers cover
the product domain up to null ties. In each chamber the old row slot
$j$ moves to $\pi(j)$ and its old column slot
$(\alpha\triangleright\beta)(j)$ moves to
$\lambda((\alpha\triangleright\beta)(j))$. Therefore the rank on that
chamber is $\lambda\circ(\alpha\triangleright\beta)\circ\pi^{-1}$.

Use the rational array in the Lean source at $d=2,k=4$. Entries whose
word contains the second letter vanish. Its degree-zero coordinate is
$1$. Kernel computation checks the 292 positive-degree ordered pairs.
The remaining 885 are the unit equations for arbitrary words and
permutations. At $(1,1),(111,231)$ the product and printed sum are
$19/4$. The genuine sum is $7/4$.

## Falsifier

A square membrane extends to an ambient function by assigning zero
outside the square. Conversely, every eligible ambient function
restricts to a square membrane satisfying the same closed-cell
conditions. Two extensions agreeing on the square agree locally at
every point of its interior. Their native mixed partials agree there,
and the boundary of the square is null under the paired coordinate
evaluations. Every signature coordinate is independent of the choice
of extension. Open-cell derivative calculations also show that
reversing differentiation order gives the same mixed coefficient
almost everywhere for these membranes.

The order of the permutations is determined by the column evaluation
$t_{\tau(j)}$ in Definition 1.1. The pair using $231$ detects inversion
because it is a three-cycle. The proof applies to arbitrary positive
finite uniform grids and requires every printed truncated relation,
including the empty-word cases.

## Evidence

Lean proves the closed negation under the name refute_conjecture_6_10_v1.
It uses only the standard axioms propext, Classical.choice and Quot.sound.
The rational comparisons use kernel reduction. The settling declaration
uses the complete finite certificate and the native integral identity.
[Lean source](../D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.lean)

## Triage

Tier 1 external conjecture. Resolution refuted for arXiv:2610.16724v1.
The utility is a certified instance refuting the closed printed claim.

### What the settlement shows

- **Proved.** The printed truncated equations with degree-zero
  normalization admit a nonrealizable array. The degree-$(1,3)$ native
  signature identity is the obstruction in the settling declaration.
- **By inspection of the source formulas.** For nonempty pairs of
  total degree at most three, each block has at most two slots, so
  each block permutation is its own inverse. The empty pair is
  governed by the unit rule. The specific inversion obstruction
  therefore first becomes available in total degree four. It leaves
  the degree-two statement of Theorem 5.8 outside its scope.
- **Open.** The realizability question for normalized arrays satisfying
  the genuine shuffle equations, including the forward $(1,3)$
  identity, remains open here. Conjectures 6.8 and 5.10 remain
  separate questions.

## ASSUMED-UNVERIFIED

The bounded literature check establishes a search scope for priority.
Conjectures 5.10 and 6.8 and the all-degree genuine-shuffle realizability
question remain open in this dossier.
