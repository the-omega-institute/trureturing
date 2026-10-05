# FourCycle: the shared zero-curvature vector (paper-level closure)

This note isolates the remaining existence step after
`fourcycle_curvature_box`.  It uses one variable for each global edge; no
independent local copies or quotient/collar construction are introduced.

## Finite edge set is forced by the incidence hypotheses

Write `O = T × Fin 6` and `source(t,i) = edge t i`.  If `s` satisfies
`FourCycle`, then every `e : E` occurs in `source`: when `low e = true`,
`card (star s e) = 8`; otherwise `card (star s e) ≥ 12`.  Thus `source : O → E`
is surjective.  Since `O` is finite, `E` is finite as well.  Consequently the
rectangle below is a finite-dimensional compact rectangle, even though the
analytic theorem does not need a `[Fintype E]` argument as an extra
hypothesis.

## The local blocks are strictly admissible on the whole rectangle

Let `a_e = lower s e`, `b_e = upper s e`, and
`Ω = ∏_e [a_e,b_e]`.  The merged theorem
`fourcycle_curvature_box s hs` gives `Ω ≠ ∅`, and for every `x ∈ Ω` and every
occurrence `o`,

```
            -1 < localCosine s x o < 1.
```

Every coordinate of `Ω` is `> 1` (`5/4` for a low edge and `1+d` for a high
edge, with `d > 0`).  Hence each radicand

```
rad (x (coordinate o 0)) (x (coordinate o 1)) (x (coordinate o 5)),
rad (x (coordinate o 0)) (x (coordinate o 2)) (x (coordinate o 4))
```

is strictly positive (indeed `rad(u,v,w) ≥ 4` for `u,v,w ≥ 1`).  Zhao's
length-domain criterion (Proposition 2.4) says that a positive six-length
vector is a genuine hyper-ideal tetrahedron exactly when its six cosines lie
in `(-1,1)`.  Thus every block lies strictly in the geometric domain
throughout `Ω`; if `D_t>0` denotes the usual strict-domain predicate, this is
precisely `D_t(x)>0`.  (The merged Lean API names the criterion by the six
strict cosine inequalities rather than by a symbol `D_t`.)  In particular,
the argument never approaches a flat block or a square-root singularity.
Concretely, for each of the six target edges one may record the scalar
certificate

```
R^-_o R^+_o (1 - localCosine_o^2) > 0,
```

where `R^-_o,R^+_o` are the two radicands in the denominator of that target
cosine.  Both radicands are at least `4`, and
`1-localCosine_o^2=(1-localCosine_o)(1+localCosine_o)>0`.  This discharges any
equivalent local `D_t` determinant convention used for admissibility.

## Continuity of the shared curvature map

On the open set where all coordinates are `> 1`, the two radicands above stay
positive.  Polynomial operations, positive square roots, and division
therefore make `localCosine s · o` continuous on a neighbourhood of `Ω`.
`Real.arccos` is continuous on `[-1,1]` (and the displayed strict cosine
bound holds on `Ω`), so each local angle is continuous on `Ω`.  Since `star s e`
is finite,

```
K_e(x) = 2π - ∑ o ∈ star s e, angle s x o
```

is continuous for every `e`; hence `K : Ω → ℝ^E` is a continuous map.

## Finite Poincaré–Miranda from Brouwer

For a finite index type `E`, let `clamp_e(t) = max a_e (min b_e t)`.  If

```
x_e = a_e  ⇒  K_e(x) > 0,       x_e = b_e  ⇒  K_e(x) < 0,                 (†)
```

then the map

```
G_e(x) = clamp_e (x_e + K_e(x))
```

is a continuous self-map of `Ω`.  Brouwer on a finite product of intervals
(obtained from the merged simplex Brouwer theorem by the product-of-simplices
transport) gives a fixed point `x*`.  At a lower face, (†) makes
`clamp_e(a_e + K_e(x*)) > a_e`, contradicting `G_e(x*) = a_e`; the upper-face
case is identical.  Thus every coordinate of `x*` is interior, where the
clamp is inactive, and `G_e(x*) = x*_e` implies `K_e(x*) = 0` for every `e`.

This is the finite Poincaré–Miranda lemma in exactly the orientation needed
here.  The product transport is the only fixed-point API not already supplied
by PR #13070; no geometric input is hidden in this step.

## Independent co-volume closure (no product adapter)

There is a second paper-level route that avoids the finite-product Brouwer
port.  Put `I_e=[arccosh(a_e), arccosh(b_e)]` and
`\overline Ω_ℓ=∏_e I_e`.  Luo--Yang's extended tetrahedral co-volume is
`C¹` on all of `ℝ⁶`; summing it over tetrahedra and subtracting
`2π∑_e ℓ_e` gives a `C¹` global functional `H` on `ℝ^E`, with

```
                    ∂H/∂ℓ_e = −K_e(cosh ℓ).
```

The rectangle `\overline Ω_ℓ` is compact, so `H` has a minimizer.  If a
minimizer lies on a lower face, the box theorem gives `K_e ≥ η`, hence the
one-sided derivative in the inward `+ℓ_e` direction is at most `−η`; a small
positive step strictly decreases `H`.  On an upper face, `K_e ≤ −η`, and the
inward `−ℓ_e` step strictly decreases `H`.  Therefore a minimizer is interior,
where every derivative vanishes and `K_e=0` for all global edges.  The strict
cosine inequalities already proved on the box identify the generalized angles
in this gradient formula with the ordinary angles used in `K`.

This route requires only the standard extended-co-volume regularity and
gradient identity (Luo--Yang/Zhao); it does not assume a zero-curvature metric
or use a Ricci-flow convergence theorem.  A formal Lean development would
need those co-volume declarations instead of the product-PM adapter.

## FourCycle consequence

The merged box theorem supplies a single `η > 0` with

```
η = min(π,
        2π − 8 arccos(293/400),
        8 arccos(1577/2236) − 2π,
        12 arccos(37/43) − 2π),
```

```
x_e = a_e ⇒ K_e(x) ≥ η,
x_e = b_e ⇒ K_e(x) ≤ −η.
```

Applying the preceding lemma gives one shared vector `x : E → ℝ` such that

```
∀ e, a_e < x_e < b_e,
∀ t, D_t(x) > 0,
∀ e, ∑ o ∈ star s e, angle s x o = 2π.
```

Thus the actual FourCycle bottleneck—simultaneous strict block admissibility
and all global angle sums—is closed at the paper level by either route above.
A Lean completion still needs (i) either the finite-product
Brouwer/Poincaré–Miranda adapter or the extended co-volume API and (ii)
routine continuity/gradient lemmas; `fourcycle_curvature_box` already proves
the shared box, strict cosine domain, and uniform face margins.  No claim here
identifies the resulting zero-curvature vector with a complete manifold
realization unless the usual face-pairing and zero-curvature-to-metric
hypotheses are supplied separately.


# A counting obstruction to an all-flat minimum-valence angle structure

Consider a finite generalized angle structure on `N` tetrahedra.  Assume
every global edge has target angle sum `2π` and degree at least `d ≥ 6`.
Call a tetrahedron flat when its six local angles are
`(0,0,0,0,π,π)` up to the opposite-pair permutation, and let `F` be the
number of flat tetrahedra and `E` the number of global edges.

Each flat tetrahedron contributes exactly two local `π` occurrences.  A fixed
global edge can contain at most two such occurrences, because its total angle
is `2π` and all angles are nonnegative.  Counting flat `π` occurrences by
global edge gives

```
                 2 F ≤ 2 E,  hence  F ≤ E.
```

On the other hand, counting all local edge occurrences gives

```
                 6 N = Σ_e deg(e) ≥ d E,
```

so `E ≤ 6N/d`.  Therefore

```
                 F/N ≤ 6/d.
```

In particular, minimum valence eight forces at least one quarter of the
tetrahedra to be non-flat (`F ≤ 3N/4`), and minimum valence nine forces at
least one third to be non-flat.  This is a genuine exclusion of an all-flat
maximum-volume candidate, but it does not exclude isolated flat blocks; a
local perturbation or stronger incidence argument is still required for the
unrestricted minimum-eight problem.  It uses only nonnegativity, the global
`2π` equations, and degree counting, so it applies independently of a chosen
co-volume or fixed-point proof.

## Source anchors

- Zhao, arXiv:2601.15174v2, Propositions 2.4, 2.7 and 2.9 (domain, co-volume, and gradient):
  https://arxiv.org/html/2601.15174v2
- The merged analytic input is `D5.S3.Geometry.Hyperideal.FourCycleCurvature.fourcycle_curvature_box`.
