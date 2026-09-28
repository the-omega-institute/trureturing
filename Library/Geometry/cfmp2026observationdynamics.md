---
bibkey: cfmp2026observationdynamics
authors: trureturing contributors
year: 2026
title: CFMP angle-incidence symmetry and Fibonacci discriminant observations
doi: null
url: https://github.com/the-omega-institute/trureturing/pull/9474
claim: Written angle-incidence realization criteria, primitive conjugate-channel kernel classification, and actual geometric face-pairing families with a persistent five-state observation ambiguity.
license: citation-only
triage: anchor
strata_touched: []
---

# Sources and scope for CFMP Sections 126–139

The source owner for this sequential continuation of the same CFMP goal is
`docs/develop/theory/CFMP_GEOMETRIC_REALIZATION_OBSERVATION_DYNAMICS.md`.
It follows the existing group-transport Sections 119–125 and leaves the four
preceding source volumes and all parallel Lean/Scribe/Reg/frozen files intact.
This is ordinary written mathematics pending independent review, not a new
kernel proof or a worldwide priority claim.

## Publication and inherited work

Sections 126–132 were previously delivered only as conversation files. They
are first committed in this continuation, with their historical publication
limitation corrected explicitly. The exact finite checker was rerun before
publication and is now in the branch as `cfmp_incidence_group_check.py`.
The current research baseline is `b61aaa2ffe5e1879b34a37248d7bc7a5ee8c0f59`.
The original PR description's 218-conclusion formalization gate is not
silently changed or claimed completed by this additional written material.

The previous main volume supplies the exact incidence map, strict-angle
framework and repeated named-type rule. Group-transport Section 119 supplies
the signed Gram determinant test for six positive independent cosh lengths.
The new angle-incidence group need preserve the actual edge fibres and local
vertex triples, but need not commute with face pairings. Uniqueness of the
volume maximizer makes it invariant under this larger action. A local
stabilizer image containing a three-cycle has no fixed flat opposite pair.

The actual seventeen-tetrahedron packet has ten edges of degrees 7,11,15,
five boundary components of genera (2,2,2,3,3), and six distinct actual labels
in every tetrahedron. Its face-pairing automorphism group is trivial, while
its angle-incidence group contains S3 x C2. The checker examines all 408
initial automorphism maps, eleven short obstruction witnesses, the full
face table and twenty independent link fans. The resulting three length
orbits reduce the genuine solution to two scalar equations. Existence and
uniqueness rely on the written geometric proof, not its floating root.

## Pinned Fibonacci source

The request's `FIBONACCI_ATOMIC_RELATION_GENERATION.md` was read on dev at
commit `409ac8ac7e6ea43a5afc318381b0af261543ca73`, blob
`734088bcd52f4f752593942f5ecda392bbc67ea8`. It did not exist on the checked
PR branch. This continuation links to that immutable source instead of
copying or overwriting a parallel source owner.

https://github.com/the-omega-institute/trureturing/blob/409ac8ac7e6ea43a5afc318381b0af261543ca73/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md

Sections 3,5,15 of that source supply the Fibonacci composition matrix,
unimodular two-time observation, the golden operation ring, conjugation
and norm. Section 17.5 leaves primitive conjugate-channel recovery at powers
of five open. The new Section 134 gives a complete written algebraic answer.
No existing GoldenInt code is treated as proof of this uncompiled bridge.

For h=c+d*theta, gcd(c,d)=1, N=c^2+c*d-d^2 and T=2*c+d,

`gcd(abs(N),abs(T)) is 1 or 5`,

and the ideal `(h,h*)` is R if 5 does not divide N, or `(2*theta-1)` otherwise.
The proof gives explicit Bezout coefficients and integral division by the
discriminant element. For every m>=2 the full R-valued two-channel map
`x -> (h*x,h* * x)` has zero kernel unless both 5|N and 5|m; in that case its
kernel is exactly

`{ t*(m/5)*(2+theta) : t in Z/5Z }`.

Its size is five even at arbitrarily high powers of five. Complete future
Fibonacci readings do not shrink this invariant kernel. A five-symbol
phase attains the exact additional-information lower bound. When 25|m,
reading the low coefficients modulo five cannot separate the hidden states;
a suitable high-block phase does. This does not assert collisions over the
exact characteristic-zero ring and does not conflate full ring outputs with
two selected scalar coefficients.

Section 139 records one explicit source-proof correction: the sentence in
Fibonacci 6.4 claiming that one of two consecutive indices above three is
divisible by three is false. The conclusion about the two adjacent prime
weight pairs remains valid using the even index and F_(2k)=F_k L_k. The
source on dev is not silently edited, and the erroneous step is not used.

## Exact connection to CFMP returns and noncommuting words

For the cyclic specialization of the existing Section 122 face table,

`C=[[2,-1],[1,2]]`, `M=[[0,1],[1,1]]`, `J=[[0,1],[1,0]]`, `W=J*M*J`.

The exact identities are `C=(2M-I)J`, `(2M-I)^2=5I` and `CW=MC`.
Thus the determinant-five observation is the golden discriminant operator
on swapped coordinates. It is injective with index-five image over Z,
while modulo m divisible by five it has kernel
`{t*(m/5)*(1,2):t in Z/5Z}`. All future output sequences have the same kernel.
The inputs are gluing parameters, not hyperbolic edge lengths.

The free-group Fibonacci automorphism u->uv, v->u has the same W on
abelianization. The normal closure of v^-1*u^2 and v^2*u has quotient C5,
with u->1,v->2 and Fibonacci acting by multiplication by three. The actual
ordinary boundary subgroup must not be replaced by that normal closure:
in the free group it has infinite index. Noncommutative word order is
additional information, not recovered by fixing the five-element quotient.

For N=5^k, k>=1, the five actual cyclic parameter pairs
`u_j=j*N/5`, `v_j=1+2*j*N/5` have identical return translations -1 and 2.
Every complete face pairing has two actual edges of degree 3N and one
boundary link (V,E,F)=(4,6N,4N), of genus N-1. Assigning the regular
hyperideal cosh length `cos(2pi/(3N))/(2*cos(2pi/(3N))-1)` gives a genuine
metric on each prescribed triangulation. The five coverings are distinct
only in the precisely stated category over the fixed local base framing.
No distinction of unmarked homeomorphism types is claimed. The base
projection ramifies at edges, so it is not called an ordinary unbranched
manifold cover. All future Fibonacci return observations still agree.
The familiar regular local formula is credited, not claimed new.

## Primary literature

Luo–Yang, *Volume and rigidity of hyperbolic polyhedral 3-manifolds*,
arXiv:1404.5365, Theorem 6.3, supplies the unique maximum and shared positive
generalized length input for Sections 127–130. Printed page 21 was inspected
as an image in the present run. Its flat possibilities remain part of the
input, and nearby prose using convex is not imported as volume convexity.

https://arxiv.org/pdf/1404.5365

Baake, Grimm and Joseph, *Trace maps, invariants, and some of their
applications*, arXiv:math-ph/9904025, is credited for the classical Fibonacci
substitution/trace-map setting. Goldman, *Trace Coordinates on Fricke spaces
of some simple hyperbolic surfaces*, arXiv:0901.1404, supplies the classical
three-trace background. Their abstracts were read in this run. Section 138
independently derives the required Cayley-Hamilton identities and uses full
traces, not the half-trace normalization of some papers. Neither source is
used to claim that an arbitrary trace triple realizes a CFMP holonomy.

https://arxiv.org/abs/math-ph/9904025
https://arxiv.org/abs/0901.1404

The historical source readings for Sections 126–132, including Joswig and
Regge literature, retain their original attribution in Section 132.
Elementary group actions, Bezout identities, covering-graph ranks and the
regular hyperideal formula are classical inputs. No exhaustive novelty
survey has been completed.

## Executed supplements and remaining scope

`cfmp_fibonacci_ramification_check.py` was run successfully. It checks 3920
primitive pairs, including 636 ramified ones; 3920 exact Bezout decoders;
180 complete finite-kernel cases over 29640 residue states; all return
fibres for moduli 2 through 80; 1365 free-word substitution cases; and 3375
integer Fricke-polynomial cases. Fifteen full actual face-pairing packets
cover all five phases at N=5,25,125, with independent oriented edge returns
and link fans. There are 240 additional Fibonacci phase-evolution checks.
These computations supplement, rather than prove, the universal results.

The prior incidence-group checker was independently rerun in the same
session before publication and retains its executed exact byte content.
No Lean build, project CI, Scribe projection, admission or Freeze was run.
No formalization or review status is changed. General CFMP, unrestricted
unpaired incidence, torus-end completeness, and unmarked classification
remain outside the proved written conclusions.
