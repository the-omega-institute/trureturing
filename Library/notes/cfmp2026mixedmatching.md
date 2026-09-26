---
bibkey: cfmp2026mixedmatching
authors: trureturing contributors
year: 2026
title: Sources and scope for the CFMP mixed-matching continuation
doi: null
url: https://github.com/the-omega-institute/trureturing/pull/9474
claim: A coupled transverse-angle inequality excludes flat blocks in a three-value mixed-matching metric, and role-balanced incidence promotes that obstruction to realization of a restricted minimum-six class.
license: citation-only
triage: anchor
strata_touched: []
---

# Source map: CFMP geometric realization, continuation Sections 65–69

The theory owner remains `docs/develop/theory/CFMP_GEOMETRIC_REALIZATION.md`.
The new continuation is stored in
`docs/develop/theory/CFMP_GEOMETRIC_REALIZATION_MIXED_MATCHING.md`.
This note is neither a published paper nor a priority certificate. The new
arguments are ordinary written mathematics, not new Lean declarations.

## Verified primary inputs

Costantino, Frigerio, Martelli and Petronio, *Triangulations of 3-manifolds,
hyperbolic relative handlebodies, and Dehn filling*, arXiv:math/0402339,
Conjecture 0.8. The external target concerns realization of the given
triangulation. The continuation retains the strictly hyperideal setting,
with every boundary component closed and of genus at least two.

https://arxiv.org/abs/math/0402339

Luo and Yang, *Volume and rigidity of hyperbolic polyhedral 3-manifolds*,
arXiv:1404.5365v2. Lemma 4.3 supplies the actual length-to-angle formula;
Propositions 4.4–4.5 and Lemma 4.6 give the classification over the whole
positive length domain. Theorem 6.3 gives the maximum-volume angle assignment
and a shared positive global length vector realizing it. Proposition 6.7
supplies the explicit concavity statement used in the averaging argument.
PDF images of printed pages 2, 21 and 22 were inspected. Nearby prose using
"convex" is not used as a volume-convexity assumption.

https://arxiv.org/pdf/1404.5365v2

Xinrong Zhao, *Combinatorial Ricci Flows and Hyperbolic Structures on a Class
of Compact 3-Manifolds with Boundary*, arXiv:2601.15174. On 2026-09-25 the
arXiv version history lists v3, uploaded 2026-09-24 at 14:11:01 UTC. Its
Theorems 1.1 and 1.5 still prove the general minimum-nine realization result;
Lemma 2.2 is the six-variable cosine formula. The earlier theory's references
to v2 are historical readings, not assertions that v2 is still latest.

https://arxiv.org/abs/2601.15174
https://arxiv.org/html/2601.15174v3

Feng, Ge and Hua, *Combinatorial Ricci flows and the hyperbolization of a
class of compact 3-manifolds*, Geometry & Topology 26 (2022), 1349–1384,
DOI 10.2140/gt.2022.26.1349, remains a credited source for the existing
co-volume/flow framework. No convergence theorem conditional on geometric
existence is used to assume the missing existence result.

https://doi.org/10.2140/gt.2022.26.1349

## What the continuation actually adds

For a tetrahedron with cosh lengths `(R,T,T,S,T,T)`, set
`Q=2*T^2/(R-1)` and `k=1-cos(theta)`, where theta is the R angle. The exact
formulas give

`S=(Q+1)*k-1`,

`cos(beta)^2=(Q+T^2)*k / (2*(T^2-1)+(Q+1)*k)`.

Under `R>=1+2*T`, `S>1` and `0<theta<=pi/5`, two decreasing rational
functions yield `0<cos(beta)<tan(theta/2)<1/2`, so `beta>pi/3`.
This is a continuous coupled estimate, not a supplied cosine premise or a
finite grid calculation. It is the live non-linear exclusion step.

If every tetrahedron has one of the two patterns

`C=(R,T,T,R,T,T)` or `D=(R,T,T,S,T,T)`,

all edge sums are 2pi, minimum degree is six, and one shared positive metric
really has these three typewise cosh lengths, the continuation rules out all
flat blocks without incidence balance. A hypothetical flat C gives an R
angle `theta=pi/b`, integer `b>=5`, in D. The transverse angle must be
`beta=2pi/n` for an integer n. The coupled bound forces n=5. The cases b=5
and b>=6 lie on opposite strict sides of 2pi/5, so neither is possible.
Colouring alone is explicitly not treated as proof of equal lengths.

For the positive realization theorem, actual edge classes have occurrence
counts R:(p,q), T:(u,v), S:(0,w), with positive integers p,q,u,v,w and
minimum degrees p+q,u+v,w at least six. The counting identity pv=2qu and
separate local-type averaging preserve every actual edge equation.
Concavity supplies a type-symmetric maximum, while genuine D blocks and
angle rigidity force the three common length values. This discharges, rather
than assumes, the equal-length premise in the exclusion theorem.

The explicit 11-tetrahedron packet has edge degrees (6,6,10,22,22), one
genus-seven vertex link, and counts (p,q,u,v,w)=(1,5,2,20,10). Its complete
face table and oriented normal circles occur in the theory. The topology is
checked using the actual face maps and link-vertex fans, not Euler
characteristic alone. Connected cyclic covers give an unbounded family;
no new census entry or newly discovered homeomorphism type is claimed.

The complementary local result constructs a complete cyclic degree-d edge
star with one flat pi occurrence and d-1 genuine occurrences of angle
pi/(d-1), with actual shared face lengths. The other faces and edge equations
are not completed. It refutes an isolated-star obstruction, not CFMP.

## Repository relationship and verification boundary

The existing role-averaging idea in theory Section 37, strict-angle
construction in Section 42, and exposed-edge obligation in Sections 61–64
are reused. The new mixed-type angle bound and exclusion are distinguished
from those inputs. Relevant CFMP PR search found #9474 and #8155; the latest
dev history for the original theory file still points to its earlier source
increment. These bounded searches do not establish worldwide novelty.

The supplementary script
`docs/develop/theory/cfmp_mixed_matching_check.py` verifies all 44 face slots,
22 pairings, odd permutations, color preservation, five actual edge classes,
first-return oriented edge circles, link data, role counts and exact rational
strict angles. The six rational substitution/derivative identities in the
analytic proof were also checked with Sympy during this continuation.
Finite checks and symbolic normalization do not replace the written
continuous proof, and no independent review is claimed.

No new Lean, Scribe, admission, frozen-state or CI result accompanies this
publication. Full CFMP, unrestricted minimum-six realization, arbitrary
unequal-length transverse stars and torus-end completeness remain open
obligations of the original research goal.

## Continuation on 2026-09-26: Sections 70–74

The preceding paragraphs describe the Sections 65–69 publication. This
appendix records the subsequent results in the same theory continuation.
The original strict-boundary setting and occurrence-counting conventions
are retained. There is no new named external conjecture and no claim of
worldwide mathematical priority.

### Additional primary source and exact index check

Roberto Frigerio and Marco Moraschini, *On volumes of truncated tetrahedra
with constrained edge lengths*, arXiv:1801.05326v3, 11 April 2019, Section
1.1, equations (1), (3), (4), printed page 6. The page image was inspected.
It gives the angle-to-length cosine formula whose denominator reads the
two endpoint VERTEX triples. The length-to-angle formula instead reads
FACE triples; a general nonsymmetric computation must not interchange
them. The paper's volume theorem under a lower-edge-length restriction
is not being imported as a minimum-six realization result or as an
unconditional bound on the angles used here.

https://arxiv.org/abs/1801.05326
https://arxiv.org/pdf/1801.05326

Theorem 6.3 and Proposition 6.7 of Luo–Yang were rechecked in images of
printed pages 21 and 22. Their common positive length realization and
local concavity are existing inputs. Michael Joswig's *Projectivities in
Simplicial Complexes and Colorings of Simple Polytopes*, arXiv:math/0102186,
was checked at record/abstract level as colouring background only. No
additional theorem is imported from an unread proof. The parity needed
below is proved directly by actual oriented endpoint transport.

https://arxiv.org/pdf/1404.5365
https://arxiv.org/abs/math/0102186

The Zhao arXiv record was checked again on 2026-09-26 and still lists v3.
The general minimum-nine statement does not directly apply to the new
six-degree examples. Repository CFMP PR search returned #9474 and #8155.
These readings are bounded provenance checks, not exhaustive novelty tests.

### New local estimates on six independent lengths

For a genuine tetrahedron, let the two vertex-angle sums at an edge be
at most sigma_1,sigma_2, both at most pi/2. The new written bound is

`ell < asinh(tan(sigma_1/2)) + asinh(tan(sigma_2/2))`.

At equal caps sigma the sharp supremum of cosh(ell) is
`(3-cos(sigma))/(1+cos(sigma))`. Thus two endpoint sums at most pi/2
force cosh(ell)<3. No two lengths need agree. The proof uses the positive
matrix `[[1,cos(theta)],[cos(theta),1]]`, its Cauchy–Schwarz inequality,
and the endpoint determinant factorization

`D=(cos(theta)+cos(a+b))*(cos(theta)+cos(a-b))`.

The angle family `(sigma-2eps,eps,eps,eps,eps,eps)` is genuinely realizable
for small positive eps and converges to the stated supremum. It is a
local sharpness family, not a globally glued metric.

A second bound allows a target angle and three adjacent angles at most
pi/5 and the fourth adjacent angle at most pi/3. It gives
`cosh(ell)<sqrt(237620/28431)<3`, without constraining the opposite angle
beyond genuineness. The two endpoint determinant lower bounds are
243/125 and 117/100; the numerator is less than 109/25. The constant is
not claimed sharp.

These bounds give a shared-length flat-candidate certificate: if both
selected pi labels have genuine occurrences satisfying either bound,
then both cosh values are below three. The existing flat inequality
`(r-1)(o-1)>4` is incompatible with that. This certificate needs neither
colouring nor role balance, but its qualifying angle witnesses must be
proved. Minimum degree alone does not supply them at every occurrence.

### Four-colour realization, with genuine transverse anisotropy

The new actual local patterns are `C=(R,A,B,R,A,B)` and
`D=(R,A,B,S,A,B)`. Global classes have per-edge (C,D) counts
R:(p,q), A:(u,v), B:(h,k), S:(0,w), all listed parameters positive.
The four degrees are at least six. These are still role-balance
hypotheses; the global theorem does not remove them.

Actual counting yields pv=2qu and pk=2qh. Merging R,S creates a global
rainbow three-edge colouring, so oriented normal-circle transport makes
all degrees even. Colour-preserving angle averaging retains each edge
equation. Genuine D blocks and local angle rigidity then determine
shared values R,A,B,S without requiring A=B.

All three possible flat C states are excluded. Flat R forces p=1,
q>=5 and u,h even; both R endpoint angle sums are at most 2pi/5, so
R<3, whereas flatness requires R>=1+A+B>3. Flat A forces u=1,
v odd and p divisible by four. A direct cosine subtraction gives
sign(beta-delta)=sign(A-B); flat A therefore puts its true D occurrence
in the four-small/one-medium angle window, contradicting A>3. The B
case is the same argument with the two transverse classes interchanged.

The complete 22-tetrahedron packet has degrees
(6,6,6,6,20,22,22,44), counts (p,q,u,v,h,k,w)=(1,5,2,20,4,40,20),
and one genus-fifteen vertex link. All its face permutations are EVEN;
a specified tetrahedron-sign assignment proves orientability. It must
not be justified using the older packet's odd-permutation argument.
The exact positive angle assignment has maximum corner sum 31pi/66.
Its realized lengths satisfy A>B: the angle equations imply
`(b-c)+10*(beta-delta)=pi/2`, and both differences have sign(A-B).
This establishes actual unequal transverse lengths, not only formal
permission to use two letters. Connected cyclic covers give 22n
blocks and Euler characteristic -14n, without claiming a new census type.

### Check and certification boundaries

The existing supplementary Python checker is extended, rather than
replaced by a numerical solver. It rechecks the old 11-block packet and
local star, then the new 44 face pairings, orientations, eight edge
classes, first oriented returns, all sixteen link-vertex fan cycles,
role counts and rational strict angles. The analytic checks use 2000
nonsymmetric angle vectors, 9202 applicable endpoint-cap tests, 1000
five-angle-window tests, two sharp-family sequences and 722 bounded
integer-parity cases. These tests do not prove the continuous or
unbounded statements; the written arguments do.

An additional authored Scribe Remark can describe this continuation
without referring to a new Lean declaration. Its presence is not a
Scribe compilation/projection receipt. There is no new Lean, admission,
Freeze, CI or independent review certification. General unequal-length,
non-role-balanced CFMP still requires constructing sufficiently many
qualifying endpoint witnesses or a valid nonuniform averaging method.
