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
