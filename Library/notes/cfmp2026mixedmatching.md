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

## Continuation on 2026-09-26: Sections 75–80

The previous scope records remain historical descriptions of their own
increments. The new continuation stays in the same theory file and research
question. It supplies a written no-role-averaging realization theorem for
three actual global edges with two singleton-per-tetrahedron labels. It does
not claim unrestricted CFMP, independent peer review or new Lean certification.

### Classical inputs and DNA motivation

Frigerio–Moraschini, arXiv:1801.05326v3, Section 1.1 equations (1),(3),(4),
is the source of the inverse cosine formula. Its printed page 6 was inspected
again. Proposition 3.1's angle restrictions require a volume hypothesis;
that hypothesis is not silently removed or imported into the new local
estimates. Luo–Yang, arXiv:1404.5365v2, Theorems 1.4 and 6.3 supply the shared
positive generalized length realization and true/flat classification. The
new proof uses the existing strict-angle construction and flat Cauchy
inequality, without any new typewise averaging.

https://arxiv.org/html/1801.05326v3
https://arxiv.org/pdf/1404.5365

Goodman, Berry and Turberfield (2004), *The single-step synthesis of a DNA
tetrahedron*, DOI 10.1039/B402293A, reports four designed oligonucleotides
assembling into a tetrahedron with duplex edges. Goodman et al. (2005),
*Rapid chiral assembly of rigid DNA building blocks for molecular
nanofabrication*, DOI 10.1126/science.1120367, supplies further experimental
context on chirality, rigidity and linking. The authors' PubMed abstracts
were read. This motivates compatible paired data, not an assertion that
ordinary DNA consists of rigid tetrahedra or proves a hyperbolic theorem.

https://pubmed.ncbi.nlm.nih.gov/15179470/
https://pubmed.ncbi.nlm.nih.gov/16339440/

### New coupled local estimate and sharp unequal caps

For genuine angles (theta,a,b,g,c,d), put u=a+b and v=c+d. The new bound is

`cosh(ell12) < 1+2*sin(theta)^2/[(cos(theta)+cos(u))*(cos(theta)+cos(v))]`.

The proof uses an exact half-angle expression, replaces cos(g) strictly by
one, and bounds the two endpoint angle imbalances while preserving the SAME
central theta. It works over the whole genuine domain, including theta>pi/2.

For endpoint caps sigma1,sigma2<pi, let m=min(sigma1,sigma2),
M=max(sigma1,sigma2). The sharp supremum is

`1+2*(1-cos(m))/(cos(m)+cos(M-m))`.

The genuine family `(m-2eps,eps,eps,eps,eps,M-m+eps)` attains this in the
limit. Caps (pi/3,2pi/3) give the strict bound cosh(ell)<2. These are local
sharpness statements, not assertions that a limit family globally glues.

If the SUM of the two endpoint angle sums is at most pi, then cosh(ell)<3.
This permits one endpoint sum to exceed pi/2, so it strictly enlarges the
older coordinatewise condition. A logarithmic concavity calculation proves
this consequence. Every genuine occurrence of a common edge with cosh
length at least three therefore demands

`2*target_angle + sum(four_adjacent_angles) > pi`.

The individual-angle window also expands: the target and three adjacent
angles can be at most pi/5, with the fourth at most 7pi/15. The resulting
bound remains cosh(ell)<3; optimality of that separate window is not claimed.

### No-role-averaging capacity and a realized three-edge class

Let m_e count flat pi slots and g_e count genuine occurrences. Let mu_e(f)
be the maximum number of adjacent e slots at an actual genuine f slot.
The genuine-star demand gives the necessary condition for cosh(ell_e)>=3:

`g_e < 2*(2-m_e)+sum_f mu_e(f)*(2-m_f)`.

Actual multiplicities remain in the statement. They cannot generally be
set to one. If e occurs at most once per tetrahedron, the other genuine
angles are counted at most once, which makes the bound useful globally.

The new realization theorem assumes exactly three actual global edges
U,V,H, minimum degree six, the existing strict-boundary manifold hypotheses,
and at most one U slot and at most one V slot in each tetrahedron. No role
balance, fixed local templates, global automorphism or averaging is used.
The true/flat dichotomy first gives at most two flats. Singleton incidence
prevents U,V saturation; H appears in every genuine tetrahedron, so cannot
saturate either. Thus at most one flat remains.

At a selected singleton pi label e of this flat, at least five genuine
occurrences would require more than 5pi if its cosh length were >=3.
The actual total genuine angular mass gives at most 2pi+3pi=5pi.
Hence that cosh length is <3. A flat U,V pair contradicts the existing
product threshold. A flat e,H pair has at least three H zero slots and
forces `(x_e-1)*(s-1)>=4*sqrt(s^3*z)>4*s^(3/2)`, whereas x_e<3 makes its
left side smaller than 2s. Both cases are excluded.

The actual eleven-tetrahedron example changes only the Section 68 face
pair `(1,0;3,0;0132)` to `(1,0;3,0;0213)`. It has degrees (6,6,54), one
genus-nine link, and a unique `(U,H,H,V,H,H)` local type. It therefore is
not covered by the earlier sufficient condition that every actual label
type repeat at least twice. The original mixed-pattern theorem cannot be
applied by assigning H simultaneously to two disjoint colour classes.
Connected cyclic covers have 11n tetrahedra and Euler characteristic -8n;
their 3n global edges mean the cover argument uses metric lifting, not a
false claim that every cover still satisfies the three-edge hypothesis.
No new census/homeomorphism-type priority is asserted.

### New preprint and verification boundary

Huabin Ge, *Geometric ideal triangulations of hyperbolic 3-manifolds*,
arXiv:2609.27635v1, posted 2026-09-23, claims existence of a geometric
triangulation using compatible subdivisions. The primary text was read;
its introduction explicitly distinguishes the CFMP prescribed-triangulation
question. It is not treated as a proof of the same fixed minimum-six
triangulation, nor is independent verification of the whole new preprint
claimed. Its tetrahedral height quotient has dimension zero, illustrating
why same-vertex subdivision flexibility stops at the smallest 3-simplex.
This observation is background, not an input to the new realization proof.

https://arxiv.org/html/2609.27635v1

The extended checker preserves the earlier packet and analytic tests. New
checks cover all three edge cycles and six link-vertex fans of the (6,6,54)
packet; 3500 nonsymmetric genuine angle vectors and 21000 edge envelopes;
10281 combined endpoint caps, including 2972 outside the old separate caps;
1354 long-edge demands; four sharp-limit families; and 1000 enlarged-window
cases. The half-angle identity's maximum relative floating-point error was
about 5.46e-15. These computations supplement the continuous written proofs;
they are not kernel proofs, independent review or CI/Scribe/Freeze receipts.
The general multiple-occurrence capacity problem and unrestricted CFMP
remain unresolved by this increment. Bounded source searches do not prove
worldwide novelty of the new estimates or theorem.

## Continuation on 2026-09-26: Sections 81–87

Baseline `478f655d82e0aaff36f8a1f770544b2a36dd6f29` and its Sections 75–80
are retained. The current increment reuses their stronger coupled endpoint
bound and angular capacity, rather than duplicating the older separate-end
estimate in the preceding PR research comment. All results below are written
proofs pending independent review, with no new formal certification.

### Strict exposed-edge budget and a necessary small-area corner

For the entire nonempty flat set F, let f=|F|, m_e count pi slots and n_e
count all flat slots at an actual global edge. Set x_e=cosh(ell_e)>1 and
X={e:m_e=1, n_e in {1,2}}. The original Section 50 flat Cauchy inequality
and Section 61 occurrence budget now give the strict shifted product

`product_(e in X) ((x_e-1)^2 / x_e^(n_e-1)) > 16^f`.

The strictness comes from a positive omitted-edge remainder, proved using
sum m_e=2f and sum n_e=6f. A component-relative count is not substituted
for the entire-flat-set count. Some exposed edge must therefore have x_e>3.
This uses no role balance, colouring or length equality.

Combining the shared-length bound with a genuine target angle at most pi/g_e
forces one actual genuine endpoint sum above

`Phi_3(pi/g_e)`, where `Phi_B(t)=t+acos(sin(t)/sqrt((B-1)/2)-cos(t))`.

Here g_e>=4, so the sum exceeds 3pi/4 and its genuine truncated triangle
has area less than pi/4 in curvature -1. With one flat occurrence g_e>=5,
and the threshold exceeds 138.781389 degrees. This is a necessary
configuration, not yet a universal contradiction. The initial angle
assignment's caps cannot be transferred to the maximizer without proof.
The explicit surviving local six-star has r=4,t=5, one flat opposite
value 103/3, and five genuine opposite values (147-53sqrt(5))/12. Its
large corner sum is about 169.646598 degrees. Exterior faces and other
edge equations remain uncompleted, so it is not a CFMP counterexample.

### Length-weighted capacity

For B>=3, set Theta_B=acos((3-B)/(B+1)) and c_B=pi/Theta_B.
A genuine target edge with cosh length at least B must satisfy

`c_B*theta + a+b+c+d > pi`.

The proof uses the existing coupled bound and the concavity of
`acos(2/(B-1)-(1+2/(B-1))*cos(theta))` on its explicit domain.
Summing over genuine occurrences yields

`g_e < c_B*(2-m_e)+sum_f mu_e(f)*(2-m_f)`.

Multiplicity mu is retained. For B=3 this recovers the previous condition;
for B=7 the target coefficient becomes 3/2. An improved real bound need
not change every integer candidate's rounded capacity.

### Bounded-multiplicity realization and an actual new packet

The new theorem requires exactly three global labels U,V,H, minimum degree
six and the original genus-at-least-two boundary hypotheses. For some
r in {1,2,3}, each tetrahedron has at most one U slot, at most r V slots,
and at least three H slots. The sufficient degree threshold is

`d(V)>=5r+1`.

The r=1 case recovers the previous two-singleton theorem. For r=2, the H
quota is automatic and d(V)>=11 suffices. For r=3, the H quota remains an
explicit additional hypothesis, and the threshold is 16. No optimality of
these thresholds is asserted.

The proof first leaves at most two flats, then excludes all saturated
labels and leaves at most one. At a selected non-H pi label with local
multiplicity r_e, the genuine target-angle mass is pi and other genuine
mass is 3pi. Longness would require

`g_e*pi < 2*pi+(r_e-1)*pi+3*r_e*pi=(4*r_e+1)*pi`.

The degree and flat-multiplicity bounds give the reverse inequality. The
selected non-H cosh length is below three. The flat U,V pair then violates
the product threshold; a flat e,H pair has at least two H zero slots and
requires `(x_e-1)*(s-1)>4s`, incompatible with x_e<3. Thus every flat is
excluded without averaging.

Section 86 supplies all 22 face pairings of an actual eleven-tetrahedron
packet of degrees (6,12,48), with one genus-nine vertex link. V occurs
twice in four tetrahedra, including adjacent pairs; the previous two
singleton condition does not apply. There are six vertex-relabelled local
types, with the all-H type appearing only once. No census or worldwide
homeomorphism-type novelty is claimed. The metric lifts to connected cyclic
covers with 11n tetrahedra, 3n edges and Euler characteristic -8n; the
three-edge theorem is not falsely reapplied to their larger edge sets.

### Primary inputs and executed checks

Frigerio–Moraschini arXiv:1801.05326v3, printed page 6, and Luo–Yang
arXiv:1404.5365v2, printed pages 21–22, were inspected as page images in
this increment. They supply the inverse formula, positive-angle domain,
maximizer and common-length inputs. The existing Sections 76–77 are
credited repository inputs. These checks do not establish exhaustive
literature coverage or mathematical priority. The other source-reading
records above retain their original historical attribution.

The independent standard-library script is
`docs/develop/theory/cfmp_exposed_corner_check.py`.
The exact executed script blob is
`de2f65c74fc2a324cfb86ef2fb5e3cc29bfeb5c5`.
It performs 24000 edge comparisons on 4000 nonsymmetric genuine vectors,
including 854 obtuse targets, 10119 cases with a cap above pi/2, and 1520
length-weighted demand checks. The independent angle round-trip error is
at most 1.724714121520421e-13. It also checks 1000 abstract occurrence
identities, three sharp sequences, four threshold sequences, 999
complementary-cap identities and the explicit surviving local star.

The packet checks verify all face slots, odd permutations, connectedness,
actual edge classes, ordered endpoint first returns and six independent
link-vertex fans of sizes (6,6,12,12,48,48). Link counts are (6,66,44),
and the exact maximum normalized initial corner sum is 13/24. The 528
flat candidates after the proved f<=2 reduction are exhausted: 512 fail
saturation consistency and 16 satisfy the capacity exclusion. These
finite checks support the fixed example; the continuous estimates and
unbounded realization theorem depend on the written proofs.

The earlier checker and Scribe document, Lean sources and formal-status
files are unchanged by this increment. No new CI, Lean build, Scribe
projection, Freeze or independent-review approval is claimed. Larger flat
supports, general repeated-label incidence, unrestricted CFMP and torus-end
completeness remain outside the proved scope.

## Continuation on 2026-09-26: Sections 88–94

Baseline `e1263fe61d64b25d7b367d5922ebfee8f5374531` is retained. The new
results stay in the existing mixed-matching theory. They remove the bound
of three on the number of global edges in a different explicit structural
class: one actual shared edge H, with all non-H local slots forming a
matching. The two opposite special slots may have the same global label.
This is written research pending independent review, not a new Lean claim.

### Exact response and strict convexity

For genuine cosh lengths `(r,h,h,o,h,h)`, put Q=2h^2/(r-1) and
lambda=sqrt((h^2-1)/(Q+h^2)). The previous Sections 65–66 specialize the
classical Luo–Yang length cosine. Dividing its positive sine/cosine
expressions yields the exact scalar response

`beta=b_lambda(theta)=atan(lambda*cot(theta/2))`, with 0<lambda<1.

For D=sin(theta/2)^2+lambda^2*cos(theta/2)^2,

`b'=-lambda/(2D)` and `b''=lambda*(1-lambda^2)*sin(theta)/(4D^2)>0`.

This convexity concerns b_lambda, not the volume function. At fixed r,h,
lambda is the same in different blocks even when the opposite lengths and
target angles differ. For g>=3 genuine blocks, r>=1+2h and sum theta_i=pi,
feasibility forces Q>cot(pi/(2g))^2 and h>=Q. Scalar Jensen then proves

`sum beta_i > g*acos(tan(pi/(2g))) > pi/2`.

This estimates an existing sum without replacing any tetrahedra by their
average or assuming that an averaged length vector remains globally legal.

### Arbitrary-edge-count matching theorem

The actual finite connected orientable ideal triangulation has boundary
components of genus at least two. Choose one actual global edge H and a
nonempty set of other global labels. In every tetrahedron those other slots
are zero, one, or two opposite edges. Assume every non-H edge has degree at
least four. Then the SAME prescribed triangulation has genuine hyperbolic
realization and totally geodesic boundary, with no bound on its edge count.

Actual link counting gives t>E>=2 and d(H)>=4t>=12. Thus the explicit
assignment 2pi/d(label) has corner sum at most 5pi/6 and provides the
strict-angle premise directly at degree four. The earlier minimum-six
strict-angle theorem is not applied outside its range.

The credited Luo–Yang theorem supplies shared positive generalized lengths.
At least one block is genuine, so H cannot carry two flat pi slots. Every
special slot in any flat must therefore be a pi slot: n_e=m_e for non-H e.
Saturation of a special edge would give degree two, impossible. Each selected
special consequently has one flat occurrence and at least three genuine ones.

A flat's exact threshold `(r-1)*(o-1)>=4h^2` yields a selected non-H edge
with r>=1+2h. This edge cannot repeat in a genuine block, since its opposite
repeat would itself meet the flat threshold. Its genuine occurrences are
therefore in distinct blocks. Their target angles sum to pi, and the Jensen
bound makes their disjoint H slots contribute more than 2pi. This violates
H's actual global angle equation and excludes the entire flat set, with no
prior restriction on the number of flat blocks.

The one-H and matching conditions are essential stated hypotheses, not
consequences of minimum degree six. Adjacent special slots allowed in the
previous three-edge theorem are excluded here, so the full theorem classes
are not claimed to be nested. Multiple independent H lengths cannot silently
be treated as one shared parameter.

### Actual six-degree and four-degree examples

The theory supplies complete face tables for a fourteen-tetrahedron packet
of degrees (6,6,6,66), one genus-eleven boundary link (8,84,56), and exact
maximum initial normalized corner sum 13/33; and an eight-tetrahedron packet
of degrees (4,4,4,36), one genus-five link (8,48,32), with maximum 11/18.
Both have three distinct special labels forming an interaction triangle and
a real opposite-slot self-loop. Repeated labels are not only formally allowed.
The four-degree example is a restricted application, not unrestricted CFMP
at degree four. No new census or homeomorphism-type priority is asserted.

The resulting metrics lift to cyclic covers. Their respective counts are
14n or 8n tetrahedra, 4n edges, and manifold Euler characteristic -10n or -4n.
The lifted H generally splits into n actual edges. This uses metric lifting,
not the false assertion that every cover retains the one-H hypothesis.

### Executed tests and source boundaries

The independent standard-library checker is
`docs/develop/theory/cfmp_matching_reservoir_check.py`.
Its executed bytes have Git blob `eb2cfc6038f73eeb5c142bf12d5acfb7f5db4085`.
Both fixed tables pass face coverage, permutation parity, dual connectedness,
actual edge identification, ordered-endpoint first returns and eight separate
connected degree-two link-fan checks. Matching, repeated opposite labels,
interaction triangles and rational initial angles are checked directly.

With analytic seed 947488, 3000 genuine response checks include 1995 obtuse
targets. Maximum discrepancy from the original six-variable forward formula
is 1.4101567136215465e-14; the finite-difference derivative discrepancy is
at most 4.430500410990135e-11. There are 950 unequal-angle shared-parameter
stars with g=3,...,40, totaling 20425 genuine occurrences. These finite
floating checks supplement the continuous proof; they are not interval or
kernel certificates. A g=2 local family with h=Q=101/100, r=151/50, o_i=h
has total selected H angle 8atan(1/sqrt(101))<2pi. It demonstrates why this
star lemma does not automatically extend to g=2, without claiming a closed
counterexample or optimality of the global degree-four threshold.

Luo–Yang arXiv:1404.5365v2 supplies the classical formulas and maximizer
inputs. Parsed PDF text and successful images of printed pages 2 and 21
were read. Screenshot requests for pages 16 and 17 failed; those formula
locations are not claimed to have been image-verified in this increment.
CFMP remains anchored at arXiv:math/0402339, Conjecture 0.8. Repository PR
search located #9474 and #8155. Bounded searches do not certify worldwide
priority. Earlier source-reading and execution records retain their original
historical attribution.

The original Lean, Scribe, existing checkers and formal-status files remain
unchanged. No Lean build, project CI, Scribe projection, Freeze or independent
review approval is claimed. General adjacent-special incidence, multiple
independent shared lengths, unrestricted CFMP and torus-end completeness
remain outside this theorem.
