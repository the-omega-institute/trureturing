# Hard-core Weitz trees: geometric memory and certified ordering

## 1. Target and current result

The research target is a uniform complex zero-free neighborhood for the
independence polynomials of all finite induced square-grid subgraphs, extending
the interval currently obtained from the Weitz-tree connective-constant bound
2.429. Chen, Shao and Shi [1, Appendix A.6] give the threshold 2.538 and explicitly
identify improved Weitz growth bounds as a possible improvement mechanism.

This first result resolves a smaller, precise optimization question within that
route: how much can adaptive neighbor ordering improve the spatial radius-three
blocked-memory upper approximation? With the model defined below, let C_n^pi be
its root descendant count under a controller pi, allowed to depend on the entire
path history. Put

\[
 g(pi)=\limsup_{n\to\infty}(C_n^{pi})^{1/n},\qquad
 g_3^*=\inf_{pi}g(pi).
\]

The exact certificate and the induction below establish, at the mathematical
and independently replayed integer-certificate level,

\[
 \boxed{2.5205\le g_3^*\le2.5206,\qquad g(\mathrm{SRL})\ge2.5209.}
\]

In particular, an explicit adaptive policy strictly improves fixed SRL in this
same memory model, while **every** ordering on this model is still above 2.429.
The certificate therefore both supplies a constructive improvement and identifies
which resource must change before this route can improve the global threshold.
No improved global zero-free constant is asserted.

The four accompanying Lean modules contain proof scripts for the finite
certificates, the all-depth integer inequalities, and a genuine finite-domain
simulation. They have been logically reviewed but not compiled in the authoring
runtime. The asymptotic rate notation in this section is a paper consequence of
the all-depth inequalities, not a separately elaborated Lean limsup theorem.

This is the first dedicated square-grid hard-core research volume. Earlier
repository hard-core transfer discussions concern one-dimensional forbidden
adjacency and RH-related constructions; their determinant theorems do not
supply the two-dimensional deletion-tree estimates needed here.

## 2. Literature interface and provenance

Sinclair, Srivastava, Stefankovic and Yin [2, Appendix A] allow an ordering that
depends on the complete root-to-current path. Their straight-right-left ordering
and finite-cycle-memory construction give 2.433 at cycle cutoff 26 and 2.429 at
cycle cutoff 30. The PDF appendix and its boundary-condition convention were
visually checked. Adaptive ordering itself is therefore prior art.

The radius used here is a Manhattan **spatial radius** for retained deleted
vertices. It is not the paper's cycle-length cutoff. Comparing the two numerical
bounds without distinguishing these state semantics would be misleading.

The positive-vector certificate method is also standard. The proposed research
increment is the concrete, fully specified radius-three ordering separation,
the narrow all-controller bracket, and its actual geometric simulation. No
first-formalization priority or literature-wide novelty claim has been established.

The 2026 zero-free theorem uses a family-uniform finite-depth growth quantity,
including counts up to depth k and a supremum over roots and finite domains.
A root-only spectral fit with a domain-dependent uncontrolled prefactor would
not supply that input. Our finite-domain upper count keeps a fixed explicit
prefactor. Its formal connection to partition functions and the complex block
contraction theorem remains to be proved.

Repository source audit began at dev cdf5cd4f86a59704197979f49cc40c5e0664ecae;
the delivery branch starts from refreshed dev
b89d56d0c9a433f9b714821d2bb1779066c59ede. Searches for Weitz and
independencePolynomial found no existing owner in the searched repository/code
index. The existing RationalFarkas owner was read; it proves rational linear
infeasibility, not the controlled branching or geometric simulation statements.

Cross-author audit included loning's merged PR #5326: behavioral Hankel
minimality is distinct from determinant preservation. Here, likewise, a smaller
linear realization cannot replace a geometric path-counting automaton without
an exact semantic transport. PR #5562 supplies symmetric complex quadratic row
bounds, whose symmetry assumptions do not apply to directed branching. PR #5405
reinforces the distinction between finite sample success and all-input coverage.
The present modules therefore use an explicit all-depth induction and full
geometric closure, rather than an unproved compression or sampled coverage premise.

## 3. Actual ordered deletion and the memory approximation

Coordinates are relative to an east-facing incoming edge. The parent vertex
(-1,0) has already been removed. The three possible next directions are

\[
 S=(1,0),\qquad R=(0,-1),\qquad L=(0,1).
\]

An action a is one of the six permutations SRL, SLR, RSL, RLS, LSR, LRS.
For a chosen direction d, let E(a,d) be the directions preceding d in that
permutation, and put

\[
 K(a,d)=\{(0,0)\}\cup E(a,d).
\]

The coordinate normalization is

\[
 T_S(x,y)=(x-1,y),\quad T_R(x,y)=(-y-1,x),\quad
 T_L(x,y)=(y-1,-x).
\]

Each map is injective and sends the old origin to the new parent (-1,0).
For an actual finite available vertex set V, taking child d is allowed exactly
when d belongs to V, and the new available set is

\[
 V'=T_d(V\setminus K(a,d)).
\]

This is the ordered vertex-deletion expansion used in the hard-core ratio
recursion. The source's orderedCount counts its three-direction paths. It
requires no claimed relation between a supplied count and a grid: availability
is tested against the actual finite set of integer vertices.

For a retained blocked set F and radius r define

\[
 M_r(F,a,d)=T_d(F\cup K(a,d))\cap
 \{(x,y):|x|+|y|\le r\}.
\]

A memory child is allowed whenever d is absent from F. Blockers forgotten by
truncation do not reappear unless generated again by subsequent deletions.
This creates an upper approximation, including some geometrically impossible
long paths.

### Geometric simulation lemma

If V and F are disjoint, then V' and M_r(F,a,d) are disjoint.
Indeed, a point in both sets would have preimages u in V minus K and v in F
union K. Injectivity gives u=v. Membership in F contradicts initial disjointness;
membership in K contradicts u being outside K. Truncation only removes blockers.

Consequently, every child available in V is allowed by F. Induction over depth
gives actual ordered-domain count no greater than memory count, provided the
finite representation has all required geometric successors. The radius-three
closure theorem checks exactly that obligation.

## 4. Finite presentation and reproducible construction

Start at F0={(-1,0)}. Close under every allowed move and all six orderings at
radius three. The set-based replay finds 483 distinct reachable masks, verifies
all 8694 state-order-direction cases, and checks that each unblocked successor
has exactly its prescribed geometric mask. Every stored state is reachable when
all actions are available. The selected policy reaches 70 states; fixed SRL
reaches 75. These reachability counts were externally replayed, not separately
asserted as Lean theorem conclusions.

Coordinates are ordered lexicographically within the punctured Manhattan disk,
followed by the origin. The initial code is 64. The data use a lossless packing:
low 19 bits encode the mask; the remaining quotient modulo six encodes the
ordering; its quotient by six indexes one of 55 repeated weight triples.
The expanded radiusThreeRows is the sole owner of masks, three weights and policy.
No transition table, approximate eigenvalue or solver success flag is a premise.
The Lean transition function computes the geometric update and exact lookup.

Candidate discovery used finite-set exploration and numerical nonlinear power
iteration for the Bellman operator

\[
 (Tv)_i=\min_a\sum_{d:\,i\overset{a,d}{\longrightarrow}j}v_j.
\]

The resulting float vector was only a proposal. Lower weights were rounded down,
upper weights rounded up with a floor of one, at scale 10^9. A separate fixed-SRL
vector supplied the third witness. Acceptance uses the exact integer inequalities
below. Numerical convergence or eigenvalue approximation is unnecessary for
certificate validity.

## 5. Integer certificate and proof of the rate bracket

Write w_-(i), w_+(i), w_S(i) for the three integer weights and pi_*(i) for the
selected ordering. Missing children contribute zero, and multiple directions
to the same state retain their multiplicities. The finite certificate checks

\[
\begin{aligned}
0&\le w_-(i)\le10^9, &1&\le w_+(i), &0&\le w_S(i)\le10^9,\\
5041w_-(i)&\le2000\sum_{i\overset{a,d}{\longrightarrow}j}w_-(j)
 &&\text{for every }i,a,\\
5000\sum_{i\overset{\pi_*(i),d}{\longrightarrow}j}w_+(j)&\le12603w_+(i)
 &&\text{for every }i,\\
25209w_S(i)&\le10000\sum_{i\overset{\mathrm{SRL},d}{\longrightarrow}j}w_S(j)
 &&\text{for every }i.
\end{aligned}
\]

All three initial weights are exactly 10^9. These are 2898 all-order lower rows,
483 selected upper rows and 483 fixed lower rows, totaling 3864 row checks.

For a controller pi, count descendants recursively: C_0=1 and C_(n+1) is the
sum of the depth-n child counts. The controller can choose differently at every
history. The lower row holds for whichever action it chooses. Induction gives

\[
 5041^n w_-(i)\le10^9 2000^n C_n^{pi}(i).
\]

At the initial state the cap cancels. The upper row for pi_* similarly gives

\[
 5000^n C_n^{pi_*}(i)\le12603^n w_+(i).
\]

The fixed-order sub-potential gives the third inequality. At the initial state:

\[
\boxed{
(5041/2000)^n\le C_n^{pi},\quad
C_n^{pi_*}\le10^9(12603/5000)^n,\quad
(25209/10000)^n\le C_n^{\mathrm{SRL}}.
}
\]

Taking nth roots and limsup proves the bracket in Section 1. In particular,
no history-dependent ordering on this radius-three approximation has exponential
rate below 2.5205. This is stronger than testing finitely many stationary policies.
It is not an exact formula for g_3^*, and it does not prove that every optimal
policy is stationary.

### Actual finite-domain consequence

For every finite V with (-1,0) absent, let P_n(V) be orderedCount under pi_*.
The geometric simulation and the actual certificate give

\[
 \boxed{5000^nP_n(V)\le10^9 12603^n.}
\]

No matrix-growth or path-coverage hypothesis remains in this concrete endpoint.
Finite holes and irregular boundaries are allowed. A full four-neighbor root
can be handled by summing its at most four parent-deleted child expansions;
this root wrapper and the partition-polynomial identity are not included in the
current Lean endpoint.

**Do not reverse this simulation.** Lower bounds on the relaxed memory tree do
not give lower bounds on the actual square-grid Weitz tree. The memory barrier
restricts this chosen approximation strategy, not the physical critical point.

## 6. What this changes in the next research step

Ordering-only optimization within radius three has at most 0.0001 of room left
below the selected upper certificate. The gap from its certified floor 2.5205
to the published 2.429 target is 0.0915. More solver precision, more policy
iterations or a richer dependence on history cannot close that gap while the
same relaxed branching model is retained.

The next mathematical target is therefore **retained-geometry refinement**.
For r<=R and F contained in G, under the same action and direction,

\[
 M_r(F,a,d)\subseteq M_R(G,a,d).
\]

This follows by monotonicity of union, injective image and nested disks. Coupling
the two explorations under the same history-dependent sequence of actions then
shows that the larger-memory tree has no more paths. This is the next proposed
formal lemma. For independently chosen state policies the actions need not
agree, so monotonicity cannot be asserted without a controller transport.

A scalable implementation should retain deleted vertices associated with
potential loop closures, and seek an exact simulation or action-respecting
bisimulation before merging states. Equality of an approximate Perron weight
is not sufficient for a quotient. The complete all-order state union may be
much larger than the states reachable under a proposed policy, so upper and
lower certificates should use their appropriate, explicitly proved coverage.

Exploratory, unvalidated power iterations for fixed SRL at radii 4,5,6 returned
approximately 2.48260, 2.46329, 2.45139. They motivate retaining more geometry but
are not exact certificates or new global results. They cannot be extrapolated
into a claim that some particular radius must achieve 2.42.

After obtaining a genuine geometry-certified growth bound below 2.429, the next
analytic tasks are the exact partition-function/deletion-tree bridge and the
family-uniform complex block contraction. The sufficient proposed target
mu<=121/50 would imply lambda_c(mu)>51/20 through the standard threshold formula,
but the premise mu<=121/50 is unproved here. No 2.55 zero-free theorem is claimed.

## 7. Formal source map and verification

- BranchingPotential: weighted child sums, history-dependent counts, upper and
  lower all-depth integer induction.
- OrderedGridMemory: actual integer-grid maps, arbitrary-radius disjointness,
  finite-domain path definition and simulation.
- RadiusThreeData: lossless exact certificate data.
- RadiusThreeCertificates: full geometric closure, integer row checks, concrete
  upper, all-controller lower, fixed lower and finite-domain upper endpoints.

All 28 public declarations have paired canonical Scribe source handles using
StatementSource.FromLean. No authored formula replaces a Lean statement.
No information score, sampled analysis arena, catalog admission or sealing
claim is attached to these results. The finite presentation is checked against
the actual geometric blocked-set object. The referenced single-compilation
specification was read at version 4.3, blob
bba1875f68c733b925582ffc81f1344cfce96931.

Reproduce the independent exact research replay from the repository root:

```sh
python research/hard_core_weitz/verify_radius_three.py
```

The verifier reads the Lean-owned integer payload, reconstructs transitions
with integer-coordinate sets, checks all geometry and rows, replays 243 depth
regressions and 81 finite-domain regressions, and rejects six deliberately
corrupted certificates. It uses no discovery cache, NumPy, eigenvalue solver or
stored success JSON. The emitted validation JSON is a recorded output only.
This replay is a separate implementation by the same authoring assistant; it
is not independent-author review and does not check Lean proof terms.

Lean compilation, executed axiom closure and Scribe emission were unavailable
in the authoring runtime. The finite source proofs use decide +kernel, with no
native_decide or external verdict axiom. Those proof scripts have not yet been
executed. Thus the current delivery is a mathematically reviewed and exactly
replayed candidate formalization, not a kernel-admitted truth release.

## References

[1] Yuan Chen, Shuai Shao and Ke Shi. *Zero-Freeness of the Hard-Core Model with
Bounded Connective Constant*. arXiv:2604.02746v1 (2026), especially Definition 1.1,
Theorem 1.2 and Appendix A.6.
https://arxiv.org/html/2604.02746v1

[2] Alistair Sinclair, Piyush Srivastava, Daniel Stefankovic and Yitong Yin.
*Spatial mixing and the connective constant: Optimal bounds*.
arXiv:1410.2595, Appendix A, printed pages 27-28.
https://arxiv.org/abs/1410.2595

[3] Ricardo Restrepo, Jinwoo Shin, Prasad Tetali, Eric Vigoda and Linji Yang.
*Improved mixing condition on the grid for counting and sampling independent
sets*. The connective-constant paper [2] discusses this preceding multi-type
branching-matrix approach. It is prior art for geometry-sensitive tree bounds.

[4] Juan C. Vera, Eric Vigoda and Linji Yang. *Improved Bounds on the Phase
Transition for the Hard-Core Model in 2-Dimensions*. arXiv:1306.0431.
Its limitations on strong spatial mixing of full Weitz trees must be respected
when considering how far ordering-based refinements can ultimately go.
https://arxiv.org/abs/1306.0431


## 8. Retained geometry and explicit controller transport

The continuation starts from the preceding radius-three delivery. The latest
read of dev is b89d56d0c9a433f9b714821d2bb1779066c59ede. The original sources
remain unchanged. MemoryRefinement now proves the radius/blocker inclusion
statement proposed in Section 6 and its all-depth counting consequences.

There is an important distinction between inclusion and projection. Running
radius three and radius four from the same parent mask, with fixed SRL ordering
and direction history S,S,R,R, gives a point (2,-1) present in the fine memory
but absent from the coarse memory. That point is inside the radius-three disk:
it had previously left the coarse disk and been forgotten. The independent
integer-set replay checks the four steps and both memberships. Thus the fine
state cannot simply be intersected with the coarse disk to recover the actual
coarse controller state. This example is a replayed diagnostic, not a separately
elaborated Lean theorem.

For a policy depending only on the complete direction history, both models
choose the same action automatically. The theorem history_count_antitone proves
that r<=R and F contained in G imply C_R(n,G)<=C_r(n,F) for every depth and history.
For a policy depending on its coarse state as well, coupledStep retains the pair
(F,G), reads the policy at F, decides availability at G, and updates both with
the same action. The theorem coupled_count_le_coarse proves the same domination
for every such controller. No state-reconstruction hypothesis is used.

The exact fixed_presentation_count theorem separately transfers a finite table
to actual geometric sets by direction-preserving transition equality. Only the
selected order requires closure. This avoids creating states for unused actions
when a single-policy upper certificate is sufficient. Direction multiplicities
are preserved even when two directions have equal successor states.

## 9. Finite propagation and exact complete prefixes

Let rho(p)=|p_x|+|p_y|. The actual recentering maps satisfy

\[
 \rho(p)\le\rho(T_d p)+1.
\]

Consequently, if two blocker sets agree inside radius n+1, their updates agree
inside radius n when both retention radii are at least n. A point outside that
larger disk cannot enter the smaller disk in one step. This is the local
agreement theorem memoryStep_agreeWithin in MemoryLightCone.

Define completeStep using the same deletion/recentering operation without the
radius filter. For a common history-based ordering, finite_horizon_exact proves

\[
 \boxed{r\ge n,\quad F\cap B_n=G\cap B_n
 \quad\Longrightarrow\quad C_r(n,F)=C_\infty(n,G).}
\]

There is no upper bound on the complete initial blocker set's size. At each
induction step, availability agrees because the three candidate directions have
radius one, and child blockers agree on the remaining smaller light cone.
This result alone is a finite-depth statement. Uniform control over unbounded
depth is supplied by the next theorem, rather than assumed by exchanging limits.

## 10. Uniform block bounds and completeness of fixed-order memory

Fix one relative ordering a. Write P={(-1,0)}, c_k=C_infinity(k,P), and
c_n^(r)=C_r(n,P). Every allowed update retains the parent for r>=1. Any descendant
blocker set therefore contains P, and its continuation count is bounded above
by the count after resetting to P under the same fixed relative ordering.
This reset domination would require an additional controller argument for a
state-dependent policy; the theorem in this section fixes a.

MemoryBlockBounds.fixed_order_block_bound proves, for every r>=1, k<=r,
q,s>=0, every starting history and every finite F containing P,

\[
 \boxed{ C_r(qk+s,F)\le c_k^{\,q}\,3^s. }
\]

Proof: at depth k, reset domination followed by finite_horizon_exact bounds the
number of descendants by the actual complete prefix c_k. Every child at depth k
again contains P. Induct on the number q of full blocks; the remaining s steps
have at most 3^s descendants. This is an all-depth inequality with a uniform
coefficient for all eligible initial blocker sets, not an assumed spectral bound.
The companion complete_count_le_memory proves c_n<=c_n^(r) for every n and r.

### Paper consequence: the hierarchy reaches the complete growth rate

Define mu_infinity=limsup c_n^(1/n) and mu_r=limsup (c_n^(r))^(1/n).
For each fixed ordering, the following follows from the formal-source integer
inequalities by ordinary real limit arguments:

\[
 \boxed{
 \mu_\infty\le\mu_R\le\mu_r\quad(1\le r\le R),\qquad
 \inf_{r\ge1}\mu_r=\mu_\infty=\inf_{k\ge1}c_k^{1/k}.
 }
\]

Here are the quantifiers and proof. For a fixed k>=1 and any r>=k, write
n=qk+s with 0<=s<k. The block inequality gives
mu_r<=c_k^(1/k), since the factor 3^s is uniformly bounded as n grows.
Complete domination gives mu_infinity<=mu_r. Hence
mu_infinity<=inf_k c_k^(1/k). The reverse inequality follows because the infimum
of a sequence is at most its limsup. For every epsilon>0 choose one k with
c_k^(1/k)<mu_infinity+epsilon; then every r>=k satisfies
mu_infinity<=mu_r<mu_infinity+epsilon. Monotonicity comes from the common-order
refinement theorem. The complete all-straight path ensures c_k>=1, and all
counts are bounded by 3^k, so no infinite or zero-root pathology is used.

Thus larger fixed-order geometric memories converge in growth rate to the
complete ordered-deletion process. This establishes mathematical completeness
of this approximation hierarchy. It supplies neither a convergence rate nor a
particular finite radius attaining 2.429 or 2.42. It also makes no assertion that
optimizing over arbitrary controllers commutes with either limit. The limsup,
infimum and epsilon argument are proved here on paper; no separate Lean limit
declaration is claimed.

### Paper consequence: strict targets admit finite rational potentials

Suppose alpha is positive rational and c_k<alpha^k. For r>=k and r>=1, let
B_r act by summing a function over the selected-order children, and define

\[
 W(F)=\sum_{j=0}^{k-1}\alpha^{k-1-j}C_r(j,F).
\]

For every eligible F containing P, W(F)>0 and telescoping gives

\[
 B_rW(F)-\alpha W(F)=C_r(k,F)-\alpha^k
 \le c_k-\alpha^k<0.
\]

The radius-r universe of blocker sets is finite and closed under allowed steps.
All these potential values are rational, so a common denominator gives a finite
integer certificate. The hierarchy result guarantees such a k for each strict
rational target alpha>mu_infinity. This is a paper existence construction; it
is not a new executed large-radius certificate or a polynomial-time algorithm.
The potentially very large prefix and state enumeration costs remain real.

## 11. A concrete radius-four certificate and universal finite separation

The fixed-SRL radius-four closure has 851 distinct geometric states, verified
reachable from P by an independent set-based traversal. RadiusFourData contains
the exact masks and a positive integer weight w with

\[
 1\le w_i\le20000,\qquad w_0=20000,\qquad
 10000\sum_{i\longrightarrow j}w_j\le24827w_i.
\]

There are 307 distinct weight values. The data share these values losslessly;
no geometric states are identified. The 41 mask bits refer to lexicographically
ordered points of the punctured Manhattan disk followed by the origin. All
2553 state-direction cases reconstruct their successors from memoryStep itself,
and all 851 row inequalities pass exact integer replay. Minimum row slack is
zero, which is permitted for this non-strict upper certificate.

Candidate weights came from a numerical proposal, rescaling and monotone
integer ceiling updates until every row passed. Only the final integer rows
and geometric closure are mathematical evidence. No eigensolver output is
assumed in the theorem. Unused actions are outside the finite table's coverage;
the raw geometric transition remains defined for all six actions.

The existing super-potential induction and exact presentation transport give

\[
 \boxed{10000^n c_n^{(4)}\le20000\,24827^n,\qquad
 \mu_4(\mathrm{SRL})\le2.4827.}
\]

The same bound holds for the actual ordered deletion count of every finite
integer-grid domain with its parent absent. That endpoint uses raw geometry and
real domain membership; it never discards a real child because a lookup failed.
The theorem radiusFour_finite_domain_upper has no supplied growth or finite-table
coverage hypothesis.

A stronger finite comparison consumes the previous radius-three lower theorem.
The exact integer comparison

\[
 20000\,24827^{700}<25205^{700}
\]

combines with 5041^n<=2000^n C_n^pi to prove

\[
 \boxed{c_{700}^{(4,\mathrm{SRL})}<C_{700}^{(3,\pi)}
 \quad\text{for every history-dependent radius-three controller }\pi.}
\]

This is the public theorem radiusFour_beats_every_radiusThree_controller.
The depth 700 is a sufficient choice, not a minimality assertion. The conclusion
compares the two actual relaxed geometric models. It does not transfer their
lower bound to the physical grid. The new upper rate remains above the published
2.429, so no global zero-free improvement is claimed.

## 12. Literature-guided continuation beyond scalar growth

The checked version of Chen, Shao and Shi [1] remains v1 of 3 April 2026.
Its family-uniform fixed-depth definition counts all depths up to k and takes
suprema over roots and finite domains. Our complete-process and finite-domain
count theorems still require a partition-polynomial/deletion-tree identification,
the four-neighbor root wrapper, and this uniform analytic interface before any
complex zero-free conclusion can be claimed.

Vera, Vigoda and Yang [4, Section 5, version 2] already use type-dependent
piecewise-linear message functions and linear programming to prove stronger
spatial-mixing conditions than scalar branching estimates alone. Their
criterion motivates the next certificate target on our actual geometric types:

\[
 x_i=(1+\lambda\prod_jx_j)^{-1},\qquad
 (1-x_i)\sum_j\Psi_{t_j}(x_j)<\Psi_i(x_i).
\]

For positive decreasing affine pieces Psi_i(x)=b_i-a_i*x on intervals [X_i,Y_i],
a sufficient row is

\[
 (1-X_i)\sum_j(b_{t_j}-a_{t_j}X_{t_j})
 < b_i-a_iY_i.
\]

Only interval tuples consistent with the actual parent recursion are relevant.
Every required child-pruning/boundary configuration must be included, and strict
positivity of all message pieces must be checked. A fitted derivative at one
fixed point does not certify strong spatial mixing. The piecewise-affine method
and this sufficient inequality are prior art from [4], not a new method claimed
by this repository.

For the zero-free target, real contraction must additionally be extended to a
common complex neighborhood under valid regularity and denominator conditions.
Piecewise real messages do not themselves provide a holomorphic coordinate
change. One must either construct a suitable smooth/analytic approximation with
a retained strict margin or apply an independently proved complex-extension
theorem with all of its hypotheses discharged. No such nonlinear message
certificate or complex extension has been constructed in this increment.

The next substantive target is therefore a geometry-specific rational
contraction certificate at a parameter strictly above 2.538, or a stronger
certified geometric growth bound below 2.429. Larger memory is now justified by
a complete fixed-order hierarchy, while the type-dependent route can use the
full geometry rather than reducing all types to a single growth constant.
Neither target is promised by the present radius-four certificate.

Cross-author comparison informed this separation. Loning's #5326 distinguishes
behavioral compression from preservation of the mathematical quantity consumed
downstream. The newer #5882 supplies an explicit determinant-loss family even
under small balanced behavior error. Our shared-weight packing accordingly
preserves every mask and direction; it is not a behavioral quotient. The recent
#5602 actual prolate-model comparison likewise emphasizes deriving the relation
between concrete objects before transporting estimates. These PRs were read as
research context, not imported as proofs of hard-core facts.

## 13. Source and verification status of this continuation

The five new Lean owners are MemoryRefinement, MemoryLightCone,
MemoryBlockBounds, RadiusFourData and RadiusFourCertificates. They have 24
explicitly named public declarations with 24 matching canonical Scribe handles.
The prior 28 declarations are unchanged. The general induction and geometry
proofs reuse the preceding owners; no parallel pathCount or memoryStep is created.

The final independent replay reads the actual Lean-owned radius-four payload.
It checks 2553 geometric transitions, 851 integer rows, all 851 states through
101 depths (85951 inequalities), 1875 finite-propagation cases, 1080 memory
inclusions, 120 controller comparisons, 126 light-cone equalities, 558 block
bounds and 90 actual-domain cases. It also checks the depth-700 integer
comparison. Four malformed certificates are rejected; removing the necessary
radius-versus-depth guard is witnessed by a depth-three mismatch. The S,S,R,R
projection diagnostic is replayed explicitly.

```sh
python research/hard_core_weitz/verify_radius_four.py
```

Data SHA-256:
539f060617047d4334ac6e638b0e92d4f37369c174a89a4f092b6948d5eff36d.
Verifier SHA-256:
32ff8ab35c6087ebec88c5eddf3dc2dc17b197ca5ddb78e29f18f623f429eb2b.

The replay uses arbitrary-precision integers and finite coordinate sets, no
floating-point eigensolver or saved success flag. It was executed again after
final source assembly and reproduced the result JSON byte for byte. It is a
separate implementation by the same authoring assistant, not independent-author
review. Its finite regressions do not certify universal Lean proof terms.

Logical source review and exact replay have been performed. Lean/lake is absent
from the authoring environment, so elaboration, kernel checking, executed axiom
closures and Scribe emission have not been performed. The new finite proofs
request decide +kernel; this records their intended checking method, not an
executed acceptance result. The original-problem zero-free improvement remains
open. No first-formalization priority or literature-wide mathematical novelty
has been established.

Additional precise locator for [4]:
https://arxiv.org/html/1306.0431v2#S5


## 14. Adaptive radius four and the change from counting to messages

Continuation dated 7 September 2026. Sections 1-13 are retained as historical
increments. The fixed-SRL radius-four construction in Section 11 remains a
separate, unchanged result. The recovered adaptive construction is now stored
under AdaptiveRadiusFourData and AdaptiveRadiusFourCertificates, so it does not
overwrite the concurrently developed fixed-order modules.

The adaptive controller has 881 distinct reachable geometric masks and the
exact integer potential

\[
 1\le w_i\le100000,\quad w_0=100000,\qquad
 2500\sum_{i\to j}w_j\le6202w_i.
\]

Its scalar growth upper bound is 2.4808. The all-domain endpoint has prefactor
100000, and an explicit four-direction root wrapper has prefactor 400000.
The 41 coordinates here are the full lexicographic Manhattan disk, with the
origin in its lexicographic position. This differs from the fixed-SRL payload's
coordinate enumeration. Masks and message assignments must not be exchanged
between these two presentations.

Storage was losslessly changed to increasing masks. Each increment literal
stores 1116 times the mask increment plus six times its weight index plus the
selected order. Geometric successors are recomputed, never taken from a saved
edge list. The selected-action version of the existing finite-domain simulation
is factored out of OrderedGridMemory; the original public all-action statement
is preserved. ControllerShadow also constructs the history-only lift of a
coarse state policy and certifies the Section 8 projection diagnostic.

The 2.4808 count bound remains above 2.429. The next construction therefore
retains the actual child types in the nonlinear vacancy recursion instead of
reducing all of them to one scalar growth constant. This direction was already
identified in Section 12 from Vera, Vigoda and Yang [4]. Affine messages and LP
search are established methods; the proposed new increment is the exact
whole-box certificate at activity 51/20 on this concrete geometric controller.

## 15. An exact affine contraction certificate through activity 51/20

Set

\[
 \Lambda=51/20,
 \quad L=(1+\Lambda)^{-1}=20/71,
 \quad\gamma=999/1000,
 \quad\eta=3/1000.
\]

For each actual geometric type i, the data supply nonnegative rational a_i and
rational b_i, with denominator one million, and

\[
 \Psi_i(x)=b_i-a_ix,
 \qquad b_i-a_i\ge10577/1000000>0.
\]

There are 332 distinct coefficient pairs, shared only for storage. Every one
of the 881 geometric rows is checked using its own actual successor types.
No behavioral quotient theorem or sampled state-space restriction is assumed.
An absent direction has child coefficients a=b=0.

For all lambda in [0,Lambda] and all three child values x_d in [L,1], put

\[
 y=\frac1{1+\lambda\prod_dx_d}.
\]

The exact certificate proves

\[
 \boxed{(1-y)\sum_d\Psi_{j_d}(x_d)<\gamma\Psi_i(y).}
\tag{15.1}
\]

Zero coefficients are used for absent geometric children. In addition,
y belongs to [L,1], and every actual message is bounded below by the same
positive constant. The statement holds on the full probability box, not only
at the recursion's fixed point or sampled tuples.

### Exact global separation of the affine product

For a parent pair (a_p,b_p) and its three child pairs, write

\[
 C=\sum_db_d-\gamma b_p,
 \qquad s_0=\gamma(b_p-a_p).
\]

Multiplication by the positive denominator gives the exact identity

\[
\begin{split}
 &(1+\lambda\prod_dx_d)
   \left[\gamma\Psi_p(y)-(1-y)\sum_d\Psi_d(x_d)\right]\\
 &\hspace{12mm}=s_0-\lambda(\prod_dx_d)(C-\sum_da_dx_d).
\end{split}
\tag{15.2}
\]

Each row has one of two exact certificates. When C<=L*sum(a_d), the product's
residual is nonpositive throughout the box, so it suffices that s_0>=eta.
Otherwise the certificate supplies t>0 and reference values r_d in [L,1] with

\[
 C=t+\sum_da_dr_d,
\]

and, for every direction, at least one of

\[
 r_d=L,\ t\le a_dr_d;
 \qquad r_d=1,\ a_dr_d\le t;
 \qquad a_dr_d=t.
\]

These finite rational conditions imply the global inequality

\[
 (\prod_dx_d)(C-\sum_da_dx_d)\le t\prod_dr_d.
\tag{15.3}
\]

Here is a proof that does not trust numerical global optimization. If the
residual S=C-sum(a_d*x_d) is nonpositive, (15.3) is immediate. Otherwise consider
the four nonnegative numbers S/t and x_d/r_d. Exact balance gives

\[
 S/t+\sum_dx_d/r_d
 =4+\sum_d(x_d-r_d)(1/r_d-a_d/t)\le4.
\]

Each summand is nonpositive by its clamping condition. Four-term AM-GM bounds
the product of the four numbers by one. Multiplication by t*prod(r_d) proves
(15.3). Mathlib's existing AM-GM theorem is reused in AffineProductCertificate;
no new abstract AM-GM result is claimed.

The final finite check is

\[
 s_0-\Lambda t\prod_dr_d\ge\eta.
\]

It implies (15.2)>=eta for every smaller nonnegative lambda as well. The
reference point and level are reconstructed from three base-three pattern
digits using the balance equation. All divisions, interval bounds and sign
conditions are then checked exactly. Among the 881 rows, 704 use a clamped
certificate and 177 use the nonpositive-residual case.

The minimum exact certified row margin is

\[
 \frac{15933066155943166674084141574726553949}
 {4676403243490598502400000000000000000000}
 >\frac3{1000}.
\]

Its decimal rendering is approximately 0.003407119815452501. The rational
fraction, rather than this decimal, is the recorded evidence.

### Deleting children preserves the same inequality

For any subset of actual children, set missing coordinates to one. The parent
recursion is unchanged. The complete row includes the omitted terms Psi_j(1),
which are nonnegative; removing them decreases the left side of (15.1), since
1-y>=0. Thus the same contraction constant holds for every subtree-pruning
pattern, including a leaf. The formal endpoint affine_pruned_row_contraction
quantifies over every subset. This check is essential: stability of the full
branching tree alone would not justify the finite-grid application.

### Discovery and acceptance are distinct

A sampled linear program and successive continuous separation searches proposed
coefficients. Its sampled optimum, approximate fixed-point derivative and
optimizer convergence are not evidence for (15.1). Coefficients were rounded
to denominator one million, then all clamping and margin conditions were
reconstructed and accepted by exact rational arithmetic. The independent
verifier uses no optimizer, precomputed edges or saved success verdict.

## 16. Paper transfer to a common complex zero-free neighborhood

The following analytic and graph argument is a candidate computer-assisted
proof of a uniform zero-free neighborhood of [0,51/20]. Its finite premises
have been exactly replayed. The analytic continuation and graph induction in
this section have been mathematically reviewed, but have not been formalized
or independently reviewed. Consequently this is not an end-to-end Lean theorem,
a kernel-admitted release or a literature-priority claim.

The real-to-complex contraction principle is established prior art, especially
Shao and Sun [5]. Their general theorem is not silently instantiated with
unproved type-dependent hypotheses. The finite-type version needed here is
spelled out below, including analytic coordinates, pruning and the four-child
root. The interval endpoint 2.55 exceeds the 2.538 sufficient endpoint in
[1, Appendix A.6]. The larger conjectural analyticity interval near 3.796
remains open; the scalar 2.429 connective-constant question is not settled.

### 16.1 Analytic coordinates and the actual Jacobian

For each type, use the real coordinate

\[
 \phi_i(x)=\frac{\log x-\log(b_i-a_ix)}{b_i},
 \qquad \phi_i'(x)=\frac1{x\Psi_i(x)}.
\]

Both x and Psi_i(x) are strictly positive on [L,1], and b_i>0. The inverse is
explicit:

\[
 \phi_i^{-1}(m)=\frac{b_i e^{b_i m}}{1+a_i e^{b_i m}}.
\]

These formulas remain valid when a_i=0. They define holomorphic functions near
the corresponding compact real intervals, using the logarithm branches that
agree with the real logarithms. Positive lower bounds and finitely many types
provide a common sufficiently small neighborhood with no denominator or log
argument vanishing. Write I_i=phi_i([L,1]); it is a compact real interval.

For a parent type i and an allowed subset S of its actual children, transform
the vacancy recursion to g_(i,S,lambda) in these coordinates. Direct
differentiation gives, for every retained child j,

\[
 \frac{\partial g_{i,S,\lambda}}{\partial m_j}
 =-\frac{(1-y)\Psi_j(x_j)}{\Psi_i(y)}.
\]

Thus (15.1) and the pruning result bound the absolute Jacobian row sum by
gamma throughout every real product of the child intervals and for all
lambda in [0,Lambda]. This derivative identification is a paper calculation;
the current Lean endpoint proves the displayed algebraic row inequality.

### 16.2 Uniform complex invariant neighborhoods

Choose gamma' strictly between gamma and one, for example 1999/2000. There
are finitely many parent types and child subsets. Holomorphy and compactness
therefore provide positive radii delta_0 and epsilon_0 such that all transformed
maps are defined and their complex Jacobian row sums are at most gamma' when
the messages are delta_0-close to their real intervals and the activity is
epsilon_0-close to [0,Lambda]. Their activity derivatives have a common finite
bound M on a smaller closed neighborhood.

Choose 0<delta<delta_0 and then 0<epsilon<epsilon_0 with
M*epsilon<(1-gamma')*delta, with the harmless M=0 case treated separately.
Let Omega_i be the open delta-neighborhood of I_i. Each Omega_i is convex.
For z within epsilon of [0,Lambda] and each m_j in Omega_j, choose nearest
real points m_j^0 in I_j and lambda in [0,Lambda]. Integrating the derivatives
along the straight segments gives

\[
 \left|g_{i,S,z}(m)-g_{i,S,\lambda}(m^0)\right|
 \le\gamma'\max_j|m_j-m_j^0|+M|z-\lambda|<\delta.
\]

The real output lies in I_i by the vacancy interval theorem. Hence the complex
output lies in Omega_i. The empty-child case is included in the same argument.
This provides one invariant collection of neighborhoods and one activity
neighborhood, independent of the tree's depth or the graph's size.

At the unconditioned root there can be four children. No root contraction
estimate is required. Its denominator 1+lambda*prod(x_j) is at least one on
the compact real set. Shrinking delta and epsilon further, while keeping the
invariance inequality, makes all these root denominators nonzero as well.
All root branches may be initialized at the parent-only geometric type; the
extra actual deletions only prune the represented tree.

### 16.3 Exact graph recursion and its geometric typing

For a finite induced grid graph H and vertex v, separate independent sets
according to whether v is occupied:

\[
 Z_H(z)=Z_{H-v}(z)+zZ_{H-N[v]}(z).
\tag{16.1}
\]

Order the available neighbors u_1,...,u_k as prescribed by the current geometric
type, and let H_j=H-v-\{u_1,...,u_{j-1}\}. Wherever the smaller partition
functions are nonzero, telescoping gives

\[
 \frac{Z_{H-N[v]}(z)}{Z_{H-v}(z)}
 =\prod_{j=1}^k\frac{Z_{H_j-u_j}(z)}{Z_{H_j}(z)}.
\tag{16.2}
\]

These are finite exact identities. No assumption of independence between
neighbors in the original graph is used. Orders may depend on the entire
recursion history, since (16.2) holds at each finite subproblem separately.
The translation and quarter-turns preserve square-grid adjacency. The proved
blocker disjointness guarantees that every actual available child is represented,
and the geometric closure assigns its correct successor type. Missing actual
vertices simply remove children, which Section 15 already covers.

Induct on the finite number of available vertices, simultaneously carrying
the nonroot typed vacancy values in the invariant message neighborhoods.
The empty partition function is one. At each step all smaller denominators in
(16.2) are nonzero by induction, so (16.1) expresses Z_H as the nonzero smaller
partition function times the certified nonzero local recursion denominator.
Nonroot outputs remain in their typed neighborhoods by Section 16.2; the full
root uses its separate four-child nonvanishing bound. Every finite induced
subgraph, including disconnected graphs and irregular boundaries, is covered.

This yields the paper/computer-assisted conclusion

\[
 \boxed{\exists\epsilon>0\ \forall H\subseteq_{\mathrm{fin,ind}}\mathbb Z^2\
 \forall z\in\mathbb C:\
 \operatorname{dist}(z,[0,51/20])<\epsilon\ \Longrightarrow\ Z_H(z)\ne0.}
\tag{16.3}
\]

The argument gives existence, not a numerical value of epsilon. It concerns
unconditioned finite induced partition functions. An occupied pinned vertex
can contribute a factor z, so no claim of nonvanishing at zero for arbitrary
pinned partition functions is made. Infinite-volume free-energy analyticity
and an implemented approximation algorithm are not separately established here.

## 17. Formal endpoints, replay and the next research step

New formal-source endpoints include clipped_product_bound, checked_row_sound,
affine_message_certificate, affine_message_positive, affine_polynomial_margin,
vacancy_mem, affine_full_row_contraction and affine_pruned_row_contraction.
The finite data, real inequality proofs and geometry all have paired canonical
Scribe declarations. The historical fixed-order and block-memory modules remain
unchanged. No artificial finite arena, information score or sealing claim is
attached to the certificate; the type assignments refer to actual grid masks.

The independent pure-Python verifier reads the current Lean-owned literals,
reconstructs all successors with integer-coordinate sets, and performs:

- 2643 geometric transition checks and 881 integer growth rows;
- 881 exact whole-box affine row checks, including 704 clamped cases and
  177 nonpositive-residual cases;
- 21144 exact rational recursion/pruning regressions across all child subsets;
- six corruption tests, all rejected, including message/type misalignment,
  a wrong clamp pattern, omitted root deletion, loss of message positivity,
  a missing state and an unsupported increase of the activity to three.

```sh
python research/hard_core_weitz/verify_adaptive_affine.py
```

The final replay was executed twice and produced byte-identical output. It is
a separate implementation by the same authoring assistant, not independent
researcher review. Finite regressions supplement the universal clamped-product
proof; they do not replace it. Source transcription errors were detected by
exact remote/local blob comparison and corrected before final delivery.

The authoring runtime has no Lean/lake executable. No source elaboration,
executed axiom closure, Scribe emission or kernel admission is asserted.
The finite scripts request decide +kernel and contain no new axioms or admits.
Sections 16.1-16.3 remain a paper transfer requiring independent scrutiny and
future end-to-end formalization, even if the current real certificate compiles.

The next priority is to formalize the actual finite independent-set identities
(16.1)-(16.2), the typed holomorphic coordinates and Jacobian, and the
uniform complex-neighborhood induction. This turns the proposed 2.55 conclusion
into a complete machine-checkable graph theorem. A quantitative epsilon would
also be useful, but is distinct from proving its existence. Larger activity
certificates or larger geometric memories should be pursued only after the
current actual-graph transfer is independently checked. Improving a scalar
connective-constant bound is no longer a prerequisite for this message route.

[5] Shuai Shao and Yuxin Sun. *Contraction: A Unified Perspective of Correlation
Decay and Zero-Freeness of 2-Spin Systems*. Journal of Statistical Physics 185,
12 (2021); arXiv:1909.04244v3. The real-to-complex extension is prior art; the
specific finite-type coordinate argument and numerical certificate above are
spelled out rather than attributed as an already instantiated theorem.
https://arxiv.org/abs/1909.04244
https://doi.org/10.1007/s10955-021-02831-0


## 18. Actual independent-set partitions and noncircular elimination

This continuation begins at ceb6e285c889669fd4090da55ae26e38f28a60ef and reads
dev at 76d7b4a789e9c44f49b4800fc93e569f68a48b51. The previously delivered
IndependentPartitionDeletion, OrderedPartitionRecursion and RealPartitionMessages
sources are present on the research branch. Their missing cumulative mathematical
summary is supplied here, before the new grid correspondence.

For a simple graph G, a finite vertex domain V and activities w in a commutative
semiring, the existing partition is the actual independent-configuration sum

\[
 Z_G(V;w)=\sum_{S\subseteq V,\;S\text{ independent}}\prod_{u\in S}w(u).
\]

The configuration predicate is Mathlib's SimpleGraph.IsIndepSet. The ambient
graph may be infinite. Splitting configurations by the occupancy of v in V
and inserting v into configurations on C=(V\{v})\N_G(v) gives

\[
 Z_G(V;w)=Z_G(V\setminus\{v\};w)+w(v)Z_G(C;w).
\]

No nonzero assumption is used. The identity holds as a polynomial identity
and at complex activities where intermediate partitions vanish.

For an ordered list of neighbors, let W0=V\{v}, Wj=W(j-1)\{uj}, and define
N=prod_j Z_G(Wj;w), D=prod_j Z_G(W(j-1);w). Exact cross multiplication gives

\[
 Z_G(V;w)D=Z_G(W_0;w)(D+w(v)N).
\]

If every partition on a subset of W0 is nonzero, this becomes

\[
 Z_G(V;w)=Z_G(W_0;w)\left(1+w(v)\prod_j
 \frac{Z_G(W_j;w)}{Z_G(W_{j-1};w)}\right).
\]

The target Z_G(V;w) is not assumed nonzero. This is the noncircular induction
step needed for the later complex result.

For nonnegative real activities, the empty configuration contributes one and
all other terms are nonnegative. Configuration inclusion gives domain
monotonicity. If the root activity is at most Lambda, then

\[
 Z_G(W_0;w)\le Z_G(V;w)\le(1+\Lambda)Z_G(W_0;w),
 \qquad \frac1{1+\Lambda}\le\frac{Z_G(W_0;w)}{Z_G(V;w)}\le1.
\]

Thus constant activity in [0,51/20] places every actual real vacancy in
[20/71,1]. These classical facts are now source dependencies rather than
unproved graph-message interpretations.

## 19. Exact configuration transport for the square-grid frames

PartitionRelabeling constructs the image and inverse-image correspondence
between complete independent-configuration families. For a vertex equivalence
e from G to H that preserves and reflects adjacency, it proves

\[
 \mathcal I_H(e(V))=\{e(S):S\in\mathcal I_G(V)\},\qquad
 Z_H(e(V);w)=Z_G(V;w\circ e).
\]

Weights are pulled back explicitly. The result is over every commutative
semiring; it therefore preserves entire independence polynomials and all their
complex evaluations. Injectivity also proves e(V\{v})=e(V)\{e(v)}, so the
marked numerator is transported together with the denominator.

SquareGridCoordinates defines the nearest-neighbor grid on the already-owned
integer-pair type. It proves directly that translation to an arbitrary root and
the existing recenter maps preserve and reflect each grid edge. Explicit inverse
maps witness bijectivity. No graph-isomorphism premise remains in the concrete
coordinate theorems.

For the existing recenter map T_d, constant activity z and every finite V,

\[
 Z_{\rm grid}(T_dV;z)=Z_{\rm grid}(V;z),\qquad
 \alpha(T_dV,T_dv;z)=\alpha(V,v;z).
\]

Here alpha is the ratio of two actual independent-set sums. Equality of total
field expressions at zero denominators does not assert holomorphic regularity;
all recursive cancellation still requires proper-domain nonvanishing.

## 20. Exact child types, actual contraction and the four-child root

Fix one of the six existing orders a. Before child d, let
B_d=V\K(a,d), using the original deleted definition, and V_d=T_d(B_d), using
the original advance definition. The new exact correspondence is

\[
 \boxed{\alpha(V_d,0;z)=\frac{Z(B_d\setminus\{d\};z)}{Z(B_d;z)}.}
\]

The selected neighbor becomes the origin. The finite order check proves that
B_d is precisely the successive domain occurring in ordered elimination,
including earlier absent vertices. The child factors are neither independent
marginals of the original graph nor an unconditioned computation-tree surrogate.
Their product is the exact ordered graph product.

For a present origin and an absent parent, proper-domain nonvanishing yields

\[
 Z(V;z)=Z(V\setminus\{0\};z)
        \left(1+z\prod_{d\in\{S,R,L\}}\alpha(V_d,0;z)\right).
\tag{20.1}
\]

On the real nonnegative interval all denominator conditions follow from the
empty configuration. If an actual neighbor is absent, its two partitions are
identical and positive, so its child value is exactly one.

For an actual domain V disjoint from the certified mask F_i, every present
child d has a successor j in the existing 881-state table. The theorem
typed_child_context derives simultaneously

\[
 0\in V_d,\qquad V_d\cap F_j=\varnothing,\qquad |V_d|<|V|.
\]

It consumes the existing full geometric closure and blocker-disjointness
proofs. No separate table-coverage or child-type assumption is supplied by a
caller. Strict size decrease supplies the well-founded measure for induction.

Let S(V) be the set of actual present nonparent directions. The new endpoint
actual_grid_affine_contraction applies the existing affine certificate to the
actual graph parent and child ratios:

\[
 \boxed{
 \frac{(1-\alpha(V,0;\lambda))
       \sum_{d\in S(V)}\Psi_{j_d}(\alpha(V_d,0;\lambda))}
      {\Psi_i(\alpha(V,0;\lambda))}<\frac{999}{1000},
 \quad 0\le\lambda\le\frac{51}{20}.
 }
\tag{20.2}
\]

The original childMessage accessor is used, with its zero value for absent
geometric directions. Actual presence implies a genuine successor, as proved
above. The proof derives the input interval, recursion identity and neutral
absent-child values before invoking affine_pruned_row_contraction. No floating
approximation or graph-message equality hypothesis is used.

The unconditioned root is treated separately. SquareGridRootMessages proves
that the four existing rootDomain objects are exactly the successive root
neighbor domains under their actual coordinate equivalences. Consequently,

\[
 Z(V;z)=Z(V\setminus\{0\};z)
   \left(1+z\prod_{e=0}^3\alpha(\operatorname{rootDomain}(V,e),0;z)\right).
\tag{20.3}
\]

Only proper pre-recentered subsets are required nonzero. Every present first
child is smaller, contains its new origin, and is disjoint from the existing
type-zero mask {(-1,0)}. Extra earlier-neighbor deletions stay in the actual
vertex domain. No three-child contraction is applied to the four-child root.
An arbitrary marked root is handled by the proved translation equivalence.

## 21. What the 5040 research contributes to this lane

The 5040 research line was read in the current dev source, including
ZECKENDORF_EULER_5040.md, GoldenResourceObjectiveFactorization,
GoldenResource5040PriceInterval, and GoldenResource/EightStepAbundancy.
The recent padding-mass PR 6131 was also read at its discussion level. These
are cross-line mathematical inputs to the research strategy, not Lean imports
or a claim that the grid and arithmetic state spaces are the same object.

### A stable optimum depends on the specified resource

The exact objective in the price-interval theorem is

\[
 F_\theta(n)=\log(\sigma(n)/n)-\theta\log n.
\]

Prime factorization separates it into local exponent contributions. For
5040=2^4 3^2 5\,7, the existing theorem establishes unique optimality over all
positive integers throughout the open price interval

\[
 \boxed{\frac{\log(12/11)}{\log11}<\theta<
        \frac{\log(31/30)}{\log2}.}
\]

The approximate endpoints are 0.03628656 and 0.04730571. Price 1/25 lies
strictly inside. The prime-layer marginal is

\[
 m_p(a)=\frac{\log((1-p^{-(a+1)})/(1-p^{-a}))}{\log p}.
\]

The boundary layers are the last selected (p,a)=(2,4) and first unselected
(p,a)=(11,1). Strict local margins imply a stable global optimizer through an
exact sum decomposition. This is the useful certificate pattern here.

The same dev contains an explicit distinction: with the different constraint
Omega(n)=8, the unique maximum of sigma(n)/n is attained at 180180, with

\[
 \frac{\sigma(180180)}{180180}=\frac{224}{55}>
 \frac{403}{105}=\frac{\sigma(5040)}{5040},
 \qquad \Omega(180180)=\Omega(5040)=8.
\]

Thus 5040 does not optimize every resource formulation. For the square grid,
the actual parent-child relation and the complete message box define the
problem; replacing them by a more convenient scalar cost changes the claim.

### Exact local accounting is the transferable structure

For nonnegative activities, list all vertices and successively delete them.
The existing ordered telescoping theorem gives

\[
 \prod_{j=1}^{|V|}\alpha(W_{j-1},v_j;w)=\frac1{Z_G(V;w)},
 \qquad \log Z_G(V;w)=-\sum_{j=1}^{|V|}\log\alpha(W_{j-1},v_j;w).
\]

This paper consequence identifies an exact local accounting of the graph's
target observable. The arithmetic lane obtains its local sum from independent
prime factors; the graph lane obtains its sum from successive conditional
deletions, preserving the original correlations. The logarithmic formula is
not a separate new Lean declaration in this increment.

PR 6131's exponent-tagged padding injection illustrates a second safeguard:
a many-to-one map must retain a fiber tag or multiplicity bound when comparing
weighted sums. The grid transport proved here is a bijection, so each
configuration has multiplicity exactly one and no loss of the existing margin
is introduced by a coordinate change. PR 6131 explicitly retains its finite-set
mass-escape hypothesis; it is not read as an RH proof or a source of grid bounds.

Robin's classical criterion has the specific cutoff n>5040. A recent analogue
[6] uses a different divisor statistic and cutoff 2162160. Together with the
two distinct repository optimization problems, this reinforces that the number
5040 is important in specified arithmetic statements. No grid automorphism,
message dimension, contraction constant or complex-neighborhood width has been
shown here to equal or be controlled by 5040. There is no numerical 5040 premise
in the new grid Lean sources.

## 22. Verification and the remaining analytic step

Four new Lean owners have four canonical Scribe companions and 34 explicitly
named public declarations: PartitionRelabeling, SquareGridCoordinates,
SquareGridMessages and SquareGridRootMessages. Existing partition, geometric,
affine-message and root-domain owners are reused without replacement.

The independent exact replay enumerates every independent subset of all 512
subdomains of the 3-by-3 square. It checks 2048 complete configuration bijections,
2048 weighted equalities, 17368 marked-ratio equalities, 3328 child matches,
5120 denominator-cleared recursions, 4134 valid division recursions, 986 cases
with a zero intermediate factor, and 13056 real input-box checks. A separate
bounded exploration of 652 radius-four masks supplies 67152 compatible-child
regressions; it is not a second full check of the 881-state certificate.
Seven malformed transports are rejected. Their changes include loss of
adjacency, injectivity, weight transport, marked-root transport, correct ordered
deletion, the fourth root direction, and the root nonvanishing obligation.

```sh
python research/hard_core_weitz/verify_grid_correspondence.py
```

This verifier computes reference values directly from independent subsets,
not from the deletion identity it tests. It uses exact rational and
Gaussian-rational arithmetic. The logarithmic endpoint decimals are illustrative
only. The upstream affine certificate is reused by the Lean source and has not
been rerun in this continuation. The separate implementation is by the same
authoring assistant, not an independent researcher.

The new sources have been mathematically reviewed and regression-tested.
Lean elaboration, kernel checking, executed axiom closure and Scribe emission
remain unperformed. The finite proof scripts request decide +kernel. No
kernel-admitted or independent-review status is inferred from that request.

The exact graph/type correspondence in Section 20 removes the semantic
premises from the current real certificate. The remaining work is to formalize
the actual holomorphic coordinates and their Jacobian, build one invariant
complex neighborhood for all types and pruning subsets, and combine it with
the strict-cardinality induction and the separate four-child root denominator.
These analytic obligations are not replaced by real positivity or the 5040
analogy. No new zero-free endpoint or RH conclusion is asserted in this increment.

[6] Steve Fan, Mits Kobayashi and Grant Molnar. *A family of analogues to the
Robin criterion*. arXiv:2511.02106 (2025). The statistic and the explicit cutoff
change together in their Robin-type equivalence.
https://arxiv.org/abs/2511.02106


## 23. Additive charts, multiplicative odds and type-dependent projective flow

This continuation reads dev at 3478a75a07f72d4a71d995bc1071d999ffd2f2bd and
continues the exact-grid source at 65af741aefefef2a9a5f549b5b0910d23d325dcb.
The mathematical target remains a common complex zero-free neighborhood through
activity 51/20. The new analytic construction below gives explicit widths;
it does not change the preceding finite coefficient or geometric payloads.

Three existing dev sources provide relevant, distinct structures:

* GoldenEulerStepPhaseLaw proves Euler's sine/cosine expression for the prime
  step phase, unit norm, the golden long-step factorization using phi^2=phi+1,
  and the loss of adjacent order when only scalar phases are multiplied.
* PrimeGoldenComplexMode retains a positive amplitude and a phase separately;
  its norm recovers the amplitude. Its damping hypotheses matter for recovering
  the prime label from that amplitude.
* Quantum/Algebra/WeylDisplacement proves the finite-window shift/clock
  composition law with its symplectic phase, including a genuine two-address
  anticommutation example. It is a projective operator representation.

These existing results were read as actual source, not inferred from names.
They are not imported as hard-core inequalities. Spatial grid translations act
on vertices and configurations, while the following translations act on message
coordinates. Section 20 supplies the exact observable correspondence between
the geometric model and these message coordinates.

For a fixed type with Psi(x)=b-a*x, use the odds coordinate

\[
 q=\frac{x}{b-ax},\qquad m=\frac{\log q}{b}.
\]

The inverse is f(m)=b exp(bm)/(1+a exp(bm)). The new inverse_odds theorem gives
q(f(m))=exp(bm) exactly. Thus m -> m+u+iv multiplies the odds by
exp(bu) exp(ibv): real shifts change the modulus, imaginary shifts rotate phase.
The modulus identity and exponential factorization are formalized together.

In the original x coordinate, an odds multiplier E acts as

\[
 T_{k,E}(x)=\frac{Ex}{1+k(E-1)x},\qquad k=a/b.
\]

Its matrix is [[E,0],[k(E-1),1]]. The exact pole-free composition is
T_(k,E) composed with T_(k,F)=T_(k,EF). For two different type ratios k,l,
the difference between the lower-left entries of the two matrix products is

\[
 \boxed{(k-l)(E-1)(F-1).}
\tag{23.1}
\]

Consequently, type-dependent projective transport generally retains ordering
information that scalar phase multiplication loses. The first two actual
coefficient pairs give k=2544246/2780973 and l=782543/1650757, with
k-l=224855659987/510078960729, a nonzero exact rational. For E=F=2 and x=1/2,
the two projective compositions differ by the exact rational recorded by the
replay. That diagnostic is outside the small analytic tube below and asserts
only the algebraic ordering distinction. Equation (23.1) also permits nonzero
ordering defects for multipliers arbitrarily close to one.

The golden ratio can be used as a step parameter and its quadratic identity
then gives the existing long-step factorization. No golden-ratio value has
been shown to optimize the present coefficients or the activity width. The
real golden ratio, a phase angle, and a logarithmic coordinate are different
parameters. Likewise, the finite Weyl operator law and the present fractional
linear action are different representations; no isomorphism between them is
asserted. A physical wave-particle statement would additionally require a
specified quantum state space, observables and measurement probabilities.
The classical hard-core partition is not assigned that interpretation here.

## 24. One-log holomorphic coordinates and the exact full Jacobian

Write Log for the principal complex logarithm. Define

\[
 \chi_i(x)=-\frac{\operatorname{Log}(b_i/x-a_i)}{b_i},\qquad
 f_i(m)=\frac{b_i e^{b_i m}}{1+a_i e^{b_i m}}.
\]

On the positive real interval this agrees with Section 16's coordinate.
AffineChart proves, with explicit pole and slit-plane hypotheses,

\[
 \chi_i'(x)=\frac1{x\Psi_i(x)},\qquad
 f_i'(m)=f_i(m)\Psi_i(f_i(m)).
\]

It also proves the real-center inverse and the two-sided inverse on the
principal strip -pi<Im(b_i*m)<pi. The later tube excludes wrapping uniformly.
All formulas include a_i=0. No logarithm of activity is used, so activity zero
is inside the same analytic construction.

For a subset S of actual geometric children put

\[
 P=\prod_{j\in S}f_j(m_j),\qquad
 H=b_i-a_i+b_i zP,\qquad G_{i,S}(z,m)=-\operatorname{Log}(H)/b_i.
\]

The empty product is one. On the pole-free domain, the inverse is exactly
f_i(G_(i,S))=(1+zP)^(-1). The new TypedJacobian derives the full differential,
including simultaneous changes in activity and every child coordinate:

\[
 \boxed{dG=-\frac{P}{H}\,dz
 -\sum_{j\in S}\frac{zP\Psi_j(f_j(m_j))}{H}\,dm_j.}
\tag{24.1}
\]

The source proves this along arbitrary differentiable complex input curves
and separately proves joint complex differentiability on the finite-dimensional
product domain. It does not infer holomorphy from a sampled derivative fit.
The child coefficient is algebraically identical to
-(1-y)Psi_j(x_j)/Psi_i(y), where y=(1+zP)^(-1). Thus the existing real row
certificate controls the actual Jacobian of the constructed map.

## 25. Explicit widths and pole-free quantitative estimates

The existing coefficient certificate gives a_i>=0 and
b_i-a_i>=10577/1000000. The added finite source check gives b_i<=3 on the same
Lean-owned payload. The analysis uses the weaker common bounds

\[
 0\le a_i,\quad b_i-a_i\ge1/100,\quad b_i\le3.
\]

Choose the explicit widths

\[
 \boxed{\delta=10^{-20},\qquad\epsilon=10^{-30},\qquad
 \gamma=999/1000,\quad\gamma'=1999/2000.}
\tag{25.1}
\]

For r in [1/4,1], let c_i(r) be the real value of chi_i(r). If
|m-c_i(r)|<=delta, set u=m-c_i(r), E=exp(b_i*u), and k=a_i*r/b_i in [0,1].
Exact algebra gives

\[
 f_i(m)=\frac{rE}{1+k(E-1)}.
\]

The exponential bound |exp(w)-1|<=2|w| for |w|<=1 gives |E-1|<=6delta.
Hence |1+k(E-1)|>=1/2. The exact difference numerator is
r(1-k)(E-1), giving |f_i(m)-r|<=12delta<=100delta and |f_i(m)|<=2.
This simultaneously excludes every inverse-coordinate pole.

The following deliberately loose estimates hold for every subset of at most
four children, so the same constants also cover the unconditioned root.
Put P0=prod(r_j), choose real lambda in [0,3], and |z-lambda|<=epsilon.
The finite-product induction and triangle inequalities give

\[
\begin{aligned}
 |P|&\le16,&0\le P_0&\le1,\\
 |P-P_0|&\le6400\delta,&
 |zP-\lambda P_0|&\le16\epsilon+19200\delta\le20000\delta.
\end{aligned}
\]

For H0=b_i-a_i+b_i*lambda*P0, we have H0>=1/100 and
|H-H0|<=60000delta. Consequently,

\[
 \boxed{\operatorname{Re}H\ge1/200,\qquad
 \operatorname{Re}(1+zP)\ge1/2.}
\tag{25.2}
\]

This explicitly excludes the logarithm cut, the transformed-map pole and the
vacancy denominator zero. The activity derivative satisfies |P/H|<=3200<=10000.
No compactness-only assertion is used to select these widths.

For one child coefficient in (24.1), compare the complex value with the same
real anchor. We use |Psi_j(x_j)-Psi_j(r_j)|<=300delta, |Psi_j(x_j)|<=9,
|lambda*P0*Psi_j(r_j)|<=9 and the denominator floors above. The exact quotient
estimate is

\[
 \left|\frac{u}{v}-\frac{u_0}{v_0}\right|
 \le200|u-u_0|+20000|u_0||v-v_0|.
\]

The numerator perturbation is at most 180900delta. Thus each Jacobian entry
changes by at most

\[
 (200\cdot180900+20000\cdot9\cdot60000)\delta
 =10836180000\delta<10^{11}\delta.
\]

At most four entries contribute, so their sum changes by at most 10^12 delta.
The real certificate therefore gives the strict complex row bound

\[
 \sum_{j\in S}|\partial_{m_j}G|
 \le\gamma+10^{12}\delta<\gamma'.
\tag{25.3}
\]

This last contraction use is for genuine nonroot pruning rows. At the root
only (25.2) is used; no three-child contraction is imposed on four children.

## 26. The actual all-type invariant complex neighborhoods

Define the following open sets using the actual 881 coefficient assignments:

\[
 \Omega_i=\bigcup_{r\in[20/71,1]}B(c_i(r),\delta),\qquad
 U_\epsilon=\bigcup_{\lambda\in[0,51/20]}B(\lambda,\epsilon).
\]

Every child subset must refer to genuine successors of the existing geometric
transition. Pruning in AdaptiveComplexNeighborhood records exactly that fact;
its default child accessor is never used for an active nonexistent direction.

Choose a real anchor for each input point. Interpolate linearly from the real
activity and message anchors to the complex inputs. Along the whole segment,
the inverse-coordinate and denominator estimates remain valid. Applying the
actual derivative (24.1), the real mean-value estimate on [0,1], and (25.3)
gives

\[
 |G_{i,S}(z,m)-G_{i,S}(\lambda,c(r))|
 \le\gamma'\delta+10000\epsilon<\delta.
\]

The remaining exact positive slack is 499/10^26. The real output is the center
of y=(1+lambda*prod(r_j))^(-1), and y lies in [20/71,1]. Therefore

\[
 \boxed{z\in U_\epsilon,\quad m_j\in\Omega_{j}\ (j\in S)
 \quad\Longrightarrow\quad G_{i,S}(z,m)\in\Omega_i.}
\tag{26.1}
\]

The quantified theorem covers every actual type and every valid pruning,
including leaves. There is no supplied complex Lipschitz or invariance premise.
The proof reuses the existing full-real-box all-pruning certificate, identifies
it with the real Jacobian, then derives the complex estimates.

The sets are proved open. Every m in Omega_i satisfies |Im(b_i*m)|<=3delta<pi,
so the principal chart is genuinely inverse to f_i on the whole constructed
message domain. The transformed map is jointly holomorphic there, and its
inverse coordinate is exactly the vacancy recursion. For four first-child
messages in Omega_0, the source proves

\[
 \operatorname{Re}\left(1+z\prod_{e=0}^{3}f_0(m_e)\right)\ge1/2,
\]

hence the root denominator is nonzero. Missing first children may use c_0(1),
whose inverse is exactly one.

The same epsilon works independently of the finite domain, holes, root position
and recursion depth. The number 10^-30 is a sufficient explicit width, with no
claim of optimality or physical significance.

### Relation to the graph theorem

Combining (26.1) with Section 20 gives the following complete paper induction.
Carry both nonvanishing of each smaller-domain partition and a typed inverse
message representation. For an internal node, each present child has the exact
successor type and fewer vertices; absent children contribute one. The new
analytic theorem puts the parent message in its own Omega and excludes its
local denominator zero. The exact graph recursion proves parent nonvanishing.
For an arbitrary unconditioned root, center its vertex, use the four smaller
rootDomain instances at type zero and the separate four-factor denominator
bound. The empty partition is one. Strong induction on finite cardinality
therefore gives the candidate explicit consequence

\[
 z\in U_\epsilon\ \Longrightarrow\ Z_{\rm grid}(V;z)\ne0
 \quad\text{for every finite induced grid domain }V.
\tag{26.2}
\]

The new Lean endpoint is the all-type analytic theorem and its root bound.
The final simultaneous finite-graph induction in this paragraph has not been
assembled as a public Lean theorem in this increment. Prior coefficient and
geometric proof scripts also retain their stated uncompiled status. Thus
(26.2) is a paper consequence of the delivered certificate chain, not a
kernel-verified zero-free theorem or an independently reviewed new record.

## 27. Source scope, verification and the next mathematical target

Six new Lean owners under HardCore/Holomorphic have six canonical Scribe
companions: AffineChart, TypedJacobian, TubeEstimates, RowTubeBounds,
InvariantTube and AdaptiveComplexNeighborhood. Their 47 explicitly named public
declarations are paired with StatementSource.FromLean handles. Existing
geometry, independent-set sums, real-message certificates and coefficient
payloads are unchanged.

Mathlib source interfaces were checked at db584cd6d46c92f209a44c0f1c829460d327499d:
complex logarithm differentiation, the slit-plane criterion, exponential
remainder bound, full Frechet finite-product derivative, complex-to-real
restriction and the one-dimensional mean-value inequality. The genuine joint
holomorphy proof uses HasFDerivAt.finsetProd, rather than the scalar-only
DifferentiableAt.fun_finsetProd overload. The repository information-escape
specification read in this continuation is version 4.3, blob
473d684ffda13d291c7df78f0edd8d4922550be6. No new information arena, score or
sealing assertion is attached to the analytic result.

Reproduce the supplementary research checks with

```sh
python research/hard_core_weitz/verify_holomorphic_tube.py
```

The executed run checks all numerical proof budgets with exact Fraction
arithmetic and ten symbolic rational identities with SymPy. At 110 decimal
digits, it checks 384 three-child pruning cases and 48 four-child root cases,
including zero slope and activity zero. Exactly 313 of the three-child cases
satisfy the separately evaluated exact real-anchor row test and receive the
additional contraction/invariance checks. The maximum simultaneous derivative
error is 2.97533988991e-110. Four negative controls detect a missing x factor in
the chart derivative, principal-branch wrapping, an unsupported larger activity
width, and commuting distinct-type projective maps.

Two final executions produced byte-identical JSON. This is a separate
implementation by the same assistant, not independent-author review. The
optional coefficient-source scan was not part of that recorded execution;
the existing full 881-row rational certificate was not rerun. Its unchanged
source theorem is a dependency, and the new b_i<=3 check is a finite Lean proof
script requesting kernel reduction. Numerical regression does not certify any
universal Lean proof term.

No Lean/lake executable is present in the authoring runtime. Source elaboration,
kernel checking, executed axiom closure and Scribe emission have not occurred.
The scripts are mathematically reviewed candidate formalizations, with no new
axioms, admits or native_decide verdicts. The real-to-complex principle is prior
art from Shao and Sun [5]; the exact finite-type coordinate, explicit constants
and the projective ordering calculation are the present application. No
first-formalization or literature-priority claim is established.

The next direct target is the simultaneous actual-grid cardinality induction
in (26.2), with the existing exact coordinate/partition bridge as its consumer.
After that, the same local derivative accounting can control the analytic
logarithm of the actual partition and its activity derivative through exact
vertex elimination. A sharper epsilon should use actual type-dependent margins
and coefficient ratios; arbitrary phase compression or inserting a golden
constant does not preserve those estimates without a separate theorem.


## 28. Closing the simultaneous induction on actual finite grid domains

This continuation reads dev at 22c63f8d3ae9d1f057506c860e89294f115711ea and
extends research head 144fbe648f9343da83c78b003e1ec3c09485eec2. The new endpoint
consumes the actual geometric typing, partition identities and common analytic
neighborhoods of the preceding sections. None is replaced by a new hypothesis.

For every finite induced square-grid domain V, the candidate source now proves

\[
 \boxed{
 z\in U_\epsilon\quad\Longrightarrow\quad
 |Z_{\rm grid}(V;z)|\ge 2^{-|V|}>0,
 \qquad\epsilon=10^{-30}.
 }
\tag{28.1}
\]

The explicit Lean statement for nonvanishing uses the equivalent witness form

\[
 \exists\lambda\in[0,51/20],\quad |z-\lambda|<10^{-30}.
\]

No bound on |V|, specified root, connectivity, rectangular boundary, preassigned
message, supplied nonzero partition or caller-provided contraction constant is
required in the final theorem. The ambient square grid remains infinite; the
actual vertex domain is finite. The ordinary integer-coefficient independence
polynomial is handled by its previously proved evaluation identity.

### Why two conclusions must be maintained together

For every cardinality n, carry the following pair of assertions:

1. Every finite domain V of size n has |Z(V;z)|>=2^(-n).
2. Every such V whose origin is present and whose vertices avoid an actual
   geometric mask F_i has a message m in Omega_i with
   f_i(m)=Z(V\{0};z)/Z(V;z).

The second assertion is needed only for compatible internal nodes. The first
must quantify over all finite domains, because the proper domains occurring
in telescoping need not be supplied with any geometric type. The induction is
strong induction on n, with both assertions for every k<n available together.

At size zero the partition is one, and no internal node with a present origin
exists. At a nonempty untyped domain, choose any vertex and use the proved grid
translation to move it to the origin. Translation preserves both cardinality
and the actual partition. Each present first child in the four-direction root
formula is strictly smaller and compatible with the existing type-zero mask.
The induction hypothesis supplies its actual inverse message in Omega_0.

A missing first child contributes exactly one. This conclusion uses
nonvanishing of its actual proper pre-recentered partition, obtained from the
first induction hypothesis. No argument from real positivity is used at a
complex activity. The neutral coordinate c_0(1) lies in Omega_0 and has inverse
one, so all four factors enter the already proved root denominator bound.
We obtain a genuine complex D with

\[
 \operatorname{Re}D\ge\tfrac12,\qquad
 Z(V;z)=Z(V\{0};z)D.
\]

The proper-domain modulus bound and |D|>=1/2 prove the first assertion at size n.
No same-size typed assertion is used in this root argument.

For the second assertion at size n, the geometric theorem gives every present
child's exact successor type, compatible remaining domain, new origin, and
strict cardinality decrease. The second induction hypothesis represents these
child ratios in their corresponding Omega sets. The first induction hypothesis
again makes every denominator in the ordered elimination legitimate. Missing
actual children have ratio one and are removed from the product by exact
finite-set algebra, yielding precisely the valid pruning consumed by the
analytic map. Invariance gives m_parent in Omega_i, and inverse recovery gives

\[
 f_i(m_{\rm parent})=(1+z\prod_d\alpha(V_d,0;z))^{-1}.
\]

The local denominator has real part at least one half. The actual partition
recursion first proves Z(V;z) nonzero, and only then identifies the displayed
inverse with the actual parent vacancy. Thus neither target nonvanishing nor
target representation is smuggled into its own premises.

This completes both induction components at every finite size. It is the
previously missing source-level connection between the typed analytic theorem
and an actual finite-grid zero-free endpoint.

### Complex absent-child handling is a substantive obligation

On a positive real activity, identical numerator and denominator are automatically
positive. On a complex activity, an absent marked vertex only gives Z/Z. Without
Z!=0 this need not equal one under total field division, and under ordinary
partial division it is undefined. The new complex_child_absent and
complex_root_child_absent lemmas retain precisely the smaller-domain nonzero
premises. Their callers discharge those premises by cardinality induction.
A singleton partition at activity -1 supplies a regression detecting omission
of this guard; that activity is outside the claimed tube.

## 29. Quantitative consequences for actual partition increments and vacancies

The induction preserves more than a Boolean nonzero conclusion. The explicit
root half-plane margin gives (28.1) by multiplying one factor of at least one
half per deleted vertex. This lower bound concerns the actual independent-set
sum, not the relaxed geometric tree's number of paths.

After the global induction, every present origin satisfies the source theorem

\[
 \boxed{\operatorname{Re}\frac{Z(V;z)}{Z(V\setminus\{0\};z)}
 \ge\tfrac12.}
\tag{29.1}
\]

The proved translation equivalence transfers the same statement to any present
marked vertex. Taking the inverse ratio yields the further public conclusion

\[
 \boxed{|\alpha(V,v;z)|\le2}
\tag{29.2}
\]

for every finite domain and every marked vertex. An absent vertex is included:
its ratio is one, now justified by the established global nonvanishing.

These bounds provide a direct next route to an actual analytic free energy.
Choose a complete vertex deletion order and write W_j for its successive
remaining domains. Set

\[
 F_V(z)=\sum_j\operatorname{Log}\left(
       Z(W_{j-1};z)/Z(W_j;z)\right).
\]

Every argument lies in the right half-plane by (29.1), so its principal
logarithm has a consistent analytic branch. Polynomiality and the established
nonzero denominators make every summand holomorphic. Exact telescoping gives
exp(F_V)=Z(V), and at zero activity every summand is zero. Different deletion
orders therefore give the same normalized analytic logarithm on the connected
activity tube. This follows by continuity of their difference in 2*pi*i*Z and
its value zero at z=0.

For this proposed normalized logarithm the elementary estimates give

\[
 -|V|\log2\le\operatorname{Re}F_V(z)\le|V|\log4,
 \qquad |\operatorname{Im}F_V(z)|\le |V|\pi/2.
\]

The upper real bound uses |z|<3 on U_epsilon and the independent-set sum bounded
by the sum over all subsets, |Z(V;z)|<=(1+|z|)^|V|. The imaginary bound follows
from each right-half-plane increment having argument between -pi/2 and pi/2.
These logarithm construction and bounds are the next paper deductions, not
additional public Lean declarations in this increment. Establishing an
infinite-volume limit still requires convergence and boundary control;
finite-volume boundedness alone is not claimed as a thermodynamic-limit theorem.

## 30. Delivered source endpoint and verification status

ActualGraphLift and FiniteGridZeroFree are the two new Lean owners. Each has
a canonical Scribe companion; all sixteen explicitly named public declarations
are covered. ActualGraphLift constructs the neutral message, handles absent
complex children, transfers the actual pruning/product, and proves the typed
and four-direction graph steps. FiniteGridZeroFree performs the simultaneous
strong induction and exposes the quantitative lower bound, nonvanishing,
explicit interval-width theorem, integer-polynomial version, root increment
half-plane and arbitrary marked-vacancy bound.

The final nonvanishing theorem is no longer a conditional graph-transfer
interface. Its only activity premise is membership in the specified common
neighborhood. The geometry, coefficient rows, holomorphic estimates, and graph
identities are concrete proof dependencies. This description is about the
logical shape of the source; it does not upgrade unexecuted dependencies to
kernel-checked truth.

The supplementary exact replay reuses the previous direct independent-subset
enumerator. It does not use the deletion recursion to manufacture reference
partition values, and it does not read any stored result JSON. Across all 512
subdomains of a 3-by-3 square and 21 exact Gaussian-rational activities in the
claimed tube, the executed checks include:

- 10752 quantitative partition lower bounds;
- 59136 marked-vacancy modulus bounds;
- 48384 root increment half-plane and four-child reconstruction checks;
- 64512 present first-child and 129024 missing first-child checks;
- 2304 internal geometric contexts and 5376 internal reconstruction checks;
- 1536 complete vertex-elimination products.

Five negative controls detect omission of the fourth root direction, assuming
target nonvanishing from proper-domain nonvanishing alone, dropping the absent
child's denominator guard, failing to delete the current root, and discarding
the ordered sibling context. These finite tests supplement logical proof review;
they do not prove any universal result or validate a Lean proof term.

```sh
python research/hard_core_weitz/verify_finite_grid_zero_free.py
```

The existing holomorphic and 881-type affine proof scripts are dependencies,
not re-executed verdicts in this replay. Lean/lake is unavailable in the authoring
runtime, so the new and inherited proof scripts still lack an executed
elaboration, kernel/axiom report and Scribe emission in this session. This is an
end-to-end candidate formalization with exact finite regressions, not an
end-to-end kernel-verified theorem or independent-author review.

The public literature versions were rechecked: [1] remains arXiv:2604.02746v1
of 3 April 2026, and [5] remains arXiv:1909.04244v3 with its 2021 journal reference.
Real-to-complex contraction and the finite-graph deletion argument are prior
art. The current work instantiates them through a concrete typed certificate
and now supplies its missing all-domain consumer. The endpoint 2.55 is the
specific proposed extension under investigation; no priority claim, optimal
critical threshold, RH consequence, or solution of the full square-lattice
phase-transition problem is asserted.


## 31. Branch-correct local logarithmic squares

This continuation verifies the seven preceding delivery blobs at
`a565cc4798502a5c77c703aabaf8d4eff98033ad` against the retained delivery bytes;
all seven match. The current dev source read is
`63ba7cc8376be34ff5ba4ed3bb73c0eab56f1f6d`. The existing v4.33.0 Mathlib pin
is `db584cd6d46c92f209a44c0f1c829460d327499d`. The new mathematics consumes the
actual finite-grid endpoint without changing its coefficient or geometric data.

Define the actual insertion factor

\[
 R(V,v;z)=\frac{Z(V;z)}{Z(V\setminus\{v\};z)}.
\]

The preceding origin half-plane theorem transports through the actual marked
translation, so Re R(V,v;z)>=1/2 for every marked vertex and z in U_epsilon.
An absent vertex has factor one, justified by the established nonzero partition.
The principal logarithm of each factor therefore has imaginary part strictly
between -pi/2 and pi/2.

For any two vertices u,v, exact cancellation gives the multiplicative square

\[
 R(V,u;z)R(V\setminus\{u\},v;z)
 =R(V,v;z)R(V\setminus\{v\},u;z).
\]

The four individual factors are in the right half-plane. The sum of the two
arguments on either side lies strictly between -pi and pi. Mathlib's actual
principal-log multiplication theorem therefore upgrades the square to

\[
\boxed{
 \operatorname{Log}R(V,u;z)+\operatorname{Log}R(V\setminus\{u\},v;z)
 =\operatorname{Log}R(V,v;z)+\operatorname{Log}R(V\setminus\{v\},u;z).
}
\tag{31.1}
\]

The equality is exact in the complex numbers, with no unresolved multiple of
2*pi*i. This proves zero additive circulation around every actual deletion
square. It is a concrete local flatness statement for the intended observable.
No global principal-log identity for Z(V;z) is assumed.

This yields a more local proof of deletion-order independence than the
connected-domain uniqueness argument proposed in Section 29. Adjacent swaps
of vertices generate every finite permutation, and each swap is certified by
(31.1). The argument works pointwise throughout the activity tube and does not
need a separate connectedness theorem. It also covers permutations of partial
lists and lists containing repeated or absent vertices.

## 32. One normalized holomorphic logarithm from every complete deletion order

For a list l=(v1,...,vk), define the ordered sum of principal local logs along
successive actual domains W0=V, Wj=W(j-1)\{vj}. The new source proves

\[
 \exp F_{V,l}(z)=\frac{Z(V;z)}{Z(W_k;z)},\qquad F_{V,l}(0)=0.
\]

This statement explicitly retains the remaining domain for an incomplete list.
For a complete distinct enumeration of V, Wk is empty and its partition is one.
Choose the existing Finset.toList enumeration to define F_V. Every other
complete distinct enumeration gives the same exact complex value by the
permutation theorem. Thus the chosen enumeration is absent from the mathematical
content of F_V.

Each local factor is the quotient of two entire independent-configuration sums,
with a nonzero denominator on U_epsilon and image in the right half-plane.
Differentiating its principal logarithm gives

\[
 \frac{d}{dz}\operatorname{Log}R(V,v;z)
 =\frac{Z'_V(z)}{Z_V(z)}-
   \frac{Z'_{V\setminus\{v\}}(z)}{Z_{V\setminus\{v\}}(z)}.
\]

The derivatives telescope on partial lists as well. For a complete list the
remaining empty-domain derivative is zero. The concrete endpoint is therefore

\[
\boxed{
 \exp F_V(z)=Z_V(z),\qquad F_V(0)=0,\qquad
 F'_V(z)=\frac{Z'_V(z)}{Z_V(z)},\qquad
 F_V\text{ is holomorphic on }U_\epsilon.
}
\tag{32.1}
\]

All statements use the original activity neighborhood, with no graph-dependent
shrinking or supplied logarithm-existence premise. The candidate proof also
establishes the exact canonical deletion equation

\[
 F_V(z)=\operatorname{Log}R(V,v;z)+F_{V\setminus\{v\}}(z).
\tag{32.2}
\]

Uniqueness among all normalized holomorphic logarithms can also be deduced on
the connected tube, but that broader uniqueness theorem is not a public
statement in this increment. What is proved in source is exact independence
from every complete distinct deletion enumeration.

### Why the full principal logarithm would be incorrect

Even inside the tiny common activity tube, a large finite collection of isolated
vertices has Z(z)=(1+z)^N and normalized log N*Log(1+z). At N=10^32 and
z=i/(3*10^30), the latter has imaginary part approximately 33.3333, outside the
principal strip. Its exponential still equals the correct partition. The
principal logarithm of the exponential differs by 5*(2*pi*i).

The supplementary regression evaluates this closed isolated-vertex formula;
it does not enumerate an enormous graph or certify the example with interval
arithmetic. The structural point is general: positive-real-part local factors
can accumulate phase. The local square proof preserves that accumulated phase
while ensuring it does not depend on deletion order.

## 33. Volume control and the next observable bridge

Direct comparison of actual independent configurations with all vertex subsets
gives, on the whole complex plane,

\[
 |Z_V(z)|\le\sum_{S\subseteq V}|z|^{|S|}=(1+|z|)^{|V|}.
\]

On U_epsilon, |z|<3. Combined with the preceding lower bound 2^(-|V|),
exp(F_V)=Z_V, and the local argument bound, the new source proves

\[
\boxed{
 -|V|\log2\le\operatorname{Re}F_V(z)\le |V|\log4,
 \qquad |\operatorname{Im}F_V(z)|\le |V|\pi/2.
}
\tag{33.1}
\]

For nonempty domains, the normalized finite-volume pressure F_V/|V| is therefore
uniformly bounded on the same complex neighborhood. This is a concrete input
for a normal-family argument, rather than a conclusion about an infinite-volume
limit. Identifying that limit still needs real-volume convergence and boundary
or tiling control. Chen, Shao and Shi [1] study precisely this relation between
uniform zero-freeness and analytic free energy; their result is literature
context, not an implicit assumption that the present finite-domain limit exists.

The next finite observable identity can be derived before addressing the limit.
Differentiating the actual independent-set polynomial and counting each occupied
vertex once gives

\[
 zZ'_V(z)=\sum_{v\in V}\bigl(Z_V(z)-Z_{V\setminus\{v\}}(z)\bigr),
 \qquad
 zF'_V(z)=\sum_{v\in V}(1-\alpha(V,v;z)).
\tag{33.2}
\]

This uses actual configurations, not independence between neighbors. The
identity avoids dividing by z and therefore includes z=0. Equation (33.2) is
the next proposed formalization target; it is not counted among the current
public declarations. On positive real activity it links the derivative to
expected particle number after the Gibbs probability measure is explicitly
constructed. Such a probability interpretation is not assigned to general
complex activities.

## 34. Source and verification status

The two new owners PartitionLogCocycle and NormalizedPartitionLog have two
canonical Scribe companions and 26 explicitly named public declarations.
They reuse the existing actual partitions, marked translations, zero-free
endpoint and ordered deletion domains. There is no parallel partition model,
new activity width or finite-state payload.

The supplementary verifier reads actual configuration polynomials from the
existing direct independent-subset enumerator. Exact rational and Gaussian-
rational arithmetic checks products, half-planes and logarithmic-derivative
quotients. Principal-log and exponential values are supplemental 100-digit
mpmath regressions, not exact transcendental certificates. It covers all 512
subdomains of a three-by-three square at six activities and checks:

- 3012 deletion squares and 3072 partial/repeated/absent deletion lists;
- 27804 complete deletion orders and exact derivative telescopes;
- 24732 order comparisons, 27804 volume bounds and 4634 zero normalizations;
- three negative controls for branch wrapping, inferring log equality from
  exponential equality alone, and reusing an undeleted sibling domain.

```sh
python research/hard_core_weitz/verify_normalized_partition_log.py
```

Two final runs on the assembled source bytes produced identical JSON. The
maximum square-log and complete-order errors were respectively
2.85746847821e-101 and 5.71493695641e-101. These numbers describe finite numerical
regressions. They do not establish the universal statements or validate their
proof terms. The implementation is by the same assistant, not an independent
author review. Existing coefficient, geometric and holomorphic proof scripts
remain dependencies and were not recompiled or rerun by this verifier.

The source proofs were logically reviewed against the pinned Mathlib logarithm
branch, finite-product, permutation and derivative interfaces. No Lean/lake
executable is available in this runtime, so Lean elaboration, kernel acceptance,
executed axiom closure and Scribe emission remain unperformed. The current result
is a candidate formalization of the normalized finite-volume log and its bounds.
It does not claim a new numerical zero-free threshold, mathematical priority or
an established thermodynamic limit.


## 35. Actual occupation double counting and the Euler moment hierarchy

This continuation starts at `155387b141f83fa5db47966f5906643be5d4830f` and
reads dev at `389f79227a4640dcbcb83ad1bc5a12a5160aaa68`. The new generic
configuration and Gibbs modules depend only on the existing actual independent
sets and standard Mathlib calculus/probability. The later square-grid consumer
also uses the preceding normalized-log and zero-free chain. No coefficient,
geometric transition, activity width, or existing partition definition changes.

For a finite domain V of any simple graph, define unnormalized occupation moments
on the existing configuration family by

\[
 M_k(V;z)=\sum_{S\in\mathcal I_G(V)}|S|^k z^{|S|},\qquad M_0(V;z)=Z_G(V;z).
\]

The new source proves the exact configuration equality

\[
 \mathcal I_G(V\setminus\{v\})
 =\{S\in\mathcal I_G(V):v\notin S\}.
\]

Consequently the total weight of configurations containing v is the partition
on V minus the partition on V without v. The corresponding addition identity
holds in every commutative semiring, with no subtraction or nonzero premise.
Counting each configuration once for each of its occupied vertices then gives,
for arbitrary vertex weights in a commutative ring,

\[
 \sum_{S\in\mathcal I_G(V)}|S|\prod_{u\in S}w_u
 =\sum_{v\in V}\left(Z_G(V;w)-Z_G(V\setminus\{v\};w)\right).
\tag{35.1}
\]

This preserves all correlations between vertex indicators. No independence of
neighbors, graph-size hypothesis, or probability interpretation is used.

Termwise differentiation gives the source-level all-order identity

\[
 \boxed{zM_k'(V;z)=M_{k+1}(V;z)\quad(k\ge0).}
\tag{35.2}
\]

For the empty configuration, the derivative term has coefficient zero. Every
other term satisfies z*z^(n-1)=z^n. This explicit split preserves the endpoint
z=0 and does not divide by z. Combining k=0 with (35.1) completes the target

\[
 \boxed{zZ'_G(V;z)=\sum_{v\in V}
 \left(Z_G(V;z)-Z_G(V\setminus\{v\};z)\right).}
\tag{35.3}
\]

The identity holds at partition zeros as well. Only subsequent normalization
requires Z!=0. Wherever that condition holds, quotient differentiation and
(35.2) give a normalized response hierarchy:

\[
 \boxed{z\frac{d}{dz}\frac{M_k}{Z}
 =\frac{M_{k+1}}{Z}-\frac{M_k}{Z}\frac{M_1}{Z}.}
\tag{35.4}
\]

This general lemma is the common algebraic owner of both the mean and the
fluctuation calculation below. Real and complex specializations reuse it.

## 36. A standard Gibbs PMF, its actual mean and its fluctuation response

For lambda>=0, the empty independent configuration contributes one and all
weights are nonnegative, so the existing theorem gives Z_G(V;lambda)>=1.
Define the actual mass on all finite subsets of the ambient vertex type by

\[
 p_{V,\lambda}(S)=
 \begin{cases}\lambda^{|S|}/Z_G(V;\lambda),&S\in\mathcal I_G(V),\\
 0,&\text{otherwise}.\end{cases}
\]

The new source proves nonnegativity and that the finite support sums to one,
then constructs Mathlib's `PMF (Finset alpha)` using `PMF.ofFinset`. Its
real-valued point masses are proved equal to the displayed weights. The
ambient graph need not be finite; only V is finite. This is a probability law
on actual configurations, with no newly assumed distribution or normalizer.

Finite PMF summation yields, for every k,

\[
 \mathbb E_{p_{V,\lambda}}|S|^k=M_k(V;\lambda)/Z_G(V;\lambda).
\]

The actual one-vertex event and the expected cardinality satisfy

\[
 \boxed{\Pr(v\in S)=1-\frac{Z_G(V\setminus\{v\};\lambda)}{Z_G(V;\lambda)},
 \qquad \mu_V(\lambda)=\mathbb E|S|=\sum_{v\in V}\Pr(v\in S).}
\tag{36.1}
\]

A vertex outside V has occupancy zero. The source also proves
0<=mu_V<=|V|. For the centered variance, it first uses the actual weighted
squared deviations, then derives its raw-moment expression:

\[
 \operatorname{Var}_{V,\lambda}(|S|)
 =\sum_Sp_{V,\lambda}(S)(|S|-\mu_V)^2
 =\frac{M_2}{Z}-\left(\frac{M_1}{Z}\right)^2\ge0.
\]

Specializing (35.4) to k=1 gives the further completed source theorem

\[
 \boxed{\lambda\,\mu'_V(\lambda)=\operatorname{Var}_{V,\lambda}(|S|).}
\tag{36.2}
\]

For positive lambda this proves mu'_V>=0. At lambda=0 the mean and variance
are both zero; the PMF is still normalized, with only the empty configuration
having nonzero mass. The scaled identity includes that endpoint directly.
No second-moment expression is mislabeled as a centered variance, and no sum
of individual Bernoulli variances is substituted for the full correlated one.

These facts hold for every finite domain of every simple graph and every
nonnegative real activity. They do not depend on the square-grid zero-free
certificate or on the cap 51/20. They are classical hard-core/exponential-family
identities, not new extremal inequalities. Their formal role is to connect the
previous analytic objects with the precise Gibbs observable.

## 37. The normalized grid logarithm now measures actual occupation

The square-grid consumer applies the previous normalization F'_V=Z'_V/Z_V,
actual nonvanishing, and (35.3), obtaining throughout the same ActivityTube

\[
 \boxed{zF'_V(z)=\frac{M_1(V;z)}{Z_V(z)}
 =\sum_{v\in V}(1-\alpha(V,v;z)).}
\tag{37.1}
\]

At real 0<=lambda<=51/20 this is exactly the finite-PMF expected cardinality,
with the real mean cast into the complex numbers. The proof transports the
actual finite sums and weights, rather than postulating an expectation identity.
At general complex activities, (37.1) remains an analytic quantity; it is not
assigned probability values.

The already-owned bound |alpha(V,v;z)|<=2 now gives a volume-uniform analytic
response estimate, also formalized in this increment:

\[
 \boxed{|zF'_V(z)|\le3|V|.}
\tag{37.2}
\]

For nonempty V, this bounds the scaled derivative of F_V/|V| by three on the
common complex neighborhood. It does not assert that dividing by z is safe at
zero, or that differentiating a thermodynamic limit is already justified.

### Next finite-volume target: linear-volume fluctuation control

There is now a direct paper route from (37.2) to a graph-size-uniform variance
bound. The function H_V(z)=M_1(V;z)/Z_V(z) is holomorphic on ActivityTube.
For every real lambda in [0,51/20], the closed disk of radius epsilon/2 around
lambda lies inside that tube. Cauchy's derivative estimate applied to (37.2)
gives

\[
 |H'_V(\lambda)|\le6|V|/\epsilon.
\]

The normalized moment identity (35.4), together with the real coefficient
transport, identifies lambda*H'_V(lambda) with the actual real Gibbs variance.
Thus the candidate chain yields the paper consequence

\[
 0\le\operatorname{Var}_{V,\lambda}(|S|)
 \le\frac{153}{10\epsilon}|V|<16\cdot10^{30}|V|.
\]

The final strict inequality is intended for nonempty V; the empty variance is
zero, and a non-strict bound with 16*10^30 covers all finite domains. This is an
extremely conservative sufficient constant. Its point is the linear volume
scaling, not numerical sharpness. The Cauchy-domain inclusion, derivative bound
and full real/complex variance transport have not been assembled as new public
Lean declarations here. They are the next concrete proof target. No infinite-
volume susceptibility, central limit theorem or phase-transition theorem is
asserted by this finite-volume deduction.

## 38. Literature interface and executed verification

Davies, Sandhu and Tan [7] study occupancy and variance fractions through the
operator lambda*d/dlambda, explicitly relating them to expected configuration
size and its variance. Zhang and Xu [8] continue that study in 2026 with
extremal bounds. Their work confirms that the observable and response in
(36.1)-(36.2) are standard active research quantities. This increment does not
claim their formulas as new discoveries or claim to settle their extremal
conjectures. Chen, Shao and Shi [1] remains the external guide for connecting
uniform complex zero-freeness to analytic free energy.

The current dev owner `D5/S3/Analytic/ZetaGibbs.lean` was also read. It already
uses standard PMF normalization for an infinite logarithmic-integer ensemble.
That source requires a summability condition on its inverse temperature. The
present finite hard-core law instead normalizes the existing independent-set
configuration family; the infinite zeta ensemble and its convergence condition
are not silently imported or identified with the graph model. Mathlib's
finite-support PMF constructor is reused directly.

Three new Lean owners have three canonical Scribe companions and 36 public
declarations: OccupationMoments (12), GibbsOccupation (18), and
Holomorphic/OccupationResponse (6). Every declaration has a source-bound
StatementSource.FromLean handle. The existing partition, normalized logarithm,
geometric and analytic owners are unchanged.

The independent verifier directly enumerates independent subsets of all 76
labeled simple graphs on at most four vertices and all 512 domains of a 3-by-3
square. It computes reference polynomial derivatives coefficientwise and uses
exact rational and Gaussian-rational arithmetic. It checks 20580 Euler moment
identities, 17800 normalized responses, 4116 partition occupation identities,
3528 Gibbs normalizations, 21168 raw-moment identities, 15534 vertex marginals,
and 3528 fluctuation-response identities. There are 556 partition-zero cases
where only the denominator-free identities are tested. All 588 domain instances
include a zero-activity probability test.

Seven negative controls detect a missing activity factor, division by zero
activity, false independence of vertices, dropped indicator covariances,
uncentered second moments, normalization at a partition zero, and omission of
the empty configuration. Exact tests were rerun after final source assembly
and the emitted JSON was byte-identical.

```sh
python research/hard_core_weitz/verify_occupation_response.py
```

The verifier reuses only the earlier exact Gaussian-rational arithmetic class;
its configuration and probability checks are explicitly performed from finite
subsets. It does not read a stored success verdict or execute Lean proof terms.
The implementation is by the same assistant, not independent-author review.
Lean/lake is absent from the authoring runtime; no source elaboration, kernel
acceptance, executed axiom closure or Scribe emission is claimed. The generic
moment/Gibbs modules have no dependency on the candidate zero-free theorem;
the normalized-log consumer and the next Cauchy deduction do inherit it.
No additional zero-free endpoint, accepted numerical record or mathematical
priority claim is made in this increment.

[7] Ewan Davies, Juspreet Singh Sandhu and Brian Tan. *On expectations and
variances in the hard-core model on bounded degree graphs*. arXiv:2505.13396v2,
especially the definitions of free energy, occupancy fraction and variance
fraction in Section 1.
https://arxiv.org/html/2505.13396v2

[8] Weiyuan Zhang and Kexiang Xu. *On expectations and variances in the hard-core
model*. arXiv:2604.01717v1 (2 April 2026).
https://arxiv.org/abs/2604.01717


## 39. Uniform finite-volume variance from the common complex neighborhood

This continuation reads dev at `5e5d5e07c56044176abd8b16b1414f1368889ff3`
and extends research head `9ea79d4b1aca3a56636e8c29c8585d585d2be8ae`.
The final target proposed in Section 37 is now supplied as candidate Lean
source. The existing geometric types, real certificate, complex neighborhood,
partition definition and Gibbs PMF are unchanged.

Let H_V(z)=M_1(V;z)/M_0(V;z), where the existing zeroth-moment theorem identifies
M_0 with the actual independent-set partition. The prior response identity gives
H_V(z)=z F'_V(z), and the prior marked-vacancy bound gives |H_V(z)|<=3|V| on the
same ActivityTube. Since both moments are polynomials and the denominator is
nonzero there, H_V is holomorphic throughout this common open set.

For each real lambda in [0,51/20], including both endpoints, the entire closed
disk of radius epsilon/2 centered at lambda lies strictly inside ActivityTube.
The proof uses the same real center as the tube witness. In particular,
continuity on the closed disk and holomorphy in its interior are derived, not
postulated as an external Cauchy-bound premise.

The source applies Mathlib's existing first-derivative Cauchy estimate:

\[
 |H'_V(\lambda)|\le\frac{3|V|}{\epsilon/2}
 =\frac{6|V|}{\epsilon},\qquad \epsilon=10^{-30}.
\]

The real variance is transported exactly to the complex derivative using the
same finite moment sums in both fields and the earlier normalized-moment
response theorem. This avoids assuming any unproved interchange of real and
complex differentiation. The resulting equality is

\[
 (\operatorname{Var}_{V,\lambda}N:\mathbb C)=\lambda H'_V(\lambda),
 \qquad N(S)=|S|.
\]

Consequently the new source proves

\[
 \boxed{
 0\le\operatorname{Var}_{V,\lambda}N
 \le\frac{6\lambda}{\epsilon}|V|
 \le C|V|,\qquad C=16\cdot10^{30},\quad 0\le\lambda\le51/20.
 }
\tag{39.1}
\]

The empty domain and zero activity are included. No division by lambda occurs.
The sharp intermediate coefficient from the interval cap is 153/(10 epsilon);
C is a convenient larger integer. The adjective sharp here refers only to
multiplying these chosen coarse constants, not to a sharp variance theorem.

The large constant is a cost of the deliberately tiny sufficient tube, not a
numerical estimate of physical fluctuations. The bound need not be useful for
ordinary finite simulation sizes. Its useful mathematical feature is that one
coefficient works for every finite induced grid domain, with arbitrary holes
and boundaries. This is a standard analytic consequence of the project's
candidate zero-free chain, not an independently reviewed new extremal record.

## 40. Discrete particle counts, continuous response, and density concentration

The microscopic sample space is discrete: each vertex is occupied or vacant,
and only independent vertex subsets are allowed. The activity varies
continuously, and a finite sum over those discrete states produces a polynomial
in that activity. For example, on two adjacent vertices the three configurations
are empty, left occupied and right occupied. Direct calculation gives

\[
 Z(\lambda)=1+2\lambda,\qquad
 \mathbb E N=\frac{2\lambda}{1+2\lambda},\qquad
 \operatorname{Var}N=\frac{2\lambda}{(1+2\lambda)^2}.
\]

Thus integer-valued occupation and smooth response functions coexist in the
same model. The complex neighborhood is an analytic tool for controlling
these responses uniformly. It does not assert that physical space is discrete,
introduce dynamical time, or establish a spatial continuum limit.

For a nonempty domain of size n, the new source uses the actual finite PMF to
form the centered density moment. Exact algebra gives

\[
 \mathbb E_{V,\lambda}\left[
   \left(\frac{N}{n}-\frac{\mathbb E N}{n}\right)^2\right]
 =\frac{\operatorname{Var}_{V,\lambda}N}{n^2}\le\frac{C}{n}.
\tag{40.1}
\]

Every sum is over the existing independent configurations and uses the
existing PMF point masses. There is no independence assumption between sites.
A finite second-moment event estimate then gives, for t>0,

\[
 \boxed{
 \Pr_{V,\lambda}\left(
 \left|\frac{N}{n}-\frac{\mathbb E N}{n}\right|\ge t\right)
 \le\frac{C}{t^2 n}.
 }
\tag{40.2}
\]

The source also checks that its explicit event sum is between zero and one.
The event bound is useful only when its right side is below one; (40.2) may
always be combined with the elementary upper bound one. These formulas imply
vanishing fluctuations about the finite-volume mean along any sequence of
nonempty domains with size tending to infinity. This is a paper asymptotic
consequence of the explicit finite inequalities, not a separately declared
Lean limit theorem in this increment.

Concentration about each domain's own mean is weaker than convergence to a
common thermodynamic density. Establishing such a mean limit still requires
boundary/tiling or other convergence control. Neither a central limit theorem
nor a continuum field equation follows from (40.1)-(40.2) alone. The present
research dependency remains one chain: actual configurations, partition,
uniform complex control, occupation response, and finite-volume fluctuations.

## 41. Source, literature and verification of this continuation

Two Lean owners, Holomorphic/LinearVolumeVariance and
Holomorphic/OccupationConcentration, have two canonical Scribe companions and
17 explicitly named public declarations. The first imports the existing
OccupationResponse owner and Mathlib.Analysis.Complex.Liouville; the second
consumes the first and the already-owned actual Gibbs PMF. No finite geometric
payload is changed. The endpoint variance and concentration statements have
only the finite-domain, real-activity-interval and positive-threshold premises
appropriate to their assertions, with nonemptiness required for density bounds.
The analytic and probability ingredients are concrete proof dependencies.

The Cauchy derivative API was read at the existing Mathlib pin
`db584cd6d46c92f209a44c0f1c829460d327499d`. In particular, the proof checks the
closed-disk inclusion before applying DifferentiableOn.diffContOnCl_ball and
Complex.norm_deriv_le_of_forall_mem_sphere_norm_le. Cauchy's theorem and the
second-moment event inequality are established mathematics; no novelty in
those general tools is asserted.

The literature versions read include Davies, Sandhu and Tan [7], v2, and
Zhang and Xu [8], v2 revised 5 June 2026. They study occupancy and variance as
actual hard-core observables. Their extremal graph results are distinct from
this sufficient upper bound on finite induced square-grid domains in a
specified activity interval. No claim to solve those separate extremal
problems or improve their constants is made.

The supplementary verifier enumerates actual independent configurations of
all 512 subdomains of a 3-by-3 grid. It evaluates polynomial derivatives
coefficientwise and uses exact rational/Gaussian-rational arithmetic. It checks
16384 rational points on the chosen Cauchy boundary circles, 2048 actual
variance-response and linear-bound instances, 2044 nonempty density second
moments and 10220 actual Gibbs tail probabilities. The boundary samples
supplement the universal closed-disk proof; finite sampling does not establish
holomorphy, Cauchy's theorem, or the all-domain variance assertion.

Five elementary diagnostics exercise mistakes involving a size-dependent
radius, discrete support alone, incorrect density normalization, a boundary
pole, or using only the value at the disk center. They are fixed diagnostic
examples, not a claim of exhaustive mutation coverage. Two complete executions
of the final verifier produced byte-identical JSON.

```sh
python research/hard_core_weitz/verify_linear_volume_variance.py
```

The verifier reuses the earlier actual configuration enumerator and exact
Gaussian-rational arithmetic. It never reads a saved success verdict as an
input. It is another implementation by the same assistant, not independent
researcher review. The local environment has no Lean/lake executable; new and
inherited Lean proof terms have not been elaborated or kernel-checked here.
No executed axiom-closure report or Scribe emission is claimed. The delivered
result is a logically reviewed candidate formalization with supplementary
finite regressions, inheriting the existing zero-free chain's validation status.
