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
