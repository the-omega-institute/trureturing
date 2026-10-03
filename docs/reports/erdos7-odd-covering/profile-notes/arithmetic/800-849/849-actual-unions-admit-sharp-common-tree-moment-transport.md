# Actual unions admit a sharp common-tree moment transport

[Common source](../350-399/388-source-global-substitution-collision-moment.md) · [Shared-old moments](848-common-old-coordinate-refines-collision-moments.md) · [Whole-cover prefix certificates](../../321-384/340-whole-cover-completion-constrains-original-prefix-loads.md)

The complete new-coordinate union, including all cross-column overlaps,
has a direct second-moment comparison under a common random tree. For a
uniform \(r\)-branch subtree of an \(s\)-ary tree, put
\[
 c_{r,s}=\frac{s-r}{r(s-1)}.
\]
For any fixed finite-height forbidden union with original Haar fraction
\(\mu\), its pulled-back Haar fraction \(\alpha\) satisfies
\[
 \boxed{\mathbb E_\Theta\alpha=\mu,\qquad
 \mathbb E_\Theta\alpha^2\le
 (1-c_{r,s})\mu^2+c_{r,s}\mu.} \tag{1}
\]
The coefficient is sharp; unions determined by the first digit attain it.
For \(r=5,s=7\), it is \(1/15\). No reciprocal cofactor sum occurs in
(1), because the argument transports the actual union rather than its
labelled load. A fixed old law can then be integrated on the same source.
An embedding-dependent old law cannot be inserted without a further
argument; Section 5 gives an exact counterexample even when its marginal
is Haar.

This is an ordinary application of finite sampling without replacement,
conditional variance and orthogonal martingale differences to report 388's
source. It is not a new general probability principle or a Lean result.
It supplies a comparison with the original union moments, not the strict
arithmetic budget required to settle unrestricted Erdős #7.

The first moment is the finite-population unbiasedness of
[Horvitz--Thompson, *A Generalization of Sampling Without Replacement From
a Finite Universe* (1952)](https://doi.org/10.1080/01621459.1952.10483446):
each original leaf has inclusion probability \((r/s)^B\), giving the
sample-mean coefficient \(s^{-B}(r/s)^{-B}=r^{-B}\). Conditional variance
is also existing library material; the pinned Mathlib provides
`integral_condVar_add_variance_condExp` in `Mathlib/Probability/CondVar.lean`.
The tree coefficients below are the application-specific calculation;
these references do not claim that this application has been compiled.

## 1. The common tree and the exact observable

Let \(2\le r<s\) be integers and let \(B\ge1\) be a finite height.
Primality is not needed for this sampling calculation. At every node of
the full \(s\)-ary tree, independently choose a uniform \(r\)-subset of
its children. Only the descendants reached from the root form the sampled
tree \(T_\Theta\); it has exactly \(r^B\) leaves at depth \(B\).
Sampling choices at unreached nodes does not change the law of the reached
tree. This is the unlabelled image-tree law of report 388.

For a function \(f:[s]^B\to\mathbb R\), define
\[
 A_\Theta(f)=r^{-B}\sum_{w\in T_\Theta}f(w),\qquad
 \mu=\mathbb E_{H_s}f,
 \tag{2}
\]
where \(H_s\) is uniform on all \(s^B\) words. The same tree is used for
every original label. For the covering application, \(f\) is the indicator
of the union of all active original \(s\)-prefix cylinders, so
\(A_\Theta(f)=\alpha\). Repeated prefixes and cylinders contained in
shorter active prefixes count once in \(f\). Neither the labels nor their
phases are reselected when forming this union.

Equivalently, retain the minimal active prefixes. They form an antichain;
at an active node the local union fraction is one. At every other internal
node it is the average of the fractions in its selected children. This is
an evaluation of the same literal union, not a deletion of original
liability from the covering problem.
The repository already has
[canonical prefix-union and adaptive event-tree code](../../../frontier/cover-geometry/fibre-credit-partition/adaptive_prefix_union.py);
that representation need not be reimplemented to use the moment comparison.

## 2. Exact finite-sampling recursion

Restrict \(f\) to child \(a\in[s]\). Let \(A_a\) be its independently
sampled subtree average, \(\mu_a=\mathbb EA_a\), and
\(q_a=\mathbb EA_a^2\). At height zero the subtree average is its leaf
value. If \(S\) is the uniform root \(r\)-subset, independent of these
subtree choices, then
\[
 A=\frac1r\sum_{a\in S}A_a.
\]
Using \(\Pr(a\in S)=r/s\) and
\(\Pr(a,b\in S)=r(r-1)/(s(s-1))\) for \(a\ne b\),
\[
 \mathbb EA=\frac1s\sum_a\mu_a,\qquad
 \mathbb EA^2=\frac1{rs}\sum_aq_a
 +\frac{r-1}{rs(s-1)}\sum_{a\ne b}\mu_a\mu_b. \tag{3}
\]
Subtracting the square of the mean yields the variance form
\[
 \operatorname{Var}(A)
 =\frac1r\mathbb E_{a\sim H_s}\operatorname{Var}(A_a)
 +c_{r,s}\operatorname{Var}_{a\sim H_s}(\mu_a). \tag{4}
\]
The child averages may be correlated as functions of an old coordinate.
Equation (4) first fixes that coordinate; it uses only independence of
the random child trees under the stated sampling law.

## 3. The exact contribution of every prefix depth

Let \(f_j=\mathbb E_{H_s}[f\mid\text{first }j\text{ digits}]\), so
\(f_0=\mu\) and \(f_B=f\). Write
\[
 D_j(f)=\mathbb E_{H_s}(f_j-f_{j-1})^2\quad(1\le j\le B).
\]
Finite conditional expectation gives orthogonal differences, hence
\(\sum_jD_j(f)=\operatorname{Var}_{H_s}(f)\).
Expanding (4) down the finite tree proves the exact identity
\[
 \boxed{\operatorname{Var}_\Theta A_\Theta(f)
 =c_{r,s}\sum_{j=1}^{B}r^{-(j-1)}D_j(f).} \tag{5}
\]
Indeed, the root variance of the child means is \(D_1(f)\). At each
successive level (4) multiplies the averaged child variance by \(1/r\);
the mean of the child depth-\(j\) energies is the root depth-\(j+1\)
energy. This is finite induction on \(B\).

Every coefficient \(r^{-(j-1)}\) is at most one. Thus
\[
 \operatorname{Var}_\Theta A_\Theta(f)
 \le c_{r,s}\operatorname{Var}_{H_s}(f). \tag{6}
\]
For an indicator, \(\operatorname{Var}_{H_s}(f)=\mu(1-\mu)\), giving
(1). A nonconstant indicator depending only on the first digit has
\(D_j=0\) for \(j\ge2\), so it attains (6) and establishes sharpness.
Conversely, for \(r>1\) equality forces every \(D_j\), \(j\ge2\), to
vanish. More detailed prefix information gives the exact improvement
\[
 (1-c_{r,s})\mu^2+c_{r,s}\mu-\mathbb E_\Theta\alpha^2
 =c_{r,s}\sum_{j=2}^{B}(1-r^{-(j-1)})D_j(f). \tag{7}
\]
This keeps deeper distinctions without replacing them by a count of
original labels.

## 4. Integrating one fixed old law

In the arithmetic source, let \(v=(u,x)\) denote the safe \(r\)-coordinate
and the old cofactor word. Fix any finite law \(\nu\) of \(v\), independent
of the newly sampled tree. The components of \(v\) need not be independent
of each other. Fix all original residues once. Let \(f_v\) be the union
indicator of exactly those original \(s\)-prefixes whose old constraints
are satisfied at \(v\), and put
\[
 \mu(v)=\mathbb E_{H_s}f_v,\qquad
 M_1=\mathbb E_\nu\mu(v),\qquad M_2=\mathbb E_\nu\mu(v)^2.
\]
For the one common tree, set
\(M_{j,\Theta}=\mathbb E_\nu\alpha_\Theta(v)^j\).
Finite averaging of (1) and (5) gives
\[
 \boxed{\mathbb E_\Theta M_{1,\Theta}=M_1,\qquad
 M_2\le\mathbb E_\Theta M_{2,\Theta}
 \le(1-c_{r,s})M_2+c_{r,s}M_1.} \tag{8}
\]
No independence of old congruence events, cofactor cutoff, numerical
distinctness assumption or separate cross-column estimate is needed for
this comparison. All old phases and overlaps already enter \(f_v\).

For \(r=5,s=7\), the second bound is
\[
 \mathbb E_\Theta M_{2,\Theta}\le\frac{14}{15}M_2+\frac1{15}M_1.
 \tag{9}
\]
This compares the complete original and transported union moments; it
does not give numerical values for the actual \(M_1,M_2\).
It also shows that tree averaging itself does not decrease the union's
second moment. Its added variance is exactly the weighted prefix energy
in (5), averaged over the same old law.

For a fixed \(0<\delta\le1/2\), write \(d_\delta=4\delta(1-\delta)\).
The elementary inequality between an average of minima and the minima of
averages shows that at least one common tree satisfies
\[
 \min\{M_{1,\Theta},M_{2,\Theta}/d_\delta\}
 \le\min\{M_1,[(1-c_{r,s})M_2+c_{r,s}M_1]/d_\delta\}. \tag{10}
\]
This is one fixed-old-law stage comparison. It does not choose a separate
tree for each old point, and it does not assert simultaneous coordinatewise
optimality of the first and second moments. Applying it to a full BBMST
construction still needs the actual legal exposure order, the old laws at
every stage and a strict sum of all stage charges below one.

## 5. Marginal Haar does not replace tree independence

Already at height one, sample a uniform \(r\)-subset \(S\subset[s]\),
then sample an old variable \(X\) uniformly from \(S\). The marginal of
\(X\) is uniform on \([s]\). Use the fixed family
\(f_x(y)=\mathbf1_{\{y=x\}}\), with \(\mu(x)=1/s\).
On the actual joint law, \(X\in S\) always, so \(\alpha_S(X)=1/r\) and
\[
 \mathbb E\alpha_S(X)^2=1/r^2>1/(rs).
\]
But substituting only the marginal old law into (8) would give
\[
 (1-c_{r,s})/s^2+c_{r,s}/s=1/(rs).
 \tag{11}
\]
For \(5,7\), the two values are \(1/25\) and \(1/35\). The error is
the lost dependence between the tree and the old coordinate. An actual
kernel \(\nu_\Theta\) created by source selection or later conditioning
must be retained jointly; (8) cannot be applied to its marginal without
an additional comparison.

## 6. A genuine old-prime fibre already gains from union compression

Take the literal original congruences
\[
 (d,a_d)=(3,0),(5,0),(7,0),(9,2),(15,2),(21,4),(35,2),(63,1),(105,1).
 \tag{12}
\]
Their moduli are odd, distinct and divisor closed; their 17 comparable
pairs are disjoint. Fix safe \(u=1\bmod5\) and old \(x=1\bmod9\).
This point avoids every original not divisible by seven. The active
seven-prefixes, with original identities retained, are
\[
 7\mapsto0,\quad21\mapsto4,\quad63\mapsto1,\quad105\mapsto1.
\]
The old cofactors are \(1,3,9,3\), so no future prime is being treated as
old. Their actual union has \(\mu=3/7\) and only first-digit energy.
Consequently the exact transported union moment is \(1/5\). The labelled
load instead counts digit one twice and has moment \(38/105\), losing
\(17/105\) of overlap credit.

This is a legal fixed old-survivor fibre, not a whole cover or a claim
that its point mass supplies all BBMST cylinder caps. The integer eight is
uncovered by the original family. It demonstrates that the union improvement
is available even when all old cofactors use primes below the new block.

## 7. What the random-injection literature supplies

Kamčev, Sudakov and Volec,
[*Bounded colorings of multipartite graphs and hypergraphs*, arXiv:1601.02271v2](https://arxiv.org/abs/1601.02271v2),
Theorem 2.2 and Appendix A, Theorem A.1, provide a reusable lopsided
dependency theorem for products of independent uniform injections.
Their canonical events prescribe finitely many images. The conflict graph
joins inconsistent prescriptions: the same domain element sent to
different images, or the same image assigned to different preimages.
For a canonical event \(E_i\) and nonneighbors \(J\), the conclusion is
\[
 \Pr(E_i\mid\bigcap_{j\in J}E_j^c)\le\Pr(E_i)
 \tag{13}
\]
whenever the conditioning event has positive probability. This is not a
pairwise negative-correlation statement.

For a finite source tree, assign an independent uniform injection
\(\sigma_z:[r]\hookrightarrow[s]\) at every predetermined source node
\(z\in[r]^{<B}\), and define the rooted embedding by
\(\Psi(zi)=\Psi(z)\sigma_z(i)\). With node tags retained,
\(\{\Psi(z)=w\}\) is a canonical event of probability \(s^{-|w|}\)
for fixed words \(z,w\) of equal depth. Forgetting the ordering of source
children gives the same uniform-subset image-tree law used in (2).

Changing that ordering transports every output phase by one common
rooted-tree automorphism. It preserves the whole new-block Haar union for
each fixed old point. It does not preserve the same literal exposed prefix
or an arbitrary embedding-dependent old law without transporting those
data as well.

Target-prefix survival is the disjoint union of these canonical events
over all possible source words. Inequality (13) transfers to disjoint
groups if every pair of constituents from nonadjacent groups is
nonadjacent. However, the graph formed by placing an edge whenever any
constituent pair conflicts is complete on nonempty target-prefix groups
when \(r\ge2\). If their first target digits differ, choose the same first
source child; if they agree, choose different first source children. The
two corresponding canonical prescriptions conflict at the root in either
case. This proves a limitation of that grouping construction, not of every
possible dependency graph.

The paper's Lemma 2.1 gives the sufficient thresholds
\(\Pr(E_i)\le1/4\) and
\(\sum_{j\sim i}\Pr(E_j)\le1/4\). The arithmetic bad-event encoding
and its conflict loads have not been shown to meet them. The useful
published theorem is therefore available, but a sparse grouped encoding
or a successful canonical-event budget remains an additional obligation.

## 8. Verification and remaining arithmetic obligation

The [exact finite checker](../../../frontier/cover-geometry/source-global-collision-moment/tree_union_transport.py)
and [results](../../../frontier/cover-geometry/source-global-collision-moment/tree_union_transport.json)
compare direct common-tree enumeration with the original-word martingale
energies. They retain nested and repeated prefix unions, check the sharp
first-digit case, and check the correlated-old-law failure in (11).
The all-height argument is (3)--(7); finite enumeration is not a substitute
for its quantifiers or a new Lean check.

The default cases check 651 functions, including every depth-two ternary
indicator and every one-level seven-child indicator, in 34,019 direct
common-tree evaluations. They also compare deeper prefix energies and
the literal old-survivor example (12). Replay from the repository root:

```sh
python3 -B -I -S -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/source-global-collision-moment/tree_union_transport.py --check
```

The remaining task is to control the actual original union moments under
the old laws needed by a complete covering argument, or to construct a
legal EB1 replacement preserving all deleted-class liability. Under a
hypothetical full cover, the bad union above an old survivor can have
\(\mu=1\); (1) then also equals one. Thus sharp probabilistic transport
alone creates no strict noncoverage margin. The needed strictness must
come from arithmetic restrictions on the full family or a law construction
with a justified common-source comparison.
