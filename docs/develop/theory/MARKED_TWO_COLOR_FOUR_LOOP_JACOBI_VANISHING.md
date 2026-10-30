# Marked two-color four-loop Jacobi vanishing

## 1. The original quotient and the stable domain

**Definition 1.1 (Flag graphs).** All vector spaces are over $\mathbb{Q}$. A finite graph consists of a finite flag
set $H$, a fixed-point-free edge involution $\iota$, and a partition of
$H$ into vertex fibers of size one or three. Each size-three fiber has
an actual three-cycle $\omega_v$. Loops and parallel edges retain their
separate edge IDs and flags. One-valent vertices are either numbered
anchors in a set $A$, or ordinary legs of a specified color. Isomorphisms
preserve the involution, fibers, three-cycles, anchor numbers, and colors.
The bare topological circle is included as the usual exceptional
genus-one graph without vertices. An auxiliary bivalent cell on it is
only a cellular coordinate device, never a Jacobi vertex or an anchor.

**Definition 1.2 (The original quotient).** The original space $\mathcal{P}_{g,\boldsymbol\ell}$ is the rational span of
connected such graphs with first Betti number $g$ and ordinary color
population $\boldsymbol\ell$, modulo AS, oriented IHX, and CL. AS reverses
one three-cycle with scalar $-1$. CL exchanges two neighboring ordinary
legs along a path between their attachment vertices, with the path
orders unchanged. It applies to different ordinary colors too. Anchors
never participate in CL. In particular a marked leg is an ordinary
singleton color, not an anchor. This is the quotient of the primary source [Kuperberg](../../../Library/Topology/kuperberg2026oddvas.md), without extra graph relations.

**Definition 1.3 (Oriented IHX).** For four external flags $h_1,h_2,h_3,h_4$ and a central edge
$k^+\leftrightarrow k^-$, fix the oriented resolutions

<a id="eq-ihx"></a>
<a id="eq:ihx"></a>

**Equation 1.1 (`eq:ihx`).**

$$
\begin{array}{c|cc}
 &\text{first fiber and cycle}&\text{second fiber and cycle}\\\hline
I&(k^+,h_1,h_2)&(k^-,h_3,h_4)\\
H&(k^+,h_1,h_3)&(k^-,h_2,h_4)\\
X&(k^+,h_1,h_4)&(k^-,h_2,h_3)
\end{array}
\qquad I-H+X=0.
$$

The central endpoints are distinct. The edge involution is unchanged;
in particular external flags may already be paired to each other. The
cycles in this table are retained, not sorted after resolution.
This is the flag version of the usual oriented Jacobi identity. As a
check independent of a picture, the transpositions $(12),(23),(34)$ of
external flags send $(I,H,X)$, after AS normalization, respectively to
$(-I,X,H)$, $(H,I,-X)$, and $(-I,X,H)$. Each negates the relator. Thus
checking one port labeling checks every labeling with its correct sign.

**Definition 1.4 (AS sign and auxiliary directions).** An unoriented graph isomorphism $\phi$ between graphs with selected
three-cycles has a scalar

<a id="eq-chi"></a>
<a id="eq:chi"></a>

**Equation 1.2 (`eq:chi`).**

$$
\chi(\phi)=\prod_{v\in V_3}\chi_v(\phi),\qquad
\phi\omega_v\phi^{-1}=\omega_{\phi(v)}^{\chi_v(\phi)},
\quad \chi_v(\phi)\in\{1,-1\}.
$$

This scalar is the AS sign. Independently choose an orientation of each
edge, an ordered pair of its actual flags, for chain coordinates.
Reversing an auxiliary edge direction does not reverse a vertex cycle.
A loop-direction reversal must be a swap of its two flags.

<a id="thm-main"></a>
<a id="thm:main"></a>

**Theorem 1.5 (Two-color four-loop vanishing; `thm:main`).**
For every $p,q\geq0$ with $p+q$ odd,

$$
\mathcal{P}_{4,(p,q)}=0.
$$

Consequently $\mathcal{P}_{4,(1,\ell-1)}=0$ for every odd $\ell\geq1$.

**Definition 1.6 (Stable auxiliary domain).** The auxiliary presentation below uses the domain

<a id="eq-stable"></a>
<a id="eq:stable"></a>

**Equation 1.3 (`eq:stable`).**

$$
g\geq1\quad\hbox{or}\quad |A|\geq2.
$$

**Proposition 1.7 (The one-anchor unstable boundary).** For $g=0$, one anchor and one ordinary leg form a nonzero
strut. The one-anchor Y with two differently colored ordinary legs is also nonzero.

**Proof.** The strut has no trivalent vertex and admits none of the three relators. For the Y, the graph
has one trivalent vertex, no possible IHX central edge, and no possible
two-attachment CL. Its three distinct leaf types forbid an AS-negative
automorphism. Its AS quotient is one-dimensional. Pruning these graphs
gives an isolated anchor and zero relative $H^1$, so neither graph can
be covered by the unrestricted wording of [Kuperberg, Lemma `l:sympow`](../../../Library/Topology/kuperberg2026oddvas.md).
These are actual counterexamples to that extended wording, not to
[Theorem 1.5](#thm-main). Our target, all its positive-genus cut factors,
and the auxiliary two- and three-anchor local stars satisfy
[(1.3)](#eq-stable). $\square$

**Proof of Theorem 1.5.** The argument occupies Sections 2–8. The original quotient, coefficient viewpoint, and marked question are due to [Kuperberg](../../../Library/Topology/kuperberg2026oddvas.md), §§2–3 and §7. His Theorem 1.1 proves the one-color four-loop statement. The proof below keeps the two ordinary colors throughout.

## 2. Pruning, cherries, and a precise local normal form

**Definition 2.1 (Pruned hull and skeleton).** For a stable connected graph $D$, delete non-anchor leaves and their
edges repeatedly. Equivalently take the maximal subgraph $K(D)$ in
which every non-anchor vertex has degree at least two and every anchor
is retained. The terminal result is independent of deletion order:
any subgraph with these properties survives every deletion, and the
terminal result has the properties. It is connected. Deleting a leaf
does not alter genus or separate remaining vertices. If $g\geq1$, a
cycle survives; if $g=0$ and $|A|\geq2$, the paths between anchors
survive. Thus the result is not an isolated point. The surviving
non-anchor vertices have degree two or three. Suppress degree-two
vertices to obtain a cubic skeleton with its anchors, denoted $G(D)$.
If everything is bivalent it is the circle. An anchor-to-anchor path
may instead give the two-anchor strut. Suppression preserves the two
distinct ends of a returning path and the IDs of parallel paths.

**Proposition 2.2 (Ordinary trees and the insertion normal form).** Every deleted component is a tree attached once to $K(D)$.

**Proof.** Two attachment
points would give a surviving path; a cycle would survive. Viewed from
the attachment it is a rooted binary tree with only ordinary leaves.

On a path directed from $A$ to $B$, a positive insertion has cycle

<a id="eq-positive"></a>
<a id="eq:positive"></a>

**Equation 2.1 (`eq:positive`).**

$$
(\text{leg flag},\text{toward }A,\text{toward }B).
$$

Let $D_{xy}$ insert $x$ before $y$, and let $Y_{xy}$ be the rooted
cherry specified by the $X$ cycles in the following table. Substituting
$(h_1,h_2,h_3,h_4)=(x,A,B,y)$ into [(1.1)](#eq-ihx) gives

<a id="eq-cherry"></a>
<a id="eq:cherry"></a>

**Equation 2.2 (`eq:cherry`).**

$$
\begin{array}{c|cc|c}
I&(k^+,x,A)&(k^-,B,y)&D_{xy}\\
H&(k^+,x,B)&(k^-,A,y)&D_{yx}\\
X&(k^+,x,y)&(k^-,A,B)&Y_{xy}
\end{array}
\qquad Y_{xy}=D_{yx}-D_{xy}=0.
$$

The interpretation of the $H$ term has sign $+1$: reading along $A$ to
$B$ reverses each of its two insertion cycles, giving two AS signs.
The last equality is precisely CL. Every attached ordinary tree with
at least two leaves has a terminal cherry. The stem of that cherry
ends at another trivalent vertex, except in the entire unstable
one-anchor Y already excluded. Hence [(2.2)](#eq-cherry) applies inside
the full graph and kills it. No induction on a degree bound is involved.
We have proved that every nonzero stable diagram is represented by
single ordinary legs inserted on skeleton edges. $\square$

**Definition 2.3 (The local quotient and its coefficient algebra).** Fix the underlying flag skeleton $G$, its selected cycles, and auxiliary
edge directions. A local diagram includes an identification of its
pruned suppressed underlying skeleton with $G$. This identification
retains every flag of a loop and distinguishes parallel edges. It need
not preserve the chosen cycles: their discrepancies contribute to
[(1.2)](#eq-chi). For a circle fix an orientation; a temporary cut records
the insertion list, and forgetting that cut is a cyclic permutation
already allowed by CL.

We now define the local relations without a circular “isomorphic
skeleton” criterion. For any actual IHX central edge, first contract
that edge, then prune the common contracted graph. If its contracted
vertex survives, let $r$ be its degree in that pruned graph. The local
cases are $r=2,3$, and the case where that vertex disappears. The case
$r=4$ is always global. Local identifications are those induced by
common contraction and suppression away from its degree-four case.
AS, with its scalar, and ordinary CL are local as well. This defines
$\mathcal L_{\boldsymbol\ell}(G)$. A global skeleton IHX that happens
to return to a graph isomorphic to $G$ is therefore not placed in this
local space's defining ideal.

Write $s(e),t(e)$ for the oriented edge endpoints and put

<a id="eq-poly"></a>
<a id="eq:poly"></a>

**Equation 2.3 (`eq:poly`).**

$$
b_{ve}={\bf1}_{t(e)=v}-{\bf1}_{s(e)=v},\qquad
 r_{v,c}=\sum_e b_{ve}X_{e,c},\qquad
 \mathscr A_G=\mathbb{Q}[X_{e,c}\mid e,c]/(r_{v,c}\mid v\notin A,c).
$$

The multigrading counts ordinary colors; no anchor relation is imposed.
On a circle the cellular model has one auxiliary vertex and one loop,
so its vertex relation is zero.

<a id="prop-local"></a>
<a id="prop:local"></a>

**Proposition 2.4 (Actual local presentation; `prop:local`).**
In the stable domain there are inverse maps

$$
N_G:\mathscr A_{G,\boldsymbol\ell}\longrightarrow
       \mathcal L_{\boldsymbol\ell}(G),\qquad
 \Lambda_G:\mathcal L_{\boldsymbol\ell}(G)\longrightarrow
       \mathscr A_{G,\boldsymbol\ell}.
$$

They identify the latter space with
$\bigotimes_c\operatorname{Sym}^{\ell_c}H^1(G,A;\mathbb{Q})$.

**Proof.**
The coefficient correspondence is [Kuperberg, Lemma `l:sympow`](../../../Library/Topology/kuperberg2026oddvas.md), §3.1. We construct it in the stable domain with explicit inverse maps. Here are actual finite constructions. For an oriented edge with flags
$h_t,h_h$, insert an ordered list of $m$ legs by replacing its pairing
with

$$
h_t\leftrightarrow b_1,\quad
 f_j\leftrightarrow b_{j+1}\ (j<m),\quad
 f_m\leftrightarrow h_h,\quad
 \lambda_j\leftrightarrow l_j.
$$

The new trivalent fibers have cycles $(\lambda_j,b_j,f_j)$ and $l_j$
is an ordinary leaf with its prescribed color. For $m=0$ keep the original
pairing. This works unchanged for a loop because $h_t\ne h_h$. Define
$N_G$ on monomials by these insertions, using any fixed order of colors
on each edge. CL makes the order choice irrelevant.

To see the vertex relations in actual diagrams, give a core vertex cycle
$(a,b,c)$ and temporarily direct its three branches outward. The following
one-leg instances of [(1.1)](#eq-ihx) are exact:

<a id="eq-move"></a>
<a id="eq:move"></a>

**Equation 2.4 (`eq:move`).**

$$
\begin{array}{c|cc|c}
I&(k^+,b,c)&(k^-,a,\lambda)&L_a\\
H&(k^+,b,a)&(k^-,c,\lambda)&-L_c\\
X&(k^+,b,\lambda)&(k^-,c,a)&L_b
\end{array}
\qquad L_a+L_b+L_c=0.
$$

In the middle row the retained vertex has reversed cycle; the insertion
vertex does not. For arbitrary auxiliary edge directions, the outward
branch is positive at a tail flag and negative at a head flag. Thus
[(2.4)](#eq-move) is $-r_{v,c}=0$. When two flags form a loop they contribute
with opposite signs, rather than one of them being discarded. Other
legs can be sorted and placed outside the little central neighborhood.
This realizes every monomial multiple of every $r_{v,c}$ as actual
local IHX; consequently $N_G$ descends through [(2.3)](#eq-poly).

Define $\Lambda_G$ on an actual diagram to be zero if it has a branching
ordinary tree. Otherwise associate every ordinary leg with its suppressed
edge and output

<a id="eq-lambda"></a>
<a id="eq:lambda"></a>

**Equation 2.5 (`eq:lambda`).**

$$
\Lambda_G(D)=\epsilon(D)\prod_j X_{e(j),c(j)}.
$$

The sign compares each insertion cycle with [(2.1)](#eq-positive) and each
retained trivalent cycle, via the rigidification, with $G$'s chosen cycle.
These comparisons are literal three-cycle comparisons.

We check *all* its local relations. AS is built into $\epsilon$.
For CL on retained paths the two monomials and their signs agree. For CL
in deleted trees the two sides still have a branching ordinary tree and
both images are zero. For IHX, contraction and pruning supply an exhaustive
classification, as follows.

The contracted vertex has degree four before pruning, is not an anchor,
and therefore, if retained, has degree $2,3$, or $4$. Every flag removed
there leads into a tree containing no anchor and meeting the retained
part only at that vertex. No such branch can return via another flag:
that return would be a surviving cycle or path. Inserting the two-vertex
resolution commutes with pruning away from this little tree. In
particular this classification is invariant across the three resolutions,
and is not inferred from the original resolution alone.

If the contracted vertex disappears, the neighborhood is itself in a
deleted rooted tree. Of its four exits at most one leads toward the
surviving hull. At least three exits thus lead to ordinary leaves, through
possibly larger rooted trees. Every resolution still contains branching
ordinary leaves. Its three images are zero. This also covers a central
edge wholly inside an already discarded tree.

If $r=2$, there are two retained path directions and two deleted rooted
branches. If either deleted branch has more than one ordinary leaf, it
remains a branching attached tree in every resolution, so all images
vanish. Otherwise the two branches are single ordinary legs. Two
resolutions are the two successive insertions along that same retained
path and the third is a cherry. Equation [(2.2)](#eq-cherry) shows that
their images cancel. The retained directions can be paired to each
other outside the neighborhood; this is the circle case and the same
cycle comparison applies.

If $r=3$, there is one discarded rooted branch. Again a branch with
several leaves makes all three terms zero. A single leaf instead gives
the three ways to move it past a retained core vertex. The cycles and
signs are exactly [(2.4)](#eq-move); the image is a monomial multiple of
$r_{v,c}$, with an immaterial overall sign.

If $r=4$, all four directions survive. Both central endpoints in each
resolution are retained trivalent vertices. This is a global skeleton
IHX and no claim is made that its image belongs to the local ideal.
These four cases exhaust the possibilities; arbitrary permutations of
the port names preserve the calculation by the alternating-relator
check following [(1.1)](#eq-ihx). Remote branches and insertions are common
to the three terms and multiply their images by a common signed
monomial, or make all three zero. This proves that $\Lambda_G$ is
well-defined on the actual local quotient, without inventing relations.

The composite $\Lambda_GN_G$ fixes every monomial class. Conversely a
nonbranching diagram equals its normalized insertion graph by AS and CL,
so $N_G\Lambda_G$ is the identity on it. On a branching diagram it is
also the identity, since [(2.2)](#eq-cherry) has already made that diagram
zero. These are the two inverse equations.

For completeness the last algebra identification has an explicit
description, rather than an extra graph assumption. Put

$$
H^1(G,A)=\mathbb{Q}^E/\delta\{f\in\mathbb{Q}^V:f|_A=0\},\qquad
 (\delta f)_e=f(t(e))-f(s(e)).
$$

The quotient-polynomial map sends $X_{e,c}$ to the degree-one class of
the edge cochain in the $c$th symmetric algebra. Its inverse sends a
cochain class $[a]$ to $[\sum_e a_eX_{e,c}]$. Restricted coboundaries
map to the specified vertex relations, so both maps are well-defined
and their composites fix the generators. This proves the algebra
identification in every multidegree, including zero degrees.
$\square$

## 3. Global presentation, contraction, and occupied central edges

**Definition 3.1 (Relative cycle coordinates).** We give the direction of every coefficient map explicitly. Chains have
boundary $\partial e=t(e)-s(e)$. Relative cycles are

$$
Z_{G,A}=\{z\in\mathbb{Q}^E:(\partial z)_v=0\ (v\notin A)\}.
$$

The coordinate pairing gives a perfect pairing between $H^1(G,A)$ and
$Z_{G,A}$. Indeed the annihilator of the kernel of a finite matrix is
the image of its transpose: a functional killing the kernel factors
through the image, extends linearly to the target, and is then a row
functional of that matrix. This also proves surjectivity onto the kernel's
dual by extension. These are generic finite-dimensional algebra facts,
not additional Jacobi relations.

**Proposition 3.2 (Nonloop contraction and its inverse).** Let $e:u\longrightarrow v$ be a nonloop central edge between non-anchor
trivalent vertices. Contract it to form $C$ and let $D$ delete its chain
coordinate. Then

$$
\partial_C D=\pi_\#\partial_G,
 \qquad T_G:Z_{G,A}\xrightarrow{\sim}Z_{C,A},\quad z\longmapsto Dz.
$$

**Proof.** The inverse on surviving coordinates $y$ is

<a id="eq-cycleinverse"></a>
<a id="eq:cycleinverse"></a>

**Equation 3.1 (`eq:cycleinverse`).**

$$
(T_G^{-1}y)_h=y_h\ (h\ne e),\qquad
 (T_G^{-1}y)_e=\sum_{h\ne e}b_{uh}y_h.
$$

At $u$ the boundary is zero by this formula; at $v$ it is zero by the
merged-vertex equation, and elsewhere it is unchanged. This proves both
inverse equations, including bridges, loops among the surviving edges,
and parallel edges. Nonloopness is essential.

The cohomology pullback $`\kappa_G=T_G^*`$ extends a surviving cochain by
zero. Its inverse $\theta_G$ has the explicit computation rule

<a id="eq-evacuate"></a>
<a id="eq:evacuate"></a>

**Equation 3.2 (`eq:evacuate`).**

$$
[X_{e,c}]\longmapsto\sum_{h\ne e}b_{uh}[X_{h,c}],\qquad
 [X_{h,c}]\longmapsto[X_{h,c}]\quad(h\ne e).
$$

For a cochain $a$, extending its image back by zero gives
$a+a_e\delta\mathbf1_u$, hence the same class. This proves both
inverse equations directly. Using the head instead gives
$-\sum_{h\ne e}b_{vh}X_{h,c}$; the difference is the vertex relation
at the merged vertex. Equivalently $r_u$ maps to zero, $r_v$ maps to
the merged-vertex relation, and every other relation maps to its
corresponding relation. $\square$

**Proposition 3.3 (Evacuating an occupied central edge).** Equation [(3.2)](#eq-evacuate) is realized in actual graphs, not just in
an abstract ring.

**Proof.** Choose the leg on $e$ nearest $u$ and apply
[(2.4)](#eq-move). In each resulting summand that leg is on a different
branch and the number of legs on $e$ drops by one. Repeat finitely many
times, for every color. This is precisely substitution
[(3.2)](#eq-evacuate); coincident monomials are combined by CL, with the
usual binomial and multinomial coefficients. Choices of leg order and
endpoint yield the same algebra class, and [Proposition 2.4](#prop-local)
therefore proves their equality in the actual local graph quotient.
The process never moves through an anchor. $\square$

**Proposition 3.4 (The full coefficient presentation).** The original stable quotient is the direct sum of its local coefficient algebras modulo signed flag isomorphisms and common-contraction IHX.

**Proof.** For the three skeleton resolutions $G_i$ of [(1.1)](#eq-ihx), all central
contractions have the same surviving flags and the same contracted graph
$C$. Consequently every common coefficient $\alpha$ gives the genuine
graph relation

<a id="eq-global"></a>
<a id="eq:global"></a>

**Equation 3.3 (`eq:global`).**

$$
[G_I,\operatorname{Sym}^{\boldsymbol\ell}(\kappa_I)\alpha]
 -[G_H,\operatorname{Sym}^{\boldsymbol\ell}(\kappa_H)\alpha]
 +[G_X,\operatorname{Sym}^{\boldsymbol\ell}(\kappa_X)\alpha]=0.
$$

To realize it, use a representative involving surviving edge variables
only and apply the empty-central-edge IHX. Arbitrary original
coefficients first evacuate as just proved. Thus occupied central edges
cause no extra assumption.

An actual flag isomorphism $\phi:G\to T$ has signed chain map $U_\phi$,
including its loop-flag swaps, and gives the relation

<a id="eq-iso"></a>
<a id="eq:iso"></a>

**Equation 3.4 (`eq:iso`).**

$$
[G,a]=\chi(\phi)[T,\phi_\#a],\qquad
                 \phi_\#=(\phi^{-1})^*.
$$

This separates edge-direction signs from vertex AS signs. Contraction
commutes with these signed chain maps by restriction to surviving edge
IDs. Any sequence of nonloop contractions likewise restricts to the
final edge set, so the coefficient maps are independent of contraction
order when the surviving flag identifications agree.

Here is a proof that these constructions identify the *entire*
original quotient. Take the direct sum of the local algebras for all
stable underlying skeletons, and quotient by [(3.4)](#eq-iso) and
[(3.3)](#eq-global). Insertion gives a map from this presentation to the
original quotient. It is surjective by pruning and cherry vanishing.
In the other direction send each original diagram to the signed
monomial [(2.5)](#eq-lambda) on its skeleton, or zero for branching trees.
AS and CL are respected. Every IHX has precisely the common-pruning
classification proved above: the first three cases are local and the
degree-four case is exactly [(3.3)](#eq-global). The map therefore
descends. The two composites are the identity by the same insertion
normalization, proving the identification. In particular we have proved
the needed source-presentation theorem, rather than citing the
overbroad version at the unstable boundary.

This also identifies the source's framed description. Given a framing
$f:G\simeq\Phi$ (relative to $A$ when present), use $`f^*`$ to send model
cohomology to actual cohomology. Altering $f$ and the model coefficient
together by the corresponding homotopy automorphism has the same image.
Conversely choose any framing to represent an actual coefficient;
different choices are precisely these coinvariant identifications.
The construction respects common contractions, AS, and actual graph
isomorphisms. No extra determinant twist is introduced by the leg map.

An important consequence is valid specifically for *absolute*
cohomology. If $e$ is a bridge of an unanchored skeleton, the characteristic
function of the component on its head side has coboundary $\mathbf e_e$.
Thus a leg inserted on a skeleton bridge is zero in the actual quotient.
This does not say every diagram with a bridge is zero. For relative
cohomology, a bridge between two anchor-containing sides can survive:
the two-anchor strut has one relative cochain coordinate and no vertex
relations. None of the following bridge arguments use that false
relative extrapolation. $\square$

## 4. Ordinary sockets and bridge reduction

<a id="lem-glue"></a>
<a id="lem:glue"></a>

**Lemma 4.1 (Actual socket descent; `lem:glue`).**
For $g,h\geq1$, gluing a singleton ordinary socket color on each
factor defines a bilinear map

$$
\#:\mathcal{P}_{g,(1,\boldsymbol v)}\times\mathcal{P}_{h,(1,\boldsymbol k)}
       \longrightarrow\mathcal{P}_{g+h,\boldsymbol v+\boldsymbol k}.
$$

The sockets remain commuting ordinary legs throughout the construction.

**Proof.**
This is [Kuperberg, Lemma `l:consum`](../../../Library/Topology/kuperberg2026oddvas.md), §3.2, in the positive-genus setting. The socket CL calculation is included in full. On disjoint flag sets let the socket leaf flags be $l_1,l_2$ and their
paired flags $h_1,h_2$. Delete $l_1,l_2$ and their leaf vertices and
replace the pairings by $h_1\leftrightarrow h_2$. All vertex three-cycles
are retained. This is a connected genus-$g+h$ graph. AS and IHX commute
with this raw operation, even when the socket is an external flag of
the IHX neighborhood. CL not involving the socket also commutes with it.

For socket CL, in [(2.2)](#eq-cherry) replace $x$ by the socket $s$ and
glue the other factor $E$ there. Before taking quotients, the actual
IHX gives

$$
D_{s,c}\#E-D_{c,s}\#E=-Y_{s,c}\#E.
$$

On the right, the two formerly cherry leaves become respectively the
entire second factor and the ordinary leg $c$. The cherry stem leads
to the rest of the first factor. These two sides both still have positive
genus. Their unique connecting path is therefore retained by pruning,
and the $c$ attachment lies on that path, which consists of absolute
bridges. If a further branching ordinary tree is present, the graph is
already zero; otherwise the $c$ insertion represents the cochain of
this absolute skeleton bridge and is zero by Proposition
[2.4](#prop-local). Thus the displayed defect is zero. This proves
socket CL, including raw factors with socket-containing trees, since
the two positive-genus sides still survive in that case. There are no
anchors in the defect graph. This proves descent in each argument and
bilinearity. No injectivity or extension of functionals is asserted.

For an explicit flag instance, take the first factor with cycles
$(1,2,3)$ and $(-1,-3,4)$, socket leaf $-2$, and ordinary leaf $-4$.
Take the second factor with cycle $(5,6,-6)$ and socket leaf $-5$.
Here signed integers denote literal flags and the edge involution is
$j\leftrightarrow -j$. Gluing replaces flag $5$ by $-2$.
The $X$ defect has cycles $(1,2,4)$, $(-1,3,-3)$,
$(-2,6,-6)$ and ordinary leaf $-4$.
Pruning retains edges $1,2,3,6$; the ordinary leg is at the bivalent
point of the path made from bridges $1$ and $2$, each separating two
genus-one parts. There are no anchors. This is the defect geometry
in the preceding argument.

$\square$

<a id="lem-small"></a>
<a id="lem:small"></a>

**Lemma 4.2 (Low-genus vanishing and tetrahedron support; `lem:small`).**
For any finite set of ordinary colors and odd total population, the
one- and two-loop spaces vanish. The odd three-loop space is generated
by diagrams whose skeleton is the tetrahedron.

**Proof.**
The one- and two-loop vanishing statements are [Kuperberg, Corollary `c:odd12`](../../../Library/Topology/kuperberg2026oddvas.md), §4. The skeleton reductions used here retain only the tetrahedron-support conclusion at three loops. The local normal form applies since all these genera are positive.
The one-loop skeleton is the circle, whose reflection negates its
one-dimensional homology and has no retained-vertex AS sign. Each
insertion acquires the sign of its reversed path. Thus every color
population of odd total size is negated. The two-loop unanchored
cubic skeletons have two vertices and are the theta or the dumbbell.
For theta, exchange the two vertices and reverse all three edge flags:
the product of the two cycle signs is $+1$ and the homology action is
$-I$. For dumbbell, reverse the two loops; the two vertex AS signs
multiply to $+1$, the bridge coordinate is zero, and homology is again
negated. These prove one- and two-loop odd vanishing with arbitrarily
many commuting colors, without any three-color invariant assertion.

For a bridge of a cubic unanchored skeleton each side has positive
genus. Indeed after cutting it and adding one socket leaf to each side,
a genus-zero side would be a tree with exactly one leaf and all other
vertices trivalent. For a tree, the degree identity gives
$n_1=n_3+2$, contradicting $n_1=1$. A bridge with inserted ordinary
legs is already zero; otherwise make this cut as an actual graph
operation. In genus three it splits the genera as $1+2$. The two
socket-bearing factors have total leg counts whose sum is the original
odd count plus two, still odd. Exactly one factor is odd, and its genus
is one or two, so it is zero by the preceding paragraph. Lemma
[4.1](#lem-glue) kills its gluing.

The bridgeless cubic three-loop skeleton has four vertices. A loop
would force a bridge. If a double-edge pair is present, its two other
branches must meet the other two vertices separately (otherwise there
is a bridge), and those other two vertices must also form a double-edge
pair. Otherwise the simple graph is $K_4$. On the double-digon graph
with ordered edges

$$
01,01,23,23,02,13,
$$

the signed edge map $(-1,-2,-3,-4,6,5)$ sends vertices by
$(1,0,3,2)$, preserves all four selected cycles, and acts as $-I$ on
the cycles with chord coefficients $2,4,6$. Thus its odd part is zero.
Only tetrahedron-supported diagrams remain. This is a generation
statement; it does not say the entire arbitrary-color three-loop space
vanishes, classify determinant classes, or extend a tetrahedral
functional to a global one.
$\square$

<a id="lem-bridgeB"></a>
<a id="lem:bridgeB"></a>

**Lemma 4.3 (Reduction to bridgeless cores and the core B; `lem:bridgeB`).**
For an odd two-color population at four loops, every diagram is a sum
of diagrams with a bridgeless skeleton or with skeleton $B$, a
tetrahedron joined by a bridge to a loop.

**Proof.**
Apply the local normal form and discard legs on skeleton bridges. For
a remaining bridge, cut and attach a fresh ordinary socket color on
each component. Both genera are positive by the degree argument above,
and sum to four. The sum of the two factors' leg counts is $p+q+2$,
so one factor is odd. If its genus is one or two, it is zero by Lemma
[4.2](#lem-small). If its genus is three, the other factor has genus one.
The odd factor is a linear combination of tetrahedron-supported
diagrams by that lemma, and the one-loop factor is represented on a
circle. These equalities may be glued by [Lemma 4.1](#lem-glue). Normal
insertion representatives have sockets on their respective core edges;
gluing the socket of the tetrahedron to that of the circle has skeleton
$B$. All other ordinary colors and populations are retained. This proves
the claim without any $\mathrm{SL}_3$ classification, without a nonzero
gluing premise, and also when the original graph had repeated bridges
or a Y-shaped bridge configuration.
$\square$

## 5. Dual polynomials and the exact finite core relations

**Definition 5.1 (Global weight polynomials in a fixed population).** Fix $p,q$ and $N=p+q$ odd. A four-loop graph with $N$ ordinary leaves has
$N+6$ trivalent vertices, $2N+6$ vertices in all, and $2N+9$ edges. For
this fixed size there are finitely many flag pairings, partitions,
three-cycles, and colorings. Its rational quotient is finite-dimensional.
It therefore suffices to annihilate every *global* weight functional
$w$ on the original quotient.

The perfect cohomology-cycle pairing induces a perfect symmetric-power
pairing, with normalization

$$
\langle h_1\cdots h_n,z_1\cdots z_n\rangle
 =\frac1{n!}\sum_{\sigma\in S_n}\prod_i\langle h_i,z_{\sigma(i)}\rangle.
$$

For dual bases, equal monomials with exponent vector $\alpha$ pair to
$\alpha!/n!$, all unequal ones to zero. These factors are nonzero;
for $n=0$ use multiplication in $\mathbb{Q}$. On a core with a four-cycle basis,
the pullback of $w$ along insertion is thus a polynomial

$$
F_G(a,b,c,d;r,s,t,u)\in\mathbb{Q}[a,b,c,d,r,s,t,u],
$$

of degree $p$ in the first tuple and $q$ in the second. Each core
comparison acts by the same substitution on both tuples. They remain
independent formal variables even when $p=0$ or $q=0$. Simultaneous
negation of every variable multiplies $F_G$ by $(-1)^N=-1$.
These are restrictions of a global $w$; arbitrary unrelated core
functionals are not being assumed to extend.

**Definition 5.2 (Six cores and fixed cycle bases).** The six core edge lists and chords are

<a id="eq-cores"></a>
<a id="eq:cores"></a>

**Equation 5.1 (`eq:cores`).**

$$
\begin{array}{c|l|l}
G&\text{edges }e_1,\ldots,e_9&\text{chords}\\\hline
R&01,01,23,23,45,45,12,34,50&2,4,6,9\\
S&01,01,45,45,23,02,13,24,35&2,4,7,9\\
C&02,03,12,13,23,04,45,45,51&4,5,8,9\\
P&01,12,20,34,45,53,03,14,25&3,6,8,9\\
K&03,04,05,13,14,15,23,24,25&5,6,8,9\\
B&02,03,12,13,23,04,41,45,55&4,5,7,9
\end{array}
$$

An edge $ij$ is directed $i\to j$; $55$ has two distinct flags. The
cycle at a vertex lists its incident edge indices increasingly, and
the positive flag of a loop precedes its negative flag. Chords have
fundamental-cycle coefficient $+1$, defining the basis $(a,b,c,d)$.
The ordered cycle columns are explicitly

<a id="eq-columns"></a>
<a id="eq:columns"></a>

**Equation 5.2 (`eq:columns`).**

$$
\begin{array}{c|llll}
R&-e_1+e_2&-e_3+e_4&-e_5+e_6&e_1+e_3+e_5+e_7+e_8+e_9\\
S&-e_1+e_2&-e_3+e_4&e_1-e_5-e_6+e_7&-e_3+e_5-e_8+e_9\\
C&e_1-e_2-e_3+e_4&e_1-e_2+e_5&-e_7+e_8&-e_1+e_3+e_6+e_7+e_9\\
P&e_1+e_2+e_3&e_4+e_5+e_6&e_1-e_4-e_7+e_8&e_1+e_2-e_4-e_5-e_7+e_9\\
K&e_1-e_2-e_4+e_5&e_1-e_3-e_4+e_6&e_1-e_2-e_7+e_8&e_1-e_3-e_7+e_9\\
B&e_1-e_2-e_3+e_4&e_1-e_2+e_5&-e_1+e_3+e_6+e_7&e_9
\end{array}
$$

Here $P$ is the triangular prism, $K=K_{3,3}$, and $B$ is the
tetrahedron-with-loop core of [Lemma 4.3](#lem-bridgeB).

**Definition 5.3 (Inverse transport of coefficients).** For completeness we specify the calculation that turns a signed flag
map into a polynomial substitution. Let $R$ be a resolution of original
$G$, let $\phi:R\to T$ be a signed edge isomorphism, and let the
contractions be $T_G,T_R$. Then the map on target cycles back to the
original cycles is

<a id="eq-L"></a>
<a id="eq:L"></a>

**Equation 5.3 (`eq:L`).**

$$
L=T_G^{-1}T_RU_\phi^{-1}:H_1(T)\longrightarrow H_1(G),
 \qquad L^*=\phi_\#\kappa_R\kappa_G^{-1}.
$$

It satisfies $`\langle L^*a,z\rangle_T=\langle a,Lz\rangle_G`$.
If $Q_G,Q_T$ are the column matrices in [(5.2)](#eq-columns), and $D_e$
deletes the central coordinate, the unique matrix $M$ is determined by

<a id="eq-solve"></a>
<a id="eq:solve"></a>

**Equation 5.4 (`eq:solve`).**

$$
D_eQ_GM=D_eU_\phi^{-1}Q_T.
$$

The substitution is $F_T(M^{\mathsf T}\mathbf x,M^{\mathsf T}\mathbf y)$.
The columns of $M$ are the transported target generators, which explains
the transpose when their images are listed as substitution rows. The
same rule without $D_e$ handles an automorphism. Equation
[(3.1)](#eq-cycleinverse) proves existence, uniqueness and integral
invertibility; no spanning tree is assigned to the resolution. The AS
scalar in [(1.2)](#eq-chi) stays outside this substitution.

In a signed edge tuple the $j$th entry $m$ maps $e_j^+$ to $e_{|m|}^+$
if $m>0$ and to $e_{|m|}^-$ if $m<0$, and maps its opposite flag to
the opposite target flag. The tables in Section 8 give all 23 maps,
their reversed *source* vertex sets, and their substitutions.
Thus every datum can be verified by fiber membership, three-cycle
comparison, and [(5.4)](#eq-solve); the table does not merely classify
unoriented pairings.

**Proposition 5.4 (Exact signed core relations).** The finite flag data of Section 8 give the following relations for restrictions of every global weight functional.

**Proof.** Here are the relations from those data in the form needed below. The
three automorphisms have AS sign $+1$ and substitutions

<a id="eq-autos"></a>
<a id="eq:autos"></a>

**Equation 5.5 (`eq:autos`).**

$$
\begin{array}{c|l}
 S&(-a,-b,-c,-d)\\
 C&(-a,-b,-c,d+a+c)\\
 P&(a,b,a-b-d,a-b+c-d).
 \end{array}
$$

In particular the prism's stated signed edge map has *forward*
cycle action $(a,b,d-c,a-b-c)$, whose inverse is the last row. Using
the forward action for the inverse transport [(5.3)](#eq-L) would be a
concrete error. The inverse row is used here.

The seven self-returning resolution substitutions are

<a id="eq-seven"></a>
<a id="eq:seven"></a>

**Equation 5.6 (`eq:seven`).**

$$
\begin{array}{c|l|c}
\text{resolution}&T&\text{other core}\\\hline
C1:H&(-a+b,-a,-c,-d)&S\\
C3:X&(b,a,c,d)&S\\
C4:H&(b,a,c,d+a-b)&S\\
P2:H&(-a,b,c-a,d-a)&C\\
P3:X&(-a,b,c-a,d-2a)&C\\
P5:H&(a,-b,c+b,d+b)&C\\
P6:X&(a,-b,c+b,d+2b)&C
\end{array}
$$

The H rows have AS sign $-1$ and IHX coefficient $-1$; the X rows
have both signs $+1$. Thus if the other core's weight polynomial is
zero, each row is the actual relation

<a id="eq-anti"></a>
<a id="eq:anti"></a>

**Equation 5.7 (`eq:anti`).**

$$
F_G+F_G\circ T=0.
$$

All these are global degree-four central-neighborhood relations. None
has been smuggled into the local vertex ideal.

The remaining three IHX triples are

<a id="eq-linkR"></a>
<a id="eq:linkR"></a>

**Equation 5.8 (`eq:linkR`).**

$$
F_C(a,b,c,d)-F_R(-b,-a+b,-c,-d)
                  +F_C(-a+2b,b,c,d+a-b)=0,
$$

<a id="eq-linkB"></a>
<a id="eq:linkB"></a>

**Equation 5.9 (`eq:linkB`).**

$$
F_C(a,b,c,d)-F_B(a,b,d,c)-F_C(a,b,-c,d)=0,
$$

<a id="eq-linkK"></a>
<a id="eq:linkK"></a>

**Equation 5.10 (`eq:linkK`).**

$$
F_K(a,b,c,d)+F_P(a,-d,b,a-c+d)
                  -F_P(-c,b,-a,-b-c+d)=0.
$$

In every abbreviated formula the identical substitution acts on
$(r,s,t,u)$. All the maps in these triples are invertible. The actual
occupied-edge evacuation above is what makes them valid for arbitrary
leg populations on the central skeleton edge.

For one illustrative flag check, in $C1:H$ the changed cycles are
$(1^+,2^+,3^-)$ and $(1^-,6^+,5^+)$. The map in Section 8 sends
them to $(3^-,5^+,1^-)$ and $(3^+,9^-,4^+)$. The first is positive
at target vertex 2 and the second negative at target vertex 1. Taking
all six source vertices gives the reversed-source set $\{2\}$.
For $C7:H$ the cycle $(7^+,8^+,8^-)$ maps to
$(8^-,9^+,9^-)$ at $B$'s loop vertex. Both loop flags are essential.
As a cycle calculation,

$$
Q_C(a,b,c,d)=(a+b-d,-a-b,-a+d,a,b,d,-c+d,c,d).
$$

After deleting coordinate 1, the original chord coordinates of a
pulled target cycle in $C1:H$ are $(z_2,z_4,-z_8,-z_6)$. Inserting the
four target cycle columns yields $(-a+b,-a,-c,-d)$ as claimed. These
examples exhibit separately the AS comparison and the cycle transport. $\square$

## 6. All-degree elimination

<a id="lem-shears"></a>
<a id="lem:shears"></a>

**Lemma 6.1 (Two simultaneous shears; `lem:shears`).**
If a polynomial $F\in\mathbb{Q}[a,b,c,d,r,s,t,u]$ is fixed by both

$$
(d,u)\mapsto(d+a,u+r),\qquad (d,u)\mapsto(d+b,u+s),
$$

with the other six variables fixed, it is independent of $d,u$.

**Proof.**
Iteration gives the same identities with each nonnegative integer
multiple of the direction. Regarding the multiple as a new variable,
the resulting polynomial identity holds identically: pass to the
fraction field of the coefficient polynomial domain and use infinitely
many distinct rational roots. Differentiation at zero gives

$$
a\partial_dF+r\partial_uF=0,\qquad
 b\partial_dF+s\partial_uF=0.
$$

Elimination yields $(as-br)\partial_dF=0$ and
$(as-br)\partial_uF=0$. The formal polynomial $as-br$ is nonzero
in an integral domain. Both derivatives vanish and characteristic zero
implies independence. This uses no nonvanishing after numerical
specialization and no lower bound on either color population.
$\square$

**Proposition 6.2 (All six core weights vanish).** Every global weight functional at an odd two-color population restricts to zero on the six core coefficient spaces.

**Proof.** Let $w$ be any global weight functional. By [(5.5)](#eq-autos) and odd
total degree, $F_S=-F_S$, so $F_S=0$.

For $C$, all three of its rows in [(5.6)](#eq-seven) now apply. The first
and odd degree give invariance under

$$
U(a,b,c,d)=(a-b,a,c,d).
$$

The next two give anti-invariance under

$$
J(a,b,c,d)=(b,a,c,d),\qquad
 V(a,b,c,d)=(b,a,c,d+a-b).
$$

Hence $F_C$ is invariant under $S_0=J\circ V$, which fixes the first
three coordinates and adds $a-b$ to $d$. It is also invariant under

$$
U^{-1}S_0U:(a,b,c,d)\mapsto(a,b,c,d-b).
$$

To check the order, $U$ first replaces $(a,b)$ by $(a-b,a)$, so the
addition is $(a-b)-a=-b$; $U^{-1}$ restores $(a,b)$. Combining this
shear's inverse with $S_0$ adds $a$ to $d$. Exactly the same operations
add $r$ or $s$ to $u$. [Lemma 6.1](#lem-shears) proves independence of
$d,u$. The $C$ automorphism in [(5.5)](#eq-autos) then simultaneously
negates all remaining variables while fixing $F_C$. Odd degree forces
$F_C=0$.

For $P$, all four rows now apply. Call their substitutions
$A_2,A_3,A_5,A_6$ in that order. Each changes the sign of $F_P$.
Their compositions are

$$
A_3A_2:(a,b,c,d)\mapsto(a,b,c,d+a),\qquad
 A_6A_5:(a,b,c,d)\mapsto(a,b,c,d-b).
$$

For example $c-a-(-a)=c$ and $d-a-2(-a)=d+a$ in the first, and
$c+b+(-b)=c$, $d+b+2(-b)=d-b$ in the second. On the second color
these add $r$ and $-s$ to $u$. [Lemma 6.1](#lem-shears) again eliminates
$d,u$. The inverse prism automorphism then reads

$$
F_P(a,b,c;r,s,t)=F_P(a,b,a-b-d;r,s,r-s-u).
$$

Set $d=a-b$ and $u=r-s$; the left side is unchanged, and the right
side has its third coordinates zero. Thus $F_P$ is also independent
of $c,t$. The $A_2$ and $A_5$ relations now change its sign under
$(a,r)\mapsto(-a,-r)$ and $(b,s)\mapsto(-b,-s)$ respectively.
Their composition fixes $F_P$ but negates every remaining variable.
Odd degree gives $F_P=0$. Finally [(5.8)](#eq-linkR)--[(5.10)](#eq-linkK)
and invertibility give $F_R=F_B=F_K=0$. $\square$

## 7. Exhaustion of the target and boundary populations

**Proposition 7.1 (Complete bridgeless list).** The bridgeless four-loop cubic skeletons are exactly $R,S,C,P,K$.

**Proof.** We justify the complete list, including multigraphs. A cubic
four-loop skeleton has six vertices and nine edges. A loop forces a
bridge on its vertex's third flag, and a triple edge would isolate a
two-vertex component. Thus a connected bridgeless six-vertex core is
loopless, with disjoint double-edge pairs. Replace a double pair by a
bivalent two-port marker and suppress it. This is only a classification
operation, not a homology-preserving contraction.

With three pairs the three markers form a connected bivalent graph on
three vertices, hence a triangle; this is $R$. With two pairs the
reduced bridgeless two-loop cubic graph is theta. The two insertions
must be on distinct theta edges, since otherwise the other two direct
edges constitute a third double pair; this is $S$. With one pair the
reduced bridgeless three-loop core is tetrahedron or the double digon
of [Lemma 4.2](#lem-small). One insertion cannot destroy both pairs of
the latter, so only the tetrahedron possibility remains, giving $C$.
With no pairs the graph is simple cubic on six vertices. Its complement
is simple bivalent, either a six-cycle or two disjoint triangles; these
give $P$ and $K$. Thus these are all five bridgeless cores. $\square$

**Conclusion of the proof of Theorem 1.5.** The preceding elimination shows that $w$ vanishes on the entire local
coefficient spaces of these five cores and of $B$. Lemma
[4.3](#lem-bridgeB) covers every remaining bridge graph. Branching
ordinary trees were already zero. Thus $w=0$ on every original
diagram. Finite-dimensional duality proves [Theorem 1.5](#thm-main).
In particular the potential nonzero three-color three-loop determinant
classes, if present, have zero image in the required circle--tetrahedron
gluing: the whole odd two-color $B$ coefficient space is annihilated.
No claim about those three-loop classes themselves was used.

For a zero population the
corresponding factor is $\operatorname{Sym}^0=\mathbb{Q}$; the formal independent coefficient
variables in [Lemma 6.1](#lem-shears) remain available. For $\ell=1$ the
marked population is $(1,0)$, directly covered by the theorem. Loops,
parallel paths, occupied central edges, and repeated bridges have not
been discarded. Relative relations occur only for true anchors; all
target diagrams and socket-cut factors are unanchored and of positive
genus. Therefore neither the unstable $g=0,a=1$ counterexamples nor an
anchored bridge has been used to force any vanishing. $\square$

## 8. Complete signed flag data

**Definition 8.1 (Literal oriented fibers).** Write $j^+$ and $j^-$ for the tail and head flags of edge $e_j$, with involution $j^+\leftrightarrow j^-$. The six selected three-cycles of each core are the following. Each entry is a three-cycle, so cyclic rotations denote the same orientation. Both flags of the loop in $B$ are retained.

| Core | Vertex 0 | Vertex 1 | Vertex 2 | Vertex 3 | Vertex 4 | Vertex 5 |
| --- | --- | --- | --- | --- | --- | --- |
| $R$ | $(1^{+},2^{+},9^{-})$ | $(1^{-},2^{-},7^{+})$ | $(3^{+},4^{+},7^{-})$ | $(3^{-},4^{-},8^{+})$ | $(5^{+},6^{+},8^{-})$ | $(5^{-},6^{-},9^{+})$ |
| $S$ | $(1^{+},2^{+},6^{+})$ | $(1^{-},2^{-},7^{+})$ | $(5^{+},6^{-},8^{+})$ | $(5^{-},7^{-},9^{+})$ | $(3^{+},4^{+},8^{-})$ | $(3^{-},4^{-},9^{-})$ |
| $C$ | $(1^{+},2^{+},6^{+})$ | $(3^{+},4^{+},9^{-})$ | $(1^{-},3^{-},5^{+})$ | $(2^{-},4^{-},5^{-})$ | $(6^{-},7^{+},8^{+})$ | $(7^{-},8^{-},9^{+})$ |
| $P$ | $(1^{+},3^{-},7^{+})$ | $(1^{-},2^{+},8^{+})$ | $(2^{-},3^{+},9^{+})$ | $(4^{+},6^{-},7^{-})$ | $(4^{-},5^{+},8^{-})$ | $(5^{-},6^{+},9^{-})$ |
| $K$ | $(1^{+},2^{+},3^{+})$ | $(4^{+},5^{+},6^{+})$ | $(7^{+},8^{+},9^{+})$ | $(1^{-},4^{-},7^{-})$ | $(2^{-},5^{-},8^{-})$ | $(3^{-},6^{-},9^{-})$ |
| $B$ | $(1^{+},2^{+},6^{+})$ | $(3^{+},4^{+},7^{-})$ | $(1^{-},3^{-},5^{+})$ | $(2^{-},4^{-},5^{-})$ | $(6^{-},7^{+},8^{+})$ | $(8^{-},9^{+},9^{-})$ |

**Definition 8.2 (The twenty common-contraction resolutions).** For a central edge $i:u\to v$, rotate the cycles at $u$ and $v$ to $(i^+,h_1,h_2)$ and $(i^-,h_3,h_4)$. The $H$ resolution has cycles $(i^+,h_1,h_3)$ and $(i^-,h_2,h_4)$; the $X$ resolution has $(i^+,h_1,h_4)$ and $(i^-,h_2,h_3)$. The first and second fibers keep source vertex names $u$ and $v$. Every other fiber and every edge pairing is unchanged. Contracting $i$ in the original, $H$, or $X$ graph gives the same four-flag fiber $\{h_1,h_2,h_3,h_4\}$, and deletes exactly chain coordinate $i$. This specifies the common contracted graph in every row, including when external flags are paired to each other.

| Resolution | First oriented fiber | Second oriented fiber | Target under the signed map |
| --- | --- | --- | --- |
| $C1:H$ | $(1^{+},2^{+},3^{-})$ | $(1^{-},6^{+},5^{+})$ | $C$ |
| $C1:X$ | $(1^{+},2^{+},5^{+})$ | $(1^{-},6^{+},3^{-})$ | $S$ |
| $C3:H$ | $(3^{+},4^{+},5^{+})$ | $(3^{-},9^{-},1^{-})$ | $S$ |
| $C3:X$ | $(3^{+},4^{+},1^{-})$ | $(3^{-},9^{-},5^{+})$ | $C$ |
| $C4:H$ | $(4^{+},9^{-},5^{-})$ | $(4^{-},3^{+},2^{-})$ | $C$ |
| $C4:X$ | $(4^{+},9^{-},2^{-})$ | $(4^{-},3^{+},5^{-})$ | $S$ |
| $P2:H$ | $(2^{+},8^{+},3^{+})$ | $(2^{-},1^{-},9^{+})$ | $P$ |
| $P2:X$ | $(2^{+},8^{+},9^{+})$ | $(2^{-},1^{-},3^{+})$ | $C$ |
| $P3:H$ | $(3^{+},9^{+},7^{+})$ | $(3^{-},2^{-},1^{+})$ | $C$ |
| $P3:X$ | $(3^{+},9^{+},1^{+})$ | $(3^{-},2^{-},7^{+})$ | $P$ |
| $P5:H$ | $(5^{+},8^{-},6^{+})$ | $(5^{-},4^{-},9^{-})$ | $P$ |
| $P5:X$ | $(5^{+},8^{-},9^{-})$ | $(5^{-},4^{-},6^{+})$ | $C$ |
| $P6:H$ | $(6^{+},9^{-},7^{-})$ | $(6^{-},5^{-},4^{+})$ | $C$ |
| $P6:X$ | $(6^{+},9^{-},4^{+})$ | $(6^{-},5^{-},7^{-})$ | $P$ |
| $C5:H$ | $(5^{+},1^{-},2^{-})$ | $(5^{-},3^{-},4^{-})$ | $R$ |
| $C5:X$ | $(5^{+},1^{-},4^{-})$ | $(5^{-},3^{-},2^{-})$ | $C$ |
| $C7:H$ | $(7^{+},8^{+},8^{-})$ | $(7^{-},6^{-},9^{+})$ | $B$ |
| $C7:X$ | $(7^{+},8^{+},9^{+})$ | $(7^{-},6^{-},8^{-})$ | $C$ |
| $K1:H$ | $(1^{+},2^{+},4^{-})$ | $(1^{-},3^{+},7^{-})$ | $P$ |
| $K1:X$ | $(1^{+},2^{+},7^{-})$ | $(1^{-},3^{+},4^{-})$ | $P$ |

**Definition 8.3 (All signed flag maps).** In the signed edge tuple, the $j$th entry $m$ maps $j^+$ to $|m|^+$ for $m>0$ and to $|m|^-$ for $m<0$; the opposite flag maps to the opposite target flag. The AS sign is independently $(-1)^{|V_-|}$. The two resolution rows at each central edge, together with the original $I$ graph, have IHX coefficients $1,-1,1$. An “auto” row is an automorphism of the indicated core.

| Row | Target | Signed edge tuple | Reversed source vertices $V_-$ |
| --- | --- | --- | --- |
| $S auto$ | $S$ | $(-1,-2,-3,-4,-5,7,6,9,8)$ | $\{\}$ |
| $C auto$ | $C$ | $(2,1,4,3,-5,6,8,7,9)$ | $\{0,1,4,5\}$ |
| $P auto$ | $P$ | $(2,3,1,5,6,4,8,9,7)$ | $\{0,2,3,5\}$ |
| $C1:H$ | $C$ | $(-3,5,1,2,4,-9,-7,-8,-6)$ | $\{2\}$ |
| $C1:X$ | $S$ | $(6,1,-5,-7,2,8,3,4,-9)$ | $\{3\}$ |
| $C3:H$ | $S$ | $(5,-6,7,-1,-2,8,3,4,-9)$ | $\{\}$ |
| $C3:X$ | $C$ | $(1,2,-3,5,4,6,7,8,9)$ | $\{2,3\}$ |
| $C4:H$ | $C$ | $(1,2,-5,4,-3,6,7,8,9)$ | $\{2\}$ |
| $C4:X$ | $S$ | $(-6,5,-1,-7,2,8,3,4,-9)$ | $\{0\}$ |
| $P2:H$ | $P$ | $(-3,2,-1,4,5,6,7,8,9)$ | $\{0\}$ |
| $P2:X$ | $C$ | $(7,-9,-8,1,5,-2,-6,3,4)$ | $\{4\}$ |
| $P3:H$ | $C$ | $(7,-8,6,-3,4,-5,1,9,2)$ | $\{0,2\}$ |
| $P3:X$ | $P$ | $(-2,-1,3,4,5,6,7,8,9)$ | $\{0,1\}$ |
| $P5:H$ | $P$ | $(1,2,3,-6,5,-4,7,8,9)$ | $\{3\}$ |
| $P5:X$ | $C$ | $(1,5,-2,7,-9,-8,6,-3,-4)$ | $\{1\}$ |
| $P6:H$ | $C$ | $(-1,2,-5,-7,8,-9,-3,6,-4)$ | $\{0,2,3,5\}$ |
| $P6:X$ | $P$ | $(1,2,3,-5,-4,6,7,8,9)$ | $\{3,4\}$ |
| $C5:H$ | $R$ | $(1,2,-3,-4,7,-9,-5,-6,-8)$ | $\{\}$ |
| $C5:X$ | $C$ | $(1,2,4,3,5,6,7,8,9)$ | $\{1,3\}$ |
| $C7:H$ | $B$ | $(1,2,3,4,5,6,-8,9,7)$ | $\{\}$ |
| $C7:X$ | $C$ | $(1,2,3,4,5,6,-7,-8,9)$ | $\{5\}$ |
| $K1:H$ | $P$ | $(7,-3,4,-1,2,8,6,-9,-5)$ | $\{0,4,5\}$ |
| $K1:X$ | $P$ | $(7,1,-6,-4,-8,5,3,-2,9)$ | $\{1,2,3,4,5\}$ |

**Definition 8.4 (All inverse-transport substitutions).** Every row below acts identically on the two color tuples. These substitutions use the inverse transport in Equation 5.3 and the cycle bases in Equation 5.2; the AS scalar stays separate. The nonzero determinants give invertibility for all twenty-three rows.

| Row | Substitution on $(a,b,c,d)$ | Determinant |
| --- | --- | --- |
| $S auto$ | $(-a,-b,-c,-d)$ | $1$ |
| $C auto$ | $(-a,-b,-c,a+c+d)$ | $-1$ |
| $P auto$ | $(a,b,a-b-d,a-b+c-d)$ | $1$ |
| $C1:H$ | $(-a+b,-a,-c,-d)$ | $1$ |
| $C1:X$ | $(b,c,-a,-d)$ | $1$ |
| $C3:H$ | $(a-b,c,-a,-d)$ | $-1$ |
| $C3:X$ | $(b,a,c,d)$ | $-1$ |
| $C4:H$ | $(b,a,c,a-b+d)$ | $-1$ |
| $C4:X$ | $(-a+b,c,a,-a-d)$ | $-1$ |
| $P2:H$ | $(-a,b,-a+c,-a+d)$ | $-1$ |
| $P2:X$ | $(b-c+d,b,-a,c)$ | $-1$ |
| $P3:H$ | $(a-d,a-b-d,-a,c)$ | $-1$ |
| $P3:X$ | $(-a,b,-a+c,-2a+d)$ | $-1$ |
| $P5:H$ | $(a,-b,b+c,b+d)$ | $-1$ |
| $P5:X$ | $(a+c-d,a,-b,-c)$ | $1$ |
| $P6:H$ | $(-b-d,-a,b,c)$ | $-1$ |
| $P6:X$ | $(a,-b,b+c,2b+d)$ | $-1$ |
| $C5:H$ | $(-b,-a+b,-c,-d)$ | $-1$ |
| $C5:X$ | $(-a+2b,b,c,a-b+d)$ | $-1$ |
| $C7:H$ | $(a,b,d,c)$ | $-1$ |
| $C7:X$ | $(a,b,-c,d)$ | $-1$ |
| $K1:H$ | $(a,-d,b,a-c+d)$ | $1$ |
| $K1:X$ | $(-c,b,-a,-b-c+d)$ | $-1$ |

## 追加锚（本行以下为增补区）
