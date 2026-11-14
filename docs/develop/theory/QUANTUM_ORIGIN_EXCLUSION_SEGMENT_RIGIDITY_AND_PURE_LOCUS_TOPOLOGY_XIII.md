# QUANTUM ORIGIN: EXCLUSION SEGMENT RIGIDITY AND PURE LOCUS TOPOLOGY XIII

## 160. Generic singleton labels, zero-kernel confirmation and the exact budget bridge

### 160.1 The unchanged original domain and the reused suppliers

**定义 160.1（Full original objects and local redundancy）。** Let $V\ne0$ be a finite-dimensional real vector space,
$C\subset V$ a closed pointed generating convex cone, and $u\in V^*$ strictly positive on $C\setminus\{0\}$.
Use the entire original state base, pure locus, effect interval and confirmation menus:

$$
\begin{gathered}
C^*=\{h\in V^*:h(c)\ge0\ (c\in C)\},\quad K=C\cap\{u=1\},\quad P=\operatorname{ext}K,\\
\mathcal E=[0,u]_{C^*},\quad F_p=\{e\in\mathcal E:e(p)=1\},\\
T_p(x)=\min_{e\in F_p}e(x)\quad(p\in P,\ x\in K),\qquad D_p=\{x\in K:T_p(x)=0\}.
\end{gathered}
\tag{XIII160.1}
$$

Assume complete EB3: every entire $D_p$ is affinely isomorphic to a nondegenerate closed three-ball.
Assume literal pure PR: $T_p(q)=T_q(p)$ for all $p,q\in P$.
The second input $x$ in (XIII160.1) still ranges over every mixed state as well as every pure state.
There is no bound on the finite ambient dimension, no global label injectivity premise, and no least-confirmer premise.
PR exchanges two pure endpoints; it does not assert commutativity of sequential measurements.

Fix auxiliary Euclidean norms on $V$ and $V^*$; all Hausdorff limits use the ambient norm on $V$,
and interiors and boundary contacts of $K$ are relative to $\operatorname{aff}K=\{u=1\}$.
These norms supply topology, not a physical inner product. Define

$$
\begin{gathered}
\mathscr B=\{D_p:p\in P\},\quad S(F)=P\cap F=\operatorname{ext}F,\quad I(F)=\{p\in P:D_p=F\},\\
P_{\rm s}=\{p\in P:I(D_p)=\{p\}\},\quad
\mathcal R=\operatorname{Cont}(p\mapsto D_p),\quad \Sigma=P\setminus\mathcal R,\\
N_p=\{h\in C^*:h(p)=0\},\quad L_p=\operatorname{span}_{\mathbb R}N_p,\quad
R_p:L_p\longrightarrow\operatorname{Aff}(D_p),\quad R_ph=h|_{D_p},\\
\mathcal A_p=\{e\in F_p:e|_{D_p}=0\},\quad N_F=\{h\in C^*:h|_F=0\},\quad
a(p)=\dim\ker R_p\quad(p\in P_{\rm s}).
\end{gathered}
\tag{XIII160.2}
$$

Here $\operatorname{Aff}(D_p)$ is the four-dimensional real space of affine functions on the whole three-ball.
A ball is called repeated when $I(F)$ has more than one point; otherwise it has a singleton label.
The integer $a(p)$ is defined only at singleton labels. It is distinct from the contrast coefficient below.

The following are existing suppliers, used with their original hypotheses, rather than new results of this chapter.
The full-face classification is [Blueprint Theorem 1.7, `exclusion_ball_faces`][Faces160], whose first two conclusions
are recalled in [IX114.2][IX160] with the older locator “1.6”. Every nonempty proper face is a pure singleton
or an actual whole ball $D_p$; these balls are exposed maximal proper faces, different balls meet at most in one pure point,
$S(F)$ is their whole relative sphere, and $F=\operatorname{conv}S(F)$.
Common exposure gives $\mathcal A_p\ne\varnothing$. It does not make $\mathcal A_p$ the whole menu $F_p$.

[IX114.3–114.4][IX160] give pure exposure PE from PR and compactness of the entire $P$.
[IX115.3–115.6][IX160] give the closed zero graph, the whole-ball limit dichotomy, and the open dense set $\mathcal R$;
thus $\Sigma$ is closed nowhere dense in $P$.
They also give lower semicontinuity of $p\mapsto\beta_{D_p}$ on all $P$.
[IX116.2][IX160] gives the exact repeated-pair alternative: a repeated ball $H$ has a unique actual partner $G$, with

$$
I(H)=S(G),\qquad I(G)=S(H),\qquad H\cap G=\varnothing.
\tag{XIII160.3}
$$

Neither ball meets a third different actual ball. [IX116.6][IX160] gives singleton balls and,
for every singleton ball $F$, $S(F)\subset P_{\rm s}$.
The dimension-free local [XII147.2][XII160], not the nine-dimensional Theorem XII147.1, gives, for $p\in P_{\rm s}$,

$$
R_p\text{ surjective},\qquad
a(p)=\dim_{\rm aff}\mathcal A_p,\qquad \dim L_p=a(p)+4,\qquad
N_{D_p}=\operatorname{cone}\mathcal A_p,\qquad
\dim\operatorname{span}N_{D_p}=a(p)+1.
\tag{XIII160.4}
$$

For an actual ball $F$, use the existing contrast and positive-extension budget:

$$
\delta(F)=\max_{r,s\in S(F)}(1-T_r(s))=2\alpha_F>0,\qquad
\beta_F=\delta(F)^{-1}\in[1,\infty).
\tag{XIII160.5}
$$

The coefficient $\alpha_F$ is the real number denoted $a_F$ in [IX114.5][IX160], not the integer $a(p)$.
In every affine ball chart $b_F$, that supplier gives
$T_{b_F(v)}(b_F(w))=1-\alpha_F+\alpha_F v\cdot w$ for $v\in S^2,w\in\overline B^3$,
including the whole mixed interior. [IX114.6][IX160] identifies $1/(2\alpha_F)$ with the attained common optimal budget
for positive extension of all affine face effects to the original cone. These formulas are reused throughout.

### 160.2 Singular points forced by actual repeated pairs

**定理 160.2（Each repeated sphere meets the singular locus）。** If $H,G$ are an actual repeated pair, then

$$
S(H)\cap\Sigma\ne\varnothing,\qquad S(G)\cap\Sigma\ne\varnothing.
\tag{XIII160.6}
$$

More precisely, for each $h\in S(H)$ there are labels $b_j\to s\in S(G)\cap\Sigma$ along a subsequence
with $D_{b_j}\to\{h\}$; the analogous statement holds with $H,G$ exchanged.
This does not assert that every point on either repeated sphere is singular.

证明。PR supplies PE by IX114.3. For the chosen $h\in S(H)$, apply [X124.7][X160], using its
extreme-dual-singleton mechanism X124.5: there are actual whole balls $D_{b_j}\to\{h\}$.
Compactness of $P$ permits a subsequence $b_j\to s\in P$.
[X124.9][X160] localizes the limit to $D_s=H$ and $s\in S(G)$; its isolation premise is (XIII160.3).
Since $H$ is nondegenerate and $D_{b_j}$ instead converges to a point, $D$ is discontinuous at $s$.
Thus $s\in\Sigma$. Choose any $h$ to obtain the second nonempty intersection, and exchange the two balls
to obtain the first. No stronger localization of the singular points has been used.证毕。

**定理 160.3（Repeated balls approaching a singleton force singularity on both limiting sides）。**
Let $p\in P_{\rm s}$, and let repeated actual balls $H_n\to D_p$ have partners $G_n$.
Then

$$
G_n\longrightarrow\{p\},\qquad \{p\}\cup S(D_p)\subset\Sigma.
\tag{XIII160.7}
$$

Consequently, for $p\in\mathcal R\cap P_{\rm s}$ there is a Hausdorff neighborhood of $D_p$
containing no repeated actual ball.

证明。Take arbitrary $s_n\in S(G_n)=I(H_n)$ and any convergent subsequence $s_n\to s\in P$.
For each $x\in D_p$, Hausdorff convergence supplies $x_n\in H_n=D_{s_n}$ with $x_n\to x$.
The closed zero graph IX115.4 gives $x\in D_s$, so $D_p\subseteq D_s$.
Maximality of these proper faces gives $D_s=D_p$, and the singleton label gives $s=p$.
Compactness of $P$ now gives uniform collapse of the entire partner spheres:
otherwise some $s_n\in S(G_n)$ would remain a fixed positive distance from $p$ and have a different cluster point.
Since $G_n=\operatorname{conv}S(G_n)$, the same distance bound holds throughout $G_n$.
Nonemptiness then gives $G_n\to\{p\}$.

Theorem 160.2 supplies $s_n\in S(G_n)\cap\Sigma$ for each $n$.
Uniform collapse gives $s_n\to p$, so closedness of $\Sigma$ gives $p\in\Sigma$.
To treat the other limiting side, use D. Labardini-Fragoso, M. Neumann-Coto and M. Takane,
*Cones and convex bodies with modular face lattices*, [Lemma 4(b)][LNT160].
That part of the lemma applies to any convex body with compact extreme set: convergence of actual faces to an actual face
implies Hausdorff convergence of their extreme sets. It has no modularity premise.
Here the body is $K$ in $\operatorname{aff}K$, its extreme set $P$ is compact by IX114.4,
and $H_n,D_p$ are actual faces. Thus $S(H_n)\to S(D_p)$.
For each $q\in S(D_p)$ choose $q_n\in S(H_n)$ with $q_n\to q$.
Pairing gives $D_{q_n}=G_n\to\{p\}$, whereas $D_q$ is a nondegenerate three-ball.
Hence $q\in\Sigma$, proving the full inclusion in (XIII160.7).

Finally, if every Hausdorff neighborhood of a regular singleton ball $D_p$ contained a repeated actual ball,
choose one at distance less than $1/n$ for each $n$. The result just proved would force $p\in\Sigma$,
contradicting $p\in\mathcal R$. This proves the neighborhood assertion.证毕。

### 160.3 An open dense domain of singleton labels

**定理 160.4（Generic regular singleton labels）。** The set

$$
U=\mathcal R\cap P_{\rm s}
\tag{XIII160.8}
$$

is open and dense in the entire original pure locus $P$.

证明。First fix $z\in\mathcal R$. If $z$ is singleton, it already belongs to $U$.
If $z$ is repeated, it lies on one sphere of an actual repeated pair by IX116.2.
X124.7 therefore supplies actual whole balls $L_j\to\{z\}$.
Since $\mathcal R$ is open in $P$, all of $S(L_j)$ lies in $\mathcal R$ for large $j$.
Theorem 160.2 rules out repeated $L_j$, since such a ball would have a sphere point in $\Sigma$.
Thus $L_j$ has a singleton label. IX116.6 gives $S(L_j)\subset P_{\rm s}$, so in fact $S(L_j)\subset U$.
Choosing any $t_j\in S(L_j)$ gives $t_j\to z$. Every regular label is consequently in $\overline U^{\,P}$.
Since $\mathcal R$ is dense in $P$, $U$ is dense in $P$.

To prove openness, let $p\in U$. Openness of $\mathcal R$ supplies a pure neighborhood of $p$ contained in $\mathcal R$.
If no such neighborhood consisted entirely of singleton labels, there would be repeated labels $b_j\to p$.
Continuity at $p$ would give $D_{b_j}\to D_p$, contrary to the last assertion of Theorem 160.3.
Hence a smaller neighborhood is contained in $U$, proving that $U$ is open in $P$.证毕。

### 160.4 Dense zero kernel without an ambient dimension bound

**定理 160.5（Residual zero-kernel whole-face confirmation）。** Define

$$
Z=\{p\in U:a(p)=0\}.
\tag{XIII160.9}
$$

Then $Z$ is a dense $G_\delta$ subset of $P$. At every $p\in Z$,
$\mathcal A_p=\{e_p\}$, $N_{D_p}=\mathbb R_+e_p$, and
$R_p:L_p\to\operatorname{Aff}(D_p)$ is a linear isomorphism with $\dim L_p=4$.
In particular it is the whole-face zero normal $N_{D_p}$ that is a ray; $N_p$ is not a ray.

证明。Fix $p\in U$ and any $y\in\operatorname{ri}D_p$.
This is a mixed boundary state, since the relative boundary of the three-ball consists exactly of its pure points.
We use the inner-ball support construction of [IX120.9][IX160], supplying its local label and ball convergence here
in place of that theorem's global Inj premise.

Choose $z_j\in\operatorname{ri}K$ with $z_j\to y$, let
$r_j=\operatorname{dist}(z_j,\partial_{\rm rel}K)>0$, and choose a nearest boundary contact $x_j$.
The closed relative Euclidean ball $\overline B(z_j,r_j)$ is contained in $K$:
a segment from $z_j$ to any point of that ball outside $K$ would first meet the boundary at a smaller distance.
Since $y$ is itself a boundary point,

$$
\|x_j-y\|\le r_j+\|z_j-y\|\le2\|z_j-y\|\longrightarrow0.
\tag{XIII160.10}
$$

Every supporting hyperplane of $K$ at $x_j$ also supports this inner ball at the same contact,
and hence is the ball's unique tangent hyperplane there.
Homogenizing affine functions on $K$ identifies the nonnegative functions vanishing at $x_j$
with $N_{x_j}:=\{h\in C^*:h(x_j)=0\}$; unique support makes this cone a nonzero ray.
Compactness of $P$ and $y\notin P$ give $x_j\notin P$ eventually.
Any supporting face through such an $x_j$ is nonpoint, hence is an actual whole ball $H_j$ by the face classification.
As the boundary of $H_j$ is pure, $x_j\in\operatorname{ri}H_j$.

A nonnegative affine function zero at a relative interior point of a face is zero on the entire face:
for any point of the face, extend a short segment through that interior point in the opposite direction;
the convex-combination identity and nonnegativity at both endpoints force both values to vanish.
Thus $N_{H_j}=N_{x_j}$ and $\dim\operatorname{span}N_{H_j}=1$.
Choose any original label $p_j\in I(H_j)$.

For completeness, convergence of contacts alone is insufficient; the whole faces and labels converge as follows.
From any subsequence, compactness of $P$ and of the hyperspace of nonempty compact subsets of $K$
permits a further subsequence with $p_j\to t\in P$ and $H_j\to Q$.
IX115.5 says $Q=D_t$ or $Q$ is a pure singleton.
The limit contains $y$, so its mixedness excludes the singleton branch.
The actual balls $D_t,D_p$ share the mixed point $y$, so the face-intersection rule gives $D_t=D_p$.
The singleton label of $D_p$ then gives $t=p$.
Every subsequence has these same limiting values, proving

$$
H_j\longrightarrow D_p,\qquad p_j\longrightarrow p.
\tag{XIII160.11}
$$

Theorem 160.3 excludes repeated $H_j$ for all sufficiently large $j$, because $p$ is regular singleton.
For those terms $p_j\in P_{\rm s}$, and (XIII160.4) gives
$a(p_j)+1=\dim\operatorname{span}N_{H_j}=1$.
Openness of $U$ and $p_j\to p$ put $p_j\in U$ eventually, hence $p_j\in Z$.
Thus $Z$ is dense in $U$, and Theorem 160.4 makes it dense in all $P$.

It remains to prove the stated descriptive topology, rather than infer it from density.
Each $\mathcal A_p$ is a nonempty compact subset of the same original compact effect interval $\mathcal E$.
On $U$ these sets have closed graph. Indeed, suppose $p_j\to p\in U$ and $e_j\to e$ with $e_j\in\mathcal A_{p_j}$.
Then $e\in\mathcal E$ and $e(p)=1$.
For each $x\in D_p$, continuity at $p$ gives $x_j\in D_{p_j}$ with $x_j\to x$,
so $e(x)=\lim_j e_j(x_j)=0$. Hence $e\in\mathcal A_p$.

Define $d_A(p)=\operatorname{diam}_{V^*}\mathcal A_p$ on $U$.
Compactness of $\mathcal E$ and the closed graph make $d_A$ upper semicontinuous:
along a subsequence attaining any limiting upper value, take maximizing pairs in $\mathcal A_{p_j}$,
pass to convergent pairs in $\mathcal E^2$, and use the closed graph to bound their limit distance by $d_A(p)$.
By (XIII160.4), $a(p)=0$ exactly when $d_A(p)=0$. Therefore

$$
Z=\bigcap_{k\ge1}\{p\in U:d_A(p)<1/k\}.
\tag{XIII160.12}
$$

Each factor is open in $U$, hence open in $P$ since $U$ is open.
Each contains the already dense $Z$, so each is dense in $P$.
This proves the dense $G_\delta$ assertion.
Finally (XIII160.4) gives the singleton confirmer, the ray $N_{D_p}$ and the four-dimensional restriction isomorphism.
Its domain is $L_p=\operatorname{span}N_p$, whose dimension four rules out $N_p$ being a ray.
No order-preserving inverse or least element of $F_p$ follows from this linear isomorphism.证毕。

### 160.5 The extended-supremum reduction and the unpaid classification bridge

**定理 160.6（The full uniform-budget question is already present on $Z$）。** With extended suprema in $[1,+\infty]$,

$$
\sup_{p\in P}\beta_{D_p}=\sup_{p\in Z}\beta_{D_p}.
\tag{XIII160.13}
$$

In this same complete EB3+PR domain the following are equivalent:

$$
\begin{gathered}
\sup_{p\in Z}\beta_{D_p}<\infty;\qquad \sup_{p\in P}\beta_{D_p}<\infty;\qquad
\forall p\in P:\beta_{D_p}=1;\\
\exists\text{ real-linear bijection }\Psi:V\longrightarrow\operatorname{Herm}_3(\mathbb C):\quad
\Psi(C)=\operatorname{Herm}_3(\mathbb C)_+,\quad u=\operatorname{Tr}\circ\Psi.
\end{gathered}
\tag{XIII160.14}
$$

Equivalently, either the original cone and unit have this static complex qutrit representation and all budgets are one,
or $\sup_{p\in Z}\beta_{D_p}=+\infty$.
This is a conditional dichotomy; it does not assert realizability of the second branch.
If the supremum is infinite, there are $z_n\in Z$ and, after a subsequence, $s,r\in P$ such that

$$
\begin{gathered}
\beta_{D_{z_n}}\longrightarrow+\infty,\quad \operatorname{diam}D_{z_n}\longrightarrow0,\quad
z_n\longrightarrow s\in\Sigma,\\
D_{z_n}\longrightarrow\{r\},\qquad r\in D_s,\qquad r\ne s.
\end{gathered}
\tag{XIII160.15}
$$

证明。By IX115.6, $p\mapsto\beta_{D_p}$ is lower semicontinuous on all $P$.
For every real $t$, a nonempty strict superlevel set $\{p\in P:\beta_{D_p}>t\}$ is open and meets dense $Z$.
Consequently, if the left supremum in (XIII160.13) exceeds $t$, so does the right supremum.
The reverse inequality follows from $Z\subset P$.
These comparisons for every finite $t$ prove equality for both finite and infinite extended suprema.

The remaining equivalences are exactly [X124.10–124.11][X160], now applied using (XIII160.13).
Their uniform finite budget condition is on every actual ball of the same original cone;
it yields noncollapse, then injectivity, and then the existing static classification.
The inverse of the source's $\Phi:\operatorname{Herm}_3(\mathbb C)\to V$ is the $\Psi$ in (XIII160.14).
No classification theorem is being extended to weaker premises in this step.
Since every individual budget is finite and at least one by IX114.6,
failure of the finite-supremum branch means precisely the infinite branch stated above.

In that branch choose $z_n\in Z$ with $\beta_{D_{z_n}}>n$.
For every $\varepsilon>0$, IX115.3 bounds the budget of any actual ball of diameter at least $\varepsilon$
by $1/\gamma(\varepsilon)<\infty$; thus $\operatorname{diam}D_{z_n}\to0$.
Choose $r_n\in S(D_{z_n})$. Compactness of $P$ gives a joint subsequence $z_n\to s\in P$, $r_n\to r\in P$.
For every $x\in D_{z_n}$,
$\|x-r\|\le\operatorname{diam}D_{z_n}+\|r_n-r\|\to0$,
so the whole balls converge to $\{r\}$.
The closed zero graph gives $r\in D_s$, while $T_s(s)=1$ gives $r\ne s$.
If $s$ were regular, continuity would instead give $D_{z_n}\to D_s$, a nondegenerate ball;
hence $s\in\Sigma$. This proves (XIII160.15).证毕。

**命题 160.7（Geometric interpretation and the exact remaining implication）。** Under Definition 160.1,
singleton labels are generic on the open dense set $U$, and the subset $Z$ of regular singleton labels
with exactly one normalized whole-face confirmer is dense $G_\delta$ in $P$.
The remaining implication needed for (XIII160.14) from complete EB3 and pure PR alone is

$$
\exists M<\infty\quad\forall p\in Z:\ \beta_{D_p}\le M.
\tag{XIII160.16}
$$

This uniform bound is not proved here. Density of $Z$, its zero kernels, and the pointwise finiteness of its budgets
do not by themselves establish (XIII160.16).

证明。The genericity and uniqueness assertions are Theorems 160.4–160.5, and the necessary and sufficient bridge
to the stated static representation is (XIII160.13)–(XIII160.14).
Geometrically, the original ball and endpoint conditions already produce a large set of labels where one whole-face
confirmer is forced: the nonnegative function vanishing on that whole ball has one normalized direction.
At the associated pure point there are still four independent normal directions.
Thus generic uniqueness arises endogenously, without adding another uniqueness axiom.
The remaining question is uniform contrast and scale: can the contrasts $\delta(D_p)$ on $Z$ approach zero,
so that whole balls shrink and their extension budgets diverge, or must they have one common positive lower bound?
Theorem 160.6 gives the exact equivalence between excluding that loss and obtaining the static qutrit model.

Local bounds near points of $Z$ do not answer the uniform question.
IX115.6 supplies such bounds at every regular point, but these neighborhoods need not cover $\Sigma$;
$Z$ need not be closed or compact. Compactness of $P$ therefore does not supply a finite subcover of $P$ from them.
The present results neither force every label to have zero kernel nor prove $\Sigma=\varnothing$,
global Inj, absence of repeated pairs, or the representation from EB3+PR alone.
The finite-rank L2/L3/actual-NC entrance of [chapter 159][XII160] is a different conditional reconstruction route;
its extra common-realization and noncollapse premises are not supplied by this generic theorem.
Physical composites, instruments, dynamics and a value of $\hbar$ also remain outside these static conclusions.

The mathematical attribution of Theorems 160.2–160.6 is `repo-derived`: the new content is their original-domain
combination of repeated-pair localization, regularity, local normal redundancy and dense-set budget reduction.
The face classification, pure exposure and compactness, contrast and budget formulas, repeated-pair structure,
inner-ball support construction, and conditional qutrit classification retain their cited project suppliers.
The compact-extreme-set face convergence step is the mature Lemma 4(b) of [LNT160], used only in Theorem 160.3;
its modular-face-lattice classification results are not invoked.
These are paper proofs, with no Lean/kernel certification, global priority or minimality claim.证毕。

[Faces160]: ../../../Blueprint/D5/S3/Quantum/Foundation/ExclusionBallFaces.md "Theorem 1.7, exclusion_ball_faces; only its first two conclusions are used."
[IX160]: https://github.com/the-omega-institute/trureturing/blob/d4a6bd75fd78850fed8cf60aebb6ce7fceffa2e1/docs/develop/theory/QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX114.2–114.6; IX115.3–115.6; IX116.2 and IX116.6; IX120.9."
[X160]: https://github.com/the-omega-institute/trureturing/blob/d4a6bd75fd78850fed8cf60aebb6ce7fceffa2e1/docs/develop/theory/QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_X.md "X124.5, X124.7, X124.9–X124.11."
[XII160]: https://github.com/the-omega-institute/trureturing/blob/d4a6bd75fd78850fed8cf60aebb6ce7fceffa2e1/docs/develop/theory/QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XII.md "Dimension-free Lemma XII147.2 and the distinct finite-rank entrance in chapter 159."
[LNT160]: https://arxiv.org/pdf/0903.0643v1 "D. Labardini-Fragoso, M. Neumann-Coto and M. Takane, Cones and convex bodies with modular face lattices, Lemma 4(b); compact extreme set and actual faces, without modularity for this lemma."

## 追加锚（本行以下为增补区）
