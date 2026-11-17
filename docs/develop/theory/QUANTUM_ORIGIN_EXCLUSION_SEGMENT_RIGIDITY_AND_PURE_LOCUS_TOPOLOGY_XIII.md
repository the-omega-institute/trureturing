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
complete EB3 already supplies its actual-face NC by (XII159.38), distinct from chapter 124's uniform noncollapse.
The actual L2 and L3 conditions for every pair and triple remain unproved here.
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

## 163. Singular landings of actual zero-kernel collapses

**定义 163.1（Original domain, actual zero-kernel labels and static scope）。** Take exactly the data and hypotheses of Definition 160.1:
$V\ne0$ is finite-dimensional over $\mathbb R$, $C$ is closed, pointed and generating, and $u$ is strictly positive on $C\setminus\{0\}$.
The objects $K=C\cap\{u=1\}$, $P=\operatorname{ext}K$, $\mathcal E=[0,u]_{C^*}$ and
$F_p=\{f\in\mathcal E:f(p)=1\}$ are the entire original objects. For every original $x\in K$, including mixed $x$,
$T_p(x)=\min_{f\in F_p}f(x)$ is attained and $D_p=\{x\in K:T_p(x)=0\}$ is the entire zero set.
Assume every $D_p$ is a nondegenerate affine closed three-ball and only the literal reciprocity
$T_p(q)=T_q(p)$ for $p,q\in P$. Keep the auxiliary norms and all notation of Definition 160.1, and put

$$
\begin{gathered}
S_p=P\cap D_p,\qquad G_p=N_p\cap\mathcal E=\{h\in\mathcal E:h(p)=0\},\\
U=\mathcal R\cap P_{\rm s},\qquad Z=\{p\in U:a(p)=0\}.
\tag{XIII163.1}
\end{gathered}
$$

Thus $Z$ is the actual dense $G_\delta$ of Theorem 160.5, and $\Sigma=P\setminus\mathcal R$ is the actual discontinuity locus
of the whole-ball map. The budget $\beta_{D_p}$ is the positive-extension budget of (XIII160.5), for all affine effects
on the whole face and extensions to the original cone.
There is no dimension upper bound, all-pair proper-face assumption, global label injectivity, least confirmer,
positive restriction inverse, spectrality or projectivity premise.
In particular the affine-infimum property $(**)$ of [Niestegge, §3 and Theorem 1][N163] is not assumed:
that infimum ranges over all nonnegative affine functions normalized at the source, without the upper bound by the unit.
The projective-face and well-behaved transition-space hypotheses of [Landsman, §§1.2–1.3][L163] are also not assumed.

The data here are static. They specify no family of physically available preparations or controls, instruments,
composites or positivity tests against every finite spectator, and no time, Hamiltonian, energy or $\hbar$ calibration.
The source, full-history, native-control and genuine all-future Return conditions of [OTF008, Definition 21.6][OTF163]
remain separate conditions; a comparison with a run's own marginal is not such a Return condition.

**定理 163.2（Singleton common-zero face and singular landing）。** Under Definition 163.1, let $z_n\in Z$ and suppose

$$
z_n\longrightarrow s,\qquad D_{z_n}\longrightarrow\{r\}
\quad\text{in Hausdorff distance}.
\tag{XIII163.2}
$$

For $q\in S_{z_n}$ let $e_q$ denote the unique member of $\mathcal A_q$; its existence and uniqueness follow from
the local calculation below, even when $q\notin Z$.
Define the cluster family using every actual neighboring label:

$$
\begin{aligned}
\mathcal B
&=\bigcap_{m\ge1}\overline{\bigcup_{n\ge m}\{e_q:q\in S_{z_n}\}}^{\,\mathcal E}\\
&=\{b\in\mathcal E:\ \exists n_j\uparrow\infty,\ q_j\in S_{z_{n_j}},\ e_{q_j}\to b\}.
\end{aligned}
\tag{XIII163.3}
$$

This is a nonempty compact family, and

$$
\begin{gathered}
\mathcal B\subseteq\{b\in\mathcal E:b(r)=1,\ b(s)=0\},\qquad
K\cap\bigcap_{b\in\mathcal B}\ker b=\{s\},\\
s,r\in\Sigma,\qquad r\in S_s,\qquad s\ne r.
\tag{XIII163.4}
\end{gathered}
$$

The assertion applies to every collapse (XIII163.2) on actual $Z$, without a budget-divergence hypothesis.

证明。We first supply the full-menu estimate needed at each $p\in Z$.
Theorem 160.5 gives $\mathcal A_p=\{e_p\}$ and the isomorphism
$R_p:L_p\to\operatorname{Aff}(D_p)$ with $\dim L_p=4$.
The dimension-free [Lemma XII147.2][XII163] gives singleton labels at every $q\in S_p$,
$a(q)=a(p)=0$, and hence $\mathcal A_q=\{e_q\}$.
It also gives the singleton top face of each $e_q$ and the original positive-annihilator maximum identity

$$
\max_Kh=\max_{D_p}h\quad(h\in N_p).
\tag{XIII163.5}
$$

These are the local suppliers used in the calculation of [XII147.6][XII163].
That proposition has a nine-dimensional premise; the calculation needed here follows directly from XII147.2 and
$a(p)=0$, as follows, without importing that premise.

Write $D_p=c+B\overline B^3$ with $B:\mathbb R^3\to\ker u$ injective, and let $g=u-e_p$.
The constant-one relative-interior representative and slice identity in the proof of XII147.2 give
$g\in\operatorname{ri}N_p$, $g|_{D_p}=1$, and $K\cap\ker g=\{p\}$.
Use $R_p^{-1}$ only as a linear map to choose $H_i\in L_p$, $1\le i\le3$, such that
$H(c+Bw)=w$, where $H=(H_1,H_2,H_3)$.
Every element of $L_p$ is uniquely $\alpha g+v\cdot H$. Define

$$
\rho(v)=\sup_{x\in K\setminus\{p\}}\frac{-v\cdot H(x)}{g(x)}.
\tag{XIII163.6}
$$

The denominator is strictly positive on the indicated domain. Relative interior supplies $\varepsilon>0$ such that
$g\pm\varepsilon H_i\in N_p$ for all three $i$; therefore
$\|H(x)\|\le\sqrt3g(x)/\varepsilon$ on all $K$.
Thus $\rho$ is finite. Evaluation at $c-Bv/\|v\|$ gives $\rho(v)\ge\|v\|$ for $v\ne0$, and $\rho(0)=0$.
The definition, $H(p)=g(p)=0$, and $C=\mathbb R_{\ge0}K$ now give the exact equivalence

$$
\alpha g+v\cdot H\in N_p\quad\Longleftrightarrow\quad\alpha\ge\rho(v).
\tag{XIII163.7}
$$

Only after this positivity condition holds, (XIII163.5) gives
$\max_K(\alpha g+v\cdot H)=\alpha+\|v\|$.

Fix a unit $t\in\mathbb R^3$ and put $q_\pm=c\pm Bt$, $R_\pm=\rho(\pm t)\ge1$.
Reciprocity puts $p\in D_{q_\pm}$, so $e_{q_\pm}\in N_p$.
The ball-support equality at the unique top point $q_\pm$ and injectivity of $R_p$ imply

$$
e_{q_\pm}=(1-\theta_\pm)g\pm\theta_\pm t\cdot H,\qquad 0<\theta_\pm\le\tfrac12.
\tag{XIII163.8}
$$

Indeed a zero slope would make the whole $D_p$ part of its singleton top face.
Positivity gives $(1-\theta_\pm)/\theta_\pm\ge R_\pm$.
Choose $y_\pm\in D_{q_\pm}\setminus\{p\}$, which exists because this entire exclusion is a nondegenerate three-ball.
Then $g(y_\pm)>0$ and $e_{q_\pm}(y_\pm)=0$ give the reverse inequality in (XIII163.6).
Consequently, as identities on the entire original $V$,

$$
\begin{gathered}
e_{q_\pm}=\frac{R_\pm g\pm t\cdot H}{1+R_\pm},\\
g=A_t e_{q_+}+B_t e_{q_-},\qquad
A_t=\frac{1+R_+}{R_++R_-},\quad B_t=\frac{1+R_-}{R_++R_-},\quad
A_t+B_t=1+\frac2{R_++R_-}\le2.
\tag{XIII163.9}
\end{gathered}
$$

Now take any nonzero $h=\alpha g+v\cdot H\in G_p$.
Its maximum is $M=\alpha+\|v\|\in(0,1]$.
If $v\ne0$, take $t=v/\|v\|$ and
$\lambda=(1+\rho(t))\|v\|/M\in[0,1]$, using (XIII163.7) and positive homogeneity of $\rho$.
Then

$$
\frac hM=(1-\lambda)g+\lambda e_{q_+}.
\tag{XIII163.10}
$$

Substitution of (XIII163.9) expresses $h$ as
$M((1-\lambda)A_t+\lambda)e_{q_+}+M(1-\lambda)B_t e_{q_-}$.
Both coefficients are nonnegative and their sum is at most $2$.
For $v=0$ use (XIII163.9) in any unit direction and $h=Mg$.
For $h=0$ take both coefficients zero. Thus every member of the entire original $G_p$ is a nonnegative combination
of two actual neighboring whole-face confirmers with coefficient sum at most $2$.
In particular, for every original mixed or pure $x\in K$,

$$
0\le\max_{h\in G_p}h(x)\le2\sup_{q\in S_p}e_q(x),\qquad
T_p(x)=1-\max_{h\in G_p}h(x).
\tag{XIII163.11}
$$

The second identity uses the bijection $F_p=u-G_p$ for the full original menus.
The constant $2$ bounds generating coefficients in $G_p$; it is not a bound on $\beta_{D_p}$,
a positive inverse for restriction, or a least-confirmer statement.

We now apply this estimate to (XIII163.2).
Pure compactness [IX114.4][IX163] gives $s,r\in P$: for $r$, choose any $q_n\in S_{z_n}$ and use the whole-ball collapse.
In fact every such choice converges to $r$, uniformly over $S_{z_n}$.
The closed zero graph [IX115.4][IX163] gives $r\in D_s$; $T_s(s)=1$ gives $r\ne s$.
Regularity at $s$ would give $D_{z_n}\to D_s$, contradicting the singleton limit and EB3, so $s\in\Sigma$.

The interval $\mathcal E$ is compact. Its nonempty compact tail closures in (XIII163.3) are nested,
so $\mathcal B$ is nonempty compact. In this finite-dimensional metric space their intersection is exactly the
subsequential cluster family on the second line of (XIII163.3).
Let $L=\max_{e\in\mathcal E}\|e\|_*<\infty$.
For any defining sequence $e_{q_j}\to b$ with $q_j\in S_{z_{n_j}}$, we have $q_j\to r$,
$e_{q_j}(q_j)=1$ and $e_{q_j}(z_{n_j})=0$.
The last equality uses $z_{n_j}\in D_{q_j}$ and whole-face vanishing.
Bounded effect norms and joint continuity therefore give $b(r)=1$ and $b(s)=0$.

Set $Q=K\cap\bigcap_{b\in\mathcal B}\ker b$. This is a nonempty compact face of $K$ containing $s$.
Fix an original pure point $x\in P\cap Q$.
Then

$$
\sup_{q\in S_{z_n}}e_q(x)\longrightarrow0.
\tag{XIII163.12}
$$

Otherwise some $\eta>0$ and a subsequence admit $q_j\in S_{z_{n_j}}$ with $e_{q_j}(x)\ge\eta$.
Compactness of $\mathcal E$ gives a further effect limit $b\in\mathcal B$ with $b(x)\ge\eta$,
contradicting $x\in Q$.
By (XIII163.11), (XIII163.12) implies $T_{z_n}(x)\to1$.
Here $z_n$ and $x$ are pure, so literal pure reciprocity gives $T_x(z_n)=T_{z_n}(x)\to1$.
The fixed function $T_x$ is $L$-Lipschitz on all $K$ by [IX114.4][IX163], hence $T_x(s)=1$.
Pure exposure [IX114.3][IX163] supplies an original confirmer of $x$ whose top face is $\{x\}$.
Since $T_x$ is bounded above by that confirmer, $T_x(s)=1$ forces $s=x$.
Thus $P\cap Q=\{s\}$.
Every extreme point of the compact face $Q$ is extreme in $K$, and finite-dimensional compact convex sets are
convex hulls of their extreme points. This proves $Q=\{s\}$, including its entire mixed domain.

Finally suppose $r\in\mathcal R$.
For each $b\in\mathcal B$ choose a defining sequence $q_j\to r$, $e_{q_j}\to b$.
Regularity at $r$ gives convergence of the entire balls $D_{q_j}\to D_r$.
For every $y\in D_r$ choose $y_j\in D_{q_j}$ with $y_j\to y$.
Since $e_{q_j}(y_j)=0$ and the effect norms are bounded by $L$, it follows that $b(y)=0$.
This holds for every $b\in\mathcal B$ and every mixed or pure $y\in D_r$.
It would imply $D_r\subseteq Q=\{s\}$, contrary to EB3.
Therefore $r\in\Sigma$, completing (XIII163.4).
The common-zero conclusion concerns the limit family $\mathcal B$; it asserts no exact common contact at a finite index.证毕。

**推论 163.3（Every singular root has an actual singular zero-neighbor）。** Under Definition 163.1, for each specified
$s\in\Sigma$ there exist $r\in\Sigma\cap S_s$ and a sequence $z_n\in Z$ such that

$$
\begin{gathered}
z_n\to s,\qquad \beta_{D_{z_n}}\to+\infty,\qquad D_{z_n}\to\{r\},\\
r\ne s,\qquad T_s(r)=T_r(s)=0.
\tag{XIII163.13}
\end{gathered}
$$

In particular, the non-qutrit branch of Theorem 160.6 requires an actual orthogonal pair entirely inside $\Sigma$.

证明。The local-budget equivalence of [IX115.6][IX163] says that every neighborhood of $s\in\Sigma$
has unbounded budgets. For each $n$ the relative open ball $\{p\in P:\|p-s\|<1/n\}$ therefore contains a point
with $\beta_{D_p}>n$.
The budget is lower semicontinuous on all $P$, so this ball's intersection with $\{p:\beta_{D_p}>n\}$ is nonempty open.
Density of the actual $Z$ supplies $z_n$ in that intersection.
Thus $z_n\to s$ and $\beta_{D_{z_n}}>n$.
By [IX115.3][IX163], balls of diameter at least any fixed $\varepsilon>0$ have bounded budget;
consequently $\operatorname{diam}D_{z_n}\to0$.
Choose $r_n\in S_{z_n}$. Compactness of $P$ gives a subsequence $r_n\to r\in P$.
For every $x\in D_{z_n}$,
$\|x-r\|\le\operatorname{diam}D_{z_n}+\|r_n-r\|$, so the entire balls along that subsequence converge to $\{r\}$.
Relabel this subsequence. Theorem 163.2 gives $r\in\Sigma\cap S_s$ and $r\ne s$;
pure reciprocity supplies the displayed two zero values.
If the original cone and unit are not statically qutrit, Theorem 160.6 supplies such a collapse with a singular root,
so the assertion just proved gives the stated actual pair.
This is a necessary condition on that branch and makes no assertion that the branch is realizable.证毕。

**推论 163.4（Uniform budgets for balls meeting a fixed compact regular set）。** Under Definition 163.1,
for every fixed compact $A\subset\mathcal R$ there exists $M_A<\infty$ such that

$$
\forall z\in Z:\quad D_z\cap A\ne\varnothing\ \Longrightarrow\ \beta_{D_z}\le M_A.
\tag{XIII163.14}
$$

The labels $z$ need not lie in $A$. The intersection is with the entire original $D_z$.

证明。The empty intersection family is immediate, with $M_A=1$.
Otherwise, failure of (XIII163.14) would give $z_n\in Z$ with $\beta_{D_{z_n}}>n$ and
$x_n\in D_{z_n}\cap A$.
As in the preceding proof, [IX115.3][IX163] gives $\operatorname{diam}D_{z_n}\to0$.
Compactness of $A$ and $P$ gives a joint subsequence $x_n\to r\in A$, $z_n\to s\in P$.
The diameter estimate then gives $D_{z_n}\to\{r\}$.
Theorem 163.2 forces $r\in\Sigma$, contradicting $r\in A\subset\mathcal R$.
This proves the restricted uniform bound.

No assumption here makes every $D_z$ meet one fixed compact regular set, or excludes an orthogonal pair in $\Sigma$.
Thus (XIII163.14) is not the global bound over all $Z$ in (XIII160.16).
The exclusion of the singular branch, zero-kernel domination on all $Z$, all-Pair, and a faithful countermodel on the
entire original domain remain unresolved.
If all-Pair is separately obtained, [VII103.2–103.8][VII163] supplies the same-original static qutrit reconstruction
under EB3, without an additional TC or L3 premise.
The different [Binary Tangent XIII, Theorem 162.19][BT163] likewise retains its actual L2 premise;
neither entrance is supplied by the restricted bound.证毕。

[IX163]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX114.3–114.4: pure exposure, compact P and fixed-input Lipschitz continuity; IX115.3–115.6: diameter control, closed zero graph, regularity and budget semicontinuity."
[XII163]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XII.md "Dimension-free Lemma XII147.2; the supporting local calculation of XII147.6 is reconstructed here from actual zero kernel, without its nine-dimensional premise."
[VII163]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md "VII103.2 uses EB alone for proper-face exhaustion; VII103.3–103.8 retain all-Pair for reconstruction and the complete qutrit dictionary."
[BT163]: QUANTUM_ORIGIN_BINARY_TANGENT_CLOSURE_AND_GLOBAL_NONCOLLAPSE_XIII.md "Theorem 162.19: complete EB3 plus actual L2 iff same-original qutrit; the bare EB3+purePR entrance remains open."
[OTF163]: OTF_008_NATIVE_FOURIER_BETA_ACQUISITION_AND_FULL_RETURN.md "Definition 21.6: unchanged source, native-control, full-history and physical-return conditions."
[N163]: https://arxiv.org/html/2312.13213v2 "G. Niestegge, Quantum transition probability in convex sets and self-dual cones, §3 and Theorem 1: affine-infimum property (**) and its additional order assumptions."
[L163]: https://arxiv.org/html/quant-ph/9603005v2 "N. P. Landsman, Poisson spaces with a transition probability, §§1.2–1.3: projective faces and well-behaved transition probability spaces."

## 追加锚（本行以下为增补区）

## 164. Selected actual neighbors and uniform reverse collapse

**定义 164.1（Original objects and the selected neighboring family）。** Retain exactly Definition 163.1.
Thus $V\ne0$ is a finite-dimensional real vector space, $C\subset V$ is a closed pointed generating convex cone,
and $u$ is strictly positive on $C\setminus\{0\}$. On this same original carrier use

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad \mathcal E=[0,u]_{C^*},\\
F_p=\{e\in\mathcal E:e(p)=1\},\qquad
T_p(x)=\min_{e\in F_p}e(x)\quad(p\in P,\ x\in K),\\
D_p=\{x\in K:T_p(x)=0\},\qquad S_p=P\cap D_p.
\end{gathered}
\tag{XIII164.1}
$$

Every minimum is attained, every entire $D_p$ is a nondegenerate affine closed Euclidean three-ball,
and $T_p(q)=T_q(p)$ is assumed only for pure $p,q\in P$. The second input in (XIII164.1) includes every original mixed state.
Use the fixed auxiliary norms of Definition 160.1 and Hausdorff distance $d_H$ on nonempty compact subsets of $K$.
Let $\mathcal R=\operatorname{Cont}(p\mapsto D_p)$ and $\Sigma=P\setminus\mathcal R$.
As in (XIII160.2), $P_{\rm s}$ consists of singleton labels,
$N_p=\{h\in C^*:h(p)=0\}$, $L_p=\operatorname{span}_{\mathbb R}N_p$,
and $a(p)$ is the kernel dimension of signed restriction $L_p\to\operatorname{Aff}(D_p)$ at a singleton label.
Then $Z=\{p\in\mathcal R\cap P_{\rm s}:a(p)=0\}$ is the actual dense $G_\delta$ of Theorem 160.5.
For $p\in Z$ and every actual $q\in S_p$, the dimension-free [Lemma XII147.2, (XII147.4)][XII164]
gives $q\in P_{\rm s}$ and $a(q)=0$. Consequently
$\mathcal A_q=\{e\in F_q:e|_{D_q}=0\}=\{e_q\}$.
This defines the actual neighboring whole-face confirmer $e_q$ even when $q$ is not regular.
The full menu $F_q$ remains the original one; it contains $u$ and the nonconstant $e_q$ and is not this singleton.
The budget $\beta_F$ retains its original positive-extension meaning in (XIII160.5).

**定理 164.2（Uniform return over a fixed positive selection）。** Suppose $z_n\in Z$ and
$z_n\to s$, $D_{z_n}\to\{r\}$. By Theorem 163.2, $s,r\in P\cap\Sigma$, $s\ne r$,
and pure reciprocity gives $s\in S_r$. Fix any one $y\in S_r\setminus\{s\}$, and put

$$
\begin{gathered}
c=1-T_s(y)>0,\qquad \eta=c/8,\\
Q_n=\{q\in S_{z_n}:e_q(y)\ge\eta\}.
\end{gathered}
\tag{XIII164.2}
$$

There is $N$ such that $Q_n\ne\varnothing$ for every $n\ge N$, and, with this same fixed $y$ and $\eta$,

$$
\Delta_n:=\sup_{q\in Q_n}\ \sup_{x\in D_q}\|x-s\|\longrightarrow0.
\tag{XIII164.3}
$$

Both suprema concern actual objects, and the inner one ranges over the entire original ball, including its mixed interior.
No regularity of the selected $q$ is required.

证明。The nondegenerate ball $D_r$ has pure sphere $S_r$, so such a $y$ exists.
Pure exposure from [IX114.3][IX164] supplies an original confirmer of $s$ whose top face is $\{s\}$.
Its value at the distinct pure point $y$ is less than one, proving $c>0$.
By pure reciprocity at the pure endpoints $z_n,y$ and $s,y$, and fixed-row continuity
[IX114.4, (IX114.13)][IX164],

$$
T_{z_n}(y)=T_y(z_n)\longrightarrow T_y(s)=T_s(y).
$$

Choose $N$ so that $1-T_{z_n}(y)\ge c/2$ whenever $n\ge N$.
The original full-menu estimate (XIII163.11), applied with $p=z_n$ and $x=y$, gives

$$
c/2\le1-T_{z_n}(y)\le2\sup_{q\in S_{z_n}}e_q(y).
$$

Thus this supremum is at least $c/4=2\eta>\eta$.
Some actual $q$ has $e_q(y)>\eta$, so $Q_n$ is nonempty; no attainment of the supremum is used.
All subsequent indices may be restricted to this tail.

If (XIII164.3) failed, there would be $\varepsilon>0$, increasing indices $n_j$,
actual $q_j\in Q_{n_j}$, and original $x_j\in D_{q_j}$ with $\|x_j-s\|\ge\varepsilon$.
These witnesses can be chosen from the definition of a supremum, reducing $\varepsilon$ if necessary.
Since $q_j\in D_{z_{n_j}}$, the whole-ball collapse gives $q_j\to r$.
Compactness of the original $\mathcal E$ and $K$ permits a common subsequence with
$e_{q_j}\to b\in\mathcal E$ and $x_j\to x\in K$.
At every finite index, whole-face vanishing and the actual zero edge give

$$
e_{q_j}(q_j)=1,\qquad e_{q_j}(z_{n_j})=0,\qquad
 e_{q_j}(x_j)=0,\qquad e_{q_j}(y)\ge\eta.
$$

Here $z_{n_j}\in D_{q_j}$ follows from pure reciprocity on the actual pure pair $z_{n_j},q_j$.
Joint continuity of evaluation in finite dimension yields

$$
b(r)=1,\qquad b(s)=0,\qquad b(x)=0,\qquad b(y)\ge\eta>0.
\tag{XIII164.4}
$$

In particular $b$ belongs to the original $F_r$. Its entire zero face
$Z_K(b)=K\cap\ker b$ is nonempty, contains $s,x$, and is contained in $D_r$:
for every $v\in Z_K(b)$, $0\le T_r(v)\le b(v)=0$.
It is a face of $D_r$, and is proper because it omits $y\in D_r$.
A proper nonempty face of this affine Euclidean ball is a singleton.
Indeed, if it contained two distinct points, their midpoint would lie in $\operatorname{ri}D_r$;
a nonnegative affine function vanishing at that midpoint vanishes throughout $D_r$, contrary to $b(y)>0$.
Therefore $Z_K(b)=\{s\}$ and $x=s$, contradicting $\|x_j-s\|\ge\varepsilon$.
This proves the uniform estimate without exchanging PR at any mixed endpoint.证毕。

**推论 164.3（Selected synchronized actual pairs at every singular root）。** In Theorem 164.2 discard the finite initial
prefix and relabel. Any choices $q_n\in Q_n$, with $p_n=z_n$ on this common tail, give

$$
\begin{gathered}
p_n\in Z,\qquad q_n\in S_{p_n},\qquad
p_n\to s,\quad q_n\to r,\quad s\ne r,\\
D_{p_n}\longrightarrow\{r\},\qquad D_{q_n}\longrightarrow\{s\},\\
q_n\in P_{\rm s},\qquad a(q_n)=0,\qquad
\beta_{D_{p_n}}\longrightarrow+\infty,\quad \beta_{D_{q_n}}\longrightarrow+\infty.
\end{gathered}
\tag{XIII164.5}
$$

Every specified $s\in\Sigma$ is the first limit of such a pair, for some $r\in\Sigma\setminus\{s\}$.
No assertion places $q_n$ in $\mathcal R$ or in $Z$.

证明。The original collapse gives $q_n\to r$, and (XIII164.3) gives convergence of the entire nonempty $D_{q_n}$ to $\{s\}$.
The label and kernel assertions are [XII147.2, (XII147.4)][XII164], applied at $p_n\in Z$ along the actual edge.
Put $L=\max_{e\in\mathcal E}\|e\|_*<\infty$.
The contrast identity (XIII160.5) and the fixed-row Lipschitz estimate give the universal original-ball inequality
used in the proof of [IX115.3][IX164]:

$$
0<\beta_F^{-1}=\max_{v,w\in P\cap F}(1-T_v(w))\le L\operatorname{diam}F.
\tag{XIII164.6}
$$

Both diameters in (XIII164.5) tend to zero, so both budgets tend to infinity.
For a specified $s\in\Sigma$, Corollary 163.3, (XIII163.13), supplies the initial $Z$-collapse to some
$r\in\Sigma\cap S_s$, $r\ne s$. Choose one $y\in S_r\setminus\{s\}$ and apply Theorem 164.2,
keeping that $y$ fixed throughout the sequence.

Along any convergent subsequence of the selected $e_{q_n}$, the limit $b$ belongs to the cluster family
$\mathcal B$ of (XIII163.3) and satisfies (XIII164.4), hence $Z_K(b)=\{s\}$.
Such a subsequence exists by compactness of $\mathcal E$.
The existence of an original effect with $b(r)=1$ and $Z_K(b)=\{s\}$ is already supplied by
[X126.3, (X126.10)][X164], with its limiting pair $(p,q)$ identified with $(s,r)$.
Here it is obtained as a limit of the actual neighboring $e_{q_n}$ with a fixed positive reading at $y$;
the uniform control (XIII164.3) concerns all their whole reverse balls.证毕。

**推论 164.4（Compact symmetric irreflexive collapse relation）。** Define a relation on the original pure locus by

$$
\mathcal C_Z=\{(s,r)\in P^2:\ \exists z_n\in Z,\ z_n\to s,
\ d_H(D_{z_n},\{r\})\to0\}.
\tag{XIII164.7}
$$

Then $\mathcal C_Z$ is compact, symmetric and irreflexive, and

$$
\begin{gathered}
\mathcal C_Z\subseteq\{(s,r)\in\Sigma^2:s\ne r,\ T_s(r)=T_r(s)=0\},\\
\pi_1(\mathcal C_Z)=\pi_2(\mathcal C_Z)=\Sigma.
\end{gathered}
\tag{XIII164.8}
$$

证明。Theorem 163.2, (XIII163.4), gives the inclusion and irreflexivity for every defining collapse.
Corollary 163.3 gives $\pi_1(\mathcal C_Z)=\Sigma$.
To prove symmetry, fix $(s,r)\in\mathcal C_Z$ and use Corollary 164.3 to obtain actual neighboring $q_n\to r$
whose entire balls converge to $\{s\}$.
The $q_n$ need not be regular. For each fixed $n$, the one-sided upper semicontinuity of
[IX115.4, (IX115.9)][IX164] gives a relative open neighborhood $U_n$ of $q_n$ in $P$ such that

$$
w\in U_n\quad\Longrightarrow\quad
D_w\subseteq\{x\in K:\operatorname{dist}(x,D_{q_n})<1/n\}.
\tag{XIII164.9}
$$

This uses the open $1/n$-neighborhood of the compact value $D_{q_n}$.
It asserts only the displayed containment, not Hausdorff closeness to $D_{q_n}$ in both directions.
Density of $Z$ in $P$ permits
$w_n\in Z\cap U_n$ with $\|w_n-q_n\|<1/n$.
Then $w_n\to r$ and

$$
\sup_{x\in D_{w_n}}\|x-s\|
\le 1/n+\sup_{v\in D_{q_n}}\|v-s\|\longrightarrow0.
\tag{XIII164.10}
$$

The values are nonempty, so $D_{w_n}\to\{s\}$ and $(r,s)\in\mathcal C_Z$.
This perturbation does not preserve the original edge: $w_n\in S_{z_n}$ is not asserted.
The synchronized actual edge is the unperturbed $q_n\in S_{z_n}$ in (XIII164.5).
Symmetry now also gives the second projection assertion.

For closedness, let $(s_j,r_j)\in\mathcal C_Z$ converge in $P^2$ to $(s,r)$.
From a defining sequence for each pair choose one $v_j\in Z$ with
$\|v_j-s_j\|<1/j$ and $d_H(D_{v_j},\{r_j\})<1/j$.
Then $v_j\to s$ and $d_H(D_{v_j},\{r\})\to0$, so $(s,r)\in\mathcal C_Z$.
Thus the relation is closed in the compact space $P^2$, where compactness of $P$ is [IX114.4][IX164],
and hence is compact. This also covers the case $\Sigma=\varnothing$, when the relation is empty.证毕。

**推论 164.5（Exact static consumer）。** Under Definition 164.1 the following conditions are equivalent:

$$
\begin{gathered}
\exists\text{ real-linear bijection }\Psi:V\to\operatorname{Herm}_3(\mathbb C):\quad
\Psi(C)=\operatorname{PSD}_3(\mathbb C),\qquad u=\operatorname{Tr}\circ\Psi;\\
\Sigma=\varnothing;\\
\nexists\ s,r\in P,\ p_n\in Z,\ q_n\in S_{p_n}:\quad
s\ne r,\quad p_n\to s,\quad q_n\to r,\quad
D_{p_n}\to\{r\},\quad D_{q_n}\to\{s\}.
\end{gathered}
\tag{XIII164.11}
$$

In the last condition, $p_n,q_n$ range over sequences, the memberships hold for every $n$,
and the two whole-ball limits are Hausdorff limits.

证明。First consider the standard qutrit with its entire original effect interval.
At a rank-one projector $p$, every confirmer matrix $A$ satisfies $0\le A\le I$ and $\operatorname{Tr}(Ap)=1$.
Positivity of $I-A$ therefore gives $(I-A)p=0$, so $Ap=p$;
the other block of the Hermitian $A$ on $p^\perp$ is nonnegative.
Consequently $A\ge p$, and $A=p$ attains the minimum.
Thus in these coordinates

$$
T_p(X)=\operatorname{Tr}(pX),\qquad
D_p=\{X\ge0:\operatorname{Tr}X=1,\ pX=Xp=0\}.
\tag{XIII164.12}
$$

These entire balls vary continuously with $p$.
Indeed, if rank-one $p_j\to p$ and $X\in D_p$, then
$(I-p_j)X(I-p_j)/\operatorname{Tr}((I-p_j)X(I-p_j))$ belongs to $D_{p_j}$ for large $j$
and converges uniformly to $X$ over the compact $D_p$, since the denominator converges uniformly to one.
Conversely, every cluster point of $X_j\in D_{p_j}$ belongs to $D_p$ by positivity, trace normalization and $p_jX_j=0$.
Compactness then gives Hausdorff convergence.
A linear cone-and-unit isomorphism transfers this continuity to the same original $P$, proving the first condition implies the second.
This qutrit computation has both $I$ and $p$ in $F_p$; it does not identify the entire menu with its least member.

If $\Sigma=\varnothing$, no $Z$-collapse to a singleton can occur by Theorem 163.2, so no displayed synchronized pair exists.
Conversely, any specified point of nonempty $\Sigma$ produces such a pair by Corollaries 163.3 and 164.3.
This proves equivalence of the second and third conditions.
Finally, if the static representation fails, Theorem 160.6, (XIII160.14)–(XIII160.15), supplies an actual $Z$-collapse
with a singular root; Corollary 164.3 produces the displayed synchronized pair.
Thus the third condition implies the first.

These implications reduce the static endpoint to excluding the specified actual configuration.
They establish neither its exclusion from the original axioms nor a faithful original realization of it.
Symmetry of $\mathcal C_Z$ supplies the reversed ordered pair; no third endpoint or inconsistency follows from symmetry alone.
The whole mixed domain is used in the zero-face argument of Theorem 164.2.
No premise here asserts global label injectivity, all-pair proper faces, an ambient dimension upper bound,
a uniform positive-extension budget, positivity of a signed restriction inverse, affine $T_p$ on all $K$,
a least original confirmer, filters, a Jordan carrier or composites.
Physical dynamics, time and $\hbar$ are outside (XIII164.11).证毕。

Attached mathematical sources and boundaries for 164.1–164.5 are as follows.
The correspondence from (XIII163.11) and the actual neighboring whole-face confirmers to the fixed-threshold uniform
return estimate (XIII164.3) is `repo-derived`. The synchronized pair, the relation (XIII164.7) and the static reduction
are consequences of that estimate and the cited suppliers, not separate classifications.
Compact subsequence extraction, joint evaluation, the elementary face property of an affine ball and diagonal selection
are intermediate finite-dimensional arguments within these proofs.
The singleton-zero effect itself retains [X126.3, (X126.10)][X164] as an antecedent.

For comparison, [G. Niestegge, *Quantum transition probability*, §3, property $(**)$ and Theorem 1][N164]
defines $e_\omega(\zeta)$ by an infimum over all nonnegative continuous affine $a$ with $a(\omega)=1$,
without requiring $a\le1$. This larger menu differs from the original interval $[0,u]$ in (XIII164.1);
the source additionally requires the infimum to be affine in property $(**)$. Neither that property nor an identification
of the two infima is supplied here. No projectivity assumption or conclusion is imported through this comparison.

[N. P. Landsman, *Poisson spaces with a transition probability*, §1.3, (1.4)–(1.5)][L164]
uses the bounded menu $0\le f\le1$; in finite dimension its affine functions on $K$ homogenize to the original effects,
and its notation is $p(\rho,\sigma)=T_\sigma(\rho)$ on pure inputs.
This agrees with the original upper unit bound, in contrast to Niestegge's larger menu above.
Landsman's §1.2 explicitly assumes projective norm-exposed faces in AHS1, including an affine retraction with
transversality, and actual pair-ball faces in AHS2; those requirements are not consequences asserted here.
The well-behaved transition-space conditions of §1.3, (1.10)–(1.11), likewise include basis requirements beyond pure PR.
Accordingly neither reconstruction route settles (XIII164.11) from the original EB3+PR premises.
These references locate the definitions and their different assumptions; the correspondence above carries no global priority
or exhaustive literature claim.

[IX164]: https://github.com/the-omega-institute/trureturing/blob/a3338a34598246b3d4c93b249042a6c8172d1186/docs/develop/theory/QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX114.3–114.4 and (IX114.13): pure exposure, compact P and fixed-row continuity; IX115.3: inverse-budget diameter inequality in its proof; IX115.4 and (IX115.9): closed zero graph and one-sided upper semicontinuity."
[X164]: https://github.com/the-omega-institute/trureturing/blob/a3338a34598246b3d4c93b249042a6c8172d1186/docs/develop/theory/QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_X.md "X126.3, (X126.10): an original effect confirming the landing point and having the limiting label as its entire singleton zero face."
[XII164]: https://github.com/the-omega-institute/trureturing/blob/a3338a34598246b3d4c93b249042a6c8172d1186/docs/develop/theory/QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XII.md "Dimension-free XII147.2, (XII147.4): local singleton-label whole-face confirmation and equality of signed restriction kernel dimensions along actual zero edges."
[N164]: https://arxiv.org/html/2312.13213v2#S3 "G. Niestegge, Quantum transition probability, §3, property (**) and Theorem 1; no upper unit bound in the defining infimum."
[L164]: https://arxiv.org/html/quant-ph/9603005v2#S1.SS2 "N. P. Landsman, Poisson spaces with a transition probability, §§1.2–1.3, AHS1–AHS2 and (1.4)–(1.11); projectivity, pair-ball and basis requirements retain their own assumptions."

## 追加锚（本行以下为增补区）

## 165. Closed unit-budget zero-redundancy locus and original exterior effects

**定义 165.1（Complete original domain and the stronger seed）。** Let $V\ne0$ be a finite-dimensional real vector space,
$C\subset V$ a closed pointed generating convex cone, and $u\in V^*$ strictly positive on $C\setminus\{0\}$.
Retain the entire original objects

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad
\mathcal E=[0,u]_{C^*},\\
F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(x)=\min_{f\in F_p}f(x)\quad(p\in P,\ x\in K),\\
D_p=\{x\in K:T_p(x)=0\},\qquad S_p=P\cap D_p.
\end{gathered}
\tag{XIII165.1}
$$

Every minimum in (XIII165.1) is attained on the full original menu at every original mixed input.
Assume complete EB3: every entire $D_p$ is affinely isomorphic to a nondegenerate closed Euclidean three-ball.
Assume pure PR, $T_p(q)=T_q(p)$ only for $p,q\in P$.
Use the singleton-label locus, original normal cones, signed restriction and whole-face confirmer sets

$$
\begin{gathered}
P_{\rm s}=\{p\in P:\ \forall q\in P,\ D_q=D_p\Longrightarrow q=p\},\\
N_p=\{h\in C^*:h(p)=0\},\qquad L_p=\operatorname{span}_{\mathbb R}N_p,\qquad
R_p:L_p\longrightarrow\operatorname{Aff}(D_p),\quad R_ph=h|_{D_p},\\
\mathcal A_p=\{f\in F_p:f|_{D_p}=0\},\qquad
a(p)=\dim\ker R_p\quad(p\in P_{\rm s}),\\
\beta_F=\left(\max_{q,r\in P\cap F}(1-T_q(r))\right)^{-1},\qquad
A=\{p\in P_{\rm s}:a(p)=0,\ \beta_{D_p}=1\}.
\end{gathered}
\tag{XIII165.2}
$$

Here $\operatorname{Aff}(D_p)$ has dimension four.
The integer $a(p)$ is the redundancy of signed restriction, distinct from any ball contrast coefficient.
The budget $\beta_F\in[1,\infty)$ has its original positive-extension meaning from (XIII160.5).
For $p\in A$, let $e_p$ be the unique member of $\mathcal A_p$; this uniqueness follows from
[dimension-free XII147.2][XII165], not from an ambient dimension bound.
The whole $F_p$ still contains $u$ and is not identified with $\mathcal A_p$.

Fix an auxiliary Euclidean norm on $V$, its dual norm, and
$L=\max_{f\in\mathcal E}\|f\|_*>0$.
The original suppliers [IX114.2–114.6 and IX115.4–115.6][IX165] give compact $K,P,\mathcal E$,
$K=\operatorname{conv}P$, $C=\mathbb R_{\ge0}K$, the pure sphere $S_p=\partial_{\rm rel}D_p$,
the closed zero graph, lower semicontinuity of $\beta_{D_p}$, and the whole-ball limit dichotomy:
if $p_i\to p$ and $D_{p_i}$ has a Hausdorff limit, that limit is either $D_p$ or a singleton in $S_p$.
Each fixed row $T_p:K\to[0,1]$ is $L$-Lipschitz.
Indeed, every effect in the same compact menu has this Lipschitz bound, so their minimum has it.
No continuity of the whole-ball map on all $P$ is assumed.

A stronger seed means an actual original $p_0\in A$.
When it is supplied, define

$$
Q=\Gamma(p_0)=
\{p_n:\ n\ge0,\ p_0,p_1,\ldots,p_n\in P,\ p_{j+1}\in S_{p_j}\ (0\le j<n)\},
\qquad M=\overline Q^{\,P}.
\tag{XIII165.3}
$$

Every path is finite and uses actual original zero edges.
Neither existence of a stronger seed nor zero redundancy from bare unit budget is part of this definition.

**定理 165.2（Closed original least-confirmation locus）。** Under Definition 165.1, $A$ is closed in $P$, hence compact,
and $p\in A$ implies $S_p\subseteq A$. Every $p\in A$ satisfies

$$
e_p\le_{C^*}f\quad(f\in F_p),\qquad
T_p(x)=e_p(x)\quad(x\in K).
\tag{XIII165.4}
$$

The effect map $p\mapsto e_p$ is Lipschitz on $A$ in the fixed ambient norms.
The entire-ball map $p\mapsto D_p$ is Hausdorff continuous relative to $A$;
moreover, if $p_i\in A$ tends to $p\in A$, every $q\in S_p$ has actual approximants $q_i\in S_{p_i}$ with $q_i\to q$.
These assertions concern the relative domain $A$, which may be empty.

证明。We first recall and apply the local normal calculation, including its exact assumptions.
At any singleton $p$ with $a(p)=0$, [XII147.2][XII165] supplies the restriction isomorphism $R_p$,
$\dim L_p=4$, the unique $e_p\in\mathcal A_p$, and

$$
\{e_p=0\}\cap K=D_p,\qquad
\{e_p=1\}\cap K=\{p\},\qquad
g_p:=u-e_p\in\operatorname{ri}N_p,\qquad
\{g_p=0\}\cap K=\{p\}.
\tag{XIII165.5}
$$

For completeness, its constant-one slice meets $\operatorname{ri}N_p$ and is
$\{g\in N_p:g|_{D_p}=1\}=u-\mathcal A_p$.
Thus the zero-dimensional slice identifies that relative-interior representative with $g_p$.
Every actual $q\in S_p$ is singleton and has $a(q)=a(p)$, so its whole-face confirmer is also unique.
For every $h\in N_p$ the original positive-annihilator maximum identity is

$$
\max_Kh=\max_{D_p}h.
\tag{XIII165.6}
$$

One direct justification is to choose a pure global maximizer $s$ of a nonzero $h\ge0$.
Its maximum $b$ is positive because $P$ spans $V$; $h/b$ is an original effect with values one at $s$ and zero at $p$.
The complement effect gives $s\in D_p$.
The zero functional is immediate.
This is also the identity supplied by
[SingleLabelNormalBody.positive_annihilator_maximum][Max165];
it requires neither singleton status nor a global injectivity hypothesis.

Write $D_p=c_p+B_p\overline B^3$, with $B_p:\mathbb R^3\to\ker u$ injective.
The components of the unique linear map $H_p:V\to\mathbb R^3$ belong to $L_p$ and satisfy
$H_p(c_p+B_pz)=z$.
Thus $H_p(p)=0$, and every $h\in L_p$ is uniquely $\alpha g_p+v\cdot H_p$.
The local calculation (XIII163.6)–(XIII163.9), using precisely the preceding singleton and zero-redundancy interfaces, gives

$$
\begin{gathered}
\rho_p(v)=\sup_{x\in K\setminus\{p\}}
\frac{-v\cdot H_p(x)}{g_p(x)}\ge\|v\|,\\
N_p=\{\alpha g_p+v\cdot H_p:\alpha\ge\rho_p(v)\},\\
q_t=c_p+B_pt,\quad \|t\|=1
\quad\Longrightarrow\quad
e_{q_t}=\frac{\rho_p(t)g_p+t\cdot H_p}{1+\rho_p(t)}
\quad\hbox{on }V.
\end{gathered}
\tag{XIII165.7}
$$

The supremum is finite: relative interior gives some $\varepsilon>0$ with
$g_p\pm\varepsilon(H_p)_j\in N_p$ for each component, bounding $\|H_p(x)\|/g_p(x)$ uniformly off $p$.
The lower bound follows by evaluation at the opposite sphere point.
To see the last formula without a positivity assumption on $R_p^{-1}$,
the actual zero edge gives $p\in D_{q_t}$, so $e_{q_t}\in N_p$; its restriction is $1-\theta+\theta t\cdot z$ with $0<\theta\le1/2$,
by ball support and its singleton top face.
Positivity gives $(1-\theta)/\theta\ge\rho_p(t)$.
Choose $y\in D_{q_t}\setminus\{p\}$; whole-face vanishing at $y$ and $g_p(y)>0$ give the reverse inequality.
This proves (XIII165.7) on the entire original $V$.

Now take $p\in A$.
Unit budget gives actual antipodal orthogonality $q_t\perp q_{-t}$ by the same-ball comparison formula
[IX114.5–114.8][IX165].
Consequently $e_{q_t}(q_{-t})=0$, and (XIII165.7) gives $\rho_p(t)=1$ separately for every unit $t$.
Positive homogeneity then gives $\rho_p(v)=\|v\|$ for all $v$.
In particular the reused saturation identities are

$$
\begin{gathered}
N_p=\{\alpha g_p+v\cdot H_p:\alpha\ge\|v\|\},\qquad
\|H_p(x)\|\le g_p(x)\quad(x\in C),\\
e_{q_t}=\tfrac12(g_p+t\cdot H_p),\qquad
e_{q_t}+e_{q_{-t}}=g_p,\\
h=\alpha g_p+v\cdot H_p\in N_p
\quad\Longrightarrow\quad \max_Kh=\alpha+\|v\|.
\end{gathered}
\tag{XIII165.8}
$$

The last equality applies (XIII165.6) only after positivity is established.
These are the local consequences underlying (XII157.17)–(XII157.18);
the dimension-dependent capture step of XII157 is not used.

For any $f\in F_p$, set $h=u-f\in N_p\cap\mathcal E$.
Write $h=\alpha g_p+v\cdot H_p$.
Then $\alpha\ge\|v\|$ and $\alpha+\|v\|\le1$ by (XIII165.8).
On the original $C$,

$$
h(x)\le(\alpha+\|v\|)g_p(x)\le g_p(x).
$$

Thus $f\ge e_p$ on $C$. Since $e_p\in F_p$, the attained minimum on every original mixed input equals $e_p$.
This proves (XIII165.4), using the full menu rather than only the whole-face slice.

Actual neighbor closure already follows from the local suppliers.
If $q=q_t\in S_p$ for $p\in A$, XII147.2 gives $q\in P_{\rm s}$ and $a(q)=0$.
The actual $r=q_{-t}$ is orthogonal to both $p$ and $q$.
Thus the whole $D_q$ contains the two distinct original pure points $p,r$ with $T_p(r)=0$;
its same-ball comparison formula forces its contrast to be $1/2$, hence $\beta_{D_q}=1$.
Therefore $q\in A$.
This is the edge propagation in IX114.8 with the actual common neighbor exhibited.

To prove closedness, take $p_i\in A$ with $p_i\to p\in P$.
Compactness of $\mathcal E$ supplies a subsequence $e_{p_i}\to e\in\mathcal E$.
Joint evaluation gives $e(p)=1$.
For every fixed original pure $x$, (XIII165.4), pure PR and fixed-row continuity give

$$
e(x)=\lim_i e_{p_i}(x)
=\lim_i T_{p_i}(x)=\lim_i T_x(p_i)=T_x(p)=T_p(x).
\tag{XIII165.9}
$$

The same chosen effect limit works for all pure $x$; no exchange at a mixed endpoint occurs.
For every $f\in F_p$, (XIII165.9) gives $f-e\ge0$ on $P$.
Convex generation and positive scaling extend this inequality to $K$ and $C$.
Thus $e$ is least in $F_p$, $T_p=e$ on all $K$, and $e\in\mathcal A_p$.

Lower semicontinuity of the original budget gives
$1\le\beta_{D_p}\le\liminf_i\beta_{D_{p_i}}=1$.
This unit-budget ball has a singleton label.
Indeed, if $D_p=F$ were repeated, [IX116.2][IX165] gives a disjoint partner $G$ with
$D_q=G$ for every $q\in P\cap F$.
Unit-budget antipodes $q,r\in P\cap F$ satisfy $r\in D_q=G$, contradicting $F\cap G=\varnothing$.
For any $f\in\mathcal A_p$, the already proved least property makes $h=f-e$ positive on $C$;
it vanishes at $p$ and on all $D_p$.
Identity (XIII165.6) forces $h=0$.
Hence $\mathcal A_p=\{e\}$ and XII147.2 gives $a(p)=\dim_{\rm aff}\mathcal A_p=0$.
Therefore $p\in A$, proving closedness and compactness.

For the quantitative effect continuity, choose an original pure basis $x_1,\ldots,x_d$ of $V$;
$d=\dim V$ is arbitrary finite.
There is $c_{\mathcal B}>0$ with
$\|h\|_*\le c_{\mathcal B}\max_j|h(x_j)|$ for every $h\in V^*$.
For $p,q\in A$, pure PR and the fixed-row bound give

$$
\begin{aligned}
|e_p(x_j)-e_q(x_j)|
&=|T_{x_j}(p)-T_{x_j}(q)|\le L\|p-q\|,\\
\|e_p-e_q\|_*&\le c_{\mathcal B}L\|p-q\|.
\end{aligned}
\tag{XIII165.10}
$$

For the relative whole-ball continuity, antipodal $q_\pm=c_p\pm B_pt$ satisfy
$e_{q_+}(q_+)=1$ and $e_{q_+}(q_-)=0$.
Thus every unit $t$ and every $p\in A$ satisfy

$$
1\le L\|q_+-q_-\|=2L\|B_pt\|,\qquad
\min_{\|t\|=1}\|B_pt\|\ge\frac1{2L}.
\tag{XIII165.11}
$$

For $p_i\in A$ tending to $p\in A$, compactness of the nonempty-compact hyperspace of $K$
provides a Hausdorff convergent further subsequence of any subsequence of $D_{p_i}$.
Bound (XIII165.11) excludes a singleton limit.
The original limit dichotomy therefore identifies every such limit with $D_p$.
Hence the whole sequence tends to $D_p$.

We also need approximation by actual sphere points.
The charts $D_{p_i}=c_i+B_i\overline B^3$ have bounded centers and operators because all their images lie in $K$.
On any subsequence choose a further one with $c_i\to c$ and $B_i\to B$.
Bound (XIII165.11) keeps $B$ injective, and Hausdorff convergence gives $D_p=c+B\overline B^3$.
For any fixed $q\in S_p$ there is a unit $t$ with $q=c+Bt$.
Then the actual pure $c_i+B_it\in S_{p_i}$ tends to $q$ on this further subsequence.
If $\operatorname{dist}(q,S_{p_i})$ failed to tend to zero, the same extraction on a separated subsequence would contradict it.
Choosing nearest points in the compact $S_{p_i}$ proves the asserted $q_i\to q$.
This proves only continuity relative to $A$, not global regularity of its points.证毕。

**定理 165.3（Seed closure and the simultaneous strict-interior alternative）。** Suppose an actual stronger seed
$p_0\in A$ is supplied and define $Q,M$ by (XIII165.3).
Then $M$ is nonempty compact, $Q\subseteq M\subseteq A$, and

$$
p\in M\quad\Longrightarrow\quad S_p\subseteq M.
\tag{XIII165.12}
$$

For each $p\in A$, use the actual whole-ball coordinates of (XIII165.7)–(XIII165.8).
On the same original $V$ define the linear map

$$
\Pi_p(x)=g_p(x)c_p+B_pH_p(x).
\tag{XIII165.13}
$$

It is positive on the original $C$, has rank four, and satisfies

$$
\begin{gathered}
\Pi_p^2=\Pi_p,\qquad \Pi_p|_{\operatorname{span}D_p}=\operatorname{id},\qquad
\Pi_p(p)=0,\qquad u\circ\Pi_p=u-e_p,\\
\Pi_p(C)=\operatorname{cone}D_p,\qquad C\cap\ker\Pi_p=\mathbb R_{\ge0}p.
\end{gathered}
\tag{XIII165.14}
$$

If $M\ne P$, then for every original pure $x\in P\setminus M$ the attained quantity

$$
m_M(x)=\min_{p\in M}e_p(x)
\tag{XIII165.15}
$$

is strictly positive, and for every $p\in M$,

$$
g_p(x)-\|H_p(x)\|\ge2m_M(x)>0,\qquad
\frac{\Pi_p(x)}{g_p(x)}\in\operatorname{ri}D_p\subset K\setminus P.
\tag{XIII165.16}
$$

Thus all these original positive projections send the same exterior pure input to strictly mixed normalized outputs.

证明。The zero-length path puts $p_0\in Q$.
The neighbor closure of $A$ in Theorem 165.2 propagates along every finite path, so $Q\subseteq A$.
Since $A$ is closed, $M\subseteq A$; compactness follows from compact $P$.
For $p\in M$ choose $p_i\in Q$ tending to $p$.
Given any $q\in S_p$, relative continuity from Theorem 165.2 supplies $q_i\in S_{p_i}$ with $q_i\to q$.
Each $q_i$ belongs to $Q$ by appending its actual edge.
Therefore $q\in M$, proving (XIII165.12).
A closed zero graph alone would give the opposite direction of this limiting implication;
the sphere approximation supplies the required direction here.

The projection calculation uses only (XIII165.8).
For $z\in\overline B^3$, $g_p(c_p+B_pz)=1$ and $H_p(c_p+B_pz)=z$,
so $\Pi_p$ fixes the entire $D_p$.
Its range is contained in $\operatorname{span}D_p$ and contains that span, which has dimension four.
This proves its rank, idempotence and restriction identity.
Also $g_p(p)=H_p(p)=0$, $u(c_p)=1$ and $uB_p=0$, proving $\Pi_p(p)=0$ and $u\Pi_p=g_p$.
For $x\in C$ with $g_p(x)>0$, the established inequality $\|H_p(x)\|\le g_p(x)$ gives

$$
\Pi_p(x)=g_p(x)\left(c_p+B_p\frac{H_p(x)}{g_p(x)}\right)\in\operatorname{cone}D_p.
$$

If $g_p(x)=0$, the same inequality gives $H_p(x)=0$ and $\Pi_p(x)=0$.
Thus positivity is derived on the whole original cone.
Conversely $\Pi_p$ fixes $D_p$, giving its stated positive image.
If $x\in C\setminus\{0\}$ is in the kernel, then $g_p(x)=u\Pi_p(x)=0$;
normalizing by the original strictly positive $u(x)$ and using (XIII165.5) puts $x$ on the ray of $p$.
The converse inclusion is already proved.

Now let $x\in P\setminus M$.
For every $p\in M$, $e_p(x)=0$ would put $x\in S_p\subseteq M$, a contradiction.
Effect continuity on compact $M$ makes the minimum (XIII165.15) attained and positive.
Every actual $q_t=c_p+B_pt$ belongs to $M$ by (XIII165.12), so (XIII165.8) gives

$$
\frac{g_p(x)-\|H_p(x)\|}{2}
=\min_{\|t\|=1}e_{q_t}(x)\ge m_M(x).
\tag{XIII165.17}
$$

In particular $g_p(x)>0$, and division puts the normalized projection strictly inside the actual ball.
The relative interior of this proper ball face contains no original pure point.
This proves (XIII165.16) simultaneously for every $p\in M$, with the same fixed $x$.证毕。

The identities used for (XIII165.13)–(XIII165.14) are local saturation and linear projection consequences;
positivity here is a mathematical property of an original linear map.
It supplies neither a physically available filter nor preservation of purity.
For comparison, [Barnum, Müller and Ududec, Theorem 16][BMU165] assumes finite-dimensional projectivity,
symmetric transition probabilities and purity preservation by filters to obtain a formally real Jordan state space.
Its projectivity is global and its purity condition is additional.
Neither is supplied by projections indexed only by $A$; (XIII165.16) specifies their strict mixed-output alternative
if an exterior pure point exists.

**定理 165.4（An original exterior effect and the missed original maximum）。** Under Theorem 165.3, if $M\ne P$,
then for every original pure $x\in P\setminus M$ there are an original $f\in F_x$
and an original pure $y\in S_x\setminus M$ such that

$$
\begin{gathered}
\min_K f=f(y)=0,\qquad f(p)\ge e_p(x)\ge m_M(x)\quad(p\in M),\\
(f-\lambda e_p)(y)<0\quad(p\in M,\ \lambda>0),\\
\max_M f<\max_K f=1.
\end{gathered}
\tag{XIII165.18}
$$

In particular $f\notin\operatorname{cone}\{e_p:p\in M\}$, where the cone uses finite nonnegative sums.
No positive multiple of any one of these original least rays can be subtracted from $f$ while preserving positivity on $C$.

证明。Choose any $p_*\in M$.
Original attainment on the full $F_x$ at the input $p_*$ supplies $f\in F_x$ with

$$
f(p_*)=T_x(p_*)=T_{p_*}(x)=e_{p_*}(x)<1.
\tag{XIII165.19}
$$

The exchange is between the original pure endpoints $x,p_*$.
The strict inequality follows from $x\ne p_*$ and the singleton top face of $e_{p_*}$.

Put $b=\min_K f$, attained by compactness, so $0\le b\le f(p_*)<1$.
If $b>0$, the linear functional

$$
f'=\frac{f-bu}{1-b}
$$

is an original effect: on the full $K$ it has values in $[0,1]$, hence the same order bounds hold on $C$.
Also $f'(x)=1$, so $f'\in F_x$.
But

$$
f'(p_*)-f(p_*)=\frac{b(f(p_*)-1)}{1-b}<0,
$$

contradicting the original minimum in (XIII165.19).
Thus $b=0$.
The nonempty compact zero face $K\cap\ker f$ has an extreme point $y$.
Because it is a face of the original $K$, this $y$ belongs to the original $P$.
Since $f\in F_x$ and $f(y)=0$, $y\in S_x$.
This extraction uses original attainment and compact convex generation, with no affine-$T$ assumption.

For every $p\in M$, the definition of the same original menu, pure PR and (XIII165.4) give

$$
f(p)\ge T_x(p)=T_p(x)=e_p(x)\ge m_M(x)>0.
\tag{XIII165.20}
$$

In particular $y\notin M$.
Equivalently, if $y$ belonged to $M$, its actual zero neighbor $x$ would belong to $M$ by (XIII165.12).
For every $p\in M$, (XIII165.5) and neighbor closure now give $e_p(y)>0$.
Consequently

$$
(f-\lambda e_p)(y)=-\lambda e_p(y)<0\qquad(\lambda>0).
$$

Every nonzero finite nonnegative combination of the $e_p$ likewise has strictly positive value at this same $y$,
whereas $f(y)=0$; and $f\ne0$ because $f(x)=1$.
This proves the cone and subtraction assertions.

Finally, if $f(p)=1$ at any $p\in M$, then $f\in F_p$ and original least confirmation yields
$e_p\le_{C^*}f$.
Evaluation at $y$ contradicts $e_p(y)>0=f(y)$.
Thus $f(p)<1$ for every $p\in M$.
Compactness of $M$ gives $\max_Mf<1$, while $f(x)=1$ and $f\le u$ give $\max_Kf=1$.
This proves every part of (XIII165.18).证毕。

The closedness of $A$, the relative passage from finite zero paths to (XIII165.12), and the original exterior
certificate (XIII165.18) are repo-derived deductions from the stated original interfaces.
The local normal identities, antipodal saturation and least calculation reuse
[XII147.2 and (XII157.17)–(XII157.18)][XII165] and (XIII163.5)–(XIII163.9);
compact subsequence extraction and finite-dimensional convex generation are intermediate standard arguments.
The zero-minimum rescaling also appears in the original full-menu argument of
[CommonOldExclusionConfirmation, minimizer_has_zero][Menu165].

The positive-dual generation argument of [LeastConfirmationGeneration][Generation165] uses least confirmation
and maximum attainment on its entire chosen probe and positivity domain.
For the original order and a proposed ray family indexed by $M$, a maximum attained somewhere in $M$
must be an original global maximum, not merely a maximum of the restriction.
Equation (XIII165.18) gives an original positive effect for which precisely that original-maximum premise fails
if $M$ is proper.
Testing positivity only on $M$ instead would replace the original order interval by one tested only on $M$;
(XIII165.4) establishes no least property for that interval.
Thus no original positive-dual generation over $M$ follows from compactness and local least confirmation alone.

[Landsman, §§1.2–1.3][L165] uses the bounded affine menu $0\le f\le1$ for transition probability;
under finite-dimensional homogenization its $p(\rho,\sigma)$ corresponds to $T_\sigma(\rho)$ here.
His AHS1 requires every norm-exposed face to be projective, and AHS2 requires the whole face of every equivalent
distinct pure pair to be the complex qubit ball.
The well-behaved transition-space conditions further impose basis requirements on orthoclosed subsets.
These are additional global interfaces, not consequences asserted by (XIII165.12).
The cited results supply comparisons and intermediate sources, not a priority claim for the present deductions.

No dimension upper bound, global label injectivity, actual all-pair L2, Hit, TC, global least confirmation,
positive restriction inverse at other labels, uniform budget on all $P$, Jordan or matrix carrier,
physical filter, composite or dynamical assumption is used.
The signed rank-four restriction at labels of $A$ asserts no persistence of positive generators along sequences outside $A$.
The relative continuity proved here does not put $M$ in the globally regular locus.
Neither $Q=M$ nor $M=P$ is established.
A proper $M$ is neither excluded nor realized, and existence of a stronger seed is not proved.
In particular a bare unit-budget seed does not supply the zero-redundancy step needed to enter $A$.
The same-original full qutrit reconstruction, a faithful complete original countermodel,
and exclusion or realization of the synchronized-collapse alternative in (XIII164.11) remain unresolved.

[IX165]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX114.2–114.6: original faces, compact pure locus, full-menu row bounds and ball comparison; IX114.8: actual zero triangles and unit budget; IX115.4–115.6: closed zero graph, whole-ball limit dichotomy and budget semicontinuity; IX116.2: repeated-pair alternative."
[XII165]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XII.md "Dimension-free XII147.2: singleton neighbors, redundancy, whole-face slices and original positive maxima; XII157.17–XII157.18: local antipodal evaluation, without importing the chapter's dimension-dependent capture theorem."
[Max165]: ../../../D5/S3/Quantum/Foundation/SingleLabelNormalBody.lean "positive_annihilator_maximum: original positive-annihilator maximum, without EB or label injectivity."
[Menu165]: ../../../D5/S3/Quantum/Foundation/CommonOldExclusionConfirmation.lean "Full original confirmer compactness and fixed-row bounds; private minimizer_has_zero: original minimum rescaling."
[Generation165]: ../../../D5/S3/Quantum/Foundation/LeastConfirmationGeneration.lean "ConfirmationSystem.least and maximum; positive_dual_generation consumes the full chosen positivity domain."
[BMU165]: https://arxiv.org/html/1403.4147v4 "H. Barnum, M. P. Müller and C. Ududec, Higher-order interference and single-system postulates characterizing quantum theory, Theorem 16: projectivity, symmetric transition probabilities and purity-preserving filters."
[L165]: https://arxiv.org/html/quant-ph/9603005v2 "N. P. Landsman, Poisson spaces with a transition probability, §§1.2–1.3: AHS1–AHS2, bounded transition menu and orthoclosed-subset basis conditions."

## 追加锚（本行以下为增补区）
