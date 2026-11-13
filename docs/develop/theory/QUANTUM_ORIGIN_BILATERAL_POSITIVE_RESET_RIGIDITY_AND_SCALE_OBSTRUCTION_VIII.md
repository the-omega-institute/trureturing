# Quantum origin: whole PSD projections and intrinsic symmetry lifts VIII

## 109. Same-carrier projection data and conditional rigidity

**Definition 109.1 (Whole PSD projection datum).** Fix $n\ge2$. Let
$V$ be a finite-dimensional real vector space, $C\subset V$ a closed,
pointed, generating convex cone, and $u\in V^*$ strictly positive on
$C\setminus\{0\}$. Retain the entire original objects

$$
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad E=[0,u]_{C^*}.
\tag{109.1}
$$

Write $\operatorname{Herm}_n(\mathbb C)$ for the real space of Hermitian
matrices, $\operatorname{PSD}_n$ for its positive cone, and

$$
\mathcal D_n=\{\rho\ge0:\operatorname{Tr}\rho=1\},\qquad
\mathcal R_n=\{Q\in\mathcal D_n:\operatorname{rank}Q=1\}.
\tag{109.2}
$$

The additional projection data are a surjective real-linear map $\pi$
and the following whole-domain identities:

$$
\begin{aligned}
\pi &: \operatorname{Herm}_n(\mathbb C)\longrightarrow V,\qquad
N=\ker\pi,\\
\pi(\operatorname{PSD}_n)&=C,\qquad
u(\pi(X))=\operatorname{Tr}X
\quad(X\in\operatorname{Herm}_n(\mathbb C)),\\
b=\pi|_{\mathcal R_n}&:\mathcal R_n\overset{\sim}{\longrightarrow}P.
\end{aligned}
\tag{109.3}
$$

In particular $b$ is bijective onto **all** original pure points.
For every distinct $p,q\in P$, let $F_K(p,q)$ be their entire actual
minimal face in $K$. Assume

$$
\dim_{\mathrm{aff}}F_K(p,q)\le3\qquad(p\ne q\in P).
\tag{109.4}
$$

The stronger L3 condition that every such face is affinely isomorphic
to the whole closed real three-ball implies (109.4). No assertion that
a linear image of a source face is a face is included in the datum.
No selected pure orbit, generic pair, section, or restricted set of
positive preimages can replace a whole-domain clause of (109.3)–(109.4).

For the original prediction specialization, $V,C,u,K,P,E$ are exactly
those of [VI, Definition 89.2][VI]: the same $\Omega$, original legal
words, normalization column, and complete original terminal-future or
future-outcome coordinates. Nothing here replaces that carrier by a
quotient of selected predictions. Its original compact-continuation
frontend is [OriginalProbabilityCompactAction][Compact], under that
frontend's full-row, reversibility, prefix and normalization premises.
Neither frontend supplies (109.3) or (109.4).

**Theorem 109.2 (Projected-PSD rigidity with a supplied unitary group).**
Assume Definition 109.1. Suppose a compact subgroup $G\le U(n)$ acts
transitively on all $\mathcal R_n$ by conjugation and preserves $N$:

$$
gNg^*=N\qquad(g\in G).
\tag{109.5}
$$

Then $N=0$. The inverse $\Phi=\pi^{-1}$ is a real-linear bijection on
the same entire original carrier, with

$$
\Phi(C)=\operatorname{PSD}_n,\qquad
\operatorname{Tr}\Phi(x)=u(x)\quad(x\in V).
\tag{109.6}
$$

For $2\le n\le5$, the same conclusion follows from Definition 109.1
without any group hypothesis. The dimension bound (109.4) itself forces
the full three-ball shape of every actual pair face. No independence
or minimality claim for these premises is made. Sections 110–114 give
the proof.

**Theorem 109.3 (Rigidity from the original compact pure action).** Assume
Definition 109.1. In place of (109.5) and its supplied $G$, suppose an
actual compact matrix subgroup

$$
H\le\operatorname{Aut}(C,u)
=\{h\in GL(V):hC=C,\ u\circ h=u\}
\tag{109.7}
$$

is transitive on the entire original $P$. Then (109.6) holds.
The proof constructs the compact unitary group needed by Theorem 109.2
over $H^0$, without choosing phases for individual symmetries.
The full $H$ has unitary or antiunitary implementers and need not have
only unitary ones. Sections 115–119 prove this statement and the exact
extension assertions.

Connectedness of $H$, Hilbert or Born structure on $V$, spectrality of
$C$, least confirmation, the full S bridge, $\mathrm{Pair}_{\perp}$,
and bit, frame or strong symmetry are not additional hypotheses of
Theorem 109.3. The whole PSD source in (109.3) is an explicit supplied
representation hypothesis; this theorem does not derive it from bare
AURIC, EB3, L3 or original word readouts.

## 110. Two-dimensional supports and actual minimal faces

For a complex subspace $S\subset\mathbb C^n$, write
$\operatorname{Herm}(S)$ for the entire real space of Hermitian matrices
supported on $S$, extended by zero on $S^\perp$, and
$\mathcal D(S)=\mathcal D_n\cap\operatorname{Herm}(S)$.
Write $I_S$ for the orthogonal projection onto $S$.

**Lemma 110.1 (Whole base and injective two-support restrictions).**
Under Definition 109.1,

$$
K=\pi(\mathcal D_n),\qquad
N\subset\{X:\operatorname{Tr}X=0\}.
\tag{110.1}
$$

For every complex two-plane $S$, $\pi$ is injective on all
$\operatorname{Herm}(S)$. Consequently $L_S=\pi(\mathcal D(S))$ is
a solid affine three-dimensional ellipsoid, and every point of its
relative boundary is globally pure in $K$.

Proof. A positive preimage of $x\in K$ has trace $u(x)=1$, and every
$\rho\in\mathcal D_n$ maps into $K$. Applying the trace identity to
a kernel matrix proves the second claim in (110.1).

If $0\ne A\in N\cap\operatorname{Herm}(S)$, its two eigenvalues on
$S$ sum to zero, so $A=\lambda(Q-R)$ for some $\lambda>0$ and
orthogonal rank-one projectors $Q,R$ supported on $S$. Then
$b(Q)=b(R)$, contrary to injectivity of $b$. This proves injectivity
on the whole supported Hermitian space, including its trace direction.

The two-dimensional complex density body is a solid three-ball in
its trace-one affine hyperplane. Its boundary consists exactly of
rank-one projectors. The injective affine restriction of $\pi$ gives
the stated ellipsoid, and (109.3) sends each of those boundary
projectors to a global extreme point of $K$. ∎

**Proposition 110.2 (Equality with the entire actual pair face).**
For any distinct $Q,R\in\mathcal R_n$, put
$S=\operatorname{ran}Q+\operatorname{ran}R$. Then

$$
F_K(b(Q),b(R))=\pi(\mathcal D(S))=L_S.
\tag{110.2}
$$

In particular this actual minimal face has affine dimension exactly
three and is affinely isomorphic to the whole closed real three-ball.

Proof. The state $m=(Q+R)/2$ is positive definite on the two-plane
$S$. Every $\sigma\in\mathcal D(S)$ occurs in a convex decomposition

$$
m=t\sigma+(1-t)\tau,\qquad
0<t<1,\quad\tau\in\mathcal D(S).
\tag{110.3}
$$

Indeed choose $t>0$ small enough that $m-t\sigma\ge0$ on $S$ and set
$\tau=(m-t\sigma)/(1-t)$. Its trace is one. The actual face
$F=F_K(b(Q),b(R))$ contains $\pi(m)$. Applying its face property to
the image of (110.3) gives $L_S\subset F$.

Lemma 110.1 gives $\dim_{\mathrm{aff}}L_S=3$; (109.4) therefore gives
$\operatorname{aff}F=\operatorname{aff}L_S$. If $z\in F\setminus L_S$,
the segment from the center $c$ of the solid ellipsoid $L_S$ to $z$
crosses its boundary at

$$
y=(1-t)c+tz,\qquad0<t<1.
\tag{110.4}
$$

Both $c,z$ belong to $K$ and are distinct. But $y$ is globally pure
by Lemma 110.1, contradicting (110.4). Thus $F=L_S$. This uses
neither exposedness nor closedness of $F$, nor preservation of faces
by arbitrary projections. It also applies when $n=2$, in which case
$S$ is the whole source space. ∎

The use of actual minimal faces for every pair is essential to this
argument. A generic complex secant, a selected family of pair sections,
or an image described only as lying in some larger face does not give
the equality in (110.2). The distinct whole-pair/common-support route
of [V, §88][V] is not a premise of this proof.

## 111. Entire positive preimages and all-state singleton fibers

**Proposition 111.1 (Entire normalized positive preimage).** In the
notation of Proposition 110.2,

$$
\pi^{-1}\bigl(F_K(b(Q),b(R))\bigr)\cap\mathcal D_n
=\mathcal D(S).
\tag{111.1}
$$

Proof. The inclusion from right to left is (110.2). Conversely take
$\rho\in\mathcal D_n$ whose image belongs to that face $F$. A source
spectral decomposition has the form

$$
\rho=\sum_{i=1}^r\lambda_i P_i,\qquad
\lambda_i>0,\quad\sum_i\lambda_i=1,\quad P_i\in\mathcal R_n.
\tag{111.2}
$$

The face property gives $b(P_i)\in F$ for each positive-weight term.
For a single term this is immediate; for more terms isolate each one
as one endpoint of a two-term convex combination. Each $b(P_i)$ is
globally pure, hence extreme in $F$. The affine bijection
$\mathcal D(S)\to F$ in (110.2) identifies the extreme points of
these two bodies. It therefore supplies a rank-one $Q_i$ supported
on $S$ with $b(Q_i)=b(P_i)$. Injectivity of the entire pure labeling
$b$ gives $Q_i=P_i$. Every term in (111.2) is supported on $S$,
and so is $\rho$. ∎

**Corollary 111.2 (Rank at most two versus all density matrices).**
For every $\rho\in\mathcal D_n$ of rank one or two,

$$
\{\sigma\in\mathcal D_n:\pi(\sigma)=\pi(\rho)\}=\{\rho\}.
\tag{111.3}
$$

Proof. For rank two take $S=\operatorname{ran}\rho$. Choose any two
distinct source rays spanning $S$ and use their actual pair face.
The image of $\rho$ belongs to $\pi(\mathcal D(S))$. Every competing
$\sigma$ is supported on $S$ by (111.1), and the injectivity on
$\operatorname{Herm}(S)$ gives $\sigma=\rho$. For rank one choose
any two-plane containing its support, possible because $n\ge2$, and
use exactly the same argument. This includes $n=2$; there is no
rank-zero normalized state. ∎

The comparison in (111.3) is against **every** density matrix,
including matrices of larger rank. Injectivity only within the
rank-at-most-two subset would not give the next sign-rank conclusion.
Source spectral decomposition in (111.2) uses ordinary matrix
positivity in the supplied PSD domain. It grants neither spectrality
of the original cone before rigidity nor a native decomposition
procedure for original preparations.

## 112. Kernel inertia and the small-dimension boundary

**Proposition 112.1 (Both sign ranks are at least three).** Every
nonzero $A\in N$ satisfies

$$
n_+(A)\ge3,\qquad n_-(A)\ge3,
\tag{112.1}
$$

where $n_+$ and $n_-$ count strictly positive and strictly negative
eigenvalues with multiplicity.

Proof. The traceless Hermitian $A\ne0$ has both signs. Write its
positive and negative spectral parts as $A=A_+-A_-$ and put

$$
s=\operatorname{Tr}A_+=\operatorname{Tr}A_->0,\qquad
\rho_+=A_+/s,\quad\rho_-=A_-/s.
\tag{112.2}
$$

These are distinct density matrices, with orthogonal supports, and
$\pi(\rho_+)=\pi(\rho_-)$ because $A\in N$. If either sign rank
were one or two, Corollary 111.2 would force $\rho_+=\rho_-$.
Thus each sign rank is at least three. ∎

**Corollary 112.2 (Rigidity for $2\le n\le5$).** In these dimensions,
Definition 109.1 alone implies $N=0$, hence (109.6).

Proof. A nonzero kernel matrix would have at least six nonzero
eigenvalues by (112.1), impossible in dimension at most five.
Surjectivity, the entire cone-image identity and the trace identity
then give (109.6). ∎

The mature comparison is [Carmeli–Heinosaari–Schultz–Toigo,
§4.1, Theorem 1(a)][CHST], source arXiv:1308.5502v2: rank-at-most-$t$
states distinguished from all states require the minimum of the two
sign ranks of each nonzero self-adjoint annihilator element to be at
least $t+1$. Here $t=2$ and the elementary traceless-kernel argument
is given directly. No observable or native POVM is manufactured from
$\pi$. The weaker comparison between two rank-restricted classes
does not replace this all-state criterion.

## 113. Scalar enlargement and sphere-transitive classification

Assume now the compact $G$ of Theorem 109.2, and set

$$
\mathbb T=\{zI:|z|=1\},\qquad M=\mathbb T G\le U(n).
\tag{113.1}
$$

**Lemma 113.1 (The connected enlarged group is sphere transitive).**
$M$ is compact, preserves $N$, and is transitive on the full complex
unit sphere. Its identity component $M^0$ also acts transitively
there and contains $\mathbb T$.

Proof. Centrality of $\mathbb T$ makes its product with $G$ a subgroup,
and compactness makes that product compact. Scalar conjugations are
trivial, so $M$ preserves $N$. Given two unit vectors, $G$ sends
the projector of the first to that of the second; a scalar phase
corrects their chosen vector representatives. Thus $M$ is sphere
transitive. The scalar circle is connected and contains the identity,
so lies in $M^0$.

A compact matrix group is a Lie group with finitely many components.
Normality of $M^0$ and transitivity of $M$ make the sphere a union
of finitely many $M^0$-orbits: use representatives of $M/M^0$ on one
starting vector. These orbits are compact, and distinct ones are
disjoint. A finite closed partition of a connected sphere has one
member, since each member's complement is closed as well. Hence
$M^0$ is transitive. ∎

**Proposition 113.2 (The actual defining complex representation).**
After unitary conjugacy, the connected subgroup $M^0$ is either

$$
U(n),\qquad\text{or}\qquad
\mathbb T\operatorname{Sp}(m)\quad(n=2m).
\tag{113.2}
$$

Here $\operatorname{Sp}(m)$ is the standard compact symplectic matrix
subgroup of $U(2m)$. The second group is the image of scalar phases
times that subgroup, a central product, not a faithful direct product.

Proof. Apply [Albertini–D'Alessandro, §4, Theorem 4 and Lemma 4.2][AD]
to the compact connected effective matrix action of $M^0$ in its
actual defining complex representation. Their unitary sphere-transitive
classification gives Lie algebra $\mathfrak{su}(n)$ or
$\mathfrak u(n)$, or, for even $n=2m$, $\mathfrak{sp}(m)$ with or
without the scalar $iI$. Lemma 4.2 and its Appendix proof supply
unitary conjugacy of the symplectic embedding. Because
$\mathbb T\subset M^0$, its Lie algebra contains $iI$. The remaining
Lie algebras are therefore $\mathfrak u(n)$ and
$\mathfrak{sp}(m)+\mathbb RiI$. The connected matrix subgroup of
$U(n)$ with a given Lie algebra is unique, which gives (113.2). ∎

This classifies $M^0$, not arbitrary $G$. A list of local isomorphism
types for real sphere actions would not by itself identify these
complex embeddings. The classification is a mature matrix-group
input, not a conclusion about controllability by original words.
The coincidence $SU(2)=\operatorname{Sp}(1)$ creates no missing case:
all $n\le5$ are already covered by Corollary 112.2. The symplectic
stabilizer argument below is needed only for even $n=2m\ge6$.

## 114. Compact stabilizer averages and projection rigidity

**Theorem 114.1 (Completion of Theorem 109.2).** Under the hypotheses
of Theorem 109.2, $N=0$.

Proof. Corollary 112.2 handles $n\le5$, so assume $n\ge6$. Since
$N$ is a closed finite-dimensional real subspace invariant under
$M^0$, a Haar average of conjugates of any $A\in N$ over a compact
subgroup of $M^0$ remains in $N$. Suppose $A\ne0$. There is a unit
vector $v$ with

$$
a=\langle v,Av\rangle\ne0.
\tag{114.1}
$$

First let $M^0=U(n)$. Average over its full subgroup $U(n-1)$ fixing
$v$ pointwise. Relative to $\mathbb Cv\oplus v^\perp$, the element
$I_{\mathbb Cv}\oplus(-I_{v^\perp})$ kills the off-diagonal blocks
of the invariant average. The complementary Hermitian block is
scalar: invariance under $U(n-1)$ makes its quadratic form constant
on the complementary unit sphere, and polarization determines the
Hermitian operator. The average is therefore

$$
\overline A=aP_v+b(I-P_v),\qquad b=-\frac{a}{n-1}.
\tag{114.2}
$$

Trace zero gives the displayed value of $b$. The $v$ expectation
remains $a$, so $\overline A\ne0$. Its smaller sign rank is one,
contradicting Proposition 112.1 for $\overline A\in N$.

Now let $M^0=\mathbb T\operatorname{Sp}(m)$, $n=2m\ge6$, in the
standard embedding of Proposition 113.2. This contains the full
$\operatorname{Sp}(m)$. Choose its defining antiunitary $J$ with
$J^2=-I$, and put

$$
T_v=\operatorname{span}_{\mathbb C}\{v,Jv\}.
\tag{114.3}
$$

Antiunitarity and $J^2=-I$ give $v\perp Jv$. Thus $T_v$ is a
$J$-stable complex two-plane and $T_v^\perp$ is also $J$-stable.
Complete $v$ to a quaternionic orthonormal basis. In that basis the
pointwise stabilizer of $T_v$ inside the full $\operatorname{Sp}(m)$
is exactly the embedded standard $\operatorname{Sp}(m-1)$ acting
on $T_v^\perp$. In particular it contains
$I_{T_v}\oplus(-I_{T_v^\perp})$ and is transitive on the unit sphere
of $T_v^\perp$. These are properties of the full embedded stabilizer,
not consequences of a local isomorphism label alone.

Average $A$ over this compact stabilizer. The sign element kills
the cross terms. Sphere transitivity makes the quadratic form of the
complementary block constant on its sphere, hence makes that block
scalar. The result has the form

$$
\overline A=B\oplus bI_{T_v^\perp},\qquad
B\in\operatorname{Herm}(T_v),\qquad
\operatorname{Tr}B+(n-2)b=0.
\tag{114.4}
$$

The stabilizer fixes $v$, so $\langle v,\overline A v\rangle=a\ne0$.
If $b\ge0$, the negative eigenspace of $\overline A$ is contained
in $T_v$ and has dimension at most two. If $b\le0$, the positive
eigenspace has dimension at most two. This includes $b=0$. Either
case contradicts (112.1) for the nonzero $\overline A\in N$.
Both alternatives in (113.2) therefore force $N=0$. Surjectivity of
$\pi$ and (109.3) finish (109.6). ∎

This proof does not assume irreducibility of the conjugation action
on Hermitian matrices. Quaternionic notation identifies a subgroup
of the original complex $U(2m)$; it does not change the source to a
quaternionic PSD cone. Haar averages are mathematical elements of
an invariant subspace, not averages of supplied native operations.
The enlargement by phases and the full stabilizers create no
original gate, preparation or control interface.

## 115. Intrinsic face centers, gauges, overlap and antipodes

The following construction uses only Definition 109.1 and the actual
face equality already proved. It precedes the construction of a
unitary group and does not assume an inner product on the original $V$.

**Definition 115.1 (Intrinsic pair overlap).** For distinct $p,q\in P$,
let $F=F_K(p,q)$. Its solid ellipsoid has a unique center $c_F$.
Let $L_F=\operatorname{span}_{\mathbb R}(F-c_F)$ and define its
centered Minkowski norm by

$$
g_F(w)=\inf\{r>0:w\in r(F-c_F)\}\qquad(w\in L_F).
\tag{115.1}
$$

Define

$$
t(p,p)=1,\qquad
t(p,q)=g_F\left(\frac{p+q}{2}-c_F\right)^2\quad(p\ne q).
\tag{115.2}
$$

These definitions refer to the actual original face and its entire
centered body. They do not choose a coordinate chart on its sphere.

**Proposition 115.2 (The pair gauge recovers the source overlap).**
For distinct $Q,R\in\mathcal R_n$ and
$S=\operatorname{ran}Q+\operatorname{ran}R$, one has

$$
c_{F_K(b(Q),b(R))}=\pi(I_S/2),\qquad
g_F(\pi(A))^2=2\operatorname{Tr}(A^2)
\quad\bigl(A\in\operatorname{Herm}(S),\ \operatorname{Tr}A=0\bigr).
\tag{115.3}
$$

Consequently, for every $Q,R\in\mathcal R_n$, including $Q=R$,

$$
t(b(Q),b(R))=\operatorname{Tr}(QR).
\tag{115.4}
$$

For distinct $Q,R$, the midpoint of $b(Q),b(R)$ is the center of
their actual face exactly when the source rays are orthogonal.

Proof. Proposition 110.2 identifies the whole face with
$\pi(\mathcal D(S))$, whose center is $\pi(I_S/2)$. This center is
intrinsic: two centers of a bounded centrally symmetric body would
give a nonzero translation preserving that body, which boundedness
excludes. The centered ellipsoid is a symmetric convex unit ball,
so its Minkowski functional is a norm.

Every traceless Hermitian $A$ on the two-plane has eigenvalues
$a,-a$. The condition $I_S/2+A\ge0$ is $|a|\le1/2$. Thus the
source centered gauge at $A$ is $2|a|$. The affine bijection onto
the whole face transports the gauge, giving
$g_F(\pi(A))^2=4a^2=2\operatorname{Tr}(A^2)$.

For the pair in question put $A=(Q+R-I_S)/2$. Since $Q^2=Q$,
$R^2=R$ and $I_SQ=Q$, $I_SR=R$,

$$
\operatorname{Tr}(A^2)=\frac12\operatorname{Tr}(QR),\qquad
\pi(A)=\frac{b(Q)+b(R)}2-c_F.
\tag{115.5}
$$

Equations (115.2)–(115.3) give (115.4) for distinct projectors.
For $Q=R$ both sides are one by definition and $\operatorname{Tr}Q=1$.
Finally injectivity on $\operatorname{Herm}(S)$ says that the
midpoint is the center precisely when $Q+R=I_S$, equivalent to
orthogonality of the two rank-one projectors. ∎

In particular $0\le t(p,q)\le1$. Antipodes in an actual pair ball
have $t=0$, while the diagonal has $t=1$. The construction also
works for $n=2$, where every distinct pair spans the entire source.
This local norm calculation assumes no global least-confirmation
effect and uses no inaccessible face-reconstruction proposition.

## 116. Original affine symmetries and all-ray Wigner implementation

**Lemma 116.1 (The entire pure space and its intrinsic symmetries).**
Under Definition 109.1, $b:\mathcal R_n\to P$ is a homeomorphism,
$P$ is compact and connected, and $\operatorname{span}_{\mathbb R}P=V$.
Every $h\in\operatorname{Aut}(C,u)$ induces the bijection

$$
f_h=b^{-1}\circ h\circ b:\mathcal R_n\longrightarrow\mathcal R_n,
\tag{116.1}
$$

and it preserves $\operatorname{Tr}(QR)$ for every pair.

Proof. The entire rank-one projector space $\mathcal R_n$ is compact
and connected, as the continuous image of the complex unit sphere.
The map $b$ is a continuous bijection to the Hausdorff subspace $P$
of $V$, hence a homeomorphism. Rank-one projectors span
$\operatorname{Herm}_n(\mathbb C)$ over $\mathbb R$, by the spectral
decomposition of every Hermitian matrix. Surjectivity of $\pi$
therefore gives the spanning assertion for $P$.

The linear map $h$ restricts to an affine automorphism of $K$ and
maps extreme points bijectively to extreme points. The image of an
actual minimal face is the actual minimal face of the image pair:
apply $h$ and $h^{-1}$ to the defining face inclusions. It carries
the unique center to the unique center, and its linear restriction
carries the entire centered ellipsoid onto the target centered
ellipsoid. Consequently

$$
g_{hF}(hw)=g_F(w),\qquad t(hp,hq)=t(p,q).
\tag{116.2}
$$

Together with Proposition 115.2, this proves all-pair transition
probability preservation for (116.1). ∎

**Proposition 116.2 (All-ray Wigner intertwining).** For every
$h\in\operatorname{Aut}(C,u)$ there is a unitary or antiunitary
$W$ on $\mathbb C^n$ such that, with
$\Gamma_W(X)=WXW^{-1}$ on Hermitian matrices,

$$
f_h(Q)=\Gamma_W(Q)\quad(Q\in\mathcal R_n),\qquad
\pi\Gamma_W=h\pi
\quad\text{on all }\operatorname{Herm}_n(\mathbb C).
\tag{116.3}
$$

In particular $\Gamma_W(N)=N$.

Proof. Apply the unnumbered Wigner theorem in [Gehér, §1,
equation (1), arXiv:1407.0527v1][Geher] to the map on **all**
self-adjoint rank-one projectors in (116.1). It preserves every
$\operatorname{Tr}(QR)$ by Lemma 116.1. The cited theorem supplies
a linear or antilinear isometry on the whole Hilbert space; in
finite dimension it is respectively unitary or antiunitary. Its
statement needs neither bijectivity nor separability, although our
map is bijective. This applies also when $n=2$.

Conjugation by either kind of implementer is real-linear on the
Hermitian space. Equality of $\pi\Gamma_W$ and $h\pi$ on all
rank-one projectors extends to their real span, proving (116.3).
This identity gives $\Gamma_W(N)\subset N$; applying the inverse
identity gives equality. ∎

No choice of $W$ here is asserted continuous or multiplicative in
$h$. Orthogonality-only Uhlhorn theorems and their dimension-three
restrictions are unnecessary, because (115.4) provides the full
all-pair overlap on the entire ray space.

## 117. Closed implementer graph and the full twisted extension

Fix a source complex conjugation $\kappa$ and give

$$
U^{\pm}(n)=U(n)\cup U(n)\kappa
\tag{117.1}
$$

its usual finite-dimensional compact group topology. The two components
are the unitary and antiunitary implementers. Let $H$ be the actual
compact subgroup in Theorem 109.3.

**Theorem 117.1 (Compact graph with the exact phase kernel).** Define

$$
\mathcal L=\{(h,W)\in H\times U^{\pm}(n):\pi\Gamma_W=h\pi\}.
\tag{117.2}
$$

Its image $\widetilde G$ under projection to $U^{\pm}(n)$ is a
compact subgroup, and the graph gives a continuous surjection
$\widetilde\psi:\widetilde G\to H$ with exact sequence

$$
1\longrightarrow\mathbb T\longrightarrow\widetilde G
\overset{\widetilde\psi}{\longrightarrow}H\longrightarrow1.
\tag{117.3}
$$

In particular $H\cong\widetilde G/\mathbb T$ as a topological group,
faithfully embedded in

$$
U^{\pm}(n)/\mathbb T\cong PU(n)\rtimes\mathbb Z_2.
\tag{117.4}
$$

Proof. The equation in (117.2) is closed: all maps are continuous
in finite-dimensional matrix coordinates, and equality of linear
maps can be checked on a fixed finite basis. Conjugation composes
as $\Gamma_{W_1W_2}=\Gamma_{W_1}\Gamma_{W_2}$, so $\mathcal L$
is a closed subgroup of a compact group. Projection to $H$ is onto
by Proposition 116.2. Projection to $U^{\pm}(n)$ is injective,
because surjectivity of $\pi$ makes $h$ uniquely determined by $W$
in the intertwining equation. The compact-to-Hausdorff continuous
bijection $\mathcal L\to\widetilde G$ is a homeomorphism. The
other projection therefore defines the continuous surjective
homomorphism $\widetilde\psi$.

All scalar phases belong to its kernel. Conversely, if
$\widetilde\psi(W)=1$, then for every $Q\in\mathcal R_n$,

$$
b(\Gamma_W(Q))=\pi\Gamma_W(Q)=\pi(Q)=b(Q).
\tag{117.5}
$$

Since $\Gamma_W(Q)$ is again rank one, the injectivity of the
**entire** $b$ implies $\Gamma_W(Q)=Q$. Thus $W$ fixes every ray.
A unitary fixing every ray is scalar: coordinate rays make it
diagonal, and the rays of sums of coordinate vectors make all
diagonal phases equal. An antiunitary cannot fix every ray when
$n\ge2$. On two coordinate rays write $We_j=\alpha_j e_j$;
fixing the ray of $e_1+e_2$ forces $\alpha_1=\alpha_2$.
Antilinearity then sends $e_1+i e_2$ to
$\alpha_1(e_1-i e_2)$, a different ray. Hence the kernel is exactly
$\mathbb T$.

The quotient of the compact $\widetilde G$ by this closed kernel
maps continuously and bijectively to the Hausdorff $H$, so it is
topologically isomorphic to $H$. Inclusion in the ambient quotient
is faithful. Fixing $\kappa$ identifies that ambient quotient with
the semidirect product in (117.4). ∎

**Proposition 117.2 (Phase action and the twisted extension).** Let
$\sigma(W)=+1$ for unitary $W$ and $-1$ for antiunitary $W$. Then
$\sigma$ is a continuous homomorphism and

$$
W(zI)W^{-1}=z^{\sigma(W)}I\qquad(|z|=1).
\tag{117.6}
$$

Thus (117.3) is generally a twisted phase extension. Its kernel is
central on the unitary restriction; if antiunitaries occur, the
full kernel is not central.

Proof. Composition multiplies the two linearity signs. The two
components in (117.1) are open and closed, giving continuity.
Complex linearity fixes scalar multiplication and antilinearity
complex conjugates it. On the unit circle $\overline z=z^{-1}$,
which is (117.6). An antiunitary therefore fails to commute with
scalar phases other than the real ones. ∎

The mature phase and sign structure is [De Nittis–Gomi, §3.1,
equations (3.2)–(3.4), arXiv:1804.10111v2][DNG]. Here the compatible
compact graph (117.2) is built for the original $H$ using the
intrinsic overlap. No global continuous or homomorphic choice of
phases, no splitting of (117.3), and no global unitary phase section
is asserted. The semidirect product describing the ambient quotient
does not assert a splitting for this original-$H$ extension.

## 118. Original identity-component transitivity and a central lift

**Lemma 118.1 (The original $H^0$ is pure transitive).** The identity
component $H^0$ of the given compact matrix group acts transitively
on all of $P$.

Proof. By Lemma 116.1, $P$ is connected. A compact matrix Lie group
has finitely many components, and $H^0$ is normal. For $p\in P$
and representatives $h_i$ of $H/H^0$, transitivity of $H$ gives

$$
P=Hp=\bigcup_i H^0h_i p.
\tag{118.1}
$$

Every orbit in this finite union is compact, hence closed. Distinct
orbits are disjoint, so their distinct values form a finite closed
partition of connected $P$. Each part has closed complement, and
there can only be one. ∎

**Proposition 118.2 (The compact unitary preimage supplies $G$).** With
$\widetilde\psi$ from Theorem 117.1, put

$$
G=\widetilde\psi^{-1}(H^0).
\tag{118.2}
$$

Then $G$ is a compact subgroup of $U(n)$, its kernel over $H^0$ is
the central $\mathbb T$, and $G/\mathbb T\cong H^0$. It preserves
$N$ by conjugation and acts transitively on all $\mathcal R_n$.

Proof. The sign $\sigma$ is trivial on the kernel $\mathbb T$ of
$\widetilde\psi$. It therefore descends, by the quotient topology
in Theorem 117.1, to a continuous homomorphism
$\overline\sigma:H\to\{\pm1\}$. Its restriction to connected
$H^0$ is trivial. Hence all elements of (118.2) are unitary.
This is a closed preimage in compact $\widetilde G$, and so a
compact subgroup of $U(n)$. The kernel remains exactly $\mathbb T$,
now central by (117.6), and the quotient identification restricts
accordingly.

Every $U\in G$ satisfies $\pi\Gamma_U=h\pi$ for
$h=\widetilde\psi(U)$, so it preserves $N$. Given
$Q,R\in\mathcal R_n$, Lemma 118.1 supplies $h\in H^0$ with
$hb(Q)=b(R)$. Choose any preimage $U\in G$. Intertwining yields
$b(UQU^*)=b(R)$, and injectivity of $b$ gives $UQU^*=R$.
Thus $G$ is projectively transitive on the entire source ray space. ∎

This argument proves only what is needed to apply Theorem 109.2.
It does not require $G$ connected, does not require $H$ connected,
and does not put every original continuation in $H^0$. The preimage
construction, rather than a phase section, supplies all its lifts.
The finite-component argument is given directly and depends on no
uninspected Lie-group textbook passage.

## 119. Intrinsic rigidity and the existing original-cone dictionary

**Theorem 119.1 (Completion of Theorem 109.3).** Under Definition
109.1 and the original compact pure-transitive $H$ of (109.7),
$N=0$ and $\Phi=\pi^{-1}$ satisfies (109.6). On the entire original
state, pure and effect spaces,

$$
\begin{aligned}
\Phi(K)&=\mathcal D_n,& \Phi(P)&=\mathcal R_n,&
\operatorname{Tr}\Phi&=u,\\
e(x)&=\operatorname{Tr}(B\Phi(x)),&
E&\longleftrightarrow\{B\in\operatorname{Herm}_n(\mathbb C):0\le B\le I\}.
\end{aligned}
\tag{119.1}
$$

Here each real-linear functional $e$ has one unique Hermitian
representative $B$. Every supplied $h\in H$ acts, in this same
dictionary, by some unitary or antiunitary conjugation:

$$
\Phi h\Phi^{-1}=\Gamma_W.
\tag{119.2}
$$

Proof. Proposition 118.2 supplies precisely the compact subgroup,
entire projective transitivity and kernel invariance required by
Theorem 109.2. All of Definition 109.1 remains in force. Theorem
114.1 therefore gives $N=0$ and (109.6). The whole-base and pure
identities follow from (110.1) and (109.3).

For the functional/effect identification use the already-owned
trace-duality and dictionary part of [VI, Theorem 90.2][VI], once
the trace-preserving cone isomorphism is available. In that dictionary
$u$ corresponds to $I$, positivity of $e$ to $B\ge0$, and positivity
of $u-e$ to $I-B\ge0$. This gives the exact entire interval in
(119.1); no second Jordan reconstruction or matrix-dictionary proof
is needed. Finally (116.3) conjugated by the inverse $\Phi$ gives
(119.2). ∎

The face equality of Proposition 110.2 already forces L3 in this
projection framework. Thus VI's other conditional certificate
consumers remain applicable with their own hypotheses. They are
not extra proof premises here: neither S-to-Jordan, an equalizing
form, the curvature certificate, nor homogeneity or pure bias was
used to obtain $N=0$.

For Theorem 109.2 with only supplied $G$, its quotient conjugation
action is well-defined even before injectivity:

$$
h_g(\pi(X))=\pi(gXg^*)\qquad(g\in G).
\tag{119.3}
$$

Kernel invariance makes this independent of $X$; (109.3) and the
inverse $g^{-1}$ make it a normalized cone automorphism. After
rigidity it becomes $h_g=\pi\Gamma_g\Phi$. Identifying this quotient
action with any particular original legal action still requires
that action's stated compatibility. In Theorem 119.1 the group
$H$ is original by hypothesis and the graph enforces its compatibility.

All identifications in (119.1) concern mathematical states and
functionals of the original cone. They do not expand the legal
preparation or measurement menu. In the original-prediction
specialization the ready row maps to a rank-one density matrix only
under the retained condition that this actual ready row is in $P$.
A label for an abstract source projector does not establish that
native-ready condition.

## 120. Whole-domain suppliers and the retained quantum-origin gaps

The two rigidity theorems keep the exact original $\Omega$, legal
words, normalization column, and entire prediction/future-outcome
domain of [VI89.2][VI]. They do not restrict the future coordinates
to make a representation faithful. The additional suppliers are
precisely the whole PSD trace cover, the complete rank-one-to-all-$P$
bijection, the bound for every actual entire pair face, and either
the compatible compact $G$ or the original compact pure-transitive
$H$. AURIC relation normalization, EB3, bare L3 and the fact of
having one source do not supply these hypotheses in this argument.

**Proposition 120.1 (Scope of the obstruction).** Under the stated
suppliers, a lossy whole-PSD projection with the stated trace,
pure-label and symmetry properties is impossible. This conclusion
does not establish rigidity for arbitrary L3 cones without that
cover, and does not supply an original equalizer from L3 alone.

Proof. Under supplied $G$ this is Theorem 109.2; under original $H$
it is Theorem 119.1. Both begin with (109.3), so neither can remove
it from its own hypotheses. In particular a general generic-$k=1$
or complex-projective entry-locus assertion has not replaced the
positive preimage proof of §111. The geometry continuation in VII
has its own scope and is not a proof dependency here. ∎

The control in [VI, Proposition 92.1][VI] has $\pi=\mathrm{id}$ and
an available equalizing form $Q_0$, although a supplied invariant
$Q_\varepsilon$ has unequal pair radii. It is compatible with these
rigidity results. It must not be described as an L3 example with
no equalizer, and no conclusion that every invariant metric
equalizes pair radii follows here.

The separate existing [complex projection Gleason owner][Gleason]
starts, for $N\ge3$, from a full complex projection labeling and a
`ProjectionPackage`: a total matrix function nonnegative on all
star projections, normalized at $I$, and additive on orthogonal
binary sums. Its existing `gleason_representation` gives the unique
PSD trace-one representative of that supplied assignment on every
star projection. These full labeling, noncontextuality and
orthogonal-sum premises are substantial. That theorem supplies
neither (109.3), nor all original pure labels, nor original frames.
It is a downstream interface comparison, not a new Born or Gleason
theorem in this volume. The $n=2$ result here uses the whole cover
and the intrinsic all-pair overlap; it makes no qubit Gleason claim.

The full $H$ in (117.3) can contain antiunitary implementers.
Eliminating a transpose component of an original generator requires
its separately supplied original path/action interface, as retained
in [VI, Theorem 96.2][VI]. The central extension over $H^0$ does not
establish identity-component membership of every original word.
Neither scalar phases nor a quotient identification provide a
global unitary phase section, a splitting, or original-word unitarity.

Compact closure elements, Haar averages, convex mixtures, source
spectral decompositions, the whole effect interval, and the auxiliary
groups are mathematical constructions. None is by itself a native
control, preparation, measurement, inverse, filter or Return. The
original whole-future laws, true branch masses, archives and returned
rows retain the interfaces of [VI §§94–96][VI]. A matched marginal
or invertible matrix does not provide those interfaces.

Joint laws, process descent, instruments, complete positivity,
composites, tensor products, time, clocks and physical correspondence
retain their separate original contracts. The static cone and
symmetry identifications here do not establish those contracts or
derive quantum foundations from the single-$\Omega$ word model.
The full quantum-origin problem therefore retains these concrete
unsupplied bridges.

The reused ingredients are PSD support geometry, positive and negative
spectral parts, the mature sign-rank criterion, compact unitary
sphere-transitive classification, Haar integration, all-ray Wigner
theory, phase extensions and trace duality. The conditional synthesis
connects actual faces to entire positive fibers and then to a
stabilizer obstruction; its intrinsic overlap and closed graph supply
the compatible lift needed for the original compact action. No
global priority, new classification or physical-origin claim is made.

[V]: QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md
[VI]: QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_VI.md
[Compact]: ../../../Blueprint/D5/S3/Quantum/Algebra/OriginalProbabilityCompactAction.md
[Gleason]: ../../../Blueprint/D5/S3/Quantum/GleasonComplexRepresentation.md
[AD]: ../../../Library/LieTheory/albertinidalessandro2001transitivity.md
[CHST]: ../../../Library/HilbertOperators/carmeliheinosaarischultztoigo2014tasks.md
[Geher]: ../../../Library/HilbertOperators/geher2014wigner.md
[DNG]: ../../../Library/LieTheory/denittisgomi2018twisted.md

## 追加锚（本行以下为增补区）
