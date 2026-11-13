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

## 121. 两步原排斥的四维纯点片与全域唯一完整确认

**卷间编号与引用约定。** 本章条目及公式采用本卷的121.x编号。下表规定本章所有跨卷引用的来源；裸章号、罗马卷号及其相应式号均按此表解释，不指本卷同号条目。

| 本章使用的来源编号 | 原始来源 |
| --- | --- |
| 125、127、128、129、130章及全部相应子条目、Q125及Q127—Q130式号 | [SAME_READBACK《同一实际读回与并行全重置的概率校准》][SameReadback] |
| VII103、VII104及相应子条目 | [FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS VII][FacetVII] |
| VIII113及相应子条目 | [EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY VIII][ExclusionVIII] |
| IX116、IX119、IX120及相应子条目 | [EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY IX][ExclusionIX] |
| THREE_COPY VII121.6 | [THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY VII][ThreeCopyVII] |
| (83.8) | [BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION V][V] |
| VI(89.13) | [INTRINSIC_POLAR_QUOTIENT_AND_NONCOLLAPSE VI][PolarVI] |

其中用于“原合同”的127.10专指SAME_READBACK第127.10节及其完整引用链，不指该卷关于共同圆球的定理127.10；THREE_COPY VII121.6也不是本章定理121.6。表中的EXCLUSION VIII不是本卷BILATERAL VIII，INTRINSIC_POLAR VI也不是本卷既有参考标签[VI]所指的整球卷；(83.8)则直接复用本卷既有参考标签[V]。

### 121.1 完整原域、较弱入口与直接复用的接口

本章在同一原模型内证明：EB3、Inj及 $\dim V=9$ 已迫使每个原纯标签的完整确认效应唯一。因此该结论适用于127.1的完整 $\mathsf E_0$，但不把唯一确认等同于原单位预算一，也不把它当作完整量子重构。

**约定 121.1（原对象与假设范围）。** $V\ne0$ 是有限维实空间，$C\subset V$ 是闭、尖、生成凸锥，$u\in V^*$ 在 $C\setminus\{0\}$ 上严格正。始终使用整个

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad \mathcal E=[0,u]_{C^*},\\
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\qquad
\mathcal T_p(x)=\min_{f\in\mathcal F_p}f(x),\qquad
D_p=\{x\in K:\mathcal T_p(x)=0\},\\
\mathcal A_p=\{f\in\mathcal E:f(p)=1,\ f|_{D_p}=0\},\qquad
P_0=\{p\in P:\mathcal A_p\text{ 为单点}\},\\
N_p=\{h\in C^*:h(p)=0\},\qquad
N_{D_p}=\{h\in C^*:h|_{D_p}=0\},\qquad
\nu_p=\dim_{\rm aff}\mathcal A_p.
\end{gathered}
\tag{121.1}
$$

这里 $K$、$\mathcal E$ 紧，$\operatorname{aff}K=\{u=1\}$，其方向空间记为 $H=\ker u$。原二元关系为

$$
p\perp q\quad\Longleftrightarrow\quad
\exists f\in\mathcal E:\ f(p)=1,\ f(q)=0
\quad\Longleftrightarrow\quad q\in D_p\qquad(p,q\in P).
\tag{121.2}
$$

补效应使它对称。EB3要求每个完整 $D_p$ 仿射同构于整个闭三球；Inj要求 $D_p=D_q\Rightarrow p=q$。121.2—121.5只使用EB3+Inj；121.6另用 $\dim V=9$。全部辅助内积只供有限维紧性、Gram行列式和坐标使用，不替换原效应或概率。

直接复用VII103.2、VII104.1及IX119.1、IX120.2的完整面接口：每个 $D_p$ 为非点紧暴露极大真面；全部非空真面只有原纯单点或完整排除球；$S_p:=P\cap D_p=\partial_{\rm rel}D_p$；不同完整球至多交于一个原纯点。$\mathcal A_p$ 非空紧凸，其中任一效应的整个零面恰为 $D_p$，整个一值面恰为 $\{p\}$。这里的面是整个原面，不是选定截面。

确认冗余就是IX119.10的 $a(p)$，采用128的记号 $\nu_p$ 以免与别处球内斜率混淆。该定理的完整结论直接复用：

$$
\begin{gathered}
\dim\operatorname{span}N_p=\nu_p+4,\qquad
N_{D_p}=\operatorname{cone}\mathcal A_p,\qquad
\dim\operatorname{span}N_{D_p}=\nu_p+1,\\
p\perp q\ \Longrightarrow\ \nu_p=\nu_q.
\end{gathered}
\tag{121.3}
$$

至少一个 $P_0$ 标签的存在也属既有结果。IX120.9的 $P_0$ 标签稠密、THREE_COPY VII121.6的稠密 $G_\delta$ 及非塌缩层完整确认闭图、原宽度上半连续和原宽度紧层均保持原结论，不重新证明。整个 $P$ 中的残余集不能直接限制为每张指定 $S_p$ 上的残余集；本章在一张固定实际球面的闭二盘上另作闭覆盖。

在E0应用中，入口仍逐项取127.1、128.1：EB3、Inj、一组含 $P_0$ 顶点的实际原正交三角 $\triangle=(p_1,p_2,p_3)$、同一三角的全部原零效应联合分离 $\mathsf J_\triangle$，以及三个规范 $T_i$ 的全原锥正性。准确地，

$$
\begin{gathered}
\forall x,y\in K:\quad
[\forall i\ \forall b\in\mathcal E,\ b(p_i)=0\Rightarrow b(x)=b(y)]\Rightarrow x=y,\\
T_i:V\to M_i=\operatorname{span}D_{p_i},\qquad
h(T_ix)=h(x)\quad(h\in\operatorname{span}N_{p_i},\ x\in V),\qquad
T_i(C)\subseteq C.
\end{gathered}
\tag{121.4}
$$

125.3—125.6已在这些前件下给出 $\dim V=9$。本章不重证九维张成或分类，也不把种子、联合分离、规范压缩正性或PC1归给裸EB3。

### 121.2 九个真实球面点的二次评估秩

**引理 121.2（九点与唯一二次关系）。** 固定任一完整三维仿射椭球 $D\subset\{u=1\}$，令 $M=\operatorname{span}D$，则 $\dim M=4$。可在 $\partial_{\rm rel}D$ 选九个点，使齐次二次形式的评估映射

$$
\operatorname{Sym}^2 M^*\longrightarrow\mathbb R^9,\qquad
Q\longmapsto(Q(x_1),\ldots,Q(x_9))
\tag{121.5}
$$

秩为九，其核恰由 $D$ 的边界二次方程生成。九个点必仿射张成 $\operatorname{aff}D$。

证明。在任一仿射参数化 $D=b+L\overline B^3$ 中，取标准球面上的

$$
\pm e_1,\quad\pm e_2,\quad\pm e_3,\qquad
(e_1+e_2)/\sqrt2,\quad(e_1+e_3)/\sqrt2,\quad(e_2+e_3)/\sqrt2.
$$

$u|_M=1$ 的仿射三平面不经过线性原点，所以其次数至多二的全部多项式，恰与 $M$ 上齐次二次形式通过齐次化对应。把一个消失于上述九点的多项式写成 $c+\ell\cdot t+t^*At$，其中 $A$ 对称。六个轴端点迫使 $\ell=0$、$A_{ii}=-c$；后三点再逐一迫使 $A_{12}=A_{13}=A_{23}=0$。故核只有 $c(1-|t|^2)$ 这一维。该空间维数为十，评估秩因而恰为九。

一般地，仿射维数至多二的集合上，次数至多二的多项式空间维数至多六；其任意九点评估秩不可能达到九。因此在一个仿射三平面中，秩九还迫使九点仿射张满该平面。证毕。

在 $V$ 上固定一个辅助欧氏结构，并在 $\operatorname{Sym}^2 V$ 上使用诱导内积。令 $\xi(x)=x\otimes x$，定义连续非负量

$$
\Gamma(x_1,\ldots,x_9)
=\det\bigl[\langle\xi(x_i),\xi(x_j)\rangle\bigr]_{i,j=1}^9.
\tag{121.6}
$$

$\Gamma>0$ 恰表示九个评估泛函线性无关。因为任一 $M$ 上的二次形式都可延伸到 $V$，这些点位于 $M$ 时，环境评估秩与(121.5)的秩相同。此处是在四维线性 $M$ 上处理十维二次形式空间，不能误用“九个一般位置点决定任意环境二次曲面”的说法。

### 121.3 同一指定球面上的非塌缩闭层

固定 $p\in P$，取任意非空相对开集 $U\subset S_p$。在其中取一张闭二盘 $Q$，其相对内部在 $S_p$ 中非空，且 $Q\subset U$。以下每个移动标签 $q$ 都在这同一张紧的实际二盘中。

对四点定义

$$
\tau(y_0,y_1,y_2,y_3)
=\det\bigl[\langle y_a-y_0,y_b-y_0\rangle\bigr]_{a,b=1}^3.
\tag{121.7}
$$

它是平行六面体体积的平方，严格正恰表示四点仿射无关。

**引理 121.3（控制每个采样标签的第二层球）。** 对整数 $m\ge1$，令 $Q_m\subset Q$ 由以下存在条件定义：存在

$$
\begin{gathered}
x_1,\ldots,x_9\in S_q,\qquad
\Gamma(x_1,\ldots,x_9)\ge1/m,\\
g_j\in\mathcal A_{x_j},\qquad
 y_{j0},y_{j1},y_{j2},y_{j3}\in D_{x_j},\qquad
\tau(y_{j0},y_{j1},y_{j2},y_{j3})\ge1/m
\quad(1\le j\le9).
\end{gathered}
\tag{121.8}
$$

则每个 $Q_m$ 在 $Q$ 中闭，且 $Q=\bigcup_{m\ge1}Q_m$。

证明覆盖性。对每个固定 $q$，引理121.2在实际 $S_q$ 上提供 $\Gamma>0$ 的九点。对每个这样的纯点 $x_j$，完整三球 $D_{x_j}$ 含四个仿射无关点，并有 $g_j\in\mathcal A_{x_j}$。只有有限个严格正数，取充分大的同一个 $m$ 即满足全部下界。此处没有作连续选择。

证明闭性。设 $q_n\in Q_m$、$q_n\to q\in Q$。将(121.8)中全部有限见证，连同任取的 $e_n\in\mathcal A_{q_n}$，一起放在紧的 $K$ 和 $\mathcal E$ 的有限乘积中取共同收敛子列，极限分别记 $x_j,y_{jk},g_j,e$。固定 $Q\subset S_p$ 保证 $q$ 已是原纯点。连续评价给

$$
e(q)=1,\qquad e(x_j)=0,\qquad
 g_j(x_j)=1,\qquad g_j(y_{jk})=0.
\tag{121.9}
$$

由第一对等式及 $e\in\mathcal E$，先得 $x_j\in D_q$，尚不假定 $x_j$ 纯。每个极限四点仍有 $\tau\ge1/m$，所以 $g_j$ 的零面是含三维四面体的非空真面；它不可能是单点，原面分类使它恰为某个 $D_z$。又 $g_j\in N_{D_z}=\operatorname{cone}\mathcal A_z$，且 $g_j(x_j)=1$、$0\le g_j\le u$，故其全域最大值为一。$\mathcal A_z$ 中每张效应的全域最大值也是一，归一迫使 $g_j\in\mathcal A_z$。原一值面接口遂给 $x_j=z\in P$。

因而 $x_j\in P\cap D_q=S_q$，$g_j\in\mathcal A_{x_j}$，全部 $y_{jk}\in D_{x_j}$。连续性还保留 $\Gamma\ge1/m$ 与所有 $\tau\ge1/m$。极限见证因此仍满足(121.8)，即 $q\in Q_m$。序列闭性在紧度量 $Q$ 中就是闭性。证毕。

这一步只在原紧基中取极限，再用同一极限效应的一值面证明标签仍纯；没有假定 $P$ 闭。只控制移动 $D_q$ 自己的直径或体积，不能代替对九个 $D_{x_j}$ 各自的非塌缩控制。

### 121.4 九个纯边界点固定整颗Hausdorff极限球

**引理 121.4（每个闭层上的整球连续）。** 映射 $q\mapsto D_q$ 在每个 $Q_m$ 上按环境Hausdorff距离连续。

证明。设 $q_n\to q$ 且各点在同一个 $Q_m$。把实际球写成

$$
D_{q_n}=b_n+L_n\overline B^3,\qquad
L_n:\mathbb R^3\to H\text{ 单射}.
\tag{121.10}
$$

球心 $b_n\in K$；因 $b_n\pm L_nt\in K$ 对全部单位 $t$ 成立，$\|L_n\|\le\operatorname{diam}K/2$。任意子列因而还有子列使 $b_n\to b$、$L_n\to L$，其中 $L$ 的秩暂时只知不超过三。统一参数球上的一致收敛给

$$
D_{q_n}\longrightarrow D_\infty:=b+L\overline B^3
\quad\text{于Hausdorff距离}.
$$

同时取 $e_n\in\mathcal A_{q_n}$ 的收敛子列。极限 $e\in\mathcal E$ 满足 $e(q)=1$，并在每个 $b+Lt$ 上取零。因此 $D_\infty\subset D_q$。这正是原效应紧性给出的上包含，并不先声称 $e\in\mathcal A_q$ 或整球已收敛到 $D_q$。

再沿共同子列取(121.8)的全部见证极限。引理121.3的证明保证九点 $x_j$ 仍属于 $S_q$，且 $\Gamma\ge1/m$。各 $x_{jn}\in D_{q_n}$，故 $x_j\in D_\infty$。若 $\operatorname{rank}L\le2$，这些点位于仿射维数至多二的空间，其二次评估秩至多六，与 $\Gamma>0$ 矛盾。所以 $D_\infty$ 是非退化三维椭球，与 $D_q$ 有同一仿射三平面。

每个 $x_j$ 是 $D_q$ 的极点，而 $D_\infty\subset D_q$ 且包含它，所以也是 $D_\infty$ 的极点，位于两颗椭球的相对边界。两边界二次形式于是都在同一个四维线性 $M=\operatorname{span}D_q$ 的九点评估核中。该核由引理121.2及 $\Gamma>0$ 恰为一维，两二次形式必成非零比例。其边界相同，取边界凸包得到 $D_\infty=D_q$。

以上对任意子列都成立：若整列不趋于 $D_q$，存在Hausdorff距离有固定正下界的子列；该子列又有刚证明必趋于 $D_q$ 的子列，矛盾。因此整列收敛，得到连续性。证毕。

$Q$ 是非空紧二盘，故为Baire空间。引理121.3给可数闭覆盖，某个 $Q_m$ 在 $Q$ 中有非空相对内部。$Q$ 的边界在 $Q$ 中无处稠密，所以可在这个内部中选取更小的闭二盘 $Q'$，其内部仍是 $S_p$ 中的非空开集。引理121.4遂在 $Q'$ 上给真正的整球连续族。这里的Baire作用域始终是指定实际球面内的一张闭二盘。

### 121.5 局部仿射标架与没有标签碰撞的四维紧片

**定理 121.5（任意实际球面开片的两步四维提升）。** 在EB3+Inj下，对每个 $p\in P$ 及每个非空相对开集 $U\subset S_p$，集合

$$
\{r\in P\setminus\{p\}:\exists q\in U,\ p\perp q\perp r\}
\tag{121.11}
$$

含有一个同胚于闭四维立方体的紧集。整张紧片上的 $\nu_r$ 都等于 $\nu_p$。

证明。先取121.4所给 $Q'\subset U$。为把它上面的整球连续性变成局部仿射参数化，在 $\{u=1\}$ 固定一个参考原点 $o$，令

$$
h_q(v)=\max_{x\in D_q}\langle v,x-o\rangle\qquad(v\in H).
$$

写球心为 $b(q)$，形状算子为 $A(q)=L_qL_q^*$，则

$$
\begin{gathered}
\langle v,b(q)-o\rangle=\tfrac12\bigl(h_q(v)-h_q(-v)\bigr),\\
\langle v,A(q)v\rangle
=\bigl(h_q(v)-\langle v,b(q)-o\rangle\bigr)^2.
\end{gathered}
\tag{121.12}
$$

Hausdorff收敛使支撑函数在单位方向上一致收敛。第一式确定连续的球心；第二式经极化确定连续的正半定形状算子，且每个 $A(q)$ 的秩恰为三。它们都是由整颗球唯一确定的，不依赖最初所选 $L_q$。

固定 $q_0\in\operatorname{int}_{S_p}Q'$，在 $\operatorname{ran}A(q_0)$ 选一组基 $v_1,v_2,v_3$。三个 $A(q_0)v_i$ 线性无关，故在 $q_0$ 的一个小邻域内，连续的 $A(q)v_i$ 仍线性无关，并恰张成 $\operatorname{ran}A(q)$。Gram—Schmidt给该像空间的连续正交标架 $U(q):\mathbb R^3\to H$。正半定平方根的连续性给

$$
L(q)=A(q)^{1/2}U(q),\qquad
D_q=b(q)+L(q)\overline B^3,\qquad
S_q=b(q)+L(q)S^2.
\tag{121.13}
$$

每个 $L(q)$ 单射。平方根连续性是有限维正半定算子的通常连续函数演算；也可在共同有界谱区间上以多项式一致逼近平方根取得。这里只在 $q_0$ 附近建立标架，不输入全局球丛、全局纯域连续性或任何可逆群。

对每个 $q\in Q'$，已有 $p\perp q$，所以 $p\in S_q$。在参数球 $S^2$ 上选一张小闭二帽 $T$，使它的 $q_0$ 像避开 $p$。该像紧，因此与 $p$ 有严格正距离。联合连续性及 $T$ 紧允许把底盘缩为 $q_0$ 附近的小闭二盘 $Q''$，使

$$
\Psi(q,t)=b(q)+L(q)t\ne p
\qquad(q\in Q'',\ t\in T).
\tag{121.14}
$$

可把两个二盘都选为局部坐标中的闭方盘，因而各自同胚于 $[0,1]^2$。$\Psi$ 的全部像都是实际 $S_q$ 上的原纯点。

此乘积映射单射。固定 $q$ 时来自 $L(q)$ 单射。若 $q\ne q'$，Inj给 $D_q\ne D_{q'}$；它们都含 $p$，而不同完整球至多交一点，故 $D_q\cap D_{q'}=\{p\}$。两帽都避开这个共同点，不能发生跨标签碰撞。因此 $\Psi:Q''\times T\to K$ 是连续单射。紧源及Hausdorff靶使其成为到像的同胚，其像 $R$ 紧且同胚于 $[0,1]^4$，并满足(121.11)。

每个像点实际沿两条原边 $p\perp q\perp r$ 到达，(121.3)两次应用给 $\nu_r=\nu_p$。这里没有给任意两个纯点添边，也没有将两步原边偷换成三条边或一台共同三结果仪器。证毕。

### 121.6 八维法向层的紧投影覆盖排除全部确认歧义

直接复用128.2及其证明中更明确的投影结论。对有非空内部的紧凸体 $L\subset\mathbb R^n$，记

$$
\mathcal N_L(x)=\{v:\langle v,z-x\rangle\le0\ (z\in L)\},\qquad
\Sigma_k(L)=\{x\in\partial L:\dim\operatorname{span}\mathcal N_L(x)\ge k\}.
$$

128.2给可数紧集 $X_j\subset\partial L$ 覆盖 $\Sigma_k(L)$；每个 $X_j$ 有一个到 $(n-k)$ 维线性空间的正交投影 $\pi_j$，在 $X_j$ 上单射，逆满足

$$
\|x-y\|\le\frac2{\sqrt3}\|\pi_jx-\pi_jy\|\qquad(x,y\in X_j).
\tag{121.15}
$$

本章直接使用这一已证全点紧覆盖，不重建普遍法向奇异层定理，也不用“几乎处处可求长”替代全点覆盖。

**定理 121.6（全域唯一完整确认）。** 在EB3+Inj且 $\dim V=9$ 的整个原域中，

$$
\boxed{\quad P=P_0,\qquad \nu_p=0\quad(p\in P).\quad}
\tag{121.16}
$$

因此对每个 $p$ 唯一写 $\mathcal A_p=\{e_p\}$，有 $\dim\operatorname{span}N_p=4$、$N_{D_p}=\mathbb R_+e_p$。结论特别适用于完整E0。

证明。先按128.3已核对的准确识别，将原正法向与 $\operatorname{aff}K$ 中的外法向对应：

$$
N_r\longrightarrow\mathcal N_K(r),\qquad h\longmapsto-h|_H.
\tag{121.17}
$$

这是线性锥同构。限制为零则 $h$ 是 $u$ 的倍数，而 $h(r)=0$ 迫其为零。反向对外法向 $v\in H^*$，泛函 $h(x)=-v(x-u(x)r)$ 在 $K$、从而在 $C$ 非负，且在 $r$ 为零，唯一补回常数项。故维数没有额外加减一。

假设某 $p$ 有 $\nu_p\ge1$。定理121.5产生一个连续嵌入 $F:[0,1]^4\to P$，像中每个 $r$ 满足 $\nu_r=\nu_p\ge1$。由(121.3)、(121.17)，整个像都在八维凸体 $K$ 的 $\Sigma_5(K)$ 中。

在128.2取 $n=8,k=5$，得到紧覆盖 $X_j$ 及单射投影 $\pi_j:X_j\to E_j^\perp$，其中 $\dim E_j^\perp=3$。集合 $F^{-1}(X_j)$ 在紧立方体中闭，并覆盖整个 $[0,1]^4$。Baire定理使其中一项有非空相对内部。立方体内部在立方体中稠密，因此存在非空的 $\mathbb R^4$ 开集 $O\subset(0,1)^4$，其全部像位于某个固定 $X_j$。

于是

$$
\pi_j\circ F|_O:O\longrightarrow E_j^\perp\cong\mathbb R^3
\tag{121.18}
$$

连续且单射。把 $\mathbb R^3$ 以线性方式嵌入 $\mathbb R^4$ 的一个坐标超平面，复合后便是非空开集 $O\subset\mathbb R^4$ 到 $\mathbb R^4$ 的连续单射。区域不变性定理要求它的像在 $\mathbb R^4$ 中开；但它包含在一个内部为空的三维超平面中，矛盾。因此没有这样的 $p$，全部 $\nu_p=0$。非空紧凸 $\mathcal A_p$ 的仿射维数零等价于它是单点，其余结论由(121.3)直接复用。证毕。

这里的拓扑矛盾有明确的定理桥，不仅是口头比较“四维”与“三维”：128.2的紧层保证拉回闭，第二次Baire把一个真正的四维开片压到同一个可单射投影层，再由区域不变性排除。证明不要求 $F$ 或其逆为Lipschitz，也不从一般拓扑嵌入直接断言四维Hausdorff测度严格正。

法向索引分别是：原态仿射维数八；假设分支的法向锥线性维数至少五；单位外法向集合维数至少四；128.2取锥索引 $k=5$，投影维数 $8-5=3$。若仅核对Alberti原文Definition 1.7与Theorem 3，则应取其环境 $h=8$、单位法向索引 $k=4$，得到 $8-4-1=3$。这两种 $k$ 的定义不同，不能相互照抄。本证明的承重覆盖是128.2的既有全点投影结论。

128.3的点或线段结论仍成立；本定理消去其非退化线段分支。尺寸矛盾实际直接处理全部 $\nu_p\ge1$，无须把已排除的更大冗余重算为新成果。121.2—121.5本身不使用维数九；维数九只在最后把五维法向层的投影靶限制为三维时进入。

### 121.7 唯一确认之后仍须支付的同一个原单位接触

回到完整E0及其同一实际种子 $w=p_1+p_2+p_3$、共同正定型 $B$ 与三个 $\Delta_i$。129的固定内球原定义保持：

$$
c=w/3,\qquad
I=\{c+v:v\in\ker u,\ \|v\|_B^2\le1/6\},\qquad
I\subset K\subset\{c+v:\|v\|_B^2\le2/3\}.
\tag{121.19}
$$

这些是相对于仿射中心 $c$ 的半径平方。对 $u(x)=1$，仍有 $\|x\|_B^2=1/3+\|x-c\|_B^2$；原点范数的相应阈值是一半与一，不能把六分之一当成一半。

定理121.6现在为每个原纯点唯一确定 $e_p$。129.4的准确点态等价直接给

$$
\begin{gathered}
e_p(w)=1\quad\Longleftrightarrow\quad D_p\cap I\ne\varnothing
\quad\Longleftrightarrow\quad\|p\|_B^2=1\\
\Longleftrightarrow\quad\Delta_1(p)=\Delta_2(p)=\Delta_3(p)=0.
\end{gathered}
\tag{121.20}
$$

成立时 $e_p=B(p,\cdot)$，唯一接触点为 $(w-p)/2$。这仍是点态PC3；点态PC1只要求至少一个 $\Delta_i(p)=0$。127的PC1到PC3升级使用全部原纯标签及完整实际球面，不能缩成一个孤立标签的一次接触推三次接触。

129.7的IC0候选保持原式 $\forall p\in P_0:D_p\cap I\ne\varnothing$。本章只是证明其域 $P_0=P$。因此已有129.8及130.5条件链现在可写为

$$
\begin{aligned}
\mathsf{IC}_0
&\Longleftrightarrow\ \forall p\in P:\ e_p(w)=1\\
&\Longleftrightarrow\ \forall p\in P\ \exists i:\Delta_i(p)=0
\Longleftrightarrow\ \mathsf W\\
&\Longleftrightarrow\ \text{130.3的全部原状态谱性及其非中心边界检验}\\
&\Longleftrightarrow\ \exists\Phi:\operatorname{Herm}_3(\mathbb C)\overset\sim\longrightarrow V,
\quad\Phi(\mathrm{PSD}_3)=C,\quad u\Phi=\operatorname{Tr}.
\end{aligned}
\tag{121.21}
$$

这里全量化PC1、IC0、W及完整静态字典的等价均为既有条件结果，不是新的分类。W下的G、Jordan分类、状态谱存在和谱唯一直接取VIII113.7—113.9；130.2在尚无W的EB加Inj域已给全部原态的仿射直径覆盖，130.3—130.4已给指定 $3/4,1/4$ 非中心原混态的谱性反向消费者及无任何有限原谱分解的见证。本章不重复这些内容，也不将仿射直径里的球内对径当作已可原区别。

仍未证明 $\mathsf E_0\Rightarrow\mathsf{PC1}/\mathsf{IC}_0$，也没有完整E0且失败PC1的同域反模型。确认唯一消除了完整确认集合内的非零差方向，未取得限制映射的正逆：IX119.8及125.6所指的 $N_p|_{D_p}\subseteq\operatorname{Aff}(D_p)_+$ 是否为满正锥，依然不能由线性同构推出。故不能据此把 $e_p$ 称为全部 $\mathcal F_p$ 的least，或声称 $\mathcal T_p(x)=e_p(x)$ 对所有原混态成立。

同样，本章不证明 $P$ 闭、全域整球连续、全局球丛、projectivity、全纯二点面、共同三结果预算或实际仪器。局部四维片没有提供任意标签到种子的两步路径，也没有把有限原边传播变成满宽传播。若假设W，既有VII104.2—104.3已支付全域三结果完成，无须再另添一项联合预算；当前缺的是从E0取得该等价条件。

若IC0失败，129.8的原失败见证及129.6的严格联合界保持原义：存在同一原 $p_*$，其三个 $\Delta_i(p_*)>0$；其唯一 $e_{p_*}$ 在三个种子上的总读数 $t_*=e_{p_*}(w)$ 仍满足

$$
\begin{gathered}
r_*:=\|p_*\|_B\in(1/\sqrt2,1),\qquad
s_*:=\min_{x\in D_{p_*}}\|x\|_B\in(1/\sqrt2,1),\\
\frac3{1+\sqrt{6r_*^2-2}}<t_*<
\frac{3\sqrt{6s_*^2-2}}{1+\sqrt{6s_*^2-2}},\qquad 1<t_*<2.
\end{gathered}
\tag{121.22}
$$

本章没有消除这个唯一确认分支。相容的必要不等式不是反证，也不是一个已实现的完整反模型；“唯一”不允许缩放确认尺，因为 $e_p(p)=1$、原 $u$ 和整个原效应上界均已固定。

### 121.8 条件静态字典与所有未代付的原物理合同

仅在(121.21)的等价条件成立以后，沿127.9、129.6及VIII113.9的同一个 $\Phi$，完整静态对应如下，均为直接复用：

| 原对象 | 同一原锥、同一原单位的对应 |
| --- | --- |
| 全纯态、混态、非负质量 | $P=\{\Phi(zz^*/(z^*z)):z\ne0\}\cong\mathbb{CP}^2$；$K$ 为全部迹一PSD像，整个 $C=\Phi(\mathrm{PSD}_3)$ 含零、全部非负质量及有限凸组合 |
| 全部原效应与Born评价 | $u\Phi=\operatorname{Tr}$；整个 $\mathcal E$ 恰对应 $0\preceq A\preceq I_3$，对所有原混态 $f_A(\Phi\rho)=\operatorname{Tr}(A\rho)$，保持零、单位与补 |
| 全确认、least与整个排除球 | 对归一 $z$，全部确认对应 $zz^*\oplus A$、$0\preceq A\preceq I_{z^\perp}$；此时least才是 $zz^*$，完整 $D_{p_z}$ 为 $z^\perp$ 上全部密度矩阵 |
| 纯比较、正交、三框架 | 最低确认比较为归一复内积模方；原正交为复正交，每条原正交纯边有唯一第三点，三张秩一原效应和为 $u$，容量为三 |
| 数学POVM、可观测量与谱 | 任意有限原 $f_j\ge0,\sum_jf_j=u$ 恰对应全部有限POVM；每态有含零权、重复谱的三谱分解；全部实线性可观测量对应Hermitian矩阵 |
| Jordan、共同尺与球心 | 运输 $(XY+YX)/2$ 得Jordan乘积，$B(\Phi X,\Phi Y)=\operatorname{Tr}(XY)$、$\Phi(I_3)=w$；此后全锥自对偶、共同圆球与中心 $(w-p)/2$ 才由完整字典取得 |

完整候选仍保留**127.10全部原合同及其引用链**，不因(121.16)而缩小任何来源、过程或时间域。

**原来源、操作、记录与未来。** 同一原装饰元组 $\mathcal O$、共同来源域、全部中点实现、原概率像紧性、全测试表及闭性、零／单位／补／有界倍增、重复标签与每种同中点实现、全部非负质量及零／次归一／不等质量，过程和参考各自完整的相关联合输入均保留。原 $L,p,\omega,K,M$、两次使用同一读回、两实张成、全实关系、完整(83.8)、VI(89.13)全部两尺度等式、C2、整个 $G=1_E$、精确PRE之后整个H13及每个原资格态、活跃块严格负方向、共享总迹一、非活跃零质量及空活跃集均保持各自原定义；操作映射 $p$ 不与纯标签混型。设备／事件／来源绑定、全部菜单分支、实际参考／副本／相关联合、记录／权限／控制、ready／flags、失败／拒绝／停止／销毁／返回、实际混合、原字、全部合法未来和每个中间切口，连同原生与细化消费者、terminal futures、联合有符号关系、细标签粗归组、记录后的条件未来、source-adoption及资源合同均不删减。

**全部有限联合域。** 对每个有限 $N\ge1$，仍须提供实际 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成 $C_N$、严格正 $u_N=u^{\otimes N}$、整个 $K_N$、全部 $P_N$ 和完整原效应区间。每个实际分块 $a+b=N$ 保留

$$
C_a\otimes_{\min}C_b\subseteq C_{a+b}\subseteq C_a\otimes_{\max}C_b.
\tag{121.23}
$$

同一产品配对、严格张量单位、全部原因子置换及逆的正性、规范重括号与不连续位置分块的指定运输均保持。完整实际 $S_2$ 仍按(Q127.36)量化任意产品或纠缠纯点、任意有限凸族、全部非负权、零权及重复标签；仅产品态比较不能代付。低二份 $q=1,2$ 的least／谱性／正面投影及保纯到Jordan桥、唯一实际自复合的直和扇区限制及秩和实维乘法、同一实际两因子的产品正规形，仍为原全有限层级分别使用的三项供应。单体确认唯一不支付二份谱性或二份比较。

**三份资源及更高有限次数。** $\mathsf F_{\max}$ 精确保留(Q127.37)：同一最大复块 $L\ge2$、同一含相位正交基，$g_r=\sum_{a=1}^L|a\rangle_r|a\rangle_r|a\rangle_r$，实际 $\Delta_r=|g_r\rangle\langle g_r|\in C_3$、$u_3(\Delta_r)=L$，其余扇区零，归一原源为 $\Delta_r/L$。不预付三份纯性或实际制备；全经典 $L=1$ 分支仍按原定理免除资源。条件复三能级支路中 $L=3$，二、三份秩九、二十七，不把高阶整个排除集合继续要求为单体EB3。部分三角形正性、非PSD混合锚及各自限定的循环结论只按原域使用，不支付当前单体E0接触或完整有限层级。

**全旁观CP、事件、同族仪器与Lüders。** (Q127.38)仍量化每个 $b\ge0$、任意含纠缠的同一共同输入，要求 $(\operatorname{id}_{W_b}\otimes F)(C_{b+m})\subseteq C_{b+n}$。只有完整有限层级及共同表示已供应，才沿原Choi桥识别通常CP、矩形跨扇区Kraus与逐输入TP／TNI预算。实际事件另需原完整提升、实际探针及相容核；让所有数学CP-TNI分支实际可用仍需事件饱和选择。共同输入预算、接线、记录、粗粒化与校准负责同族仪器。仅严格正质量分支作条件归一，零质量分支不强定归一条件态；Lüders更新另外要求同一分支的锐效应、接受态中性和输出校准。全数学POVM及和为单位不替代可执行仪器。

**物理钟、动态来源、Hamiltonian和数值 $\hbar$。** 原钟、实际动态来源、连续齐次可逆时间群及单位仍分别供应。另给同载体上的全实时间连续保单位锥自同构群 $A_t$，才有这项供应的有限维生成元；在已重构复块中另给保迹酉时间族，才使用(Q127.39)的 $U_t=\exp(-\mathrm itH/\hbar)$、$\rho_t=U_t\rho U_t^*$、$\mathcal L(\rho)=-\mathrm i[H,\rho]/\hbar$。量词覆盖全部原输入及全部实际时间；$H$ 的标量平移、时间重标和生成元尺度边界保持。实际Hamiltonian、能量识别与标定、数值 $\hbar$、时空和物理空间维数均未由确认唯一产生。

裸EB3到Inj、实际种子三角、原联合分离及规范全锥正压缩的各入口桥仍分别保留。本章在明确的九维较弱域中消除确认歧义，不声称裸EB3重构、独立公理更少、实际量子动力学或完整量子物理已经完成。

### 121.9 复用边界与成熟来源

本章归属为 `repo-derived` 纸面综合，不主张全球原创、历史优先权、Lean核验或经验验证。新增消费者是：在一张指定原球面中，以九个采样纯标签各自的第二层非塌缩见证构造闭层；由九点评估秩取得局部整球连续；用两步实际原边产生四维紧纯点片；最后将该片接入已证八维法向层紧投影覆盖，消去全部确认冗余。九点二次插值、紧性、Baire、支撑函数、正半定平方根与区域不变性均为成熟工具，不另称新的一般插值或凸分析定理。

直接复用的承重结果是：VII103.2、VII104.1的面分类；IX119.1、IX120.2的准确零面与一值面；IX119.10的法向维数及沿边常数；128.2的可数紧覆盖和单射Lipschitz投影逆；128.3、128.5所给旧分支及联合约束；IX120.9和THREE_COPY VII121.6的稠密与闭层；125.3—125.6的九维原配对；127的共同种子尺和完整条件重构；129的同心内外球、逐点等价与严格联合界；130的原态覆盖及谱性反向消费者；VIII113.7—113.9的整个W分类、G和谱字典。它们不作为本章新增成果重计。

[Alberti原文][Alberti] Definition 1.7明确定义单位外法向集合，并说明其Hausdorff维数为法向锥维数减一；Theorem 3给闭全维凸集相应奇异层的 $h-k-1$ 维可数 $C^2$ 可求长性，按其Definition 1.1允许该维Hausdorff零测例外。本章仅核对成熟来源和索引，实际证明用128.2已展开的全点紧层投影，不从一条“几乎处处”结论自行删去例外集。

区域不变性使用[Hatcher《Algebraic Topology》][Hatcher] §2.B、Theorem 2B.3、印刷页172的准确形式：$O\subset\mathbb R^d$ 开、$f:O\to\mathbb R^d$ 连续单射，则 $f(O)$ 开。121.6先把投影靶 $\mathbb R^3$ 线性放入 $\mathbb R^4$，才在同维四的源靶上应用此定理；没有把不同维的映射直接代入。两次Baire分别作用于实际球面的紧二盘和拉回的紧四立方体，二者都是明确的完备度量空间。

[Alfsen—Shultz][AS]的Hilbert ball property仍要求每对极点生成的整个最小面为norm-exposed Hilbert球，其有限维分类还保留相应projectivity。[Barnum—Müller—Ududec][BMU] Theorem 16仍要求projectivity、跃迁概率对称及全部相应滤子保纯。本章的唯一完整确认、一个局部连续球族和三张正种子压缩没有支付这些全域前件；条件静态分类仍按127和VIII113的既有完整桥消费。文献核对不构成穷尽搜索或全球新颖性证书。

[SameReadback]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "第125、127—130章：原种子配对、完整E0、法向紧层、内球接触和谱性条件消费者；第127.10节：全部原来源、有限复合、资源、事件、仪器、记录与时间合同。"
[PolarVI]: QUANTUM_ORIGIN_INTRINSIC_POLAR_QUOTIENT_AND_NONCOLLAPSE_VI.md "定义89.7及式(89.13)：同一原装饰元组与全部两尺度、原质量及整个输出合同；不同于整球卷VI。"
[FacetVII]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md "VII103.2、104.1：完整原面；104.2—104.3：取得Pair_perp以后已有的全部对径与共同三结果。"
[ExclusionIX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX119.1、119.10：准确原端面、法向维数及沿边冗余；119.8：线性限制与原单位费用的区别；IX120.8—120.9：限制同构及P0稠密。"
[ThreeCopyVII]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md "定理121.6：既有非塌缩层完整确认闭图及P0稠密Gdelta。"
[ExclusionVIII]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_VIII.md "VIII113.7—113.9：整个W的同锥同单位分类、G、Jordan、状态谱及复三能级字典。"
[Alberti]: https://people.dm.unipi.it/alberti/ricerca/1989-91/convex.pdf "Giovanni Alberti, On the structure of singular sets of convex functions, Calculus of Variations and Partial Differential Equations 2 (1994), 17—27, DOI 10.1007/BF01234313；Definition 1.1、Definition 1.7及Theorem 3。"
[Hatcher]: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf "Allen Hatcher, Algebraic Topology, §2.B, Theorem 2B.3, p.172：区域不变性。"
[AS]: https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6236-11511_2006_Article_BF02392307.pdf "E. M. Alfsen and F. W. Shultz, State spaces of Jordan algebras, Acta Mathematica 140 (1978), 155—190；条件范围按127.11、129.7和130.7复用。"
[BMU]: https://arxiv.org/html/1403.4147v4#Thmtheorem16 "Howard Barnum, Markus P. Müller and Cozmin Ududec, Higher-order interference and single-system postulates characterizing quantum theory, Theorem 16；条件范围按127.11复用。"

### 121.10 完整白话

仍把全部原状态看成同一块八维仿射实体，全部测试都是这整块实体上的零到一读数尺。每个纯标签背后有一整颗排除三球，球边的所有点也都是原纯标签。旧结果已经说：同一个标签的完整确认尺至多是一点或一条线段。本章在EB3、标签不重复及九维原空间内，排除那条非退化线段。

原因来自两步关系自己的大小。先沿一条真实排斥边走到起点背后的二维球面；在这张球面中只取一小盘。再从盘中每个标签，走到它背后的球面上取一小帽。盘有两个方向，帽也有两个方向。不同帽所在的整球都经过原起点，除此以外不能相交；让帽避开原起点，就不会把不同标签的输出混在一起。因此两盘相乘确实成为原纯点中的一块四维紧片。

这里不能先画一族平滑移动的球。真正困难的是防止极限标签变混、极限球压扁。做法是在每颗移动球上钉九个足以确定其二次边界的纯点，还为每个钉子背后的下一颗球保留一个不塌缩的四面体。取极限时，同一把原效应既确认钉子又在四面体上读零，原面规则便迫使钉子仍纯。九个真实纯边界点随后固定整颗极限球。只在这张指定二盘内用Baire取得一个连续小区，就足够造出上述四维片；没有假定整个纯域闭合或全部球全局连续。

如果起点有一整段不同的完整确认尺，旧法向公式会把这种冗余沿两条实际边传到整张四维片，使片上每点都需要至少五维法向。八维凸实体里，这类点已有可数紧层，每层都能单射投到三维空间。再对四维片的拉回用Baire，就会有真正四维开片单射进入三维。区域不变性严格排除这件事。因此每个原纯点都只剩一张完整确认尺。

但剩一张尺不等于它的三个种子读数总和恰为一。这个总和仍由同一原单位固定，不能靠缩放改掉。129已经证明：它恰为一，等价于该标签达到共同外球，也等价于它的完整排除球碰到同一个固定内球，或三个种子压缩全为纯射线或零。本章没有补出这一下接触。完整E0是否必然给每个标签至少一次种子接触，仍未证明；满足全部E0却失败接触的完整反模型也未取得。

因此推进是明确的一项：确认歧义在全原纯域消失，未解模型只剩“确认唯一但预算偏高”的分支。原IC0候选、全域PC1及既有静态量子字典之间的条件等价保持；一个标签的一次接触仍不能当作三次。条件链若补齐，才接回全部复三能级态、效应、Born概率、数学测量和谱；共同来源、实际操作、全部有限复合与纠缠、三份资源、全旁观CP、事件及同族仪器、Lüders、完整记录与合法未来、物理钟、Hamiltonian和数值 $\hbar$ 仍各按127.10承担。

## 追加锚（本行以下为增补区）

## 122. 三相位三次族的完整原效应与族内端点刚性

### 122.1 同一原域、三次族与文献范围

**定义 122.1（整个三次族及最低确认）。** 令 $V=\mathbb R^3\oplus\mathbb C^3$ 为实九维空间，写 $x=(a_1,a_2,a_3;z_1,z_2,z_3)$；$z_i$ 对应补指标组成的边 $jk$。固定

$$
\begin{gathered}
u(x)=a_1+a_2+a_3,\qquad
p_1=(1,0,0;0,0,0),\quad p_2=(0,1,0;0,0,0),\quad
p_3=(0,0,1;0,0,0),\qquad w=p_1+p_2+p_3,\\
\Delta_i(x)=a_ja_k-|z_i|^2\quad(\{i,j,k\}=\{1,2,3\}),\\
d_\lambda(x)=a_1a_2a_3-\sum_{i=1}^3a_i|z_i|^2
                    +2\lambda\operatorname{Re}(z_1z_2z_3),\\
C_\lambda=\{x:a_i\ge0,\ \Delta_i(x)\ge0\ (i=1,2,3),\ d_\lambda(x)\ge0\},
\qquad -1\le\lambda\le1.
\end{gathered}
\tag{122.1}
$$

对每个参数均取整个 $K_\lambda=C_\lambda\cap\{u=1\}$、$P_\lambda=\operatorname{ext}K_\lambda$ 和 $\mathcal E_\lambda=[0,u]_{C_\lambda^*}$。沿用原最低定义，标量函数与线性压缩分别记为 $\mathcal T_p$ 和 $T_i$：

$$
\begin{gathered}
\mathcal F_p=\{f\in\mathcal E_\lambda:f(p)=1\},\qquad
\mathcal T_p(x)=\min_{f\in\mathcal F_p}f(x)\quad(x\in C_\lambda),\\
D_p=\{x\in K_\lambda:\mathcal T_p(x)=0\},\qquad
\mathcal A_p=\{f\in\mathcal F_p:f|_{D_p}=0\},\qquad
P_0=\{p\in P_\lambda:\mathcal A_p\text{ 为单点}\},\\
N_p=\{h\in C_\lambda^*:h(p)=0\},\qquad
N_{D_p}=\{h\in C_\lambda^*:h|_{D_p}=0\},\\
p\perp q\quad\Longleftrightarrow\quad
\exists f\in\mathcal E_\lambda:\ f(p)=1,\ f(q)=0
\quad\Longleftrightarrow\quad q\in D_p\qquad(p,q\in P_\lambda).
\end{gathered}
\tag{122.2}
$$

EB$_{\ge1}$ 表示每个原纯点的完整 $D_p$ 仿射同构于某个整数维数至少为一的整个闭球，维数可随标签改变；EB3把该维数固定为三。Inj表示 $D_p=D_q\Rightarrow p=q$。本章先不假设其中任何一项，也不假设全纯least确认、全局自对偶或实际仪器。二能级密度球的实仿射维数是三，其非归一Lorentz锥的实线性维数是四。

本章所称125、127—130及其子条目均指[SAME_READBACK][Q122SR]，其中“127.10原合同”专指该卷第127.10节及其完整引用链，并非该卷定理127.10。关于一般原模型的条件结果直接复用这些条目及本卷121.6—121.8；本章新增的消费者仅是显式族(122.1)的全效应结算与族内反模型排除，归属为 `repo-derived`。双曲锥的分支、闭包和凸性采用[Renegar原始稿][Q122Renegar] §2、Proposition 1、Theorem 2及Theorem 3，属于成熟Gårding理论的中间复用；Hermitian主子式判据及端点的矩阵量子事实也只作为下列证明的成熟中间事实。这里不作历史优先权或全球新颖性判断，所给有限文献范围不构成这种判断的依据。

[Q122SR]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "第125、127—130章：完整原域、规范种子、PC1、IC0、条件静态字典；第127.10节及其引用链：全部原合同。"
[Q122Renegar]: https://optimization-online.org/wp-content/uploads/2004/03/844.pdf "James Renegar, Hyperbolic Programs, and Their Derivative Relaxations, §2, Proposition 1、Theorems 2—3；2004年原始稿。发表于 Foundations of Computational Mathematics 6 (2006), 59—79, DOI 10.1007/s10208-004-0136-z；本文仅使用所引原始稿中的准确命题。"

### 122.2 整个显式集合的锥合法性

**定理 122.2（全参数的闭双曲锥）。** 对每个 $|\lambda|\le1$，$d_\lambda$ 关于 $w$ 双曲，且(122.1)的整个 $C_\lambda$ 恰为该方向的闭双曲锥。因而它是闭、尖、生成的凸锥，$w\in\operatorname{int}C_\lambda$，$u$ 在非零锥元上严格正，$K_\lambda$ 为紧凸基底，$\mathcal E_\lambda$ 为紧的完整效应区间，(122.2)中的最小值确实达到。实线性对合

$$
R(a_1,a_2,a_3;z_1,z_2,z_3)
 =(a_1,a_2,a_3;-z_1,-z_2,-z_3)
\tag{122.3}
$$

保持 $u,w$，且 $R(C_\lambda)=C_{-\lambda}$。

证明。固定任意实向量 $x$，置 $P=z_1z_2z_3$、$r=|P|$。若 $r>0$，由 $|\lambda\operatorname{Re}P|\le r$，可以选取模长分别为 $|z_i|$ 的三个复数 $\widetilde z_i$，使
$\operatorname{Re}(\widetilde z_1\widetilde z_2\widetilde z_3)=\lambda\operatorname{Re}P$；例如先指定乘积的相位，再分配给三个因子。若 $r=0$，保留原 $z_i$ 即可。令

$$
H_x=\begin{pmatrix}
a_1&\widetilde z_3&\overline{\widetilde z_2}\\
\overline{\widetilde z_3}&a_2&\widetilde z_1\\
\widetilde z_2&\overline{\widetilde z_1}&a_3
\end{pmatrix}.
\tag{122.4}
$$

对每个实 $\tau$，行列式展开给

$$
d_\lambda(x+\tau w)=\det(H_x+\tau I_3).
\tag{122.5}
$$

$H_x$ 为Hermitian矩阵，故此单变量多项式全部根为实数；又 $d_\lambda(w)=1$，所以双曲性成立。这里的 $H_x$ 只是对每个固定 $x$ 的选择，不要求也没有取得关于 $x$ 的线性选择。

按Renegar §2在Theorem 2之前的闭锥定义，闭双曲锥由 $\tau\mapsto d_\lambda(x+\tau w)$ 的根全不正刻画。由(122.5)，这恰等价于 $H_x\succeq0$。成熟的Hermitian判据说，所有主子式非负恰等价于PSD；在(122.4)中，七个非空主子式分别就是 $a_i$、$\Delta_i(x)$ 和 $d_\lambda(x)$。因此这个闭锥恰是(122.1)，双向包含同时成立。Renegar Theorem 2的Gårding凸性及其闭包结论遂给整个 $C_\lambda$ 的凸性；此处不需要借相位选择构造线性矩阵表示。

显式不等式连续，故锥闭；它们在 $w$ 处全部严格，故 $w$ 是内点，锥满维并生成 $V$。若 $x\in C_\lambda$ 且 $u(x)=0$，三个非负 $a_i$ 全零，三个二阶条件再迫使全部 $z_i=0$。所以 $u$ 严格正；同时 $x,-x\in C_\lambda$ 只能发生于零，故锥尖。归一截面中 $0\le a_i\le1$、$|z_i|^2\le a_ja_k\le1/4$，所以 $K_\lambda$ 闭且有界，确为紧基底。

效应区间闭。若其中一列 $f_n$ 的任一辅助对偶范数无界，取 $f_n/\|f_n\|$ 的单位极限 $h$。对每个 $x\in K_\lambda$，$0\le f_n(x)\le1$ 迫使 $h(x)=0$，而 $K_\lambda$ 线性张成 $V$，矛盾。因此效应区间紧。$\mathcal F_p$ 是含 $u$ 的闭子集，最低值达到。最后，直接代入得 $d_{-\lambda}(Rx)=d_\lambda(x)$，而 $R$ 不改变 $a_i,\Delta_i,u,w$；由于 $R^2=I$，得到(122.3)的全部断言。证毕。

### 122.3 三种子的完整最低排除、法向与规范正压缩

**定理 122.3（三扇二元窗口在整个族中不变）。** 对任意 $|\lambda|\le1$，三个 $p_i$ 都是原纯点。设 $\{i,j,k\}=\{1,2,3\}$，令

$$
\begin{gathered}
\pi_i x=(a_j,a_k,z_i),\qquad
\mathscr L_i=\{(b,c,z):b,c\ge0,\ bc\ge|z|^2\},\qquad
\upsilon_i(b,c,z)=b+c,\\
M_i=\{x:a_i=0,\ z_j=z_k=0\},\qquad e_i(x)=a_i.
\end{gathered}
\tag{122.6}
$$

其中 $\pi_i$ 的逆嵌入只在 $M_i$ 上使用；定义 $T_i$ 为将 $a_i,z_j,z_k$ 置零并保留 $a_j,a_k,z_i$ 的实线性映射。则

$$
\begin{gathered}
N_{p_i}=\pi_i^*(\mathscr L_i^*),\qquad
\operatorname{span}N_{p_i}
=\operatorname{span}_{\mathbb R}\{a_j,a_k,\operatorname{Re}z_i,\operatorname{Im}z_i\},\\
\mathcal F_{p_i}
=\{e_i+q\circ\pi_i:q\in[0,\upsilon_i]_{\mathscr L_i^*}\},\qquad
\mathcal T_{p_i}(x)=a_i(x)\quad(x\in C_\lambda),\\
D_{p_i}=\{x\in K_\lambda:a_i=0\}
=\{a_i=0,\ z_j=z_k=0,\ a_j+a_k=1,\ a_j,a_k\ge0,\ |z_i|^2\le a_ja_k\},\\
\mathcal A_{p_i}=\{e_i\},\qquad N_{D_{p_i}}=\mathbb R_+e_i.
\end{gathered}
\tag{122.7}
$$

每个完整 $D_{p_i}$ 是实三维闭球，$\dim M_i=4$，$\dim\operatorname{span}N_{p_i}=4$，$\dim\operatorname{span}N_{D_{p_i}}=1$。三个规范压缩唯一满足

$$
\begin{gathered}
T_i:V\longrightarrow M_i,\qquad h(T_ix)=h(x)
\quad(h\in\operatorname{span}N_{p_i},\ x\in V),\qquad
T_i(C_\lambda)\subseteq C_\lambda,\\
T_i^2=T_i,\quad \operatorname{im}T_i=M_i,\quad T_ip_i=0,\quad
uT_i=u-e_i,\qquad T_iT_j=T_jT_i=e_k(\cdot)p_k\quad(i\ne j).
\end{gathered}
\tag{122.8}
$$

三种子的全部原零效应联合分离整个 $V$，特别满足125.5的 $\mathsf J_\triangle$；$e_i(p_j)=\delta_{ij}$、$\sum_i e_i=u$，所以这三个原纯点构成实际原二元关系下的三角。

证明。若 $p_1$ 是两张归一态的非平凡凸组合，非负的 $a_2,a_3$ 在两张态上都须为零。二阶条件迫使三个 $z_i$ 全零，再由归一得两张态都等于 $p_1$。循环置换给全部种子纯性。

先算整个 $N_{p_1}$。任意实线性泛函可写成 $h=\sum_i b_i a_i+2\operatorname{Re}\sum_i\overline{\eta_i}z_i$。若 $h\in N_{p_1}$，则 $b_1=0$。对任意 $\varepsilon>0$、相位 $\phi$，点

$$
(1,\varepsilon^2,0;0,0,\varepsilon e^{\mathrm i\phi})\in C_\lambda
\tag{122.9}
$$

满足全部显式条件，其三次式为零。把 $h\ge0$ 除以 $\varepsilon$ 再令其趋零，得 $\operatorname{Re}(\overline{\eta_3}e^{\mathrm i\phi})\ge0$ 对所有相位成立，故 $\eta_3=0$。以 $(1,0,\varepsilon^2;0,\varepsilon e^{\mathrm i\phi},0)$ 同理得 $\eta_2=0$。所以 $h$ 只读取 $(a_2,a_3,z_1)$。

每个 $C_\lambda$ 元的这一块属于 $\mathscr L_1$，而 $\mathscr L_1$ 的每个元零延拓后本来就在 $C_\lambda$。因此正性恰是此块上的正性，给出第一行的法向锥等式。具体地，块对偶由
$b_2,b_3\ge0$、$b_2b_3\ge|\eta_1|^2$ 刻画；这是二阶Hermitian迹配对的PSD判据，故它的线性张成是全部四维块对偶。其余指标循环成立。

对 $f\in\mathcal F_{p_i}$，$g=u-f\in N_{p_i}$，故 $g=\widetilde g\circ\pi_i$。将 $f\ge0$ 限制到整个嵌入的 $\mathscr L_i$，得 $\upsilon_i-\widetilde g\ge0$；而 $g\ge0$ 给 $\widetilde g\ge0$。置 $q=\upsilon_i-\widetilde g$ 即得(122.7)的完整 $\mathcal F_{p_i}$。反向，对区间中的任意 $q$，$e_i+q\pi_i\ge0$ 且其补为 $(\upsilon_i-q)\pi_i\ge0$ 于整个 $C_\lambda$，并在 $p_i$ 读一，故没有漏效应。全部这类 $f$ 都逐点大于等于 $e_i$，而 $q=0$ 已给 $e_i$，所以最低函数恰为 $a_i$。

在 $a_i=0$ 时，另两条二阶不等式迫使 $z_j=z_k=0$，三次式自动为零。归一后余下条件恰为(122.7)。坐标

$$
(a_j-a_k,\ 2\operatorname{Re}z_i,\ 2\operatorname{Im}z_i)
\tag{122.10}
$$

将它仿射双射到整个实单位三球，因为平方范数不超过 $(a_j+a_k)^2=1$。该球是 $e_i$ 的整个零面，故其球面极点也都是 $K_\lambda$ 的原纯点。若一个完整确认效应还在该球上全零，其 $q$ 必在整个 $\mathscr L_i$ 上全零，故 $q=0$，得到 $\mathcal A_{p_i}=\{e_i\}$。若 $h\in N_{D_{p_i}}$，它尤其同时在 $p_j,p_k$ 取零；刚算出的 $N_{p_j}$ 和 $N_{p_k}$ 的交恰为 $\mathbb R_+e_i$，得其余法向断言。

$T_i$ 保留的块属于 $\mathscr L_i$，其零延拓属于 $C_\lambda$，所以它在整个原锥上正。该块的全部四维线性读数正是 $\operatorname{span}N_{p_i}$，在 $M_i$ 上分离向量，故读数保持既证明规范性也证明唯一性。投影、质量及相乘公式逐坐标成立。三个法向张成之和覆盖全部三个实对角坐标和三个复边坐标，恰为 $V^*$。任一非零 $h\in N_{p_i}$ 可除以 $\max_{K_\lambda}h>0$ 而成为原零效应，所以真正的全部原零效应也联合分离，而非只有任意线性泛函分离。最后 $e_i\in\mathcal E_\lambda$ 且上述种子读数成立，给实际原边及全域单位和。证毕。

### 122.4 内参数的两个全局唯一相位极值

**命题 122.4（完整支持面的两个纯单点）。** 固定 $-1<\lambda<1$。令 $s=s_\lambda$ 是

$$
1-3s^2+2\lambda s^3=0
\tag{122.11}
$$

在 $(1/2,1)$ 中的唯一根，令 $t=s_{-\lambda}$，并置

$$
X=\frac{(1,1,1;s,s,s)}3,\qquad
Y=\frac{(1,1,1;-t,-t,-t)}3,\qquad
S(x)=\sum_{i=1}^3\operatorname{Re}z_i.
\tag{122.12}
$$

则 $X,Y\in P_\lambda$，并且对整个 $K_\lambda$ 有

$$
-t\le S(x)\le s,\qquad
\{x\in K_\lambda:S(x)=s\}=\{X\},\qquad
\{x\in K_\lambda:S(x)=-t\}=\{Y\}.
\tag{122.13}
$$

证明。$F_\lambda(r)=1-3r^2+2\lambda r^3$ 在 $r=1/2$ 的值为 $(1+\lambda)/4>0$，在 $r=1$ 的值为 $2(\lambda-1)<0$，而在该区间导数 $6r(\lambda r-1)<0$。所以 $s$ 存在且唯一；对 $-\lambda$ 同理得 $t$。未归一的 $x_0=3X$ 满足 $a_i=1$、$\Delta_i=1-s^2>0$、$d_\lambda(x_0)=0$，故 $X\in K_\lambda$。$Y=R X_{-\lambda}$ 同样属于 $K_\lambda$。

根式给出三个精确恒等式

$$
\begin{gathered}
1-\lambda s=\frac{1-s^2}{2s^2}>0,\\
1+\lambda s-2s^2=\frac{(1-s^2)(4s^2-1)}{2s^2}>0,\qquad
1+2\lambda s=\frac{4s^2-1}{s^2}>0.
\end{gathered}
\tag{122.14}
$$

在 $x_0$ 处的一阶微分为

$$
Dd_\lambda(x_0)
=(1-s^2)u-2s(1-\lambda s)S
=c_s(su-S),\qquad c_s=2s(1-\lambda s)>0.
\tag{122.15}
$$

对任意 $y\in C_\lambda$，锥的凸性给 $x_0+\tau y\in C_\lambda$ 对 $\tau\ge0$ 成立。在 $\tau=0$ 的非负右导数遂给 $Dd_\lambda(x_0)[y]\ge0$。所以 $su-S$ 是整个锥上的正泛函，特别在全部归一态上 $S\le s$。

为证明等号唯一，写实变分
$v=(b_1,b_2,b_3;\xi_1+\mathrm i\eta_1,\xi_2+\mathrm i\eta_2,\xi_3+\mathrm i\eta_3)$，并限制到

$$
u(v)=0,\qquad S(v)=0,
\quad\text{即}\quad \sum_i b_i=\sum_i\xi_i=0.
\tag{122.16}
$$

三次式的二阶微分在这整个七维空间上为

$$
\begin{aligned}
Q(v):=D^2d_\lambda(x_0)[v,v]
={}&-\sum_i b_i^2-4s\sum_i b_i\xi_i
-2(1+\lambda s)\sum_i\xi_i^2\\
&-2(1-\lambda s)\sum_i\eta_i^2
-2\lambda s\Bigl(\sum_i\eta_i\Bigr)^2.
\end{aligned}
\tag{122.17}
$$

令 $m=\sum_i\eta_i$、$\eta^\perp=\eta-(m/3)(1,1,1)$，配方得到

$$
\begin{aligned}
-Q(v)={}&\sum_i(b_i+2s\xi_i)^2
+2(1+\lambda s-2s^2)\sum_i\xi_i^2\\
&+2(1-\lambda s)\|\eta^\perp\|^2
+\frac23(1+2\lambda s)m^2.
\end{aligned}
\tag{122.18}
$$

由(122.14)，它对每个非零 $v$ 严格为正。这是直接在完整切空间上的配方，不另借一般曲率定理。

若 $q\in K_\lambda$ 且 $S(q)=s$，令 $v=3(q-X)$。它满足(122.16)。对 $0\le\varepsilon\le1$，$x_0+\varepsilon v=3((1-\varepsilon)X+\varepsilon q)$ 属于 $C_\lambda$。若 $q\ne X$，常数项和一次项为零、二次项为 $Q(v)/2<0$，从而对充分小的正 $\varepsilon$，$d_\lambda(x_0+\varepsilon v)<0$，矛盾。因此等号点只有 $X$。一个线性泛函的唯一最大点是暴露极点：若其为两张态的严格凸组合，两张态都必须达到同一最大值，故都等于它。这证明 $X$ 的实际纯性。

把刚才整段论证用于参数 $-\lambda$，再沿 $R:C_\lambda\to C_{-\lambda}$ 运输。由于 $S(Rx)=-S(x)$，便得整个 $K_\lambda$ 上的下界 $-t$、唯一等号点 $Y$ 及其纯性，完成(122.13)。证毕。

### 122.5 从整个效应区间计算最低函数

**定理 122.5（内参数的全效应单点排除）。** 对命题122.4的 $X,Y,s,t$，令 $h_X=su-S$、$h_Y=tu+S$。则

$$
\begin{gathered}
N_X=\mathbb R_+h_X,\qquad N_Y=\mathbb R_+h_Y,\\
\mathcal F_X=\{u-\alpha h_X:0\le\alpha\le(s+t)^{-1}\},\qquad
\mathcal F_Y=\{u-\beta h_Y:0\le\beta\le(s+t)^{-1}\},\\
\mathcal T_X(x)=\frac{S(x)+t u(x)}{s+t},\qquad
\mathcal T_Y(x)=\frac{s u(x)-S(x)}{s+t}\qquad(x\in C_\lambda),\\
D_X=\{Y\},\qquad D_Y=\{X\},\qquad
\mathcal A_X=\{\mathcal T_X\},\qquad
\mathcal A_Y=\{\mathcal T_Y\},\qquad X,Y\in P_0.
\end{gathered}
\tag{122.19}
$$

右侧最低函数同时是 $V$ 上的线性效应；等式的最低解释量化所有 $x\in C_\lambda$。二者之和为 $u$，且

$$
\mathcal T_X(w)=\frac{3t}{s+t}\in(1,2),\qquad
\mathcal T_Y(w)=\frac{3s}{s+t}\in(1,2).
\tag{122.20}
$$

证明。在 $x_0=3X$ 处，所有对角及二阶不等式严格，且(122.15)非零。因此在它的一个环境开邻域中，$C_\lambda$ 恰由 $d_\lambda\ge0$ 决定，$d_\lambda=0$ 是光滑边界。若 $h\in N_X$，则 $h(x_0)=0$；每个满足 $Dd_\lambda(x_0)[v]=0$ 的切向量都能由边界上穿过 $x_0$ 的双侧光滑曲线实现。$h$ 在这条曲线上非负且在中点为零，所以导数 $h(v)=0$。故 $h$ 必为 $Dd_\lambda(x_0)$ 的实倍数。非零正泛函在内点 $w$ 严格为正，而 $Dd_\lambda(x_0)[w]=3(1-s^2)>0$，倍数必须为正。再用(122.15)和命题122.4已证明的 $h_X\ge0$，便得整个 $N_X=\mathbb R_+h_X$。对参数 $-\lambda$ 作相同论证并沿 $R$ 运输，得 $N_Y=\mathbb R_+h_Y$。这里的法向计算使用实际局部边界，没有预置某张支持面代替原法向锥。

若 $f\in\mathcal F_X$，则 $u-f\in N_X$，故且仅故它可写为 $u-\alpha h_X$、$\alpha\ge0$，再要求 $f\ge0$。因 $h_X\ge0$，上界 $f\le u$ 已自动成立。基底齐次性使 $f\ge0$ 等价于

$$
\alpha\max_{K_\lambda}h_X\le1.
\tag{122.21}
$$

由完整的全局极值(122.13)，$\max_{K_\lambda}h_X=s+t$，恰在 $Y$ 达到。于是确认集合恰为(122.19)的整条闭线段。对于任何 $x\in C_\lambda$，$h_X(x)\ge0$，所以最低值在 $\alpha=(s+t)^{-1}$ 达到，得到所写线性公式。其归一零集是 $S=-t$ 的整个原支持面，由命题122.4它正好只有 $Y$。要求一个确认效应再在 $Y$ 取零，迫使 $\alpha=(s+t)^{-1}$，所以完整确认集合也是所写单点。$Y$ 的全部论证相同：$\max_{K_\lambda}h_Y=s+t$，唯一最大点为 $X$，由此取得其完整确认集合、最低值及完整零集。

两个公式直接相加为 $u$。在 $w$ 处 $u(w)=3,S(w)=0$，得(122.20)；因为 $s,t\in(1/2,1)$，有 $2t>s$、$2s>t$，恰给两端严格界。至此最低值确实遍历整个 $[0,u]_{C_\lambda^*}$，没有把两张所选效应当作全部候选，也没有把局部严格弯曲当作完整排除的替代。证毕。

### 122.6 实际二元关系中的孤立边

**推论 122.6（保留种子三角而出现不可三角完成的原边）。** 对每个 $-1<\lambda<1$，纯点原正交图中 $X,Y$ 的邻点分别只有 $Y,X$，所以 $\{X,Y\}$ 构成一条独立的二顶点连通分支。不存在第三个纯点与它们共同构成原正交三角，也不存在与 $X,p_i$ 同时原正交的纯点，或与 $Y,p_i$ 同时原正交的纯点。与此同时，定理122.3的种子三角、全部种子球面及三个规范正压缩仍全部存在。特别地，内参数同时违反EB$_{\ge1}$、EB3及同种子的全原PC1。

证明。由(122.2)与(122.19)，纯邻点集合恰为所写单点；$X\ne Y$ 且 $p\not\perp p$，所以该边无额外邻点，也无三角完成。若纯点同时邻接 $X,p_i$，它必须等于 $Y$；但 $a_i(Y)=1/3>0$，故 $Y\notin D_{p_i}$，矛盾。交换 $X,Y$ 同理。

单点的仿射维数为零，不能仿射同构于任何正整数维的完整闭球，因此两种EB条件都失败。还可直接看出同种子压缩的失败：

$$
\Delta_i(X)=\frac{1-s^2}{9}>0,\qquad
\Delta_i(Y)=\frac{1-t^2}{9}>0\qquad(i=1,2,3).
\tag{122.22}
$$

各 $T_iX,T_iY$ 都是四维种子Lorentz锥的内部向量；没有一个是极射线向量或零，故全原PC1失败。这里不借用只有EB3入口下才成立的127条件链，而是直接算出真实二元后果。

直观地看，三个种子各自打开的二能级窗口始终是完整球体，窗口能读取的四个实方向和正压缩也始终相同；变化发生在三个复边共同参与的三次项。参数处在两端之间时，相位和有一张只碰到一个纯点的上支持面，也有一张只碰到另一个纯点的下支持面。上端纯点的全部确认效应只能沿一条线段变化，降到最低时只把下端纯点排除；下端同样只排除上端。因此二元图里出现一条接不到第三个顶点的独立边，尽管原来的三扇球窗及种子三角仍然完好。这个图景只解释已证公式，不增加假设；$s,t$ 一般不同，未将 $X,Y$ 称为关于某个共同固定中心的对径点。证毕。

### 122.7 共同固定内球与仅限本族的端点判据

**定理 122.7（同族几何约化及端点的准确静态字典）。** 在整个(122.1)族中，以实际种子尺度定义

$$
\begin{gathered}
B(x,y)=\sum_i a_i b_i+2\operatorname{Re}\sum_i z_i\overline{\zeta_i}
\quad\bigl(y=(b_1,b_2,b_3;\zeta_1,\zeta_2,\zeta_3)\bigr),\\
c=w/3,\qquad I=\{c+v:u(v)=0,\ B(v,v)\le1/6\}.
\end{gathered}
\tag{122.23}
$$

则它正是127.2的同种子 $B$，并且对全部参数有

$$
I\subseteq K_\lambda\subseteq
\{c+v:u(v)=0,\ B(v,v)\le2/3\}.
\tag{122.24}
$$

在这一个显式族内，下列七项等价：$|\lambda|=1$；EB$_{\ge1}$；EB3；全原PC1；全部 $p\in P_\lambda$ 满足 $B(p,p)=1$；以(122.2)、(122.23)定义的接触谓词 $\forall p\in P_0:D_p\cap I\ne\varnothing$；存在实线性双射 $\Phi:\operatorname{Herm}_3(\mathbb C)\to V$，满足 $\Phi(\mathrm{PSD}_3)=C_\lambda$、$u\Phi=\operatorname{Tr}$。在两个端点，127.1及129.1的全部单体入口 $\mathsf E_0$ 也满足；在内参数，该入口已因EB3失败而不满足。

对 $\lambda=1$ 定义实线性双射

$$
J_+(x)=\begin{pmatrix}
a_1&z_3&\overline z_2\\
\overline z_3&a_2&z_1\\
z_2&\overline z_1&a_3
\end{pmatrix},\qquad J_-=J_+R.
\tag{122.25}
$$

则 $J_+(C_1)=\mathrm{PSD}_3$、$J_-(C_{-1})=\mathrm{PSD}_3$，两者均保持原单位为迹。对任一端点，记 $\Phi=J_\pm^{-1}$，完整静态对应恰为127.9及129.6的下列字典，不含操作、复合或时间的自动结论。

证明。种子球(122.10)的单位球型在横向 $z_i$ 上为 $4|z_i|^2$，故其一半恰为 $2|z_i|^2$；在对角纯射线上 $B(p_i,p_j)=\delta_{ij}$，六个直和块相互正交。这与127.2的规范定义逐项相同，且

$$
B(w,x)=u(x),\quad B(w,w)=3,\qquad
B(x,x)=u(x)^2-2\sum_i\Delta_i(x).
\tag{122.26}
$$

因此对 $x\in K_\lambda$，$B(x,x)\le1$，而 $B(x-c,x-c)=B(x,x)-1/3$，给(122.24)的外包含。

为证明内包含，任取非零 $h\in C_\lambda^*$，唯一写为 $h=B(\widehat h,\cdot)$，令 $r=h(w)=u(\widehat h)>0$。将 $h$ 限制到三个实际种子锥，二阶迹配对的PSD判据给 $\widehat h$ 的每个对角坐标非负及每个 $\Delta_i(\widehat h)\ge0$。这里只取得三个二阶正性，并未认定 $\widehat h\in C_\lambda$。由(122.26)，

$$
B(\widehat h,\widehat h)\le r^2,\qquad
B(\widehat h-rw/3,\widehat h-rw/3)\le2r^2/3.
\tag{122.27}
$$

对 $u(v)=0,B(v,v)\le1/6$，Cauchy—Schwarz遂给

$$
h(c+v)=\frac r3+B(\widehat h-rw/3,v)
\ge\frac r3-\sqrt{\frac{2r^2}{3}}\sqrt{\frac16}=0.
\tag{122.28}
$$

零泛函当然也满足。闭凸锥的分离定理使 $c+v\in C_\lambda$，而其质量为一，完成内包含。这是固定内球论证在本显式族中的直接应用，不使用全锥自对偶。

当 $\lambda=1$ 时，$d_1=\det J_+$，且显式条件正是 $J_+$ 的全部主子式非负，故整个锥等于PSD像。由(122.3)，$\lambda=-1$ 时用 $J_-$ 得相同结论。两者 $u\Phi=\operatorname{Tr}$、$\Phi(I_3)=w$，并满足 $B(\Phi A,\Phi B)=\operatorname{Tr}(AB)$。以下矩阵事实是成熟谱理论及PSD对偶性的直接复用，用以明确这两个端点，而非另立一般量子分类定理。

| 原对象 | 端点同一 $\Phi$ 下的全部静态对应 |
| --- | --- |
| 锥、质量、全部混态 | $C_\lambda=\Phi(\mathrm{PSD}_3)$，含零及全部非负质量；$K_\lambda=\{\Phi\rho:\rho\succeq0,\operatorname{Tr}\rho=1\}$，保持全部有限凸组合 |
| 全部纯态 | $p_v=\Phi(vv^*/(v^*v))$，$v\ne0$，恰覆盖 $P_\lambda\cong\mathbb{CP}^2$；复射线表示同一纯点 |
| 整个效应区间与Born评价 | 每个原效应唯一对应 $0\preceq A\preceq I_3$，且反向全部这样的 $A$ 都是原效应；$f_A(\Phi\rho)=\operatorname{Tr}(A\rho)$，保持零、单位和补 |
| 全确认、least、完整排除 | 对 $v^*v=1$，全部确认矩阵是 $vv^*\oplus A_\perp$，$0\preceq A_\perp\preceq I_{v^\perp}$；least为 $vv^*$，$\mathcal T_{p_v}(\Phi\rho)=v^*\rho v$；整个 $D_{p_v}$ 为支撑在 $v^\perp$ 上的全部密度矩阵 |
| 原二元关系与三元框架 | $\mathcal T_{p_v}(p_z)=|v^*z|^2/((v^*v)(z^*z))$；原正交恰为复正交；每条原正交纯边有唯一第三纯点；三秩一确认效应和为 $u$，容量为三 |
| 数学POVM、谱和可观测量 | 任意有限 $f_j\ge0,\sum_jf_j=u$ 恰为全部有限PSD矩阵 $A_j$ 之和等于 $I_3$；全部原态有三项正交谱分解，含零权和重复谱；全部实线性可观测量对应Hermitian矩阵 |
| 共同尺、Jordan及压缩 | $B$ 为迹配对，运输 $(AB+BA)/2$ 得Jordan结构；$\Phi^{-1}T_i\Phi(A)=Q_iAQ_i$，$Q_i=I_3-E_{ii}$；全锥在 $B$ 下自对偶 |

具体地，迹一PSD矩阵若秩至少为二，可以在两个正本征值之间作非零小量的相反扰动，保持迹和PSD，故不是极点；秩一投影的任何凸分解都因其正交补上读数为零而被迫支撑在同一条射线，所以它是极点。这给全部纯态的覆盖。每个实线性效应由迹配对唯一表示；在所有秩一投影上检查非负及上界恰等价于 $0\preceq A\preceq I_3$，故上述字典使用的是整个原区间。

对 $v^*v=1$，若 $v^*Av=1$ 且 $0\preceq A\preceq I_3$，PSD矩阵 $I_3-A$ 在 $v$ 上的二次型为零，故 $(I_3-A)v=0$。于是 $A$ 在 $\mathbb Cv\oplus v^\perp$ 上正是表中块形，最低矩阵为 $vv^*$。对 $\rho\succeq0$，$v^*\rho v=0$ 同样等价于 $\rho v=0$，得到整个二能级密度球；再要求确认效应在这整个球上全零，迫使 $A_\perp=0$，所以完整确认唯一。反之该球的支撑正交补唯一决定 $\mathbb Cv$，所以端点也满足Inj。规范压缩公式由它保留的全部补块法向读数及定理122.3的唯一性得到。因此种子、联合分离、正性、EB3及Inj共同给两个端点的全部单体 $\mathsf E_0$ 入口。

在任一端点，所有纯态 $p$ 有 $B(p,p)=1$；所有角压缩为秩一PSD或零，故全原PC1成立；每个 $D_p$ 是完整三球，且

$$
\frac{w-p}{2}\in D_p,\qquad
B\left(\frac{w-p}{2}-c,\frac{w-p}{2}-c\right)=\frac16.
\tag{122.29}
$$

其完整确认效应唯一，所以 $P_0=P_\lambda$，接触谓词成立。连同(122.25)，这证明 $|\lambda|=1$ 推出所列其余六项。

对于任一内参数，推论122.6已否定两种EB及PC1；而

$$
B(X,X)=\frac{1+2s^2}{3}<1,\qquad
B(Y-c,Y-c)=\frac{2t^2}{3}>\frac16.
\tag{122.30}
$$

因为 $X\in P_0$ 且 $D_X=\{Y\}$，接触谓词也失败；全纯单位球面同样由 $X$ 失败。最后，任一保单位序同构通过对偶拉回双射整个效应区间，也双射所有确认效应、保留最低值并仿射双射完整排除集合。若存在所列PSD表示，成熟矩阵字典因而强迫EB3，内参数已被排除。因此其余六项均迫使参数位于端点，等价闭合。这些接触计算仍在本族原域内完成，没有在内参数上套用要求EB3的129条件链。两个端点的静态字典由同一原锥、同一 $u$ 和全部效应给出，数学角压缩与数学POVM尚不因此成为实际仪器。证毕。

### 122.8 原E0加IC0候选及未缩小的物理合同

**定义 122.8（保留的原条件候选与准确缺口）。** 在一个不预设(122.1)三次表示的一般原模型中，$\mathsf E_0$ 始终逐字取127.1和129.1：闭尖生成有限维原锥及严格正原单位、整个 $K,P,\mathcal E$ 和最低定义、全纯EB3、Inj、含 $P_0$ 顶点的实际原正交种子三角、该三角全部原零效应的联合分离 $\mathsf J_\triangle$、由全部原法向读数唯一确定的三个规范 $T_i$ 的全锥正性。它不包含PC1或IC0。共同 $B,w,c,I$ 仍是127.2及129.2从同一实际种子得到的对象；$I$ 的仿射半径平方是 $1/6$，在 $u=1$ 上相应原点范数平方是 $1/2$。

原候选不变：

$$
\begin{gathered}
\mathsf{PC1}:\quad \forall p\in P\ \exists i:\Delta_i(p)=0,\\
\mathsf{IC}_0:\quad \forall p\in P_0:\ D_p\cap I\ne\varnothing,\\
\text{完整候选}=\mathsf E_0+\mathsf{IC}_0
\quad\text{连同SAME_READBACK第127.10节全部原合同及其完整引用链}.
\end{gathered}
\tag{122.31}
$$

现有定理127.11、129.8及本卷(121.21)已经在同一 $\mathsf E_0$ 内给出IC0、全原PC1、全原PC3、全宽条件W及同原PSD$_3$/迹完整静态字典的条件等价；整个W下的Jordan分类、状态谱及谱唯一仍直接复用这些原引用，不作为本章新成果。本卷121.6已经给 $P_0=P$；121.7准确保留每个唯一完整确认效应尚需满足 $e_p(w)=1$ 的缺口。点态上 $D_p\cap I\ne\varnothing$ 等价于该点三个 $\Delta_i$ 全零，是点态PC3；一次压缩取零只是点态PC1，不能在一个孤立标签上偷用全域升级。

定理122.7只证明：若预先把原锥限制在(122.1)，则正维完整排除、全原PC1或上述接触谓词都会把参数限制为 $|\lambda|=1$。它没有给任意 $\mathsf E_0$ 锥一个三次多项式，也没有给它(122.1)的坐标表示；内参数恰因完整排除失败而不能成为 $\mathsf E_0$ 反模型。因此一般 $\mathsf E_0\Rightarrow\mathsf{PC1}/\mathsf{IC}_0$ 仍未由本章证明，完整同域反模型也未在这里产生。唯一完整确认与三个正种子压缩仍不自行给每个标签的正限制逆或全部确认中的least。条件静态字典和族内条件的简短写法均不构成普遍独立公理数目的减少。

127.10原合同在(122.31)中按其原量词保留，以下是该引用的操作范围，而非额外静态结论。

1. 同一原装饰元组 $\mathcal O$、共同来源域、全部中点实现、概率像紧性、全测试表及闭性、零／单位／补／有界倍增、重复标签与每种同中点实现、全部非负质量及零／次归一／不等质量、过程与参考各自完整相关联合输入均保留。原 $L,p,\omega,K,M$、两次同一读回、两实张成、全实关系、完整(83.8)、VI(89.13)全部两尺度等式、C2、整个 $G=1_E$、精确PRE之后整个H13及每个原资格态、活跃块严格负方向、共享总迹一、非活跃零质量与空活跃集均保持原义。操作映射 $p$ 与纯标签不混型。
2. 设备／事件／来源绑定、全部菜单分支、实际参考／副本／相关联合、记录／权限／控制、ready／flags、失败／拒绝／停止／销毁／返回、实际混合、原字、全部合法未来及每个中间切口，连同原生与细化消费者、terminal futures、联合有符号关系、细标签粗归组、记录后条件未来、source-adoption及资源合同全部保留。
3. 对每个有限 $N\ge1$，仍需实际 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成 $C_N$、严格正 $u_N=u^{\otimes N}$、整个 $K_N$、全部 $P_N$ 及整个效应区间；每个实际分块的最小／最大张量夹逼、产品配对、严格张量单位、因子置换及逆的正性、规范重括号和不连续位置分块运输均按(Q127.35)。整个实际 $S_2$ 按(Q127.36)覆盖任意产品或纠缠纯点、任意有限凸族、全部非负权、零权与重复标签。低二份 $q=1,2$ 的least／谱性／正面投影及保纯到Jordan桥、唯一实际自复合的直和扇区与秩／实维乘法限制、同一实际两因子的产品正规形仍分别供应。
4. 三份资源 $\mathsf F_{\max}$ 仍精确要求(Q127.37)的同一最大复块 $L\ge2$、同一含相位正交基、实际 $g_r=\sum_a|a\rangle_r|a\rangle_r|a\rangle_r$、$\Delta_r=|g_r\rangle\langle g_r|\in C_3$、$u_3(\Delta_r)=L$、其余扇区零和归一原源 $\Delta_r/L$，不预付三份纯性或实际制备；全经典 $L=1$ 分支按原定理处理。复三能级支路的 $L=3$、二三份秩九及二十七与全部更高有限次数都保留，不将单体EB3推广为高阶整个排除条件。
5. 全旁观正性(Q127.38)量化每个 $b\ge0$ 及任意含纠缠共同输入；只有整个有限层级及共同表示已给，才沿原Choi桥识别通常CP、矩形跨扇区Kraus及逐输入TP／TNI预算。实际事件仍需完整提升、实际探针和相容核，事件饱和另行供应；共同输入预算、接线、记录、粗粒化和校准负责同族仪器。严格正质量分支才条件归一，零质量不强定归一条件态；Lüders另需同一分支的锐效应、接受态中性与输出校准。数学效应、正压缩和POVM没有替代这些要求。
6. 物理钟、实际动态来源、连续齐次可逆时间群及单位仍分别供应。另给同载体全实时间连续保单位锥自同构群才有相应生成元；在重构复块中另给保迹酉时间族才沿(Q127.39)使用Hamiltonian共轭及交换子形式。量词仍覆盖全部原输入和实际时间，$H$ 的标量平移、时间重标和生成元尺度边界保留；实际Hamiltonian、能量识别与标定、数值 $\hbar$、时空和物理空间维数均未由本章静态端点判据产生。

这些合同与原先裸EB3到Inj、实际种子、联合分离及三个全锥正压缩的入口桥均保持各自范围。本章结算的是一个明确三元耦合形变为何在完整二元排除处失败，而非完整量子物理的自动完成。

## 追加锚（本行以下为增补区）

## 123. 收缩实三线性三次族的整排除面与有限方向刚性

### 123.1 三条实边平面与完整原域

**定义 123.1（收缩三线性族）。** 令 $L_1,L_2,L_3$ 为三个带指定欧氏内积的实二维空间，$V=\mathbb R^3\oplus L_1\oplus L_2\oplus L_3$。写 $x=(a_1,a_2,a_3;z_1,z_2,z_3)$，其中 $z_i$ 对应补指标 $jk$ 的边。取任意实三线性型 $\tau:L_1\times L_2\times L_3\to\mathbb R$，要求

$$
|\tau(z_1,z_2,z_3)|\le |z_1||z_2||z_3|
\quad(z_i\in L_i).
\tag{123.1}
$$

不要求 $\tau$ 对称。令

$$
\begin{gathered}
u(x)=a_1+a_2+a_3,\qquad
p_i=(\delta_{i1},\delta_{i2},\delta_{i3};0,0,0),\qquad
w=p_1+p_2+p_3,\\
\Delta_i(x)=a_ja_k-|z_i|^2\quad(\{i,j,k\}=\{1,2,3\}),\\
d_\tau(x)=a_1a_2a_3-\sum_i a_i|z_i|^2+2\tau(z_1,z_2,z_3),\\
C_\tau=\{x:a_i\ge0,\ \Delta_i(x)\ge0\ (i=1,2,3),\ d_\tau(x)\ge0\}.
\end{gathered}
\tag{123.2}
$$

始终使用整个 $C_\tau$，以及

$$
\begin{gathered}
K_\tau=C_\tau\cap\{u=1\},\qquad P_\tau=\operatorname{ext}K_\tau,
\qquad \mathcal E_\tau=[0,u]_{C_\tau^*},\\
\mathcal F_p=\{f\in\mathcal E_\tau:f(p)=1\},\qquad
\mathcal T_p(x)=\min_{f\in\mathcal F_p}f(x)\quad(x\in C_\tau),\\
D_p=\{x\in K_\tau:\mathcal T_p(x)=0\},\qquad
\mathcal A_p=\{f\in\mathcal F_p:f|_{D_p}=0\},\qquad
P_0=\{p\in P_\tau:\mathcal A_p\text{ 为单点}\},\\
N_p=\{h\in C_\tau^*:h(p)=0\},\qquad
p\perp q\ \Longleftrightarrow\ \exists f\in\mathcal E_\tau:
f(p)=1,\ f(q)=0.
\end{gathered}
\tag{123.3}
$$

最后一行用于纯端点；补效应给其对称性。标量最低函数 $\mathcal T_p$ 与线性种子压缩 $T_i$ 不同型。EB3表示每个原纯标签的整个 $D_p$ 仿射同构于整个闭实三球；EB$_{\ge1}$ 允许各标签有不同的正整数球维数。二者都不把所选效应的零面预先等同于 $D_p$。这里不输入矩阵表示、Pair、least、全纯互易或任何效应子菜单。

本章所称125—131及127.10均指[SAME_READBACK][Q123SR]；本卷121指[完整确认章节][Q123BV]；VII103.2指[完整排除面第七卷][Q123VII]。这些公开定义和条件结果按各自原前件复用。122的标量定义是(123.1)的一条子族；以下涉及一般 $\tau$ 的承重步骤均在本章证明。

### 123.2 整个集合的合法性与不变的二元窗口

**定理 123.2（整个闭双曲锥）。** 对每个满足(123.1)的 $\tau$，$d_\tau$ 关于向量 $w$ 双曲，整个 $C_\tau$ 恰为该方向的闭双曲锥。因此 $C_\tau$ 闭、凸、尖且生成 $V$，$w\in\operatorname{int}C_\tau$，$u$ 在非零锥元上严格正。$K_\tau$ 为紧凸基，$\mathcal E_\tau$ 紧，(123.3)中的最小值达到。

证明。固定任意 $x\in V$，置 $r_i=|z_i|$。若 $r_1r_2r_3>0$，由(123.1)选实数 $\theta$，使 $r_1r_2r_3\cos\theta=\tau(z_1,z_2,z_3)$。选择模长分别为 $r_i$ 的三个复数 $\xi_i$，使其乘积为 $r_1r_2r_3e^{\mathrm i\theta}$。若某个 $r_i=0$，三线性使 $\tau=0$，任取相应模长的 $\xi_i$ 即可。对这个固定 $x$ 令

$$
H_x=\begin{pmatrix}
a_1&\xi_3&\overline{\xi_2}\\
\overline{\xi_3}&a_2&\xi_1\\
\xi_2&\overline{\xi_1}&a_3
\end{pmatrix}.
\tag{123.4}
$$

行列式展开给出整个单变量恒等式

$$
d_\tau(x+tw)=\det(H_x+tI_3)\quad(t\in\mathbb R).
\tag{123.5}
$$

Hermitian矩阵的本征值为实数，故右侧全部根为实数；$d_\tau(w)=1$。这里的双曲方向是 $w\in V$，不是泛函 $u\in V^*$。所选 $H_x$ 可随 $x$ 改变；(123.5)没有提供关于 $x$ 的共同线性矩阵表示。

采用[Renegar §2][Q123R]的记号，闭双曲锥 $\Lambda_+$ 由(123.5)的根全不正刻画，等价于 $H_x\succeq0$。Hermitian矩阵全部主子式非负的成熟判据，在此恰为三个 $a_i\ge0$、三个 $\Delta_i\ge0$ 和 $d_\tau\ge0$。因此 $\Lambda_+=C_\tau$，不是整个 $\{d_\tau\ge0\}$。Renegar Proposition 1定位含 $w$ 的开分支，Theorem 2及其闭包结论给凸性；Theorem 3保证换为同一开锥中的方向时分支不变。这里只消费成熟双曲性工具，不另作一般行列式表示推断。

齐次不等式给闭锥；全部不等式在 $w$ 处严格，故其满维并生成 $V$。若 $x\in C_\tau$ 且 $u(x)=0$，非负的三个 $a_i$ 全零，二阶条件再使全部 $z_i=0$。故 $u$ 严格正；同一观察证明锥尖。归一后 $0\le a_i\le1$ 且 $|z_i|^2\le a_ja_k\le1/4$，所以基底紧。取 $K_\tau$ 中一组张成 $V$ 的向量，任一 $f\in[0,u]$ 在这组向量上的读数都在零一之间，因此完整效应区间闭且有界。$\mathcal F_p$ 是其中含 $u$ 的闭子集，最小值达到。零质量情形只有零向量，亦被上述论证覆盖。证毕。

**定理 123.3（三个对角种子的全部确认与正压缩）。** 对任意(123.1)，三个 $p_i$ 都是原纯点。令 $\pi_i x=(a_j,a_k,z_i)$，并把

$$
\mathscr L_i=\{(b,c,z):b,c\ge0,\ |z|^2\le bc\},\qquad
\upsilon_i(b,c,z)=b+c
\tag{123.6}
$$

零延拓嵌入 $M_i=\{a_i=0,z_j=z_k=0\}\subset V$。则

$$
\begin{gathered}
N_{p_i}=\pi_i^*(\mathscr L_i^*),\qquad
\operatorname{span}N_{p_i}=\pi_i^*((\mathbb R^2\oplus L_i)^*),\\
\mathcal F_{p_i}=
\{a_i+h\circ\pi_i:h\in[0,\upsilon_i]_{\mathscr L_i^*}\},\qquad
\mathcal T_{p_i}(x)=a_i(x)\quad(x\in C_\tau),\\
D_{p_i}=\{x\in K_\tau:a_i=0\}
=\{a_i=0,z_j=z_k=0,a_j+a_k=1,\ |z_i|^2\le a_ja_k\},\\
\mathcal A_{p_i}=\{a_i\}.
\end{gathered}
\tag{123.7}
$$

每个 $D_{p_i}$ 是完整三球。将 $a_i,z_j,z_k$ 置零、保留余下块的映射 $T_i$，是取值于 $M_i$ 且满足 $h(T_i x)=h(x)$（$h\in N_{p_i},\ x\in V$）的唯一实线性映射。其像恰为 $M_i$，$T_i^2=T_i$，且 $T_i(C_\tau)\subset C_\tau$、$uT_i=u-a_i$。三个种子的全部原零效应联合分离 $V$，三个效应 $a_i$ 和为 $u$。

证明。对角坐标非负，故 $p_i$ 的任何归一凸分解都迫使其余两对角坐标为零；二阶条件再清零全部边，得到纯性。下面直接核对一般 $\tau$ 所需的全部确认公式。若 $h\in N_{p_1}$，其 $a_1$ 系数为零。对任意单位 $\eta\in L_3$，整个曲线

$$
(1,t^2,0;0,0,t\eta)\in C_\tau\quad(t\in\mathbb R)
\tag{123.8}
$$

成立，因为至少两条边为零，三次式为零。$h\ge0$ 对正负小 $t$ 同时成立，故 $h$ 的 $z_3$ 系数为零。曲线 $(1,0,t^2;0,t\eta,0)$ 同理清零 $z_2$ 系数。因此 $h$ 只读 $\pi_1$。整个 $C_\tau$ 的 $\pi_1$ 像是 $\mathscr L_1$，且每个块的零延拓都属于 $C_\tau$；正性遂等价于块正性，给出法向公式。其线性张成是整个四维块对偶。其余指标同理，不要求 $\tau$ 具有置换对称性。

对 $f\in\mathcal F_{p_i}$，$u-f$ 在 $N_{p_i}$ 中，故 $f=a_i+h\pi_i$。在完整零延拓块上检查 $f\ge0$、$u-f\ge0$，恰给 $0\le h\le\upsilon_i$。反向，这两个块不等式也在整个 $C_\tau$ 上保证效应资格。$h=0$ 已可取，全部其他 $h\pi_i$ 非负，所以 $a_i$ 是全确认族的least，得到最低函数和整个 $D_{p_i}$。$a_i=0$ 时，二阶条件清零另两条边；坐标 $(a_j-a_k,2z_i)$ 把归一零面仿射双射到整个单位三球。它是 $K_\tau$ 的暴露面，其球面全部是原纯点。确认效应还要在整个球上读零，就须 $h=0$，得 $\mathcal A_{p_i}$。

记块零延拓为 $\iota_i:\mathbb R^2\oplus L_i\to M_i$，则 $T_i=\iota_i\pi_i$ 且 $\pi_i\iota_i=I$，故其像恰为 $M_i$，并在 $M_i$ 上恒等，得到投影性质。$h\in N_{p_i}$ 只读保留块，所以 $hT_i=h$。若另一实线性映射 $S:V\to M_i$ 也保持全部这些读数，则 $Sx-T_i x\in M_i$ 被 $\operatorname{span}N_{p_i}$ 中每个泛函读成零；(123.7)的四维块对偶在 $M_i$ 上分离向量，故 $Sx=T_i x$ 对所有 $x\in V$ 成立。这证明的是指定像空间内的唯一性。投影的像块仍属 $\mathscr L_i$，零延拓正性给全锥正性；保留对角坐标之和给 $uT_i=u-a_i$。三个法向张成合起来是 $V^*$；任一非零正法向除以其在紧基底上的正最大值即成为原零效应，所以联合分离确实使用原效应。证毕。

### 123.3 边缘标签的准确零面与点态整球识别

**定理 123.4（饱和子空间决定暴露面的球维数）。** 对 $L_1$ 中任意单位向量 $v$，定义两个实际种子球面纯点

$$
q_v=(0,1/2,1/2;v/2,0,0),\qquad
r_v=(0,1/2,1/2;-v/2,0,0).
\tag{123.9}
$$

唯一实线性矩阵束 $M_v:L_3\to L_2$ 由

$$
\tau(v,z_2,z_3)=\langle z_2,M_vz_3\rangle
\tag{123.10}
$$

定义，且 $v\mapsto M_v$ 实线性、$\|M_v\|\le|v|$。置 $E_v=\ker(I-M_v^{\mathsf T}M_v)$、$m_v=\dim E_v$。原确认效应

$$
e_{q_v}(x)=\frac{a_2+a_3}{2}+\langle v,z_1\rangle
\tag{123.11}
$$

的整个归一零面 $F_v=K_\tau\cap\ker e_{q_v}$ 恰为

$$
\begin{gathered}
a_1=a\ge0,\quad a_2=a_3=b\ge0,\quad a+2b=1,\quad z_1=-bv,\\
z_3=z\in E_v,\qquad z_2=-M_vz,\qquad |z|^2\le ab.
\end{gathered}
\tag{123.12}
$$

它包含不同的原纯点 $p_1,r_v$，是非点暴露真面，仿射同构于整个闭 $B^{1+m_v}$，且总有 $F_v\subseteq D_{q_v}$。若仅对这个指定的 $q_v$ 另外知道整个 $D_{q_v}$ 是某个正维仿射闭球，则已经有

$$
D_{q_v}=F_v,\qquad \dim_{\rm aff}D_{q_v}=1+m_v.
\tag{123.13}
$$

此识别不需要其他标签的EB条件，也不需要Pair、Inj、PR或least。

证明。由(123.1)对 $z_2$ 取单位球上的上确界，得到 $\|M_vz_3\|\le|v||z_3|$；三线性和有限维Riesz配对给唯一性与实线性。二阶条件保证

$$
\frac{a_2+a_3}{2}\ge\sqrt{a_2a_3}\ge|z_1|
\ge-\langle v,z_1\rangle.
\tag{123.14}
$$

同时 $|\langle v,z_1\rangle|\le(a_2+a_3)/2$，所以 $0\le e_{q_v}\le a_2+a_3\le u$ 于整个锥。它在 $q_v$ 取一，确属整个原确认族。其零集迫使(123.14)全部取等，得到 $a_2=a_3=b$、$z_1=-bv$。代入三次式得

$$
\begin{aligned}
d_\tau(x)&=-b\bigl(|z_2|^2+|z_3|^2
                         +2\langle z_2,M_vz_3\rangle\bigr),\\
|z_2|^2+|z_3|^2+2\langle z_2,M_vz_3\rangle
&=|z_2+M_vz_3|^2
 +\langle z_3,(I-M_v^{\mathsf T}M_v)z_3\rangle\ge0.
\end{aligned}
\tag{123.15}
$$

若 $b>0$，$d_\tau\ge0$ 迫使两个非负项全零，所以 $z_3\in E_v$、$z_2=-M_vz_3$。此时二者等长，另外两条二阶条件恰为 $|z_3|^2\le ab$。若 $b=0$，二阶条件直接给 $z_2=z_3=0$，仍是(123.12)。若 $a=0$，同一条件也直接给 $z=0$，不需要除以 $a$。反向将(123.12)逐项代回，全部约束成立。去掉 $a+2b=1$ 即得到整个锥零面的同一参数式；零质量迫使 $a=b=0,z=0$，没有遗失零锥元。

归一后 $a=1-2b$，故

$$
|z|^2+2(b-1/4)^2\le1/8.
\tag{123.16}
$$

参数到 $V$ 的映射在 $\mathbb R\oplus E_v$ 上单射，且该椭球有相对内部。因此仿射维数准确为 $1+m_v$：$m_v=0,1,2$ 分别给线段、二维圆盘和三球。由于 $e_{q_v}$ 是确认候选，$0\le\mathcal T_{q_v}\le e_{q_v}$，得 $F_v\subset D_{q_v}$；这一步没有把 $e_{q_v}$ 称为least。

最后说明(123.13)为何只需点态前件。[VII103.2][Q123VII]证明的第一段在单个标签上就有效：若整个 $D_p$ 是球，取其自身中心 $c_p$，由 $\mathcal T_p(c_p)=0$ 选 $f\in\mathcal F_p$ 使 $f(c_p)=0$。对每个 $y\in D_p$，反射 $2c_p-y$ 仍在 $D_p$，非负性给

$$
0=2f(c_p)=f(y)+f(2c_p-y),
\qquad f(y)=0.
\tag{123.17}
$$

反向，$f(y)=0$ 自身就是 $y\in D_p$ 的原见证，所以 $D_p=K_\tau\cap\ker f$。因此这个指定的 $D_p$ 已是原暴露真面。现在 $F_v$ 是包含于 $D_{q_v}$ 的原非点面，也是该球的面；严格凸球的非空真面只有单点，包括一维球情形。故 $F_v=D_{q_v}$。反射中心始终是该球自己的中心，未假设共同球心或与固定内球接触。

若采用全局EB$_{\ge1}$下的另一条既有论证，VII103.2先将非点真面 $F_v$ 写成某个 $D_s$。极大的是这个被包含的 $F_v=D_s$；由 $F_v\subseteq D_{q_v}\subsetneq K_\tau$ 才得到相等。不能仅用包含它的 $D_{q_v}$ 极大来反推相等。点态论证已经免去这项全局面分类前件。证毕。

### 123.4 两个独立边缘方向已经足够

**定理 123.5（完整三球的有限检测与全族正规形）。** 固定 $L_1$ 的正交单位基 $e_1,e_2$，令 $e_+=(e_1+e_2)/\sqrt2$。在定义123.1的整个族中，以下六项等价：

1. 两个完整排除集 $D_{q_{e_1}},D_{q_{e_2}}$ 都是仿射闭三球。
2. 三个完整排除集 $D_{q_{e_1}},D_{q_{e_2}},D_{q_{e_+}}$ 都是仿射闭三球。
3. 每个单位 $v\in L_1$ 都有 $M_v^{\mathsf T}M_v=I$。
4. 存在三个正交同构 $O_i:\mathbb R^2\to L_i$，把标准平面识别为 $\mathbb C$ 后满足

$$
\tau(O_1\xi_1,O_2\xi_2,O_3\xi_3)
=\operatorname{Re}(\xi_1\xi_2\xi_3)
\quad(\xi_i\in\mathbb C).
\tag{123.18}
$$

5. 存在实线性双射 $\Psi:V\to\operatorname{Herm}_3(\mathbb C)$，满足 $\Psi(C_\tau)=\mathrm{PSD}_3$、$\operatorname{Tr}\Psi=u$、$\Psi(w)=I_3$。
6. 全局EB3。

第1项还可换成任意两个线性无关单位向量 $v_1,v_2$ 的相同完整三球检验。这些标签都是同一颗 $D_{p_1}$ 的边缘纯点，不是三个对角种子 $p_1,p_2,p_3$。

证明。先证第1项到第3项，并同时说明两个任意独立方向的版本。由定理123.4，两个完整三球分别迫使 $m_{v_i}=2$，即 $M_{v_i}^{\mathsf T}M_{v_i}=I$。对任意固定 $z\in L_3$，考虑 $L_1$ 上的二次型

$$
Q_z(v)=|v|^2|z|^2-|M_vz|^2\ge0.
\tag{123.19}
$$

非负性正是全方向收缩(123.1)的后果；它不是新增的球面前件。$Q_z(v_1)=Q_z(v_2)=0$。在基 $v_1,v_2$ 中写成 $Q_z(sv_1+tv_2)$，两个平方项均为零，只剩 $2cst$；对所有实 $s,t$ 非负迫使 $c=0$。因此 $Q_z$ 恒零。$z$ 任意，故

$$
M_v^{\mathsf T}M_v=|v|^2I\quad(v\in L_1).
\tag{123.20}
$$

这就证明第3项。特别地，第2项中的第三个检测在已给全方向收缩的本族内可以省去。若直接使用三个方向，置 $A=M_{e_1}$、$B=M_{e_2}$，三次饱和也立即给

$$
A^{\mathsf T}A=B^{\mathsf T}B=I,\qquad
A^{\mathsf T}B+B^{\mathsf T}A=0.
\tag{123.21}
$$

两次检测的证明则先用(123.19)支付最后一式。这里有限性来自一个已知次数的实线性矩阵束和全方向范数界，不能移植成任意原模型的有限检测原则。

现给第3项到第4项的显式二维代数。任选 $L_2,L_3$ 的正交坐标，$A,B$ 均为二阶实正交矩阵。令 $C=A^{\mathsf T}B$；由(123.21)，$C$ 同时正交且斜对称，故

$$
J=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad
C=\varepsilon J\quad(\varepsilon\in\{-1,1\}),\qquad
M_{(x,y)}=A(xI+\varepsilon yJ).
\tag{123.22}
$$

理由只是二阶斜对称矩阵具有 $cJ$ 形式，正交性迫使 $c^2=1$。令

$$
K=\operatorname{diag}(1,-1),\qquad
O_1=\operatorname{diag}(1,-\varepsilon),\qquad O_2=A,\qquad O_3=K.
\tag{123.23}
$$

这些矩阵与前面任选的正交坐标复合，给三个原平面上的所需同构。新矩阵束为

$$
O_2^{\mathsf T}M_{O_1(x,y)}O_3=(xI-yJ)K.
\tag{123.24}
$$

若 $\xi_1=x+\mathrm iy$、$\xi_2=s+\mathrm it$、$\xi_3=h+\mathrm ik$，右侧与 $\xi_2$ 的实内积是 $s(xh-yk)+t(-yh-xk)=\operatorname{Re}(\xi_1\xi_2\xi_3)$，得到(123.18)。这是成熟 $[2,2,2]$ 正交乘法事实的直接二维展开，不调用更高维Hurwitz分类。

为证第4项到第5项，令 $L_O(a;\xi)=(a;O_1\xi_1,O_2\xi_2,O_3\xi_3)$，并定义

$$
H(a;\xi)=\begin{pmatrix}
a_1&\xi_3&\overline{\xi_2}\\
\overline{\xi_3}&a_2&\xi_1\\
\xi_2&\overline{\xi_1}&a_3
\end{pmatrix},\qquad
\Psi_O=H\circ L_O^{-1},\qquad \Phi_O=\Psi_O^{-1}.
\tag{123.25}
$$

这一次 $H$ 是共同的实线性双射。正交变换保持全部边长，(123.18)保持整个三次式，故(123.2)的全部不等式恰对应 $H$ 的全部主子式非负。于是 $\Psi_O(C_\tau)=\mathrm{PSD}_3$、$\operatorname{Tr}\Psi_O=u$、$\Psi_O(w)=I_3$，得到第5项。它在原态空间上是保基锥同构，其对偶是保持原效应单位的序同构。

第5项到第6项：任取第5项给出的 $\Psi$，令 $\Phi=\Psi^{-1}$。定理123.6的(123.26)—(123.27)仅以这三个同构恒等式为前件，对这个任意给定的 $\Psi$ 运输整个对偶效应区间和全部确认候选的最小值，得到每个原纯标签的完整 $D_p$ 为三球，故有第6项；这一步不要求 $\Psi$ 采用(123.25)的坐标构造。第6项立即给第2项，第2项给第1项，等价链闭合。整个证明的非成熟消费者是原完整排除球到(123.20)的有限检测；其余正交乘法和PSD端点均按成熟工具复用。证毕。

### 123.5 同一个映射保留全部纯射线、效应与最低值

**定理 123.6（全域运输的准确静态后果）。** 设给定任意实线性双射 $\Psi:V\to\operatorname{Herm}_3(\mathbb C)$，满足 $\Psi(C_\tau)=\mathrm{PSD}_3$、$\operatorname{Tr}\Psi=u$、$\Psi(w)=I_3$，令 $\Phi=\Psi^{-1}$。则对这个给定的同构有

$$
\begin{gathered}
C_\tau=\Phi(\mathrm{PSD}_3),\qquad
K_\tau=\{\Phi\rho:\rho\succeq0,\operatorname{Tr}\rho=1\},\\
P_\tau=\{p_\psi=\Phi(\psi\psi^*/(\psi^*\psi)):
\psi\in\mathbb C^3\setminus\{0\}\}\cong\mathbb{CP}^2,\\
\mathcal E_\tau=\{f_A:0\preceq A\preceq I_3\},\qquad
f_A(\Phi X)=\operatorname{Tr}(AX).
\end{gathered}
\tag{123.26}
$$

全部非零纯锥射线是 $\mathbb R_+\Phi(\psi\psi^*)$。对单位 $\psi$，记 $P_\psi=\psi\psi^*$，则全部确认矩阵和原最低值为

$$
\begin{gathered}
\mathcal F_{p_\psi}\longleftrightarrow
\{P_\psi\oplus A_\perp:0\preceq A_\perp\preceq I_{\psi^\perp}\},\\
\mathcal T_{p_\psi}(\Phi X)=\operatorname{Tr}(P_\psi X)
\quad(X\succeq0),\\
D_{p_\psi}=\{\Phi\rho:\rho\succeq0,\operatorname{Tr}\rho=1,
\rho\psi=0\},\qquad
\mathcal A_{p_\psi}=\{f_{P_\psi}\}.
\end{gathered}
\tag{123.27}
$$

因而每个完整 $D_p$ 是三球，Inj成立。全部原纯比较是归一复内积模方，原正交恰为复正交。整个静态字典继续沿127.9、129.8和VIII113.7—113.9复用，包括全部有限数学POVM、谱、Jordan乘积与数学压缩，不重立这些成熟端点为新的量子分类。

关于指定种子的坐标字典另作条件陈述：若给定满足(123.18)的三个正交同构 $O_i$，则(123.25)的 $\Psi_O,\Phi_O$ 还满足(123.28)及下述角压缩公式。这项坐标陈述与任意给定 $\Psi$ 的(123.26)—(123.27)分别按各自前件证明。

证明。由所给同构，$u\Phi=\operatorname{Tr}$、$\Phi(I_3)=w$。保基实线性锥同构仿射双射整个归一基并保留极点。PSD基底的极点恰为秩一投影：两个正本征值允许相反小扰动，秩至少二者不极端；秩一投影的凸分解则由正交补上的零二次型迫使全部正项支撑于同一复线。因此(123.26)覆盖全部原纯点与纯射线。

对任意原实线性泛函 $f$，$f\Phi$ 在全部Hermitian空间上由唯一矩阵 $A$ 作迹配对。反向定义 $f_A(x)=\operatorname{Tr}(A\Psi x)$（$x\in V$），得到全部Hermitian矩阵与整个 $V^*$ 的实线性双射。因为 $\Psi(C_\tau)=\mathrm{PSD}_3$，$f_A\in C_\tau^*$ 当且仅当 $\operatorname{Tr}(AX)\ge0$ 对每个 $X\succeq0$ 成立；用全部 $X=\eta\eta^*$ 检查，这又当且仅当 $A\succeq0$。故这个双射是整个对偶锥的序同构，且 $f_{I_3}=u$，于是 $0\le f_A\le u$ 当且仅当 $0\preceq A\preceq I_3$。它保持评价、零、单位、补和所有有限非负和，给出(123.26)的完整效应区间。

现在取任意原纯点 $p=p_\psi$、单位 $\psi$，以及任意原锥输入 $x=\Phi X$、$X\succeq0$。全部确认候选恰对应 $0\preceq A\preceq I_3$ 且 $\psi^*A\psi=1$，所以原定义的最小值准确为

$$
\mathcal T_{p_\psi}(\Phi X)
=\min_{\substack{0\preceq A\preceq I_3\\ \psi^*A\psi=1}}
\operatorname{Tr}(AX).
$$

这里候选集是整个原 $\mathcal F_{p_\psi}$ 的双射像；其最小值达到，也可直接由矩阵区间的紧性得到。

成熟PSD事实还给出显式最低公式：若 $0\preceq A\preceq I_3$ 且 $\psi^*A\psi=1$，则 $(I_3-A)\psi=0$，所以 $A=P_\psi\oplus A_\perp$。反向每个这样的块矩阵都确认该纯点，且 $A_\perp=0$ 可取。所有这些 $A-P_\psi$ 都为PSD，故 $\operatorname{Tr}(AX)\ge\operatorname{Tr}(P_\psi X)$ 对所有 $X\succeq0$ 成立；$A=P_\psi$ 同时达到下界。因此 $f_{P_\psi}$ 是原全确认族的least，并得到(123.27)的最低公式。$X\succeq0$ 时 $\psi^*X\psi=0$ 等价于 $X\psi=0$，所以最低定义的整个 $D_{p_\psi}$ 恰为 $\psi^\perp$ 上全部密度矩阵的 $\Phi$ 像，包括其混态内部。这是整个二维复密度矩阵闭三球，故对所有原纯标签得到EB3。完整确认还要在这个整球上全零，迫使 $A_\perp=0$，给最后一个单点公式。补空间唯一决定原复线，故Inj成立。以上全纯点、全效应和完整排除公式对任意给定的 $\Psi$ 均成立，且线性运输保持所有有限凸组合、所有非负质量及零输入。

对种子坐标的条件陈述，使用所给满足(123.18)的 $O_i$ 和(123.25)的指定构造 $\Psi_O=H\circ L_O^{-1}$、$\Phi_O=\Psi_O^{-1}$。该构造逐坐标满足本定理的三个同构恒等式，所以上述(123.26)—(123.27)同样适用于这对映射。它们还满足 $\Psi_O(p_i)=E_{ii}$，并由保留各对角坐标和各边内积得到种子定义的共同型

$$
B(x,y)=\sum_i a_i b_i+2\sum_i\langle z_i,\zeta_i\rangle,
\qquad B(\Phi_O X,\Phi_O Y)=\operatorname{Tr}(XY).
\tag{123.28}
$$

因此在这同一对 $\Psi_O,\Phi_O$ 下，原效应空间、全确认最低函数、纯边、完整排除球及共同尺相容。特别是对所有 $X\in\operatorname{Herm}_3(\mathbb C)$，$\Psi_O T_i\Phi_O(X)=Q_iXQ_i$，$Q_i=I_3-E_{ii}$，因为(123.25)把 $T_i$ 的坐标置零恰变为把矩阵第 $i$ 行及第 $i$ 列置零；单位、共同三框架、数学POVM和Jordan结构可直接使用所引端点字典。由正交同构保持各 $a_i,|z_i|$，矩阵秩一时三个 $\Delta_i$ 全零，故同一种子的全原PC3及PC1成立。这里没有把任何数学POVM、正压缩或锥同构识别成实际仪器。证毕。

### 123.6 标量子族与三个对角种子的准确区别

**推论 123.7（标量族的一次边缘三球检测）。** 对 $\tau_\lambda=\lambda\operatorname{Re}(z_1z_2z_3)$、$|\lambda|\le1$，任意固定单位 $v\in L_1$ 都满足

$$
M_v^{\mathsf T}M_v=\lambda^2I,\qquad
m_v=\begin{cases}0,&|\lambda|<1,\\2,&|\lambda|=1.\end{cases}
\tag{123.29}
$$

因此在此子族，单个指定边缘标签的整个 $D_{q_v}$ 为三球，当且仅当 $|\lambda|=1$；内参数的每个相应暴露面 $F_v$ 都是 $[p_1,r_v]$。与此同时，整个一般族中三个对角种子的完整 $D_{p_i}$ 始终都是三球，故只检测它们不足以得到正规形。

证明。标准坐标中 $M_{(x,y)}=\lambda(xI-yJ)K$；对单位 $v$ 得(123.29)，再用定理123.4。如果内参数的指定 $D_{q_v}$ 是三球，点态识别便把它等于一维 $F_v$，矛盾。端点由定理123.5—123.6给整个三球。一般族的对角种子结论已由定理123.3独立证明；例如 $\tau=0$ 的这些种子全部通过检验，而所有 $M_v=0$，故不能满足定理123.5的正规形。

这里对内参数只取得边缘完整三球条件的失败。若只假设指定 $D_{q_v}$ 是某个正维球，(123.13)允许它是线段，不能以维数矛盾排除。故此简短消费者没有加强122.5—122.6所述内参数EB$_{\ge1}$排除结论；那里更强的单点排除依赖其完整确认计算，本章一般 $\tau$ 的证明不以该计算为前提。也没有在不满足点态球前件时声称 $D_{q_v}=[p_1,r_v]$。证毕。

### 123.7 文献归属与有限域的新增消费者

**约定 123.8（成熟工具及本章的范围）。** 本章采用 `repo-derived` 的纸面综合归属。三次双曲锥、二维正交乘法及PSD量子字典都已有成熟来源；新增消费者是把这个收缩实三线性族的整个原效应域接到准确零面(123.12)，只在指定标签的整球前件下识别完整最低排除，再由两个独立边缘标签得到整个族的正规形。两个方向到全部方向使用非负二次型(123.19)，不把有限采样当作一般无限条件的替代。

| 来源 | 准确使用范围 |
| --- | --- |
| Renegar，*Hyperbolic Programs, and Their Derivative Relaxations*，原始稿§2，Proposition 1、Theorems 2—3 [Q123R] | 含双曲方向的连通分支、闭包、凸性及内方向不变性；不提供本章全效应排除或共同线性三阶Hermitian表示 |
| Saunderson，*Certifying polynomial non-negativity via hyperbolic optimization*，arXiv:1904.00491v2，§5.1、Proposition 5.1 [Q123S] | 对准确正规式 $s^3-3s|y|^2+2q(y)$，关于 $e_0$ 的双曲性等价于 $\max_{|y|=1}|q(y)|\le1$；说明有界三次型与双曲性的关系已有先例，不供应完整 $D_p$ 或有限边缘检测 |
| Chi—Wang，*Orthogonal multiplications of type $[3,4,p],p\le12$*，arXiv:1705.04762v1，Introduction及§2 [Q123CW] | 正交乘法是满足 $|F(x,y)|=|x||y|$ 的双线性映射，采用定义域和值域正交等价；其引言明确回溯Hurwitz的 $[l,l,l]$ 分类。本章只用已展开的 $[2,2,2]$ 情形，不将复数乘法分类计为新成果 |
| VII103.2 [Q123VII] | 中心反射给原完整排除面的暴露性；本章只抽取该证明对指定标签有效的部分，再消费精确 $F_v$；不输入Pair |
| SAME_READBACK125—131、本卷121及VIII113.7—113.9 [Q123SR] [Q123BV] [Q123EVIII] | 固定完整入口中的种子、共同尺、确认唯一、PC1／IC0／W条件链及全部静态字典；既有密度、法向层和状态谱不重证、不计新成果 |

限定于这些原文及有关三次双曲型、实三线性耦合、正交乘法的有界来源范围，未见与(123.12)—(123.20)这个全效应有限检测消费者精确相同的条目；这不构成全球新颖性或历史优先权判断。VII106.12已经在其W及相应等价条件下得到原效应侧的内生三次双曲分支；它不表示任意原E0锥具有(123.2)的坐标，亦未给本章的任意收缩 $\tau$ 族。这里从明定族出发，与那个已付W的恢复结果保持各自前件。

[Q123R]: https://optimization-online.org/wp-content/uploads/2004/03/844.pdf "James Renegar, Hyperbolic Programs, and Their Derivative Relaxations, §2, Proposition 1, Theorems 2—3；Foundations of Computational Mathematics 6 (2006), 59—79，DOI 10.1007/s10208-004-0136-z。使用所引原始稿的准确命题。"
[Q123S]: https://arxiv.org/html/1904.00491v2#S5.SS1 "James Saunderson, Certifying polynomial non-negativity via hyperbolic optimization, §5.1, Proposition 5.1；所用条件只涉及准确正规式及球面三次界。"
[Q123CW]: https://arxiv.org/html/1705.04762v1 "Quo-Shin Chi and Haiyang Wang, Orthogonal multiplications of type [3,4,p], p≤12, Introduction, §2；只复用正交乘法定义、正交等价与Hurwitz背景。"

### 123.8 原E0加IC0候选与仍然准确的全局缺口

**定义 123.9（不限定三次坐标的原条件候选）。** 对一般原模型，$\mathsf E_0$ 始终逐项取127.1、129.1：有限维闭尖生成原锥和严格正原单位，整个 $K,P,\mathcal E$ 及最低定义；全部原纯标签的EB3；Inj；一组含 $P_0$ 顶点的实际原正交种子三角；该三角全部原零效应的联合分离 $\mathsf J_\triangle$；按125.6取值于 $M_i=\operatorname{span}D_{p_i}$ 并保留全部原法向读数而唯一确定的三个规范线性投影 $T_i$ 的全锥正性。PC1和IC0不在这个入口中。共同 $B,w,c,I$ 由同一实际种子按127.2、129.2定义：

$$
\begin{gathered}
c=w/3,\qquad I=\{c+h:u(h)=0,\ B(h,h)\le1/6\}\subset K,\\
\mathsf{PC1}:\quad\forall p\in P\ \exists i:\Delta_i(p)=0,\qquad
\mathsf{IC}_0:\quad\forall p\in P_0:\ D_p\cap I\ne\varnothing,\\
\text{完整条件候选}=\mathsf E_0+\mathsf{IC}_0
\quad\text{连同127.10全部原合同及其完整引用链}.
\end{gathered}
\tag{123.30}
$$

$1/6$ 是以 $c$ 为中心的仿射半径平方；在 $u=1$ 上相应原点范数平方为 $1/2$。已有127.11、129.8、130.5及本卷121.6—121.7在同一 $\mathsf E_0$ 内给出 $P=P_0$，并给条件等价

$$
\mathsf{IC}_0\ \Longleftrightarrow\ \mathsf{PC1}
\ \Longleftrightarrow\ \text{全原PC3}
\ \Longleftrightarrow\ \mathsf W
\ \Longleftrightarrow\ \text{同原全锥、同单位的PSD}_3\text{静态字典}.
\tag{123.31}
$$

在每个指定标签上，接触等价于 $e_p(w)=1$、$B(p,p)=1$ 及三个 $\Delta_i(p)$ 全零，是点态PC3；点态PC1只要求其中一个为零，全域升级仍取原全称量词。IX120.9的 $P_0$ 稠密、THREE_COPY VII121.6的稠密 $G_\delta$ 与非塌缩层闭图、原宽度紧层、本卷121的确认唯一均直接复用。整个W下的G、Jordan分类、状态谱及谱唯一直接复用VIII113.7—113.9；130.2在尚无W的EB加Inj域给全态覆盖，130.3—130.4及131保留原非中心边界谱性和近似闭包条件，不在这里重计。

定理123.5只在已先给(123.1)—(123.2)的族内把有限边缘检验、EB3和PSD正规形接通；定理123.3与123.6保证正规形分支满足同一种子的整个 $\mathsf E_0$ 以及PC1／IC0。它没有为任意 $\mathsf E_0$ 模型取得这个三次表示。因而一般 $\mathsf E_0\Rightarrow\mathsf{PC1}/\mathsf{IC}_0$ 仍未由本章证明，也未构造完整同域反模型。把族表示加作前提再套用定理123.5，不能算作该全局蕴含的证明。

[X125][Q123X]在EB3+PR域所给旧整球共同近零确认，仍仅是近零读数结论；其CS／UF／NC稳定入口也保持原义。它不自动给真实接触或从任意单张效应的小读数到其零集的距离界。本章的点态识别来自准确取零与整球反射，未消费该未付稳定桥；同样未从本章有限检测推出裸EB3的Inj、种子、联合分离或正压缩自动性。谓词缩短不表示独立公理更少。

### 123.9 全来源、操作、有限复合、记录与时间的保留合同

**约定 123.10（127.10及其引用链的原量词）。** 式(123.30)完整保留127.10，并沿其原引用链继承125.11、124.9、123.13、VIII113.11、VIII112.9、IX120.11、THREE_COPY第七卷121.12及122.14。VI(89.13)指[原极商第六卷][Q123PolarVI]的全部两尺度式。以下范围仍由这些原合同承担，定理123.5—123.6只支付单体静态部分。

1. 同一原装饰元组 $\mathcal O$、共同来源域、全部中点实现、原概率像紧性、全测试表及闭性、零／单位／补／有界倍增、重复标签与每种同中点实现，全部非负质量及零／次归一／不等质量，过程与参考各自完整相关联合输入均保留。原 $L,p,\omega,K,M$、两次使用同一读回、两实张成、全实关系、完整(83.8)、VI(89.13)全部两尺度等式、C2、整个 $G=1_E$、精确PRE之后整个H13及每个原资格态、活跃块严格负方向、共享总迹一、非活跃零质量与空活跃集均保持原义。操作映射 $p$ 不与纯标签混型。
2. 设备／事件／来源绑定、全部菜单分支、实际参考／副本／相关联合、记录／权限／控制、ready／flags、失败／拒绝／停止／销毁／返回、实际混合、原字、全部合法未来及每个中间切口全部保留。原生与细化消费者、terminal futures、联合有符号关系、细标签粗归组、记录后的条件未来、source-adoption与资源合同仍各按原消费者承担。
3. 对每个有限 $N\ge1$，仍需实际 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成 $C_N$、严格正 $u_N=u^{\otimes N}$、整个 $K_N$、全部 $P_N$ 和整个效应区间。每个实际分块的最小／最大张量夹逼、产品配对、严格张量单位、因子置换及逆的正性、规范重括号与不连续位置分块的指定运输均按(Q127.35)。整个实际 $S_2$ 按(Q127.36)覆盖任意产品或纠缠纯点、任意有限凸族、全部非负权、零权和重复标签。低二份 $q=1,2$ 的least／谱性／正面投影及保纯到Jordan桥、唯一实际自复合的直和扇区和秩／实维乘法限制、同一实际两因子的产品正规形，仍是全有限层级原定理的各项供应。
4. 三份资源 $\mathsf F_{\max}$ 仍精确要求(Q127.37)：同一最大复块 $L\ge2$、同一含相位正交基，$g_r=\sum_{a=1}^L|a\rangle_r|a\rangle_r|a\rangle_r$，实际 $\Delta_r=|g_r\rangle\langle g_r|\in C_3$、$u_3(\Delta_r)=L$、其余扇区零，以及归一原源 $\Delta_r/L$。不预付三份纯性或实际制备；全经典 $L=1$ 分支按原定理处理。复三能级支路中 $L=3$，二、三份秩九、二十七及全部更高有限次数均保留，不将单体EB3复制为高阶整个排除条件。
5. 全旁观正性(Q127.38)量化每个 $b\ge0$、任意含纠缠的共同输入。只有完整有限层级和共同表示已给，才沿原Choi桥识别通常CP、矩形跨扇区Kraus及逐输入TP／TNI预算。实际事件仍需完整提升、实际探针与相容核；事件饱和另行供应。共同输入预算、接线、记录、粗粒化与校准负责同族仪器。严格正质量分支才条件归一，零质量分支不强定归一条件态；Lüders另需同一分支的锐效应、接受态中性与输出校准。数学效应、正压缩和全部数学POVM不能替代这些条件。
6. 物理钟、实际动态来源、连续齐次可逆时间群和单位仍分别供应。另给同载体上全实时间连续保单位锥自同构群，才有该供应的有限维生成元；重构复块另给保迹酉时间族后，才沿(Q127.39)使用 $U_t=\exp(-\mathrm itH/\hbar)$、共轭演化与 $-\mathrm i[H,\rho]/\hbar$。量词覆盖全部原输入及全部实际时间，$H$ 的标量平移、时间重标和生成元尺度边界均保留。实际Hamiltonian、能量识别与标定、数值 $\hbar$、时空及物理空间维数未由本章静态定理产生。

这些条件与通常量子公理的对应仍是有条件的：正锥上的归一态和全部效应给密度矩阵及Born评价，数学框架给投影测量的概率结构，完整有限联合合同负责实际复合，旁观合同负责CP，事件和仪器合同负责分支实现与更新，时钟和动态来源负责物理演化。单体静态正规形不把后五类供应变成几何定理。

### 123.10 二元窗口与三元兼容的几何含义

三个对角种子像三扇固定的二能级窗口：每扇都能看到一整颗实心三球，边界上的每个点都是原纯点，投向窗口的规范压缩始终为正。只改变三个窗口共同参与的三线性耦合，不会改变这些窗口自身。因此只检查三个对角顶点，无法看见三元拼接是否相容。沿第一扇窗口的边缘选方向 $v$，实际确认尺(123.11)在窗口对面的原面上读零。三次约束把另外两条边锁成 $z_2=-M_vz_3$，而允许自由通过的方向恰是 $M_v$ 不损失长度的子空间。再加上一条对角方向，这个准确暴露面的维数就是 $1+m_v$。只有另知该标签背后的整个排除集合是球时，才由它自身的中心反射和严格凸性把这个面识别为整颗球。

若两条线性无关边缘方向的完整排除都必须是三球，每个方向就必须让二维横向空间完整通过，不能损失长度。全方向收缩把任何可能的损失写成一个非负二次型；它在两条独立线上全为零，只能处处为零。这就把连续的方向兼容缩成有限的精确代数条件，而二维正交矩阵束随后只能给复数乘法的实部。指定的第三条斜方向当然也相容；它在这个已知三线性且全方向收缩的族内是冗余检测。整个推导只需二阶实矩阵、两个平方项和一个非负二次型，不需要在七维切空间研究Hessian。得到的是明确族内的复三能级静态几何；一般原E0为什么必有接触，以及完整物理所需的实际来源、任意有限复合、操作、记录和时间，仍按(123.30)与上述原合同保留。

[Q123SR]: https://github.com/the-omega-institute/trureturing/blob/18995bad7b93a8ca351c75862c415d5161171e52/docs/develop/theory/QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "125—131：原完整定义、固定E0、PC1／IC0条件链、静态字典；SECTION127.10及其完整引用链：全部物理合同。"
[Q123BV]: QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_VIII.md "121.6—121.8：九维EB3+Inj的唯一完整确认、未付接触与完整物理范围。"
[Q123VII]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md "103.2：EB≥1下完整暴露与真面穷尽；其第一段为点态中心反射，Pair不参与此段。106.12保留其W及原等价条件。"
[Q123EVIII]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_VIII.md "113.7—113.9：整个W下的G、秩三Jordan分类、状态谱、谱唯一和准确复三能级字典。"
[Q123X]: https://github.com/the-omega-institute/trureturing/blob/18995bad7b93a8ca351c75862c415d5161171e52/docs/develop/theory/QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_X.md "125：完整EB3+PR中的共同近零确认及CS／UF／NC条件链；没有自动接触。"
[Q123PolarVI]: QUANTUM_ORIGIN_INTRINSIC_POLAR_QUOTIENT_AND_NONCOLLAPSE_VI.md "89.7及(89.13)：同一原装饰元组与全部两尺度、原质量和整个输出合同；完整链沿SAME_READBACK127.10继承。"

## 追加锚（本行以下为增补区）

## 124. 立方双曲几何的完整排除球分类与收缩三线性族的全域结算

### 124.1 指定立方多项式、原单位与完整排除条件

**定义 124.1（正则立方双曲原域）。** 设 $V\ne0$ 为有限维实空间，$h:V\to\mathbb R$ 为次数恰为三的齐次多项式，$e\in V$，且 $h(e)>0$。要求对每个 $x\in V$，多项式 $t\mapsto h(te-x)$ 的三个根均为实数，记为 $\lambda_1(x)\le\lambda_2(x)\le\lambda_3(x)$，按重数计。原锥必须恰为指定分支的整个闭包

$$
C=\Lambda_+(h,e)=\{x:\lambda_i(x)\ge0\ (i=1,2,3)\},
\qquad C\cap(-C)=\{0\},\qquad \operatorname{span}C=V.
\tag{124.1}
$$

这里“正则”指尖且满维，不指多项式不可约、锥齐性或边界处处光滑。$e$ 是向量双曲方向；另外给定的原单位 $u\in V^*$ 在 $C\setminus\{0\}$ 上严格正，二者不混同。始终取

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad
\mathcal E=[0,u]_{C^*},\\
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\qquad
\mathcal T_p(x)=\min_{f\in\mathcal F_p}f(x)\quad(x\in C),\\
D_p=\{x\in K:\mathcal T_p(x)=0\},\qquad
N_x=\{g\in C^*:g(x)=0\}.
\end{gathered}
\tag{124.2}
$$

所有正性和效应上界均在整个原锥上成立，最小化遍历全部原确认效应，第二变量包括全部混态。有限维闭尖锥与严格正单位使 $K$ 紧；它张成 $V$，故 $\mathcal E$ 紧，非空闭切片 $\mathcal F_p$ 紧，最小值达到。这些全效应基本事实直接沿用[VII103.1—103.2][Q124CubicVII]。

本章在这一立方类别中采用的几何候选是

$$
\boxed{\mathrm{EB}_{\ge1}:\quad
\forall p\in P\ \exists d_p\in\mathbb N,\ d_p\ge1:
D_p\simeq_{\rm aff}\overline B^{d_p}.}
\tag{124.3}
$$

球是整个闭实球，允许线段，允许球维数随标签改变；仿射球图不预给原空间的共同内积、中心或长度。这里没有输入Inj、Pair、纯值互易、least、Jordan、自对偶、齐性、连续纯标签或共同矩阵表示。定义双曲秩 $r_h(x)=\#\{i:\lambda_i(x)\ne0\}$；它始终相对于指定的 $(h,e)$，不预先解释成矩阵秩。ROG也取Ito—Lourenço Definition 3.1的相对意义。

### 124.2 秩二边界的实际分支只有一条正法向

**引理 124.2（包含全部活跃约束的法向结论）。** 在定义124.1中，若 $x\in C$ 且 $r_h(x)=2$，则存在 $\ell_x\in C^*\setminus\{0\}$，使

$$
N_x=\mathbb R_+\ell_x,\qquad \ell_x=Dh(x).
\tag{124.4}
$$

证明。此时 $x$ 的根为 $0,\alpha,\beta$，其中 $\alpha,\beta>0$。根的连续性给 $x$ 的一个开邻域 $U$，在其中始终有两根严格正，只有最小根能够变号。由

$$
h(y)=h(e)\lambda_1(y)\lambda_2(y)\lambda_3(y)
\tag{124.5}
$$

得到实际闭分支的局部等式

$$
C\cap U=\{y\in U:h(y)\ge0\}.
\tag{124.6}
$$

这使用所有根的符号，绝非把全局集合 $\{h\ge0\}$ 误当原锥。又因根沿 $e$ 平移，

$$
h(x+te)=h(e)t(t+\alpha)(t+\beta),\qquad
Dh(x)e=h(e)\alpha\beta>0.
\tag{124.7}
$$

隐函数定理使 $\{h=0\}\cap U$ 成为实际边界的光滑超曲面，其切空间为 $\ker Dh(x)$。对任意 $g\in N_x$，$g$ 非负于这张局部边界且在 $x$ 为零。沿边界中任意两侧可微曲线求导，得到 $g$ 零于整个切空间。因此 $g=cDh(x)$；若 $g\ne0$，内部点 $e$ 上的严格正性及(124.7)迫使 $c>0$。

闭凸锥在边界点存在非零支撑泛函 $g_0\in N_x$；刚证的结论给 $g_0=c_0Dh(x)$、$c_0>0$，故 $Dh(x)\in C^*$，所有非负倍数也都属于 $N_x$。由此得到(124.4)。这是Renegar Lemma 7、Theorem 6所描述的重数一边界在本原域上的直接局部证明。

特别地，若一个具体锥还写成若干 $a_i\ge0$、$\Delta_i\ge0$、$h\ge0$，即使 $x$ 处有前两类等号，(124.6)仍由实际双曲分支成立；这些活跃等号不能在此另生第二条独立正法向。证毕。

### 124.3 完整排除球迫使原纯射线双曲秩一

**定理 124.3（立方原域内的自动ROG与全Pair）。** 在定义124.1—124.2及 $\mathrm{EB}_{\ge1}$ 下，每个原纯点都有 $r_h(p)=1$。因此 $C$ 相对于原指定 $(h,e)$ 是ROG，而且对任意不同的实际原纯点 $p,q$，

$$
r_h(p+q)=2,\qquad
H_K(p,q)\ne K.
\tag{124.8}
$$

后一项是VII103.1的全Pair，量化所有不同纯点，不仅量化可区别对。

证明。若 $\dim V=1$，紧基只有一个点 $p$，每张确认效应在该点取一，故 $D_p=\varnothing$，与(124.3)矛盾。因此在本定理前件下 $\dim V>1$，每条极射线都是原锥的真边界面。

Renegar §6 Theorem 23明确断言闭双曲锥的所有边界面都暴露；其对象是整个 $\Lambda_+$，不要求锥齐性，也不只处理光滑点。把它应用于原极射线 $\mathbb R_+p$，得到 $h_p\in C^*\setminus\{0\}$，其原归一零面恰为 $\{p\}$。所以X124.1的PE已经由双曲锥提供，无须另加。

现在直接消费[X124.2引理][Q124CubicX]：EB$_{\ge1}$加PE使每个 $N_p$ 含两条不同的非零正射线。其中一条只在 $p$ 取零，另一条的整个原零面是包含 $p$ 的非点完整排除球。该引理使用VII103.2的全排除面分类及补效应的零对称，不需要数值互易、Inj或Pair。这里不把这条已发表引理重报为新结论。

原纯点不可能是 $C$ 的内点：若是，沿非零 $v\in\ker u$ 作充分小的两侧扰动，便给出其非平凡归一凸分解。因此 $r_h(p)<3$。Ito—Lourenço Proposition 2.4(iv)在尖锥上给 $r_h(p)=0\Longleftrightarrow p=0$，而 $u(p)=1$，所以秩零也不可能。若 $r_h(p)=2$，引理124.2却给 $N_p$ 只有一条非零正射线，与前段矛盾。故全部原纯点的双曲秩恰为一。

极射线与紧基极点一一对应，因而这已经满足相对于指定 $(h,e)$ 的ROG定义。不同归一纯点线性独立。现在准确应用Ito—Lourenço Lemma 3.3(ii)：正则ROG锥中的两个独立秩一点之和恰为秩二；其上界来自Proposition 2.4(i)的秩次可加性，下界来自最小面的秩严格增长。由此得到(124.8)第一式。

立方次数使秩二的 $m=(p+q)/2$ 留在原锥边界。在 $m$ 取非零原正支撑 $g$，则 $g(m)=0$ 及 $g(p),g(q)\ge0$ 给 $g(p)=g(q)=0$。因此整个原最小面满足

$$
H_K(p,q)\subseteq K\cap\ker g\subsetneq K.
\tag{124.9}
$$

这证明全Pair，没有将所选零面直接宣称为 $D_p$，也没有将Pair预藏在ROG的定义中。证毕。

本证明的立方用途十分明确：纯边界点只有秩一或秩二两种非零可能，排除后者后，两个纯点的秩和上界二仍严格小于整个锥的秩三。一般高次数ROG或稀疏PSD截面不因此变成Jordan锥。

### 124.4 正则立方双曲域的准确完整分类

**定理 124.4（不输入Pair的同锥同单位等价）。** 在定义124.1的正则立方双曲原域中，以下三项等价：

$$
\begin{aligned}
&\mathrm{EB}_{\ge1};\\
&\mathrm{Pair}+\mathrm{EB}_{\ge1};\\
&\exists\text{有限维秩三EJA }J,\ 
\Phi:J\overset{\sim}{\longrightarrow}V:\quad
\Phi(J_+)=C,\quad u\Phi=\operatorname{tr}_J.
\end{aligned}
\tag{124.10}
$$

$\operatorname{tr}_J$ 是每个本原幂等元取一的规范迹。表示覆盖同一个原锥、原归一泛函、全部原态和全部原效应。完整S、原least确认、全部纯值互易及Inj是后果。

证明。第一项到第二项由定理124.3。第二项到第三项直接应用VII103.4；其前件在这里逐项就是有限维、闭尖生成的同一 $C$、严格正的同一 $u$、整个 $K,P,[0,u]$、全Pair及完整EB$_{\ge1}$。VII103.2—103.4先给原面穷尽、点球双射、全锥序least及全部纯比较互易，随后才消费[Library的完整S桥][Q124CubicS]。后者供应谱性、忠实自对偶、projectivity与滤子保纯，并调用Barnum—Müller—Ududec Theorem 16；它们不是本章另加的输入。本章不重建这些成熟及已发表中间结果。

第三项到第二项直接用VII103.6的完整反向。具体地，若 $p=\Phi c$、$c$ 为本原幂等元，则全部效应对应 $0\le a\le1_J$，原least为

$$
e_p(x)=\operatorname{tr}_J(c\circ\Phi^{-1}x),\qquad
D_p=\Phi\{y\in J_0(c)\cap J_+:\operatorname{tr}_J y=1\}.
\tag{124.11}
$$

秩三的 $J_0(c)$ 是秩二EJA，其整个迹一基为正维球，包括非简单秩二的线段。两个不同本原支撑的并为秩二，故整个二纯最小面真于 $K$。同一序同构的对偶双射整个效应区间与确认切片，所以这里运输的是原最小值和整个 $D_p$，没有用一个自选零面代替它。第二项到第一项直接成立。

对任意非零 $x\in C$，都由 $x=u(x)\widehat x$、$\widehat x\in K$ 齐次运输；$x=0$ 映到零，所有效应和最低确认函数在零都为零。反向不在零质量上作归一，也不把非零本原元漏出原基。原 $u$ 与规范迹的匹配是VII103.6已处理的同单位归一，不需要假定原坐标中 $u$ 就是某个迹。证毕。

此分类的全部支路，直接沿VII103.7及VIII113.7的成熟秩三EJA分类，为

$$
\mathbb R\oplus\operatorname{spin}_d\ (d\ge1),\qquad
H_3(\mathbb R),\ H_3(\mathbb C),\ H_3(\mathbb H),\ H_3(\mathbb O).
\tag{124.12}
$$

其中 $\operatorname{spin}_d=\mathbb R\oplus\mathbb R^d$，规范迹为 $2t$，$d=1$ 包含经典 $\mathbb R^3$。参数与完整排除维数是分类后的结论：

| 秩三支路 | $\dim V$ | 全部完整 $D_p$ 的球维数 |
| --- | --- | --- |
| $\mathbb R\oplus\operatorname{spin}_d$ | $d+2$ | 旗标标签为 $d$，所有球纯标签为 $1$ |
| $H_3(\mathbb R)$ | $6$ | 全部为 $2$ |
| $H_3(\mathbb C)$ | $9$ | 全部为 $3$ |
| $H_3(\mathbb H)$ | $15$ | 全部为 $5$ |
| $H_3(\mathbb O)$ | $27$ | 全部为 $9$ |

每一支都确实出现在立方类别中：取其Jordan单位 $1_J$ 和三次Jordan行列式，成熟谱定理给 $\det_J(t1_J-y)=\prod_{i=1}^3(t-\mu_i(y))$，全部 $\mu_i(y)$ 为实数，且 $J_+=\{y:\mu_i(y)\ge0\}$。所以该行列式关于 $1_J$ 双曲，整个闭分支就是平方锥；有限EJA的平方锥闭、尖且满维。这里复用的是分类后的谱字典，不以谱性作为前向证明的输入。

一般结论不能擅自删掉第一、第二、第四、第五行。例如对 $d\ge1$，

$$
\begin{gathered}
V=\mathbb R\oplus\mathbb R\oplus\mathbb R^d,\quad
h(s,t,v)=s(t^2-|v|^2),\quad e=(1,1,0),\\
C=\{s\ge0,\ t\ge|v|\},\qquad u(s,t,v)=s+2t
\end{gathered}
\tag{124.13}
$$

就是正则立方双曲实现：$h$ 的根来自线性因子与Lorentz二次因子，含 $e$ 的开分支为 $s>0,t>|v|$。其全基是旗标 $f=(1,0,0)$ 与整球 $B=\{(0,1/2,v/2):|v|\le1\}$ 的join，全部纯点为 $f$ 和 $b_n=(0,1/2,n/2)$、$|n|=1$。VII103.7的完整效应字典给

$$
D_f=B,\qquad D_{b_n}=[f,b_{-n}].
\tag{124.14}
$$

所以变维和线段确实出现于全原域，并非人为删点或限制效应造成的现象。(124.10)给的是秩三EJA的完整分类；复型选择还须使用应用对象实际具有的信息。

### 124.5 任意收缩实三线性参数的整个原锥及种子

**定义 124.5（全参数实九维族）。** 取三个实欧氏二维空间 $L_i$，并设

$$
\begin{gathered}
V=\mathbb R^3\oplus L_1\oplus L_2\oplus L_3,\qquad
x=(a_1,a_2,a_3;z_1,z_2,z_3),\\
|\tau(z_1,z_2,z_3)|\le|z_1||z_2||z_3|
\quad\text{对全部实 }z_i\in L_i,\\
u(x)=a_1+a_2+a_3,\quad
p_i=(\delta_{i1},\delta_{i2},\delta_{i3};0,0,0),\quad
w=p_1+p_2+p_3,\\
\Delta_i=a_ja_k-|z_i|^2,\qquad
h_\tau=a_1a_2a_3-\sum_i a_i|z_i|^2+2\tau(z_1,z_2,z_3),\\
C_\tau=\{x:a_i\ge0,\ \Delta_i\ge0\ (i=1,2,3),\ h_\tau\ge0\}.
\end{gathered}
\tag{124.15}
$$

$z_i$ 位于补指标 $jk$ 的边，$\tau$ 为实三线性型，不要求对称。所有 $K_\tau,P_\tau,\mathcal E_\tau,\mathcal F_p,\mathcal T_p,D_p$ 都按(124.2)从整个 $C_\tau$ 定义。这是123.1的同一家族，不另选满支撑子域、纯轨道、效应菜单或光滑部分。

以下两个上下文事实与123.2—123.3一致；这里给出应用定理124.4所需的直接论证，不将它们计作新的家族构造。

首先，$h_\tau$ 关于 $w$ 双曲且 $C_\tau=\Lambda_+(h_\tau,w)$。固定任意 $x$，置 $r_i=|z_i|$。收缩界允许选择模长为 $r_i$ 的复数 $\xi_i$，满足 $\operatorname{Re}(\xi_1\xi_2\xi_3)=\tau(z_1,z_2,z_3)$；若某个 $r_i=0$，两侧均为零。令

$$
H_x=\begin{pmatrix}
a_1&\xi_3&\overline{\xi_2}\\
\overline{\xi_3}&a_2&\xi_1\\
\xi_2&\overline{\xi_1}&a_3
\end{pmatrix}.
\tag{124.16}
$$

直接展开给 $h_\tau(x+tw)=\det(H_x+tI_3)$。每个固定 $x$ 的右侧全实根，$h_\tau(w)=1$；根全不正等价于 $H_x\succeq0$，而其全部非空主子式恰是三个 $a_i$、三个 $\Delta_i$ 和 $h_\tau$。这同时证明整个闭分支等于(124.15)。$H_x$ 可随 $x$ 非线性地选择，此步没有产生共同矩阵表示。Renegar §2 Proposition 1、Theorems 2—3给该实际分支及其闭包的凸性。$w$ 满足全部严格不等式，故锥满维；若 $x\in C_\tau$ 且 $u(x)=0$，三个 $a_i$ 全零，二阶条件迫全部 $z_i=0$。于是原单位严格正，锥尖且生成，定理124.4的全部入口已经支付。

其次，三个 $p_i$ 都是实际原纯点，且它们的完整最低函数和排除集满足

$$
\begin{gathered}
\mathcal T_{p_i}(x)=a_i(x)\quad(x\in C_\tau),\\
D_{p_i}=\{a_i=0,\ z_j=z_k=0,\ a_j+a_k=1,
\ |z_i|^2\le a_ja_k\}\simeq_{\rm aff}\overline B^3.
\end{gathered}
\tag{124.17}
$$

为在全效应域核对这一点，记 $\pi_i x=(a_j,a_k,z_i)$ 及

$$
\mathscr L_i=\{(b,c,z):b,c\ge0,\ |z|^2\le bc\},
\qquad \upsilon_i(b,c,z)=b+c.
\tag{124.18}
$$

该块的全部零延拓都在 $C_\tau$ 中，而整个 $C_\tau$ 的块投影恰为 $\mathscr L_i$。若正泛函 $g$ 在 $p_1$ 为零，则其 $a_1$ 系数为零。分别独立任取单位向量 $\eta_3\in L_3$、$\eta_2\in L_2$，原锥内的曲线 $(1,t^2,0;0,0,t\eta_3)$、$(1,0,t^2;0,t\eta_2,0)$ 对全部实 $t$ 成立，正负小 $t$ 迫使 $g$ 的 $z_3,z_2$ 系数为零。因此

$$
N_{p_i}=\pi_i^*(\mathscr L_i^*),\qquad
\mathcal F_{p_i}
=\{a_i+b\circ\pi_i:0\le b\le\upsilon_i
\text{ 于 }\mathscr L_i\}.
\tag{124.19}
$$

后一式由 $u-f\in N_{p_i}$ 以及完整零延拓块上的上下界得到；反向块界在整个 $C_\tau$ 上保证效应资格。$b=0$ 可取且其余 $b\pi_i$ 非负，故 $a_i$ 确为全确认族的least，得到(124.17)第一式。$a_i=0$ 时二阶条件清零另外两条边，$\tau$ 随之为零，所以其整个归一零面恰为(124.17)。坐标 $(a_j-a_k,2z_i)$ 将其双射到整个单位三球。原 $p_i$ 的纯性则由任意凸分解中另两对角坐标必须为零、继而全部边为零得到。

这里每个种子的 $D_{p_i}$ 都是通过全确认族算出的整个排除集，不是只展示一个包含于其中的三球。上述曲线也没有对一般 $\tau$ 使用任何未给的指标置换对称性。

### 124.6 EB至少一维在整个实九维族中已选择复三阶

**定理 124.6（全族的弱球条件刚性）。** 对定义124.5中的任意收缩实三线性型 $\tau$，下列条件等价：

1. 每个实际原纯点的整个 $D_p$ 都是某个正维仿射闭球，即EB$_{\ge1}$。
2. 存在实线性双射 $\Psi:V\to\operatorname{Herm}_3(\mathbb C)$，满足 $\Psi(C_\tau)=\operatorname{PSD}_3$、$\operatorname{Tr}\Psi=u$。
3. 每个实际原纯点的整个 $D_p$ 都是三球，即EB3。
4. 存在实线性欧氏等距同构 $O_i:L_i\to\mathbb C$，使对全部实输入都有

$$
\tau(z_1,z_2,z_3)
=\operatorname{Re}\bigl(O_1z_1\,O_2z_2\,O_3z_3\bigr).
\tag{124.20}
$$

可选同一个 $\Psi$ 使 $\Psi(w)=I_3$，并使 $\Psi(p_i)$ 为标准对角秩一投影。

证明第一项到第二项。124.5已证明这是实维九的正则立方双曲原域。定理124.4先给同锥同单位的秩三EJA。简单秩三分支的实维数为 $6,9,15,27$，维数九只留下 $H_3(\mathbb C)$，但还须排除可约分支。

可约秩三EJA的秩分拆只能是 $1+2$ 或 $1+1+1$，统一写为 $\mathbb R\oplus\operatorname{spin}_d$。实维九迫使 $d=7$；此模型每个完整排除集的维数只能为七或一，详见(124.14)。原同单位表示运输所有实际纯点及其整个 $D_p$，然而本族的三个实际种子各自有维数三的完整排除集，矛盾。经典三标量分支维数三，也不可能。故可约分支全部排除，得到第二项。这里用的是本族实际的九维加完整种子三球，不是将任意九维秩三Jordan代数误判为简单。

第二项到第三项使用124.8中仅以保迹锥同构为前件的全域运输；第三项到第一项直接成立。第四项将(124.16)改成 $\xi_i=O_i z_i$ 的共同实线性双射，行列式及全部主子式恰为(124.15)，故第四项给第二项。下面独立证明第二项到第四项及单位向量的准确对应。

### 124.7 从忠实表示读回三线性参数，不预给矩阵束

在第二项的任意 $\Psi$ 下，令 $P_i=\Psi(p_i)$。它们是迹一秩一投影。(124.19)给原least为 $a_i$；同单位序同构运输确认族及全锥序，而PSD原纯点 $P_i$ 的least效应是 $X\mapsto\operatorname{Tr}(P_iX)$。因此在整个 $V$ 上有

$$
a_i(x)=\operatorname{Tr}(P_i\Psi x),\qquad
\sum_iP_i=I_3.
\tag{124.21}
$$

后三个秩一投影和为单位，故两两正交：写 $P_i=v_iv_i^*$，三个单位列组成的方阵 $U$ 满足 $UU^*=I_3$，因而酉。共轭 $\Psi$ 后可令 $P_i=E_{ii}$；于是所有 $a_i$ 都是 $\Psi x$ 的相应对角元，且 $\Psi(w)=I_3$。

令 $M_i=\{a_i=0,z_j=z_k=0\}$。原完整面 $D_{p_i}$ 的线性张成是 $M_i$；由(124.17)、(124.21)和PSD正性，其像为全部满足 $\rho\succeq0$、$\operatorname{Tr}\rho=1$、$\rho e_i=0$ 的矩阵，张成整个支撑于第 $jk$ 二平面的Hermitian空间。对 $x$ 仅含 $z_i$ 的向量，其全部对角读数为零，而 $x\in M_i$，所以 $\Psi x$ 只含相应的一个复非对角元。由此有实线性同构 $O_i:L_i\to\mathbb C$，使整个 $\Psi$ 正是(124.16)中 $\xi_i=O_i z_i$ 的形式。两个块锥完全对应，在块内取 $a_j=a_k=t\ge0$，原正性为 $t\ge|z_i|$，像的正性为 $t\ge|O_i z_i|$；对所有 $t$ 的等价迫使 $|O_i z_i|=|z_i|$。所以 $O_i$ 确为欧氏等距同构，未假定全局辅助内积被保持。

还须证明这三个边映射同时保持三元项，不能仅凭三个二元窗口相同作结论。对任意固定实三元组 $z_i$，置 $r_i=|z_i|$、$\tau_z=\tau(z_1,z_2,z_3)$，任取 $t>r_1$，定义

$$
a_2=a_3=t,\qquad
A=a_1=\frac{t(r_2^2+r_3^2)-2\tau_z}{t^2-r_1^2}.
\tag{124.22}
$$

由收缩界，分子至少为 $(t-r_1)(r_2^2+r_3^2)\ge0$，故 $A\ge0$。此外

$$
\begin{aligned}
\Delta_1&=t^2-r_1^2>0,\\
\Delta_2&=tA-r_2^2
=\frac{t^2r_3^2+r_1^2r_2^2-2t\tau_z}{t^2-r_1^2}
\ge\frac{(tr_3-r_1r_2)^2}{t^2-r_1^2}\ge0,\\
\Delta_3&=tA-r_3^2
\ge\frac{(tr_2-r_1r_3)^2}{t^2-r_1^2}\ge0,\\
h_\tau(A,t,t;z_1,z_2,z_3)&=0.
\end{aligned}
\tag{124.23}
$$

所以该向量 $x_*\in C_\tau$。将 $a_1$ 减少任意 $\varepsilon>0$ 会使三次式变成 $-\varepsilon(t^2-r_1^2)<0$，故 $x_*$ 是整个原锥的边界点。它的像必须是PSD边界点，于是 $\det\Psi(x_*)=0$。前段已固定全部对角元和边长，两个三次展开相减恰为

$$
0=\det\Psi(x_*)-h_\tau(x_*)
=2\left[\operatorname{Re}(O_1z_1\,O_2z_2\,O_3z_3)-\tau_z\right].
\tag{124.24}
$$

这证明(124.20)对全部实输入成立。若某条边为零，收缩界和复乘积均使相应三元项为零；(124.22)—(124.23)也仍有效，没有删去零边、零对角或活跃二阶约束。至此四项双向全部闭合。证毕。

(124.20)的复正规形与123的家族端点分类重合，不计作新的正交乘法分类。这里真正增加的入口是：只要求每个完整排除集合为某个正维球，便由一般立方几何自动取得全Pair、秩三分类及本族全部三球；不再预给球维数三或有限方向上的三球检测。

### 124.8 同一个忠实映射下的全部静态量子对象

**推论 124.8（原全效应最小值和完整排除的运输）。** 只要有定理124.6第二项的保迹锥同构 $\Psi$，就有以下全域运输；124.7还给该同一映射的 $\Psi(w)=I_3$。令 $\rho=\Psi x$，整个原静态字典为

$$
\begin{gathered}
\Psi(C_\tau)=\operatorname{PSD}_3,\quad
\Psi(K_\tau)=\{\rho\succeq0:\operatorname{Tr}\rho=1\},\quad
\Psi(w)=I_3,\\
\Psi(P_\tau)=\{vv^*:v^*v=1\},\qquad
\mathcal E_\tau=\{f_A:f_A(x)=\operatorname{Tr}(A\Psi x),\ 0\preceq A\preceq I_3\}.
\end{gathered}
\tag{124.25}
$$

这覆盖全部原密度态、原纯射线、效应补与凸混合。对任意原纯点 $p$，写 $\Psi p=vv^*$、$v^*v=1$，则整个确认族、最低确认函数和整个排除集分别为

$$
\begin{gathered}
\mathcal F_p=\{f_A:A=vv^*\oplus B\text{ 于 }\mathbb Cv\oplus v^\perp,
\ 0\preceq B\preceq I_{v^\perp}\},\\
\mathcal T_p(x)=v^*\Psi(x)v\quad(x\in C_\tau),\\
D_p=\Psi^{-1}\{\rho\succeq0:\operatorname{Tr}\rho=1,\ \rho v=0\}
\simeq_{\rm aff}\overline B^3,\\
\mathcal T_p(q)=|v^*z|^2\quad\text{若 }\Psi q=zz^*,\ z^*z=1.
\end{gathered}
\tag{124.26}
$$

证明。锥同构的对偶双射全部正泛函，保迹恒等式再双射整个零一效应区间，因此确认切片也被完整双射。若 $0\preceq A\preceq I$ 且 $v^*Av=1$，正矩阵 $I-A$ 的 $v$ 二次型为零，故 $(I-A)v=0$。Hermitian性清零跨块，得到所列全确认族。对任意PSD输入，补块项非负且 $B=0$ 可取，故全族最小值恰为 $v^*\rho v$，并由秩一投影取得。这同时证明同一原least的存在，而非先把确认族缩成一个投影。

正性使 $v^*\rho v=0\Longleftrightarrow\rho v=0$，所以整个最低零集是完整二能级密度体。其仿射三球是支撑在 $v^\perp$ 上的全部迹一PSD矩阵，不是一份纯零关系图或所选截面。纯—纯模方由秩一迹计算得到。以上对任意保迹锥同构都成立，不依赖124.7的坐标正规形，故也完成124.6中第二项到第三项的证明。

有限数学效应族 $f_j\ge0$、$\sum_jf_j=u$ 恰对应全部有限POVM $A_j\succeq0$、$\sum_jA_j=I_3$，每个原读数正是Born评价 $\operatorname{Tr}(A_j\rho)$。在非归一正输入上质量仍为原 $u(x)=\operatorname{Tr}\rho$；零输入对应零矩阵，全部读数为零，不为它强定归一条件态。证毕。

| 通常的单体量子对象或公理 | 本族完整几何候选所给的准确对应 |
| --- | --- |
| 复三维Hilbert空间与纯射线 | 所得同一表示中的 $\mathbb C^3$ 及全部 $\mathbb{CP}^2$ |
| 混态与准备混合 | 全部迹一PSD矩阵及原线性凸组合 |
| 全部效应与Born规则 | 整个 $[0,u]$ 对应全部 $0\preceq A\preceq I_3$，原评价为迹配对 |
| 确认与排除 | 全确认族的真实最小值为秩一评价，完整排除为其整个二能级密度三球 |
| 原单位与三元完备框架 | $u$ 对应迹，$w$ 对应 $I_3$，三个种子对应同一正交完备基 |
| 谱、Jordan与数学面滤子 | 所得完整PSD模型的成熟谱定理、Jordan积及支撑角压缩 |
| 数学有限测量 | 全部效应和为单位的有限POVM；实际共同仪器另有合同 |

### 124.9 完整几何候选的范围与一般原问题

在正则立方双曲类别内，完整候选只需(124.3)，其准确结论是(124.10)的秩三EJA全分类。在明确的实九维收缩三线性族内，同一个候选已经等价于完整复三能级静态字典；这里三个种子的三球和九维都是族定义的后果，Inj及全Pair都是所得结论。这里不声称独立公理数最少，也不声称从更弱的任意原凸几何已取得指定立方表示。

特别地，一般原 $\mathsf E_0$ 仍逐项取SAME_READBACK127.1、129.1：完整原闭尖生成有限维域与严格正单位、全部原态效应及最低定义、全纯EB3、Inj、含 $P_0$ 顶点的实际原种子正交三角、同一三角全部原零效应的联合分离，以及三个规范压缩的全原锥正性。它没有被本章证明具有(124.1)或(124.15)的表示。因此，一般 $\mathsf E_0\Rightarrow\mathrm{PC1}/\mathsf{IC}_0$ 的表示桥与自动接触问题仍保留原状态；本章只给一个完整且已指定的立方域内的新消费者，不拿族内分类冒充该一般桥。

若另行证明某个原模型忠实具有本族表示，且保留同一 $C,u$ 与完整效应，则本章才可在那个模型上消费；不能只匹配三张种子窗口或一个三次零方程后就宣称表示已给。球图中的仿射半径也不自动等于原点范数。SAME_READBACK129的固定内球半径平方 $1/6$、相应原点范数平方 $1/2$，继续只按其共同配对、中心及原单位前件使用；本章没有用这些数值作为输入。

### 124.10 原来源、有限复合、仪器、记录和时间的完整保留

本章完整继承[SAME_READBACK第127.10节][Q124CubicSR]及其全部传递引用，具体包括该卷125.11、124.9、123.13，[EXCLUSION VIII的命题113.11及112.9][Q124CubicEVIII]、[EXCLUSION IX120.11][Q124CubicIX]、[THREE_COPY VII121.12与122.14][Q124CubicTCVII]，以及它们继续指向的VI89.9—89.10、原来源／过程、共同输入和动态消费者。上述继承取各原文的完整前件、原对象及量词；以下对应保留其承担的内容。

**共同来源、全部操作和合法未来。** 同一原装饰元组 $\mathcal O$ 的共同来源域、全部中点实现、概率像紧性、全测试表及闭性、零／单位／补／有界倍增、重复标签与每种同中点实现全部保留。质量遍历全部非负数，含零、次归一与不等质量；过程和参考各有完整相关联合输入域。原 $L,p,\omega,K,M$、两次同一读回、两实张成、全实关系、完整(83.8)、VI(89.13)全部两尺度等式、C2、整个 $G=1_E$、精确PRE后的整个H13及每个原资格态、活跃块严格负方向、共享总迹一、非活跃零质量和空活跃集，仍由原消费者承担；操作映射 $p$ 与本章纯态标签不混同。

设备／事件／来源绑定、全部菜单分支、实际参考／副本／相关联合、记录／权限／控制、ready／flags、失败／拒绝／停止／销毁／返回、实际混合、原字、全部合法未来及每个中间切口均保留。原生及细化消费者、terminal futures、联合有符号关系、细标签粗归组、记录后的条件未来、source-adoption和资源合同继续在同一共同来源上承担。一个数学球、一张原效应或一个正角压缩没有因此成为可实际调用的来源或接线。

**全部有限联合载体。** 对每个有限 $N\ge1$，仍须提供实际 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成 $C_N$、严格正 $u_N=u^{\otimes N}$、整个 $K_N=C_N\cap\{u_N=1\}$、全部 $P_N=\operatorname{ext}K_N$ 以及完整原效应区间。每个实际分块 $a+b=N$ 均须有

$$
C_a\otimes_{\min}C_b\subseteq C_{a+b}
\subseteq C_a\otimes_{\max}C_b.
\tag{124.27}
$$

同一产品配对、严格张量单位、全部原因子置换及其逆的正性、规范重括号、指定运输下的不连续位置分块都不删减。二份比较仍量化整个实际联合 $S_2$：每个产品或纠缠纯点 $p,q_\ell\in P_2$、每个有限族、全部非负 $t_\ell$ 且和为一，包括零权和重复标签，要求

$$
\mathcal T_p^{(2)}\!\left(\sum_\ell t_\ell q_\ell\right)
=\sum_\ell t_\ell\mathcal T_{q_\ell}^{(2)}(p),\qquad
\mathcal T_p^{(2)}(x)=
\inf_{\substack{f\in[0,u_2]_{C_2^*}\\f(p)=1}}f(x).
\tag{124.28}
$$

仅产品态上的比较不能替代它。三项具名供应仍分别是原低二份 $q=1,2$ 的least／谱性／正面投影及保纯到Jordan桥，唯一实际自复合 $(W_1,W_1,W_2)$ 的直和扇区限制、秩和实维乘法的复型选择，以及同一实际两因子的产品正规形。

非经典支路的 $\mathsf F_{\max}$ 仍要求同一最大复块 $n_r=L\ge2$ 与同一含相位正交基给出

$$
g_r=\sum_{a=1}^L|a\rangle_r|a\rangle_r|a\rangle_r,\qquad
\Delta_r=|g_r\rangle\langle g_r|\in C_3,\qquad u_3(\Delta_r)=L.
\tag{124.29}
$$

其余扇区零，归一原源为 $\Delta_r/L$，不预付三份纯性或实际制备；全经典 $L=1$ 支路按原定理免除此资源。本族所得单体复型的 $L=3$，二、三份秩为九、二十七；高阶整个排除集合不被要求继续满足单体EB3。只有全部联合前件和三项供应齐备后，才消费既有全有限层级结论。

**全旁观CP、实际事件、同族仪器与记录。** 数学全旁观正性仍量化每个 $b\ge0$ 以及任意含纠缠的同一共同输入，要求

$$
(\operatorname{id}_{W_b}\otimes F)(C_{b+m})\subseteq C_{b+n}.
\tag{124.30}
$$

全有限层级及其共同表示已提供后，才沿原Choi桥识别通常CP、矩形跨扇区Kraus和逐输入TP／TNI预算。同一实际事件的CP还需原完整提升、实际探针及相容核；使全部数学CP-TNI分支成为实际事件另需事件饱和选择。共同输入上的预算、接线、记录、粗粒化和校准负责把分支组成同族仪器。仅严格正质量分支作条件归一，零质量分支不强定归一条件态；Lüders更新还要求同一分支的锐效应、接受态中性与输出校准。全部数学POVM、效应和为单位与可执行的共同仪器各按原合同承担。

**原钟、动态来源、能量与数值 $\hbar$。** 原钟、实际动态来源、连续齐次可逆时间群与单位仍是原前件。若另给对全部实时间的连续线性群 $A_t$，满足 $A_0=I$、$A_{s+t}=A_sA_t$、$A_t(C)=C$、$uA_t=u$，生成元只描述该额外给定过程。在重构复块中另给保迹酉时间族后，通常写为

$$
U_t=\exp(-\mathrm itH/\hbar),\qquad
\rho_t=U_t\rho U_t^*,\qquad
\mathcal L(\rho)=-\frac{\mathrm i}{\hbar}[H,\rho],\qquad H=H^*.
\tag{124.31}
$$

量词覆盖该已给时间族的全部原输入与全部实时间。$H$ 的标量平移不改变态作用，时间重标改变生成元尺度却保留静态几何；恒等时间族和非平凡Hamiltonian族可共享全部静态对象。因此实际 $H$、能量标定、数值 $\hbar$、时空和物理空间维数均未由立方分类选出，球面参数也没有被解释成物理时间。

### 124.11 成熟复用与本章连接的准确归属

Renegar的[原始论文][Q124CubicRenegar] §2 Proposition 1、Theorems 2—3定位双曲开分支、闭包与凸性；§3 Lemma 7及Theorem 6处理重数一边界，Theorem 10、§6 Proposition 25及Theorem 26处理实际面的切支撑与重数；§6 Theorem 23明确给全部边界面暴露。本章仅按这些原条件使用，尤其不以“代数零点”替代实际闭分支。

Ito—Lourenço [arXiv:2207.11986v3][Q124CubicIL] Proposition 2.4供应双曲秩次可加性、最小面相对内部与秩的对应、沿面严格增长及尖锥秩零判据；Definition 3.1、Remark 3.2固定ROG对指定多项式的依赖；Lemma 3.3(ii)给两个独立秩一元之和恰为秩二。该论文不是一般ROG等于Jordan的定理。本章先由完整排除条件取得ROG，再由次数三取得Pair，最后通过VII103.4的完整原效应桥进入Jordan。

VII103.2的完整排除面与全部真面分类、X124.2的两条不同正法向、VII103.4及其Library完整S／Jordan桥、VII103.6的任意原单位反向、VII103.7及VIII113.7—113.9的成熟秩三支路与静态字典均直接复用。它们各自的原前件保持不变。123的族定义、合法性、三个种子全效应窗口和复正规形也不作为本章的新构造；124.5及124.7只将所需上下文与完整参数对应写明，供本章消费者使用。

本章的 `repo-derived` 连接是：在指定正则立方双曲原域，完整正维排除球经自动PE与原纯点法向矛盾，排除双曲秩二纯点；相对指定多项式得到ROG后，以次数三供应所有不同原纯对的Pair，从而消费既有完整分类。新的家族结算是EB$_{\ge1}$已经足够，并由实九维及原种子完整三球排除可约分支。所列原始文献与既有源接口限定归属；不作全球原创、文献穷尽、独立公理最少或形式内核核验的主张。

### 124.12 完整中文图景

把原状态体想成一块包含全部纯态与混态的实体，把原效应想成能在这整块实体上合法读取零到一的全部尺。对一个纯态，把所有能被某张“肯定它”的尺完全排除的状态收齐，才是它的完整排除集合；不能只挑一张好看的切片。本章只要求这些完整集合都是非退化实心球，允许有的只是一条线段，有的维数更高。关键不是先规定它们都是量子三球，而是利用立方双曲边界只有三个秩层：纯态若落在秩二的光滑边界，只能有一个支撑方向；但它既能被一张尺单独指出，又必须处在另一颗完整排除球上，已经给出两个不同支撑方向，所以它只能落在秩一层。两个秩一纯态加在一起至多到秩二，离整个秩三实体的内部还差一层，于是任意两纯态都留在一个真实的原真面里，准确补上旧分类需要的Pair。一般立方实体因此可以是实、复、四元、八元或带旗标的秩三Jordan模型，不能一概叫作复量子系统；而在这里指定的实九维三线性族，三个种子的完整三球排除了旗标加七球支路，维数又排除了其余简单类型，最终只剩完整复三能级。得到的同一映射同时覆盖全部密度态、全部纯射线、全部效应、Born读数、确认最小值和每个完整排除三球。它完成的是这一个完整家族内的静态几何分类；共同物理来源、任意有限复合、事件和仪器、记录与合法未来，以及钟、能量和 $\hbar$ 仍须逐项履行124.10继承的原合同。

[Q124CubicRenegar]: https://doi.org/10.1007/s10208-004-0136-z "James Renegar, Hyperbolic Programs, and Their Derivative Relaxations；§2、§3及§6。"
[Q124CubicIL]: https://arxiv.org/pdf/2207.11986v3 "Masaru Ito and Bruno F. Lourenço, Automorphisms of rank-one generated hyperbolicity cones and their derivative relaxations；DOI 10.1137/22M1513964；Proposition 2.4、Definition 3.1、Remark 3.2、Lemma 3.3。"
[Q124CubicVII]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md "VII103.1—103.8：全Pair的准确原义、完整面分类、完整S桥、任意原单位反向及全部秩三支路。"
[Q124CubicX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_X.md "X124.1—124.2：PE与每个原纯点的两条不同正法向。"
[Q124CubicS]: ../../../Library/QuantumStates/mullerududec2012selfduality.md#reciprocal-least-confirmation-and-the-spectrality-bridge "原全效应域中完整S到谱性、自对偶、projectivity及滤子保纯的既有桥；所引Barnum—Müller—Ududec Theorem 16。"
[Q124CubicEVIII]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_VIII.md "VIII113.7—113.9：成熟秩三分类与完整静态字典；命题113.11及112.9的全部原联合、操作和时间合同。"
[Q124CubicSR]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "第127.10节及完整传递引用：来源、全部有限复合、资源、CP、实际事件仪器、记录、全部合法未来及时间；125.11、124.9、123.13、127.1、129.1与PC1／IC0的原范围。"
[Q124CubicIX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX120.11：同一原静态字典及其完整物理合同和引用链。"
[Q124CubicTCVII]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md "THREE_COPY VII121.12、122.14：共同来源、全有限层级、事件仪器、记录及连续时间的完整合同。"

## 追加锚（本行以下为增补区）

## 125. 整个代数边界的最低三次条件与同原量子几何入口

### 125.1 整个边界理想，而非所选窗口的零方程

设 $V\ne0$ 为有限维实向量空间，$C\subset V$ 为非零、闭、尖、满维凸锥。先不假定半代数、双曲、齐性、光滑性或任何矩阵表示。记 $\mathbb R[V]$ 为实系数多项式环，$\partial C$ 为相对于整个 $V$ 的欧氏边界，定义

$$
I_\partial(C)=\{q\in\mathbb R[V]:q(x)=0\ \text{对全部 }x\in\partial C\},
\qquad
\partial_aC=\overline{\partial C}^{\,\mathrm{Zar}}.
\tag{MC125.1}
$$

Zariski闭包取实系数方程；也可把同一理想的零集放入复化仿射空间。这里的理想由**整个欧氏边界**确定，不由某个光滑片、某组种子面、纯态轨道或选出的有限测试确定。当 $I_\partial(C)\ne\{0\}$ 时，定义

$$
\delta(C)=\min\{\deg q:0\ne q\in I_\partial(C)\}.
\tag{MC125.2}
$$

次数是总次数，不是不可约分量次数的最大值。没有非零边界方程时记 $\delta(C)=\infty$。本章的附加几何条件为

$$
\mathsf{AB}_{\le3}:\qquad \delta(C)\le3.
\tag{MC125.3}
$$

下文证明有限次数时整个边界理想确为主理想，并把其约化生成元记作 $p_C$。因此(MC125.2)与“整个代数边界的约化方程之次数”一致；不是先假设存在一个具有所需性质的最小双曲多项式。

对量子消费者，另外给定在 $C\setminus\{0\}$ 上严格正的原 $u\in V^*$，始终使用

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad
\mathcal E=[0,u]_{C^*},\\
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\qquad
\mathcal T_p(x)=\min_{f\in\mathcal F_p}f(x)\quad(x\in C),\\
D_p=\{x\in K:\mathcal T_p(x)=0\}.
\end{gathered}
\tag{MC125.4}
$$

$K,P,\mathcal E$ 与确认族全部保留原全域；$\mathcal T_p$ 的第二变量包括全部混态及全部非负质量输入。有限维闭尖满维性与严格正单位使 $K,\mathcal E,\mathcal F_p$ 紧，且最小值达到，直接沿用124.1及VII103.2的接口。双曲方向 $e\in V$ 是向量，与归一泛函 $u$ 不同型。

### 125.2 有限边界方程供应的存在性、齐次性和约化性

**引理 125.1（整个边界最低方程）。** 若 $\delta(C)<\infty$，则 $C$ 为半代数集，且

$$
I_\partial(C)=(p_C),\qquad
p_C\text{ 齐次、平方自由},\qquad
\deg p_C=\delta(C)\ge1.
\tag{MC125.5}
$$

$p_C$ 除非零实常数外唯一。此引理不声称 $p_C$ 在内部无零，也不声称 $C$ 已是它的双曲分支。

证明。取 $0\ne q\in I_\partial(C)$，令 $Z=\{q=0\}$。非零实多项式不在任何非空开集上恒零，所以 $Z$ 无内部。半代数集 $V\setminus Z$ 只有有限个连通分量，各分量均半代数。每个分量全部落在 $\operatorname{int}C$ 或全部落在 $V\setminus C$：在避开 $\partial C$ 的分量内，这两个相对开集互补，连通性禁止二者同时非空。满维凸性给 $C=\overline{\operatorname{int}C}$；删去无内部的 $Z$ 不改变该闭包。因此 $C$ 是落在其内部的有限个上述分量之并的闭包，故半代数。这里使用半代数连通分量的有限性与闭包稳定性，正是Sinn Proposition 2.9证明中的成熟工具；并未把“边界已是超曲面”当作这一步的前提。

$C$ 为真子集，因为它尖且 $V\ne0$；它及其补集均非空且regular。Sinn Definition 2.1、Lemma 2.5于是适用于整个边界；Gouveia—Ito—Lourenço Proposition 2.2的准确结论给出唯一的最低次数方程及每个边界方程的整除性，即(MC125.5)的主理想断言。这是成熟接口，不另计作新的代数边界定理。

再直接核对其余性质。$\partial C$ 对正数缩放不变。把最低次数方程分为齐次部分 $p_C=\sum_jp_j$；对每个 $b\in\partial C$，恒等式 $\sum_jt^jp_j(b)=0$ 对全部 $t>0$ 成立，故每个 $p_j$ 都属于 $I_\partial(C)$。任何次数小于 $\delta(C)$ 的非零部分都会违背最低性，所以只有最高部分，$p_C$ 齐次。$0\in\partial C$ 排除非零常数，故次数至少一。

若不可约分解中有重复因子，把全部正重数改为一所得乘积仍在每个实边界点为零；它非零而次数严格下降，矛盾。因此 $p_C$ 平方自由。齐次多项式的每个非恒定因子也齐次：两个因子的最低和最高非零齐次次数分别相加，乘积这两个极端部分均非零；乘积只有一个次数迫使各因子的次数范围也只有一个值。证毕。

### 125.3 紧基与整个边界之间的精确次数对应

**引理 125.2（基的边界、齐次化与径向连续性）。** 在 $\dim V\ge2$ 时，可选严格正线性泛函 $\ell$，使

$$
B=C\cap H,\qquad H=\{\ell=1\}
\tag{MC125.6}
$$

为 $H$ 中有非空内部的紧凸体，且

$$
\partial C\setminus\{0\}
=\{rb:r>0,\ b\in\partial_H B\}.
\tag{MC125.7}
$$

$p_C|_H$ 非零，其仿射总次数恰为 $\delta(C)$，也是覆盖 $\partial_HB$ 的非零仿射多项式的最低次数。对每个 $a\in\operatorname{int}_H B$，从 $a$ 发出的径向投影给单位球面与 $\partial_HB$ 的同胚；不要求边界可微。

证明。严格正 $\ell$ 的存在可由有限维强分离得到：$C$ 与辅助单位球的交紧，且其凸包不含零，否则一个正权非零锥元会同时属于 $C$ 和 $-C$。分离零点与该紧凸包，便得在全部单位锥元上有统一正下界的 $\ell$。这也使截面 $B$ 有界；闭性给紧性，满维给其仿射内部非空。若原单位 $u$ 已给，可直接取 $\ell=u$。

映射 $(r,b)\mapsto rb$ 把 $(0,\infty)\times H$ 同胚到 $\{\ell>0\}$，并把 $(0,\infty)\times B$ 对应到 $C\setminus\{0\}$；比较内部与边界得到(MC125.7)。$\dim H\ge1$，故紧凸体的边界非空。齐次 $p_C$ 若在整个 $H$ 恒零，就在开集 $\{\ell>0\}$ 恒零，因而不可能。

在 $H$ 选原点 $b_0$，写 $x=sb_0+v$、$v\in\ker\ell$。任意次数 $d\ge1$ 的非零仿射多项式 $g(b_0+v)$，其齐次化

$$
G(sb_0+v)=s^d g(b_0+v/s)
\tag{MC125.8}
$$

按单项式展开为真正的次数 $d$ 齐次多项式，不在 $s=0$ 使用除法。若 $g$ 覆盖整个 $\partial_HB$，则(MC125.7)使 $G$ 在全部非零 $\partial C$ 为零，并由齐次正次数在原点为零。因此 $\delta(C)\le d$。把此结论用于 $g=p_C|_H$，结合 $\deg g\le\delta(C)$，得到次数相等及最低性。此处不存在无穷远因子或漏掉锥顶的步骤；Sinn Remark 2.10、Corollary 2.11给出相同齐次化接口的代数几何表述。

最后令 $A=B-a\subset\ker\ell$，选 $0<r<R$ 使 $r\overline B_{\rm Eucl}\subseteq A\subseteq R\overline B_{\rm Eucl}$。其Minkowski泛函 $\mu$ 次可加且正齐次，并满足

$$
\frac{\|v\|}{R}\le\mu(v)\le\frac{\|v\|}{r},\qquad
|\mu(v)-\mu(w)|\le\frac{\|v-w\|}{r}.
\tag{MC125.9}
$$

后一式分别用 $\mu(v)\le\mu(w)+\mu(v-w)$ 及交换 $v,w$ 得到，不要求 $A$ 对称。单位方向上的唯一径向端点为 $a+v/\mu(v)$，由(MC125.9)连续。凸性及 $a$ 为内点使每条射线仅有这个边界端点；紧性和Hausdorff性使该连续双射为同胚。仿射维一时单位球面是两个离散方向，结论同样成立。证毕。

### 125.4 内部零点迫使可删除的线性因子

**引理 125.3（三次以内的内部零点障碍）。** 设 $B$ 是仿射维数 $m\ge1$ 的紧凸体，$0\ne f$ 为总次数不超过三的仿射多项式，且 $f|_{\partial B}=0$。若 $f(a)=0$、$a\in\operatorname{int}B$，则 $Df(a)\ne0$，并且

$$
f(x)=L(x-a)g(x),\qquad L=Df(a),\qquad
0\ne g,\quad g|_{\partial B}=0,\quad\deg g=\deg f-1.
\tag{MC125.10}
$$

所以最低次数边界方程不可能有内部零点。

证明。任取非零方向 $v$。整条直线与 $B$ 的交为紧区间

$$
\{a+tv:\alpha(v)\le t\le\beta(v)\},\qquad
\alpha(v)<0<\beta(v),
\tag{MC125.11}
$$

两个端点都在整个边界。对多项式作精确Taylor分解

$$
f(a+tv)=tL(v)+t^2Q(v)+t^3R(v),
\tag{MC125.12}
$$

缺失的高次部分记零。若 $L(v)=0$，则零点 $t=0$ 至少二重，另外还有两个不同且非零的实根 $\alpha(v),\beta(v)$。非零次数至多三的单变量多项式不可能承担这四个按重数计的根，故该限制恒零。这也包括 $Q(v)=0$、$R(v)=0$ 及限制次数下降的方向，没有用“泛方向”删掉它们。

若 $L=0$，上述结论对全部非零 $v$ 成立，于是 $f$ 在整个仿射空间恒零，矛盾。因此 $L\ne0$。对 $v\in\ker L\setminus\{0\}$，同一结论给 $f(a+v)=0$；$v=0$ 已由 $f(a)=0$ 覆盖。故 $f$ 在超平面 $a+\ker L$ 上恒零。取 $L(x-a)$ 为一个仿射坐标，多项式除法或按该坐标展开即得 $f=L(x-a)g$，不要求 $\partial B$ 在任何点可微。“切超平面”在这里只指多项式在这个正则零点的超平面。

还须证明这个因子可从**整个**边界方程删除。由引理125.2的径向同胚，$\partial B\cap(a+\ker L)$ 对应单位方向球面上的 $\ker L$ 赤道。$m\ge2$ 时赤道无内部，其补稠密；$m=1$ 时超平面仅为内部点 $a$，与边界不交。于是 $\partial B\setminus(a+\ker L)$ 在整个 $\partial B$ 中稠密。该补集上 $L\ne0$，所以 $g=0$；连续性给 $g$ 在整个边界为零。$f\ne0$ 保证 $g\ne0$，次数降低一。若 $f$ 最低，这便矛盾。证毕。

该证明不假设内部零点已有光滑凸边界切线；它先排除零梯度，再从多项式恒等式取得线性因子，最后用实际紧凸体的径向连续性取得整个边界上的可删性。只证明局部可分解或只在一个边界片消去因子，都不足以使用最低性。

### 125.5 从最低次数到全部内部方向与整个双曲分支

**定理 125.4（最低三次整个边界入口）。** 对125.1的任意非零有限维闭尖满维凸锥，若 $\mathsf{AB}_{\le3}$ 成立，则可统一定向 $p_C$，使

$$
\begin{gathered}
p_C(x)>0\quad(x\in\operatorname{int}C),\\
\forall e\in\operatorname{int}C:\quad
p_C\text{ 关于 }e\text{ 双曲},\qquad
C=\Lambda_+(p_C,e).
\end{gathered}
\tag{MC125.13}
$$

这里 $\Lambda_+$ 取 $t\mapsto p_C(te-x)$ 全部根非负的闭分支。反向，若某个次数至多三的齐次双曲多项式具有整个闭分支 $C$，则 $\mathsf{AB}_{\le3}$ 成立。

证明。先设 $n=\dim V\ge2$。在引理125.2的紧基上，$f=p_C|_H$ 为次数 $\delta(C)\le3$ 的最低边界方程。引理125.3给 $f$ 在基内部无零。每个原锥内点可写为正数乘以基内点，齐次性于是给 $p_C$ 在整个 $\operatorname{int}C$ 无零。内部凸而连通，可选一次整体符号使其处处为正。

固定任意 $e\in\operatorname{int}C$，以及 $x\notin\mathbb Re$。考虑 $y(t)=te-x$。$e$ 的内部邻域保证 $t$ 足够大时 $y(t)\in\operatorname{int}C$，而 $t$ 足够负时 $y(t)\in-\operatorname{int}C$。凸性、闭性及沿 $e$ 的内部正向性给有限端点 $a,b$，使

$$
\{t:y(t)\in-C\}=(-\infty,a],\qquad
\{t:y(t)\in C\}=[b,\infty).
\tag{MC125.14}
$$

例如 $y(t)\in C$ 后加任意正倍 $e$ 都进内部，因此该交恰为一条闭半线；另一条同理。两端点分别属于 $-\partial C$ 和 $\partial C$。尖性给 $a<b$：若两半线相交，交点须为 $C\cap(-C)$ 中的零，迫使 $x\in\mathbb Re$，矛盾。

齐次性使 $p_C$ 在 $-\partial C$ 也为零。因此 $p_C(te-x)$ 至少有两个不同实根 $a,b$，且其首项系数为 $p_C(e)>0$，次数恰为 $\delta(C)$。这先排除此维数下 $\delta(C)=1$。次数二时两个根已全部实；次数三时除去两个实线性因子，余下实一次因子，其根也实。若 $x=se$，则 $p_C(te-x)=p_C(e)(t-s)^{\delta(C)}$，包括零向量与全部重根。这证明关于所选任意内部方向的双曲性，没有遗漏零方向或限制次数下降。

还需完整分支等式。由刚证的无内部零点，$\operatorname{int}C\subseteq\{p_C\ne0\}$；它在该开集中既开又闭，因为 $\overline{\operatorname{int}C}=C$，而其边界均在 $\{p_C=0\}$。其自身连通，所以恰为含 $e$ 的一个完整连通分量。此时才调用Renegar Proposition 1：双曲开分支就是这个分量，闭分支为其闭包。于是 $\Lambda_+(p_C,e)=C$。Theorems 2—3与这里的凸性及全部内部方向结论相容；它们未被倒用来预设原锥身份。

若 $n=1$，闭尖满维非零锥是一条射线。取坐标使 $C=\mathbb R_+$，则 $I_\partial(C)=(t)$、$\delta=1$；$p_C=t$ 关于每个 $e>0$ 双曲且整个分支为该射线。这覆盖紧基仿射维零、不能使用两个边界端点的情形。

最后，反向中双曲分支边界必在其多项式的零集中，故该多项式属于 $I_\partial(C)$，直接得到最低次数不超过三。证毕。

### 125.6 低维、可约、重复因子与尖性的准确作用

定理125.4不要求最低方程不可约。把约化方程按实不可约齐次因子分解，每个因子在内部不为零，可逐因子定向为在 $e$ 为正。其沿 $e$ 的单变量根是乘积根的一部分，故各因子均双曲；乘积的整个闭分支恰为各因子闭分支的交。因此全部次数分拆均被覆盖：

| 最低方程的次数形状 | 不加EB时的准确分支解释 |
| --- | --- |
| $1$ | 只能为一维射线；较高维线性半空间有线性部分，不能尖 |
| $1+1$ | 两个半空间的交；尖满维时恰为二维楔，线性同构于 $\mathbb R_+^2$ |
| 不可约 $2$ | 一个二次双曲锥；尖满维时为Lorentz锥 |
| $1+1+1$ | 三个半空间的交；最低性与尖满维性使三线性坐标独立且 $\dim V=3$，即经典正卦限 |
| $1+2$ | 一个半空间与一个不可约二次双曲分支之交，整个交集就是原锥；此处尚不宣称为Jordan直积 |
| 不可约 $3$ | 整个三次双曲分支；此处尚不宣称ROG、齐性或Jordan |

表中二次断言可直接核对：沿 $e$ 消去交叉项，把 $q$ 写为 $a s^2-Q(v)$、$a>0$；每个方向的判别式非负给 $Q\ge0$。分支为 $\sqrt a\,s\ge\sqrt{Q(v)}$，其线性部分恰为 $\ker Q$。尖性迫使该核为零，所得即Lorentz锥；低到两变量时二次式分为两个实线性因子，归入楔分支。三个线性因子的公共核属于锥的线性部分，故尖性要求它为零，维数至多三；维一为射线、维二为楔，最低次数分别为一、二，因而最低三线性情形只能为三维独立坐标。二维楔的两条不同边界射线分别迫使两个线性因子整除全部边界方程，故最低方程确为两因子乘积。

重复因子与额外因子不能被算入 $\delta$。已知的完整边界覆盖反例必须保留：

$$
C=\mathbb R_+^2,\quad e=(2,1),\quad h(x,y)=xy(x-y),\quad p_C(x,y)=xy.
\tag{MC125.15}
$$

$h$ 平方自由，$h(e)>0$，且是三个关于 $e$ 双曲的实线性因子的乘积。其特征根为 $x/2,y,x-y$，所以

$$
\Lambda_+(h,e)=\{x\ge y\ge0\}\subsetneq C.
\tag{MC125.16}
$$

它覆盖整个 $\partial C$，但额外因子 $x-y$ 穿过原内部，准确展示“边界覆盖加双曲”仍不足以取得整个分支。引理125.3所删除的正是这类内部线性障碍。另一个不同问题是 $\widetilde h=x^2y$：它与 $xy$ 的整个正分支相同，但两条极射线中有一条相对于 $\widetilde h$ 的秩为二。锥相同不保证指定多项式的ROG相同；平方自由约化和最低性各有实际作用。这些是已有例子的边界说明，不计作新反模型。

尖性是紧基和(MC125.14)中两个不同穿越点的直接前件，但不是最终纯几何结论不可去掉的必要条件。对任意真、闭、满维凸锥，令 $L=C\cap(-C)$，选补空间 $W$，则 $C=L\oplus C_0$，其中 $C_0=C\cap W$ 在 $W$ 中闭尖满维，且 $\partial C=L\times\partial C_0$。把边界方程按 $L$ 的坐标展开，其每个系数都在 $\partial C_0$ 为零；反向也成立。因此整个边界理想为 $I_\partial(C_0)$ 的多项式环扩张，最低生成元是 $p_{C_0}$ 的拉回，次数不变。对商锥使用定理125.4后拉回，即得原含线性部分的整个分支等式。例如半空间最低次数一也满足该几何结论。全空间的边界为空，理想为全环，常数一按次数零的平凡约定处理，不属本章正次数对象。量子部分仍严格保留尖性：非零线性部分会阻止存在在全部非零锥元上严格正的归一单位。

### 125.7 次数四的已知锐性边界

**例 125.5（四次不能替代三次）。** 取

$$
C_4=\{(t,x,y):t\ge(x^4+y^4)^{1/4}\},\qquad
F(t,x,y)=t^4-x^4-y^4.
\tag{MC125.17}
$$

$C_4$ 是闭尖满维凸锥，整个边界的最低方程为 $F$，次数恰为四；它不是任何多项式的双曲锥。该例是Helton—Vinnikov §3.2.2的 $1-x^4-y^4$ 障碍之齐次化，不作为新构造。

证明。$s\mapsto s^4$ 凸，故 $B_4=\{x^4+y^4\le1\}$ 为紧、平衡、含零内点的凸体，其Minkowski泛函是范数 $(x^4+y^4)^{1/4}$。范数的上图为凸锥；范数连续给闭性，$t=0$ 的正锥元只能为零给尖性，$(1,0,0)$ 为内点给满维。整个欧氏边界恰为 $t=(x^4+y^4)^{1/4}$，包括锥顶；非零边界处 $t>0$。因此 $F$ 覆盖整个边界。

在 $\mathbb C[t,y][x]$ 中将 $F$ 写为 $-x^4+(t^4-y^4)$。素元 $t-y$ 整除全部非首项系数，却不以平方整除常数项，因为

$$
t^4-y^4=(t-y)(t+y)(t^2+y^2),\qquad
[(t+y)(t^2+y^2)]_{t=y}=4y^3\ne0.
\tag{MC125.18}
$$

Eisenstein判据及Gauss引理给 $F$ 在复多项式环中不可约，因而在实环中不可约。引理125.1的整个边界最低生成元整除 $F$，且不为常数，所以只能与 $F$ 相差非零标量。这证明全部边界的最低性，而非只检验某条曲线。

但在内部方向 $e=(1,0,0)$ 和 $z=(0,1,0)$ 上，$F(se-z)=s^4-1$ 有非实根 $\pm\mathrm i$，故 $F$ 不关于 $e$ 双曲。若 $C_4$ 是某个双曲多项式 $g$ 的整个分支，Renegar Theorem 3可把其方向移到这个 $e$；其最低整个边界多项式 $F$ 整除 $g$，从而 $F$ 的每条方向限制都应只有实根，矛盾。证毕。

这个例子只否定将定理125.4的三次上界改为四次。它未被证明满足完整EB，更不满足本章另未构造的全部E0合同，因此不是一般 $\mathsf E_0\Rightarrow\mathsf{PC1}/\mathsf{IC}_0$ 的同域反模型。

### 125.8 完整正维排除球迫使最低次数恰为三

**定理 125.6（低次数入口的完整秩三消费者）。** 在125.1的同一有限维闭尖满维原锥及严格正原单位上，下列两项等价：

$$
\begin{aligned}
&\mathsf{AB}_{\le3}\quad\text{且}\quad
\forall p\in P\ \exists d_p\ge1:\ D_p\simeq_{\rm aff}\overline B^{d_p};\\
&\exists\text{有限维秩三EJA }J\ \exists\text{实线性双射 }\Psi:V\to J:\quad
\Psi(C)=J_+,\qquad u=\operatorname{tr}_J\Psi.
\end{aligned}
\tag{MC125.19}
$$

只要任一项成立，$\delta(C)=3$。相对于最低 $p_C$ 的全部原纯射线秩一、全Pair、Inj、完整S及同单位静态Jordan字典均成立。一般支路仍包含全部秩三EJA，不仅包含复型。

证明。先从第一项出发。定理125.4已经独立支付原锥的整个双曲分支身份。固定任意 $e\in\operatorname{int}C$，令 $\delta=\delta(C)$，显式指定

$$
h=p_C\,u^{\,3-\delta}.
\tag{MC125.20}
$$

$h$ 是次数恰为三的齐次多项式，$h(e)>0$。线性泛函 $u$ 关于 $e$ 双曲，其闭分支为 $\{u\ge0\}$。乘积特征根是各因子根的并，按重数计，所以

$$
\Lambda_+(h,e)
=\Lambda_+(p_C,e)\cap\{u\ge0\}=C.
\tag{MC125.21}
$$

若 $\delta=3$，零次幂为一；若 $\delta<3$，重复的 $u$ 因子明确保留。这里并未因(MC125.21)就声称ROG相同。

现在 $(V,h,e,C,u)$ 满足124.1的**全部**前件：恰三次、整个实际分支、尖、满维、原严格正单位，以及(MC125.4)的完整原对象。正维球条件也是124.3原来的全称条件。直接调用已发表定理124.3，取得相对于这个指定 $h$ 的ROG与全Pair；其证明中的PE、法向矛盾和秩二排除不重证为本章成果。

Ito—Lourenço Proposition 3.5(i)要求的恰是正则且相对于指定多项式ROG，故可用于 $h$：$h$ 已是产生该整个双曲锥的最低次数多项式。可是 $p_C$ 本身也双曲且产生同一整个锥，次数为 $\delta\le3$，所以 $3\le\delta$，于是 $\delta=3$，$h=p_C$。这一步准确排除了增广因子，不将“相同锥”当作“相同秩”。也可读出其秩代价：当 $\delta<3$，任意归一原纯点 $p$ 的 $u$ 因子各贡献一个非零根，故

$$
r_h(p)=r_{p_C}(p)+(3-\delta),\qquad r_{p_C}(p)\ge1.
\tag{MC125.22}
$$

后一不等式用Ito—Lourenço Proposition 2.4(iv)的尖锥秩零判据及 $u(p)=1$；因此低次数时不可能得到相对于 $h$ 的秩一。这与前述最低性证明完全一致。

随后直接调用124.4，或等价地将已得全Pair与完整EB交给VII103.4、103.6及其完整S／Jordan桥，得到(MC125.19)第二项。所有这些分类步骤都是复用；本章新增入口已在定理125.4及(MC125.20)—(MC125.22)中支付。

反向，设第二项成立。秩三EJA的三次Jordan行列式 $\det_J$ 在平方锥的整个边界为零，成熟谱定理给它关于 $1_J$ 的双曲性及整个平方锥分支。拉回 $\det_J\circ\Psi$ 是原整个边界的三次方程，故 $\mathsf{AB}_{\le3}$ 成立。VII103.6和124.4的完整同单位反向把原 $K,P,[0,u]$ 与每个全确认族、最低函数、整个Peirce-zero排除球同时运输，给全部 $d_p\ge1$。它适用于任意原严格正 $u$，其规范迹匹配已经由原同单位表示支付。前向证明再给 $\delta=3$；并且最低生成元整除同次数的 $\det_J\circ\Psi$，所以

$$
p_C=\kappa\,\det_J\circ\Psi\qquad(\kappa>0),
\tag{MC125.23}
$$

其中符号按原内部为正归一。证毕。

全部支路与尺寸直接复用124.4、VII103.7和VIII113.7：

| 秩三EJA | $\dim_{\mathbb R}V$ | 全部完整 $D_p$ 的维数 |
| --- | --- | --- |
| $\mathbb R\oplus\operatorname{spin}_d$，$d\ge1$ | $d+2$ | 旗标为 $d$，球源为 $1$；$d=1$ 是经典三角形 |
| $H_3(\mathbb R)$ | $6$ | 全部 $2$ |
| $H_3(\mathbb C)$ | $9$ | 全部 $3$ |
| $H_3(\mathbb H)$ | $15$ | 全部 $5$ |
| $H_3(\mathbb O)$ | $27$ | 全部 $9$ |

$\operatorname{spin}_d=\mathbb R\oplus\mathbb R^d$ 取秩二规范迹 $2t$。第一行穷尽非简单的秩分拆 $1+2$ 与 $1+1+1$；其完整原态为旗标与整球的join，$D_f$ 为整球、$D_{b_n}=[f,b_{-n}]$。因此不能凭“次数三”“存在一张三球”或“实维九”就删去可约支路。一般的 $1+2$ 边界交在加完整EB之后才被本定理约束为此Jordan支路；三线性最低方程则对应经典三角形。

为明确一般支路的全部静态范围，写 $\Psi p=c$ 为本原幂等元，$1_J$ 为Jordan单位。用同一个 $\Psi$，全部效应和确认切片为

$$
\begin{gathered}
f_a(x)=\operatorname{tr}_J(a\circ\Psi x),\qquad 0\le a\le1_J,\\
\mathcal F_p=\{f_{c+b}:b\in J_0(c),\ 0\le b\le1_J-c\},\\
\mathcal T_p(x)=\operatorname{tr}_J(c\circ\Psi x),\qquad
D_p=\Psi^{-1}\{y\in J_+\cap J_0(c):\operatorname{tr}_Jy=1\}.
\end{gathered}
\tag{MC125.24}
$$

这是VII103.6的成熟Peirce及全效应字典；全确认族中的正补块使最低值由 $b=0$ 取得。它包括旗标中央质量、实与四元分支，以及Albert分支的本原幂等元；不把非结合八元向量的任意外积当作全部纯态参数。对任意 $x\in C\setminus\{0\}$，质量仍为 $u(x)=\operatorname{tr}_J\Psi x$；零向量由同一映射送到零，不作归一。有限数学测量对应全部 $a_j\ge0$、$\sum_ja_j=1_J$，实际可调用性继续由125.11的原合同承担。

### 125.9 全部三球已选择完整复三能级，无须另给种子或Inj

**定理 125.7（整个低次边界的复量子候选）。** 在125.1的原闭尖满维有限维锥与严格正原单位上，下列条件等价：

$$
\boxed{\begin{aligned}
&\mathsf{AB}_{\le3}+\mathrm{EB3};\\
&\exists\text{实线性双射 }\Psi:V\to\operatorname{Herm}_3(\mathbb C):
\quad\Psi(C)=\operatorname{PSD}_3,\quad\operatorname{Tr}\Psi=u.
\end{aligned}}
\tag{MC125.25}
$$

这里EB3始终量化每个实际原纯点的**整个**最低零集。此等价不另输入Inj、固定种子、三线性参数族、九维、PR、least或全Pair；它们中适用的静态结论由同原表示供应。$\delta(C)=3$ 也是后果。

证明。第一项由定理125.6给全部秩三EJA。可约支路有球源的完整线段排除集，违反全部 $d_p=3$，故被排除。四个简单支路的完整球维数分别为 $2,3,5,9$，仅 $H_3(\mathbb C)$ 留下。这里复用VII103.7的准确类型选择，不重作Jordan或射影平面分类。所得同单位表示就是第二项。反向，$\det\circ\Psi$ 覆盖原整个边界，故最低次数至多三；同一个锥同构及其对偶运输全确认族，124.8和VII103.8的完整反向给全部原 $D_p$ 为三球。证毕。

**同一映射的完整静态字典。** 对(MC125.25)中的同一个 $\Psi$，令 $\rho=\Psi x$，则

$$
\begin{gathered}
\Psi(C)=\operatorname{PSD}_3,\qquad
\Psi(K)=\{\rho\succeq0:\operatorname{Tr}\rho=1\},\\
\Psi(P)=\{vv^*:v\in\mathbb C^3,\ v^*v=1\},\\
\mathcal E=\{f_A:f_A(x)=\operatorname{Tr}(A\Psi x),\quad0\preceq A\preceq I_3\}.
\end{gathered}
\tag{MC125.26}
$$

$\mathbb C^3$ 的全部非零向量按复相位及非零缩放识别成全部原纯射线；单位向量参数给迹一原纯点，无纯轨道缩减。对每个原 $p$，写 $\Psi p=vv^*$、$v^*v=1$，则

$$
\begin{gathered}
\mathcal F_p=\{f_A:A=vv^*\oplus B
\text{ 于 }\mathbb Cv\oplus v^\perp,\quad0\preceq B\preceq I_{v^\perp}\},\\
\mathcal T_p(x)=v^*\Psi(x)v\quad(x\in C),\\
D_p=\Psi^{-1}\{\rho\succeq0:\operatorname{Tr}\rho=1,\ \rho v=0\},\\
\mathcal T_p(q)=|v^*z|^2\quad\text{若 }\Psi q=zz^*,\ z^*z=1.
\end{gathered}
\tag{MC125.27}
$$

这些公式直接消费124.8的完整全效应运输，其输入只需同锥同单位表示，因此取 $C$ 替代其中的特定族 $C_\tau$ 即可。具体而言，对偶双射整个正泛函锥，保迹双射整个效应区间及其确认切片；$0\preceq I-A$ 与 $v^*(I-A)v=0$ 给 $(I-A)v=0$，从而确认族确为上述全补块。每个补块在全部PSD输入上非负，$B=0$ 可取，最低值于是恰由秩一效应取得。PSD性给 $v^*\rho v=0\Longleftrightarrow\rho v=0$，所以是整个二能级密度三球，不是所选球片或纯零图。

对每个有限结果数，全部 $f_j\in C^*$、$\sum_jf_j=u$ 恰对应全部 $A_j\succeq0$、$\sum_jA_j=I_3$，原评价逐项为Born值 $f_j(x)=\operatorname{Tr}(A_j\rho)$。若 $x\ne0$，其原质量 $m=u(x)>0$，唯一归一态为 $\rho/m$；若 $x=0$，则 $\rho=0$、全部读数及最低值为零，不强定零质量的归一条件态。效应补、零效应、单位效应与全部有限凸混合均由这一映射保持。

| 通常的量子公理或对象 | 该几何候选的准确对应与范围 |
| --- | --- |
| 复三维Hilbert空间及相位射线 | 所得同一表示中的 $\mathbb C^3$ 与全部 $\mathbb{CP}^2$ |
| 全部密度态与混合 | 整个原 $K$ 对应全部迹一PSD矩阵，原线性凸混合原样运输 |
| 全效应、Born规则与数学POVM | 整个 $[0,u]$ 及全部有限单位和效应族，原读数为迹配对 |
| 确认、最低比较与完整排除 | 全确认族、秩一least、全部纯—纯模方及完整二能级密度三球 |
| 单位、中心、谱与Jordan结构 | 原 $u$ 为迹，中心为 $\Psi^{-1}(I_3/3)$，成熟谱及Jordan积在所得完整模型中使用 |
| 正交框架与数学面压缩 | 全部正交完备基及 $X\mapsto QXQ$；原过程中的实现另有合同 |
| 全有限纠缠联合与全旁观CP | 单体结论未供应其原锥、产品、资源与共同表示，仍需125.11的完整输入 |
| 实际事件、仪器、Lüders与记录 | 保留事件提升、预算、接线、饱和与校准条件；数学POVM不替代它们 |
| 原时间、Hamiltonian、能量与 $\hbar$ | 继续由实际动态来源与单位标定承担；静态几何不选择数值或动力学 |

### 125.10 在固定原E0中的双向条件链与未付自动性

这里的 $\mathsf E_0$ **仍恰为**SAME_READBACK127.1、129.1的固定完整入口：非零有限维原 $V$，原闭尖生成锥 $C$，严格正的同一原 $u$，以及整个 $K,P,[0,u]$ 与原最低定义；全纯EB3；原标签Inj；一组含 $P_0$ 顶点的实际原正交三角 $(p_1,p_2,p_3)$；同一三角全部原零效应的联合分离；由其限制配对唯一确定的三个规范 $T_i$ 的全原锥正性。准确地，后两项仍为

$$
\begin{gathered}
\forall x,y\in K:\quad
\bigl[\forall i\ \forall b\in[0,u],\ b(p_i)=0\Rightarrow b(x)=b(y)\bigr]
\Rightarrow x=y,\\
M_i=\operatorname{span}D_{p_i},\quad T_i:V\to M_i,\quad
h(T_i x)=h(x)\quad(h\in\operatorname{span}N_{p_i},\ x\in V),\quad
T_i(C)\subseteq C.
\end{gathered}
\tag{MC125.28}
$$

$P_0=\{p:\mathcal A_p\text{ 为单点}\}$，其中 $\mathcal A_p=\{f\in\mathcal F_p:f|_{D_p}=0\}$；这些都是整个原确认族的定义，不是假定只有一张确认效应。联合分离量化全部相关零效应；规范压缩的正性量化整个 $C$。

**推论 125.8（原E0内的低次边界诊断）。** 在这个固定 $\mathsf E_0$ 中，以下条件等价：

$$
\mathsf{AB}_{\le3}
\quad\Longleftrightarrow\quad\delta(C)=3
\quad\Longleftrightarrow\quad\mathsf{PC1}
\quad\Longleftrightarrow\quad\mathsf{IC}_0
\quad\Longleftrightarrow\quad\text{(MC125.25)的同原完整PSD}_3\text{表示}.
\tag{MC125.29}
$$

证明。低次数与同原表示的等价由定理125.7，且给最低次数恰为三。其余等价直接复用SAME_READBACK定理127.11、129.8和130.5，不再证明全域纯压缩升级、原 $P_0$ 稠密性或谱分类。反向的表示将三次行列式拉回到**整个**原边界，故无需另加代数性。证毕。

为保留这些复用项的实际原义，PC1仍是同一种子的

$$
\forall p\in P\ \exists i\in\{1,2,3\}:\Delta_i(p)=0,
\tag{MC125.30}
$$

即至少一个 $T_ip$ 为原极射线向量或零；它等价于 $D_p$ 碰到至少一张完整种子球，或 $(p+p_i)/2$ 至少有一个位于原相对边界。$\Delta_i$ 与共同正定型 $B$ 均取127.2、129.1原定义，不能改成另选的环境二次式。$\mathsf{IC}_0$ 仍为

$$
\forall p\in P_0:\ D_p\cap I\ne\varnothing,\qquad
I=\left\{\frac w3+v:v\in\ker u,\ \|v\|_B^2\le\frac16\right\},
\quad w=p_1+p_2+p_3.
\tag{MC125.31}
$$

$1/6$ 是同一仿射中心 $w/3$ 下的半径平方，不是接触态的原点范数平方；后者在接触处为 $1/2$。这两个数及固定内球包含、点态三零等价均按129.3—129.4复用，不从本章一般代数性另推。点态PC1与点态三次纯压缩仍不同；(MC125.29)使用的是全原量词的既有升级。IX120.9的 $P_0$ 稠密、THREE_COPY VII121.6的稠密 $G_\delta$ 和原宽度紧层也仅沿这些原消费者使用，不重计新结果。

在已得同原表示后，可按127.11的同种子反向选坐标，使 $\Psi p_i=E_{ii}$、$\Psi w=I_3$、$B(x,y)=\operatorname{Tr}(\Psi x\Psi y)$，且原规范压缩恰为角压缩。于是 $\Psi^{-1}((I_3-\Psi p)/2)$ 给每个原完整球与上述固定内球的实际接触，全部原态、效应及最小值继续使用同一个 $\Psi$。这些是既有反向的准确消费者，不把预选矩阵投影放进原入口。

**仍未解决的原桥。** 本章没有证明

$$
\mathsf E_0\Longrightarrow\mathsf{AB}_{\le3},
\qquad\text{因而没有证明}\qquad
\mathsf E_0\Longrightarrow\mathsf{PC1}/\mathsf{IC}_0.
\tag{MC125.32}
$$

它也未构造满足完整E0而失败这些条件的同域模型。(MC125.29)给的是一个新的全局几何诊断与有界充分入口，不改变原任务完成判据。三张种子完整三球、三元有限读回的线性代数，乃至某个选定三次式在这些窗口上为零，都未供应整个边界的三次方程。EXCLUSION X128.2的中心关系代数生成严格不足与 $\ell^1$ 闭包结论，原本就限定于已指定标准复模型；它不支付未知E0锥的代数边界，也不把一般中心相容性或CS补齐。

$\mathsf{AB}_{\le3}$ 是显式附加的全局代数条件。在固定E0内它与旧条件等价，未被证明是E0的后果，也没有独立性、最少独立公理或更少物理假设的结论。完整的原量子重构目标继续包括下面全部非静态合同。

### 125.11 SECTION127.10及完整传递合同的原文继承

本章引用的是[SAME_READBACK的SECTION127.10][MC125SR]，即第127.10**节**，不是同卷另一个数学定理编号。其完整链为：SECTION127.10到该卷125.11、124.9、123.13，再到EXCLUSION VIII命题113.11及112.9、EXCLUSION IX120.11、THREE_COPY VII121.12与122.14，继续到[INTRINSIC_POLAR VI定义89.7、式(89.13)及89.8—89.10][MC125PolarVI]，并沿其原引用到V88.6、87章、[原生续卷VII][MC125NativeVII]及III的来源、过程、全未来和动态消费者。此处的操作／来源VI是INTRINSIC_POLAR卷，不与另一个整球BILATERAL VI混同。各传递引用取整个原文及其完整前件、对象、作用域和量词，不以以下单体入口替换任何一项。对应文件均列于本章引用。

下列正文逐字引入本卷124.10的完整正文，保留来源公式编号；其中“本族”指来源第124章的族。对本章所得同原复型，所有原对象、全部有限层级及物理合同以同样完整的量词继续承担。

本章完整继承[SAME_READBACK第127.10节][Q124CubicSR]及其全部传递引用，具体包括该卷125.11、124.9、123.13，[EXCLUSION VIII的命题113.11及112.9][Q124CubicEVIII]、[EXCLUSION IX120.11][Q124CubicIX]、[THREE_COPY VII121.12与122.14][Q124CubicTCVII]，以及它们继续指向的VI89.9—89.10、原来源／过程、共同输入和动态消费者。上述继承取各原文的完整前件、原对象及量词；以下对应保留其承担的内容。

**共同来源、全部操作和合法未来。** 同一原装饰元组 $\mathcal O$ 的共同来源域、全部中点实现、概率像紧性、全测试表及闭性、零／单位／补／有界倍增、重复标签与每种同中点实现全部保留。质量遍历全部非负数，含零、次归一与不等质量；过程和参考各有完整相关联合输入域。原 $L,p,\omega,K,M$、两次同一读回、两实张成、全实关系、完整(83.8)、VI(89.13)全部两尺度等式、C2、整个 $G=1_E$、精确PRE后的整个H13及每个原资格态、活跃块严格负方向、共享总迹一、非活跃零质量和空活跃集，仍由原消费者承担；操作映射 $p$ 与本章纯态标签不混同。

设备／事件／来源绑定、全部菜单分支、实际参考／副本／相关联合、记录／权限／控制、ready／flags、失败／拒绝／停止／销毁／返回、实际混合、原字、全部合法未来及每个中间切口均保留。原生及细化消费者、terminal futures、联合有符号关系、细标签粗归组、记录后的条件未来、source-adoption和资源合同继续在同一共同来源上承担。一个数学球、一张原效应或一个正角压缩没有因此成为可实际调用的来源或接线。

**全部有限联合载体。** 对每个有限 $N\ge1$，仍须提供实际 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成 $C_N$、严格正 $u_N=u^{\otimes N}$、整个 $K_N=C_N\cap\{u_N=1\}$、全部 $P_N=\operatorname{ext}K_N$ 以及完整原效应区间。每个实际分块 $a+b=N$ 均须有

$$
C_a\otimes_{\min}C_b\subseteq C_{a+b}
\subseteq C_a\otimes_{\max}C_b.
\tag{124.27}
$$

同一产品配对、严格张量单位、全部原因子置换及其逆的正性、规范重括号、指定运输下的不连续位置分块都不删减。二份比较仍量化整个实际联合 $S_2$：每个产品或纠缠纯点 $p,q_\ell\in P_2$、每个有限族、全部非负 $t_\ell$ 且和为一，包括零权和重复标签，要求

$$
\mathcal T_p^{(2)}\!\left(\sum_\ell t_\ell q_\ell\right)
=\sum_\ell t_\ell\mathcal T_{q_\ell}^{(2)}(p),\qquad
\mathcal T_p^{(2)}(x)=
\inf_{\substack{f\in[0,u_2]_{C_2^*}\\f(p)=1}}f(x).
\tag{124.28}
$$

仅产品态上的比较不能替代它。三项具名供应仍分别是原低二份 $q=1,2$ 的least／谱性／正面投影及保纯到Jordan桥，唯一实际自复合 $(W_1,W_1,W_2)$ 的直和扇区限制、秩和实维乘法的复型选择，以及同一实际两因子的产品正规形。

非经典支路的 $\mathsf F_{\max}$ 仍要求同一最大复块 $n_r=L\ge2$ 与同一含相位正交基给出

$$
g_r=\sum_{a=1}^L|a\rangle_r|a\rangle_r|a\rangle_r,\qquad
\Delta_r=|g_r\rangle\langle g_r|\in C_3,\qquad u_3(\Delta_r)=L.
\tag{124.29}
$$

其余扇区零，归一原源为 $\Delta_r/L$，不预付三份纯性或实际制备；全经典 $L=1$ 支路按原定理免除此资源。本族所得单体复型的 $L=3$，二、三份秩为九、二十七；高阶整个排除集合不被要求继续满足单体EB3。只有全部联合前件和三项供应齐备后，才消费既有全有限层级结论。

**全旁观CP、实际事件、同族仪器与记录。** 数学全旁观正性仍量化每个 $b\ge0$ 以及任意含纠缠的同一共同输入，要求

$$
(\operatorname{id}_{W_b}\otimes F)(C_{b+m})\subseteq C_{b+n}.
\tag{124.30}
$$

全有限层级及其共同表示已提供后，才沿原Choi桥识别通常CP、矩形跨扇区Kraus和逐输入TP／TNI预算。同一实际事件的CP还需原完整提升、实际探针及相容核；使全部数学CP-TNI分支成为实际事件另需事件饱和选择。共同输入上的预算、接线、记录、粗粒化和校准负责把分支组成同族仪器。仅严格正质量分支作条件归一，零质量分支不强定归一条件态；Lüders更新还要求同一分支的锐效应、接受态中性与输出校准。全部数学POVM、效应和为单位与可执行的共同仪器各按原合同承担。

**原钟、动态来源、能量与数值 $\hbar$。** 原钟、实际动态来源、连续齐次可逆时间群与单位仍是原前件。若另给对全部实时间的连续线性群 $A_t$，满足 $A_0=I$、$A_{s+t}=A_sA_t$、$A_t(C)=C$、$uA_t=u$，生成元只描述该额外给定过程。在重构复块中另给保迹酉时间族后，通常写为

$$
U_t=\exp(-\mathrm itH/\hbar),\qquad
\rho_t=U_t\rho U_t^*,\qquad
\mathcal L(\rho)=-\frac{\mathrm i}{\hbar}[H,\rho],\qquad H=H^*.
\tag{124.31}
$$

量词覆盖该已给时间族的全部原输入与全部实时间。$H$ 的标量平移不改变态作用，时间重标改变生成元尺度却保留静态几何；恒等时间族和非平凡Hamiltonian族可共享全部静态对象。因此实际 $H$、能量标定、数值 $\hbar$、时空和物理空间维数均未由立方分类选出，球面参数也没有被解释成物理时间。

### 125.12 成熟来源、真正新增的入口与纸面边界

| 来源 | 本章使用的准确内容及限制 |
| --- | --- |
| [Sinn][MC125Sinn] Definition 2.1、Lemma 2.5、Proposition 2.9、Remark 2.10、Corollary 2.11 | 整个代数边界、regular且非空的集及补集、纯余维一、有限半代数分量与锥的齐次化。半代数性和regular前件在125.2先支付；不从该文取得任意凸锥的双曲性 |
| [Gouveia—Ito—Lourenço][MC125GIL] §§2.1—2.2 | Proposition 2.2供应整个边界最低方程及整除性；Lemmas 2.5—2.6预设已有双曲锥，不能承担本章的反向入口 |
| [Helton—Vinnikov][MC125HV] Lemma 2.1、§3及§3.2.2 | Lemma 2.1在其algebraic-interior框架谈最低定义方程；一般定义允许内部零点。§3的rigid convexity/RZ与§3.2.2的四次体为成熟边界；不能仅凭“凸且代数”跳过125.4的可删因子证明 |
| [Renegar][MC125Renegar] §2 Proposition 1、Theorems 2—3 | 双曲开分支是无零集的连通分量、闭包与全部内部方向。仅在125.5完成实根检验后使用分支接口 |
| [Ito—Lourenço][MC125IL] Proposition 2.4、Definition 3.1、Remark 3.2、Proposition 3.5(i) | 秩的指定多项式依赖、尖锥秩零判据，以及正则且ROG才有的最低次数结论。锥同一性本身不支付ROG |
| [Netzer][MC125Netzer] Introduction、§1.1 Proposition 1.1 | 讨论已有双曲三次式的正规形及部分维数中的谱面体实现；其正向前件已经是双曲性，不是任意原凸锥的最低边界入口。本章不消费其Clifford实现或以此补一般九维表示 |
| 本卷124.1—124.4、124.8 | 正则立方整个原域中的PE／法向／ROG／Pair消费者、秩三分类与全效应运输，均保留原量词直接复用 |
| VII103.2—103.8及其Library完整S桥；VIII113.7—113.9 | 全部真面、完整S、任意原单位的忠实Jordan分类、全部秩三支路和静态字典，均不重计为本章的新分类 |
| SAME_READBACK127.11、129.8、130.5及SECTION127.10 | 固定E0中的PC1／IC0／同原表示条件链及完整物理合同；不从条件等价冒领E0自动性 |

本章保留的 `repo-derived` 纸面连接是：先从有限边界覆盖和实际紧基精确定位最低次数；以三次以内的四根障碍迫出可删的内部超平面因子，从而排除最低方程内部零点；再由正负原锥的两个真实边界穿越取得全部实根，并用无零分量证明**整个**分支等式。随后显式增广为三次，准确消费124与ROG最低性，把整个边界低次数接为完整EB分类的入口，并在固定E0中接回旧PC1／IC0条件链。新的工作不包含重新证明旧Jordan分类、谱定理、Born字典、ROG接口或四次例子。

所列原始文献中的上述命题没有以任意原凸锥的 $\mathsf{AB}_{\le3}$ 为前件给出这里的完整量子消费者；本章不据有限来源范围作全球原创、优先权、文献穷尽或公理逻辑独立主张。存在性、连通分量、分支和秩的每个接口均按其实际前件使用。本章是纸面定理、证明与条件应用；理论正文及文献都不被提升为形式内核证明。

### 125.13 完整中文图景：窗口像球，不等于整座实体只有三次边界

把整个原状态体想成一块实心实体，所有原效应就是能在这整块实体上合法读零到一的尺。每个纯态背后的完整排除集，是所有能被某张确认它的尺读成零的状态收齐后的集合。要求每个这样的完整集合是三球，控制的是实体上每一扇真实的二能级窗口；它不直接告诉我们整座实体的外壳由几次方程刻出。只展示三个种子窗口，或给出在这些窗口上正确的三次式，仍没有覆盖全部外壳。

本章另加的条件正是全局外壳的复杂度：**整个边界的最低总次数至多三**。最低意味着每个因子都必须为整个外壳承担不可删除的部分；不能为了凑三次，在内部再插一块平板。正卦限的 $xy(x-y)$ 就插入了这样的板：它仍盖住原边界，也仍双曲，但板把原内部切开，选中的分支只剩 $x\ge y\ge0$。最低方程 $xy$ 才描述原整体分支。

为什么最低三次能排除这块内部板？先把锥按一个严格正刻度切成紧凸基。假设最低方程在实体内部某点为零。从这里朝任意方向走，直线的两头还各碰一次真实外壳。若沿某方向的一阶变化也为零，内部零点便至少占两个根，加上两头边界的两个根，三次已经容不下。于是所有一阶零方向上的整条直线都必须为零，拼成一个真正的超平面因子。这个平面穿过内部，从内部看出去只遮住一圈方向，不能独自承担一块外壳；平面以外的全部外壳已由剩余因子覆盖，连续性把遗漏的一圈也补上。因此这块板可删，与最低性矛盾。这里既不要求外壳处处光滑，也不把多项式的切平面偷当成已知的凸支撑面。

内部障碍排除后，从任意内部方向看原锥与其负锥，一条不穿锥轴的直线会在两侧各遇到一个不同真实边界点。二次的根到此已齐，三次只剩一个实一次因子，全部根因此为实。还要再看完整实体：其内部从未经过多项式零点，整个边界又都在零集，所以内部正好占满一个无零连通分量。这样取得的是原锥等于整个闭双曲分支，而不只是边界包含或局部形状相像。

到了这个完整入口，才复用124的几何机制：正维完整排除球与暴露纯点给每条纯射线两个不同支撑方向，立方秩二层却只允许一个；纯射线只能在秩一层。全部两纯点因而留在真面，旧的完整Pair／Jordan桥可以准确消费。若最低次数原本不到三，显式乘上原单位以凑成立方后，额外因子会提高纯射线的相对秩；ROG最低性排除这种情况，所以完整正维球域的最低次数实际恰为三。这个阶段的一般模型仍可能是实、复、四元、八元或旗标加球。要求**每个完整排除集都恰为三球**，才排除所有线段和其他简单类型，留下完整复三能级。

同一个忠实映射随后负责全部对象：所有密度态、所有纯射线、整个效应区间、每个Born读数、全确认族的真正最小值、每颗完整排除三球，以及零和非零质量。没有给不同读数换不同表示，也没有把归一化用于零输入。固定E0中的原种子与固定内球也由旧反向一并读回；低次数条件于是与旧PC1／IC0等价。但“原E0为什么必有这样的整个三次外壳”仍是未证明的桥。它没有被三张圆窗口、一个家族的参数分类或四次反例替代。

因此这里形成了一个完整的**条件静态**量子候选：原全效应凸锥、整个边界最低三次、全部原完整排除三球。它与同原复PSD3字典双向对应；要接回完整物理理论，125.11继承的共同来源、全部操作、任意有限纠缠联合与资源、全旁观CP、事件与同族仪器、记录和全部合法未来、原钟、能量标定及数值 $\hbar$ 仍须各按原完整合同支付。

[MC125Sinn]: https://doi.org/10.1186/s40687-015-0022-0 "Rainer Sinn, Algebraic boundaries of convex semi-algebraic sets；Definition 2.1、Lemma 2.5、Proposition 2.9、Remark 2.10、Corollary 2.11。"
[MC125GIL]: https://doi.org/10.68381/jca33015 "João Gouveia, Masaru Ito and Bruno F. Lourenço, Minimal Hyperbolic Polynomials and Ranks of Homogeneous Cones；§§2.1—2.2，Proposition 2.2及Lemmas 2.5—2.6。"
[MC125HV]: https://arxiv.org/abs/math/0306180 "J. William Helton and Victor Vinnikov, Linear Matrix Inequality Representation of Sets；Lemma 2.1、§3及§3.2.2；DOI 10.1002/cpa.20155。"
[MC125Renegar]: https://optimization-online.org/wp-content/uploads/2004/03/844.pdf "James Renegar, Hyperbolic Programs, and Their Derivative Relaxations；§2 Proposition 1、Theorems 2—3；DOI 10.1007/s10208-004-0136-z。"
[MC125IL]: https://arxiv.org/pdf/2207.11986v3 "Masaru Ito and Bruno F. Lourenço, Automorphisms of rank-one generated hyperbolicity cones and their derivative relaxations；Proposition 2.4、Definition 3.1、Remark 3.2、Proposition 3.5(i)；DOI 10.1137/22M1513964。"
[MC125Netzer]: https://arxiv.org/abs/2609.12957v1 "Tim Netzer, Clifford Realizations of Hyperbolic Cubics；Introduction及§1.1 Proposition 1.1。仅用于区分已有双曲三次式的谱面体路线与本章整个边界入口。"
[MC125SR]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "127.1、127.11、129.1、129.8、130.5：同一完整E0、PC1／IC0及同原静态条件链；SECTION127.10及其全部传递引用：完整原来源、过程、全有限复合、资源、事件、仪器、记录和时间合同。"
[MC125VII]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md "VII103.2—103.8：完整原面、Pair、完整S、同锥同单位的秩三EJA及全部支路和全效应字典。"
[MC125VIII]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_VIII.md "VIII113.7—113.9：整个W域既有分类和谱字典；命题113.11与112.9：全部原联合、操作及时间合同。"
[MC125IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX118及120.4：原宽度上半连续、饱和层与紧层；IX120.9：原P0稠密；IX120.11：全部同原静态对象与完整非静态合同。"
[MC125X]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_X.md "X124.2：EB与PE下两条不同正法向；X128.2：仅标准复模型内中心关系的代数不足与有界闭包，不供应一般E0的三次边界。"
[MC125TCVII]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md "THREE_COPY VII121.6：稠密Gdelta及非塌缩层上的完整确认闭图；121.12与122.14：共同来源、全部有限复合、资源、事件仪器、记录与时间的完整合同。"
[MC125PolarVI]: QUANTUM_ORIGIN_INTRINSIC_POLAR_QUOTIENT_AND_NONCOLLAPSE_VI.md "定义89.7及式(89.13)：同一原装饰元组、原质量、两尺度及整个输出；89.8—89.10：逐消费者、原生／细化、全部原字与terminal futures、联合有符号关系、细标签粗归组、记录后条件未来、source-adoption及资源合同，连同全部传递引用完整继承。"
[MC125NativeVII]: AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_VII.md "INTRINSIC_POLAR VI89.9—89.10所引原生与细化路线：原几何、全部原字及terminal futures、联合菜单、有符号关系、回返、完整校准、source-adoption与来源边界；每条路线只按其完整原入口消费，不由本章低次边界代付。"
[MC125SBridge]: ../../../Library/QuantumStates/mullerududec2012selfduality.md#reciprocal-least-confirmation-and-the-spectrality-bridge "VII103与124所消费的既有完整S／谱性／projectivity／滤子保纯到Jordan桥；其纸面范围保持原样。"
[Q124CubicEVIII]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_VIII.md "VIII113.7—113.9：成熟秩三分类与完整静态字典；命题113.11及112.9的全部原联合、操作和时间合同。"
[Q124CubicSR]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "第127.10节及完整传递引用：来源、全部有限复合、资源、CP、实际事件仪器、记录、全部合法未来及时间；125.11、124.9、123.13、127.1、129.1与PC1／IC0的原范围。"
[Q124CubicIX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX120.11：同一原静态字典及其完整物理合同和引用链。"
[Q124CubicTCVII]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md "THREE_COPY VII121.12、122.14：共同来源、全有限层级、事件仪器、记录及连续时间的完整合同。"

## 追加锚（本行以下为增补区）
