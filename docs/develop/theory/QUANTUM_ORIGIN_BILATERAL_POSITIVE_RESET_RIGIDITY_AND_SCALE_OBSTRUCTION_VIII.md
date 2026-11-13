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
