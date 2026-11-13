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

## 追加锚（本行以下为增补区）
