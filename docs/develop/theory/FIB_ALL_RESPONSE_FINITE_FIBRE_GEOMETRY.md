# FIB all-response finite-fibre geometry

This volume records a uniform finite-fibre consequence of the literal
common-parent model.  It is a continuation of
FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md; that volume is the
source for the complete-world definitions, the clock functions, the
zero-safe lift, and the exact coefficient table cited below.  The new
statement concerns every real response in the acquired sixth-$M$ slot.

## 1. Model and quantifiers

The parent is the literal $H_4$ of Definitions 1.1--1.3 of the
owning volume, with the original clocks $0,\ldots,7$.  A complete
world has the strict source coordinates

$$
0<r<1,\qquad b>0,
$$

the nonnegative rank-one idempotent $P(r,b)$, one entire nonzero real
gain polynomial $g$ of degree at most three, and one fixed real drift
$d$.  Thus a lower-degree gain, a sampled zero, a repeated gain root,
or $d=0$ is still a complete world.  No bound is imposed on positive
off-diagonal coordinates.  The notation

$$
\mathcal F(H_4,M,p,M,v)
$$

means the complete worlds whose fifth response is $p$, whose acquired
sixth response is $v$, and whose two actions are $M$.  The same
entire $g$ and the same $d$ are used in every clock response of one
world.  In particular, $v$ is an arbitrary real number; it is not a
query count, a memory value, or a response already known to be realized.

Put

$$
\mathcal P=\left[\frac{2744214237}{10^8},\frac{2744214238}{10^8}\right],
\qquad
p_0=\frac{219537139}{8000000},\qquad
\rho=\frac1{200000000}.
$$

Thus $\mathcal P=[p_0-\rho,p_0+\rho]$.  The exact parameter $p_J$
supplied by the unique original $F_J$ box root remains the parameter
of the earlier joint-collision question.  The interval $\mathcal P$ is
used here only to prove a uniform algebraic certificate; it does not
replace $p_J$ by its containing interval or by its Taylor centre.

## 2. The zero-safe source interface

Retain $j,n,T,U,V,X,N,H$ and the scalar source equation of
Definitions 12.1--12.3 of the owning volume:

$$
\begin{gathered}
X=b^2+r-r^2,\quad N=X+br,\quad T=1+b,\quad U=1+2b,\quad V=U+n,\\
H(r,b)={}
14b^6+(95-73r)b^5+(47r^2-39r+30)b^4\\
\qquad+r(147r^2-232r+105)b^3
 +2r(1-r)(44r^2-55r+15)b^2\\
\qquad-64r^3(1-r)^2b-32r^3(1-r)^3,\\
N_4=2(b^2+8b+4)XN-4bTU(X+N),\\
\mathsf S_p(r,b)=5b(p-24)N_4+6(8b-1)H(r,b).
\end{gathered}
$$

The symbols $j,n,U,V$ above have exactly the rational expressions in
(1.6) and (12.1) of the owning volume; they are recalled only to fix
the interface.  Theorem 12.3 there is zero-safe: a strict source lifts
to a complete world in $\mathcal F(H_4,M,p)$ if and only if
$\mathsf S_p(r,b)=0$, and the lift is unique.  Its drift and its whole
gain are reconstructed from (12.5)--(12.6), with
$\Lambda^2+A_5^2>0$.  No division by $\Lambda$, by a gain sample, or
by the drift is made in that theorem.  This is why the present source
count includes the singular stratum $\Lambda=0$, degree drops, sampled
zeros, repeated roots, and zero drift.

For arbitrary real $p,v$, use the integer polynomials of Definition
20.1:

$$
\begin{gathered}
D_\Lambda=(b^2+8b+4)XN-2bTU(X+N),\\
K_\Lambda=(8b-1)(2+5b),\qquad Z_6=N+2bU,\\
G_{6,\Lambda}=(10T+45)XN-bT(36N+20X),\\
\mathsf A(r,b,p)=5b(p-24)D_\Lambda+3(8b-1)H(r,b),\\
\mathsf N_u(r,b)=
\frac{120bTD_\Lambda+15Z_6D_\Lambda(80b-1)
       -3K_\Lambda(bTXN+Z_6G_{6,\Lambda})}{T},\\
\mathsf B(r,b,v)=5bD_\Lambda v-\mathsf N_u(r,b).
\end{gathered}
$$

The displayed numerator for $\mathsf N_u$ is divisible by $T=1+b$
in $\mathbb Z[r,b]$, so $\mathsf A,\mathsf B$ are polynomials.  The
published Theorem 20.2 gives, for every nonsingular complete world,

$$
\Lambda\ne0\quad\Longrightarrow\quad
\mathsf A(r,b,p)=\mathsf B(r,b,v)=0.
$$

At the singular branch, the zero-safe parent equation gives $b=1/8$,
and the published identity
$\Lambda=\Phi(r)/(960jn)$ gives a root of

$$
\Phi(r)=438272r^4-931328r^3+540800r^2-50728r-853.
$$

Exact substitution of $b=1/8$ into the two source polynomials gives
$\mathsf A(r,1/8,p)\equiv0$ and
$\mathsf B(r,1/8,v)\equiv0$ modulo $\Phi(r)$.  Consequently every
singular complete world also lies in the affine common zero set of
$\mathsf A,\mathsf B$.  This substitution is an identity modulo
$\Phi$, not a numerical check at either of its roots.

## 3. The fixed resultant and its leading coefficient

Use the ordinary Sylvester determinant in the $b$-variable, with rows
$b^6\mathsf A,\ldots,\mathsf A,b^6\mathsf B,\ldots,\mathsf B$, and
columns $b^{13},\ldots,1$.  With that row order and descending column
order the owning volume defines $R_{18}\in\mathbb Z[r,p,v]$ by

$$
\operatorname{Res}_b(\mathsf A,\mathsf B)=
52488000\,r^{11}(r-1)^9\Psi_2(r)\Psi_4(r)\Phi(r)R_{18}(r,p,v),
$$

where

$$
\Psi_2=4r^2-2r-1,\qquad
\Psi_4=625r^4-1000r^3+50r^2+260r+36.
$$

The full 668-row coefficient table in Definition 24.1 of the owning
volume fixes every coefficient, its sign, and its scale.  It has
coordinate degrees $(18,7,7)$.  We use that table as a supplier and do
not reassert a new determinant expansion.  The only coefficient needed
for the noncollapse certificate is

$$
a(p,v)=[r^{18}]R_{18}(r,p,v)/750.
$$

The exact polynomial $a$ is listed here so that the three finite
certificates below are independently reproducible:

$$
\begin{aligned}
a(p,v)={}&375948000000p^6-418003200000p^5v
 +288640130400000p^5\\
&+186930540000p^4v^2-244797381360000p^4v
 +51693650192250000p^4\\
&-42997996000p^3v^3+79681441734000p^3v^2
 -29092711350411000p^3v\\
&-1741101916388796000p^3+5366228175p^2v^4
 -12467265195600p^2v^3\\
&+5840320948875225p^2v^2+1078183709895925800p^2v
 -118733074263213807600p^2\\
&-344286720pv^5+935826559920pv^4-482166542464920pv^3\\
&-213631924877591760pv^2+40225716516510210240pv
 +319744607467047114240p\\
&+8847360v^6-26775318528v^5+12935750417856v^4\\
&+13703870337816960v^3-3387392590125035520v^2\\
&-69057672384839625216v+1575043434745240919040.
\end{aligned}
$$

The leading $b$-coefficients supplied by the same exact expansion are

$$
[b^7]\mathsf A=5p+216,\qquad [b^7]\mathsf B=5(v+225).
$$

The second coefficient may vanish at $v=-225$; the proof below never
divides by it and therefore retains that degree-drop response.

## 4. Three endpoint resultants

Define the three source factors

$$
\begin{aligned}
\ell(p,v)&=32p-5v-366,\\
q_2(p,v)&=9000p^2-1300pv-175350p-1600v^2+225120v-6050961,\\
q_3(p,v)&=51072900p^3-38068700p^2v-1933224270p^2
 +8423500pv^2\\
&\qquad+601454235pv+10167680250p-581725v^3
 -45839880v^2\\
&\qquad-1393526691v+136430551152.
\end{aligned}
$$

These are the exact factors of the constant $r$-coefficient of the
published eliminant:

$$
[r^0]R_{18}=4\,\ell(p,v)^2q_2(p,v)q_3(p,v).
$$

For $q\in\{\ell,q_2,q_3\}$, define

$$
h_q(p)=\operatorname{Res}_v(a(p,v),q(p,v)),
$$

using the Sylvester convention “rows $v^{\deg q-1}a,\ldots,a,
v^{\deg_v a-1}q,\ldots,q$, descending powers of $v$”.  Direct exact
determinant arithmetic gives

$$
\deg h_\ell=6,\qquad \deg h_{q_2}=12,\qquad \deg h_{q_3}=18.
$$

Write the exact Taylor expansion at $p_0$ as

$$
h_q(p_0+x)=\sum_{k=0}^{d_q}c_{q,k}x^k,\qquad
c_{q,k}=\frac{h_q^{(k)}(p_0)}{k!}.
$$

All $c_{q,k}$ are rational numbers obtained from the displayed
integer $a,\ell,q_2,q_3$.  The following exact centre values fix the
sign convention and make the certificate checkable without decimal
rounding:

$$
c_{\ell,0}=
-\frac{22840206648135224684886839221025303806888962919613986118771951297}
{204800000000000000000000000000000000000}.
$$

$$
c_{q_2,0}=
\frac{443153376328343297403565417619374492622356576324586886804391963989452371419561183592818218165812936928539051759444687913047209}
{42949672960000000000000000000000000000000000000000000000000000}.
$$

$$
c_{q_3,0}=
-\frac{249292213177920260587921798396202459094574674761398997314883645219831972907966464804515795331161057601078458718621360983131758601621876870283082616244067818491635995621397422750833612971017368938124664686156799941}
{2305843009213693952000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000}.
$$

For the full interval, use the triangle inequality with the exact
rational tail

$$
T_q=\sum_{k=1}^{d_q}|c_{q,k}|\rho^k.
$$

The determinant expansions give the following strict rational
comparisons (each numerator and denominator is an integer, so these are
finite checks by cross multiplication):

$$
\frac{T_\ell}{|c_{\ell,0}|}
=\frac{978496224399822570290500553163904466734775767616344379260517823}
{5576222326204888839083700981695630812228750712796383329778308422119140625}
<\frac1{10^7},
$$

$$
\frac{T_{q_2}}{|c_{q_2,0}|}
=\frac{1256215045437611300727955943158594487623648052039334862433103870054512752255533404065861333248836831488443429861488642380102843311827}
{978296280632070473837776134675022612285518152458992019415767025041254298376951358037564971194913954488743348826842590422646224498748779296875}
<\frac1{10^7},
$$

$$
\frac{T_{q_3}}{|c_{q_3,0}|}
=\frac{4801674575923910293032911669758394096310133953585441890260494008812575371314294165386061144684088024820914941266688415690349160120798053268625580066122953600124403670719638962746808419373562909085451057877465147905487754550707}
{134358487157668644896476567479356275642108906651911199266886302599748064546086170488849810084858961852365722447856528248549395142548815040199747166934856374504245142679535084662123383287483425799143186243361345012090168893337249755859375}
<\frac1{10^7}.
$$

Therefore, for $|x|\leq\rho$,

$$
|h_q(p_0+x)-c_{q,0}|\leq T_q<|c_{q,0}|/10^7<|c_{q,0}|.
$$

In particular each $h_q$ is nonzero on all of $\mathcal P$, with
signs $\operatorname{sgn}(h_\ell)=-1$,
$\operatorname{sgn}(h_{q_2})=+1$, and
$\operatorname{sgn}(h_{q_3})=-1$.  This is a Taylor enclosure of the
full interval, not three point evaluations.

## 5. Uniform noncollapse of the eliminant

**Lemma 5.1 (No common leading/constant coefficient).** For every real
$p\in\mathcal P$, the polynomial $a(p,v)$ has no common complex root
with any of $\ell(p,v),q_2(p,v),q_3(p,v)$.

**Proof.** The Sylvester criterion says that a common complex root would
make the corresponding $h_q(p)$ vanish.  Section 4 proves that all
three resultants are nonzero on $\mathcal P$. ∎

**Theorem 5.2 (Uniform noncollapse).** For every real
$p\in\mathcal P$ and every real $v$, $R_{18}(r,p,v)$ is not the
zero polynomial in $r$.

**Proof.** If $R_{18}$ were identically zero in $r$, its leading
coefficient $750a(p,v)$ and its constant coefficient
$4\ell(p,v)^2q_2(p,v)q_3(p,v)$ would both vanish.  The latter forces
one of $\ell,q_2,q_3$ to vanish at the same complex pair $(p,v)$,
contradicting Lemma 5.1.  Thus $R_{18}$ is nonzero for every real
$(p,v)$ in the stated domain. ∎

The argument does not require $v$ to lie in the previously published
finite necessary response set.  It also does not assert that a root of
$R_{18}$ is real, strict, or liftable.

## 6. Zero-dimensional source intersection

**Lemma 6.1 (Finite source intersection).** Fix real $p\in\mathcal P$
and real $v$.  The affine complex common zero set of
$\mathsf A(r,b,p)$ and $\mathsf B(r,b,v)$ has no positive-dimensional
component.

**Proof.** By Theorem 5.2 and the exact factorization of the resultant,
$\operatorname{Res}_b(\mathsf A,\mathsf B)$ is not the zero polynomial
in $r$.  Hence $\mathsf A,\mathsf B$ have no common factor of
positive $b$-degree in $\mathbb C[r,b]$.  A common factor depending
only on $r$ would divide every coefficient of $\mathsf A$, in
particular its $b^7$-coefficient $5p+216$.  Since
$p>24$, this coefficient is a nonzero scalar, so no nonconstant
$r$-factor is possible.  Thus the two polynomials have no common
curve component. ∎

The proof remains valid at $v=-225$: the $b^7$-coefficient of
$\mathsf B$ may drop there, but no leading coefficient is divided out.
The fixed Sylvester determinant and its common-finite-root implication
are valid under this specialization.

## 7. The all-response 49-world bound

**Theorem 7.1 (Uniform all-real-response finite fibre).** For every
real $p\in\mathcal P$ and every real $v$,

$$
\left|\mathcal F(H_4,M,p,M,v)\right|\leq49.
$$

This includes lower-degree gains, sampled zeros, repeated gain roots,
zero drift, unbounded positive offdiagonals, the singular branch
$\Lambda=0$, and the source-degree drop $v=-225$.

**Proof.** By Section 2, every complete world gives a unique strict
source $(r,b)$ in the published source parametrization.  A nonsingular
world satisfies $\mathsf A=\mathsf B=0$ by Theorem 20.2, and a singular
world satisfies the same equations by the exact $\Phi$-remainder
identity in Section 2.  Thus all complete worlds inject into the strict
part of the common affine zero set of $\mathsf A,\mathsf B$.

Both polynomials have total degree at most seven.  Lemma 6.1 removes
common components.  Affine Bézout, applied after homogenizing in
$(r,b)$, bounds the sum of intersection multiplicities in the
projective plane by $7\cdot7=49$; affine distinct points are a
subset of those points.  Theorem 12.3 gives at most one complete world
over each strict source, including every zero-safe singular or degree
drop case.  Therefore the complete-world fibre has at most $49$
distinct worlds. ∎

The Bézout step is the standard affine/projective intersection theorem;
the source-specific work is the noncollapse certificate and the
zero-safe injection.  No projected root is counted as a world unless it
is real, strict, and liftable, so the bound is conservative.

## 8. Interface with the remaining collision problem

The prior finite-response theorem supplies a necessary restriction at
the exact inherited $p_J$: any child containing a distinct terminal-$M$ pair has $v$ among the real roots of its determinant-defined
$Q(p_J,v)$, together with the two explicit singular responses
$s_-(p_J),s_+(p_J)$.  The present theorem supplies a complete-world
upper bound for each such candidate, and in fact for every real $v$.
It does not replace the inherited $p_J$ by $\mathcal P$, and it does
not claim that any candidate response is realized.

For a fixed candidate $v$, the remaining exact task is finite but
unsettled.  Form the radical source algebra over the ordered algebraic
field generated by $p_J,v$, retain only real strict points satisfying
$\mathsf S_{p_J}=0$, and use the zero-safe reconstruction of Theorem
12.3.  In the tensor square of that algebra impose the terminal-$J$
or terminal-$M$ equality, the strict guards for both sources, and

$$
(r-r')^2+(b-b')^2>0.
$$

Exact Hermite/Tarski signatures can then count the two kinds of ordered
distinct pairs.  The same labels may occur in both pairs.  A positive
count for each pair at one common $v$ would settle the local
same-child witness; a zero count for either pair at every candidate
would exclude it.  Neither alternative is asserted here.  The
original exact $p_J$, all-response simultaneous pairs, common-parent
and all-fifth-response obligations, global eight-versus-nine question,
full-domain nine-sufficiency question, and any physical interpretation
remain unchanged.

## 9. Sources and boundaries

The model, clocks, source coordinates, zero-safe lift, and the exact
$R_{18}$ coefficient table are supplied by
FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md, Definitions 1.1,
12.1, 20.1, 24.1 and Theorems 12.3 and 20.2.  The affine resultant and
Bézout facts are standard; see Cox--Little--O'Shea, *Ideals, Varieties,
and Algorithms*, Chapter 3.  Univariate resultants and the root-counting
interface have the standard real-algebraic background in Basu--Pollack--
Roy, *Algorithms in Real Algebraic Geometry*.  These references supply
general algebraic methods, not the FIB-specific certificate.

The exact three Taylor enclosures above are the new source-specific
finite rational certificate.  They prove noncollapse on the whole
$\mathcal P\times\mathbb R$; they do not rerun or reprove the published
668-term determinant identity.  No exhaustive novelty claim, Lean
formalization, ingestion status, feasibility decision, candidate count,
or publication status is part of this volume.

## 追加锚（本行以下为增补区）

## 10. Multiplicity allocation and the eighteen regular-world bound

**Definition 10.1 (Complex regular source fibres).** Write $O$ for
[the owning common-parent volume](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md),
$E$ for [the exact response-strip volume](FIB_EXACT_RESPONSE_STRIP_AND_JOINT_COLLISION_EXCLUSION.md),
and $S$ for [the singular-response exclusion volume](FIB_SINGULAR_RESPONSE_CHILDREN_EXCLUSION.md).
Retain the exact polynomials of Sections 2–3 and set
$D=D_\Lambda$, $R=R_{18}$ and
$E_0=\Psi_2\Psi_4\Phi$. For real $p\in\mathcal P$ and complex $v$,
define

$$
\mathcal Z(p,v)=\{(r,b)\in\mathbb C^2:
 r(r-1)bD(r,b)\ne0,\quad
 \mathsf A(r,b,p)=\mathsf B(r,b,v)=0\}.
\tag{10.1}
$$

This is an algebraic counting domain; its complex points are not
asserted to be legal worlds. Its strict real points correspond to
regular complete worlds by $O$, Theorem 12.3 and (20.8)–(20.9), or
$E$, Lemma 3.3. In particular every regular world of the original
child has one distinct point in (10.1).

**Theorem 10.2 (Uniform regular-source and regular-world bound).**
For every real $p\in\mathcal P$ and every complex $v$,

$$
|\mathcal Z(p,v)|\le18.
\tag{10.2}
$$

Consequently, for every real $p\in\mathcal P$ and real $v$,

$$
\bigl|\{W\in\mathcal F(H_4,M,p,M,v):\Lambda(W)\ne0\}\bigr|
\le18.
\tag{10.3}
$$

The count includes multiple sources above the same projected root,
fixed base projections, repeated projected roots and specialized
source-degree drops.

Proof. First $R(r,p,v)$ is a nonzero polynomial in $r$ even when
$v$ is complex. Indeed, if it were zero, its leading and constant
coefficients from Sections 3–4 would give

$$
a(p,v)=0,\qquad \ell(p,v)^2q_2(p,v)q_3(p,v)=0.
\tag{10.4}
$$

Lemma 5.1 excludes a common complex root of $a(p,\cdot)$ and any
of $\ell(p,\cdot),q_2(p,\cdot),q_3(p,\cdot)$ for every such real
$p$. This proves the required extension of the noncollapse argument.

Let $\mathsf S(r)$ be the fixed $14$ by $14$ Sylvester matrix of
Section 3, at the present $p,v$. Its determinant is

$$
\det\mathsf S(r)=52488000r^{11}(r-1)^9E_0(r)R(r,p,v).
\tag{10.5}
$$

The coefficient $[b^7]\mathsf A=5p+216$ is a nonzero scalar.
Thus at each fixed complex $r=\alpha$ there are at most seven
finite common $b$ roots. Each distinct common root $t$ supplies
the null vector $(t^{13},t^{12},\ldots,1)^{\mathsf T}$ of
$\mathsf S(\alpha)$. The vectors for distinct roots are linearly
independent by the Vandermonde determinant. Hence the corank of
$\mathsf S(\alpha)$ is at least their number.

If a polynomial matrix has corank $k$ at $\alpha$, its determinant
vanishes to order at least $k$. To see this, apply constant
invertible row and column operations putting its value at
$\alpha$ in rank normal form. The last $k$ columns then have all
entries divisible by $r-\alpha$. Multilinearity of the determinant
gives the assertion. This is the corank argument of $E$,
Lemma 4.3, with the number of roots unrestricted up to seven.

For $\alpha\notin\{0,1\}$ let $n_\alpha$ count the points of
$\mathcal Z(p,v)$ above $\alpha$, and let
$m_\alpha=\operatorname{ord}_{r=\alpha}R(r,p,v)$, with value zero
when $R(\alpha,p,v)\ne0$. If $E_0(\alpha)\ne0$, (10.5) and the
corank inequality give $n_\alpha\le m_\alpha$.

If $E_0(\alpha)=0$, $E$, Lemma 4.2, supplies an additional finite
common root with $D=0$ for every $p,v$:

| Vanishing factor | Additional common root $b$ |
| --- | --- |
| $\Psi_2$ | $-1/2$ |
| $\Psi_4$ | $-2/5$ |
| $\Phi$ | $1/8$ |

These identities are polynomial substitutions over $\mathbb Q$,
so hold at complex roots and complex responses. The same lemma
proves that the three factors are squarefree and pairwise coprime.
Thus $E_0$ has order exactly one at $\alpha$. The additional
$D=0$ root is distinct from every point counted by $n_\alpha$.
The corank is at least $n_\alpha+1$, whereas (10.5) has order
$1+m_\alpha$. Again $n_\alpha\le m_\alpha$.
This includes every intersection of a fixed base projection with
an $R$ root, without a nonzero linear-subresultant premise.

Every nonempty fibre therefore projects to a root of the nonzero
$R$, and

$$
|\mathcal Z(p,v)|
 =\sum_{\alpha\ne0,1}n_\alpha
 \le\sum_{\alpha\ne0,1}m_\alpha
 \le\deg_r R(r,p,v)\le18.
\tag{10.6}
$$

The fixed matrix and its evaluation vectors remain valid when the
$b$ degree of $\mathsf B$ drops, in particular at $v=-225$.
No simplicity of an $R$ root or uniqueness of its $b$ lift was
used. Finally, $O$, Theorem 12.3, makes the complete-world lift
unique at each strict source, and (20.8) identifies $D\ne0$ with
$\Lambda\ne0$ there. This proves (10.3), including all gain and
drift strata in Section 1. ∎

## 11. Finiteness of the complex distinct-pair locus

**Definition 11.1 (Complex response map at the original parameter).**
Throughout Sections 11–13, $p_J$ is precisely $O$ (8.4), evaluated
at the unique zero of $O$ (8.1) in its original box
$\mathcal B_J$. In particular $p_J\in\mathcal P$ by $O$,
Theorem 8.1. Set

$$
D_m=5bD,\qquad N_u=\mathsf N_u,
\tag{11.1}
$$

and use exactly $N_m$ of $O$ (27.1). The polynomials
$D_m,N_u,N_m$ have total degree at most seven, as in $E$ (3.6).
Define

$$
\begin{aligned}
\mathcal X&=\{x=(r,b)\in\mathbb C^2:
 \mathsf A(r,b,p_J)=0,\ r(r-1)D_m(r,b)\ne0\},\\
u(x)&=N_u(x)/D_m(x),\qquad m(x)=N_m(x)/D_m(x),\\
\mathcal K&=\{(x,y)\in\mathcal X^2:
 x\ne y,\ u(x)=u(y),\ m(x)=m(y)\}.
\end{aligned}
\tag{11.2}
$$

On legal regular worlds, $u=u_M$ and $m=f_{MM}$ by $O$ (20.9)
and Theorem 27.2. Outside those real sources these are the stated
rational maps, with no world interpretation required.

**Theorem 11.2 (Every complex distinct pair has an exceptional response).**
For every $(x,y)\in\mathcal K$,

$$
Q(p_J,u(x))=0,
\tag{11.3}
$$

where $Q$ is exactly $O$, Definition 28.1. Moreover
$\mathcal K$ is finite.

Proof. Fix a complex $v$ with $Q(p_J,v)\ne0$. We prove that
$u=v$ and a fixed value of $m$ determine at most one point of
$\mathcal X$. A point with $u=v$ lies in
$\mathcal Z(p_J,v)$, so the projection argument of Theorem 10.2
gives $R(r,p_J,v)=0$, including all fixed base projections.

Use the exact minors $\mathcal L_0,\mathcal L_1$ of $O$
(20.4)–(20.5). The evaluation-vector identity $O$ (20.10) is a
polynomial common-root identity, so it gives

$$
\mathcal L_1(r,p_J,v)b+\mathcal L_0(r,p_J,v)=0
\tag{11.4}
$$

also over $\mathbb C$: its only divisor is
$72900r^6(r-1)^4\ne0$ on $\mathcal X$.
Nonzero $Q$ makes its factor
$E_1=\operatorname{Res}^{18,26}_r(R,\mathcal L_1)$ nonzero.
The common-finite-root implication for the padded determinant
therefore makes $\mathcal L_1$ nonzero at every complex $R$ root.
Equation (11.4) fixes $b=-\mathcal L_0/\mathcal L_1$.
Consequently two distinct points in this fibre have distinct
$r$ coordinates.

Let $F_*,G_*$ denote exactly the polynomials called $F,G$ in
$O$ (27.2). Fixed-degree substitution gives, at any of these
complex source points,

$$
F_* =\mathcal L_1^7N_m(r,b),\qquad
G_* =\mathcal L_1^7D_m(r,b),\qquad m=F_*/G_*.
\tag{11.5}
$$

These are polynomial homogenization identities; their use does
not extend a positivity premise to complex sources.
Write $c_{18}=[r^{18}]R(r,p_J,v)$, which is $750a(p_J,v)$ in
the normalization of Section 3. Nonzero $Q$ makes $c_{18}\ne0$
and $E_3=\operatorname{Res}^{18,186}_r(R,G_*)\ne0$.
Thus $R$ has degree eighteen and $G_*$ is nonzero at all its
complex roots. The padded resultant product formula gives

$$
T_*(p_J,v,w)=c_{18}^{188}
 \prod_{R(\alpha,p_J,v)=0}
 \{F_*(\alpha,p_J,v)-wG_*(\alpha,p_J,v)\},
\tag{11.6}
$$

with the eighteen roots counted with multiplicity. In particular
$T_*$ has degree eighteen in $w$. If distinct source points had
one common $m$, their distinct $r$ roots would give two vanishing
factors at $w=m$ in (11.6). This would be a multiple root of
$T_*$, forcing

$$
E_4=\operatorname{Res}^{18,17}_w(T_*,\partial_wT_*)=0,
\tag{11.7}
$$

contrary to $Q\ne0$. This proves (11.3) for all complex points
of the stated open locus. The resultant and product identities
are those of $O$, Definitions 27.1 and 28.1 and (30.6); their
common-root implications hold under every coefficient
specialization. Denominator and full-degree conditions here
follow from the stated open locus or from nonzero factors of $Q$.

Finally $O$, Theorems 26.2 and 30.2, give $Q(p_J,0)\ne0$ for
this same exact $p_J$. Hence $Q(p_J,v)$ has finitely many
complex roots. For each root $v$, the whole complex fibre
$\mathcal X\cap\{u=v\}=\mathcal Z(p_J,v)$ has at most eighteen
points by Theorem 10.2. Thus $\mathcal K$ lies in a finite union
of finite Cartesian squares and is finite. This argument retains
all sources at roots of $Q$, including $\mathcal L_1=0$ cases,
multiple projections and degree drops. ∎

## 12. A global bound on actual terminal-M pairs

**Definition 12.1 (Pairs across all acquired responses).** Define

$$
\begin{aligned}
\mathcal T_M^{\rm ord}=\{(W,W')\in
 \mathcal F(H_4,M,p_J)^2:\;&W\ne W',\\
 &u_M(W)=u_M(W'),\quad f_{MM}(W)=f_{MM}(W')\}.
\end{aligned}
\tag{12.1}
$$

Let $\mathcal T_M^{\rm un}$ be the quotient by interchange of the
two worlds. Their common acquired response is determined by the
pair, so these sets count pairs across all real acquired responses.

**Theorem 12.2 (Global ordered and unordered pair bounds).** At the
original exact $p_J$,

$$
|\mathcal K|\le4802,\qquad
|\mathcal T_M^{\rm ord}|\le4802,\qquad
|\mathcal T_M^{\rm un}|\le2401.
\tag{12.2}
$$

Proof. In four complex affine coordinates $x=(r,b)$ and
$y=(r',b')$, consider the four polynomial equations

$$
\begin{gathered}
\mathsf A(x,p_J)=0,\qquad \mathsf A(y,p_J)=0,\\
N_u(x)D_m(y)-N_u(y)D_m(x)=0,\\
N_m(x)D_m(y)-N_m(y)D_m(x)=0.
\end{gathered}
\tag{12.3}
$$

Let $\mathcal V\subseteq\mathbb C^4$ be their full common zero
set. Inside it, $\mathcal K$ is precisely the open subset on which

$$
r(r-1)r'(r'-1)D_m(x)D_m(y)\ne0,\qquad x\ne y.
\tag{12.4}
$$

The diagonal complement is the union of the two opens
$r-r'\ne0$ and $b-b'\ne0$, so this description also retains
pairs with equal $r$ and different $b$. Theorem 11.2 proves
finiteness on this entire complex open subset. Every point of
$\mathcal K$ is therefore isolated in $\mathcal V$: a
positive-dimensional component through such a point would meet
(12.4) in a positive-dimensional open subset, contradicting that
finiteness. The full $\mathcal V$ can still contain the diagonal
curve and components on the deleted divisors.

For the two variable groups $(r,b)$ and $(r',b')$, the equations
(12.3) have the following upper bounds on their multidegrees:

$$
\begin{pmatrix}
7&0\\0&7\\7&7\\7&7
\end{pmatrix}.
\tag{12.5}
$$

The multihomogeneous Bézout inequality for isolated complex
solutions bounds their number by

$$
[s^2t^2]\,(7s)(7t)(7s+7t)^2=2\cdot7^4=4802.
\tag{12.6}
$$

Here the exponents $2,2$ are the sizes of the two variable groups,
or the dimensions of the two projective-plane factors. The
isolated-solution form is Jan Verschelde,
*[Multihomogeneous Homotopies](https://homepages.math.uic.edu/~jan/mcs563s14/lec07.pdf)*,
Lecture 7, Theorem 4.1 and Section 3: it applies to a square
polynomial system in $\mathbb C^n$ and bounds its isolated
solutions, without requiring its full zero set to be finite.
Using upper multidegrees is valid because the coefficient bound
is monotone in these nonnegative degrees. Thus the surviving
diagonal and base components do not enter a proper-intersection
assumption. Since every point of $\mathcal K$ is isolated in
(12.3), this proves its bound.

Now take any actual pair in $\mathcal T_M^{\rm ord}$, and write
$v$ for its common $u_M$. If either member were singular,
$O$, Theorem 29.2, would give
$v=s_-(p_J)$ or $v=s_+(p_J)$. But $S$, Theorem 8.1, proves
terminal-M injectivity on each of those entire actual children,
including all regular companions. This contradicts the distinct
pair. Thus both members are regular.

Their strict sources belong to $\mathcal X$, and the actual
response identities in Definition 11.1 put their source pair in
$\mathcal K$. Fixed-source uniqueness of the entire gain and
drift, $O$, Theorem 12.3, makes this map injective and preserves
distinctness of the two complete worlds. Hence
$|\mathcal T_M^{\rm ord}|\le|\mathcal K|\le4802$.
Interchange has no fixed point on distinct ordered pairs, and
preserves all equalities in (12.1). Each unordered pair therefore
has exactly two ordered representatives, proving the final bound.
All actual singular cases have been excluded by their complete
response children, while every regular actual pair is retained in
the complex open subset (12.4). ∎

## 13. The remaining same-child existence question

**Definition 13.1 (Original simultaneous-pair obligation).** Set
$\mathcal C_v=\mathcal F(H_4,M,p_J,M,v)$, with the complete-world
domain of Section 1 and the unchanged exact $p_J$ of Definition
11.1. The remaining question is whether there exist a real $v$ and
four labels $W_{J0},W_{J1},W_{M0},W_{M1}\in\mathcal C_v$ with

$$
\begin{gathered}
W_{J0}\ne W_{J1},\qquad W_{M0}\ne W_{M1},\\
f_{MJ}(W_{J0})=f_{MJ}(W_{J1}),\qquad
f_{MM}(W_{M0})=f_{MM}(W_{M1}).
\end{gathered}
\tag{13.1}
$$

Labels can coincide across the two pairs. The original terminal
functions are $O$ (1.7), after the acquired sixth action M.
By $S$, Corollary 9.1, every hypothetical witness child in (13.1)
is wholly regular and has $Q(p_J,v)=0$; $E$, Theorem 1.3,
excludes the strip $[142,150]$. Theorem 10.2 bounds each such
entire child by eighteen worlds, and Theorem 12.2 bounds actual
terminal-M pairs across all acquired responses at $p_J$ by 2401
unordered pairs in total. These cardinality statements supply
neither a pair enumeration nor an existence or exclusion result
for (13.1). The same-child joint question remains unresolved,
with all strict sources, one entire nonzero gain of degree at most
three and one fixed drift per world retained, and with no common
gain or drift condition between different worlds.

## 追加锚（本行以下为增补区）

## 14. Rational tubes for the positive roots on an equal-source-coordinate chart

**Definition 14.1 (The parameter and the source polynomials).** Retain
exactly the complete-world domain, original $H_4$, clocks and actual
responses of Section 1 and $O$, Definitions 1.1–1.3. Put

$$
\begin{gathered}
p_c=\frac{2744214237392974691433531179656369993836520133001835}{10^{50}},
\qquad h=10^{-40},\qquad K=[p_c-h,p_c+h],\\
a=\frac{6618}{10000},\qquad w=\frac1{10000},\qquad
R_{\rm loc}=[a,a+w].
\end{gathered}
\tag{14.1}
$$

Here $R_{\rm loc}$ is an interval, distinct from the resultant
$R_{18}$. The parameter $p_J$ is still the value at the unique zero
of the original $F_J$ in its original box $\mathcal B_J$, supplied
by $O$, Theorem 8.1 and (8.4). For that same zero, $O$,
Theorem 26.2, gives $p_J\in K$.

Use exactly $D=D_\Lambda,H,X,N,T,U,K_\Lambda,N_u$ from Section 2,
with $N_u=\mathsf N_u$, and $D_m=5bD$. In particular

$$
\mathsf A(r,b,p)=5b(p-24)D+3(8b-1)H
                 =\mathsf S_p(r,b)/2.
\tag{14.2}
$$

The terminal numerator is exactly $O$ (27.1):

$$
\begin{gathered}
Z_7=2N+3bU,\qquad
G_7=(20T+84)XN-bT(70N+35X),\\
N_m=\frac{120bTD+12Z_7D(200b+11)
 -3K_\Lambda(bTXN+Z_7G_7)}{T}.
\end{gathered}
\tag{14.3}
$$

The divisions by $T=1+b$ defining $N_u,N_m$ are exact polynomial
divisions before any coefficient operation. Thus all the polynomials
used below are specified by Section 2 and (14.2)–(14.3), without
using a projected root chart or an eliminant root as a source.

**Definition 14.2 (Finite rational coefficient operation).** For
$F\in\mathbb Q[x_1,\ldots,x_d]$ of coordinate degrees at most
$n=(n_1,\ldots,n_d)$, write $F=\sum_\alpha f_\alpha x^\alpha$
and define, for $0\le j_k\le n_k$,

$$
\beta_j^n(F)=\sum_{\alpha\le j} f_\alpha
 \prod_{k=1}^d\frac{\binom{j_k}{\alpha_k}}{\binom{n_k}{\alpha_k}},
\qquad
\mathcal I_n(F)=
 [\min_j\beta_j^n(F),\max_j\beta_j^n(F)].
\tag{14.4}
$$

Missing coefficients are zero. The degrees $n$ in each use below
are fixed, including zero padding. All sums in (14.4) are finite
rational sums. On $[0,1]^d$, $F$ lies in $\mathcal I_n(F)$:
the identity

$$
x^\alpha=\sum_{j\ge\alpha}
 \left(\prod_k\frac{\binom{j_k}{\alpha_k}}{\binom{n_k}{\alpha_k}}\right)
 \prod_k\binom{n_k}{j_k}x_k^{j_k}(1-x_k)^{n_k-j_k}
\tag{14.5}
$$

expresses $F$ in a nonnegative basis whose sum is one. This is the
usual Bernstein convex-hull argument; (14.4) fixes its exact rational
form here.

Set $r(x)=a+wx$ and $p(z)=p_c+h(2z-1)$. Write
$\mathsf A=\sum_{k=0}^7 a_k(r,p)b^k$. Define two affine tubes by

$$
\begin{gathered}
L_i(r)=q_i+\ell_i(r-a),\qquad
\mathcal U_i=\{(r,b):r\in R_{\rm loc},\ |b-L_i(r)|\le e_i\},\\
F_{i,\sigma}(x,z)=
 \mathsf A(r(x),L_i(r(x))+\sigma e_i,p(z)),\quad \sigma\in\{-1,1\},\\
\widehat C_i(x,y)=C(r(x),L_i(r(x))+e_i(2y-1))
\end{gathered}
\tag{14.6}
$$

for each $C\in\mathbb Q[r,b]$. The tube constants are

| $i$ | $q_i$ | $\ell_i$ | $e_i$ |
| --- | --- | --- | --- |
| $0$ | $1550663131844/10^{13}$ | $-561077/10^8$ | $10^{-9}$ |
| $1$ | $3795203448211/10^{13}$ | $-1714782/10^7$ | $10^{-8}$ |

**Proposition 14.3 (Source-specific rational certificate).** Every
Bernstein coefficient of the indicated polynomial satisfies the
following strict bounds. For $a_k(r(x),p(z))$, use degree $(6,1)$:

| $k$ | Lower bound | Upper bound |
| --- | --- | --- |
| $0$ | $1$ | $2$ |
| $1$ | $1$ | $2$ |
| $2$ | $-47$ | $-46$ |
| $3$ | $-72$ | $-71$ |
| $4$ | $119$ | $120$ |
| $5$ | $370$ | $371$ |
| $6$ | $1089$ | $1090$ |
| $7$ | $353$ | $354$ |

For $F_{i,\sigma}$ use degree $(7,1)$. The next bounds are for
$10^{10}\beta_j^{(7,1)}(F_{i,\sigma})$:

| $i$ | $\sigma$ | Lower bound | Upper bound |
| --- | --- | --- | --- |
| $0$ | $-1$ | $148$ | $158$ |
| $0$ | $1$ | $-149$ | $-140$ |
| $1$ | $-1$ | $-8851$ | $-5851$ |
| $1$ | $1$ | $2851$ | $5853$ |

Put $s_0=1$, $s_1=-1$ and

$$
(m_0^-,m_0^+)=(7058/10,7059/10),\qquad
(m_1^-,m_1^+)=(673,6731/10),\qquad
(v^-,v^+)=(15145/100,15147/100).
\tag{14.7}
$$

For the following rows use degree $(7,7)$ and the transform
$\widehat C_i$ of (14.6). Each row means
$L<10^d\beta_j^{(7,7)}(\widehat C_i)<U$ for every $j$:

| $i$ | $C$ | $d$ | $L$ | $U$ |
| --- | --- | --- | --- | --- |
| $0$ | $D_m$ | $4$ | $1368$ | $1369$ |
| $1$ | $D_m$ | $4$ | $-3468$ | $-3467$ |
| $0$ | $s_0(N_m-m_0^-D_m)$ | $6$ | $115$ | $2237$ |
| $0$ | $s_0(m_0^+D_m-N_m)$ | $6$ | $11450$ | $13568$ |
| $1$ | $s_1(N_m-m_1^-D_m)$ | $6$ | $12515$ | $19154$ |
| $1$ | $s_1(m_1^+D_m-N_m)$ | $6$ | $15521$ | $22164$ |
| $0$ | $s_0(N_u-v^-D_m)$ | $6$ | $553$ | $878$ |
| $0$ | $s_0(v^+D_m-N_u)$ | $6$ | $1860$ | $2183$ |
| $1$ | $s_1(N_u-v^-D_m)$ | $6$ | $1033$ | $2503$ |
| $1$ | $s_1(v^+D_m-N_u)$ | $6$ | $4432$ | $5903$ |

Proof. Expand the exact polynomials (14.2)–(14.3) and $N_u,D_m$
from Section 2, performing the two exact divisions by $1+b$ first.
Their total source degrees are at most seven, and
$[b^7]\mathsf A=5p+216$. Substitution in the coefficient rows gives
degrees at most $(6,1)$; substitution in the faces gives degrees at
most $(7,1)$; the tube transforms have degrees at most $(7,7)$.
Apply (14.4) with precisely these padded degrees.

More explicitly, each table row with scale $10^d$ is the finite
set of rational inequalities

$$
L<10^d\sum_{\alpha\le j}
 [x^\alpha]F\prod_k
 \frac{\binom{j_k}{\alpha_k}}{\binom{n_k}{\alpha_k}}<U,
\qquad 0\le j_k\le n_k,
\tag{14.8}
$$

where $F,n,L,U,d$ are fixed by that row and (14.1)–(14.7), and
$d=0$ for the first table. Substitution of the displayed rational
constants gives the listed bounds by integer cross multiplication.
Thus the first table consists of $8\cdot14$ coefficient bounds,
the face table of $4\cdot16$, and the tube table of $10\cdot64$.
Equation (14.8), the fixed degree bounds and the rational affine
substitutions specify every coefficient and comparison; no numerical
root locations or unlisted cell choices enter the certificate. ∎

## 15. Exhaustion, continuity and complete original-world lifts

**Theorem 15.1 (Exactly two positive simple roots).** For every real
$p\in K$ and $r\in R_{\rm loc}$, $\mathsf A(r,b,p)$ has exactly
two positive real roots, counted with multiplicity. They are simple
and can be labelled

$$
b_0(r,p)<b_1(r,p),\qquad
|b_i(r,p)-L_i(r)|<e_i.
\tag{15.1}
$$

Both functions are continuous on $R_{\rm loc}\times K$ and locally
are restrictions of continuously differentiable functions on open
neighbourhoods in $(r,p)$.

Proof. The first table of Proposition 14.3 and (14.5) give the
ascending coefficient sign word $(+,+,-,-,+,+,+,+)$ for every
$(r,p)$ in the stated rectangle. Its descending word has exactly
two variations. Descartes' rule of signs therefore gives at most
two positive roots, counting multiplicity. In particular the
leading coefficient never vanishes.

The tube sections are disjoint and positive: the first lies in
$(15/100,16/100)$ and the second in $(37/100,39/100)$, directly
from (14.6). The face table gives signs $(+,-)$ on the first
section and $(-,+)$ on the second, uniformly in $r,p$.
The intermediate value theorem supplies a root in the interior of
each section. These two roots use the entire Descartes multiplicity
budget. Hence they are all positive roots, each simple; this also
excludes any positive root outside the two sections.

At either root $\partial_b\mathsf A\ne0$. The ordinary implicit
function theorem gives a local continuously differentiable root
function. Its positive lower or upper label is unique by the root
count, so these local functions agree wherever their domains meet
the rectangle. They give the functions (15.1), including continuity
at its boundary. ∎

**Theorem 15.2 (Whole-world lift and separated actual images).**
For each $(r,p)\in R_{\rm loc}\times K$, the complete worlds in
$\mathcal F(H_4,M,p)$ with source coordinate $r$ are exactly two
worlds $W_i(r,p)$, with sources $(r,b_i(r,p))$. Both are regular,
and their actual responses satisfy

$$
\begin{gathered}
7058/10<f_{MM}(W_0(r,p))<7059/10,\\
673<f_{MM}(W_1(r,p))<6731/10,\\
15145/100<u_M(W_i(r,p))<15147/100\qquad(i=0,1).
\end{gathered}
\tag{15.2}
$$

Proof. On the two full tubes the denominator rows of Proposition
14.3 and (14.5) give, respectively,

$$
\frac{1368}{10000}<D_m<\frac{1369}{10000},\qquad
-\frac{3468}{10000}<D_m<-\frac{3467}{10000}.
\tag{15.3}
$$

At a strict source $j=X/b$, $n=N/b$, and $b,T,U,X,N$ are
positive. The actual identity from $O$ (20.8) is

$$
\Lambda=\frac{2D}{TUXN}.
\tag{15.4}
$$

Thus $D_m=5bD\ne0$ implies regularity. Since
$\mathsf S_p=2\mathsf A=0$, the hypotheses of $O$, Theorem 12.3,
hold: the source is strict and satisfies its zero-safe scalar
criterion. That theorem supplies a unique complete world at each
source. Explicitly the regular version of its lift is

$$
\begin{gathered}
\epsilon=-\frac{3K_\Lambda XN}{5D},\qquad d=24+\epsilon,\\
(q_0,q_1,q_2,q_3)=
 \left(-24-\epsilon,-\epsilon/j,(27/5-\epsilon)/T,-\epsilon/n\right),\\
g(s)=\sum_{k=0}^3q_k
 \prod_{\substack{0\le j\le3\\j\ne k}}\frac{s-j}{k-j},\qquad
P=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix}.
\end{gathered}
\tag{15.5}
$$

This is one entire polynomial and one fixed drift in each world.
The polynomial is nonzero because the original responses at clocks
zero and one are $0$ and $24$. The converse in $O$, Theorem 12.3,
puts every complete world at this $r,p$ among the positive roots of
$\mathsf A$; Theorem 15.1 exhausts those roots. Fixed-source
uniqueness then gives exactly the two worlds claimed.

For these regular strict lifts, $O$ (20.9), $O$, Theorem 27.2,
and equivalently $E$, Lemma 3.3, give the actual identities
$u_M=N_u/D_m$ and $f_{MM}=N_m/D_m$. The positive rows of the
tube table have the form

$$
s_i(N_m-m_i^-D_m)>0,\quad s_i(m_i^+D_m-N_m)>0,
\quad s_i(N_u-v^-D_m)>0,\quad s_i(v^+D_m-N_u)>0.
\tag{15.6}
$$

Since $s_iD_m>0$, division gives (15.2). These divisions use no
gain sample, gain leading coefficient, gain-root difference or
drift. Lower degrees, sampled zeros, repeated gain roots and zero
drift retain their original admissibility. The two worlds need not
have the same gains or drifts. The bounds on the tubes locate the
roots of the unchanged unbounded source domain; no upper source
bound is imposed on that domain. ∎

## 16. An actual acquired-response crossing at the original parameter

**Definition 16.1 (Endpoint source brackets).** Put

$$
r_0=\frac{8273}{12500},\qquad r_1=\frac{13237}{20000},
\qquad a<r_0<r_1<a+w.
\tag{16.1}
$$

For $t,i\in\{0,1\}$ let $J_{ti}=[B^-_{ti}/d_{ti},B^+_{ti}/d_{ti}]$
with the following integer data:

| $t$ | $i$ | $B^-_{ti}$ | $B^+_{ti}$ | $d_{ti}$ |
| --- | --- | --- | --- | --- |
| $0$ | $0$ | $15506608880$ | $15506608882$ | $10^{11}$ |
| $0$ | $1$ | $37951348998$ | $37951349001$ | $10^{11}$ |
| $1$ | $0$ | $15506603269$ | $15506603271$ | $10^{11}$ |
| $1$ | $1$ | $3795117753$ | $3795117755$ | $10^{10}$ |

**Lemma 16.2 (Uniform endpoint signs and acquired-response differences).**
For every $p\in K$, $b_i(r_t,p)$ lies in the interior of
$J_{ti}$. Define

$$
\delta(r,p)=u_M(W_0(r,p))-u_M(W_1(r,p)).
\tag{16.2}
$$

Then, uniformly for $p\in K$,

$$
-\frac{5454}{10^8}<\delta(r_0,p)<-\frac{5430}{10^8}<0,
\qquad
0<\frac{13103}{10^8}<\delta(r_1,p)<\frac{13238}{10^8}.
\tag{16.3}
$$

Proof. Each $J_{ti}$ lies strictly inside the section of
$\mathcal U_i$ at $r_t$, by its rational endpoints. For
$e\in\{-,+\}$ form

$$
H_{ti}^e(z)=\mathsf A(r_t,B^e_{ti}/d_{ti},p(z)).
\tag{16.4}
$$

Every degree-one Bernstein coefficient of $10^{12}H_{ti}^e$ lies
strictly within the indicated interval:

| $t$ | $i$ | For $e=-$ | For $e=+$ |
| --- | --- | --- | --- |
| $0$ | $0$ | $(24,25)$ | $(-273,-272)$ |
| $0$ | $1$ | $(-1100,-1099)$ | $(656,657)$ |
| $1$ | $0$ | $(88,89)$ | $(-209,-208)$ |
| $1$ | $1$ | $(-5641,-5640)$ | $(6062,6063)$ |

These are rational evaluations of (14.2), using $n=1$ in
(14.4); the two coefficients are exactly the evaluations at
$p_c-h$ and $p_c+h$. Opposite signs and Theorem 15.1 identify
the unique root inside each bracket.

For $C=N_u,D_m$ form the one-variable polynomial

$$
C_{ti}(y)=C\left(r_t,
 \frac{B^-_{ti}+(B^+_{ti}-B^-_{ti})y}{d_{ti}}\right),
\qquad I^C_{ti}=\mathcal I_7(C_{ti}).
\tag{16.5}
$$

All endpoints of $I^{D_m}_{t0}$ lie strictly between
$1368/10000$ and $1369/10000$, and those of $I^{D_m}_{t1}$
lie strictly between $-3468/10000$ and $-3467/10000$.
The exact interval quotient is the interval whose endpoints are
the minimum and maximum of the four endpoint ratios of
$I^{N_u}_{ti}$ and $I^{D_m}_{ti}$. Formula (14.4), with
$n=7$, gives the following strict enclosing intervals for that
quotient; all numerators in the last two columns have denominator
$10^{11}$:

| $t$ | $i$ | Lower numerator | Upper numerator |
| --- | --- | --- | --- |
| $0$ | $0$ | $15145546534847$ | $15145546537429$ |
| $0$ | $1$ | $15145551968255$ | $15145551987988$ |
| $1$ | $0$ | $15145522920408$ | $15145522922990$ |
| $1$ | $1$ | $15145509685267$ | $15145509816817$ |

For reproducibility, (16.5) requires eight Bernstein coefficients
per polynomial, with the explicit sum
$\beta_j^7(C_{ti})=\sum_{k=0}^j[y^k]C_{ti}\binom jk/\binom7k$.
All denominator guards and quotient comparisons above are strict
rational comparisons of these sums and their four endpoint ratios.
Thus (16.4)–(16.5), the displayed integer brackets and (14.4)
specify every finite arithmetic assertion in these tables.

The root in $J_{ti}$ has its actual $u_M$ in this quotient by
Theorem 15.2. Subtract the upper-branch interval from the
lower-branch interval, using lower minus upper for the lower
endpoint and upper minus lower for the upper endpoint. The first
pair of rows lies strictly between $-5454/10^8$ and
$-5430/10^8$; the second lies strictly between $13103/10^8$ and
$13238/10^8$. This proves (16.3) over the full $K$, rather than
only at its rational centre. ∎

**Theorem 16.3 (Same acquired child, different terminal-M values).**
At the original exact algebraic $p_J$ there exist
$r_*\in(r_0,r_1)$, a real $v_{\rm loc}$ and distinct complete
regular original worlds $W_0,W_1$ such that

$$
\begin{gathered}
W_i=W_i(r_*,p_J)\in\mathcal F(H_4,M,p_J,M,v_{\rm loc}),\\
r(W_0)=r(W_1)=r_*,\qquad b(W_0)\ne b(W_1),\\
\frac{15145}{100}<v_{\rm loc}<\frac{15147}{100},\qquad
f_{MM}(W_0)\ne f_{MM}(W_1).
\end{gathered}
\tag{16.6}
$$

The response $v_{\rm loc}$ lies outside $[125,126]$, $[142,150]$
and both singular responses $s_-(p_J),s_+(p_J)$.

Proof. Keep $p=p_J$ fixed, using $p_J\in K$ from Definition
14.1. Theorem 15.1 and (15.3) make both rational acquired-response
functions continuous on $R_{\rm loc}$. Thus $\delta(r,p_J)$ is
continuous. Lemma 16.2 gives its opposite signs at $r_0,r_1$.
The intermediate value theorem gives an $r_*$ in their open
interval with $\delta(r_*,p_J)=0$. Its common actual value is
$v_{\rm loc}$. Theorem 15.2 gives both complete legal lifts and
the bound on this response. Their disjoint positive source tubes
make the worlds distinct, while their disjoint terminal-M ranges
in (15.2) give the last inequality in (16.6).

The response interval in (16.6) is disjoint from both displayed
strips. For the singular responses use $O$, Theorem 29.2, and
$S$, Lemma 2.4: at this same $p_J\in K$, the exhaustive singular
responses lie in the rational boxes $V_-,V_+$ of $S$ (2.1),
respectively contained in $(119,120)$ and $(138,139)$. These
are also disjoint from (16.6). The argument varies only $r$;
it never replaces $p_J$ by $p_c$. ∎

## 17. The local reduction of the original distinct-pair locus

**Corollary 17.1 (Exclusion of the equal-$r$ chart).** At the original
$p_J$, no pair in $\mathcal T_M^{\rm ord}$ of (12.1) has
$r(W)=r(W')\in R_{\rm loc}$. Equivalently, the strict real part
of the distinct-pair locus (11.2) has no point with
$r=r'\in R_{\rm loc}$ and $b,b'>0$.

Proof. Fixed-source uniqueness in Theorem 15.2 means that distinct
worlds at one such $r$ must be its lower and upper positive-root
lifts. Their actual terminal-M images lie in the disjoint
intervals (15.2), so equality is impossible, irrespective of
whether their acquired responses agree. This applies in particular
to every pair in (12.1). The actual response correspondence in
Definition 11.1 proves the equivalent source-locus formulation. ∎

**Definition 17.2 (The residual simultaneous-pair obligation).** The
predicate remains exactly (13.1), on the entire actual child
$\mathcal C_v=\mathcal F(H_4,M,p_J,M,v)$. Its terminal-M pair
may be restricted, by Corollary 17.1, to

$$
r(W_{M0})\ne r(W_{M1})
\quad\text{or}\quad
r(W_{M0})=r(W_{M1})\in(0,1)\setminus R_{\rm loc}.
\tag{17.1}
$$

This leaves all unequal-$r$ charts and all equal-$r$ charts outside
$R_{\rm loc}$. In particular (16.6) identifies two members of an
actual child, not that entire child: other-$r$ pairs at
$v_{\rm loc}$ remain subject to the original terminal-M test,
and the terminal-J pair required by (13.1) is still required in
that same entire child. No terminal-J equality is supplied by
(16.6), and its displayed pair has unequal terminal-M values.

The full-strip exclusions are those already supplied by $E$,
Theorems 1.3 and 12.1, and the two entire singular-child exclusions
are supplied by $S$, Theorem 8.1 and Corollary 9.1. The designated
roots of $Q$ in $E$, Theorem 8.2 and Section 13, are projection
artifacts for the joint test, as their entire children are excluded
there. The condition $Q(p_J,v)=0$ from Theorem 11.2 remains only
necessary for a regular terminal-M pair. Corollary 17.1 removes a
source-pair chart, not a response candidate; it excludes no further
root of $Q$. At every remaining candidate response, both distinct
pairs of (13.1), with overlap between the pairs permitted, retain
their full original obligations.

## 追加锚（本行以下为增补区）

## 18. Two positive source branches on the full strict domain

**Definition 18.1 (Uniform parameter interval and separator).** Retain
exactly $\mathsf A=\mathsf S_p/2$ of (14.2), with
$D_\Lambda,X,N,H,T,U$ as in Section 2. Set

$$
L=\frac{686}{25},\qquad H_I=\frac{549}{20},\qquad
I=[L,H_I],\qquad \sigma(r)=\frac{\sqrt{r(1-r)}}2.
\tag{18.1}
$$

The interval $K$ of (14.1) is contained in the interior of $I$,
by comparison of its rational endpoints. Thus the original
algebraic $p_J\in K$, supplied in Definition 14.1, belongs to $I$.
Neither interval changes the definition of $p_J$.

**Lemma 18.2 (Full-domain coefficient certificate).** Define
$q_k(r,p)$ by

$$
(1+b)^2\mathsf A(r,b,p)=\sum_{k=0}^9q_k(r,p)b^k.
\tag{18.2}
$$

Their exact expressions are

$$
\begin{aligned}
q_0={}&96r^3(1-r)^3,\\
q_1={}&4r^2(1-r)^2\{144(r-1/3)^2+5p-136\},\\
q_2={}&r(1-r)R_2,\qquad q_3=rR_3,\\
R_2={}&-2\{p(40r^2-50r+10)
 +720r^4-2016r^3+468r^2+1035r-195\},\\
R_3={}&p(105r^3-290r^2+245r-70)
 +768r^5-5184r^4+3960r^3\\
 &\quad+6435r^2-7704r+1905,\\
q_4={}&p(50r^4-205r^3+175r^2-50r-20)
 -1536r^5-2088r^4\\
 &\quad+14940r^3-14817r^2+4557r+390,\\
q_5={}&p(5r^4-60r^3-15r^2+60r-80)
 -2232r^4+12807r^3\\
 &\quad-12594r^2+3522r+2175,\\
q_6={}&p(-5r^3-55r^2+95r-100)
 +3648r^3-2133r^2-2829r+5418,\\
q_7={}&p(-10r^2+40r-35)+1368r^2-5181r+6087,\\
q_8={}&p(5r+10)-1872r+2670,\qquad q_9=5p+216.
\end{aligned}
\tag{18.3}
$$

For each row $(F,\alpha,\beta,n)$ below, take the degree-$n$
Bernstein coefficients in $x$ of $F(\alpha+(\beta-\alpha)x,e)$
for both $e=L,H_I$. The last columns are the minimum and maximum
of all those coefficients, including both parameter endpoints.

| $F$ | $[\alpha,\beta]$ | $n$ | Minimum | Maximum |
| --- | --- | --- | --- | --- |
| $R_2$ | $[0,1/2]$ | $4$ | $-953/5$ | $-1491/20$ |
| $R_2$ | $[1/2,1]$ | $4$ | $-839/4$ | $-24$ |
| $R_3$ | $[0,1]$ | $5$ | $-11211/20$ | $-366/25$ |
| $q_4$ | $[0,1/100]$ | $5$ | $-159$ | $-79963870321/625000000$ |
| $q_5$ | $[1/100,1]$ | $4$ | $11760225621/400000000$ | $24916449207/20000000$ |
| $q_6$ | $[0,1]$ | $3$ | $5245/4$ | $2674$ |
| $q_7$ | $[0,1]$ | $2$ | $8547/4$ | $25633/5$ |
| $q_8$ | $[0,1]$ | $1$ | $6048/5$ | $5889/2$ |
| $q_9$ | $[0,1]$ | $0$ | $1766/5$ | $1413/4$ |

Consequently, for every $p\in I$ and $0<r<1$,

$$
q_0,q_1>0,\qquad q_2,q_3<0,\qquad q_6,q_7,q_8,q_9>0,
\tag{18.4}
$$

and $q_4<0$ when $r\le1/100$, while $q_5>0$ when $r\ge1/100$.

**Proof.** Multiplying the literal expression
$5b(p-24)D_\Lambda+3(8b-1)H$ by $(1+b)^2$ and collecting
powers of $b$ gives (18.3). Here is the finite rational form of
every comparison in the table. For each row and $e\in\{L,H_I\}$,
put

$$
f_{k,e}=[x^k]F(\alpha+(\beta-\alpha)x,e),\qquad
\gamma_{j,e}=\sum_{k=0}^j f_{k,e}
 \frac{\binom jk}{\binom nk}\quad(0\le j\le n).
\tag{18.5}
$$

The extrema in the table are exactly
$\min_{j,e}\gamma_{j,e}$ and $\max_{j,e}\gamma_{j,e}$.
Equations (18.3) and (18.5) specify all 74 rational numbers;
expansion and integer cross multiplication give the displayed
extrema. For example the two $n=0$ values are $1766/5$ and
$1413/4$. No other subdivision or unspecified parameter is used.
The Bernstein identity (14.5) puts each polynomial between its
coefficient extrema. All expressions are affine in $p$, so
interpolation between $L$ and $H_I$ gives the same bounds on the
entire closed $I$. This proves the asserted signs except those
of $q_0,q_1$, which follow from (18.3), $0<r<1$ and
$5p-136\ge6/5>0$.

The Bernstein method is the standard one of (14.4)–(14.5);
see Mourrain–Rouillier–Roy,
[*Bernstein's basis and real root isolation*](https://inria.hal.science/inria-00071434/document),
Section 2, Proposition 2.8. The particular polynomials and
coefficient bounds here are repo-derived. ∎

**Lemma 18.3 (Negativity on the separating curve).** For every
$p\in I$ and $0<r<1$,

$$
\mathsf A(r,\sigma(r),p)<0.
\tag{18.6}
$$

**Proof.** Set $r=t^2/(1+t^2)$ and $b=t/(2(1+t^2))$, where
$t>0$. This parametrizes the entire separating curve, with
$0<r<1$. Substitution into the original $\mathsf A$ gives

$$
128d_e(1+t^2)^7\mathsf A
 \left(\frac{t^2}{1+t^2},\frac{t}{2(1+t^2)},e\right)
 =t^4P_e(t),\qquad d_L=5,\quad d_{H_I}=4,
\tag{18.7}
$$

where the coefficient vectors in increasing powers of $t$ are

$$
\begin{aligned}
P_L:\;&(-31760,52108,183972,-261702,-181136,112088,6672,-7552),\\
P_{H_I}:\;&(-25440,41712,147168,-209283,-144894,89712,5328,-6048).
\end{aligned}
\tag{18.8}
$$

For signs on the entire positive half-line put

$$
G_e(x)=(1-x)^7P_e\left(\frac{x}{1-x}\right).
\tag{18.9}
$$

These are polynomials, with increasing coefficient vectors

$$
\begin{aligned}
G_L:\;&(-31760,274428,-795636,711658,551632,-1305856,670788,-82806),\\
G_{H_I}:\;&(-25440,219792,-637344,570957,439278,-1043064,535842,-66069).
\end{aligned}
\tag{18.10}
$$

For each closed cell $[\alpha,\beta]$ below, the entries are the
exact maximum of the eight degree-seven Bernstein coefficients
of $G_e(\alpha+(\beta-\alpha)y)$.

| $[\alpha,\beta]$ | Maximum for $G_L$ | Maximum for $G_{H_I}$ |
| --- | --- | --- |
| $[0,1/4]$ | $-5917235/8192$ | $-9514125/16384$ |
| $[1/4,5/16]$ | $-1659020735/134217728$ | $-2920175505/268435456$ |
| $[5/16,21/64]$ | $-147469619705/240518168576$ | $-620433751095/481036337152$ |
| $[21/64,11/32]$ | $-8967359819695/2199023255552$ | $-17285328487905/4398046511104$ |
| $[11/32,3/8]$ | $-684445779505/17179869184$ | $-1108515042495/34359738368$ |
| $[3/8,1/2]$ | $-212980217/1048576$ | $-340658391/2097152$ |
| $[1/2,3/4]$ | $-6416993/28672$ | $-10268199/57344$ |
| $[3/4,1]$ | $-2186305/8192$ | $-3505695/16384$ |

The coefficient whose maximum is taken is explicitly

$$
\sum_{k=0}^j[y^k]G_e(\alpha+(\beta-\alpha)y)
 \frac{\binom jk}{\binom7k},\qquad j=0,\ldots,7.
\tag{18.11}
$$

Substitution of (18.10) gives the listed maxima by rational
arithmetic. Thus (18.10)–(18.11) specify all 128 coefficients.
The cells cover the whole closed $[0,1]$, and all maxima are
strictly negative. The convex-hull identity (14.5) gives
$G_e(x)<0$ throughout $[0,1]$. For $t>0$ use $x=t/(1+t)$:
then $x\in(0,1)$ and $(1-x)^7>0$, so $P_e(t)<0$.
Equation (18.7) proves (18.6) at both parameter endpoints.
Since $\mathsf A$ is affine in $p$, it proves the strict
inequality on the whole $I$. This source-specific certificate
uses the Bernstein identity cited in Lemma 18.2. ∎

**Theorem 18.4 (Global root count, separation and labelling).**
For every real $p\in I$ and every $0<r<1$, the original
$\mathsf A(r,b,p)$ has exactly two positive real roots, both simple.
There are unique global labels satisfying

$$
0<b_-(r,p)<\sigma(r)<b_+(r,p).
\tag{18.12}
$$

They are smooth on $(0,1)\times\operatorname{int}I$ and continuous
on $(0,1)\times I$. At each point with $p$ an endpoint of $I$,
each is locally the restriction of a smooth root function on an
open neighbourhood in $(r,p)$. In the original coordinate
$c=r(1-r)/b$, the lower branch has $c>4b$ and the upper branch
has $c<4b$.

**Proof.** Lemma 18.2 gives exactly two variations in the nonzero
coefficient word of $(1+b)^2\mathsf A$. If $r\le1/100$ the
ascending word is $(+,+,-,-,-,q_5,+,+,+,+)$, with $q_5$ arbitrary;
if $r\ge1/100$ it is $(+,+,-,-,q_4,+,+,+,+,+)$, with $q_4$
arbitrary. Deleting a zero coefficient leaves two variations
in either case. Descartes' rule of signs, counting multiplicity,
therefore bounds the number of positive roots by two; see
Mourrain–Rouillier–Roy, cited in Lemma 18.2, Theorem 1.1.
The factor $(1+b)^2$ introduces no positive root.

On the other hand $\mathsf A(r,0,p)=96r^3(1-r)^3>0$,
and its leading coefficient in $b$ is $5p+216>0$.
Together with Lemma 18.3, the intermediate value theorem gives
one root between zero and $\sigma(r)$ and one root larger than
$\sigma(r)$. They exhaust the multiplicity bound, so each is
simple and no other positive root exists.

At either root $\partial_b\mathsf A\ne0$. The smooth implicit
function theorem supplies a root function near that $(r,p)$.
After shrinking its neighbourhood it stays positive and on the
same side of the continuous separator. Uniqueness on that side
makes it equal to its global label where $p\in I$. These local
functions agree on overlaps, proving continuity and smoothness,
including the endpoint restriction statement. The smooth implicit
function theorem is used in its usual local form; see Krantz–Parks,
[*The Implicit Function Theorem*](https://doi.org/10.1007/978-1-4612-0059-8),
Chapter 1. Finally, for $b>0$,
$b<\sigma(r)$ is equivalent to $4b^2<r(1-r)$ and hence to
$c>4b$; the upper inequality is handled in the same way. ∎

## 19. Zero-safe whole-world branches and the unchanged acquired child

**Definition 19.1 (Whole-world lift along the global branches).**
For $i\in\{-,+\}$, $0<r<1$ and $p\in I$, put $b=b_i(r,p)$,
$c=r(1-r)/b$, $j=b+c$, $n=j+r$, $T=1+b$, $U=1+2b$ and $V=U+n$.
Use the zero-safe expressions of $O$, (12.1), (12.4)–(12.6):

$$
\begin{gathered}
a=24/5,\qquad \Delta=b-1/8,\qquad
B_{\rm coef}=6/T-2/U,\\
\Lambda=1+6/T+1/U-4/j-4/n,\\
A_5=1+V(4-15/j+20/T-10/n),\qquad K_5=20a\Delta V/T,\\
Z=\Lambda^2+A_5^2,\qquad
\epsilon=\frac{-a\Delta B_{\rm coef}\Lambda+A_5(p-24-K_5)}{Z},\\
(\eta_0,\eta_1,\eta_2,\eta_3)=
 \left(-24-\epsilon,-\epsilon/j,(27/5-\epsilon)/T,-\epsilon/n\right),\\
g_i(s;r,p)=\sum_{k=0}^3\eta_k
 \prod_{\substack{0\le \ell\le3\\\ell\ne k}}
 \frac{s-\ell}{k-\ell},\qquad
W_i(r,p)=\left(\begin{pmatrix}r&b\\c&1-r\end{pmatrix},
 g_i,24+\epsilon\right).
\end{gathered}
\tag{19.1}
$$

**Theorem 19.2 (Exhaustive smooth complete-world correspondence).**
Under the original complete-world definitions and zero-safe
equivalence of $O$, Theorem 12.3, for every $p\in I$ the map

$$
\{-,+\}\times(0,1)\longrightarrow\mathcal F(H_4,M,p),
\qquad (i,r)\longmapsto W_i(r,p)
\tag{19.2}
$$

is a bijection. Exactly two complete worlds lie over each $r$.
Their matrix entries, gain coefficients and drift depend smoothly
on $(r,p)$ in the interior, continuously on the full domain, with
local smooth extensions at the endpoints of $I$.
The correspondence includes $\Lambda=0$, lower gain degrees,
sampled zeros, repeated gain roots and zero drift, within the
original unbounded positive-source domain. It imposes no equality
of gains or drifts between different worlds.

**Proof.** Each source in (18.12) is strict and satisfies
$\mathsf S_p=2\mathsf A=0$. The stated supplier gives its unique
complete lift (19.1), with $Z>0$ by $O$, Lemma 12.2. Conversely,
every complete world in $\mathcal F(H_4,M,p)$ has a strict source
satisfying $\mathsf S_p=0$. Theorem 18.4 puts its positive $b$
at exactly one labelled root; fixed-source uniqueness identifies
the world with (19.1). Different $r$ give different matrix entries,
and the two labels at a common $r$ have different $b$. This proves
bijectivity.

All denominators $b,j,n,T,U$ are positive on the strict source
domain, and $Z>0$ there. Every expression in (19.1) is therefore
smooth in $(r,b,p)$ locally at every branch point, including
$\Lambda=0$. Composition with Theorem 18.4 gives the claimed
regularity in the finite coefficient coordinates of the entire
gain polynomial. At a parameter endpoint these denominators
remain positive in a sufficiently small open neighbourhood,
which also proves the local smooth extension assertion.

Explicitly, if $\Lambda=0$, the parent equation in $O$ (12.7)
gives $a\Delta B_{\rm coef}=0$. Since $a>0$ and
$B_{\rm coef}=2(2+5b)/(TU)>0$, it follows that $b=1/8$.
Then $K_5=0$, while $A_5\ne0$ by $Z>0$, and (19.1) becomes
$\epsilon=(p-24)/A_5$. No division by $\Lambda$ has been used.
Nor has there been division by a gain sample, gain leading
coefficient, difference of gain roots or drift. The interpolant
is one entire polynomial of degree at most three. It cannot
vanish identically: the clock-zero and clock-one responses would
then both equal the fixed drift, whereas the original $H_4$
requires $0$ and $24$. This retains the original complete gain
and drift convention. Exhaustion used every $b>0$, without an
imposed source box. ∎

**Definition 19.3 (Actual images at the original algebraic parameter).**
Fix exactly the original $p=p_J$ of Definition 14.1. Put
$\mathcal D=\{-,+\}\times(0,1)$ and $W(i,r)=W_i(r,p_J)$.
On each branch evaluate the actual responses of $O$ (1.7),
using the same gain and drift from (19.1):

$$
\begin{aligned}
\mathcal U(i,r)&=d+(2U+n)g_i(6;r,p_J),\\
\mathcal J(i,r)&=d+(T+2j+4r)g_i(7;r,p_J),\\
\mathcal M(i,r)&=d+(3U+2n)g_i(7;r,p_J).
\end{aligned}
\tag{19.3}
$$

These are respectively $u_M(W)$, $f_{MJ}(W)$ and $f_{MM}(W)$.
They are smooth on each full $r$ branch, including any
$\Lambda=0$ point, by Theorem 19.2. For every real acquired
response $v$, define the entire parameter fibre

$$
\mathcal D_v=\{x\in\mathcal D:\mathcal U(x)=v\}.
\tag{19.4}
$$

**Theorem 19.4 (Entire-child transport of the original joint predicate).**
For every real $v$, the bijection $W$ restricts to a bijection

$$
\mathcal D_v\longrightarrow
\mathcal C_v=\mathcal F(H_4,M,p_J,M,v).
\tag{19.5}
$$

Consequently (13.1) holds if and only if there are a real $v$ and
$x_{J0},x_{J1},x_{M0},x_{M1}\in\mathcal D_v$ satisfying

$$
\begin{gathered}
x_{J0}\ne x_{J1},\qquad x_{M0}\ne x_{M1},\\
\mathcal J(x_{J0})=\mathcal J(x_{J1}),\qquad
\mathcal M(x_{M0})=\mathcal M(x_{M1}).
\end{gathered}
\tag{19.6}
$$

Labels may coincide across the two pairs. Both within-branch
unequal-$r$ pairs and between-branch pairs are retained; at equal
$r$, distinctness is precisely use of the two different branch
labels. On $R_{\rm loc}\times K$, the global labels agree with
$b_0,b_1$ of Theorem 15.1 in lower-to-upper order.

**Proof.** Theorem 19.2 applies because $p_J\in I$. By the
literal response definitions, a parent world belongs to
$\mathcal C_v$ exactly when its actual $u_M$ is $v$.
Equation (19.3) expresses that value at every world in the
exhaustive parent parametrization. Restricting the parent
bijection therefore imposes exactly (19.4), proving (19.5)
with all child members included. Injectivity transports
both distinctness requirements, and (19.3) transports both
terminal equalities. This proves (19.6) without requiring
the two pairs to be disjoint.

Two parameter labels represent the same world exactly when
both their branch label and their $r$ agree, by Theorem 19.2.
This proves the equal- and unequal-$r$ assertions. On the local
rectangle, Theorem 15.1 exhausts the same two positive roots
of the same polynomial, so order identifies $b_-=b_0$
and $b_+=b_1$. ∎

**Definition 19.5 (Residual original equations).** The unresolved
joint question is the existence statement (19.6), with all four
parameters in the full fibre (19.4). A terminal-M pair still
requires both $\mathcal U(x)=\mathcal U(y)$ and
$\mathcal M(x)=\mathcal M(y)$ with $x\ne y$. Equality of
terminal-M images alone is an equality in the parent and does
not place the worlds in one acquired child.

Corollary 17.1 removes only equal-$r$ terminal-M pairs in
$R_{\rm loc}$. All unequal-$r$ pairs, and all equal-$r$ pairs
outside that interval, retain their original equations. The
entire singular-child and strip exclusions remain those supplied
in Definition 17.2 by $S$ and $E$; $Q(p_J,v)=0$ remains the
necessary condition of Theorem 11.2 for a regular terminal-M pair.
The global representation (19.5) supplies neither an enumeration
of terminal-M pairs nor an additional excluded root of $Q$,
and does not decide compatibility of the two distinct pairs
inside one entire $\mathcal C_v$.

## 20. Global affine separation of the actual terminal-M branches

**Definition 20.1 (Separator and its polynomial identities).** For the
complete world $W_i(r,p)$ of Definition 19.1, with $i\in\{-,+\}$,
$0<r<1$ and $p\in I$, write

$$
u_i(r,p)=d+(2U+n)g_i(6;r,p),\qquad
m_i(r,p)=d+(3U+2n)g_i(7;r,p),\qquad
F_i(r,p)=m_i(r,p)-6u_i(r,p)+216.
\tag{20.1}
$$

At $p=p_J$, these are exactly $\mathcal U(i,r)$ and
$\mathcal M(i,r)$ of (19.3). Retain the rational functions
$A_5,K_5,\Lambda$ of (19.1), with $j=X/b$, $n=N/b$, and put

$$
\begin{aligned}
L_6&=10-36/j+45/T-20/n,\\
L_7&=20-70/j+84/T-35/n,\\
F_0&=96+(3U+2n)\left(480-\frac{2268}{5T}\right)
       -6(2U+n)\left(240-\frac{243}{T}\right),\\
F_1&=-5+(3U+2n)L_7-6(2U+n)L_6,\\
C_5&=bTXNA_5,\\
Q_{\rm sep}&=5b^2TXN\{A_5F_0+F_1(p-24-K_5)\},\\
P_{\rm sep}&=\frac{N_m-6N_u+216D_m}{3}.
\end{aligned}
\tag{20.2}
$$

Here $N_u,N_m,D_m$ are exactly those of Section 14.
The last three expressions are integer polynomials, of coordinate
degrees at most $(6,7)$, $(8,8,1)$ and $(6,7)$ in $(r,b)$,
$(r,b,p)$ and $(r,b)$, respectively. In particular

$$
\begin{aligned}
P_{\rm sep}={}&1522b^7+(10063-7900r)b^6
 +(6956r^2-6049r+2591)b^5\\
&+(11704r^3-19624r^2+9588r-694)b^4\\
&+(-9500r^4+21057r^3-14714r^2+2813r)b^3\\
&+(-2364r^5+3105r^4+256r^3-303r^2-694r)b^2\\
&+(1182r^6-3090r^5+3116r^4-1690r^3+482r^2)b
 +228r^3(1-r)^3.
\end{aligned}
\tag{20.3}
$$

For a closed rational box $B$, write $\underline\beta_{n,B}(G)$
for the minimum of the degree-$n$ tensor Bernstein coefficients of
$G$ after mapping $[0,1]^d$ affinely onto $B$, using exactly (14.4).
The degrees, including zero padding, are part of each use below.
This is the coefficient operation of Section 14, not a new sign
criterion; its convex-hull implication is (14.5).

**Lemma 20.2 (A source-specific restriction on a separator zero).**
Let

$$
\begin{gathered}
E_2(r)=4r^2-2r-1,\qquad
E_4(r)=625r^4-1000r^3+50r^2+260r+36,\\
\Phi(r)=438272r^4-931328r^3+540800r^2-50728r-853,\\
J_1=[1348,1349]/10^4,\quad J_2=[8090,8091]/10^4,\\
J_3=[8500,8600]/10^4,\quad J_4=[8685,8686]/10^4,\quad
J_5=[9024,9025]/10^4.
\end{gathered}
\tag{20.4}
$$

For every $p\in I$, if an actual complete world $W_i(r,p)$ has
$F_i(r,p)=0$, then $r\in\bigcup_{k=1}^5J_k$.

**Proof.** The four samples in (19.1), evaluated by the weights in
$O$ (18.4), give

$$
g(6)=240-243/T+\epsilon L_6,\qquad
g(7)=480-2268/(5T)+\epsilon L_7.
\tag{20.5}
$$

Consequently its actual separator is $F=F_0+\epsilon F_1$.
The zero-safe parent equations $O$ (12.7) give
$\epsilon\Lambda=-(24/5)(b-1/8)B_{\rm coef}$.
Substituting (20.2), or expanding (20.3), gives the rational identity

$$
\Lambda F=
\Lambda F_0-\frac{24}{5}(b-1/8)B_{\rm coef}F_1
 =\frac{6P_{\rm sep}}{5bTUXN}.
\tag{20.6}
$$

All factors in the displayed denominator are positive at every
strict source. Thus $F=0$ implies $P_{\rm sep}=0$, including when
$\Lambda=0$. The same source satisfies $\mathsf A(r,b,p)=0$ by
Theorem 19.2.

Take the ordinary Sylvester resultant in $b$, with the coefficient
rows of $\mathsf A$ followed by those of $P_{\rm sep}$. Expansion
gives the exact polynomial identity

$$
\operatorname{Res}_b(\mathsf A,P_{\rm sep})
 =3456r^{11}(1-r)^9E_2(r)E_4(r)\Phi(r)R_{\rm sep}(r,p),
\tag{20.7}
$$

where $R_{\rm sep}\in\mathbb Z[r,p]$ has coordinate degrees $(18,7)$.
Equation (20.7) specifies it uniquely: divide the determinant by
all the displayed factors, including the positive constant $3456$.
Both inputs are fixed by (14.2) and (20.3); the determinant has
fourteen rows. Polynomial division has zero remainder. For the
signs of this particular quotient, put

$$
R_*(r,z)=100^7R_{\rm sep}\left(r,\frac{2744+z}{100}\right).
\tag{20.8}
$$

This is an integer polynomial. The following are lower bounds for
$10^{-32}\underline\beta_{(18,7),B}(\delta R_*)$, where
$B=[\alpha,\beta]\times[0,1]$.

| $[\alpha,\beta]$ | $\delta$ | Lower bound |
| --- | --- | --- |
| $[0,1/8]$ | $-1$ | $60608$ |
| $[1/8,1/4]$ | $-1$ | $9297$ |
| $[1/4,3/8]$ | $-1$ | $54870$ |
| $[3/8,1/2]$ | $-1$ | $320984$ |
| $[1/2,3/4]$ | $-1$ | $13777$ |
| $[3/4,17/20]$ | $-1$ | $7$ |
| $[43/50,1]$ | $1$ | $3$ |

These are finite rational coefficient inequalities. Explicitly,
for each row form

$$
H(x,z)=\delta\,100^7R_{\rm sep}
 \left(\alpha+(\beta-\alpha)x,\frac{2744+z}{100}\right).
$$

The 152 coefficients whose minimum is bounded are

$$
\sum_{a=0}^{j}\sum_{c=0}^{k}
 [x^az^c]H(x,z)
 \frac{\binom ja}{\binom{18}a}
 \frac{\binom kc}{\binom7c},
\quad 0\le j\le18,\quad0\le k\le7.
\tag{20.9}
$$

Substitution of the determinant quotient (20.7) gives the table.
Thus (20.7)–(20.9), the seven cells and the fixed degrees specify
all the coefficient inequalities without a root approximation.
By (14.5), $R_{\rm sep}(r,p)$ is strictly negative on
$[0,17/20]\times I$ and strictly positive on $[43/50,1]\times I$.
Any zero with $0<r<1$ and $p\in I$ therefore has $r\in J_3$.

For the other factors, the coefficient vectors in increasing powers
of $t$ of $(1+t)^dh(t/(1+t))$, with $d=\deg h$, are

$$
\begin{array}{c|l}
h&\text{coefficient vector}\\ \hline
E_2&(-1,-4,1)\\
E_4&(36,404,1046,24,-29)\\
\Phi&(-853,-54140,383498,-5324,-3837).
\end{array}
\tag{20.10}
$$

Descartes' rule, as used in Theorem 18.4, bounds their numbers of
roots in $(0,1)$ by one, one and two, respectively. The following
endpoint numerators give the corresponding sign changes. If
$J=[a,b]/10^4$, the two entries are exactly
$10^{4d}h(a/10^4)$ and $10^{4d}h(b/10^4)$.

| $h$ | $J$ | Left numerator | Right numerator |
| --- | --- | --- | --- |
| $E_2$ | $J_2$ | $-7600$ | $37124$ |
| $E_4$ | $J_4$ | $197923812890625$ | $-80318567990000$ |
| $\Phi$ | $J_1$ | $-7715213314818048$ | $40902172379369472$ |
| $\Phi$ | $J_5$ | $30626258854019072$ | $-31010500800000000$ |

The intermediate value theorem attains each of the bounds, so these
intervals contain every strict root of the corresponding factors.
Since a common finite $b$ root makes the Sylvester determinant zero,
(20.7), $0<r<1$ and the preceding bounds prove the assertion.
Only necessity of the resultant condition has been used. In
particular, (20.6) has not been divided by $\Lambda$. ∎

**Lemma 20.3 (Actual separator signs over the exceptional projections).**
For every $p\in I$ and $r\in\bigcup_{k=1}^5J_k$,

$$
F_-(r,p)>0,\qquad F_+(r,p)<0.
\tag{20.11}
$$

**Proof.** For the row labelled $(k,i)$ below, set
$B_{ki}=[\ell,h]/10^4$ and use the displayed sign $\chi$.
The roots $b_i(r,p)$ lie strictly in $B_{ki}$ for every
$(r,p)\in J_k\times I$. The four last columns are positive lower
bounds, in units of $10^{-6}$, for the following Bernstein minima:

$$
\begin{array}{c|c|c}
\text{column}&\text{polynomial and box}&\text{degrees}\\ \hline
a_\ell&\theta_i\mathsf A(r,\ell/10^4,p),\quad J_k\times I&(6,1)\\
a_h&-\theta_i\mathsf A(r,h/10^4,p),\quad J_k\times I&(6,1)\\
c&\chi C_5(r,b),\quad J_k\times B_{ki}&(6,7)\\
q&\theta_i\chi Q_{\rm sep}(r,b,p),\quad J_k\times B_{ki}\times I&(8,8,1),
\end{array}
\qquad \theta_-=1,\quad\theta_+=-1.
\tag{20.12}
$$

| $k$ | $i$ | $\ell$ | $h$ | $\chi$ | $a_\ell$ | $a_h$ | $c$ | $q$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $1$ | $-$ | $1249$ | $1251$ | $-1$ | $136$ | $54$ | $2346$ | $11591$ |
| $1$ | $+$ | $1859$ | $1863$ | $-1$ | $216$ | $369$ | $104809$ | $1088563$ |
| $2$ | $-$ | $1513$ | $1516$ | $1$ | $538$ | $962$ | $116104$ | $835618$ |
| $2$ | $+$ | $3113$ | $3117$ | $-1$ | $1695$ | $2713$ | $869515$ | $12702390$ |
| $3$ | $-$ | $1435$ | $1462$ | $1$ | $670$ | $788$ | $16582$ | $87556$ |
| $3$ | $+$ | $2689$ | $2781$ | $-1$ | $2102$ | $2532$ | $583642$ | $4334862$ |
| $4$ | $-$ | $1411$ | $1414$ | $1$ | $354$ | $486$ | $9114$ | $51412$ |
| $4$ | $+$ | $2615$ | $2621$ | $-1$ | $1826$ | $1471$ | $586149$ | $4081916$ |
| $5$ | $-$ | $1249$ | $1251$ | $-1$ | $148$ | $149$ | $16247$ | $82453$ |
| $5$ | $+$ | $2349$ | $2355$ | $-1$ | $1025$ | $980$ | $470037$ | $2115789$ |

All entries follow by substitution in (20.2), (14.2) and (14.4).
For example the first row asserts
$\underline\beta_{(6,1),J_1\times I}
(\mathsf A(r,1249/10^4,p))\ge136/10^6$ and
$\underline\beta_{(8,8,1),J_1\times B_{1-}\times I}
(-Q_{\rm sep})\ge11591/10^6$.
Thus (20.12) fixes every coefficient, box and degree used in the
table. There are no parameter subdivisions beyond the displayed
$J_k$, $B_{ki}$ and the whole $I$.

The first two columns of bounds and (14.5) give opposite strict
signs of $\mathsf A$ at the two $b$ endpoints. For each row with
$i=-$, direct rational comparison gives
$4(h/10^4)^2<r(1-r)$ on $J_k$; for each row with $i=+$ it gives
$4(\ell/10^4)^2>r(1-r)$ there. The intermediate value theorem
therefore gives a root in the indicated tube on the required side
of $\sigma(r)$. Theorem 18.4 identifies it with the unique
$b_i(r,p)$ on that side. This proves the tube assertions for both
branches on all five cells.

The column $c$ proves that $C_5$ has sign $\chi$ throughout that
tube. In particular $C_5\ne0$ and hence $A_5\ne0$ there, since
$bTXN>0$. The other zero-safe parent equation, $O$ (12.7), is
$\epsilon A_5=p-24-K_5$. It and (20.2), (20.5) give the actual
response identity

$$
F=F_0+\epsilon F_1
 =\frac{Q_{\rm sep}}{5bC_5}.
\tag{20.13}
$$

This division is justified by the strict column-$c$ bounds; it
requires neither $\Lambda\ne0$ nor a nonzero gain sample or drift.
The column $q$ says that $Q_{\rm sep}$ has sign $\theta_i\chi$.
As $b>0$, (20.13) has sign $\theta_i$, proving (20.11).
In particular this establishes actual nonzero separator values
also over the two $\Phi$ intervals, where (20.6) alone could have
a zero right side without a zero actual response. ∎

**Theorem 20.4 (Uniform affine separation on the full source branches).**
For every $p\in I$ and $0<r<1$,

$$
m_-(r,p)>6u_-(r,p)-216,\qquad
m_+(r,p)<6u_+(r,p)-216.
\tag{20.14}
$$

**Proof.** If either branch had a zero separator, Lemma 20.2 would
put its $r$ in one of the five cells, contradicting Lemma 20.3.
Thus neither separator vanishes anywhere on its entire stated
domain. Fix any $p\in I$. By Theorem 19.2 and the actual response
definitions, $F_i(r,p)$ is continuous for all $0<r<1$, including
singular sources. Lemma 20.3 supplies its positive sign on $J_1$
for $i=-$ and its negative sign there for $i=+$. The intermediate
value theorem on the connected interval $(0,1)$ keeps each sign
unchanged throughout that interval. This proves (20.14) for the
arbitrary fixed $p$, and hence on all of $I$.

The Bernstein convex-hull identity, Descartes' rule and the
common-root implication for a Sylvester determinant are the
standard supplier steps already used in Sections 6, 14 and 18.
The polynomial identity (20.7), its coefficient bounds, the actual
response bounds in Lemma 20.3 and their full-branch consequence
(20.14) concern the particular source and responses of this volume.
No restriction on a gain sample, gain degree, gain roots or drift
has entered the argument. ∎

**Corollary 20.5 (Strict opposite-branch order and the remaining joint equations).**
At the original exact algebraic $p_J$, for every $r,s\in(0,1)$,

$$
\mathcal U(-,r)=\mathcal U(+,s)
 \quad\Longrightarrow\quad
\mathcal M(-,r)>\mathcal M(+,s).
\tag{20.15}
$$

Consequently every distinct terminal-M pair in (19.6), in every
entire actual child $\mathcal C_v$, must have the form
$(i,r),(i,s)$ with the same $i$ and $r\ne s$. The remaining
terminal-M equations are exactly

$$
\mathcal U(i,r)=\mathcal U(i,s)=v,\qquad
\mathcal M(i,r)=\mathcal M(i,s),\qquad r\ne s.
\tag{20.16}
$$

The original joint predicate still additionally requires two
distinct points $x_{J0},x_{J1}$ in that same entire $\mathcal D_v$
with $\mathcal J(x_{J0})=\mathcal J(x_{J1})$. This corollary does
not decide either (20.16) or that compatibility condition.

**Proof.** The original $p_J$ belongs to $I$ by Definition 18.1.
For a common acquired response $v$, Theorem 20.4 gives

$$
\mathcal M(-,r)>6v-216>\mathcal M(+,s),
$$

which proves (20.15), including $r=s$. If a terminal-M collision
used opposite labels, reversing their order if necessary would
contradict this strict inequality. For equal labels, distinctness
is precisely $r\ne s$ by Theorem 19.2. The entire-child bijection
of Theorem 19.4 therefore leaves exactly (20.16) as the terminal-M
part of (19.6), with its original same-$v$ terminal-J requirement
unchanged. No source coordinate has been bounded or omitted. ∎
