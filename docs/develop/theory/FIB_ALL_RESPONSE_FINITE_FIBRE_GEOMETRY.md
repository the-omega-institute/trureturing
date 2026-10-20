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
