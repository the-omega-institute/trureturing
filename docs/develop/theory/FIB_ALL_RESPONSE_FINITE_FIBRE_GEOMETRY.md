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

## 21. A nonlinear order on the entire lower source branch

**Definition 21.1 (Bounded source coordinate and nonlinear response).**
Retain the interval $K=[p_c-10^{-40},p_c+10^{-40}]$ of (14.1),
the complete worlds of Definition 19.1 and their actual responses
$u_i(r,p),m_i(r,p)$ of (20.1). Set

$$
\begin{gathered}
q=r(1-r),\qquad z=b/q,\qquad b=qz,\qquad c=1/z,\\
J_0=1+qz^2,\qquad N_0=J_0+rz,\qquad
j=J_0/z,\quad n=N_0/z,\quad T=1+qz,\quad U=1+2qz,\quad V=U+n,\\
B=6/T-2/U,\qquad \Lambda=1+6/T+1/U-4/j-4/n,\\
A_5=1+V(4-15/j+20/T-10/n),\qquad
K_5=96(b-1/8)V/T,\\
\alpha=-(24/5)(b-1/8)B,\qquad
\beta=p-24-K_5,\qquad E=\alpha A_5-\beta\Lambda,\\
P_*(w)=\frac{13w}{2}+\frac{21(w-144)^2}{1600}
                  -\frac{31(w-144)^3}{48000},\\
H_-(r,p)=m_-(r,p)-P_*(u_-(r,p)).
\end{gathered}
\tag{21.1}
$$

All expressions on the first four lines extend rationally to
$0\le r\le1$, $z>0$. Polynomial quotients below are cancelled
before evaluation at $r=0$ or $r=1$. Write

$$
\widetilde A(r,z,p)=\frac{\mathsf A(r,qz,p)}{q^3}.
\tag{21.2}
$$

This is a polynomial of coordinate degrees $(8,7,1)$. Direct
substitution in (14.2) gives the identity

$$
E=-\frac{2\widetilde A}{5zTUJ_0N_0}.
\tag{21.3}
$$

In particular, on $0<r<1$, $z>0$, its zeros are exactly the
original source zeros. The lower label is characterized by
$4qz^2<1$, using Theorem 18.4. The zero-safe parent equations
are $\epsilon\Lambda=\alpha$ and $\epsilon A_5=\beta$.

**Definition 21.2 (Two polynomial response charts).** For the first
chart put

$$
n_0=\frac{N_u(r,qz)}{q^3},\qquad
m_0=\frac{N_m(r,qz)}{q^3},\qquad
d_0=\frac{D_m(r,qz)}{q^3}
   =\frac52zTUJ_0N_0\Lambda.
\tag{21.4}
$$

Here $N_u,N_m,D_m$ are exactly those of Section 14. All three
quotients in (21.4) are polynomials. For the second chart put

$$
\begin{aligned}
G_5&=(4T+20)J_0N_0-zT(15N_0+10J_0),\\
G_6&=(10T+45)J_0N_0-zT(36N_0+20J_0),\\
G_7&=(20T+84)J_0N_0-zT(70N_0+35J_0),\\
C&=zTJ_0N_0+(Uz+N_0)G_5=zTJ_0N_0A_5,\\
B_5&=zT(p-24)-96(b-1/8)(Uz+N_0),\qquad d_1=zC,\\
n_1&=\frac{\{24zT+(2Uz+N_0)(240T-243)\}C
        +\{zTJ_0N_0+(2Uz+N_0)G_6\}B_5}{T},\\
m_1&=\frac{\{24zT+(3Uz+2N_0)(480T-2268/5)\}C
        +\{zTJ_0N_0+(3Uz+2N_0)G_7\}B_5}{T}.
\end{aligned}
\tag{21.5}
$$

The two divisions by $T$ are exact in $\mathbb Q[r,z,p]$.
On an actual source with $d_k\ne0$ the corresponding responses
are $u=n_k/d_k$, $m=m_k/d_k$. For $k=0$ this is the regular
chart of Section 14. For $k=1$, substitute
$\epsilon=\beta/A_5=B_5J_0N_0/C$ in (20.5) and (19.3).
Thus this second chart is valid also at $\Lambda=0$ whenever
$A_5\ne0$.

For polynomials $f,d$ define

$$
\begin{aligned}
\mathcal L(f,d)
 &= (f_rd-fd_r)\widetilde A_z
       -(f_zd-fd_z)\widetilde A_r,\\
\mathcal R(n,m,d)
 &=16000d^2\mathcal L(m,d)\\
 &\quad-\{104000d^2+420(n-144d)d-31(n-144d)^2\}
                      \mathcal L(n,d),\\
G^{(0)}&=-\frac{\mathcal R(n_0,m_0,d_0)}{15z},\qquad
G^{(1)}=-\frac{\mathcal R(n_1,m_1,d_1)}{z}.
\end{aligned}
\tag{21.6}
$$

Both last quotients are integer polynomials. Their coordinate
degrees in $(r,z,p)$ are respectively $(38,32,1)$ and $(38,36,4)$.
Equations (21.2), (21.4)–(21.6) specify every coefficient, including
the normalization of these two polynomials.

**Definition 21.3 (Finite rational inclusions).** Use interval
addition, negation, multiplication and reciprocal with outward
rounding to the grid $Q^{-1}\mathbb Z$, where

$$
Q=2^{220},\qquad N=4096,\qquad h=\frac1{2N},\qquad
\rho=\frac{256}{N^2},\qquad r_j=\frac{2j+1}{2N}
\quad(0\le j<N).
\tag{21.7}
$$

Thus a rational $a$ is enclosed by
$[\lfloor Qa\rfloor,\lceil Qa\rceil]/Q$. On intervals with
integer endpoints $[a,b]/Q$, $[c,d]/Q$, multiplication has endpoints

$$
\frac1Q\left[
 \left\lfloor\frac{\min(ac,ad,bc,bd)}Q\right\rfloor,
 \left\lceil\frac{\max(ac,ad,bc,bd)}Q\right\rceil\right].
\tag{21.8}
$$

For an interval not containing zero, reciprocal has endpoints
$[\lfloor Q^2/b\rfloor,\lceil Q^2/a\rceil]/Q$.
Apply the ordinary product and reciprocal differentiation rules
to (21.1) for first and second derivative intervals of $E$.
For example, with $w=1/v$,

$$
(vt)_{ab}=v_{ab}t+v_at_b+v_bt_a+vt_{ab},\qquad
w_a=-w^2v_a,\qquad
w_{ab}=2w^3v_av_b-w^2v_{ab}.
\tag{21.9}
$$

The derivatives in (21.9) are with respect to $r,z$, with $p$
held fixed. All rational expressions use the parentheses of
(21.1); unparenthesized sums and products are taken from left
to right.

The following recursion specifies rational centres and slopes.
Start $t_{0,0}=1$ and, for $j>0$, $t_{j,0}=t_{j-1,3}$.
For $\ell=0,1,2$ let $V_{j\ell},Z_{j\ell}$ be the value and
$z$-derivative interval of $E(r_j,t_{j,\ell},p_c)$ and put

$$
\begin{gathered}
I_{j\ell}=[t_{j,\ell},t_{j,\ell}]-V_{j\ell}/Z_{j\ell},\qquad
t_{j,\ell+1}=2^{-40}\left\lfloor
                       2^{40}\inf I_{j\ell}\right\rfloor,\\
z_j=t_{j,3},\qquad
S_j=-[E_r](r_j,z_j,p_c)/[E_z](r_j,z_j,p_c),\qquad
s_j=2^{-24}\left\lfloor2^{24}\inf S_j\right\rfloor.
\end{gathered}
\tag{21.10}
$$

Square brackets on a rational function or derivative denote its
interval extension just specified. Define the closed intervals
and affine tubes

$$
\begin{gathered}
R_j=[r_j-h,r_j+h],\qquad
Z_j=[z_j-|s_j|h-\rho,z_j+|s_j|h+\rho],\\
\mathcal V_j=\{(r,z):r\in R_j,
                 \ |z-z_j-s_j(r-r_j)|\le\rho\},\\
D_j=[E_{rr}](R_j,Z_j,K)+2s_j[E_{rz}](R_j,Z_j,K)
                         +s_j^2[E_{zz}](R_j,Z_j,K),\\
M_j^\pm=[E](r_j,z_j\pm\rho,K)
       +\bigl([E_r](r_j,z_j\pm\rho,K)
                     +s_j[E_z](r_j,z_j\pm\rho,K)\bigr)[-h,h]
       +\tfrac12D_j[0,h^2].
\end{gathered}
\tag{21.11}
$$

For the polynomial inclusion use chart $k_j=1$ for
$j\le613$ or $j\ge3645$, and $k_j=0$ otherwise. If $j<2048$ set
$x=r$, $x_j=r_j$, $\tau_j=s_j$ and $F_j(x,z,p)=G^{(k_j)}(x,z,p)$.
Otherwise set $x=1-r$, $x_j=1-r_j$, $\tau_j=-s_j$ and
$F_j(x,z,p)=G^{(k_j)}(1-x,z,p)$.
Expand $F_j$ exactly as a polynomial before taking intervals.
Its interval extension and those of its derivatives use nested
Horner evaluation, in descending powers: first $p$ in each
coefficient, then $z$, then $x$.

For $a+b\le4$ put

$$
V_{ab,j}=\begin{cases}
 [\partial_x^a\partial_z^bF_j](x_j,z_j,K),&a+b<4,\\
 [\partial_x^a\partial_z^bF_j]
       ([x_j-h,x_j+h],Z_j,K),&a+b=4,
\end{cases}
\qquad
C_{ab,j}=\sum_{t=0}^a\binom at\tau_j^t V_{a-t,b+t,j}.
\tag{21.12}
$$

For $d>0$ write $I_d(H)=[0,H^d]$ when $d$ is even and
$I_d(H)=[-H^d,H^d]$ when $d$ is odd; put $I_0(H)=[1,1]$.
The polynomial inclusion is

$$
T_j=\sum_{a=0}^4\sum_{b=0}^{4-a}
 \frac{C_{ab,j}}{a!b!}\,I_a(h)I_b(\rho).
\tag{21.13}
$$

Finite sums in (21.12)–(21.13) use increasing indices. These
inclusions are the interval and derivative operations of $O$,
Definition 7.2, with a binary grid, together with Taylor's formula.
The interval inclusion property and derivative arithmetic are
standard; see S. M. Rump,
[*Verification methods: Rigorous results using floating-point
arithmetic*](https://doi.org/10.1017/S096249291000005X),
Sections 5.1, 5.5 and 11. The specific polynomials, recursion and
inequalities below concern the original source of this volume.

**Lemma 21.4 (A full-domain lower-branch sign).** For every $p\in K$
and $0<r<1$, the lower source point $(r,b_-(r,p)/q)$ belongs to
some $\mathcal V_j$. On that tube its selected response denominator
$d_{k_j}$ is nonzero and $G^{(k_j)}>0$.

**Proof.** The finite rational quantities (21.7)–(21.13) satisfy
the following bounds. In every row, every integer $j$ in the
stated range is included. The denominator column concerns
$-[A_5](R_j,Z_j,K)$ when $k_j=1$, and
$[\Lambda](R_j,Z_j,K)$ when $k_j=0$; $D_*$ is a lower bound
for its lower endpoint.

| $j$ | $k_j$ | $D_*$ | $-N^2\sup M_j^-$ exceeds | $N^2\inf M_j^+$ exceeds | $\inf V_{00,j}$ exceeds |
| --- | --- | --- | --- | --- | --- |
| $0,\ldots,613$ | $1$ | $1/3$ | $4000$ | $4000$ | $10^7$ |
| $614,\ldots,2047$ | $0$ | $3/50$ | $3000$ | $3000$ | $50000$ |
| $2048,\ldots,3644$ | $0$ | $1/5$ | $5000$ | $5000$ | $6\cdot10^8$ |
| $3645,\ldots,4095$ | $1$ | $5/2$ | $5000$ | $5000$ | $5\cdot10^{12}$ |

In all four rows the further inequalities are

$$
\begin{gathered}
\inf Z_{j\ell}>12\quad(\ell=0,1,2),\qquad
\frac35<\inf Z_j\le\sup Z_j<\frac74,\qquad |s_j|<6,\\
\sup\{4[R_j](1-[R_j])[Z_j]^2\}<\frac{24}{25},\qquad
\inf T_j>\frac9{10}\sup V_{00,j}>0.
\end{gathered}
\tag{21.14}
$$

Here $Z_{j\ell}$ is the derivative interval of (21.10), whereas
$Z_j$ is the coordinate interval of (21.11). The braces in the
second line mean interval arithmetic, rather than a selection of
source points. The table and (21.14) are finite rational
inequalities: substitute the polynomial definitions (21.2),
(21.4)–(21.6) into the coefficient operation (21.12), and use
(21.8)–(21.10) for the centres and derivatives. All endpoints are
integer multiples of $2^{-220}$; the displayed rational bounds
follow by integer cross multiplication. This specifies all
$4096$ tubes, both polynomial normalizations, every subdivision
and every arithmetic precision in the inequalities.

The derivative bounds in (21.14) justify every reciprocal in
(21.10). The other reciprocals used in (21.1) have positive
source denominators throughout the indicated boxes. The table's
$D_*$ bounds give $A_5<0$ on each chart-1 box and
$\Lambda>0$ on each chart-0 box. In particular the corresponding
$d_1=z^2TJ_0N_0A_5$ or
$d_0=(5/2)zTUJ_0N_0\Lambda$ never vanishes there.

Fix $p\in K$. Taylor's formula in the single variable $r$,
along $z=z_j+s_j(r-r_j)\pm\rho$, gives

$$
E(r,z_j+s_j(r-r_j)\pm\rho,p)\in M_j^\pm
\qquad(r\in R_j).
\tag{21.15}
$$

The two signs in the table are strict. For each
$r\in R_j\cap(0,1)$, the intermediate value theorem therefore
gives an $E$ zero between these two faces. Equations (21.3) and
(21.14) put that zero at a positive source satisfying
$4qz^2<1$. Theorem 18.4 identifies it with the unique lower
source root. This proves the asserted tube inclusion. The closed
cells $R_j$ cover $[0,1]$, so no strict source coordinate is lost.

For completeness, (21.13) encloses $F_j$ on its entire affine
tube, not just at its centre. Apply the one-variable Taylor
formula through degree three to

$$
t\longmapsto F_j(x_j+t\delta,
               z_j+t(\tau_j\delta+y),p),\qquad
|\delta|\le h,\quad |y|\le\rho.
\tag{21.16}
$$

The multinomial expansion of its derivatives gives the terms
$C_{ab,j}\delta^a y^b/(a!b!)$. For $a+b<4$ the derivatives
are evaluated at the centre. For total degree four the integral
remainder averages derivatives on the segment, which lies in
$[x_j-h,x_j+h]\times Z_j$. Those averages belong to the
intervals on the second line of (21.12). Parity gives
$\delta^a\in I_a(h)$ and $y^b\in I_b(\rho)$.
The interval inclusion property proves (21.13) for every such
point and every $p\in K$. Its strictly positive lower endpoint
in (21.14) proves $G^{(k_j)}>0$ on the full tube. This also
proves positivity at any source with $\Lambda=0$, since such a
source cannot belong to a chart-0 box and the chart-1 formula
uses $A_5$ instead. ∎

**Theorem 21.5 (Strict nonlinear order and lower-branch joint injectivity).**
For every real $p\in K$ and every $0<r<1$,

$$
\frac{\partial H_-}{\partial r}(r,p)>0.
\tag{21.17}
$$

Consequently, for every $r,s\in(0,1)$,

$$
u_-(r,p)=u_-(s,p),\quad m_-(r,p)=m_-(s,p)
\quad\Longrightarrow\quad r=s.
\tag{21.18}
$$

**Proof.** The lower root of $\mathsf A$ is simple and crosses
from positive to negative as $b$ increases, by Theorem 18.4.
It therefore has $\mathsf A_b<0$. Since $q>0$, (21.2) gives

$$
\widetilde A_z=q^{-2}\mathsf A_b<0.
\tag{21.19}
$$

Choose a cell containing the given $r$. Lemma 21.4 supplies its
nonzero chart denominator and the positive polynomial
$G^{(k_j)}$ at the actual lower root. In this chart,
implicit differentiation of $\widetilde A=0$ and ordinary
quotient differentiation give

$$
\frac{d}{dr}\{m-P_*(u)\}
 =\frac{\mathcal R(n_{k_j},m_{k_j},d_{k_j})}
              {16000d_{k_j}^4\widetilde A_z}
 =\begin{cases}
 \displaystyle\frac{-15zG^{(0)}}{16000d_0^4\widetilde A_z},&k_j=0,\\
 \displaystyle\frac{-zG^{(1)}}{16000d_1^4\widetilde A_z},&k_j=1.
 \end{cases}
\tag{21.20}
$$

Indeed
$16000P_*'(n/d)=104000+420(n-144d)/d-31(n-144d)^2/d^2$,
which is exactly the factor in (21.6). Each expression in
(21.20) is strictly positive by $z>0$, (21.19) and Lemma 21.4.
Both charts describe the same actual responses, so their overlap
introduces no new response or gain choice. Smoothness at every
strict source, including $\Lambda=0$, is supplied by Theorem
19.2. This proves (21.17) everywhere on the entire lower branch.

For $r<s$, the mean value theorem on $[r,s]\subset(0,1)$ gives
$H_-(r,p)<H_-(s,p)$. Equality of both actual responses would
give equality of their $H_-$ values and contradict this strict
inequality. This proves (21.18).

The interval $K$ is used uniformly in Lemma 21.4; $p_c$ enters
only the rational tube recursion. The particular polynomial
identities and lower-branch order are repo-derived. The Taylor
and interval tools cited after Definition 21.3 are intermediate
results, applied here to the original full source branches. ∎

**Corollary 21.6 (Only upper-branch terminal-M pairs can remain).**
At the original exact algebraic $p_J$, no entire child
$\mathcal C_v$ contains a distinct terminal-M pair from the lower
branch. The original joint predicate (19.6) is equivalent to the
existence of $v\in\mathbb R$, $r,s\in(0,1)$ and
$x,y\in\mathcal D_v$ such that

$$
\begin{gathered}
r\ne s,\qquad x\ne y,\\
\mathcal U(+,r)=\mathcal U(+,s)=v,\qquad
\mathcal M(+,r)=\mathcal M(+,s),\qquad
\mathcal J(x)=\mathcal J(y).
\end{gathered}
\tag{21.21}
$$

The terminal-J pair in this formula is taken in the entire
$\mathcal D_v$ and may use either label or overlap the terminal-M
pair.

**Proof.** The original $p_J$ belongs to $K$ by Definition 14.1.
Theorem 21.5 excludes same-label lower-branch terminal-M pairs
in every acquired fibre. Corollary 20.5 excludes opposite-label
terminal-M pairs. Thus a distinct terminal-M pair must consist
of two different upper-branch parameters, giving (21.21).
Conversely any points in (21.21) supply both distinct pairs in
(19.6), and Theorem 19.4 transports them to that one entire
actual child. The inherited complete-world correspondence retains
lower gain degrees, sampled zeros, repeated gain roots and zero
drift. No additional observation or restriction on the gain,
drift or source has entered this equivalence. ∎

## 追加锚（本行以下为增补区）

## 22. A regular chart containing the entire upper source branch

**Definition 22.1 (The upper actual response order).** Retain the literal
$H_4=(0,J,24,M,147/5,J,24,M,18)$, complete worlds of Section 1,
$\mathsf A$ of (14.2), $I=[686/25,549/20]$ of Definition 18.1,
and $K=[p_c-10^{-40},p_c+10^{-40}]$ of (14.1). In particular
$p_J$ is the original exact algebraic parameter specified in Definition
14.1, and $p_J\in K\subset I$; $p_c$ is only a rational centre.
Write $u_+(r,p)$ and $m_+(r,p)$ for the actual clock-six $M$ and
clock-seven $M$ responses of $W_+(r,p)$ in (19.1). Define

$$
\begin{gathered}
\Psi(x,y)=366y^2+331y^3-269x+501xy^2-539x^2-141x^2y-334x^3,\\
\Theta_+(r,p)=\Psi\left(\frac{u_+(r,p)-144}{20},
                \frac{m_+(r,p)-6u_+(r,p)+216}{20}\right).
\end{gathered}
\tag{22.1}
$$

The quantities in this definition use the one entire gain and fixed drift
of each original world. The polynomial $\Psi$ is a function of its two
actual responses, with no additional observation.

**Lemma 22.2 (A global upper-root bracket).** For every $p\in I$ and
$0<r<1$,

$$
 b_-(r,p)<\frac16<b_+(r,p)<\frac12.
\tag{22.2}
$$

Every complete world on the upper branch has $\Lambda\ne0$.

Proof. For $k=0,1,2,3$, substitute $r=(k+x)/4$, $0\le x\le1$,
into $-\mathsf A(r,1/6,p)$ and $\mathsf A(r,1/2,p)$.
Their degrees in $x$ are at most six. Apply (14.4) with degree six
at each of the two endpoints of $I$. The exact minima among the
$4\cdot2\cdot7=56$ coefficients of each polynomial are

$$
 \min\beta^6_j\bigl(-\mathsf A((k+x)/4,1/6,p)\bigr)
       =\frac{259}{27648},\qquad
 \min\beta^6_j\bigl(\mathsf A((k+x)/4,1/2,p)\bigr)
       =\frac{1577691}{81920}.
\tag{22.3}
$$

Here the minimum includes $k$, the endpoint $p$, and $j$.
The first minimum occurs at $(p,k,j)=(549/20,0,5)$ and the
second at $(549/20,2,3)$. For an explicit rational specification
of all 112 comparisons, let $c_i(b,p)=[r^i]\mathsf A(r,b,p)$,
using the literal polynomial (14.2). The coefficient indexed by
$(k,j)$ before the sign change in the first family is

$$
 \sum_{a=0}^j\frac{\binom ja}{\binom6a}
    \sum_{i=a}^6 c_i(b,p)\binom ia
                   (k/4)^{i-a}4^{-a}.
\tag{22.4}
$$

Thus (22.3) is a finite rational comparison, including zero padding
through degree six. The nonnegative partition-of-unity identity
(14.5) makes both polynomials strictly positive on each quarter.
Affinity in $p$ extends these signs from the two endpoints to all
of $I$. Hence $\mathsf A(r,1/6,p)<0<\mathsf A(r,1/2,p)$.
Theorem 18.4 supplies exactly two positive roots, with
$\mathsf A(r,0,p)>0$. The intermediate value theorem gives one
root below $1/6$ and one between $1/6$ and $1/2$; exhaustiveness
and their order identify them as $b_-$ and $b_+$.

For any actual parent world, $\Lambda=0$ forces $b=1/8$ by
(12.7) of $O$, as explained in Theorem 19.2. Equation (22.2)
excludes that value on the upper branch. This restriction is a
consequence of the original source equation for all positive $b$,
rather than an assumption bounding the original source domain. ∎

**Definition 22.3 (The fixed-gain regular response formulas).** On every
upper source with $p\in I$, put

$$
\begin{gathered}
 q=r(1-r),\quad j=b+q/b,\quad n=j+r,\quad T=1+b,\quad U=1+2b,\\
 \Lambda=1+6/T+1/U-4/j-4/n,\\
 \epsilon=-\frac{24}{5}(b-1/8)(6/T-2/U)/\Lambda.
\end{gathered}
\tag{22.5}
$$

Then the actual responses are the following rational functions of
that source:

$$
\begin{aligned}
 u(r,b)&=24+\epsilon+(2U+n)
       \{240-243/T+\epsilon(10-36/j+45/T-20/n)\},\\
 m(r,b)&=24+\epsilon+(3U+2n)
       \{480-2268/(5T)+\epsilon(20-70/j+84/T-35/n)\}.
\end{aligned}
\tag{22.6}
$$

In particular $u_+(r,p)=u(r,b_+(r,p))$ and
$m_+(r,p)=m(r,b_+(r,p))$.

The agreement with the original world follows directly from the
zero-safe whole-world lift (19.1). Its parent identity
$\epsilon\Lambda=-(24/5)(b-1/8)(6/T-2/U)$ and Lemma 22.2
justify (22.5). The four interpolation values remain exactly

$$
 (g(0),g(1),g(2),g(3))
 =(-24-\epsilon,-\epsilon/j,(27/5-\epsilon)/T,-\epsilon/n).
$$

The four-node Lagrange weights at clock six are $(-10,36,-45,20)$,
and at clock seven they are $(-20,70,-84,35)$. Multiplying these
weights by the displayed values gives the two braces in (22.6).
The actual traces are $2U+n$ and $3U+2n$ by (19.3), and the
same fixed drift is $24+\epsilon$ at both clocks. This proves
(22.6) directly from the entire interpolant.

These formulas also agree with the polynomial response charts in
Sections 2 and 14. Indeed $j=X/b$, $n=N/b$ and
$\Lambda=2D/(TUXN)$, so (22.5) becomes
$\epsilon=-3K_\Lambda XN/(5D)$. The two braces in (22.6) become
$3(80b-1)/T+\epsilon G_{6,\Lambda}/(TXN)$ and
$12(200b+11)/(5T)+\epsilon G_7/(TXN)$, respectively.
Multiplication by $5bD$ yields exactly $N_u$ and $N_m$ in
Section 2 and (14.3). All of $b,j,n,T,U$ are positive, and the
only additional divided quantity is the nonzero $\Lambda$.
No gain sample, leading coefficient, root difference, or drift
has been divided out. ∎

## 23. A full-domain rational sign certificate for the upper response order

**Definition 23.1 (Rational cells and affine tubes).** Index 1,025 closed
intervals by $k=0,\ldots,1024$. For $0\le k\le1022$ put

$$
 R_k=[k/1024,(k+1)/1024],\qquad L_k=1024.
$$

The last two intervals are

$$
 R_{1023}=[2046/2048,2047/2048],\quad
 R_{1024}=[2047/2048,1],\qquad L_{1023}=L_{1024}=2048.
$$

They cover $[0,1]$. Let $r_k$ be the midpoint of $R_k$, and put
$h_k=1/(2L_k)$ and $\rho_k=4/L_k^2$.
At $(r_k,p_c)$, start with $[l_0,v_0]=[1/6,1/2]$.
For $i=0,\ldots,31$, let $z_i=(l_i+v_i)/2$ and set

$$
 (l_{i+1},v_{i+1})=
 \begin{cases}
 (z_i,v_i),&\mathsf A(r_k,z_i,p_c)<0,\\
 (l_i,z_i),&\mathsf A(r_k,z_i,p_c)\ge0.
 \end{cases}
\tag{23.1}
$$

All these comparisons are exact rational comparisons. Set

$$
 B_k=(l_{32}+v_{32})/2,\qquad
 s_k=2^{-40}\left\lfloor
       -2^{40}\frac{\mathsf A_r(r_k,B_k,p_c)}
                      {\mathsf A_b(r_k,B_k,p_c)}\right\rfloor.
\tag{23.2}
$$

The denominator in (23.2) is strictly positive, as included in
Lemma 23.3 below. In the affine coordinates

$$
 r=r_k+t,\qquad b=B_k+s_kt+e,
 \qquad |t|\le h_k,\quad |e|\le\rho_k,\quad p\in K,
\tag{23.3}
$$

define

$$
\begin{gathered}
 a(t,e,p)=\mathsf A(r_k+t,B_k+s_kt+e,p),\\
 \vartheta(r,b)=\Psi((u(r,b)-144)/20,(m(r,b)-6u(r,b)+216)/20),\\
 \theta(t,e)=\vartheta(r_k+t,B_k+s_kt+e),\qquad
 \Gamma=\theta_t-\theta_e a_t/a_e.
\end{gathered}
\tag{23.4}
$$

All derivatives in (23.4) are taken after substitution (23.3).
The centre and the tube are auxiliary rational constructions; neither
is a replacement world or a replacement value of $p_J$.

**Definition 23.2 (Finite coefficient enclosures).** The following
specifies rational enclosures for (23.4). Put $Q=2^{160}$.
Represent an interval by $[l/Q,v/Q]$, $l,v\in\mathbb Z$, and
convert any rational interval $[c,d]$ to
$[\lfloor Qc\rfloor/Q,\lceil Qd\rceil/Q]$.
Addition and negation are exact endpoint operations. For two intervals
with integer endpoints $(l,v)$ and $(l',v')$, multiplication has
integer endpoints

$$
 \left(\left\lfloor\frac{\min(ll',lv',vl',vv')}{Q}\right\rfloor,
       \left\lceil\frac{\max(ll',lv',vl',vv')}{Q}\right\rceil\right).
\tag{23.5}
$$

For an interval excluding zero, its reciprocal has integer endpoints
$\bigl(\lfloor Q^2/v\rfloor,\lceil Q^2/l\rceil\bigr)$.
Division means multiplication by this reciprocal.

Use normalized bivariate derivative coefficients: an index $(a,b)$
stands for $\partial_t^a\partial_e^bf/(a!b!)$. The finite coefficient
arrays have total degree at most five for $a,\theta$, and at most
four for $\Gamma$. Their indices are ordered by increasing total
degree, then increasing first index. Addition is coordinatewise;
product coefficients use the convolution

$$
 [fg]_{ab}=\sum_{i=0}^a\sum_{j=0}^b[f]_{ij}[g]_{a-i,b-j},
\tag{23.6}
$$

with increasing $i$, then increasing $j$, starting each sum at zero.
For a reciprocal, process the nonconstant indices in the indicated
order and use

$$
 [f^{-1}]_{00}=[f]_{00}^{-1},\qquad
 [f^{-1}]_{ab}=-[f^{-1}]_{00}
   \sum_{\substack{0\le i\le a,\ 0\le j\le b\\i+j>0}}
               [f]_{ij}[f^{-1}]_{a-i,b-j}.
\tag{23.7}
$$

To differentiate a degree-five array and obtain degree four, use
$[f_t]_{ab}=(a+1)[f]_{a+1,b}$ and
$[f_e]_{ab}=(b+1)[f]_{a,b+1}$.

For centre arrays, give $t,e$ constant coefficients zero; for box
arrays give them constant coefficients $[-h_k,h_k]$ and
$[-\rho_k,\rho_k]$. In both cases set $[t]_{10}=[e]_{01}=1$
and all other nonconstant coefficients to zero. Constants have only
a constant coefficient. Give $p$ constant coefficient $K$ throughout.
Substitute (23.3), then evaluate (22.5)–(22.6) and (23.4).
For $\mathsf A$ use $X=bb+q$, $N=X+br$, $T=1+b$, $U=1+2b$,

$$
\begin{aligned}
 D&=(bb+8b+4)XN-2bTU(X+N),\\
 H&=14b^6+(95-73r)b^5+(47rr-39r+30)b^4\\
  &\quad+r(147rr-232r+105)b^3
     +2q(44rr-55r+15)bb-64rqqb-32q^3,\\
 \mathsf A&=5b(p-24)D+3(8b-1)H,
 \qquad q=r(1-r).
\end{aligned}
\tag{23.8}
$$

This is exactly the polynomial (14.2); in particular the last two
terms of $H$ retain both endpoint factors. In this enclosure
specification, juxtaposed products and successive additions or
subtractions are evaluated from left to right, with the displayed
parentheses taking precedence. Powers use $z^0=1$, $z^1=z$,
$z^{2j}=z^jz^j$ and $z^{2j+1}=(z^jz^j)z$.
In the second brace of (22.6), evaluate the constant rational as
$480-(2268/5)/T$. For the evaluation of $\Psi$, use the equivalent
ordered expression

$$
 (((((366yy+331y^3)-269x)+501xyy)-539xx)-141xxy)-334x^3.
\tag{23.9}
$$

Here $x=(u-144)/20$ and $y=(m-6u+216)/20$; thus (23.9)
specifies the grouping of the coefficient arithmetic without changing
(22.1). Every scalar rational conversion and each product or reciprocal
uses (23.5)–(23.7). Write $f^c_{ab},f^B_{ab}$ for the resulting
centre and box intervals.

For $H\ge0$, define $I_0(H)=\{1\}$,
$I_j(H)=[0,H^j]$ for positive even $j$, and
$I_j(H)=[-H^j,H^j]$ for odd $j$. Form the intervals

$$
\begin{aligned}
 C_k={}&a^c_{00}+a^c_{10}I_1(h_k)
               +a^B_{20}I_2(h_k)+a^B_{02}\rho_k^2,\\
 E_k={}&a^c_{01}\rho_k+a^B_{11}I_1(h_k)\rho_k,\\
 M_{k,-}={}&C_k-E_k,\qquad M_{k,+}=C_k+E_k,\\
 T_k={}&\sum_{a+b\le3}\Gamma^c_{ab}I_a(h_k)I_b(\rho_k)
       +\sum_{a+b=4}\Gamma^B_{ab}I_a(h_k)I_b(\rho_k).
\end{aligned}
\tag{23.10}
$$

The sums in $T_k$ start at zero and use the same total-degree index
order as (23.6). These are finite rational intervals, rather than
values sampled on a source curve.

**Lemma 23.3 (Exact full-cover inequalities).** All centres in (23.2)
have $\mathsf A_b(r_k,B_k,p_c)>0$. Every box (23.3) has
$9/50<b<2/5$ and $|s_k|<1$. All reciprocal intervals required by
Definition 23.2 exclude zero. The following bounds hold for every
$k=0,\ldots,1024$:

| Quantity | Strict rational lower bound |
| --- | --- |
| $L_k^2(-\sup M_{k,-})$ | $8320373/10^6$ |
| $L_k^2\inf M_{k,+}$ | $5821464/10^6$ |
| $\inf T_k$ | $2116359/10^6$ |
| $-\sup[\Lambda]^B_{00}$ | $339826/10^6$ |
| $\inf[a_e]^B_{00}$ | $2044101/10^6$ |

Proof. Everything in (23.1)–(23.10) is a specified finite rational
operation on the literal source and response expressions. The exact
minima of the five rows, expressed with common denominator $Q=2^{160}$,
are as follows. The indicated cell attains the minimum.

| Row | Numerator over $2^{160}$ | Cell |
| --- | --- | --- |
| 1 | $12160239971240186012442353144366841006796797116416$ | $0$ |
| 2 | $8508080265624263313479882100477696345820060712960$ | $179$ |
| 3 | $3098612030278324696207250656204127958232465657116$ | $1022$ |
| 4 | $496656485984516568382283235967063096523709429208$ | $346$ |
| 5 | $2987458269499582605778749472455129366078518427980$ | $176$ |

The five rows require checking $5\cdot1025=5125$ cell
inequalities. Each displayed numerator divided by $2^{160}$ is
strictly greater than the bound in its row; multiplication by the
positive integer $10^6 2^{160}$ verifies the comparisons without
rounding a decimal value. Equations (23.1)–(23.9), followed by the
minimum over the stated integer index range, specify every entry
needed to reproduce the table.

For the separate tube-coordinate bounds, the exact extrema of
$B_k-|s_k|h_k-\rho_k$, $B_k+|s_k|h_k+\rho_k$, and $|s_k|$ are

$$
 \min_k(B_k-|s_k|h_k-\rho_k)
       =\frac{314145799935647}{1688849860263936}>\frac9{50},\\
 \max_k(B_k+|s_k|h_k+\rho_k)
       =\frac{432115358175887}{1125899906842624}<\frac25,\\
 \max_k|s_k|=\frac{59505603867}{68719476736}<1.
\tag{23.11}
$$

Before defining any slope, the 1,025 exact rational centre evaluations
satisfy

$$
 \mathsf A_b(r_k,B_k,p_c)>2238298/10^6>2;
\tag{23.12}
$$

the minimum occurs at cell $173$. Thus all slope denominators are
positive independently of the box construction. These comparisons
use only (23.1), the midpoint $B_k$, and the polynomial derivative
of (23.8).

There is no hidden reciprocal premise in the interval calculation.
On every box, $0\le r\le1$, $b>9/50$, $q\ge0$, and therefore
$b,j,n,T,U$ are positive. The fourth row bounds $\Lambda$ away
from zero with negative sign; the fifth bounds $a_e$ away from
zero with positive sign. The remaining divisions are by explicit
positive rational constants. These are exactly the denominators
in (22.5)–(22.6) and (23.4), including the ones used by the
coefficient reciprocal recurrence. ∎

**Lemma 23.4 (Analytic bridge from the certificate to every upper world).**
For every $p\in K$ and $0<r<1$,

$$
 \frac{\partial\Theta_+}{\partial r}(r,p)
       >\frac{2116359}{10^6}>2.
\tag{23.13}
$$

Proof. First justify the enclosure method. The normalized product
rule is (23.6). Differentiating $ff^{-1}=1$ gives (23.7), inductively
in total degree, whenever the constant interval excludes zero.
Consequently the centre arrays enclose the corresponding normalized
derivatives at $(t,e)=(0,0)$ for every $p\in K$, and the box arrays
enclose them at every point of the entire box. This follows by
induction through the rational expressions, because all denominators
are nonzero by Lemma 23.3. Truncating at total degree five loses no
coefficient used to obtain the degree-four derivatives of $\Gamma$.

For fixed $p$ and $\sigma\in\{-1,1\}$, apply the first-order Taylor
formula with second-order integral remainder to
$a(t,\sigma\rho_k,p)$ along the segment from $(0,0)$ to
$(t,\sigma\rho_k)$. The remainder is a weighted average, with
nonnegative weight of total mass one, of

$$
 a_{20}(zt,z\sigma\rho_k,p)t^2
 +a_{11}(zt,z\sigma\rho_k,p)t\sigma\rho_k
 +a_{02}(zt,z\sigma\rho_k,p)\rho_k^2,
 \qquad 0\le z\le1.
$$

Here $a_{ij}$ denotes the normalized derivative, not a coefficient
of the original polynomial. The segment stays in the box, so
(23.10) encloses the full face value. The first two rows of
Lemma 23.3 therefore give, uniformly in $t$ and $p$,

$$
 a(t,-\rho_k,p)<0<a(t,\rho_k,p).
\tag{23.14}
$$

The fifth row gives $a_e>2$ on the whole box. For every fixed $t,p$,
continuity and (23.14) supply a unique root between these faces.
By (23.11) its $b$ is greater than $9/50>1/6$; for strict
$r=r_k+t$, Lemma 22.2 and Theorem 18.4 identify it with the
original $b_+(r,p)$. Thus every original upper source lies in
one of the tubes. No untested projected root has been promoted
to a source.

Apply the third-order Taylor formula to $\Gamma$ on the segment
from $(0,0)$ to $(t,e)$. The fourth-order remainder is a weighted
average, again with nonnegative weight of total mass one, of
$\sum_{a+b=4}\Gamma_{ab}(zt,ze,p)t^ae^b$.
The centre coefficients through degree three and the box
coefficients of degree four therefore enclose $\Gamma$ in $T_k$.
Lemma 23.3 gives $\Gamma>2116359/10^6$ at every point of the
box, including every root supplied by (23.14).

Finally, for fixed $p$, the simple root is a smooth function by
Theorem 18.4. Along it, $e=e(t)$ satisfies
$e'(t)=-a_t/a_e$ and $r=r_k+t$ has derivative one. Hence
$d\theta/d r=\theta_t-\theta_ea_t/a_e=\Gamma$.
In original coordinates this identity is also

$$
 \Gamma=(\vartheta_r+s_k\vartheta_b)
       -\vartheta_b\frac{\mathsf A_r+s_k\mathsf A_b}{\mathsf A_b}
       =\vartheta_r-\vartheta_b\frac{\mathsf A_r}{\mathsf A_b}.
\tag{23.15}
$$

Thus the affine slope cancels correctly; it does not introduce a
modified branch derivative. On the source, Definition 22.3 identifies
$\theta$ with $\Theta_+$. This proves (23.13) on all of $(0,1)$.
The endpoints $r=0,1$ used to close the interval cover are only
auxiliary points for rational enclosures and Taylor segments.
Neither is admitted as an original world. ∎

## 24. Strict upper order and exclusion in every entire acquired child

**Theorem 24.1 (Upper-branch joint-response injectivity).** For every
$p\in K$ and $0<r<s<1$,

$$
 \Theta_+(s,p)-\Theta_+(r,p)
       >\frac{2116359}{10^6}(s-r)>2(s-r)>0.
\tag{24.1}
$$

Consequently, for every $r,s\in(0,1)$,

$$
 u_+(r,p)=u_+(s,p),\quad m_+(r,p)=m_+(s,p)
       \quad\Longrightarrow\quad r=s.
\tag{24.2}
$$

Proof. The mean value theorem on $[r,s]\subset(0,1)$ and Lemma
23.4 give (24.1). If both actual responses were equal at two
parameters, both arguments of $\Psi$ in (22.1) would be equal,
and hence their $\Theta_+$ values would be equal. For unequal
parameters, order them and apply (24.1), obtaining a contradiction.
This proves (24.2). The proof is uniform in $K$, and therefore
applies to the original exact $p_J$ without replacing it by $p_c$. ∎

**Theorem 24.2 (No terminal-M pair in any entire actual child).**
At the original exact algebraic $p_J$, for every real $v$, the
actual function $f_{MM}$ is injective on
$\mathcal C_v=\mathcal F(H_4,M,p_J,M,v)$.

Proof. Theorem 19.4 identifies this entire child with the full
$\mathcal D_v$ of (19.4). Suppose two of its members have the
same terminal-M response. Opposite branch labels are impossible
by Corollary 20.5. If both labels are lower, Theorem 21.5 gives
equal $r$. If both labels are upper, Theorem 24.1 gives equal $r$,
since $p_J\in K$ and both acquired responses are $v$.
In either same-label case, Theorem 19.2 identifies the complete
worlds. These cases exhaust the two global labels at every strict
source, proving injectivity. Empty and singleton children satisfy
the same conclusion.

Equivalently, Corollary 21.6 leaves precisely the upper equations
in (21.21), and (24.2) contradicts their required $r\ne s$.
The exhaustive transport retains every lower-degree gain, sampled
zero, repeated gain root and zero drift allowed by the original
model. The upper regular chart excluded no actual upper source;
any singular lower sources are included by the zero-safe supplier
and Theorem 21.5. No bound on the original positive offdiagonal
coordinates, additional response, reset, copy, or different gain
or drift within one world has been introduced. ∎

**Corollary 24.3 (Exclusion of the unchanged simultaneous-pair predicate).**
There is no real $v$ for which the same entire actual
$\mathcal C_v$ contains both a distinct terminal-J pair and a
distinct terminal-M pair, with the original history and exact $p_J$.

Proof. Theorem 19.4 transports the predicate exactly to (19.6),
and Corollary 21.6 transports its residual form exactly to
(21.21). Theorem 24.2 excludes its required distinct terminal-M
pair for every real $v$. Therefore the conjunction is false.
This argument imposes no label restriction on the terminal-J
pair and no disjointness requirement between the two pairs.
It does not require injectivity of $f_{MJ}$ or decide the other
fifth-response or ancestor questions. ∎

## 追加锚（本行以下为增补区）

## 25. A strict separator and every sampled-odd-root endpoint

**Definition 25.1 (Full-parent collision coordinates).** In Sections
25–27, [O](https://github.com/the-omega-institute/trureturing/blob/30b5f1199c1c6c6b5f38a5b06a4d264176f119ed/docs/develop/theory/FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md)
denotes *FIB common-parent geometry and two exact mixed children*;
its numbered statements are ordinary mathematical premises with their
stated domains. Retain exactly O, Definitions 1.1–1.3:

$$
\begin{gathered}
W=(P(r,b),g,d),\qquad
P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},\\
0<r<1,\quad b>0,\quad 0\ne g\in\mathbb R[s],\quad\deg g\le3,
\quad d\in\mathbb R,\\
H_4=(0,J,24,M,147/5,J,24,M,18),\\
j=b+r(1-r)/b,\quad n=j+r,\quad T=1+b,\quad U=1+2b,\quad V=U+n.
\end{gathered}
\tag{25.1}
$$

Each world has one whole gain and one fixed drift, at the original
clocks $0,\ldots,7$, with $Q_i=E_iQ_{i-1}$ and
$y_i=d+g(i)\operatorname{tr}(Q_iP)$. Define, on the entire parent,

$$
\begin{gathered}
p=d+Vg(5),\qquad u=d+(2U+n)g(6),\qquad
m=d+(3U+2n)g(7),\\
k=m-\frac{32}{5}u,\qquad \epsilon=d-24,\qquad\Delta=b-1/8,\\
h(s)=\frac85(s-1)(s-3)(s-5),\qquad
A_r=(P(r,1/8),h,24),\qquad
\mathcal K=\{A_r:0<r<1\}.
\end{gathered}
\tag{25.2}
$$

Here $(p,u,m)$ are the three actual responses along the fixed
continuation $M,M,M$. Thus two distinct worlds in the entire actual
child $\mathcal F(H_4,M,p,M,v)$ collide at terminal M exactly when
they have equal $(p,u,m)$, with $u=v$. The set $\mathcal K$ is O's
saturated family, and its reflected collisions are already given
by O (16.3), (16.13) and Theorem 16.5.

**Theorem 25.2 (Strict drift/separator barrier on the entire p24 fibre).**
Every world $W\in\mathcal F(H_4,M,24)\setminus\mathcal K$ satisfies

$$
(d-24)\left(k+\frac{1128}{5}\right)<0.
\tag{25.3}
$$

Proof. Use the exhaustive whole-world union in O, Theorem 13.2,
including its set-theoretic treatment of intersections. Outside
$\mathcal K$ it gives $H(r,b)=0$ and

$$
\begin{gathered}
g=h+\epsilon v,\qquad
\epsilon E_2=-\frac{24}{5}\Delta,\qquad E_2=1+Tv(2),\\
v(2)=\frac15-\frac3{4j}-\frac1{2n}+\frac1{20V},\\
v(6)=1-\frac9{4j}+\frac5{2n}-\frac9{4V},\qquad
v(7)=\frac{16}{5}-\frac7j+\frac7n-\frac{21}{5V}.
\end{gathered}
\tag{25.4}
$$

The sextic $H$ is precisely the polynomial in Section 2 above,
or equivalently O (12.2). Define

$$
\mathcal B=32E_2-\frac{27}{5}
 +(3U+2n)v(7)-\frac{32}{5}(2U+n)v(6).
\tag{25.5}
$$

Substituting the same entire gain in both responses gives the identity

$$
 k+\frac{1128}{5}
 =\epsilon\mathcal B
 -32\left(\epsilon E_2+\frac{24}{5}\Delta\right)
 =\epsilon\mathcal B.
\tag{25.6}
$$

Clearing the positive source denominators yields

$$
\mathcal B=\frac{\Pi(r,b)}{5b^3jnV},
\tag{25.7}
$$

where

$$
\begin{aligned}
\Pi(r,b)={}&-73b^6+26(17r-25)b^5
 -4(88r^2-55r+54)b^4\\
&-r(868r^2-1427r+717)b^3\\
&-2r(1-r)(279r^2-334r+108)b^2\\
&+2r^2(1-r)^2(172r+7)b+171r^3(1-r)^3.
\end{aligned}
\tag{25.8}
$$

The following exact polynomial comparison proves the sign on the
whole strict graph, rather than on a restricted source rectangle.
Put

$$
q=r(1-r)(1+2r/3),\qquad B_i(r)=r^i(1-r)^{12-i}.
$$

The polynomial identities are

$$
\begin{aligned}
-729H(r,q)&=r^3(1-r)^3\sum_{i=0}^{12}h_iB_i(r),\\
-729\Pi(r,q)&=r^3(1-r)^3\sum_{i=0}^{12}a_iB_i(r),
\end{aligned}
\tag{25.9}
$$

with coefficient vectors, in increasing $i$,

$$
\begin{aligned}
(h_i)={}&(1458,16767,91125,352755,1199691,3480003,7585857,\\
&\qquad11454855,11415867,7094914,2479206,390402,17388),\\
(a_i)={}&(22599,416745,3333960,15317586,44859501,87549363,\\
&\qquad115352262,101744139,58815129,22240780,6205974,\\
&\qquad1513755,188271).
\end{aligned}
\tag{25.10}
$$

For completeness these finite identities mean direct expansion in
$\mathbb Q[r]$: substitute the displayed $q$ into (25.8) and the
Section 2 polynomial $H$, and compare powers of $r$ with the two
sums in (25.9). Thus their specifications involve only the stated
polynomials and integer arithmetic. Every listed coefficient is
strictly positive. Hence $H(r,q)<0$ and $\Pi(r,q)<0$ for $0<r<1$.

O (13.7) proves that $H(r,b)/b^2$ is strictly increasing in $b>0$
and has its unique zero at $B_H(r)$. Consequently $B_H(r)>q$.
The coefficients of $b^6,b^5,b^4,b^3,b^2$ in $\Pi$ are strictly
negative. For the three quadratics in these coefficients the
respective discriminants are

$$
-15983,\qquad-453095,\qquad-8972,
$$

and their leading coefficients are positive. The coefficient of
$b^5$ is negative because $17r-25<0$. The constant coefficient
of $\Pi$ is positive. It follows by differentiating $\Pi/b$ that

$$
\partial_b(\Pi(r,b)/b)<0\qquad(b>0).
\tag{25.11}
$$

Indeed each of its positive-degree terms has a negative
coefficient, its constant term has derivative zero, and the
positive coefficient of $b^{-1}$ has a negative derivative.
Therefore

$$
\frac{\Pi(r,B_H(r))}{B_H(r)}
 <\frac{\Pi(r,q)}q<0.
$$

All denominator factors in (25.7) are positive, so
$\mathcal B<0$ on this whole graph. Finally O, Theorem 2.2,
gives $\epsilon\ne0$ outside $\mathcal K$. Multiplying (25.6)
by $\epsilon$ proves (25.3), since $\epsilon^2\mathcal B<0$.
This proof uses the complete union of O, Theorem 13.2, including
singular sources and every allowed polynomial degree or root
multiplicity; it never divides by a gain sample or the drift. ∎

**Theorem 25.3 (Exhaustion of collisions touching a sampled odd root).**
Let $p,v\in\mathbb R$, and let distinct complete worlds
$W,W'\in\mathcal F(H_4,M,p,M,v)$ have the same terminal-M
response. If either endpoint satisfies $d=24$ or
$g(1)g(3)=0$, then, for some $r\ne t$,

$$
 W=A_r,\qquad W'=A_t,\qquad
 r+t=9/8,\qquad 1/8<r,t<1,\qquad p=24.
\tag{25.12}
$$

Conversely all these legal reflected pairs are collisions.

Proof. Either odd gain sample being zero forces $d=24$ from
its original response 24; its trace is $j>0$ or $n>0$.
O, Theorem 2.2, then places that endpoint in $\mathcal K$.
A $\mathcal K$ world has $p=24$ and $k=-1128/5$ by O (16.13).
Its partner has the same $u,m$, hence the same $k$. Theorem 25.2
excludes every partner outside $\mathcal K$.

On $\mathcal K$, the inherited response formulas are

$$
\begin{gathered}
n(r)=1/8+9r-8r^2,\qquad p=24,\\
u=84+24n(r),\qquad m=312+\frac{768}{5}n(r),\\
n(r)-n(t)=(r-t)\{9-8(r+t)\}.
\end{gathered}
\tag{25.13}
$$

Equality of $u$ and distinctness force $r+t=9/8$; strict source
legality gives $1/8<r,t<1$. Conversely these equations give equal
$p,u,m$. The complete triples are different because $r\ne t$.
Thus this is exhaustion of endpoints in the stated stratum, for
all real $p,v$, rather than a global classification of the
remaining collision correspondence. ∎

## 26. Equal projective M-trace ratios

**Definition 26.1 (Unobserved ratio and exceptional quartic).** On
the entire parent put

$$
\chi(W)=\frac{n}{U}>0,\qquad
\mathfrak p(x)=8x^4+29x^3+18x^2-15x-6.
\tag{26.1}
$$

The ratio is a source coordinate used to partition pairs of
worlds; it is not an acquired reading. At clocks $3,4,5,6,7$
the five actual M-continuation traces are

$$
 U\,(\chi,1,\chi+1,\chi+2,2\chi+3).
\tag{26.2}
$$

Let $\alpha$ denote the unique positive root of $\mathfrak p$.
Existence follows from its negative constant and positive leading
coefficient, and uniqueness follows from the single sign change
in its descending coefficient sequence, by Descartes' rule.
Use the exact rational endpoints

$$
\ell=\frac{62587023180336296158875989932560022}{10^{35}},
\qquad h_\alpha=\ell+10^{-35}.
\tag{26.3}
$$

**Definition 26.2 (Exceptional source polynomials and rational rules).**
For variables $x,z$ define the following polynomials, in this order:

$$
\begin{aligned}
c_x&=x^2+x-1,\\
D&=(1-x)^2+(2x-1)(1-x)z+c_xz^2,\\
B_*&=z(1-x),\qquad R_*=z\{x(1-x)+c_xz\},\\
T_*&=D+B_*,\qquad U_*=D+2B_*,\\
J_*&=xU_*-R_*,\qquad N_*=xU_*,\\
L_{\rm num}&=T_*U_*J_*N_*+6DU_*J_*N_*+DT_*J_*N_*\\
&\qquad-4DT_*U_*(J_*+N_*),\\
L&=L_{\rm num}/(2U_*).
\end{aligned}
\tag{26.4}
$$

The last division is exact in $\mathbb Q[x,z]$. Define further

$$
\begin{aligned}
q_0(x)&=-\frac{45x^3+89x^2-32x-40}{x(x+1)(x+2)},\\
d_x(z)&=24-\frac{3x(8B_*-D)(3U_*-T_*)J_*}{5L},\\
K_x(z)&=d_x(z)\{q_0(x)-U_*/D\},\\
\mathcal M(x,z)&=5(x+1)(x+2)L^2\partial_zK_x(z).
\end{aligned}
\tag{26.5}
$$

Cancellation in the last expression gives a polynomial in
$\mathbb Q[x,z]$. The degrees of $L$ in $(z,x)$ are $(6,8)$,
and those of $\mathcal M$ are $(10,17)$.

For any polynomial $A(x,z)$ of $z$-degree at most $N$, define
its degree-$N$ Bernstein coefficients by

$$
\beta_{k,N}(A)(x)=\sum_{i=0}^k
 [z^i]A(x,z)\frac{\binom{k}{i}}{\binom{N}{i}},\qquad0\le k\le N.
\tag{26.6}
$$

Thus $A(x,z)=\sum_k\beta_{k,N}(A)(x)\binom Nkz^k(1-z)^{N-k}$.
To evaluate a polynomial $\beta(x)=\sum_{i=0}^s b_ix^i$ on
$I_\alpha=[\ell,h_\alpha]$, set $I_{s+1}=[0,0]$ and, for
$i=s,s-1,\ldots,0$, set

$$
I_i=I_\alpha I_{i+1}+[b_i,b_i].
\tag{26.7}
$$

All coefficients, including missing zero coefficients, enter this
recursion after expansion in $\mathbb Q[x]$. Interval sums add
endpoints and interval products take the minimum and maximum of
the four endpoint products. Let $\operatorname{up}(\beta)$ be
the upper endpoint of $I_0$. Polynomial divisions in (26.4)–(26.5)
are exact divisions performed before coefficient extraction or
interval evaluation. No reduction modulo $\mathfrak p$ is part
of these definitions.

**Theorem 26.3 (Entire exceptional source fibre and strict invariant).**
At $x=\alpha$, the formulas

$$
 b=B_*/D,\qquad r=R_*/D,\qquad0<z<1
\tag{26.8}
$$

parametrize exactly all strict positive sources with $n/U=x$,
once each. Every such source has $\Lambda<0$, so has exactly
one complete parent world, with drift $d_x(z)$ and the single
gain reconstructed by O, Theorem 2.1. On the whole interval,

$$
\partial_zK_\alpha(z)<0.
\tag{26.9}
$$

Proof. Rational evaluation of the quartic at (26.3) gives
$\mathfrak p(\ell)<0<\mathfrak p(h_\alpha)$, locating its unique
positive root. These same rational endpoints give

$$
1/2<\ell<\alpha<h_\alpha<2/3,\qquad
\ell^2+\ell-1>0.
\tag{26.10}
$$

In particular all three coefficients of $D$ in (26.4) are positive
at $x=\alpha$. Direct polynomial identities give

$$
\begin{gathered}
D-R_*=(1-x)^2(1-z),\qquad
(J_*-B_*)B_*=R_*(D-R_*),\\
\frac{db}{dz}
 =\frac{(1-x)\{(1-x)^2-c_xz^2\}}{D^2}>0,
\qquad (1-x)^2-c_x=2-3x>0.
\end{gathered}
\tag{26.11}
$$

For $0<z<1$, these identities give $0<r<1$, $b>0$ and
$c=(J_*-B_*)/D=r(1-r)/b>0$, with $j=J_*/D$,
$U=U_*/D$ and $n=N_*/D=xU$. The coordinate $b$ increases
from zero to

$$
b_{\max}=\frac{1-x}{2x-1}>1.
\tag{26.12}
$$

To prove exhaustion, every source of this ratio satisfies

$$
F_b(r)=r^2-(1+b)r+b\{x+(2x-1)b\}=0.
\tag{26.13}
$$

For $0<b<b_{\max}$, $F_b(0)>0$ and $F_b(1)<0$, so this
quadratic has exactly one root in $(0,1)$; its other root is
larger than one. For $b\ge b_{\max}>1$, its derivative is
negative on $[0,1]$ and $F_b(1)\ge0$, so it has no strict
root there. The strictly increasing $b(z)$ and (26.11) therefore
supply every legal source exactly once. The closed chart endpoints
are auxiliary points, not worlds.

Here is a finite rational sign certificate on the full closed
rectangle $I_\alpha\times[0,1]$. Apply (26.6)–(26.7) to the
polynomials defined in (26.4)–(26.5). The resulting strict
comparisons, in increasing $k$, are

$$
\begin{aligned}
\operatorname{up}(\beta_{k,6}(L))&<-a_{L,k}/10^6,\\
\operatorname{up}(\beta_{k,10}(\mathcal M))&<-a_{M,k}/10^6,
\end{aligned}
\tag{26.14}
$$

where the exact integer vectors are

$$
\begin{aligned}
(a_{L,k})={}&(2568,5336,9737,15554,23008,32865,46551),\\
(a_{M,k})={}&(12697,21923,36249,59040,97503,164302,\\
&\qquad278586,466328,759734,1195254,1809568).
\end{aligned}
\tag{26.15}
$$

These comparisons are specified entirely by rational operations:
expand the divisions in (26.4)–(26.5), extract the $z^i$
coefficients, sum them with the binomial fractions (26.6), and
apply the descending recursion (26.7) with (26.3). For example
the right bound in row $k$ is the displayed integer divided by
$10^6$ with a minus sign; no floating-point root or sampled
value enters a comparison. Equations (26.3)–(26.7), (26.14)–(26.15)
are a finite reproducible certificate for all 18 inequalities.
The Bernstein weights are nonnegative and sum to one on $[0,1]$.
Thus (26.14) gives $L<0$ and $\mathcal M<0$ on the entire
closed rectangle.

On every strict source of (26.8), substitution in the original
parent coefficient gives

$$
\Lambda=\frac{L_{\rm num}}{T_*U_*J_*N_*}<0.
\tag{26.16}
$$

Indeed $T_*,U_*,J_*,N_*$ are positive there and
$L_{\rm num}=2U_*L$. Substitution also gives the rational identity

$$
(d_x-24)\Lambda+
 \frac{24}{5}(b-1/8)
 \left(\frac6{1+b}-\frac2{1+2b}\right)=0.
\tag{26.17}
$$

It follows either by clearing the stated positive denominators
in (26.4)–(26.5), or by inserting $L_{\rm num}=2U_*L$.
O, Theorem 2.1, now reconstructs exactly one complete parent
world at each source. In particular the gain is nonzero because
the original responses at clocks zero and one differ.
Finally (26.5) and the strict sign of $\mathcal M$ imply

$$
\partial_zK_x=\frac{\mathcal M}{5(x+1)(x+2)L^2}<0
\quad(x=\alpha),
$$

with a strictly positive denominator. This proves (26.9). ∎

**Theorem 26.4 (Complete equal-ratio collision classification).**
Let $W,W'\in\mathcal F(H_4)$ be any complete worlds. If

$$
\chi(W)=\chi(W'),\qquad
(p,u,m)(W)=(p,u,m)(W'),
\tag{26.18}
$$

then either $W=W'$, or they are a legal distinct reflected pair
$A_r,A_{9/8-r}$ of Theorem 25.3. Conversely every such reflected
pair satisfies (26.18). Hence the map
$W\mapsto(\chi(W),p(W),u(W),m(W))$ has fibres of size at most
two, and every two-point fibre is one of these known mirror pairs.

Proof. Write $x=\chi(W)=\chi(W')$, $H=Ug$,
$H'=U'g'$ and $\delta=d-d'$. Equality of the original readings
at clocks $3,4$ and of the three actual later readings gives

$$
(H-H')(i)=-\delta/f_i,\qquad
(f_3,f_4,f_5,f_6,f_7)=(x,1,x+1,x+2,2x+3).
\tag{26.19}
$$

The fourth difference of the degree-at-most-three polynomial
$H-H'$ vanishes. The reciprocal difference is exactly

$$
\frac1x-4+\frac6{x+1}-\frac4{x+2}+\frac1{2x+3}
 =-\frac{\mathfrak p(x)}{x(x+1)(x+2)(2x+3)}.
\tag{26.20}
$$

All denominator factors are positive. Thus
$\delta\mathfrak p(x)=0$.

First suppose $x\ne\alpha$. Then $\delta=0$, so $H-H'$ has
five distinct zeros and is identically zero. The common
clock-zero equation $g(0)=g'(0)=-d$ now gives
$d(U-U')=0$. At clock two, $T=(U+1)/2$, and the common
response $C=147/5$ gives

$$
 H(2)=\frac{2U(C-d)}{U+1}
     =\frac{2U'(C-d)}{U'+1}.
$$

Consequently $(C-d)(U-U')=0$. Since $C\ne0$, these two
equations force $U=U'$. Therefore $b=b'$, $n=n'$ and
$g=g'$, with $d=d'$. If $r=r'$ these are the identical
complete world. Otherwise $j=n-r\ne n-r'=j'$, and the
clock-one equations force $g(1)=0$, hence $d=24$.
O, Theorem 2.2, gives $b=1/8$, $g=h$. The common-source
quadratic, or (25.13), gives $r+r'=9/8$.

Now suppose $x=\alpha$. Let $q_x$ be the unique cubic with
values $(1/x,1,1/(x+1),1/(x+2))$ at nodes $3,4,5,6$.
Its explicitly reproducible Lagrange formula is

$$
q_x(s)=\sum_{i=3}^6\frac1{f_i}
 \prod_{\substack{3\le j\le6\\j\ne i}}\frac{s-j}{i-j}.
\tag{26.21}
$$

Evaluation gives $q_x(0)=q_0(x)$ of (26.5), and

$$
 q_x(7)-\frac1{2x+3}
 =\frac{\mathfrak p(x)}{x(x+1)(x+2)(2x+3)}=0.
$$

The four nodes $3,4,5,6$ in (26.19) imply the identity of whole
polynomials $H-H'=-\delta q_x$. At clock zero this gives

$$
 d(q_0-U)=d'(q_0-U').
\tag{26.22}
$$

Theorem 26.3 parametrizes both entire sources by $z,z'\in(0,1)$
and gives their unique reconstructed drifts. Thus (26.22) is
$K_\alpha(z)=K_\alpha(z')$. The strict derivative (26.9) forces
$z=z'$. Sources coincide, and the unique full-parent lift in
Theorem 26.3 gives $W=W'$.

Finally (25.13) shows that every legal reflected pair has equal
$p,u,m$ and equal $n$. It also has common $U=5/4$, hence equal
$\chi$. For a fixed world its distinct reflected partner, when
legal, is unique, proving the fibre bound. The proof nowhere
requires a nonzero gain sample, exact degree, simple roots or
nonzero drift. This is classification within an equal unobserved
source ratio, with arbitrary real acquired responses; it supplies
no acquisition of $\chi$ and no assertion about unequal ratios. ∎

## 27. Saturation at the central diagonal limit

**Definition 27.1 (Central world and full-parent local coordinates).**
Give complete worlds the Euclidean coefficient topology of O,
Definition 16.1, padding the gain coefficient vector through degree
three. Set

$$
 r_0=9/16,\qquad W_0=A_{r_0},\qquad k_0=-1128/5.
\tag{27.1}
$$

O, Theorem 2.1 and Lemma 16.2, identify the entire parent near
$W_0$ with the zeros of

$$
\begin{gathered}
R_0(b,r,e)=e\Lambda+\frac{24}{5}(b-1/8)B_{\rm coef},\\
B_{\rm coef}=6/(1+b)-2/(1+2b)>0,\qquad e=d-24.
\end{gathered}
\tag{27.2}
$$

At $e=0,b=1/8$, $\partial_bR_0=448/25$. The ordinary implicit
function theorem therefore gives a smooth chart of all nearby
parent worlds with coordinates $(r,e)$ and dependent coordinate
$b=b(r,e)$. The whole gain in this chart is the single interpolant
of O (2.3), added to $h$. Along $e=0$, (25.13) gives

$$
 p=24,\qquad k=k_0,\qquad
 u=\frac{591}{4}-192(r-9/16)^2.
\tag{27.3}
$$

In particular $(p,u,m)(W_0)=(24,591/4,720)$.

**Theorem 27.2 (Local central-diagonal saturation).** There exists
an open neighbourhood $\mathcal U$ of $W_0$ in the entire complete
parent such that any distinct $W,W'\in\mathcal U$ with equal
$(p,u,m)$ are exactly a legal reflected pair
$A_r,A_{9/8-r}$. In particular their fifth response is 24.
Consequently no sequence of distinct nonmirror terminal-M collision
pairs can converge to $(W_0,W_0)$ in the coefficient topology.

Proof. In the full-parent chart of Definition 27.1, put

$$
\alpha_0(r)=\partial_ep(r,0),\qquad
\eta_0(r)=\partial_ek(r,0).
$$

The derivatives in O, Lemmas 16.3–16.4, computed from the same
whole interpolant, have the exact form

$$
\begin{aligned}
\alpha_0&=a_0+a_1/j,&
a_0&=\frac{-512n^2-218n+475}{42n},&
a_1&=\frac{85(4n+5)}{84},\\
\eta_0&=e_0-c_0/j,&
e_0&=\frac{10240n^2+33924n-32375}{140n},&
c_0&=\frac{1672n+7455}{70},\\
j&=1/8+8r(1-r),&n&=j+r.
\end{aligned}
\tag{27.4}
$$

Here the subscripted $a_0,e_0$ in (27.4) are rational functions
of $n$ and do not denote the drift coordinate $e$. At $r=r_0$,

$$
 j=67/32,\quad n=85/32,\quad j_r=-1,\quad n_r=0,
 \quad\Lambda=12701/3417.
\tag{27.5}
$$

Substitution into (27.4) and differentiation give

$$
\begin{aligned}
\alpha_0(r_0)&=-205402/7973,&
\eta_0(r_0)&=10698679/39865,\\
\alpha_0'(r_0)&=340000/94269,&
\eta_0'(r_0)&=-1218176/31423,\\
\alpha_0\eta_0'-\eta_0\alpha_0'&=49333024/1602573.
\end{aligned}
\tag{27.6}
$$

These fractions can also be recovered directly from (27.2):
$b_e=-25\Lambda/448$, and differentiating the gain at nodes
$0,1,2,3$ gives

$$
 \left(-1,-1/j,-\{1+(24/5)b_e\}/(9/8),-1/n\right).
\tag{27.7}
$$

The extrapolation rows to clocks $5,6,7$ are
$(-4,15,-20,10)$, $(-10,36,-45,20)$ and $(-20,70,-84,35)$,
respectively. Substitution into the actual responses (25.2)
gives (27.4)–(27.6); differentiation of $j,n$ at (27.5) yields
$\alpha_0'=a_1/j^2$ and $\eta_0'=-c_0/j^2$ there.
All these denominators are positive source traces.

Since $p(r,0)=24$ and $k(r,0)=k_0$ throughout this chart,
smooth factorization gives

$$
 p-24=e\,A(r,e),\qquad k-k_0=e\,E(r,e),\qquad
 A(r,0)=\alpha_0(r),\quad E(r,0)=\eta_0(r).
\tag{27.8}
$$

For example $A(r,e)=\int_0^1p_e(r,te)\,dt$, with the
analogous formula for $E$. Thus these functions extend smoothly
through $e=0$; this is not division by a sampled gain zero.
Because $A(r_0,0)\ne0$, the inverse function theorem changes
coordinates locally from $(r,e)$ to $(r,q)$, where $q=p-24$.
Writing $e=e(r,q)$, (27.8) becomes

$$
 k-k_0=q\,L_c(r,q),\qquad
 L_c(r,q)=\frac{E(r,e(r,q))}{A(r,e(r,q))}.
\tag{27.9}
$$

At $q=0$, local uniqueness gives $e(r,0)=0$. Hence the derivative
at the centre is

$$
\partial_rL_c(r_0,0)
 =\frac{\alpha_0\eta_0'-\eta_0\alpha_0'}{\alpha_0^2}
 =\frac{1467657464}{31642486203}>0.
\tag{27.10}
$$

Choose an open product rectangle about $(r_0,0)$ in these
coordinates, small enough that $A\ne0$ and $\partial_rL_c>0$
on it. Its inverse image $\mathcal U$ is open in the entire
parent because the original reconstruction and the coordinate
changes are homeomorphisms.

Two members of $\mathcal U$ having equal $(p,u,m)$ have equal
$q$ and equal $k$. If $q\ne0$, (27.9) gives equal $L_c$ at
that fixed $q$. Its strict increase in $r$ on the rectangle
forces equal $r$, hence equal $e$ and the identical complete
world. If $q=0$, both $e$ values are zero. The parent equation
then forces $b=1/8$, and reconstruction gives $g=h$ and $d=24$.
Equality of $u$ in (27.3) gives

$$
 (r-r')\{9-8(r+r')\}=0.
$$

Distinctness removes $r=r'$, leaving $r'=9/8-r$.
Conversely every such pair lying in $\mathcal U$ has equal
responses by (25.13). This proves the local classification.
If a sequence of nonmirror collision pairs converged to
$(W_0,W_0)$, both endpoints would eventually lie in $\mathcal U$,
contradicting that classification. ∎

## 追加锚（本行以下为增补区）


## 28. A global order on the external H graph at $p=24$

The next theorem uses the ordinary premises O, Definition 13.1 and
Theorem 13.2, together with F, Theorem 25.3. O, Theorem 13.2 is used
with its original positive source domain and its single whole-gain lift;
F, Theorem 25.3 is used only for a collision having a member with
$d=24$. No transitive audit of those supplier proofs is intended here.

**Definition 28.1 (The exhaustive proportional chart).** Put

$$
q=r(1-r),\qquad t=\frac{b}{q},\qquad b=qt,
$$

on $0<r<1$, $b>0$. Define

$$
\begin{aligned}
J_0&=1+qt^2,&N_0&=J_0+rt,&U&=1+2qt,\\
T&=1+qt,&V_0&=N_0+tU,&Z&=J_0N_0V_0.
\end{aligned}
$$

Then

$$
j=\frac{J_0}{t},\qquad n=\frac{N_0}{t},\qquad V=\frac{V_0}{t}.
\tag{28.1}
$$

The change of coordinates is a bijection from the entire strict positive
source domain to $(r,t)\in(0,1)\times(0,\infty)$; its inverse is
$b=r(1-r)t$ and $r(1-r)/b=1/t$.

The polynomial equation for the external branch in these coordinates is

$$
\begin{aligned}
G(r,t)={}&14q^3t^6+(95-73r)q^2t^5+(47r^2-39r+30)qt^4\\
&+r(147r^2-232r+105)t^3\\
&+2(44r^2-55r+15)t^2-64rt-32.
\end{aligned}
\tag{28.2}
$$

Direct expansion gives

$$
H(r,qt)=q^3G(r,t).
\tag{28.3}
$$

For the whole-gain lift set

$$
\delta=8qt-1,
$$

and define

$$
\begin{aligned}
D={}&20Z+T(4Z-15tN_0V_0-10tJ_0V_0+tJ_0N_0),\\
A_6={}&4Z-9tN_0V_0+10tJ_0V_0-9tJ_0N_0,\\
A_7={}&16Z-35tN_0V_0+35tJ_0V_0-21tJ_0N_0,\\
D_0&=24D-12\delta Z,\\
G_6&=24D-3\delta A_6,\\
G_7&=384D-12\delta A_7,\\
S_6&=2tU+N_0,&S_7&=3tU+2N_0.
\end{aligned}
$$

Let $h(s)=\frac85(s-1)(s-3)(s-5)$ and let $v$ be the cubic of O,
Definition 13.1, with values $(-1,-1/j,-1/n,-1/V)$ at the nodes
$0,1,3,5$. On every strict zero of $G$ the complete world supplied by
O, Theorem 13.2, is exactly

$$
\epsilon=-\frac{12\delta Z}{D},\qquad d=24+\epsilon,\qquad
g=h+\epsilon v.
\tag{28.4}
$$

Indeed, O (13.2) gives $E_2=1+Tv(2)$ and direct substitution gives

$$
D=20J_0N_0V_0E_2.
\tag{28.5}
$$

Thus $D\ne0$ on the strict graph by O, Theorem 13.2. The same
substitution gives

$$
v(6)=\frac{A_6}{4Z},\qquad v(7)=\frac{A_7}{5Z},\qquad
g(6)=\frac{G_6}{D},\qquad g(7)=\frac{G_7}{5D}.
\tag{28.6}
$$

The actual sixth-M and seventh-M responses in (25.1)--(25.2) therefore
are

$$
u=\frac{tD_0+S_6G_6}{tD},\qquad
m=\frac{5tD_0+S_7G_7}{5tD}.
\tag{28.7}
$$

Define the integer polynomials

$$
\begin{aligned}
P={}&2(8N_0-19t)D\\
&+\delta\{19tZ+6S_6A_6-S_7A_7\},\qquad B=tD.
\end{aligned}
\tag{28.8}
$$

The cleared numerator identity is

$$
5tD_0+S_7G_7-24(tD_0+S_6G_6)=12P.
	ag{28.9a}
$$

so expansion of (28.7) gives the actual-response identity

$$
m-\frac{24}{5}u=\frac{12}{5}\frac{P}{B}.
\tag{28.9}
$$

No gain sample, drift, leading coefficient, gain root, source label or
unobserved ratio is divided out in (28.4)--(28.9).

**Lemma 28.2 (The graph lies in one derived compact strip).** Every
strict positive root of $G(r,\cdot)$ satisfies

$$
1<t<2.
\tag{28.10}
$$

Proof. In the degree-six Bernstein basis in $r$ the coefficient vectors
of $G(r,1)$ and $G(r,2)$ are respectively

$$
\begin{aligned}
&(-2,-17/2,-343/15,-459/10,-1024/15,-227/3,-68),\\
&(88,640/3,5512/15,302,160/3,4/3,32).
\end{aligned}
\tag{28.11}
$$

The Bernstein weights are nonnegative and sum to one on $0\le r\le1$.
Thus $G(r,1)<0<G(r,2)$ there. O, Theorem 13.2, supplies exactly one
positive root for every strict $r$, so that root lies in $(1,2)$. ∎

**Definition 28.3 (Derivative numerator).** Set

$$
\mathcal A(r,t)=
\frac{(P_rB-PB_r)G_t-(P_tB-PB_t)G_r}{t}.
\tag{28.12}
$$

The numerator in (28.12) is divisible by $t$ in $\mathbb Z[r,t]$;
$\mathcal A$ has bidegree $(19,19)$ and 159 nonzero monomials.

**Lemma 28.4 (Exact tensor-Bernstein certificate).** On the closed
rectangle $R=[0,1]\times[1,2]$, every zero of $G$ satisfies

$$
\mathcal A(r,t)>0.
\tag{28.13}
$$

Proof. For a polynomial $F$ of coordinate degrees at most $(M,N)$ and
a cell $[a,a+h]\times[c,c+k]$, write

$$
F(a+hx,c+ky)=\sum_{i,j}f_{ij}x^iy^j.
$$

Its degree-$(M,N)$ tensor-Bernstein coefficients are

$$
\beta_{IJ}(F)=
\sum_{i\le I,\,j\le J}f_{ij}
\frac{\binom Ii}{\binom Mi}\frac{\binom Jj}{\binom Nj}.
\tag{28.14}
$$

The corresponding tensor Bernstein basis is nonnegative on the cell
and sums to one. Consequently a strict lower bound on all coefficients
is a pointwise strict lower bound for $F$.

Encode a cell by $[i,d,j,e,\mathsf A]$ or $[i,d,j,e,\mathsf G]$,
meaning the closed rectangle

$$
\left[\frac{i}{2^d},\frac{i+1}{2^d}\right]
\times
\left[1+\frac{j}{2^e},1+\frac{j+1}{2^e}\right].
\tag{28.15}
$$

The following are the leaves of the alternating bisection of $R$, first
in $r$ and then in $t$; their interiors are disjoint and their union is
all of $R$:

$$
\begin{array}{rrrr|c@{\qquad}rrrr|c}
0&5&0&5&\mathsf G&0&5&1&5&\mathsf A\\
1&5&0&5&\mathsf G&1&5&1&5&\mathsf A\\
0&4&1&4&\mathsf A&1&4&0&4&\mathsf G\\
1&4&1&4&\mathsf A&0&3&1&3&\mathsf A\\
2&4&0&4&\mathsf G&4&5&2&5&\mathsf G\\
4&5&3&5&\mathsf A&5&5&1&4&\mathsf G\\
3&4&0&3&\mathsf G&1&3&1&3&\mathsf A\\
0&2&1&2&\mathsf A&2&3&0&3&\mathsf A\\
2&3&1&3&\mathsf A&3&3&0&2&\mathsf G\\
1&2&1&2&\mathsf A&0&1&1&1&\mathsf A\\
2&2&0&2&\mathsf G&2&2&1&2&\mathsf A\\
3&2&0&1&\mathsf G&1&1&1&1&\mathsf A
\end{array}
\tag{28.16}
$$

On every $\mathsf A$ cell, use $(M,N)=(19,19)$ in (28.14): all 400
coefficients of $\mathcal A$ are strictly greater than $500$. On every
$\mathsf G$ cell, use $(M,N)=(6,6)$ for $G$: all 49 coefficients of $G$
are at most $-49/512$. There are 14 cells of type $\mathsf A$ and 10
of type $\mathsf G$, hence 5600 and 490 exact rational comparisons.
The exact minima are

$$
\min_{\mathsf A}\beta_{IJ}(\mathcal A)=
\frac{341124130829334753610607074478220625550859}
{680564733841876926926749214863536422912}>500,
\qquad
\min_{\mathsf G}\beta_{IJ}(-G)=\frac{49}{512}.
\tag{28.17}
$$

Thus a zero of $G$ cannot lie in a $\mathsf G$ cell and lies in an
$\mathsf A$ cell, where (28.14) gives $\mathcal A>0$. This proves
(28.13). ∎

**Theorem 28.5 (Strict order on the whole external H graph).** Let
$\mathcal H(r)$ be the complete world in O, Theorem 13.2. For
$0<r<s<1$,

$$
\left[m-\frac{24}{5}u\right](\mathcal H(r))
<
\left[m-\frac{24}{5}u\right](\mathcal H(s)).
\tag{28.18}
$$

Proof. Along the strict graph, (28.3) and O, Theorem 13.2 give
$G_t=H_b/q^2>0$. Implicit differentiation gives
$t'(r)=-G_r/G_t$. From (28.9) and (28.12),

$$
\frac{d}{dr}\left(m-\frac{24}{5}u\right)
=\frac{12}{5}\frac{t\,\mathcal A}{B^2G_t}>0.
\tag{28.19}
$$

Here $t>0$, $B=tD\ne0$ by (28.5), and $\mathcal A>0$ by Lemma
28.4. The mean value theorem on every compact subinterval of $(0,1)$
proves (28.18). Equality of both actual responses on two H worlds
therefore forces equal $r$; O, Theorem 13.2 then forces equal $b$ and
the identical complete gain and drift. ∎

The certificate includes the auxiliary boundaries $r=0$ and $r=1$.
At them,

$$
G(0,t)=30t^2-32,\qquad
G(1,t)=4(5t^3+2t^2-16t-8).
\tag{28.20}
$$

The first has its unique root in $[1,2]$ at $4/\sqrt{15}$; the second
has a unique root there because its derivative is positive on $[1,2]$.
Consequently every sequence of strict graph points approaching either
strict source endpoint has $t$ bounded in the same closed interval,
$b=q t\to0$, and $1/t$ remains finite and positive. These boundary
points are not admitted as worlds. At either of the two O13.2 K/H
intersections, $\delta=0$, so (28.4) reduces to the same exact world
$g=h,d=24$; no intersection is deleted or duplicated.

## 29. The complete original $p=24$ terminal-M classification

**Theorem 29.1 (Joint-response injectivity and the whole-union
classification).** Let $W,W'$ be complete worlds in the original
positive domain of Definition 25.1 with the literal history $H_4$ and
the actual continuation $M,M,M$. Assume both have fifth-M response
$p=24$. If their actual sixth-M and seventh-M responses agree, then
either $W=W'$, or

$$
W=\mathcal K(r),\qquad W'=\mathcal K(s),\qquad
r+s=\frac98,\qquad \frac18<r,s<1,
\qquad r\ne s.
\tag{29.1}
$$

Conversely every pair in (29.1) has equal $(p,u,m)$. Thus every
two-world fibre of the original $(p,u,m)$ map at $p=24$ is exactly one
known legal K mirror pair, and no distinct external H/H pair exists.

Proof. By O, Theorem 13.2, the complete $p=24$ fibre is the set union

$$
\{\mathcal K(r):0<r<1\}\cup\{\mathcal H(r):0<r<1\},
\tag{29.2}
$$

with the two K/H intersections counted once. If neither endpoint of a
distinct matched pair belongs to $\mathcal K$, both lie on the H graph,
and Theorem 28.5 makes equality of $(u,m)$ impossible. If one endpoint
belongs to $\mathcal K$, then its drift is $24$; F, Theorem 25.3,
classifies the distinct pair as a legal K mirror pair. This proves the
only-if direction, including the intersections.

For the converse, O, (16.13), equivalently F, (25.13), gives on
$\mathcal K$

$$
 p=24,\qquad u=84+24n(r),\qquad
m=312+\frac{768}{5}n(r),\qquad
n(r)=\frac18+9r-8r^2,
\tag{29.3}
$$

and

$$
 n(r)-n(s)=(r-s)\{9-8(r+s)\}.
\tag{29.4}
$$

For distinct legal parameters, equality of the responses is therefore
equivalent to $r+s=9/8$. The strict inequalities in (29.1) are exactly
the original source legality for both reflected parameters, and
$r=s=9/16$ is removed by distinctness. ∎

The proof retains the full original scope: $g$ is one nonzero real
polynomial of degree at most three and $d$ is one fixed real drift at
all original clocks; lower degrees, repeated roots, sampled zeros,
zero drift and singular parent cases remain included. The only
divisions made above are by $q,t,Z,D,B,G_t$ on the strict H graph;
$q,t,Z$ are positive, $D\ne0$ is (28.5), $B\ne0$ follows, and
$G_t>0$ is O13.2. No endpoint is added. F24, F26 and F27 retain
their stated exact-$p_J$, equal-$\chi$ and local full-parent scopes;
Theorem 29.1 adds no conclusion for $p\ne24$ or for the general
unequal-$\chi$ correspondence away from this fibre.

## 追加锚（本行以下为增补区）

## 30. Reconstruction over every off-twenty-four acquired base

**Definition 30.1 (The entire actual child).** Retain the complete
worlds, strict source domain and literal history of O, Definitions
1.1–1.3, as recalled in (25.1). Thus

$$
\begin{gathered}
W=(P(r,b),g,d),\qquad
P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},\\
0<r<1,\quad b>0,\quad
0\ne g\in\mathbb R[s],\quad\deg g\le3,\quad d\in\mathbb R,\\
H_4=(0,J,24,M,147/5,J,24,M,18).
\end{gathered}
\tag{30.1}
$$

Here O is [the common-parent volume](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md).
Fix arbitrary real $p\ne24$ and $v$, and write

$$
C(p,v)=\mathcal F(H_4,M,p,M,v).
\tag{30.2}
$$

The products are $Q_0=I$, $Q_i=E_iQ_{i-1}$; at every original clock
$i$, the reading is $d+g(i)\operatorname{tr}(Q_iP)$. The initial
read counts and every atom is immediately read. In particular, the
acquired word through clock six is $J,M,J,M,M,M$, without a reset,
copy, skipped read, clock shift or additional port. Cardinality in
(30.2) counts distinct complete triples, including lower-degree gains,
sampled or repeated roots, zero drift, singular sources and unbounded
positive offdiagonals.

For a world in this child put

$$
\begin{gathered}
j=b+r(1-r)/b,\qquad n=j+r,\qquad
T=1+b,\qquad U=1+2b,\\
x=n/U>0,\qquad H(s)=Ug(s),\qquad C_2=147/5.
\end{gathered}
\tag{30.3}
$$

The letters $x,H$ are mathematical coordinates on worlds, not acquired
observations. For arbitrary $x>0,d\in\mathbb R$ define

$$
h_3=\frac{24-d}{x},\quad h_4=18-d,\quad
h_5=\frac{p-d}{x+1},\quad h_6=\frac{v-d}{x+2},
\tag{30.4}
$$

and let $H$ be their unique degree-at-most-three interpolant at
$3,4,5,6$. Explicitly,

$$
H(s)=\sum_{i=3}^6 h_i
 \prod_{\substack{3\le j\le6\\j\ne i}}\frac{s-j}{i-j}.
\tag{30.5}
$$

Write $H_i=H(i)$ for $i\in\{0,1,2,7\}$. The needed extrapolations are

$$
\begin{aligned}
H_0&=20h_3-45h_4+36h_5-10h_6,\\
H_1&=10h_3-20h_4+15h_5-4h_6,\\
H_2&=4h_3-6h_4+4h_5-h_6,\\
H_7&=-h_3+4h_4-6h_5+4h_6.
\end{aligned}
\tag{30.6}
$$

The interpolation theorem here is the classical distinct-node theorem;
see Berrut–Trefethen, *Barycentric Lagrange Interpolation*, §2,
[(2.1)–(2.2)](https://people.maths.ox.ac.uk/trefethen/barycentric.pdf).
It requires neither exact degree three nor nonzero sampled values.

**Lemma 30.2 (Faithful whole-world reconstruction).** The map
$W\mapsto(x,d)$ from $C(p,v)$ is injective. Its image consists exactly
of the real pairs $x>0,d\ne24$ for which, with (30.4)–(30.6),

$$
\begin{gathered}
B_0=2(C_2-d)-H_2,\qquad H_1\ne0,\qquad d^2+B_0^2>0,\\
U=\frac{-dH_0+B_0H_2}{d^2+B_0^2}>1,\qquad
b=\frac{U-1}{2},\qquad
j=\frac{U(24-d)}{H_1},\qquad r=xU-j,\\
0<r<1,\qquad j=b+\frac{r(1-r)}b,\qquad
dU=-H_0,\qquad B_0U=H_2.
\end{gathered}
\tag{30.7}
$$

The corresponding complete world has the entire polynomial $g=H/U$.

Proof. O, Theorems 2.1–2.2, applied to this exact $H_4$, say that
$d=24$ forces $b=1/8$ and
$g(s)=\frac85(s-1)(s-3)(s-5)$. Its fifth-$M$ response is $24$.
Thus $p\ne24$ implies $d\ne24$. On an actual world, the traces at
clocks zero through six, by O, (1.6)–(1.7), are

$$
1,\quad j,\quad T,\quad n,\quad U,\quad U+n,\quad 2U+n.
\tag{30.8}
$$

Consequently $Ug$ has the four samples (30.4), so is exactly the
whole polynomial (30.5). Clock one gives
$H_1=U(24-d)/j\ne0$. Clocks zero and two give, respectively,
$dU=-H_0$ and $B_0U=H_2$, since $T=(U+1)/2$. The pair
$(d,B_0)$ cannot be $(0,0)$: those equations would give $H_2=0$,
whereas the definition of $B_0$ would give $H_2=2C_2\ne0$.
Taking the scalar product of the two equations with $(d,B_0)$
therefore gives the displayed formula for $U$. All remaining source
coordinates and the entire gain are then forced by (30.7), proving
injectivity.

Conversely suppose all guards in (30.7) hold. They give a strict
source $P(r,b)$, with $n=j+r=xU$ and $T=(U+1)/2$. The last two
equations give readings zero and $C_2$ at clocks zero and two;
the definition of $j$ gives reading $24$ at clock one. Formula
(30.4) gives readings $24,18,p,v$ at clocks three through six.
The gain $H/U$ is one whole polynomial of degree at most three.
It cannot be identically zero, since that would make the first two
readings equal. This proves the converse with every original row,
rather than only an equation on projected coordinates. ∎

The two clock-seven alternatives of this reconstructed world remain
exactly O, (1.7):

$$
f_{MJ}=d+\frac{T+2j+4r}{U}H_7,\qquad
f_{MM}=d+(3+2x)H_7.
\tag{30.9}
$$

They use the same fixed world and original clock seven. The two final
actions are counterfactual alternatives, not two acquired ports.

## 31. A fixed determinant and global noncollapse

**Definition 31.1 (Source-specific polynomial equations).** For the
interpolant above put

$$
D=x(x+1)(x+2),\qquad Z=xH_1-(24-d),
\tag{31.1}
$$

and define

$$
\begin{aligned}
f={}&5D^2(dH_2+H_0B_0),\\
k={}&\frac{D^4}{4}\bigl\{
4H_0^2Z^2+2H_0(d-H_0)ZH_1\\
&\hspace{35mm}-(H_0+d)\bigl(d+(1-2x)H_0\bigr)H_1^2\bigr\}.
\end{aligned}
\tag{31.2}
$$

These are integer polynomials in $x,d,p,v$, with $d$-degrees two
and four. For a denominator-free specification of their coefficients,
set

$$
\begin{gathered}
z_3=(24-d)(x+1)(x+2),\qquad z_4=(18-d)D,\\
z_5=(p-d)x(x+2),\qquad z_6=(v-d)x(x+1),\\
a_0=20z_3-45z_4+36z_5-10z_6,\\
a_1=10z_3-20z_4+15z_5-4z_6,\qquad
a_2=4z_3-6z_4+4z_5-z_6,\\
z_*=xa_1-D(24-d).
\end{gathered}
\tag{31.3}
$$

Then $a_i=DH_i$ for $i=0,1,2$, and

$$
\begin{aligned}
f={}&5dDa_2+a_0\bigl((294-10d)D-5a_2\bigr),\\
4k={}&4a_0^2z_*^2+2a_0(dD-a_0)z_*a_1\\
&\quad-(a_0+dD)\bigl(dD+(1-2x)a_0\bigr)a_1^2.
\end{aligned}
\tag{31.4}
$$

Expansion of the second numerator gives coefficients divisible by four.

Every world of $C(p,v)$ satisfies $f=k=0$. Indeed the two clock
equations of (30.7) imply $dH_2+H_0B_0=0$. The rank-one source
identity, using $n=j+r$, is

$$
r^2-(1+b)r+b(n-b)=0.
\tag{31.5}
$$

For $d\ne0$ substitute $U=-H_0/d$ and $r=UZ/H_1$ into
(31.5). Multiplication by $4d^2H_1^2$ gives exactly the braces in
(31.2). If $d=0$, the actual clock-zero equation gives $H_0=0$,
so those same braces vanish directly. Thus zero drift is retained.
The converse $f=k=0\Rightarrow W\in C(p,v)$ is not asserted;
actual points must satisfy the full guards (30.7).

**Lemma 31.2 (Exact determinant identities).** Let $\mathsf S(x,p,v)$
be the fixed six by six coefficient matrix with rows

$$
d^3f,\ d^2f,\ df,\ f,\ dk,\ k
\quad\hbox{and columns }d^5,d^4,\ldots,1.
\tag{31.6}
$$

This is the degree-$(2,4)$ Sylvester matrix, retained with its
original size under every specialization. Define

$$
F_0=405x^3+(975-18p+5v)x^2+(90-36p+5v)x-480.
\tag{31.7}
$$

There is a uniquely specified $R\in\mathbb Z[x,p,v]$ such that

$$
\det\mathsf S=16D^8F_0^2R,\qquad
(\deg_xR,\deg_pR,\deg_vR)=(18,6,6).
\tag{31.8}
$$

Writing $c_i(p,v)=[x^i]R$, and

$$
A=32p-5v-366,\qquad
B=120p^2-38pv-3360p+3v^2+522v+23112,
\tag{31.9}
$$

one has

$$
c_0=10^6A^2B^2.
\tag{31.10}
$$

The leading $d$-coefficients $L_f=[d^2]f$ and $L_k=[d^4]k$
depend on $x$ alone and have degrees six and fourteen. For the
following certificates let $\operatorname{pp}$ mean clearing rational
denominators and taking the primitive integer polynomial with positive
leading coefficient. Set

$$
\begin{aligned}
u_i(p)&=\operatorname{pp}\!\left(c_i\left(p,\frac{32p-366}{5}\right)\right),\\
w_i(p)&=\operatorname{pp}\!\left(\operatorname{Res}_v(B,c_i)\right),
\qquad i=2,3.
\end{aligned}
\tag{31.11}
$$

Their exact degrees and their complete descending coefficient arrays
modulo $101$ are as follows. In each row the final entry is the
resultant of the two listed reduced polynomials, in the listed order.

| Polynomial pair and variable | Degrees | First coefficient array modulo $101$ | Second coefficient array modulo $101$ | Resultant modulo $101$ |
| --- | --- | --- | --- | --- |
| $\operatorname{pp}(L_f),\operatorname{pp}(L_k)$ in $x$ | $6,14$ | $(76,17,37,66,78,95,59)$ | $(81,20,0,22,71,53,30,80,19,54,96,98,75,95,85)$ | $87$ |
| $u_2,u_3$ in $p$ | $6,6$ | $(45,81,4,6,45,69,87)$ | $(21,68,8,27,37,84,77)$ | $71$ |
| $w_2,w_3$ in $p$ | $12,12$ | $(48,72,7,55,13,92,8,79,92,51,8,14,66)$ | $(62,22,14,67,84,83,15,61,76,5,83,19,52)$ | $86$ |

Proof. All identities are integer polynomial identities obtained from
the four linear forms (31.3). More explicitly, form the six rows
(31.6) using (31.4), expand their determinant, and divide by
$16x^8(x+1)^8(x+2)^8F_0^2$. The remainder is zero; the quotient has
512 nonzero monomials and coordinate degrees $(18,6,6)$, and its
constant $x$-coefficient factors as (31.10). This division fixes every
coefficient of $R$, including its normalization. Extracting
$[d^2]f,[d^4]k,[x^2]R,[x^3]R$ then gives the table by the operations
in (31.11). For example the first leading coefficient is

$$
L_f=-10\bigl(177x^6+724x^5+542x^4-742x^3-629x^2+196x+160\bigr).
\tag{31.12}
$$

The leading entries of all reduced arrays are nonzero, so the stated
degrees are preserved modulo $101$. Evaluating their Sylvester
determinants over $\mathbb F_{101}$ gives $87,71,86$, respectively.
Thus the displayed finite coefficient identities also prove that the
three integer resultants are nonzero. The Sylvester construction over
a commutative coefficient ring is the classical one; see Moreno Maza,
*[The resultant](https://www.csd.uwo.ca/~mmorenom/AM583/Lectures/ResultantGcd.html/node3.html)*,
Definition 4 and Propositions 5–7. Here it is used for these specified
polynomials, with no converse to a specialized resultant-zero test. ∎

**Lemma 31.3 (No vertical collapse and no base collapse).** For every
complex $\alpha$, $L_f(\alpha)$ and $L_k(\alpha)$ do not both vanish.
For every complex pair $(p,v)$, the specialization $R(x,p,v)$ is a
nonzero polynomial in $x$.

Proof. The first row of the table proves the first assertion: a common
complex root would force the nonzero integer resultant to vanish.
Consequently at every fixed $x=\alpha$ and every base $(p,v)$ at
least one of $f(\alpha,d,p,v),k(\alpha,d,p,v)$ has its full degree
two or four. In particular they are never both zero polynomials in $d$.

For the second assertion suppose $R(x,p,v)\equiv0$. Then
$c_0=c_2=c_3=0$. Equation (31.10) forces $A=0$ or $B=0$.
If $A=0$, then $v=(32p-366)/5$, so $u_2(p)=u_3(p)=0$,
contrary to the second nonzero resultant in the table. If $B=0$,
the common finite $v$-root of $B,c_i$ forces
$\operatorname{Res}_v(B,c_i)(p)=0$ for $i=2,3$.
This implication holds even if a leading $v$-coefficient specializes
to zero: its finite-root evaluation vector is in the kernel of the
fixed Sylvester matrix. Thus $w_2(p)=w_3(p)=0$, contrary to the
third nonzero resultant. Both alternatives are impossible. ∎

## 32. The twenty-four-world bound on the entire original child

**Theorem 32.1 (Uniform full-domain off-twenty-four finite fibre).**
For every real $p\ne24$ and every real $v$,

$$
\left|C(p,v)\right|
=\left|\mathcal F(H_4,M,p,M,v)\right|\le24.
\tag{32.1}
$$

This counts distinct complete worlds over the entire strict domain
(30.1), including the singular parent sources.

Proof. Fix the actual base $(p,v)$. Lemma 30.2 injects its complete
worlds into the real solutions $(x,d)$ of $f=k=0$ with $x>0$.
Lemma 31.3 implies that over any fixed complex $x=\alpha$ at
least one of these two polynomials in $d$ is nonzero of degree two
or four. There are therefore at most four distinct common finite
$d$-roots above $\alpha$.

Let $n_\alpha$ count these distinct common roots. Each root $t$
gives the null vector

$$
(t^5,t^4,t^3,t^2,t,1)^{\mathsf T}
\tag{32.2}
$$

of $\mathsf S(\alpha,p,v)$. Since $n_\alpha\le4<6$, the
Vandermonde determinant shows that these vectors are independent.
Hence the corank is at least $n_\alpha$. Constant invertible row
and column operations put $\mathsf S(\alpha,p,v)$ in rank normal
form. In the transformed polynomial matrix at least $n_\alpha$
columns have every entry divisible by $x-\alpha$. Multilinearity
of the determinant gives

$$
n_\alpha\le\operatorname{ord}_{x=\alpha}\det\mathsf S(x,p,v).
\tag{32.3}
$$

This is the same classical determinant-order argument used in the
proof of Theorem 10.2; its application here uses (31.8) and the
global noncollapse of Lemma 31.3, rather than that theorem's
restricted-$p$ hypotheses.

For $D(\alpha)\ne0$, (31.8) turns (32.3) into

$$
n_\alpha\le
\operatorname{ord}_{x=\alpha}\bigl(F_0(x,p,v)^2R(x,p,v)\bigr).
\tag{32.4}
$$

The polynomial on the right is nonzero: $F_0$ has leading
coefficient $405$ and $R$ is nonzero by Lemma 31.3. Its degree
is at most $2\cdot3+18=24$. Every common root with $D\ne0$
projects to a root of that polynomial, and summing (32.4) over its
finitely many roots bounds the number of distinct common pairs
$(x,d)$ with $D\ne0$ by $24$. Legal worlds have $x>0$, hence
$D>0$, and the injection proves (32.1). ∎

This proof retains every specialization of the acquired base. A drop
in either $d$-degree is harmless because the matrix (31.6) keeps
its fixed size and Lemma 31.3 prevents a whole vertical line of
solutions. Multiple projected roots and several distinct drifts over
one projected root are counted by (32.3). No division by $d$ or
$\Lambda$ occurs in the reconstruction, and the necessary equation
$k=0$ at $d=0$ was proved separately. No simplicity of a gain root,
nonzero gain sample, exact gain degree, bounded source coordinate
or regular source chart is assumed. The zeros of $F_0R$ are only
necessary projections; their reality, strictness and whole-world
lifting still require (30.7). Determinant multiplicity is used to
bound distinct points, not to manufacture additional worlds.

## 33. The same-base distinct-pair question

**Definition 33.1 (The two actual distinct-pair images).** On the
original real base domain $\{(p,v):p\ne24\}$ define

$$
\begin{aligned}
D_J=\{(p,v):{}&\exists W,W'\in C(p,v),\quad
 W\ne W',\ f_{MJ}(W)=f_{MJ}(W')\},\\
D_M=\{(p,v):{}&\exists W,W'\in C(p,v),\quad
 W\ne W',\ f_{MM}(W)=f_{MM}(W')\}.
\end{aligned}
\tag{33.1}
$$

At each fixed base Theorem 32.1 bounds the number of ordered
distinct candidate pairs for either terminal action by $24\cdot23=552$.
The original joint condition is exactly $(p,v)\in D_J\cap D_M$:
the two pairs may overlap or be disjoint, and need not have the same
terminal response. Theorem 32.1 neither supplies a point of this
intersection nor excludes all such points. Its base domain is still
the whole infinite real set $p\ne24,v\in\mathbb R$.

Theorem 7.1 remains the $49$-world bound on its stated interval
$\mathcal P$, and Theorem 10.2 remains the $18$-world bound on its
regular locus. Theorems 24.2–24.3 concern the inherited exact $p_J$;
Theorem 29.1 concerns $p=24$. Their quantified scopes are unchanged.
The extension (32.1) uses a whole-world reconstruction and global
noncollapse specific to (30.1); its interpolation, Sylvester
determinants and determinant-order counting are the classical tools
cited in Sections 30–32.

In the notation of O, Definitions 1.2–1.3 and Theorem 17.1, the
bound alone gives no $L_1$ child. Even a point of $D_J\cap D_M$
would supply only the sixth-$M$ $L_1$ child at that one acquired
base. A sixth-$J$ $L_1$ child at the same fifth response $p$, the
remaining fifth-$J$ conditions and the ancestor conditions would
still be required for the corresponding $H_4$ $L_3$, root $L_7$
or eight-versus-nine conclusion.

## 追加锚（本行以下为增补区）
