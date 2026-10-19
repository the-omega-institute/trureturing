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
