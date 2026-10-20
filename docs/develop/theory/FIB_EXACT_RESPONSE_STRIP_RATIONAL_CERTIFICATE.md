# FIB exact response strip: rational certificate

## 1. Purpose, inputs and notation

This companion supplies the exact finite proof data for
[FIB exact response strip and exclusion of joint collisions](FIB_EXACT_RESPONSE_STRIP_AND_JOINT_COLLISION_EXCLUSION.md),
called the **strip volume**. Its root bounds, source enclosures and
output inequalities are mathematical proof data for all real
parameters in a closed rectangle. No sampling conclusion is used.

The polynomials $D_m,N_p,N_u,N_m,\mathsf A,\mathsf B$ are exactly
strip (3.6); the rational functions are
$\pi=N_p/D_m$, $\upsilon=N_u/D_m$, $\omega=N_m/D_m$.
The eliminant $R=\sum c_{ijk}r^ip^jv^k$ is the integer table of
Definition 24.1 in the
[owning volume](https://github.com/the-omega-institute/trureturing/blob/3185602855df9c3f79f19ae165404ef1885777c3/docs/develop/theory/FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md).
The table has 668 entries, with coordinate degrees $(18,7,7)$.
These specified coefficients, not another resultant normalization,
are the input to Section 2.

Throughout,

$$
p_c=\frac{2744214237392974691433531179656369993836520133001835}{10^{50}},
\quad h_p=10^{-40},\quad K=[p_c-h_p,p_c+h_p].
\tag{1.1}
$$

All interval endpoints and all displayed decimal powers are exact
rational numbers. Indices for source branches start at zero.

## 2. Tensor Bernstein bounds and the complete finite subdivision

**Definition 2.1 (Initial coefficients).** Set $d=10^{50}$ and
$n=dp_c$. Define the exact power and tensor Bernstein coefficients by

$$
\begin{aligned}
A_{i\ell}
 &=\sum_{j\ge0,\,k\ge\ell}c_{ijk}p_c^j
       \binom{k}{\ell}142^{k-\ell}8^\ell,\\
\beta_{st}
 &=\sum_{i\le s,\,\ell\le t}A_{i\ell}
       \frac{\binom{s}{i}}{\binom{18}{i}}
       \frac{\binom{t}{\ell}}{\binom7\ell},
\quad 0\le s\le18,\quad0\le t\le7.
\end{aligned}
\tag{2.1}
$$

In the first sum, $i$ is fixed, $j\ge0$, and $k\ge\ell$; absent
$c_{ijk}$ are zero. Thus $\beta$ represents
$R(r,p_c,142+8u)$ on $0\le r,u\le1$.

Put

$$
\begin{aligned}
D_0&=d^7\operatorname{lcm}_{0\le i\le18}\binom{18}{i}
                  \operatorname{lcm}_{0\le k\le7}\binom7k,\\
e&=h_p\sum_{i,j,k:\,j>0}|c_{ijk}|j
             (|p_c|+h_p)^{j-1}150^k,\\
e_*&=\lceil D_0e\rceil/D_0.
\end{aligned}
\tag{2.2}
$$

The exact sum satisfies $e<10^{-9}$. A true tensor coefficient
at any $p\in K$ is within $e_*$ of its coefficient at $p_c$.

Proof. The degree-18 Bernstein coefficients of $r^i$ on $[0,1]$
lie between zero and one. The degree-7 coefficients of $v^k$ on
$[142,150]$ lie between zero and $150^k$: expand
$(142+8u)^k$ and use the nonnegative degree-elevation coefficients.
The mean value bound for $p^j$ gives (2.2) coefficient by coefficient.
Formula (2.1) is the power-to-Bernstein identity applied in both
variables. Multiplication by $D_0$ makes every initial coefficient
an integer. The stated inequality is the finite rational inequality
given by the explicit sum, with the owning table as its full input. ∎

**Definition 2.2 (Subdivision and tests).** For a Bernstein vector
$a_0,\ldots,a_N$, let
$a_j^{(0)}=a_j$ and $a_j^{(k+1)}=(a_j^{(k)}+a_{j+1}^{(k)})/2$.
Its left half has coefficients $a_0^{(k)}$ in order $k=0,\ldots,N$;
its right half has coefficients $a_{N-k}^{(k)}$ in reverse order.
Apply this positive de Casteljau operation to rows for subdivision
in $v$ and to columns for subdivision in $r$.
The error radius remains $e_*$ because every new coefficient is
a convex combination. Equivalently, integer subdivision multiplies
all numerators and the common denominator by $2^N$.

On a given $r,v$ rectangle, let $\gamma_{st}$ be its coefficients
at $p_c$, as obtained by these subdivisions. Assign a row sign

$$
\sigma_s=
\begin{cases}
+1&\min_t\gamma_{st}>e_*,\\
-1&\max_t\gamma_{st}<-e_*,\\
?&\text{otherwise}.
\end{cases}
\tag{2.3}
$$

Let $\mathcal V$ be the maximum number of sign changes among
sequences replacing each question mark by either $+1$ or $-1$.
For an entirely finite definition, start with scores zero for the
allowed signs in row zero and use
$d_{s+1}(q)=\max_t(d_s(t)+{\bf1}_{q\ne t})$ over allowed signs.
Then $\mathcal V=\max_qd_{18}(q)$.

Declare the derivative sign $\mu$ to be $+1$ if all
$\gamma_{s+1,t}-\gamma_{st}>2e_*$, $-1$ if all these differences
are less than $-2e_*$, and zero otherwise.
The endpoint signs are $\sigma_0,\sigma_{18}$ when strict.

For each $v$ interval of Section 3, restrict the initial tensor
to that interval by dyadic subdivisions. Form the binary $r$ tree
starting at $[0,1]$, with the following rules in this order:

1. Discard a node if $\mathcal V=0$, or if its strict endpoint
   signs agree and either $\mathcal V=1$ or $\mu\ne0$.
2. Retain it without further subdivision if $\mu\ne0$ and its
   strict endpoint signs are opposite.
3. Otherwise bisect in $r$, except that at depth twelve retain
   the node.

Collect the retained nodes in increasing $r$ order and join adjacent
ones into maximal closed intervals. On each such joined interval
the finite tests require the same nonzero $\mu$ on all its nodes
and opposite strict signs at its two outer endpoints.
All quantities in this tree are defined by rational recurrences;
there is no unspecified choice of a subdivision or precision.

**Lemma 2.3 (Meaning of the tests).** A discarded interval has no
root, including its endpoints. Each joined interval passing the
last tests has exactly one root, simple, for every parameter in
its closed parameter rectangle.

Proof. For a fixed $p,v$, the true univariate Bernstein coefficient
in row $s$ belongs to
$[\min_t\gamma_{st}-e_*,\max_t\gamma_{st}+e_*]$.
Its sign variation after zero deletion is at most $\mathcal V$.
The substitution $r=(a+bt)/(1+t)$ turns the Bernstein coefficients
on $[a,b]$ into coefficients multiplied by positive binomial
factors; Descartes' rule therefore bounds the number of interior
roots, counting multiplicity, by $\mathcal V$.
If the strict endpoint signs agree, the root count has even parity.
Consequently $\mathcal V\le1$ excludes roots in that case.
For $\mathcal V=0$, all rows have the same strict sign, so endpoints
are excluded as well.

The derivative's Bernstein coefficients are
$18(\gamma_{s+1,t}-\gamma_{st})/(b-a)$, with error at most
$36e_* /(b-a)$. Thus $\mu$ certifies strict monotonicity.
The same sign on adjacent nodes gives strict monotonicity on their
joined interval. Opposite nonzero endpoint signs give exactly one
root by the intermediate value theorem; its nonzero derivative
makes it simple. This also proves the other discard rule. ∎

## 3. Twenty closed projected-root covers

**Proposition 3.1 (Finite root certificate).** Applying Definition 2.2
gives exactly the six joined intervals in each row below, in
increasing order. Their endpoint signs are respectively
$(-,+),(+,-),(-,+),(+,-),(-,+),(+,-)$, and their derivative signs
are respectively $+,-,+,-,+,-$. Every complementary tree node is
discarded by the stated tests. The parameter intervals meet in
endpoints and cover $[142,150]$.

| $v$ interval | $I_0$ | $I_1$ | $I_2$ | $I_3$ | $I_4$ | $I_5$ |
| --- | --- | --- | --- | --- | --- | --- |
| $[142,569/4]$ | $[1/4,9/32]$ | $[5/16,3/8]$ | $[853/1024,3429/4096]$ | $[109/128,55/64]$ | $[111/128,7/8]$ | $[57/64,29/32]$ |
| $[569/4,285/2]$ | $[1/4,9/32]$ | $[5/16,3/8]$ | $[53/64,107/128]$ | $[27/32,55/64]$ | $[111/128,7/8]$ | $[57/64,29/32]$ |
| $[285/2,143]$ | $[1/4,9/32]$ | $[5/16,3/8]$ | $[3363/4096,3397/4096]$ | $[3445/4096,3477/4096]$ | $[111/128,7/8]$ | $[57/64,29/32]$ |
| $[143,287/2]$ | $[1/4,9/32]$ | $[5/16,3/8]$ | $[1665/2048,841/1024]$ | $[1707/2048,1723/2048]$ | $[55/64,7/8]$ | $[57/64,29/32]$ |
| $[287/2,144]$ | $[1/4,9/32]$ | $[5/16,3/8]$ | $[103/128,3331/4096]$ | $[3383/4096,3415/4096]$ | $[55/64,7/8]$ | $[57/64,29/32]$ |
| $[144,289/2]$ | $[1135/4096,1155/4096]$ | $[11/32,3/8]$ | $[1631/2048,3297/4096]$ | $[3351/4096,423/512]$ | $[55/64,7/8]$ | $[57/64,29/32]$ |
| $[289/2,145]$ | $[1/4,5/16]$ | $[11/32,3/8]$ | $[25/32,51/64]$ | $[1659/2048,419/512]$ | $[55/64,7/8]$ | $[57/64,29/32]$ |
| $[145,291/2]$ | $[1/4,5/16]$ | $[11/32,3/8]$ | $[399/512,3229/4096]$ | $[821/1024,3319/4096]$ | $[27/32,7/8]$ | $[57/64,29/32]$ |
| $[291/2,146]$ | $[1/4,5/16]$ | $[189/512,773/2048]$ | $[3157/4096,3193/4096]$ | $[3249/4096,3285/4096]$ | $[27/32,7/8]$ | $[57/64,29/32]$ |
| $[146,293/2]$ | $[1/4,5/16]$ | $[3/8,1/2]$ | $[195/256,1579/2048]$ | $[25/32,13/16]$ | $[27/32,7/8]$ | $[57/64,29/32]$ |
| $[293/2,147]$ | $[1/4,5/16]$ | $[3/8,1/2]$ | $[3083/4096,3121/4096]$ | $[397/512,1607/2048]$ | $[27/32,7/8]$ | $[57/64,29/32]$ |
| $[147,295/2]$ | $[1/4,5/16]$ | $[3/8,1/2]$ | $[1523/2048,771/1024]$ | $[49/64,25/32]$ | $[27/32,7/8]$ | $[57/64,29/32]$ |
| $[295/2,148]$ | $[1273/4096,81/256]$ | $[3/8,1/2]$ | $[3007/4096,3047/4096]$ | $[387/512,1569/2048]$ | $[27/32,7/8]$ | $[57/64,29/32]$ |
| $[148,297/2]$ | $[5/16,11/32]$ | $[3/8,1/2]$ | $[23/32,47/64]$ | $[3053/4096,3097/4096]$ | $[27/32,7/8]$ | $[57/64,29/32]$ |
| $[297/2,595/4]$ | $[5/16,11/32]$ | $[3/8,1/2]$ | $[23/32,93/128]$ | $[3031/4096,1527/2048]$ | $[27/32,7/8]$ | $[57/64,29/32]$ |
| $[595/4,149]$ | $[5/16,11/32]$ | $[3/8,1/2]$ | $[2927/4096,2949/4096]$ | $[47/64,3/4]$ | $[13/16,7/8]$ | $[57/64,29/32]$ |
| $[149,597/4]$ | $[5/16,11/32]$ | $[1773/4096,1797/4096]$ | $[11/16,23/32]$ | $[373/512,3009/4096]$ | $[13/16,7/8]$ | $[57/64,29/32]$ |
| $[597/4,299/2]$ | $[1/4,3/8]$ | $[7/16,1/2]$ | $[45/64,91/128]$ | $[2959/4096,2985/4096]$ | $[13/16,7/8]$ | $[57/64,29/32]$ |
| $[299/2,599/4]$ | $[1/4,3/8]$ | $[7/16,1/2]$ | $[2865/4096,2887/4096]$ | $[2933/4096,185/256]$ | $[13/16,7/8]$ | $[57/64,29/32]$ |
| $[599/4,150]$ | $[1/4,3/8]$ | $[7/16,1/2]$ | $[2843/4096,1433/2048]$ | $[1453/2048,1467/2048]$ | $[13/16,7/8]$ | $[57/64,29/32]$ |

Proof. Substitution of the 668 specified integers into (2.1)–(2.3),
followed by the depth-twelve rational tree, gives the listed interval
endpoints. Each strict comparison is precisely one of (2.3), a
derivative difference comparison, or an endpoint comparison in
Definition 2.2; thus the table specifies both the input and the
finite test for every sign. Lemma 2.3 proves the root assertions.
No point on a discarded interval or on an outer endpoint is a root.
This proves exactly six simple roots for every $p\in K$ and every
$v$ in each closed interval. ∎

## 4. Exact interval arithmetic for the affine certificates

**Definition 4.1 (Outward arithmetic).** Use the fixed scale $S=10^{60}$.
The enclosure of an exact rational interval $[a,b]$ is
$[\lfloor Sa\rfloor/S,\lceil Sb\rceil/S]$.
Addition and subtraction use endpoints. Multiplication takes the
minimum and maximum of the four endpoint products and rounds them
outward to this grid. Reciprocation, only on an interval excluding
zero, encloses $[1/u,1/l]$ outward for input $[l,u]$.
For an interval $I$, write $|I|_{\max}$ for the larger absolute
endpoint. Rational constants entering an interval calculation use
the same outward enclosure.

For value and derivative enclosures use pairs
$(a,(a_r,a_b))$ and the exact differentiation rules

$$
\begin{aligned}
(a,\nabla a)+(b,\nabla b)&=(a+b,\nabla a+\nabla b),\\
(a,\nabla a)(b,\nabla b)&=(ab,b\nabla a+a\nabla b),\\
(a,\nabla a)^{-1}&=(a^{-1},((-\nabla a)\,a^{-1})a^{-1}).
\end{aligned}
\tag{4.1}
$$

All operations on the right use the interval operations just defined.
Products displayed as three factors are evaluated from left to right.
Coordinates have derivative vectors $(1,0),(0,1)$; constants have
zero derivative. These sum, product and reciprocal rules enclose
both the values and derivatives of each expression throughout its
input rectangle.

**Definition 4.2 (Centered polynomial evaluation).** For any of the
four polynomials $Q=D_m,N_p,N_u,N_m$, write
$Q(r,b)=\sum q_{ij}r^ib^j$. For a rational center $m$ define

$$
\widetilde Q(X,Y)=\sum_{a,b\ge0}
\left(\sum_{i\ge a,j\ge b}
q_{ij}\binom ia\binom jb m_r^{i-a}m_b^{j-b}\right)X^aY^b.
\tag{4.2}
$$

Coefficients in (4.2) are exact rationals before insertion into the
interval operations. Evaluate by nested Horner evaluation, decreasing
the $r$ power in the outer recurrence and the $b$ power in the inner
one, padding with zero coefficients up to degrees six and seven.
Leading zero padding does not change these operations.
This specifies the evaluation order, including its derivative version
(4.1), on both a singleton center and a nontrivial rectangle.

## 5. From each rational record to its finite inequalities

**Definition 5.1 (Record scales and cells).** In Section 6 a row
labeled $t:i$ specifies branch $i$ of cell $t$, with

$$
m=10^{-38}(M_r,M_b),\qquad
C=10^{-30}\begin{pmatrix}A_{00}&A_{01}\\A_{10}&A_{11}\end{pmatrix},
\qquad \rho=10^{-24}R_\rho.
\tag{5.1}
$$

All seven entries in the row are integers.
The 190 closed cells are exactly

$$
V_t=
\begin{cases}
[142+t/20,142+(t+1)/20],&0\le t<130,\\
[297/2+(t-130)/40,297/2+(t-129)/40],&130\le t<190.
\end{cases}
\tag{5.2}
$$

Their midpoints and radii are $v_c,h_v$. Here $A_{ij}$ are the
integer table entries, whereas $C_{ij}=10^{-30}A_{ij}$ are the actual
matrix coefficients. Write $L=(C_{01},C_{11})^{\mathsf T}$ and
$w_r=|L_0|h_v+\rho$, $w_b=|L_1|h_v+\rho$.
The whole source rectangle is
$\mathcal B=m+[-w_r,w_r]\times[-w_b,w_b]$.

**Definition 5.2 (Preconditioned centered numerators).** Use (4.2) and set

$$
\begin{aligned}
h_i&=C_{i0}(\widetilde N_p-p_c\widetilde D_m)
     +C_{i1}(\widetilde N_u-v_c\widetilde D_m),\quad i=0,1,\\
\bar w&=10^{-30}
 \left\lfloor10^{30}\frac{N_m(m)}{D_m(m)}\right\rfloor,\qquad
h_w=\widetilde N_m-\bar w\widetilde D_m.
\end{aligned}
\tag{5.3}
$$

Form these polynomial coefficients exactly, before interval insertion.
Evaluate $\widetilde D_m,h_0,h_1,h_w$ by (4.1)–(4.2), first at
$X=Y=0$ and then on $[-w_r,w_r]\times[-w_b,w_b]$.
Only after excluding zero in the denominator form

$$
\mathfrak H_i=h_i/\widetilde D_m,\qquad
\mathfrak W=h_w/\widetilde D_m+\bar w.
\tag{5.4}
$$

A superscript zero denotes their singleton-center enclosures.
Their derivatives enclose those of
$H=C((\pi,\upsilon)^{\mathsf T}-(p_c,v_c)^{\mathsf T})$
and $\omega$; centering changes neither function.

Define the following rational upper bounds and intervals from those
value and derivative enclosures:

$$
\begin{aligned}
\mathfrak E_{ij}&=\delta_{ij}-\partial_j\mathfrak H_i,\\
\widehat q&=\max_i\sum_j|\mathfrak E_{ij}|_{\max},\\
\widehat\eta_i
 &=|\mathfrak H_i^0|_{\max}
   +h_v\left|\sum_j\mathfrak E_{ij}L_j\right|_{\max}
   +|C_{i0}|h_p,\\
\widehat\theta&=\widehat q+\max_i\widehat\eta_i/\rho,\\
\mathfrak a&=\sum_j(\partial_j\mathfrak W^0)L_j,\\
\widehat e
 &=\rho\sum_j|\partial_j\mathfrak W|_{\max}
 +h_v\left|\sum_j(\partial_j\mathfrak W-\partial_j\mathfrak W^0)L_j
           \right|_{\max},\\
d_i&=|L_0|-\frac{\widehat q}{1-\widehat q}\|L\|_\infty.
\end{aligned}
\tag{5.5}
$$

The symbol $d_i$ here is a derivative-sign margin for branch $i$,
not a world's drift. All sums, quotients and absolute values outside
interval expressions in (5.5) are exact rational operations.
For two records in the same cell form, by the interval operations,

$$
\mathfrak G_{ij}
 =\mathfrak W_j^0-\mathfrak W_i^0
  +(\mathfrak a_j-\mathfrak a_i)[-h_v,h_v]
  +[-\widehat e_i-\widehat e_j,\widehat e_i+\widehat e_j],
\quad \ell_{ij}=\inf\mathfrak G_{ij}.
\tag{5.6}
$$

This retains the shared sixth-response displacement.
It encloses the difference at the same actual $(p,v)$ by strip
Lemma 7.2.

**Proposition 5.3 (All guards and strict inequalities).** Every
record of Sections 6 and 7 has $\rho>0$, $\det C\ne0$,
$0<r<1$ throughout its rectangle, and nonzero interval enclosures
for $D_m,b,T,U,j,n,\Lambda$. The latter are evaluated in this order:
$c=r(1-r)/b$, $j=b+c$, $n=j+r$, $T=1+b$, $U=1+2b$, then
$\Lambda=1+6/T+1/U-4/j-4/n$, with Definition 4.1.
The $r$ rectangles of each cell are strictly ordered, and $b$ is
positive on branches zero through three, negative on branches four
and five. Moreover $\widehat q<9/20$, $\widehat\theta<1$.
On each positive branch $d_i>0$, with $L_0>0$ for branches zero
and one and $L_0<0$ for branches two and three.

Proof. Substitute the integer rows into (5.1), (4.2), (5.3)–(5.5).
The guard tests are interval exclusions of zero before any division.
The remaining source bounds are direct comparisons of the rational
endpoints $m_j\pm w_j$ and of consecutive $r$ intervals.
The table in Section 6 gives stronger aggregate rational bounds for
the 190 strip cells. The two event cells satisfy the same tests
and the additional endpoint comparisons in Section 7.
Definitions (4.1)–(5.6) specify every coefficient, operation, precision
and comparison; no approximate source root is an input. ∎

## 6. Closed strip cells: bounds and rational source records

**Definition 6.1 (Integer bounds in the first table).** In row $t$,
the first two bound integers strictly exceed $10^{10}$ times,
respectively, $\max_i\widehat q_i$ and
$\max_i\widehat\theta_i$. The third is strictly less than
$10^{10}\min_{0\le i<4}d_i$.
The last three are strictly less than
$10^{10}\ell_{02},10^{10}\ell_{21},10^{10}\ell_{13}$.
They are obtained by rounding upper bounds upward and lower bounds
downward; if a scaled number is an integer the rounding is strict
by one integer unit.

Thus this table states finitely many rational inequalities, all
with the same denominator $10^{10}$. In particular its largest
first and second entries are $4444246042,9982728179$;
the minima in its last three columns are
$69947968847,144190706814,1614405690$.

| $t$ | upper $10^{10}\widehat q$ | upper $10^{10}\widehat\theta$ | lower $10^{10}d$ | lower $10^{10}\ell_{02}$ | lower $10^{10}\ell_{21}$ | lower $10^{10}\ell_{13}$ |
| --- | --- | --- | --- | --- | --- | --- |
| 0 | $1407480966$ | $7572960422$ | $75620193$ | $101803394418$ | $144190706814$ | $10857034876$ |
| 1 | $1368738568$ | $7506271990$ | $75752740$ | $101687587797$ | $145052933843$ | $10782009995$ |
| 2 | $1331738364$ | $7504218485$ | $75886319$ | $101570036351$ | $145917263002$ | $10703776502$ |
| 3 | $1334654683$ | $7514556903$ | $76020939$ | $101450767328$ | $146783658452$ | $10622723292$ |
| 4 | $1340470203$ | $7525008668$ | $76156605$ | $101329807357$ | $147652084976$ | $10539201741$ |
| 5 | $1346351706$ | $7535575491$ | $76293323$ | $101207182450$ | $148522507977$ | $10453529572$ |
| 6 | $1352300225$ | $7546259118$ | $76431103$ | $101082918011$ | $149394893468$ | $10365993769$ |
| 7 | $1358316814$ | $7557061332$ | $76569949$ | $100957038842$ | $150269208073$ | $10276854261$ |
| 8 | $1364402552$ | $7567983952$ | $76709871$ | $100829569152$ | $151145419018$ | $10186347871$ |
| 9 | $1370558539$ | $7579028836$ | $76850875$ | $100700532087$ | $152023493655$ | $10094422482$ |
| 10 | $1376785900$ | $7590197881$ | $76992968$ | $100569950601$ | $152903400320$ | $9991383273$ |
| 11 | $1383085784$ | $7601493026$ | $77136160$ | $100437847727$ | $153785108583$ | $9883142334$ |
| 12 | $1389459367$ | $7612916250$ | $77280457$ | $100304245364$ | $154668588032$ | $9775475916$ |
| 13 | $1395907848$ | $7624469574$ | $77425867$ | $100169164854$ | $155553808833$ | $9668433188$ |
| 14 | $1402432455$ | $7636155064$ | $77572399$ | $100032626988$ | $156440741722$ | $9562058154$ |
| 15 | $1409034442$ | $7647974830$ | $77720062$ | $99894652015$ | $157329357997$ | $9456390105$ |
| 16 | $1415715092$ | $7659931029$ | $77868862$ | $99755259647$ | $158219629516$ | $9351464037$ |
| 17 | $1422475716$ | $7672025866$ | $78018811$ | $99614469065$ | $159111528689$ | $9247311023$ |
| 18 | $1429317655$ | $7684261592$ | $78169915$ | $99472298934$ | $160005028468$ | $9143958554$ |
| 19 | $1436242282$ | $7696640510$ | $78322184$ | $99328600306$ | $160899935252$ | $9041430850$ |
| 20 | $1443250999$ | $7709164974$ | $78475627$ | $99182063254$ | $161794895491$ | $8939749135$ |
| 21 | $1450345241$ | $7721837392$ | $78630253$ | $99034169805$ | $162691348621$ | $8838931905$ |
| 22 | $1457526478$ | $7734660223$ | $78786072$ | $98884937055$ | $163589264610$ | $8738989615$ |
| 23 | $1464796213$ | $7747635986$ | $78943094$ | $98734381615$ | $164488621784$ | $8639938274$ |
| 24 | $1472155983$ | $7760767255$ | $79101328$ | $98582519624$ | $165389399963$ | $8541792785$ |
| 25 | $1479607363$ | $7774056664$ | $79260783$ | $98429366754$ | $166291576177$ | $8444562844$ |
| 26 | $1487151964$ | $7787506905$ | $79421471$ | $98274938218$ | $167195127946$ | $8348256394$ |
| 27 | $1494791436$ | $7801120738$ | $79583402$ | $98119248774$ | $168100033281$ | $8252879776$ |
| 28 | $1502527469$ | $7814900982$ | $79746585$ | $97962312737$ | $169006270666$ | $8158437862$ |
| 29 | $1510361793$ | $7828850525$ | $79911032$ | $97804143980$ | $169913819061$ | $8064934184$ |
| 30 | $1518296179$ | $7842972323$ | $80076753$ | $97644755947$ | $170822657889$ | $7972371045$ |
| 31 | $1526332444$ | $7857269401$ | $80243760$ | $97484161652$ | $171732767033$ | $7880749627$ |
| 32 | $1534472446$ | $7871744858$ | $80412063$ | $97322373694$ | $172644126823$ | $7790070087$ |
| 33 | $1542718093$ | $7886401865$ | $80581675$ | $97159404255$ | $173556718038$ | $7700331645$ |
| 34 | $1551071335$ | $7901243672$ | $80752606$ | $96995265115$ | $174470521891$ | $7611532669$ |
| 35 | $1559534175$ | $7916273607$ | $80924869$ | $96829967650$ | $175385520026$ | $7523670746$ |
| 36 | $1568108665$ | $7931495080$ | $81098475$ | $96663522845$ | $176301694511$ | $7436742751$ |
| 37 | $1576796909$ | $7946911583$ | $81273436$ | $96495941295$ | $177219027832$ | $7350744917$ |
| 38 | $1585601063$ | $7962526696$ | $81449766$ | $96327233215$ | $178137502884$ | $7265672886$ |
| 39 | $1594523340$ | $7978344089$ | $81627476$ | $96157408445$ | $179057102968$ | $7181521767$ |
| 40 | $1603566010$ | $7994367522$ | $81806581$ | $95986476451$ | $179977811780$ | $7098286186$ |
| 41 | $1612731399$ | $8010600851$ | $81987091$ | $95814446339$ | $180899613410$ | $7015960331$ |
| 42 | $1622021897$ | $8027048029$ | $82169022$ | $95641326853$ | $181822492331$ | $6934537994$ |
| 43 | $1631439954$ | $8043713111$ | $82352386$ | $95467126387$ | $182746433396$ | $6854012611$ |
| 44 | $1640988088$ | $8060600255$ | $82537197$ | $95291852986$ | $183671421830$ | $6774377296$ |
| 45 | $1650668879$ | $8077713727$ | $82723469$ | $95115514350$ | $184597443224$ | $6695624877$ |
| 46 | $1660484981$ | $8095057905$ | $82911217$ | $94938117845$ | $185524483531$ | $6617747927$ |
| 47 | $1670439116$ | $8112637279$ | $83100455$ | $94759670503$ | $186452529059$ | $6540738787$ |
| 48 | $1680534080$ | $8130456460$ | $83291197$ | $94580179029$ | $187381566464$ | $6464589600$ |
| 49 | $1690772747$ | $8148520180$ | $83483459$ | $94399649805$ | $188311582746$ | $6389292328$ |
| 50 | $1701158069$ | $8166833298$ | $83677256$ | $94218088897$ | $189242565242$ | $6314838779$ |
| 51 | $1711693078$ | $8185400803$ | $83872603$ | $94035502054$ | $190174501623$ | $6241220624$ |
| 52 | $1722380892$ | $8204227819$ | $84069516$ | $93851894721$ | $191107379885$ | $6168429419$ |
| 53 | $1733224715$ | $8223319611$ | $84268011$ | $93667272035$ | $192041188347$ | $6096456622$ |
| 54 | $1744227844$ | $8242681585$ | $84468105$ | $93481638834$ | $192975915644$ | $6025293606$ |
| 55 | $1755393666$ | $8262319300$ | $84669814$ | $93294999661$ | $193911550722$ | $5954931678$ |
| 56 | $1766725667$ | $8282238467$ | $84873154$ | $93107358765$ | $194848082834$ | $5885359146$ |
| 57 | $1778227432$ | $8302444959$ | $85078144$ | $92918720108$ | $195785501533$ | $5816569573$ |
| 58 | $1789902650$ | $8322944812$ | $85284801$ | $92729087369$ | $196723796670$ | $5748554814$ |
| 59 | $1801755119$ | $8343744236$ | $85493135$ | $92538462728$ | $197662958387$ | $5681306026$ |
| 60 | $1813788748$ | $8364849616$ | $85703166$ | $92346849780$ | $198602977113$ | $5614814356$ |
| 61 | $1826007560$ | $8386267523$ | $85914919$ | $92154252073$ | $199543843560$ | $5549070954$ |
| 62 | $1838415699$ | $8408004716$ | $86128411$ | $91960672185$ | $200485548718$ | $5484066974$ |
| 63 | $1851017434$ | $8430068155$ | $86343662$ | $91766112424$ | $201428083851$ | $5419793588$ |
| 64 | $1863817163$ | $8452465001$ | $86560691$ | $91570574835$ | $202371440491$ | $5356241990$ |
| 65 | $1876819417$ | $8475202629$ | $86779517$ | $91374061202$ | $203315610438$ | $5293403403$ |
| 66 | $1890028866$ | $8498288635$ | $87000162$ | $91176573051$ | $204260585750$ | $5231269085$ |
| 67 | $1903450325$ | $8521730841$ | $87222645$ | $90978111653$ | $205206358744$ | $5169830331$ |
| 68 | $1917088760$ | $8545537308$ | $87446987$ | $90778678022$ | $206152921988$ | $5109078486$ |
| 69 | $1930949290$ | $8569716342$ | $87673209$ | $90578224348$ | $207100219720$ | $5049004940$ |
| 70 | $1945037199$ | $8594276505$ | $87901334$ | $90376593837$ | $208048087695$ | $4989601139$ |
| 71 | $1959357936$ | $8619226625$ | $88131383$ | $90173992120$ | $208996724572$ | $4930858584$ |
| 72 | $1973917129$ | $8644575804$ | $88363378$ | $89970419218$ | $209946123889$ | $4872768835$ |
| 73 | $1988720584$ | $8670333432$ | $88597342$ | $89765874912$ | $210896279416$ | $4815323519$ |
| 74 | $2003774299$ | $8696509196$ | $88833299$ | $89560358741$ | $211847185154$ | $4758514327$ |
| 75 | $2019084469$ | $8723113093$ | $89071272$ | $89353870011$ | $212798835334$ | $4702333016$ |
| 76 | $2034657494$ | $8750155443$ | $89311285$ | $89146407788$ | $213751224412$ | $4646771416$ |
| 77 | $2050499986$ | $8777646899$ | $89553363$ | $88937970907$ | $214704347065$ | $4591821428$ |
| 78 | $2066618783$ | $8805598467$ | $89797530$ | $88728557968$ | $215658198190$ | $4537475027$ |
| 79 | $2083020953$ | $8834021512$ | $90043813$ | $88518167342$ | $216612772898$ | $4483724261$ |
| 80 | $2099713806$ | $8862927779$ | $90292236$ | $88306797167$ | $217568066514$ | $4430561258$ |
| 81 | $2116704905$ | $8892329409$ | $90542827$ | $88094445355$ | $218524073498$ | $4377977143$ |
| 82 | $2134002075$ | $8922238952$ | $90795612$ | $87881109589$ | $219480789458$ | $4325964064$ |
| 83 | $2151613419$ | $8952669387$ | $91050619$ | $87666787326$ | $220438211546$ | $4274515584$ |
| 84 | $2169547323$ | $8983634140$ | $91307875$ | $87451475798$ | $221396335914$ | $4223624143$ |
| 85 | $2187812475$ | $9015147103$ | $91567409$ | $87235172009$ | $222355158913$ | $4173282261$ |
| 86 | $2206417874$ | $9047222654$ | $91829250$ | $87017872741$ | $223314677093$ | $4123482539$ |
| 87 | $2225372849$ | $9079875680$ | $92093428$ | $86799574553$ | $224274887199$ | $4074217656$ |
| 88 | $2244687067$ | $9113121599$ | $92359972$ | $86580273776$ | $225235786171$ | $4025480376$ |
| 89 | $2264370555$ | $9146976382$ | $92628913$ | $86359966522$ | $226197371138$ | $3977263539$ |
| 90 | $2284433715$ | $9181456581$ | $92900283$ | $86138648677$ | $227159639423$ | $3929560069$ |
| 91 | $2304887339$ | $9216579353$ | $93174114$ | $85916315907$ | $228122588533$ | $3882362969$ |
| 92 | $2325742630$ | $9252362489$ | $93450437$ | $85692963651$ | $229086216163$ | $3835665322$ |
| 93 | $2347011220$ | $9288824444$ | $93729287$ | $85468587126$ | $230050520190$ | $3789460291$ |
| 94 | $2368705191$ | $9325984368$ | $94010697$ | $85243181327$ | $231015498677$ | $3743741120$ |
| 95 | $2390837100$ | $9363862138$ | $94294701$ | $85016741020$ | $231981149866$ | $3698501129$ |
| 96 | $2413419995$ | $9402478393$ | $94581334$ | $84789260752$ | $232947472178$ | $3653733720$ |
| 97 | $2436467448$ | $9441854572$ | $94870634$ | $84560734839$ | $233914464213$ | $3609432370$ |
| 98 | $2459993573$ | $9482012952$ | $95162635$ | $84331157373$ | $234882124749$ | $3565590636$ |
| 99 | $2484013060$ | $9522976688$ | $95457375$ | $84100522218$ | $235850452738$ | $3522202150$ |
| 100 | $2508541200$ | $9564769862$ | $95754893$ | $83868823010$ | $236819447309$ | $3479260621$ |
| 101 | $2533593918$ | $9607417522$ | $96055228$ | $83636053153$ | $237789107762$ | $3436759833$ |
| 102 | $2559187805$ | $9650945736$ | $96358418$ | $83402205823$ | $238759433571$ | $3394693644$ |
| 103 | $2585340153$ | $9695381645$ | $96664505$ | $83167273958$ | $239730424382$ | $3353001854$ |
| 104 | $2612068992$ | $9740753513$ | $96973530$ | $82931250267$ | $240702080011$ | $3311725439$ |
| 105 | $2639393131$ | $9787090793$ | $97285534$ | $82694127217$ | $241674400446$ | $3270868598$ |
| 106 | $2667332198$ | $9834424184$ | $97600562$ | $82455897040$ | $242647385843$ | $3230425362$ |
| 107 | $2695906687$ | $9882785701$ | $97918657$ | $82216551726$ | $243621036529$ | $3190389835$ |
| 108 | $2725138001$ | $9932208745$ | $98239863$ | $81976083023$ | $244595352998$ | $3150756195$ |
| 109 | $2755048511$ | $9982728179$ | $98564228$ | $81734482431$ | $245570335914$ | $3111518695$ |
| 110 | $3092065363$ | $8807792881$ | $98891796$ | $81491741203$ | $246545986109$ | $3072671660$ |
| 111 | $3132390884$ | $8860104769$ | $99222618$ | $81247850343$ | $247522304584$ | $3034209485$ |
| 112 | $3173844518$ | $8913882339$ | $99556740$ | $81002800597$ | $248499292507$ | $2996126637$ |
| 113 | $3216473369$ | $8969186068$ | $99894214$ | $80756582456$ | $249476951216$ | $2958417649$ |
| 114 | $3260327171$ | $9026079761$ | $100235090$ | $80509186150$ | $250455282216$ | $2921077125$ |
| 115 | $3305458470$ | $9084630775$ | $100579420$ | $80260601645$ | $251434287181$ | $2884099734$ |
| 116 | $3351922829$ | $9144910273$ | $100927258$ | $80010818637$ | $252413967956$ | $2847480211$ |
| 117 | $3399779037$ | $9206993491$ | $101278657$ | $79759826553$ | $253394326554$ | $2811213356$ |
| 118 | $3449089350$ | $9270960033$ | $101633675$ | $79507614542$ | $254375365160$ | $2775294032$ |
| 119 | $3499919746$ | $9336894188$ | $101992367$ | $79254171471$ | $255357086129$ | $2739717167$ |
| 120 | $3552340206$ | $9404885278$ | $102354792$ | $78999485923$ | $256339326451$ | $2704312208$ |
| 121 | $3606425015$ | $9475028034$ | $102721010$ | $78743546193$ | $257321935219$ | $2668920597$ |
| 122 | $3662253096$ | $9547423009$ | $103091080$ | $78486340272$ | $258305226908$ | $2633849042$ |
| 123 | $3719908376$ | $9622177029$ | $103465067$ | $78227855858$ | $259289201562$ | $2599089702$ |
| 124 | $3779480181$ | $9699403684$ | $103843032$ | $77968080346$ | $260273860709$ | $2564636100$ |
| 125 | $3841063674$ | $9779223868$ | $104225042$ | $77707000814$ | $261259211492$ | $2530487254$ |
| 126 | $3904760333$ | $9861766369$ | $104611164$ | $77444604020$ | $262245257156$ | $2496638159$ |
| 127 | $3970678476$ | $9947168517$ | $105001465$ | $77180876401$ | $263232001113$ | $2463083848$ |
| 128 | $4357005461$ | $9837602745$ | $105396015$ | $76915804060$ | $264219446939$ | $2429819389$ |
| 129 | $4444246042$ | $9940035753$ | $105794886$ | $76649372761$ | $265207598379$ | $2396839887$ |
| 130 | $1481897645$ | $7779719857$ | $111128480$ | $78210467221$ | $266668787288$ | $2508292272$ |
| 131 | $1491199761$ | $7796304420$ | $111348748$ | $78080820977$ | $267163168171$ | $2491389535$ |
| 132 | $1500625769$ | $7813101479$ | $111570280$ | $77950854298$ | $267657727250$ | $2474559360$ |
| 133 | $1510178125$ | $7830115113$ | $111793085$ | $77820565610$ | $268152465103$ | $2457801095$ |
| 134 | $1519859350$ | $7847349501$ | $112017177$ | $77689953322$ | $268647382320$ | $2441114091$ |
| 135 | $1529672033$ | $7864808936$ | $112242565$ | $77559015821$ | $269142479500$ | $2424497699$ |
| 136 | $1539618830$ | $7882497817$ | $112469263$ | $77427751477$ | $269637757257$ | $2407951272$ |
| 137 | $1549702470$ | $7900420663$ | $112697281$ | $77296158643$ | $270133216212$ | $2391474167$ |
| 138 | $1559925757$ | $7918582110$ | $112926633$ | $77164235650$ | $270628857002$ | $2375065740$ |
| 139 | $1570291570$ | $7936986918$ | $113157330$ | $77031980812$ | $271124680273$ | $2358725350$ |
| 140 | $1580802869$ | $7955639975$ | $113389385$ | $76899392420$ | $271620686684$ | $2342452358$ |
| 141 | $1591462694$ | $7974546300$ | $113622810$ | $76766468750$ | $272116876906$ | $2326246125$ |
| 142 | $1602274171$ | $7993711047$ | $113857618$ | $76633208055$ | $272613251622$ | $2310106015$ |
| 143 | $1613240514$ | $8013139513$ | $114093822$ | $76499608569$ | $273109811526$ | $2294031391$ |
| 144 | $1624365027$ | $8032837140$ | $114331435$ | $76365668505$ | $273606557326$ | $2278021620$ |
| 145 | $1635651109$ | $8052809519$ | $114570470$ | $76231386057$ | $274103489741$ | $2262076067$ |
| 146 | $1647102255$ | $8073062400$ | $114810941$ | $76096759395$ | $274600609503$ | $2246194099$ |
| 147 | $1658722062$ | $8093601691$ | $115052861$ | $75961786672$ | $275097917355$ | $2230375086$ |
| 148 | $1670514231$ | $8114433469$ | $115296244$ | $75826466017$ | $275595414056$ | $2214618396$ |
| 149 | $1682482573$ | $8135563983$ | $115541104$ | $75690795539$ | $276093100374$ | $2198923398$ |
| 150 | $1694631009$ | $8156999663$ | $115787455$ | $75554773324$ | $276590977091$ | $2183289463$ |
| 151 | $1706963577$ | $8178747124$ | $116035312$ | $75418397437$ | $277089045004$ | $2167715960$ |
| 152 | $1719484437$ | $8200813171$ | $116284689$ | $75281665921$ | $277587304921$ | $2152202261$ |
| 153 | $1732197875$ | $8223204811$ | $116535600$ | $75144576794$ | $278085757662$ | $2136747737$ |
| 154 | $1745108303$ | $8245929258$ | $116788061$ | $75007128056$ | $278584404064$ | $2121351757$ |
| 155 | $1758220273$ | $8268993939$ | $117042087$ | $74869317679$ | $279083244974$ | $2106013693$ |
| 156 | $1771538473$ | $8292406504$ | $117297694$ | $74731143614$ | $279582281255$ | $2090732915$ |
| 157 | $1785067741$ | $8316174835$ | $117554896$ | $74592603789$ | $280081513781$ | $2075508792$ |
| 158 | $1798813061$ | $8340307051$ | $117813709$ | $74453696107$ | $280580943443$ | $2060340696$ |
| 159 | $1812779579$ | $8364811522$ | $118074150$ | $74314418447$ | $281080571144$ | $2045227995$ |
| 160 | $1826972600$ | $8389696877$ | $118336235$ | $74174768664$ | $281580397801$ | $2030170057$ |
| 161 | $1841397604$ | $8414972011$ | $118599980$ | $74034744587$ | $282080424345$ | $2015166250$ |
| 162 | $1856060243$ | $8440646099$ | $118865401$ | $73894344020$ | $282580651725$ | $2000215941$ |
| 163 | $1870966354$ | $8466728608$ | $119131719$ | $73753510952$ | $283081080899$ | $1985318494$ |
| 164 | $1886121968$ | $8493229303$ | $119398353$ | $73612202784$ | $283581712845$ | $1970473273$ |
| 165 | $1901533311$ | $8520158266$ | $119666693$ | $73470509806$ | $284082548552$ | $1955679641$ |
| 166 | $1917206820$ | $8547525901$ | $119936758$ | $73328429698$ | $284583589025$ | $1940936958$ |
| 167 | $1933149145$ | $8575342957$ | $120208564$ | $73185960111$ | $285084835287$ | $1926244583$ |
| 168 | $1949367163$ | $8603620532$ | $120482130$ | $73043098671$ | $285586288372$ | $1911601872$ |
| 169 | $1965867986$ | $8632370093$ | $120757474$ | $72899842974$ | $286087949334$ | $1897008180$ |
| 170 | $1982658969$ | $8661603493$ | $121034614$ | $72756190589$ | $286589819240$ | $1882462859$ |
| 171 | $1999747724$ | $8691332981$ | $121313568$ | $72612139057$ | $287091899173$ | $1867965259$ |
| 172 | $2017142127$ | $8721571226$ | $121594356$ | $72467685886$ | $287594190234$ | $1853514725$ |
| 173 | $2034850334$ | $8752331329$ | $121876997$ | $72322828559$ | $288096693539$ | $1839110603$ |
| 174 | $2052880791$ | $8783626845$ | $122161510$ | $72177564526$ | $288599410221$ | $1824752232$ |
| 175 | $2071242246$ | $8815471803$ | $122447914$ | $72031891208$ | $289102341431$ | $1810438949$ |
| 176 | $2089943766$ | $8847880723$ | $122736231$ | $71885805994$ | $289605488335$ | $1796170088$ |
| 177 | $2108994746$ | $8880868643$ | $123026479$ | $71739306244$ | $290108852117$ | $1781944978$ |
| 178 | $2128404931$ | $8914451140$ | $123318681$ | $71592389282$ | $290612433979$ | $1767762944$ |
| 179 | $2148184425$ | $8948644351$ | $123612856$ | $71445052404$ | $291116235141$ | $1753623308$ |
| 180 | $2168343714$ | $8983465005$ | $123909026$ | $71297292870$ | $291620256841$ | $1739525385$ |
| 181 | $2188893680$ | $9018930444$ | $124207213$ | $71149107910$ | $292124500334$ | $1725468487$ |
| 182 | $2209845621$ | $9055058657$ | $124507438$ | $71000494717$ | $292628966895$ | $1711451920$ |
| 183 | $2231211270$ | $9091868303$ | $124809724$ | $70851450451$ | $293133657817$ | $1697474985$ |
| 184 | $2253002817$ | $9129378752$ | $125114093$ | $70701972239$ | $293638574412$ | $1683536976$ |
| 185 | $2275232934$ | $9167610110$ | $125420568$ | $70552057169$ | $294143718012$ | $1669637182$ |
| 186 | $2297914791$ | $9206583260$ | $125729172$ | $70401702296$ | $294649089969$ | $1655774884$ |
| 187 | $2321062091$ | $9246319899$ | $126039930$ | $70250904637$ | $295154691653$ | $1641949359$ |
| 188 | $2344689087$ | $9286842576$ | $126352865$ | $70099661173$ | $295660524456$ | $1628159874$ |
| 189 | $2368810617$ | $9328174735$ | $126668001$ | $69947968847$ | $296166589790$ | $1614405690$ |

**Proposition 6.2 (Uniform finite inequalities).** Every row of this
table follows from its six source records by (4.1)–(5.6).
In particular all strip cells satisfy the Banach self-map and
derivative-sign conditions, and all three terminal differences
strictly exceed $6,14,4/25$.

Proof. The upper quantities are $\widehat q,\widehat\theta$ of
(5.5); the lower quantities use the same interval derivatives,
not a different approximation. The displayed integers bound them
strictly as in Definition 6.1. Their comparisons with $9/20$, one,
zero and the three asserted gaps are immediate integer comparisons.
For the function-theoretic implications use strip (5.3)–(5.5),
(7.1)–(7.3), and (8.4). ∎

The following are all source records, using the scales (5.1).
Ten cells are grouped per table solely for readability. Each cell
has exactly the six branch rows zero through five.

### 6.3 Cells 0 through 9

| $t:i$ | $M_r$ | $M_b$ | $A_{00}$ | $A_{01}$ | $A_{10}$ | $A_{11}$ | $R_\rho$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 0:0 | $26074243290723470087303689209471424961$ | $24087465042330663712085232150775982538$ | $-23431154666646384885935483131$ | $8067456798265771276176524546$ | $-11845993215933381818063671356$ | $5509238257698704488590530161$ | $18383559038253693987$ |
| 0:1 | $32044617773545776795918151729620709657$ | $16004351066619402396615036125821290053$ | $-28291022390342890140360580046$ | $12818593910599630182778465130$ | $11686707592981816905408823587$ | $-352892395305614364043261648$ | $4947291437568702816$ |
| 0:2 | $83674902579032117585794116912688250730$ | $28910975994696999270665382314241402875$ | $69369954009759111785065933938$ | $-15716066806235301641276303323$ | $-44199296480556575105475217312$ | $13261889396272374464326417293$ | $25194967223667642164$ |
| 0:3 | $85569562201647168235064644990274806114$ | $14473884922161027209962081227295386353$ | $50196050513050294258917201351$ | $-14581239513272142584967809155$ | $-7515813556303789474118731536$ | $3412693949504916216337631597$ | $57539277100083886720$ |
| 0:4 | $86967855603984552985647442290204937352$ | $-39162837301709344745949325706790572355$ | $744349267218947229849884824$ | $-124539851391961574221756707$ | $5656864617905557458910941023$ | $-931090376612595201203854882$ | $1494608839799047202$ |
| 0:5 | $89230275252664955228943353626063095239$ | $-59679158084877145679137830812215711285$ | $-807944454375634342311247241$ | $215297937446191054971471929$ | $-2074069940384219493224244707$ | $-73173073309800323047833627$ | $5172437270305931$ |
| 1:0 | $26114617809706428247347565393534713959$ | $24115034461419733529803341004663988199$ | $-23475307929310070732168094191$ | $8082369626893923956996481119$ | $-11886725487462179647234181107$ | $5518533600080205217864471817$ | $18436351399652948399$ |
| 1:1 | $32108783999043296045717619964002793332$ | $16002584335066737559458632539058678105$ | $-28319433006578105602042426029$ | $12847931320869446003263014801$ | $11685340188517391783049808975$ | $-353797823192665565075359064$ | $4933319020132879213$ |
| 1:2 | $83596272298072221826443126905790897166$ | $28977262163020258053658664453199418327$ | $69441618268541690456926393078$ | $-15736050935610822820527876232$ | $-44219537955031938184186086552$ | $13252434873201188459468132213$ | $25119669245578228476$ |
| 1:3 | $85496612851032172698985187237419526789$ | $14490812100621738529634877374750918154$ | $50160084948514731057341507242$ | $-14598562251720784105163613621$ | $-7248904727518152855588482157$ | $3358328765810455633588283555$ | $56151629818947839529$ |
| 1:4 | $86967233568287365050739536539518578309$ | $-39167488097011388439132103332217473867$ | $742950975973771478918223141$ | $-124274577667188958047106228$ | $5646582011069088452311770576$ | $-929228724063956156043610776$ | $1497576251383000565$ |
| 1:5 | $89231351456656788294483533192868899136$ | $-59679524024410900606926767680888387535$ | $-807489419973709557277359775$ | $215183676152836749386499193$ | $-2072719843691667276310651928$ | $-73202716813420155536046234$ | $5168439577802378$ |
| 2:0 | $26155067175978468225311648015129410389$ | $24142650421054164809318297950761251730$ | $-23519910560653856526641364040$ | $8097395847660386191775217054$ | $-11927501638472695316004959900$ | $5527854576134038030968240372$ | $18489395278568084855$ |
| 2:1 | $32173097439411340705758865382617643282$ | $16000813112226525420236408296811348388$ | $-28348175517298130575982507474$ | $12877480326696117237578850494$ | $11683887776052711835484101062$ | $-354688947551011049548577782$ | $4919392621250963494$ |
| 2:2 | $83517542014198822488675285137477178640$ | $29043498924236848700638950648616993454$ | $69513426439727631928735958140$ | $-15756068351166010893856533983$ | $-44235553489256450799187166434$ | $13242128830532449095421547010$ | $25041877062692257157$ |
| 2:3 | $85423575963684891900885447775036106168$ | $14507469710968138345350499330243444160$ | $50125053832657566155434817045$ | $-14616254259638720637742182630$ | $-6986224088167914976520824785$ | $3304864276089790635490313798$ | $54820099543665024998$ |
| 2:4 | $86966612856709580314227016363471999375$ | $-39172129598727083263812115791459884970$ | $741557346780743991737429681$ | $-124010202923744078135626736$ | $5636331062853317556628096642$ | $-927372937779574502886544211$ | $1500588323225140932$ |
| 2:5 | $89232427089595027496787550099062338352$ | $-59679890111811850930767509435658930737$ | $-807034820345948471224533565$ | $215069515985831645301466974$ | $-2071371732631225614002450141$ | $-73232220259622104553729228$ | $5164444604904717$ |
| 3:0 | $26195591958519329313988480729113733882$ | $24170313050908035931546464266304014472$ | $-23564964915172316772282172176$ | $8112536270714200866046536902$ | $-11968324403524780000044580086$ | $5537201788422375753098737544$ | $18542694746928924016$ |
| 3:1 | $32237559159682127627643656509955964355$ | $15999037469060470662521921373479692650$ | $-28377255536714024812909734307$ | $12907243757114818649351207416$ | $11682351577530986849847108313$ | $-355565990266413248627226116$ | $4905510799927851454$ |
| 3:2 | $83438711555291483625644717649806048875$ | $29109682054793816811047302031044476045$ | $69585384496288853933195839214$ | $-15776121328024009876048466605$ | $-44247403880540200732518321964$ | $13230984864324156206521851364$ | $24961652938690805253$ |
| 3:3 | $85350449692395128035683268491078800055$ | $14523862220370285182700278257866020422$ | $50090955048024922961635179759$ | $-14634315894427035952272099846$ | $-6727709320335390777185310367$ | $3252285983698490747829487522$ | $53541753028699059677$ |
| 3:4 | $86965993464766874791514516631183632584$ | $-39176761836123470240971593229028147171$ | $740168357653384592763747777$ | $-123746722932842532182011474$ | $5626111635588990663761747518$ | $-925522992071676370249426365$ | $1503645589547808154$ |
| 3:5 | $89233502151984962594734328785308563001$ | $-59680256346380783314832448500503014750$ | $-806580654850565128711699187$ | $214955456808425786800746060$ | $-2070025602854139587603027871$ | $-73261584077668425358418697$ | $5160452354105000$ |
| 4:0 | $26236192730397597970793767986770350788$ | $24198022483672478279167477040179772232$ | $-23610473408460420652727401960$ | $8127791721475920316373569959$ | $-12009196517062297023229311889$ | $5546575841226246061247283415$ | $18596253929577074676$ |
| 4:1 | $32302170239142853278728961435581545782$ | $15997257475428148894316739365087835690$ | $-28406678748472495609740050412$ | $12937224485257420820133879384$ | $11680732797319756313894344630$ | $-356429170314095744114716441$ | $4891672098562681116$ |
| 4:2 | $83359780737864806735688911527622779338$ | $29175807398784779023203026311743573307$ | $69657498459106637765892020943$ | $-15796212136993762454429420232$ | $-44255149521914663247907330052$ | $13219016436283777062553362116$ | $24879058482773741778$ |
| 4:3 | $85277232187980583548333391493392108892$ | $14539994023868356895729393728093432277$ | $50057786601214181443336864398$ | $-14652747587760903406819066782$ | $-6473298526668121558465226389$ | $3200579534143032863024669671$ | $52313845312291127138$ |
| 4:4 | $86965375387996004420230400517477620857$ | $-39181384838339515657764225566108385881$ | $738783986738865876125478003$ | $-123484133491268150204434565$ | $5615923592385006515380722379$ | $-923678861397971930556112641$ | $1506748595382905528$ |
| 4:5 | $89234576644331200270246942332246013553$ | $-59680622727420627151448637773672242433$ | $-806126922847135420376389807$ | $214841498484138225746874513$ | $-2068681450024078486051812950$ | $-73290808695389041343313363$ | $5156462827868029$ |
| 5:0 | $26276870068847530680754070786654588966$ | $24225778855064601174752077070329968817$ | $-23656438517792625646434502305$ | $8143163040824611150377503579$ | $-12050120713988597195638112431$ | $5555977340677932182994680793$ | $18650077005289207803$ |
| 5:1 | $32366931771558827564210606414060894011$ | $15995473200101419591513584527843264146$ | $-28436450907744974063481199193$ | $12967425429417128333171971566$ | $11679032622487521177286341278$ | $-357278703814526978285554219$ | $4877875042322753160$ |
| 5:2 | $83280749367090746524792737119324922758$ | $29241870867265591418038082162659436847$ | $69729774393985396199387401463$ | $-15816343044281882120212778764$ | $-44258850372315503729369034527$ | $13206236868809094064592601175$ | $24794154620441173731$ |
| 5:3 | $85203921598911965838590719388341439661$ | $14555869445095256454242793526847204224$ | $50025546628047438907082486393$ | $-14671549846995534150662449860$ | $-6222930259231060747510366308$ | $3149730719749240168930457364$ | $51133805365216951826$ |
| 5:4 | $86964758621954677692914605303626081740$ | $-39185998634386835942336043281779847298$ | $737404212317019037873642970$ | $-123222430421183732687019647$ | $5605766797122980178447857810$ | $-921840520360638661098088884$ | $1509897896822671372$ |
| 5:5 | $89235650567137665471507950398268042607$ | $-59680989254236447413170060268919117000$ | $-805673623696593213141283155$ | $214727640876756292786093727$ | $-2067339269817092204814378104$ | $-73319894539187032636490930$ | $5152476028631501$ |
| 6:0 | $26317624555346825109814583799278229889$ | $24253582303837080894110165830426547188$ | $-23702862782722402470768611735$ | $8158651085290183330463061431$ | $-12091099730243873801473615910$ | $5565406894894211211471799899$ | $18704168207825055684$ |
| 6:1 | $32431844865401999100924349966003319734$ | $15993684710778561857043416443957633591$ | $-28466577843364735910236213493$ | $12997849554140572566221501110$ | $11677252223076245858551014291$ | $-358114804088513237125665168$ | $4864118138495092607$ |
| 6:2 | $83201617236822222680013755041473235350$ | $29307868437546292613694589878947224415$ | $69802218408921948113065147449$ | $-15836516311261980656906113328$ | $-44258565928835377128134395501$ | $13192659340454071030626673100$ | $24707001566806186168$ |
| 6:3 | $85130516070931119307490080592609789138$ | $14571492737021494775225666107132659314$ | $49994233398566310317139246545$ | $-14690723256549847365966681310$ | $-5976543546293602414472123450$ | $3099725483907804199881372645$ | $49999243156227670450$ |
| 6:4 | $86964143162221429231860986411538124240$ | $-39190603253150417476188255894393083930$ | $736029012799348457083768924$ | $-122961609569943447819245103$ | $5595641114451851879476057766$ | $-920007943705313086051641151$ | $1513094061277698715$ |
| 6:5 | $89236723920907602752536156128654395464$ | $-59681355926135437532232436314409489896$ | $-805220756761226494244878975$ | $214613883850334870908574478$ | $-2065999057921567826083756593$ | $-73348842034044100536931804$ | $5148491958806153$ |
| 7:0 | $26358456775695366439267829251503240436$ | $24281432971788418077687245689772246703$ | $-23749748805702565622639964361$ | $8174256727251151887178294340$ | $-12132136303384607046584161007$ | $5574865114110484108978805192$ | $18758531827000768323$ |
| 7:1 | $32496910644085011497807150335555070568$ | $15991892074098136404779504693166999216$ | $-28497065460013793936332935903$ | $13028499871348277409422149398$ | $11675392752369794361554756180$ | $-358937681711618743108869325$ | $4850399875814889376$ |
| 7:2 | $83122384129617746273061312264877692197$ | $29373796152461399477145571693685589025$ | $69874836651621785452078599026$ | $-15856734194299101529700805898$ | $-44254355200966031312584322759$ | $13178296881800926282037702348$ | $24617658802331435065$ |
| 7:3 | $85057013746662287820828064640899608026$ | $14586868082720282896244706199260076746$ | $49963845321858499650096403772$ | $-14710268479271185772610561517$ | $-5734077917131769634908542586$ | $3050549924915588164941998485$ | $48907913928138895828$ |
| 7:4 | $86963529004395494297860794747997187579$ | $-39195198723389331386281019114720264355$ | $734658366728054936871506229$ | $-122701666809906871016844104$ | $5585546409782540756802462140$ | $-918181106320090917180067908$ | $1516337667742445835$ |
| 7:5 | $89237796706143577609137528135294326399$ | $-59681722742426912307270055031523433531$ | $-804768321404673529037162868$ | $214500227269195671552401818$ | $-2064660810038186379421583711$ | $-73377651603526007908310553$ | $5144510620775903$ |
| 8:0 | $26399367320094976322621951484079174902$ | $24309331003773868135830955911432895682$ | $-23797099252726796371588725733$ | $8189980855137943122175613880$ | $-12173233173165311809024256199$ | $5584352610815852529781153100$ | $18813172209788279600$ |
| 8:1 | $32562130246200934874071613801258032483$ | $15990095355652577087905076977657699690$ | $-28527919740461351916344366787$ | $13059379441484450273588277899$ | $11673455347158364321580683379$ | $-359747544567930768662741797$ | $4836718723770017828$ |
| 8:2 | $83043049816766791023042696598264641157$ | $29439650119620540172583445343788240716$ | $69947635307253904002346211391$ | $-15876998944626965370546802416$ | $-44246276686749894287464448347$ | $13163162371719947322600890028$ | $24526185050883415784$ |
| 8:3 | $84983412765216594089762994393411088589$ | $14601999596150858429561226815036318790$ | $49934380950726567962994679082$ | $-14730186257784382822702620387$ | $-5495473424925009033258056541$ | $3002190299431064160535595333$ | $47857653448754244791$ |
| 8:4 | $86962916144096684224677514812292607732$ | $-39199785073737443358667533295508627768$ | $733292252775067517410670419$ | $-122442598038254650102272035$ | $5575482549282643095065409525$ | $-916359983234535511763262064$ | $1519629307068489745$ |
| 8:5 | $89238868923347477811242979127377671853$ | $-59682089702422300837174719914757961684$ | $-804316316991919032481400430$ | $214386670997926513240442374$ | $-2063324521879879781972430615$ | $-73406323669787995650835069$ | $5140532016897990$ |
| 9:0 | $26440356783230192474499902693572032820$ | $24337276547717049522118348394618048733$ | $-23844916853992758074369293674$ | $8205824373641860769247700761$ | $-12214393082122806678585883947$ | $5593869999889198685011748675$ | $18868093761441356719$ |
| 9:1 | $32627504825768821696119410923036593878$ | $15988294620001515201698494526255580753$ | $-28559146747855675696411294956$ | $13090491374697086261384408330$ | $11671441127998982736794076245$ | $-360544597903187761043464127$ | $4823073131880796195$ |
| 9:2 | $82963614058315650969438382403282105330$ | $29505426510641317872496340524691460804$ | $70020620596435879200371041301$ | $-15897312808275793115870818557$ | $-44234388350762384039394872556$ | $13147268533998959598838569438$ | $24432638259999767201$ |
| 9:3 | $84909711261789805983177427497330327598$ | $14616891322958162068903301536031037832$ | $49905838986209297170630012635$ | $-14750477415828469037884034341$ | $-5260670667825980851632619833$ | $2954633025561860121803693173$ | $46846466778031823111$ |
| 9:4 | $86962304576965262771165922073352140281$ | $-39204362332704118515042848407259207878$ | $731930649741083774054904747$ | $-122184399176805779713835088$ | $5565449399871174610898442448$ | $-914544549618694567199489183$ | $1522969582245784504$ |
| 9:5 | $89239940573020514731645638527344970318$ | $-59682456805435139481977498041519914711$ | $-803864742889290354303496903$ | $214273214901380602739271993$ | $-2061990189171787957389418686$ | $-73434858653580175370737209$ | $5136556149503118$ |

### 6.4 Cells 10 through 19

| $t:i$ | $M_r$ | $M_b$ | $A_{00}$ | $A_{01}$ | $A_{10}$ | $A_{11}$ | $R_\rho$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 10:0 | $26481425764350107487770202035811794628$ | $24365269754622235032855118037401298118$ | $-23893204404587217130431202157$ | $8221788203929831308781852785$ | $-12255618776163226529709240277$ | $5603417898736325601146256921$ | $18923300946649028288$ |
| 10:1 | $32693035552485241045517994074891616744$ | $15986489930684839700526523310004045318$ | $-28590752628071305533215604033$ | $13121838832049410409087090562$ | $11669351199472127058654331337$ | $-361329044377288554198270983$ | $4809461528954105786$ |
| 10:2 | $82884076603093537123489359888463164925$ | $29571121560366209020583525524000756461$ | $70093798773440999212057784219$ | $-15917678026048534873936578302$ | $-44218747603847403142472812151$ | $13130627934324766249056647456$ | $24337075583266749401$ |
| 10:3 | $84835907367253443399963880917207234110$ | $14631547241287068801507322256652912287$ | $49878218281966003708337187894$ | $-14771142859584284422470126583$ | $-5029610808280511999480404893$ | $2907864685601988805424721998$ | $45872477829657034942$ |
| 10:4 | $86961694298661823383029900227882316062$ | $-39208930528674921393191207676344768926$ | $730573536554618514663733034$ | $-121927066171836468701137415$ | $5555446829213356363625756122$ | $-912734780782124972615435906$ | $1526359108692196441$ |
| 10:5 | $89241011655663224671150202431532145077$ | $-59682824050781064850634558777929399188$ | $-803413598464453677730647222$ | $214159858844675818729395805$ | $-2060657807651216132613895593$ | $-73463256974252898366346754$ | $5132583020895595$ |
| 11:0 | $26522574867351296080658035615289984869$ | $24393310778587331580515273398009708077$ | $-23941964765193596799274701813$ | $8237873283865051480277386855$ | $-12296913005152005253988376527$ | $5612996927428216289960603893$ | $18978798290717108919$ |
| 11:1 | $32758723611981950650813650376516771495$ | $15984681350235496378233787699443645855$ | $-28622743612113605258482035935$ | $13153425026763721544139158421$ | $11667186650434535217317094103$ | $-362101084116200834100769706$ | $4795882322310947033$ |
| 11:2 | $82804437188738676363882292206177433413$ | $29636731566065212679210571058908716090$ | $70167176124619417397683316984$ | $-15938096833543397763989899133$ | $-44199411284529848208885165711$ | $13113252977599302801223228698$ | $24239553364706020715$ |
| 11:3 | $84761999207739263048136746455754880772$ | $14645971262609465282451581867964557111$ | $49851517848534095872759821766$ | $-14792183578996242410793909249$ | $-4802235590673512766057967229$ | $2861872028435904813905710241$ | $44933920985295704190$ |
| 11:4 | $86961085304867167356294304309311292890$ | $-39213489689912311071919647363526081322$ | $729220892271060791220474263$ | $-121670594993900584450645240$ | $5545474705715443869454239739$ | $-910930652172925738700754977$ | $1529798514551599035$ |
| 11:5 | $89242082171775470180146890569778602102$ | $-59683191437777806815598980834892392767$ | $-802962883086410231761289458$ | $214046602693193997976046524$ | $-2059327373067592311656618600$ | $-73491519049762101049012817$ | $5128612633353475$ |
| 12:0 | $26563804700861860600694961410346467702$ | $24421399776817554184477756872732510744$ | $-23991200862822405468232326473$ | $8254080568233665013559739496$ | $-12338278523507059791089018874$ | $5622607708840471554045631229$ | $19034590380778561570$ |
| 12:1 | $32824570206089871433757640951857240393$ | $15982868940192028970042775744542728387$ | $-28655126018582718412646575576$ | $13185253225498741621560492118$ | $11664948554268268047797671411$ | $-362860914763287121759285192$ | $4782333896986464529$ |
| 12:2 | $82724695541724186208876054857521908159$ | $29702252886625882321551904150520759581$ | $70240758967025452770818201420$ | $-15958571461220633306554414481$ | $-44176435642030458079689117289$ | $13095155905573696679170833183$ | $24140127125072032553$ |
| 12:3 | $84687984904217142305009247171483196736$ | $14660167232562549452454205374862540652$ | $49825736857470095109746474464$ | $-14813600649091468934225041479$ | $-4578487357375164934893598640$ | $2816641971626090456094952183$ | $44029133394678691369$ |
| 12:4 | $86960477591282182894645976255134378664$ | $-39218039844556331480673828846710381194$ | $727872696071739141803511071$ | $-121414981637651658268919242$ | $5535532898519599002309424850$ | $-909132139376778927852543828$ | $1533288441000821334$ |
| 12:5 | $89243152121856441376622486481258843351$ | $-59683558965745181554060996188549772617$ | $-802512596125492516908661058$ | $213933446312580223989900292$ | $-2057998881182424925532526709$ | $-73519645296674626916473199$ | $5124644989128691$ |
| 13:0 | $26605115878326625257680880430519538526$ | $24449536909639800224138560677049549255$ | $-24040915691564995808286084139$ | $8270411028977599706455140070$ | $-12379718090795411247885769246$ | $5632250868793987399707992982$ | $19090681867033463054$ |
| 13:1 | $32890576553109534944286566109658948247$ | $15981052761110865042497854340878081743$ | $-28687906256199079333737575975$ | $13217326749661616482763918666$ | $11662637969126087462112400712$ | $-363608731530066643389694854$ | $4768814614901426291$ |
| 13:2 | $82644851377383509122068393948020004307$ | $29767681941732288525279704272161521825$ | $70314553647243348049901542319$ | $-15979104134511614018697112180$ | $-44149876320809926870444951459$ | $13076348794783882623287401795$ | $24038851549963574371$ |
| 13:3 | $84613862572066367269274554782391627711$ | $14674138931796810838399536968163934511$ | $49800874645384257136328648121$ | $-14835395231299518444848840853$ | $-4358309063260087377519723300$ | $2772161603200410590550107205$ | $43156547897610279829$ |
| 13:4 | $86959871153627725052877927313306924858$ | $-39222581020625296933644656871449694852$ | $726528927262994979933923279$ | $-121160222121666436132465103$ | $5525621277498804269057048120$ | $-907339218115998507573613680$ | $1536829542565755408$ |
| 13:5 | $89244221506404657260620883953425539241$ | $-59683926634005084615739725731529770022$ | $-802062736953360544360542203$ | $213820389568742118167102573$ | $-2056672327769260657505791026$ | $-73547636130173525195612795$ | $5120680090447201$ |
| 14:0 | $26646509018093510224020496054937208057$ | $24477722340517730307545637383723640902$ | $-24091112313371126602329474010$ | $8286865655433700219618532697$ | $-12421234472333483692740465632$ | $5641927036196934320341433049$ | $19147077464019363118$ |
| 14:1 | $32956743888088179897351157869813923107$ | $15979232872578349445858825091148786159$ | $-28721090826392708461235733874$ | $13249648976755757910144580142$ | $11660255938173213584196856435$ | $-364344727246431570890175082$ | $4755322814004093284$ |
| 14:2 | $82564904399935199685178358195533070719$ | $29833015211034380459203390555531194932$ | $70388566540403988433329129512$ | $-15999697073968299281526932065$ | $-44119788346570902394427814072$ | $13056843554771898504374733922$ | $23935780479655633170$ |
| 14:3 | $84539630320640314159833396377993605740$ | $14687890076832229998895040902188606415$ | $49776930717878835683994802406$ | $-14857568574775847599303005461$ | $-4141644288770491043252109116$ | $2728418183155003739450141964$ | $42314686510678178001$ |
| 14:4 | $86959265987644496558748708264088731954$ | $-39227113246016472927791080966478675446$ | $725189565275264049271692530$ | $-120906312488269959292229960$ | $5515739713251819051389353293$ | $-905551864248587050916184402$ | $1540422487446940476$ |
| 14:5 | $89245290325917967025165509865704742311$ | $-59684294441881484017110044586839834408$ | $-801613304942998088498053824$ | $213707432327849133398049449$ | $-2055347708613642442806412597$ | $-73575491964063326270896809$ | $5116717939509120$ |
| 15:0 | $26687984743501117428549284548006535142$ | $24505956236067562423341765826701122922$ | $-24141793858850814891872460786$ | $8303445454579296342804555908$ | $-12462830439791326162977332642$ | $5651636843188102050073376705$ | $19203781951912853483$ |
| 15:1 | $33023073463103680087902623094143177509$ | $15977409333222528010630863806062060804$ | $-28754686325958605991123436223$ | $13282223341765762721377128615$ | $11657803489825523930486844471$ | $-365069092410336238546390308$ | $4741856807381363695$ |
| 15:2 | $82484854302506867292746249849939356970$ | $29898249233309135879774917358309589644$ | $70462804049385288487010888675$ | $-16020352495451261936359068868$ | $-44086226113648262050469885556$ | $13036651926577468552010288988$ | $23830966900560259266$ |
| 15:3 | $84465286252824497363378217336595824389$ | $14701424320921313211589207045314948350$ | $49753904753399931840164454617$ | $-14880122017732207248291112351$ | $-3928437251592563634327194001$ | $2685399144687994647033187391$ | $41502154427353371135$ |
| 15:4 | $86958662089092929505646105374067253647$ | $-39231636548506752243825532748668680358$ | $723854589662165862569729702$ | $-120653248803362159397562286$ | $5505888077098177411136484763$ | $-903770053767300208599923637$ | $1544067957854954051$ |
| 15:5 | $89246358580893551363655940937959403876$ | $-59684662388700413361948794815208784460$ | $-801164299468708952716659538$ | $213594574456331850134422251$ | $-2054025019513067641984188975$ | $-73603213210775294014113283$ | $5112758538488861$ |
| 16:0 | $26729543682967560579997015950337687549$ | $24534238766074586365239861218182864722$ | $-24192963528100982482436296086$ | $8320151451284351016227690401$ | $-12504508771801008536831542363$ | $5661380925281674771699012435$ | $19260800177863190005$ |
| 16:1 | $33089566547555492257965026993687486432$ | $15975582200724684076560506155297554022$ | $-28788699449780646678195490852$ | $13315053338580692555064154080$ | $11655281637984257581964401439$ | $-365782015236978074637130303$ | $4728414882338022471$ |
| 16:2 | $82404700767158085986487917992820990467$ | $29963380605614813609844293123488004432$ | $70537272604189167840655551436$ | $-16041072610354519100903142568$ | $-44049243373719893095497004334$ | $13015785481484970029530467663$ | $23724462938227555242$ |
| 16:3 | $84390828464587941676606433048501902987$ | $14714745254917653705384996557952723563$ | $49731796607012767322289293272$ | $-14903056988777094827206057056$ | $-3718632817013489047878209591$ | $2643092095178824790386230057$ | $40717634485401779246$ |
| 16:4 | $86958059453753067908520538642769315284$ | $-39236150955753326388833668048889620226$ | $722523980099601044720045081$ | $-120401027156245952978986929$ | $5496066241073227060189136305$ | $-901993762798718878260181355$ | $1547766650355953677$ |
| 16:5 | $89247426271827923773750979504242905689$ | $-59685030473789964988085139799567206571$ | $-800715719906113248492800871$ | $213481815820881274904025755$ | $-2052704256276946387070395186$ | $-73630800281372655130412256$ | $5108801889535269$ |
| 17:0 | $26771186470080572689292096546340385319$ | $24562570103510405746738620064622005123$ | $-24244624591557417793518571731$ | $8336984688570337071094243017$ | $-12546272254569447204712529831$ | $5671159921513503196689218861$ | $19318137057358839014$ |
| 17:1 | $33156224428462819032183674446802464397$ | $15973751531830630348379868851572351178$ | $-28823136993626471215521759849$ | $13348142521457048045915240728$ | $11652691382267287155503228732$ | $-366483681707489130124636875$ | $4714995299442869957$ |
| 17:2 | $82324443464902091648714251351856823045$ | $30028405982439549183567875581751527712$ | $70611978661488257201950163354$ | $-16061859625865483079138791508$ | $-44008893225772089534096448089$ | $12994255620011372405848572889$ | $23616319851800913958$ |
| 17:3 | $84316255044527820620926884603715455639$ | $14727856408148783492551215481266464142$ | $49710606314110112300227098876$ | $-14926375008269392607380572645$ | $-3512176507024620666081384256$ | $2601484816927504592815762182$ | $39959882060171663810$ |
| 17:4 | $86957458077424451115628910447585547723$ | $-39240656495294352418829408080795196553$ | $721197716384856500639641703$ | $-120149643659456820301457458$ | $5486274077923209100589774873$ | $-900222967602328997098995221$ | $1551519276227726735$ |
| 17:5 | $89248493399216931857750401313516684201$ | $-59685398696480283140240427917330253417$ | $-800267565632143687639873695$ | $213369156288448141263032120$ | $-2051385414726560099722021741$ | $-73658253585555805634985695$ | $5104847994771754$ |
| 18:0 | $26812913743688925116756653682678726107$ | $24590950424550915259567033914443585961$ | $-24296780390872591555640448822$ | $8353946227875996490466665433$ | $-12588123682495921936993154311$ | $5680974474588941420544118767$ | $19375797575627847624$ |
| 18:1 | $33223048410770188836502975052974447347$ | $15971917382361758477787569523504835083$ | $-28858005857015966429719023444$ | $13381494506522823380291648643$ | $11650033708237021245751681916$ | $-367174275617157241743009678$ | $4701596291540444072$ |
| 18:2 | $82244082055726095013686147951127150522$ | $30093322074845463523302496234512000733$ | $70686928704335703100165839983$ | $-16082715745258420699733163452$ | $-43965228107255601909368866366$ | $12972073571121232867517952689$ | $23506588029843249668$ |
| 18:3 | $84241564073407287117108331441470525945$ | $14740761249292150138282101376416735187$ | $49690334094063489227106485148$ | $-14950077689688302927949353443$ | $-3309014508234402521175749811$ | $2560565267667596473305054087$ | $39227720346444324664$ |
| 18:4 | $86956857955925998068704168179915914069$ | $-39245153194549615179179657557616729579$ | $719875778435718329645331654$ | $-119899094448593853769865972$ | $5476511461100378144667011167$ | $-898457644569608885018098121$ | $1555326561826620257$ |
| 18:5 | $89249559963555758619487536499331301521$ | $-59685767056103557168843503232280910387$ | $-799819836025041887697530817$ | $213256595726242213175284474$ | $-2050068490695020180527882027$ | $-73685573531667494574093179$ | $5100896856296434$ |
| 19:0 | $26854726147995192951677978673614870932$ | $24619379908595021172688248930739330169$ | $-24349434339819882965155306460$ | $8371037149330140991150960602$ | $-12630065858794550995392957857$ | $5690825231032317996173032229$ | $19433786789072967723$ |
| 19:1 | $33290039817660661780204021518420942579$ | $15970079807225848675554603013105044361$ | $-28893313046166027726491040574$ | $13415112973324081874971004951$ | $11647309587624999875797307702$ | $-367853978623196034406719177$ | $4688216062726988124$ |
| 19:2 | $82163616188610046833237797884439742933$ | $30158125649609386170408871134845440860$ | $70762129242031671467972063960$ | $-16103643168219881717614311474$ | $-43918299786370328331454034069$ | $12949250391655326566507081352$ | $23404160948800717823$ |
| 19:3 | $84166753623686407282105489911552290758$ | $14753463187253120614315749216690080899$ | $49670980353826665076818692574$ | $-14974166741022679845366539662$ | $-3109093678652678990203381006$ | $2520321580866243405966627248$ | $38520035995204315756$ |
| 19:4 | $86956259085095892404239514779146785294$ | $-39249641080821185000470469741901515108$ | $718558146289592408856817435$ | $-119649375682152261236547040$ | $5466778264758162429351774790$ | $-896697770223124066109884782$ | $1559189248965737856$ |
| 19:5 | $89250625965338923757744793258503886470$ | $-59686135551994014754707967873064770619$ | $-799372530464354690398571122$ | $213144134001731590808365408$ | $-2048753480027226868660344098$ | $-73712760526697985103503099$ | $5096948476182262$ |

### 6.5 Cells 20 through 29

| $t:i$ | $M_r$ | $M_b$ | $A_{00}$ | $A_{01}$ | $A_{10}$ | $A_{11}$ | $R_\rho$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 20:0 | $26896624332649902338594015103107082724$ | $24647858738284113419871789118987341633$ | $-24402589925224791628701094661$ | $8388258552031657895352660297$ | $-12672101596121997381288763484$ | $5700712841338112263598797107$ | $19492109826742494270$ |
| 20:1 | $33357199990876877826515080339640834584$ | $15968238860427641561172136414279074025$ | $-28929065677014403027600523902$ | $13449001666415550352930757720$ | $11644519978553245367677305461$ | $-368522970292083148839164676$ | $4674852787289250880$ |
| 20:2 | $82083045501543699049819222830452198432$ | $30222813528361228716318112848436852797$ | $70837586810140385483443260797$ | $-16124644091204628837817956714$ | $-43868159355418605342912640703$ | $12925796965959982497232175270$ | $23378927303350177054$ |
| 20:3 | $84091821759046092636145256739594231451$ | $14765965572043979724194494627573910368$ | $49652545691500836844549191041$ | $-14998643966182847951539300813$ | $-2912361553406061772219467434$ | $2480742065824065173680662268$ | $37835775195684862964$ |
| 20:4 | $86955661460791468388649036942753325343$ | $-39254120181294070887027779578609303747$ | $717244800102632569046207674$ | $-119400483541357309726337741$ | $5457074363746363543025599954$ | $-894943321215629497169225543$ | $1563108095304806744$ |
| 20:5 | $89251691405060284956204182433111334540$ | $-59686504183487915159458464534384476025$ | $-798925648330930493157949597$ | $213031770982642018736186783$ | $-2047440378579828271060857604$ | $-73739814976290193036787889$ | $5093002856477162$ |
| 21:0 | $26938608952847096197757395270401210904$ | $24676387099522297983145211473211122361$ | $-24456250707923729985919907494$ | $8405611554336890603770365013$ | $-12714233717210685166134589447$ | $5710637960123908628471289237$ | $19550771891837810606$ |
| 21:1 | $33424530291050171214104804948571688155$ | $15966394595079174360046671009896471415$ | $-28965270978325528094426930774$ | $13483164396996789826086661220$ | $11641665825752430924634684099$ | $-369181428146486275586282043$ | $4661504608604636773$ |
| 21:2 | $82002369621541812988641430038731797491$ | $30287382586720980658583978037862944741$ | $70913307970651770954091931490$ | $-16145720707820673280984734266$ | $-43814857225169036803315761878$ | $12901724005704684718664845308$ | $23353054170182209389$ |
| 21:3 | $84016766533904910569266074571358875443$ | $14778271695662953474615613695244343685$ | $49635030899870810476199896841$ | $-15023511266437993744693962633$ | $-2718766349442041355678149655$ | $2441815207587255601924345533$ | $37173939622137123153$ |
| 21:4 | $86955065078889097680138532801128012245$ | $-39258590523036869234951087676224361454$ | $715935720148876287219807348$ | $-119152414229999695258479977$ | $5447399633606395387411254584$ | $-893194274329179132666285857$ | $1567083874752134389$ |
| 21:5 | $89252756283213039169944850099211778576$ | $-59686872949923542501593608159573093624$ | $-798479189006915593528715002$ | $212919506536956196537908037$ | $-2046129182221179560351835664$ | $-73766737284744802975284471$ | $5089059999204163$ |
| 22:0 | $26980680669421355647534881008457634775$ | $24704965181497398647160742081327435908$ | $-24510420323751010914894999354$ | $8423097294154568506216641223$ | $-12756465055507811116054802524$ | $5720601246285203197074447799$ | $19609778263258666744$ |
| 22:1 | $33492032098037983034334620117239089178$ | $15964547063409883459822491652098495921$ | $-29001936294881378884217309941$ | $13517605044595562469644489174$ | $11638748060776929108065582977$ | $-369829527711796787081450820$ | $4648707787358995053$ |
| 22:2 | $81921588164657372384099240518451139858$ | $30351829753435238916892241052811537812$ | $70989299312282021965613199444$ | $-16166875209242090440133808288$ | $-43758443120174779837549592952$ | $12877042049875982340808808176$ | $23326562959220060358$ |
| 22:3 | $83941585992928637495508179976180609046$ | $14790384792972348221715204514762469410$ | $49618436969921372794556223751$ | $-15048770641882213196027023315$ | $-2528256969277547033702498974$ | $2403529666683730194862218253$ | $36533583164929744780$ |
| 22:4 | $86954469935284076910191519426813095608$ | $-39263052133002408116167601990836542946$ | $714630886819387821074694217$ | $-118905163974272324606303617$ | $5437753950566562001124857404$ | $-891450606474242756388251811$ | $1571117377879091732$ |
| 22:5 | $89253820600289723908499574428169478433$ | $-59687241850641199058073753358846431030$ | $-798033151875750546569952810$ | $212807340532913091783040733$ | $-2044819886831302340671814015$ | $-73793527855025362130907621$ | $5085119906361530$ |
| 23:0 | $27022840148946315324881630089574376834$ | $24733593176702737575970702558390935285$ | $-24565102484554665924304528253$ | $8440716929248466878699520112$ | $-12798798455820443314331311254$ | $5730603363152138954252459588$ | $19669134297187251064$ |
| 23:1 | $33559706811269812131225461583601273076$ | $15962696316776475237893158816815542901$ | $-29039069090760487696861125034$ | $13552327558800080226988130493$ | $11635767602216802295556081356$ | $-370467442562290986148707482$ | $4636242434938534787$ |
| 23:2 | $81840700735992665508116887222395815317$ | $30416152009514123657276113748671317675$ | $71065567450907639671954364285$ | $-16188109784648359934460234866$ | $-43698966074992181791119682832$ | $12851761464936229003503590483$ | $23299474654742172351$ |
| 23:3 | $83866278170532403700985662042536537094$ | $14802308042574954471479457334946474023$ | $49602765094342960643433669099$ | $-15074424192932301332639234565$ | $-2340783003845682008541693286$ | $2365874278694696041737680314$ | $35913808762529928023$ |
| 23:4 | $86953876025890516077645795985596851342$ | $-39267505038028387164667283315945102585$ | $713330280621408711318419467$ | $-118658729022608494995238724$ | $5428137191537373875567219351$ | $-889712294688830010716204726$ | $1575209412347578059$ |
| 23:5 | $89254884356782218515482132500862315705$ | $-59687610884983198591322338505567055469$ | $-797587536322166535072080475$ | $212695272839007255392647334$ | $-2043512488301844180635145898$ | $-73820187088763351952384398$ | $5081182579922897$ |
| 24:0 | $27065088063834711717462555758604656465$ | $24762271280959704549221797867528155038$ | $-24620300979241750745336454301$ | $8458471637547983224399414712$ | $-12841236774967005211990755691$ | $5740644978648247515584612989$ | $19728845428712151624$ |
| 24:1 | $33627555850101953087451648921928448389$ | $15960842405672566971469361939960328855$ | $-29076676952708396621341297506$ | $13587335961041888766835603746$ | $11632725355906797124472153492$ | $-371095344366939233292521529$ | $4623787904582329573$ |
| 24:2 | $81759706929708106774198523686975951831$ | $30480346387369376854255030339204677547$ | $71142119030127737194305495881$ | $-16209426621689043123914418996$ | $-43636474431247624578767555851$ | $12825892445136142368795262280$ | $23271809818350158878$ |
| 24:3 | $83790841090375263448833487749035574861$ | $14814044567687919894197962836241925576$ | $49588016671035642458786434837$ | $-15100474121860376034130870702$ | $-2156294734492394731825935063$ | $2328838053672545737593731953$ | $35313765349905491249$ |
| 24:4 | $86953283346641227748405540773392000840$ | $-39271949264838013100735948411845494702$ | $712033882177515578675303608$ | $-118413105645521457897300703$ | $5418549234106902397841102629$ | $-887979316137621555252459598$ | $1579360803350941645$ |
| 24:5 | $89255947553181745444797392419977375671$ | $-59687980052293859701530098752547739527$ | $-797142341732181752585109965$ | $212583303323988139366592140$ | $-2042206982536038312621801169$ | $-73846715386263237664862016$ | $5077248021837399$ |
| 25:0 | $27107425092440004568473226198393554170$ | $24790999693441125089690163938281672429$ | $-24676019674853817281910713153$ | $8476362617466822627695591942$ | $-12883782882435450508396162574$ | $5750726765451277398921951565$ | $19788917173493340334$ |
| 25:1 | $33695580654181279005844040262954998949$ | $15958985379738099539610904808728547231$ | $-29114767593602954476731499832$ | $13622634346431212083295337524$ | $11629622215132404860465099327$ | $-371713402934883477386269601$ | $4611342199120018263$ |
| 25:2 | $81678606329028673956031149650190465498$ | $30544409969954386130197967604676068260$ | $71218960721949642934814061690$ | $-16230827906972678802911986302$ | $-43571015835502377009685400130$ | $12799445012970635449757613015$ | $23243588592277759232$ |
| 25:3 | $83715272764847008417835312703304807830$ | $14825597437013349463610511661038316021$ | $49574193306620345811750905796$ | $-15126922734364439087651121976$ | $-1974743134172900139872631669$ | $2292410175415515344063656683$ | $34732645078888646285$ |
| 25:4 | $86952691893487617053902739818166722831$ | $-39276384840040630928664014783367939085$ | $710741672224785143227388022$ | $-118168290135445353235801714$ | $5408989956536172059341087332$ | $-886251648111107287253608801$ | $1583572394068850218$ |
| 25:5 | $89257010189978871533445935979638417799$ | $-59688349351919499204151988440898139806$ | $-796697567493097799195758911$ | $212471431856859416866852009$ | $-2040903365448663497607122078$ | $-73873113146507495832229601$ | $5073316234029798$ |
| 26:0 | $27149851919159612393775953626090473473$ | $24819778616695438118737869971451385706$ | $-24732262517673253787912871247$ | $8494391088229991013231944624$ | $-12926439661048441491397104392$ | $5760849401156190745881587049$ | $19849355129469351758$ |
| 26:1 | $33763782683818336108208919605684053633$ | $15957125287768523523311673613126212556$ | $-29153348856018002374511062416$ | $13658226885646657951087574723$ | $11626459060833049584230478811$ | $-372321786260603996045035804$ | $4598903286707609791$ |
| 26:2 | $81597398506247842589225259575221089223$ | $30608339889906824804293439012797251161$ | $71296099227593072587076166482$ | $-16252315826578844254654140387$ | $-43502637237867176488650697578$ | $12772429019767823565990872492$ | $23214830703014516552$ |
| 26:3 | $83639571194547026999387359523489741846$ | $14836969665604941696339197775328694962$ | $49561296819966191104209970885$ | $-15153772441179993127378349171$ | $-1796079867895739993025147266$ | $2256580000609093945426483421$ | $34169680732395044920$ |
| 26:4 | $86952101662399572481489791021079828440$ | $-39280811790132350843072578319138714211$ | $709453631613966394552295510$ | $-117924278806577500467692947$ | $5399459237754590072574436655$ | $-884529268024731557055418144$ | $1587845046136626180$ |
| 26:5 | $89258072267663509270934967313357988801$ | $-59688718783208425532487198554164377880$ | $-796253212993496089999556672$ | $212359658306878304646943907$ | $-2039601632966004054745646335$ | $-73899380767161620050886120$ | $5069387218400618$ |
| 27:0 | $27192369234539804161689012213413054005$ | $24848608256671694191043103234175569148$ | $-24789033534361218844452748354$ | $8512558290209301744216739751$ | $-12969210007635850961305074719$ | $5771013568440412484003530573$ | $19910164978607868175$ |
| 27:1 | $33832163420370026868948576450802854360$ | $15955262177723760204948229498448606035$ | $-29192428715889138536915987279$ | $13694117826881262898868579580$ | $11623236761802466065185313821$ | $-372920660568796454207211379$ | $4586469099438452924$ |
| 27:2 | $81516083022728904225332664706806513811$ | $30672133328694549711567238571296609677$ | $71373541278408376205842556039$ | $-16273892566592394047112054770$ | $-43431384891320154402888647236$ | $12744854146401552629731276849$ | $23185555465219120795$ |
| 27:3 | $83563734367754996335025744790087616963$ | $14848164215730018794426103237458474422$ | $49549329245742727428102841184$ | $-15181025759735853656659742094$ | $-1620257292460474633844117751$ | $2221337057843729850916852397$ | $33624143317140385015$ |
| 27:4 | $86951512649365357450012410688572272802$ | $-39285230141496670878666254440975731369$ | $708169741308659841924194708$ | $-117681067994722033162662540$ | $5389956957355413042635411736$ | $-882812153418045312397729331$ | $1592179640129583361$ |
| 27:5 | $89259133786724918065307213349373914267$ | $-59689088345510932165233197019386191625$ | $-795809277623234276214355092$ | $212247982543554887817575417$ | $-2038301781025810054927340550$ | $-73925518644579104883082365$ | $5065460976826272$ |
| 28:0 | $27234977735382290229766548502066758628$ | $24877488822745385785221218498280404536$ | $-24846336833127919239470338678$ | $8530865485267607764349212934$ | $-13012096833714915636245582110$ | $5781219955231418058051104749$ | $19971352488700963960$ |
| 28:1 | $33900724366632168498111526468309554105$ | $15953396096736938862059344731594220492$ | $-29232015286285405439137321677$ | $13730311497846937529905712815$ | $11619956174886329189718197698$ | $-373510190358980713462175338$ | $4574037531904767557$ |
| 28:2 | $81434659428903559985118659756340563545$ | $30735787515765351163597848035302519248$ | $71451293636904600419088923272$ | $-16295560313658952830310396288$ | $-43357304351683580551509022042$ | $12716729904118225720746668306$ | $23155781785898531221$ |
| 28:3 | $83487760259893178218449567152220323903$ | $14859183997726355134702952129898800915$ | $49538292838005812471196624733$ | $-15208685315857321167629943362$ | $-1447228455533133092763419374$ | $2186671046517946561407412598$ | $33095339820860650233$ |
| 28:4 | $86950924850391502663878498355333324912$ | $-39289639920405095337893540886716285749$ | $706889982384503774637896230$ | $-117438654057134863847929948$ | $5380482995591250343572551175$ | $-881100281953865106270751548$ | $1596577076062925043$ |
| 28:5 | $89260194747651705505799472555431036365$ | $-59689458038179291078905258792931474496$ | $-795365760773442678881915715$ | $212136404436651446938673231$ | $-2037003805577257677528794181$ | $-73951527173806408137364224$ | $5061537511159189$ |
| 29:0 | $27277678124852556711346038651387812100$ | $24906420527745121563108397115704110117$ | $-24904176604936007238583598173$ | $8549313957111978494969483874$ | $-13055103066178377000224918987$ | $5791469254876748077540358096$ | $20032923515206305336$ |
| 29:1 | $33969467047242224106172142860873337308$ | $15951527091122911642403355248463666254$ | $-29272116821290902070997558999$ | $13766812307839459098847873660$ | $11616618145177196836678212869$ | $-374090538449863171713961668$ | $4561606439707555644$ |
| 29:2 | $81353127264267685319907257616229432068$ | $30799299727701104362345175728955882716$ | $71529363097883336827951430999$ | $-16317321255560800908162915634$ | $-43280440478216727724938609914$ | $12688065635469125001314545615$ | $23125528168830138744$ |
| 29:3 | $83411646832980074084959813698387619147$ | $14870031870853253057452923876908140649$ | $49528190073825835066912761353$ | $-15236753845519909685186978552$ | $-1276947094101718018052573343$ | $2152571835635560757770982197$ | $32582611121271603610$ |
| 29:4 | $86950338261502699239004400471359115543$ | $-39294041153017749030670332169536142305$ | $705614336028367463299973410$ | $-117197033372369966035615856$ | $5371037233369603853659133489$ | $-879393631417438903608693868$ | $1601038273907786985$ |
| 29:5 | $89261255150931828622142419351629130741$ | $-59689827860567746225013488811166949400$ | $-794922661836520735104505833$ | $212024923856181787427993182$ | $-2035707702580909729586105797$ | $-73977406748587891603047502$ | $5057616823227946$ |

### 6.6 Cells 30 through 39

| $t:i$ | $M_r$ | $M_b$ | $A_{00}$ | $A_{01}$ | $A_{10}$ | $A_{11}$ | $R_\rho$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 30:0 | $27320471112589988558727503978911791502$ | $24935403587980156957936137432417384593$ | $-24962557124737899013652843564$ | $8567905011656047952655882382$ | $-13098231647990953921912354285$ | $5801762166316540530303906573$ | $20094884003135646138$ |
| 30:1 | $34038393009092514841125060655295634686$ | $15949655206386547197424140788155130015$ | $-29312741720000491527675009399$ | $13803624749866248455227133676$ | $11613223506206828146213964743$ | $-374661866023474784190978210$ | $4549173637912603275$ |
| 30:2 | $81271486057374166042572444359566473421$ | $30862667287376828589971562618723476337$ | $71607756489674555505702729457$ | $-16339177581812352475119393126$ | $-43200837434783945047696309414$ | $12658870515339834548230440490$ | $23094812719205345445$ |
| 30:3 | $83335392035075178239400501897527794258$ | $14880710644136357339797890328384437220$ | $49519023656966947309454866270$ | $-15265234196656865120582242492$ | $-1109367632352269330755159934$ | $2119029462505285184802630365$ | $32085330035112958888$ |
| 30:4 | $86949752878741692594085063148074854889$ | $-39298433865383987360000589116212519842$ | $704342783537551233704836053$ | $-116956202340126960495653383$ | $5361619552248443707302009042$ | $-877692179715618622852716384$ | $1605564174124034404$ |
| 30:5 | $89262314997052595140513222708710325002$ | $-59690197812032507031889874052663620362$ | $-794479980206133456763694812$ | $211913540672410571276563709$ | $-2034413468008676326620349995$ | $-74003157761370740345061305$ | $5053698914837391$ |
| 31:0 | $27363357414819827800840669070910606043$ | $24964438223268793910812262147444224485$ | $-25021482752747843199418785782$ | $8586639977391768062389676761$ | $-13141485538894500054523101664$ | $5812099394258673602151132052$ | $20157239988992006566$ |
| 31:1 | $34107503821754232708539785994948965931$ | $15947780487230804139519571998988743052$ | $-29353898530633949653735676709$ | $13840753402839263010242075211$ | $11609773080135939212429612880$ | $-375224332669107313994039301$ | $4536736899450172993$ |
| 31:2 | $81189735325822709540453831751274296497$ | $30925887563125119522024321943907553868$ | $71686480675470846993460874429$ | $-16361131484274486107882859850$ | $-43118538691558775457577569039$ | $12629153552068766317549428808$ | $23063653148474025381$ |
| 31:3 | $83258993799714552201671827317662275975$ | $14891223077205740154673939529908878520$ | $49510796521625953822193312252$ | $-15294129331023749877005160786$ | $-944445179004238298728419339$ | $2086034131350601716842267496$ | $31602899496625509177$ |
| 31:4 | $86949168698169177100698887922771805698$ | $-39302818083443002287009999260345053093$ | $703075306318993345678028036$ | $-116716157381099992981466907$ | $5352229834431819725003837864$ | $-875995904876039349092776480$ | $1610155738210448261$ |
| 31:5 | $89263374286500664736152488828745989278$ | $-59690567891931741931058431168068194077$ | $-794037715277207901668799891$ | $211802254755852651061262661$ | $-2033121097843775734350644919$ | $-74028780603309860664907344$ | $5049783787768773$ |
| 32:0 | $27406337754467014562459712086382789456$ | $24993524656967663046289105197123465572$ | $-25080957935749596715672040272$ | $8605520205770808917861618632$ | $-13184867716122208038636928036$ | $5822481649356614624041053346$ | $20219997602756969972$ |
| 32:1 | $34176801077912585689357069107917277963$ | $15945902977564585274715936501896263139$ | $-29395595954773084519566185698$ | $13878202933835436508172715821$ | $11606267677941458348138929205$ | $-375778096427070784785714868$ | $4524293953455866837$ |
| 32:2 | $81107874576246538638246178807009603299$ | $30988957967906380988799618910489789104$ | $71765542554756717066735624728$ | $-16383185157787045375300495711$ | $-43033587027226656616561430333$ | $12598923588647175969208110176$ | $23032066779370386540$ |
| 32:3 | $83182450045336926546053911200159741976$ | $14901571881126826773751968945693690734$ | $49503511836239499486097755587$ | $-15323442326123419461252181390$ | $-782135524142213970213000893$ | $2053576211837404338379049747$ | $31134750855716707673$ |
| 32:4 | $86948585715863691485821711474204099513$ | $-39307193833024424208593713400185730012$ | $701811885888483610023803285$ | $-116476894936827890758104690$ | $5342867962765508186429108682$ | $-874304785046305156177230938$ | $1614813949272963954$ |
| 32:5 | $89264433019762050282656989424254398308$ | $-59690938099625571908042043404223977121$ | $-793595866445929657082686885$ | $211691065977272406244875110$ | $-2031830588080695370533947033$ | $-74054275664272756832896585$ | $5045871443779865$ |
| 33:0 | $27449412861271959720799701941408633312$ | $25022663116001902061806730399983029071$ | $-25140987208440594161346737354$ | $8624547071595855794265226364$ | $-13228381175122231884170472876$ | $5832909648390073244345849328$ | $20283163069929582704$ |
| 33:1 | $34246286393813419181931553853200183434$ | $15944022720510373446368203550175277775$ | $-29437842851726549570073000888$ | $13915978100427200336426485043$ | $11602708099601343223901521101$ | $-376323313832295561407351932$ | $4511842483550015456$ |
| 33:2 | $81025903304295878846890589919069013214$ | $31051875958485245379031258265900959841$ | $71844949064829795629733383648$ | $-16405340800818884274378182143$ | $-42946024531650403918096839435$ | $12568189303993427493967108059$ | $23000070551101777668$ |
| 33:3 | $83105758674700019845010959591699454815$ | $14911759719223768832839951291233137071$ | $49497173007368204395625754649$ | $-15353176377194772682952050342$ | $-622395135579378313364027066$ | $2021646237526538422461313861$ | $30680342286891776953$ |
| 33:4 | $86948003927921514980387229346534928474$ | $-39311561139848919780567869033251721774$ | $700552503869883677459391701$ | $-116238411469545585423195463$ | $5333533820732693615215740823$ | $-872618798493181475850136336$ | $1619539812611654574$ |
| 33:5 | $89265491197322119097959588968995325143$ | $-59691308434476064077500104898700296121$ | $-793154433109739335572886089$ | $211579974207683081754027346$ | $-2030541934725152966174781916$ | $-74079643332844386696242264$ | $5041961884605094$ |
| 34:0 | $27492583471908299325088731908456530976$ | $25051853830896244602932069384659404988$ | $-25201575194813527298094916558$ | $8643721973422061061255767760$ | $-13272028930291108619462079916$ | $5843384114448559598617235176$ | $20346742713618393879$ |
| 34:1 | $34315961409721670738927789887058606737$ | $15942139758411649707181113755020185629$ | $-29480648243027275846168227867$ | $13954083753085730152718298981$ | $11599095134277022376239848739$ | $-376860139957802967793643335$ | $4499380126052816508$ |
| 34:2 | $80943820994618152721805138664817946123$ | $31114639034613536579478028875350631476$ | $71924707182411034243685520881$ | $-16427600616134887624802320000$ | $-42855892608964287699693185429$ | $12536959214294625400005727403$ | $22967681024682975106$ |
| 34:3 | $83028917574286747266593796195930887036$ | $14921789207894906702463839847044063614$ | $49491783683666416687791395460$ | $-15383334799268719634046525796$ | $-465181154786446336917758594$ | $1990234904258001644509365334$ | $30239157300772240164$ |
| 34:4 | $86947423330456564207593383831901412419$ | $-39315920029528785718906571914686805425$ | $699297141994353934154427486$ | $-116000703462036789650031706$ | $5324227292449685247722173883$ | $-870937923601793952639179546$ | $1624334356327181443$ |
| 34:5 | $89266548819665594187007736387713340295$ | $-59691678895847225282591611867568986532$ | $-792713414667329083136237150$ | $211468979318346128825439451$ | $-2029255133794057885352177474$ | $-74104883996331996267009497$ | $5038055111955660$ |
| 35:0 | $27535850330102682216927145056694786362$ | $25081097035807034407077113398988795778$ | $-25262726609576282436552352212$ | $8663046333968917786412573278$ | $-13315814015717370379535838970$ | $5853905777117951026804083883$ | $20410742956688225860$ |
| 35:1 | $34385827790392028572311363190531287262$ | $15940254132840094416023730930615985589$ | $-29524021317067661264078815437$ | $13992524837659676024288951569$ | $11595429560493523814286611748$ | $-377388728458068867255655867$ | $4486904468132306035$ |
| 35:2 | $80861627120834797767501297081161812298$ | $31177244738220095811379288220133462288$ | $72004823925341175911451375845$ | $-16449966811479450573569379960$ | $-42763231981064083229297601503$ | $12505241674409080584801674325$ | $22934914388399443387$ |
| 35:3 | $82951924613700973982415950447749083884$ | $14931662917419995456125745656485125122$ | $49487347759946290853919186671$ | $-15413921029294881313395426815$ | $-310451392418273968591719289$ | $1959333068473223173801824506$ | $29810703350699688291$ |
| 35:4 | $86946843919600290804715745920085099761$ | $-39320270527568538611341262463156345761$ | $698045782099586939220905077$ | $-115763767417487915619287724$ | $5314948262661667861405211204$ | $-869262138874833723872175548$ | $1629198631947466685$ |
| 35:5 | $89267605887276555481151838981613491946$ | $-59692049483104995718458858770908854426$ | $-792272810518639099545528700$ | $211358081180770548110985811$ | $-2027970181315472602915099222$ | $-74129998040769933393346516$ | $5034151127519666$ |
| 36:0 | $27579214186756643645452246779597922609$ | $25110392968555180023294693972096266877$ | $-25324446259611215962866382284$ | $8682521600542830774825455233$ | $-13359739485935748577714281862$ | $5864475372670173772310054438$ | $20475170323963322217$ |
| 36:1 | $34455887225552178388438684670838853038$ | $15938365884602571732525186810444825837$ | $-29567971433877878101921506441$ | $14031306397932254359522679031$ | $11591712146317353733038392966$ | $-377909231612305179835681172$ | $4474413045882099162$ |
| 36:2 | $80779321145514626772713533740012290666$ | $31239690652607758897871502556536139658$ | $72085306354360985759994321065$ | $-16472441600275953997374108764$ | $-42668082691461990732792991310$ | $12473044879323410945413840052$ | $22901786463383988955$ |
| 36:3 | $82874777645052450784425238475682474708$ | $14941383372758900165932473805694009315$ | $49483869381344951857953572978$ | $-15444938628342611782367944403$ | $-158164323468790307634850470$ | $1928931745481501432082873256$ | $29394510527536614225$ |
| 36:4 | $86946265691501579772249749223789125798$ | $-39324612659365500771297904504977647058$ | $696798406129047340216879074$ | $-115527599859343223041382451$ | $5305696616738486641987074332$ | $-867591422931769064847198085$ | $1634133715075376246$ |
| 36:5 | $89268662400638441074254788950035023842$ | $-59692420195617242579727413234862213550$ | $-791832620064854170866849258$ | $211247279666712235032099641$ | $-2026687073328574339301696433$ | $-74154985850924440616850816$ | $5030249932962236$ |
| 37:0 | $27622675800070619073118557175018856096$ | $25139741870660065955364344480683070331$ | $-25386739045474781842388829551$ | $8702149245470670071198667988$ | $-13403808416692382681126314640$ | $5875093644256109093008640951$ | $20540031444488578152$ |
| 37:1 | $34526141430399037819263852587977022616$ | $15936475053747897856117479815093608012$ | $-29612508130052894177521978045$ | $14070433578259705982262072154$ | $11587943649532188667957724626$ | $-378421800367684896918780848$ | $4461903342325680736$ |
| 37:2 | $80696902520143651647470525964663419613$ | $31301974401657743313216404176967155718$ | $72166161574972932155181766181$ | $-16495027202341823871496360281$ | $-42570484109476793148629557628$ | $12440376865658400319015954062$ | $22868312709292118924$ |
| 37:3 | $82797474502330551145839263860085005953$ | $14950953054341495841471001809626295227$ | $49481352947603574518047919440$ | $-15476391283880018407641992893$ | $-8279082083432554740045586$ | $1899022107676356644631635823$ | $28990130336334476279$ |
| 37:4 | $86945688642326648544263788488555998812$ | $-39328946450210382165849160782649072208$ | $695554996131218203436058433$ | $-115292197331161184805318757$ | $5296472240670465771991710720$ | $-865925754508063339820765211$ | $1639140706058237152$ |
| 37:5 | $89269718360234048455533865665332838813$ | $-59692791032753753731918556353729584658$ | $-791392842708400214096615140$ | $211136574648173327374104014$ | $-2025405805883616851741653075$ | $-74179847810298427318355380$ | $5026351529925643$ |
| 38:0 | $27666235935670153816940811094129186905$ | $25169143987374436630261046961953127152$ | $-25449609962938559760159843002$ | $8721930766544601570586182087$ | $-13448023905721457408275382779$ | $5885761342101836325925561853$ | $20605333053850618829$ |
| 38:1 | $34596592146108393065700305425680733290$ | $15934581679573393226848086298364488975$ | $-29657641123834049332902969850$ | $14109911626294257088467030511$ | $11584124817812444803074820355$ | $-378926584382536776645559443$ | $4449372785343861980$ |
| 38:2 | $80614370685091293767750299792621166797$ | $31364093649041674763357154591268441439$ | $72247396739382204550331247230$ | $-16517725844618812633769344062$ | $-42470474934731041145796412294$ | $12407245513218049588578565517$ | $22834508230062276360$ |
| 38:3 | $82720013000766410355631335847598062335$ | $14960374398848535324202432228796908399$ | $49479803117467293835575291724$ | $-15508282812134748382277191961$ | $139244543943168266891823614$ | $1869595482707242538842048564$ | $28597134549047340827$ |
| 38:4 | $86945112768258946773904685039976558903$ | $-39333271925287858449063624158965121744$ | $694315534258853696455584429$ | $-115057556396472058421995787$ | $5287275021064260426610931505$ | $-864265112454399200110190247$ | $1644220730680049921$ |
| 38:5 | $89270773766545535739146189886082672040$ | $-59693161993886231406670885008068219180$ | $-790953477852940833867489098$ | $211025965997401555111098114$ | $-2024126375041892381104898700$ | $-74204584301136221253855392$ | $5022455920029430$ |
| 39:0 | $27709895366734365668059240760955011129$ | $25198599567720270164837511871658687650$ | $-25513064104572768654596100202$ | $8741867687478499356620810043$ | $-13492389073533703903384046780$ | $5896479223708328679531854641$ | $20671081996560553990$ |
| 39:1 | $34667241140358368397676206172590000913$ | $15932685800631218772726095658160983827$ | $-29703380320351287435037008589$ | $14149745895794858889389632489$ | $11580256388894788576346495697$ | $-379423732069536567057317614$ | $4436818745521845204$ |
| 39:2 | $80531725069572905520999845303329302085$ | $31426046097441455966722935714788929178$ | $72329019048515147039345715044$ | $-16540539761918189249442512612$ | $-42368093201928428142196516871$ | $12373658546576551865170484005$ | $22800387779747950458$ |
| 39:3 | $82642390936183048266198728387599847748$ | $14969649799983274916907705046059325205$ | $49479224813214965967290111984$ | $-15540617160540410647096762327$ | $284446118957884682491154063$ | $1840643351611761737744161473$ | $28215114127932435881$ |
| 39:4 | $86944538065499056828055854535697009510$ | $-39337589109677145131842217438397060453$ | $693080002768238061105747121$ | $-114823673638636651560521330$ | $5278104845138741866200987565$ | $-862609475735908971230331290$ | $1649374940877296132$ |
| 39:5 | $89271828620054422890528859352102621950$ | $-59693533078388285920668280032437813218$ | $-790514524903373891172649916$ | $210915453586889592452073293$ | $-2022848776875693753663872085$ | $-74229195704428299581734658$ | $5018563104870530$ |

### 6.7 Cells 40 through 49

| $t:i$ | $M_r$ | $M_b$ | $A_{00}$ | $A_{01}$ | $A_{10}$ | $A_{11}$ | $R_\rho$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 40:0 | $27753654874126719181275874128039941054$ | $25228108864525659490761599943224537184$ | $-25577106661373387824692922179$ | $8761961558376254726611346060$ | $-13536907064217212636170341114$ | $5907248054054720885454622338$ | $20737285228500302561$ |
| 40:1 | $34738090207867175896717014851795487300$ | $15930787454734496152384816710318090267$ | $-29749735817032415866885747578$ | $14189941849529127863167716608$ | $11576339090747653215353423155$ | $-379913390638922309595657865$ | $4424238533912154631$ |
| 40:2 | $80448965091608529193169605882485248405$ | $31487829487777154683902115794633265777$ | $72411035754113375210650944747$ | $-16563471197680572120381735106$ | $-42263376285885842716543067439$ | $12339623536698209729266107955$ | $22765965768409454378$ |
| 40:3 | $82564606084333037577970078259107459852$ | $14978781609233672525765471050009544177$ | $49479623225327922040600344682$ | $-15573398410272611911677234908$ | $427364565503141033638145216$ | $1812157346913241488099003275$ | $27843678214701135251$ |
| 40:4 | $86943964530264594985206696791295091444$ | $-39341898028352567919043020626616841363$ | $691848384018450815708305231$ | $-114590545660706270104969788$ | $5268961600720915318010259645$ | $-860958823431411171601629941$ | $1654604515479282150$ |
| 40:5 | $89272882921241592949504848692147052971$ | $-59693904285635429418171948466575756525$ | $-790075983265828084058118424$ | $210805037289374412098979253$ | $-2021573007468276637040444438$ | $-74253682399915999481893161$ | $5014673086023389$ |
| 41:0 | $27797515246528171927653725120490612738$ | $25257672134462719002075661206069685340$ | $-25641742924434046597585278630$ | $8782213956212307586577314743$ | $-13581581046251018446298668821$ | $5918068605805271330118527088$ | $20803949819434449017$ |
| 41:1 | $34809141170945610317236862112716150230$ | $15928886678963211802223821435418123421$ | $-29796717909186050169561739891$ | $14230505062270062109505094934$ | $11572373641738826387158822282$ | $-380395706141762025989203493$ | $4411629399709496698$ |
| 41:2 | $80366090157977820551096994938362758751$ | $31549441598443063825231314438331136086$ | $72493454160902028555778661927$ | $-16586522404750185226973812484$ | $-42156360906795862187555324313$ | $12305147902585586766969227417$ | $22731256268053925955$ |
| 41:3 | $82486656200223259398563701562722666250$ | $14987772136624996680508725077448976204$ | $49481003817306998741490800175$ | $-15606630778878704068558617118$ | $568038170610566577754779770$ | $1784129250688250164305890134$ | $27482453180869228535$ |
| 41:4 | $86943392158790113330649271241840695682$ | $-39346198706184129244409995180076869193$ | $690620660470638126104546522$ | $-114358169085283837286359928$ | $5259845176241870342999373593$ | $-859313134732653105975621543$ | $1659910660974003242$ |
| 41:5 | $89273936670587293250165710290203166322$ | $-59694275615005069637054749743531133708$ | $-789637852347659540233089238$ | $210694716977836641707506031$ | $-2020299062913821949612499704$ | $-74278044766096208466822782$ | $5010785865040085$ |
| 42:0 | $27841477280572754659323806025011995993$ | $25287289638086535511851667489965614165$ | $-25706978286663883790630278127$ | $8802626485324737022312292387$ | $-13626414213331931319091931910$ | $5928941659520144911827247039$ | $20871082955589663953$ |
| 42:1 | $34880395880064772220454537500891595197$ | $15926983509669904453704250349385582587$ | $-29844337095765201905483408661$ | $14271441223891270757185040805$ | $11568360750801174762209917647$ | $-380870823513302889253904677$ | $4398988527833407156$ |
| 42:2 | $80283099664171065458909789209155459877$ | $31610880244552063587935997041518044725$ | $72576281628830791473286637156$ | $-16609695646163362993655076053$ | $-42047083135696679654749291360$ | $12270238912951448285083651035$ | $22696273018612837428$ |
| 42:3 | $82408539017426267011634671266423984283$ | $14996623651462707033812886220678109985$ | $49483372330647291321903467640$ | $-15640318623005468299129837032$ | $706504592311746120660750937$ | $1756550992608370286233452429$ | $27131081735107343157$ |
| 42:4 | $86942820947327002343175232680021614345$ | $-39350491167938071033538313776136025985$ | $689396814687290285660375290$ | $-114126540554386172570387014$ | $5250755460732763386836778251$ | $-857672388943559477326122802$ | $1665294612300557665$ |
| 42:5 | $89274989868571136637542066697837888454$ | $-59694647065876503698236514524672411830$ | $-789200131557448421548460042$ | $210584492525499922541392659$ | $-2019026939317398422659036922$ | $-74302283180226034484127265$ | $5006901443450450$ |
| 43:0 | $27885541780985649048346413330205419118$ | $25316961639875182945000632338985210047$ | $-25772818244552619951160380824$ | $8823200777921259391813983591$ | $-13671409785215100164194276723$ | $5939868003870146635774930986$ | $20938691942303794929$ |
| 43:1 | $34951856214439521640506254963811845514$ | $15925077982485135638869747199182288317$ | $-29892604085318783794522576680$ | $14312756142564623166063165746$ | $11564301117596571977650132266$ | $-381338886616431827233111959$ | $4386313036414324204$ |
| 43:2 | $80199992994336218629189511257904245287$ | $31672143277188393981752435697306214768$ | $72659525575386492940381715326$ | $-16632993195951173382531458977$ | $-41935578400127637998987357659$ | $12234903687910297363468132042$ | $22661029433947000353$ |
| 43:3 | $82330252247377757323657822520048236311$ | $15005338383065487881512166749147742121$ | $49486734789980257175752312014$ | $-15674466441229099003433116704$ | $842800866344752846323144496$ | $1729414647960290346870687089$ | $26789222083714231119$ |
| 43:4 | $86942250892143394167502288064549215098$ | $-39354775438277433724829235261424213814$ | $688176829331525245093654152$ | $-113895656729307419105657547$ | $5241692343820832217336157445$ | $-856036565479486961549154463$ | $1670757633669188137$ |
| 43:5 | $89276042515672102681072839346743176953$ | $-59695018637630911918419561001424443707$ | $-788762820304995540293991448$ | $210474363805830270311118276$ | $-2017756632794925314526504039$ | $-74326398018327455909434900$ | $5003019822762191$ |
| 44:0 | $27929709560723828432948156299072289583$ | $25346688408270820854081646061379953012$ | $-25839268399984128671482395011$ | $8843938494598494257588674246$ | $-13716571008568811093679156595$ | $5950848435855539874398269076$ | $21006784206746810209$ |
| 44:1 | $35023524082628184518786518289337791668$ | $15923170132322742550194429940136754105$ | $-29941529802138638635869159835$ | $14354455748064403277553385336$ | $11560195432678097244669747659$ | $-381800038285278407702710383$ | $4373599974178495887$ |
| 44:2 | $80116769521221894154242719679833595221$ | $31733228582668925737709213860943014278$ | $72743193477976268333558160734$ | $-16656417339956071700137173753$ | $-41821881489949678883653578750$ | $12199149200685552552987537782$ | $22625538607869743756$ |
| 44:3 | $82251793578659627275339374520959123148$ | $15013918521488335946105930548465563515$ | $49491097508393002258289154343$ | $-15709078876991998794539001245$ | $976963413036293837535054888$ | $1702712435648035313042103870$ | $26456547140630148834$ |
| 44:4 | $86941681989524066566715104100526305057$ | $-39359051541762611578110652091332419385$ | $686960687166378133618870705$ | $-113665514290483608659862658$ | $5232655715725441953747497177$ | $-854405643866484689902431825$ | $1676301019410078355$ |
| 44:5 | $89277094612368538884884112706259231188$ | $-59695390329651351646024106863888251410$ | $-788325918001318987264770305$ | $210364330692535438187876123$ | $-2016488139473135276102893997$ | $-74350389655191951528108119$ | $4999141004461003$ |
| 45:0 | $27973981441119328836920300046146590087$ | $25376470215721897524700058165320486248$ | $-25906334462099838223363064003$ | $8864841324874870902963012926$ | $-13761901157844036483541576087$ | $5961883761029087289569282603$ | $21075367300715857707$ |
| 45:1 | $35095401423149055035186388923697769340$ | $15921259993384872464246729730010323207$ | $-29991125392610048431660798794$ | $14396546095182242415303240556$ | $11556044377650572682152719568$ | $-382254420368991810642104631$ | $4360846317726885327$ |
| 45:2 | $80033428606116237794994269914194104268$ | $31794134081812998403977604437562087264$ | $72827292876380436813404413204$ | $-16679970376662539608374381344$ | $-41706026563311103431358380604$ | $12162982279328642815445503975$ | $22589813320179474623$ |
| 45:3 | $82173160676268069555582989694614909360$ | $15022366218235622181691874820086568144$ | $49496467092934809256618251422$ | $-15744160721651054656522790518$ | $1109028044340399246869223562$ | $1676436716180923973930990771$ | $26132743783677287478$ |
| 45:4 | $86941114235770347549060654533426851009$ | $-39363319502851904300325546607386643668$ | $685748371054096713546056261$ | $-113436109937358353092508981$ | $5223645467254162396421695719$ | $-852779603740560584696047722$ | $1681926094852085190$ |
| 45:5 | $89278146159138161894888487643973022372$ | $-59695762141322751120223765803841058024$ | $-787889424058650771547887899$ | $210254393059564281983775271$ | $-2015221455489537366889932684$ | $-74374258464385110603613293$ | $4995264990010693$ |
| 46:0 | $28018358252025219423727620550112005397$ | $25406307338726479137572930028224276395$ | $-25974022249213341405134690336$ | $8885910987737561074031440929$ | $-13807403536159266476578110379$ | $5972974793723456642904999093$ | $21144448903506784399$ |
| 46:1 | $35167490205114258821748086351900825458$ | $15919347599166797777115758073158658980$ | $-30041402231774048501012861084$ | $14439033367257301669017186680$ | $11551848625329508379748065899$ | $-382702173775724709097745248$ | $4348048968702978041$ |
| 46:2 | $79949969598781611129463711146414095490$ | $31854857729220876361786207308960895404$ | $72911831375274414308765216370$ | $-16703654618041704922529052266$ | $-41588047152740084812208553134$ | $12126409608446514002264985659$ | $22553866042693630307$ |
| 46:3 | $82094351180866138184952004790492431188$ | $15030683586964064741981263497803586311$ | $49502850450321216496292474267$ | $-15779716917642235481003506196$ | $1239029971015642031996774025$ | $1650579989650620091009497098$ | $25817512153961439982$ |
| 46:4 | $86940547627200020663492453144231731338$ | $-39367579345902065017419588226947894572$ | $684539863955442711104862176$ | $-113207440388249651532524079$ | $5214661489798876368439781549$ | $-851158424846953494319873536$ | $1687634217232642929$ |
| 46:5 | $89279197156458058702715732582257336992$ | $-59696134072031903352981805390580933543$ | $-787453337890433471980481748$ | $210144550781106127489259109$ | $-2013956576992380220967464400$ | $-74398004818251223129876387$ | $4991391780853296$ |
| 47:0 | $28062840831964343508349922926373121911$ | $25436200057876727176393214060070169688$ | $-26042337690777639919011527082$ | $8907149232203836978573235679$ | $-13853081476201170570426995568$ | $5984122357283138117754311986$ | $21214036824864547802$ |
| 47:1 | $35239792428881564916178767354606124485$ | $15917432982461510532770219440338956377$ | $-30092371930110259308759531305$ | $14481923879826383293302209890$ | $11547608839898525202772559410$ | $-383143438516857958627866462$ | $4335204750844120732$ |
| 47:2 | $79866391837385017583929842940350537987$ | $31915397512560856491101916198933372005$ | $72996816646819145615293623283$ | $-16727472390409978019216084181$ | $-41467976171346372374310670453$ | $12089437730934249564330817590$ | $22517708945276531662$ |
| 47:3 | $82015362708020189884739389274849103068$ | $15038872704175566556038737627778552018$ | $49510254792846231084776026229$ | $-15815752561766533113187523667$ | $1367003809923887537970272420$ | $1625134893700433263427113028$ | $25510564995595875614$ |
| 47:4 | $86939982160147230958411980657607712369$ | $-39371831095168844621290951814011591572$ | $683335148928998966890906367$ | $-112979502380217802547287202$ | $5205703675331918783832578607$ | $-849542087039411074260304554$ | $1693426776640134693$ |
| 47:5 | $89280247604804687846485496098604127303$ | $-59696506121167460033989328449135461531$ | $-787017658911316900230525617$ | $210034803731590139958773510$ | $-2012693500140615362147894140$ | $-74421629087917850364415782$ | $4987521378409190$ |
| 48:0 | $28107430028280903279574577827276736299$ | $25466148657904547015097448977313115803$ | $-26111286829406499873092085966$ | $8928557837897267476503616257$ | $-13898938341141653558257558389$ | $5995327284301024348355950585$ | $21284139008015041081$ |
| 48:1 | $35312310126724758253542395296788043470$ | $15915516175364095153185907747240088231$ | $-30144046340549357397802403073$ | $14525224084398869942439685512$ | $11543325677065326454524861759$ | $-383578353751501140328254553$ | $4322310406910729452$ |
| 48:2 | $79782694648424200091829581772920303232$ | $31975751451865045229304611604751834401$ | $73082256433319699647815776311$ | $-16751426035301780129001768170$ | $-41345845919115583140819313714$ | $12052073049709706565932627796$ | $22481353901854053519$ |
| 48:3 | $81936192847419581556646149026990218157$ | $15046935609899886229024512885958713159$ | $49518687644513559806173180677$ | $-15852272908602463334656029034$ | $1492983591434541975975015767$ | $1600094201489824272443158962$ | $25211627033116586146$ |
| 48:4 | $86939417830962391598108888450432672163$ | $-39376074774807532520400104384745565442$ | $682134209130482349950043800$ | $-112752292668934410706425290$ | $5196771916402246160015509723$ | $-847930570279473361319366276$ | $1699305196990088011$ |
| 48:5 | $89281297504653880608432799891593956064$ | $-59696878288119925458407022697851606404$ | $-786582386537154775451987071$ | $209925151785684695735761317$ | $-2011432221103860667622277304$ | $-74445131643300375738512488$ | $4983653784077216$ |
| 49:0 | $28152126697294963486000919718150893042$ | $25496153427728431385926893434199166370$ | $-26180875822951447212405296752$ | $8950138615639179835518568335$ | $-13944977525571887378731168973$ | $6006590416859809105722976835$ | $21354763532780946957$ |
| 49:1 | $35385045363523209561368702491034690415$ | $15913597209275877900844476008379698857$ | $-30196437565724737450506287677$ | $14568940572361621704758848775$ | $11538999784216290714494205486$ | $-384007057831305217856656784$ | $4309362595487395814$ |
| 49:2 | $79698877346649339651953475886509846731$ | $32035917598833807747085463571978290091$ | $73168158549951829649611557522$ | $-16775517910356477517510284106$ | $-41221688089280390504582561985$ | $12014321829447256735424267078$ | $22444812496408787428$ |
| 49:3 | $81856839162078977603240832075393712476$ | $15054874308367125276203824434242122947$ | $49528156847398067922921335333$ | $-15889283374050550507802730568$ | $1617002766919197047486166371$ | $1575450819656878109811307357$ | $24920434384149337864$ |
| 49:4 | $86938854636012091131454256248670215074$ | $-39380310408873493822374759545205424469$ | $680937027812062380127193886$ | $-112525808028552477059078128$ | $5187866106131636295026629844$ | $-846323854635761988802966155$ | $1705270937036616826$ |
| 49:5 | $89282346856480842209396986526116836006$ | $-59697250572281650477312603382569209117$ | $-786147520185001410466205255$ | $209815594818296756008103172$ | $-2010172736062363979403356601$ | $-74468512853106536240150146$ | $4979788999234792$ |

### 6.8 Cells 50 through 59

| $t:i$ | $M_r$ | $M_b$ | $A_{00}$ | $A_{01}$ | $A_{10}$ | $A_{11}$ | $R_\rho$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 50:0 | $28196931704459951513143535139568044909$ | $25526214660501523221699022955722938201$ | $-26251110946635986110714180494$ | $8971893408055829423972120151$ | $-13991202456453918415161756424$ | $6017912606778365533831872827$ | $21425918618784333189$ |
| 50:1 | $35458000237471305776901509923197955875$ | $15911676114908351419710979100017829319$ | $-30249557965473371438993648939$ | $14613080079019204504597645481$ | $11534631800569759479789045796$ | $-384429688345624858918050909$ | $4296357887649591782$ |
| 50:2 | $79614939234980283392039975097885941478$ | $32095894036148877866416186484398883064$ | $73254530887556455368503189245$ | $-16799750390219673631502023197$ | $-41095533774753792824355206768$ | $11976190198307901521206038830$ | $22408096028949752474$ |
| 50:3 | $81777299187522593154177039915103034850$ | $15062690768670028055036429056701339699$ | $49538670568249030516720284338$ | $-15926789539015440570925974009$ | $1739094216322455668820770859$ | $1551197786281325627852729846$ | $24636734005064817343$ |
| 50:4 | $86938292571679001407453302003840153112$ | $-39384538021322702976685403767872742990$ | $679743588321685503909877058$ | $-112300045251577563157294726$ | $5178986138210917833084396654$ | $-844721920283274990992307928$ | $1711325491420600937$ |
| 50:5 | $89283395660760153000184752079812425295$ | $-59697622973046826470756550993588961948$ | $-785713059273108409421573688$ | $209706132704571242685167969$ | $-2008915041206966862874533003$ | $-74491773084840934364932555$ | $4975927025238029$ |
| 51:0 | $28241845924523233529588671092495038326$ | $25556332653660923182945351770320444901$ | $-26321998595248679688203203419$ | $8993824090201735295243194280$ | $-14037616594090468491398694918$ | $6029294715863269971885285618$ | $21497612628738804022$ |
| 51:1 | $35531176880808431609430347691663142755$ | $15909752922286872509656391176369446966$ | $-30303420164596349471332860015$ | $14657649487775080260892589344$ | $11530222357328094658508381967$ | $-384846382167069340847068916$ | $4283292763489325220$ |
| 51:2 | $79530879604419229889547338644785052718$ | $32155678876795104119296454680104610288$ | $73341381415502177071585122842$ | $-16824125867459048770271912162$ | $-40967413474610477449015747004$ | $11937684149663200232377836364$ | $22371215521451213479$ |
| 51:3 | $81697570430949670457489514984267126103$ | $15070386925416103227971448488155638026$ | $49550237305347124605213041622$ | $-15964797153231522416006541481$ | $1859290255795572069123556874$ | $1527328268850521471619823440$ | $24360283167519955677$ |
| 51:4 | $86937731634361786132315496827860941489$ | $-39388757636012273905209723326487245922$ | $678553874102404969592773173$ | $-112075001148740018370794257$ | $5170131906896229444875576326$ | $-843124747502687145753268664$ | $1717470391756166490$ |
| 51:5 | $89284443917965769649817849736430426789$ | $-59697995489811479343329220885504768209$ | $-785279003220921376883843712$ | $209596765319890416387679107$ | $-2007659132739068511757422886$ | $-74514912704809530729665055$ | $4972067863421846$ |
| 52:0 | $28286870241689848710149278653600058544$ | $25586507708978268024034787975339995817$ | $-26393545285396790952555742903$ | $9015932570199655809659006890$ | $-14084223433113567275387060239$ | $6040737616165642747378027131$ | $21569854071834127953$ |
| 52:1 | $35604577460570221693686457005574386321$ | $15907827660754131091096359678140506314$ | $-30358037060890091810886481080$ | $14702655834459660035357180612$ | $11525772077828582504785093657$ | $-385257275497482413033865812$ | $4270163608492728451$ |
| 52:2 | $79446697733958798460968982262919821054$ | $32215270263390794948208784544693290634$ | $73428718184616082007064368027$ | $-16848646753494973806300503787$ | $-40837357100603089574021875583$ | $11898809543810611627194571587$ | $22334181723755621212$ |
| 52:3 | $81617650370380455675390887858005342771$ | $15077964679369587211844663092660341579$ | $49562865895627524387571560318$ | $-16003312139238188166767471999$ | $1977622645380349593708577248$ | $1503835562230621364430214296$ | $24090848963932485107$ |
| 52:4 | $86937171820475010062751033124496788257$ | $-39392969276700986648249873388803764619$ | $677367868691716248178514990$ | $-111850672548868260349527944$ | $5161303307005308351843498871$ | $-841532316679655804672956583$ | $1723707207757107639$ |
| 52:5 | $89285491628571026330676006509733629213$ | $-59698368121973463542142873754600086878$ | $-784845351449076638309593816$ | $209487492539873256541645485$ | $-2006405006870589798814296942$ | $-74537932078124117442767826$ | $4968211515100085$ |
| 53:0 | $28332005549789485956494524849063315570$ | $25616740132611606823145398456136471234$ | $-26465757657822242689744896213$ | $9038220789897695268455995973$ | $-14131026503492674053688672987$ | $6052242190243482889442347395$ | $21642651607216372549$ |
| 53:1 | $35678204179361832994379569190901361934$ | $15905900358973388110936505325729180330$ | $-30413421833459754252520962758$ | $14748106311811407130798448772$ | $11521281577693262253375425899$ | $-385662503914393031118987052$ | $4256966709762169022$ |
| 53:2 | $79362392890485407906983247033790471504$ | $32274666367526614436402729538722133084$ | $73516549330183252759429758951$ | $-16873315479546160991846808991$ | $-40705393983700971388560231159$ | $11859572109678002066147305152$ | $22297005119436121574$ |
| 53:3 | $81537536453781912012114999603366190973$ | $15085425898083280891196046577583140845$ | $49576565522081908086191912728$ | $-16042340596511129321366595935$ | $2094122596731512489614111297$ | $1480713086645045616836575242$ | $23828207840073035643$ |
| 53:4 | $86936613126449048830253036681955003405$ | $-39397172967049810553314799797478590446$ | $676185555720897947011668643$ | $-111627056298763098600331533$ | $5152500233913807926573066747$ | $-839944608304132160640803717$ | $1730037548404970311$ |
| 53:5 | $89286538793048635900545551632492150699$ | $-59698740868932456097132645479721537874$ | $-784412103379397971855638392$ | $209378314240374843567648641$ | $-2005152659823937471605318399$ | $-74560831568706772325174046$ | $4964357981565622$ |
| 54:0 | $28377252752446790034052261775153254057$ | $25647030235158603000073926340365283354$ | $-26538642479781718258384942834$ | $9060690725544050027618353664$ | $-14178029371562967916123258186$ | $6063809331429679501934792456$ | $21716014047566692186$ |
| 54:1 | $35752059276154018803797306219540988518$ | $15903971044931479927288704813565867627$ | $-30469587951326911305346539707$ | $14794008274117478630977567304$ | $11516751464977759514993294842$ | $-386062202417980514616480797$ | $4243698252075054247$ |
| 54:2 | $79277964328677888795070782149461013895$ | $32333865389112969086379835398651051591$ | $73604883075015534115804918351$ | $-16898134497590651020386109488$ | $-40571552880639656332483232582$ | $11819977446515217864411368064$ | $22259695931614490898$ |
| 54:3 | $81457226098172372415523742106282218034$ | $15092772416520300933588538233865947042$ | $49591345721452664556936961977$ | $-16081888805756349009932573763$ | $2208820780866504936461070239$ | $1457954385662167617938260356$ | $23572145153085624200$ |
| 54:4 | $86936055548729999391174810187934259707$ | $-39401368730622424033730718246683040902$ | $675006918914358163717526158$ | $-111404149263073091252479564$ | $5143722583551644104161921446$ | $-838361602969677903313483786$ | $1736463063160604296$ |
| 54:5 | $89287585411870691081584211707871227042$ | $-59699113730089950683580941816048159638$ | $-783979258434893351477376544$ | $209269230297485743156819689$ | $-2003902087831968492624098492$ | $-74583611539294294074853885$ | $4960507264090483$ |
| 55:0 | $28422612763255086631496414516519503541$ | $25677378331711090974532458856334945961$ | $-26612206647492790975053434050$ | $9083344388479920747479165849$ | $-14225235641074507325443119724$ | $6075439944105888560868461997$ | $21789950362782034569$ |
| 55:1 | $35826145027102818905430666818363057585$ | $15902039745941586488364731794639634073$ | $-30526549182344195299173477955$ | $14840369242020712190347443729$ | $11512182340319206440688411935$ | $-386456505478599416776589275$ | $4230354313771056972$ |
| 55:2 | $79193411290901251775717299391873891979$ | $32392865555735815997807191540226475742$ | $73693727732590260805562784729$ | $-16923106281342471334551395464$ | $-40435861980470087082335589827$ | $11780031025570756051318975623$ | $22222264128730743412$ |
| 55:3 | $81376716688704300947890325777695187158$ | $15100006037665796384827412587545994132$ | $49607216392233102848306091731$ | $-16121963233373871683842480500$ | $2321747335932372772810156779$ | $1435553124194025752431357357$ | $23322454753364137563$ |
| 55:4 | $86935499083779591097460753009211143521$ | $-39405556590885730923896344090038554390$ | $673831942088986228585037511$ | $-111181948324170925194160418$ | $5134970252399370342227418927$ | $-836783281372787213418762976$ | $1742985443221079966$ |
| 55:5 | $89288631485508665636212484493926707118$ | $-59699486704849251706770207862573615017$ | $-783546816039751701269307474$ | $209160240587531392624881724$ | $-2002653287137954523138666304$ | $-74606272351442618467596439$ | $4956659363925958$ |
| 56:0 | $28468086505953618529386377581437238305$ | $25707784741911017276976859730517682401$ | $-26686457188648038130260883827$ | $9106183825851136347916358761$ | $-14272648954262982880688935343$ | $6087134943982470171493002814$ | $21864469683761157108$ |
| 56:1 | $35900463746393715343354833238869811899$ | $15900106488645760389945786656793737483$ | $-30584319602430196570611024708$ | $14887196907500101035801923696$ | $11507574797083332763638838628$ | $-386845547084911239341808810$ | $4216930862459017744$ |
| 56:2 | $79108733007095532664314350430440339379$ | $32451665122020813292543479108053735450$ | $73783091710259793036377374685$ | $-16948233327244336257390846292$ | $-40298348911097175256743246328$ | $11739738191751696658783978892$ | $22184719430261025397$ |
| 56:3 | $81296005577724296223092306310832792649$ | $15107128533128689879104211038088662905$ | $49624187802988020039462069586$ | $-16162570536098451411568510670$ | $2432931874980051915007444904$ | $1413503086507724376855726691$ | $23079100542772226144$ |
| 56:4 | $86934943728075097382938426667588142635$ | $-39409736571210373457755518499377811563$ | $672660609153509784094035116$ | $-110960450382030809867802687$ | $5126243137484580869926982778$ | $-835209624312214047363169546$ | $1749606422823961092$ |
| 56:5 | $89289677014433415539941960174829855610$ | $-59699859792615468408669484118909340034$ | $-783114775619339661001163535$ | $209051344987071489335675154$ | $-2001406253995546550068508019$ | $-74628814365531215686175925$ | $4952814282302707$ |
| 57:0 | $28513674914608387841233070164500730010$ | $25738249790007796915396810426111016100$ | $-26761401264999166764006773594$ | $9129211121339054911597592563$ | $-14320272992942810854559225069$ | $6098895258384687847495071748$ | $21939581306299474762$ |
| 57:1 | $35975017787111139831547177854614237632$ | $15898171299017213655318775805777796662$ | $-30642913605138592401778355245$ | $14934499139032255257239262332$ | $11502929421510814089615233679$ | $-387229460792672082094535987$ | $4203423750534275998$ |
| 57:2 | $79023928694659633079382760705723513233$ | $32510262369005724756929173212563092501$ | $73872983512532850377482812501$ | $-16973518155476794943933536649$ | $-40159040745797936897815730650$ | $11699104165265181197408677452$ | $22147071312380759498$ |
| 57:3 | $81215090083809432960757388550845929452$ | $15114141643733510810333167866206575613$ | $49642270601009573954777980934$ | $-16203717565824919689473676797$ | $2542403493737023525528007427$ | $1391798174251063899143908879$ | $22841765269443931806$ |
| 57:4 | $86934389478109248060127533680260258401$ | $-39413908694871241896818463134736261025$ | $671492904107857150840944070$ | $-110739652354106875116816117$ | $5117541136378341969065414792$ | $-833640612688304664112185763$ | $1756327780601025788$ |
| 57:5 | $89290721999115180151150916163690850908$ | $-59700232992795508996560620320593548004$ | $-782683136600198362803335493$ | $208942543372899381185624963$ | $-2000160984668739655231867587$ | $-74651237940767468869525757$ | $4948972020430879$ |
| 58:0 | $28559378933796702167304999223427059962$ | $25768773804917116826183316541852282062$ | $-26837046175013252280339637535$ | $9152428395911327243438596179$ | $-14368111479623339836703943710$ | $6110721826545378169890334801$ | $22015294695096397223$ |
| 58:1 | $36049809542134257257241126749499553842$ | $15896234202362358830977938009161635022$ | $-30702345911576172634996981585$ | $14982283986941722742075817089$ | $11498246792862966243620616801$ | $-387608379774227394926432172$ | $4189828710496648019$ |
| 58:2 | $78938997558330073309414097613344244916$ | $32568655603520982383775579085414751250$ | $73963411744428777489782742298$ | $-16998963310984268478673370424$ | $-40017964009710021661052604412$ | $11658134043239836413679192163$ | $22109329013570332828$ |
| 58:3 | $81133967490778998610450203953480066950$ | $15121047080102395211713715457069377598$ | $49661475821324039863777523788$ | $-16245411374626174449148849290$ | $2650190778369900705322289939$ | $1370432404493821357577315337$ | $22610229160421215950$ |
| 58:4 | $86933836330390142222569355666853458114$ | $-39418072985047980833823986275039123191$ | $670328811042524929664517819$ | $-110519551175212563579681314$ | $5108864147191651033027260912$ | $-832076227502335346809600156$ | $1763151340983633953$ |
| 58:5 | $89291766440023583377817468880290340081$ | $-59700606304798074793510475109745738375$ | $-782251898410040218955486700$ | $208833835622041459140650227$ | $-1998917475431837926301016822$ | $-74673543435191033973044461$ | $4945132579500218$ |
| 59:0 | $28605199518795525482912580046903466152$ | $25799357120281219296545792557931048564$ | $-26913399356603267922516108764$ | $9175837808593130089383328031$ | $-14416168178648968590346376609$ | $6122615599904306258231412115$ | $22091643297116069001$ |
| 59:1 | $36124841445059990081796312729226174618$ | $15894295223322600730091601017612825122$ | $-30762631580685170285076610408$ | $15030559688948439838543481043$ | $11493527483566877101119318703$ | $-387982436868767206275625032$ | $4176141350058699794$ |
| 59:2 | $78853938790054571785727645340994427576$ | $32626843157578302763750165043172825773$ | $74054385114906017732450227434$ | $-17024571364518452755864588229$ | $-39875144686282006431425057049$ | $11616832801325650023146922810$ | $22071501540160934765$ |
| 59:3 | $81052635046680641042483112010481489274$ | $15127846523227333914861766982813156950$ | $49681814896065706315926984862$ | $-16287659219972195005602477968$ | $2756321813229085991073560384$ | $1349399907785990915710360194$ | $22384316405595369881$ |
| 59:4 | $86933284281441161747727461124186700504$ | $-39422229464825492197898529271854791254$ | $669168314137950790313880587$ | $-110300143797401008229448405$ | $5100212068571923151905765076$ | $-830516449855855272094785774$ | $1770078975662051993$ |
| 59:5 | $89292810337627634841220523551519465847$ | $-59700979728033654410595883974828440104$ | $-781821060477745720732473888$ | $208725221611756551817057332$ | $-1997675722569419508806698193$ | $-74695731205678181030660725$ | $4941295960680177$ |

### 6.9 Cells 60 through 69

| $t:i$ | $M_r$ | $M_b$ | $A_{00}$ | $A_{01}$ | $A_{10}$ | $A_{11}$ | $R_\rho$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 60:0 | $28651137635773737672960383046145546439$ | $25830000074530699341408431164602518650$ | $-26990468389935163201313536490$ | $9199441557259498179764040530$ | $-14464446897364000075266150564$ | $6134577542414429854394208006$ | $22168627428598495858$ |
| 60:1 | $36200115971154290832077483792605750655$ | $15892354385875874883066684463789593066$ | $-30823786019906088603233498624$ | $15079334675921001392872995493$ | $11488772059360070149966065790$ | $-388351764633397544425896017$ | $4162357147033356139$ |
| 60:2 | $78768751568860363067173122754080132714$ | $32684823387767246064590370470619336992$ | $74145912440366213051662816848$ | $-17050344913699599148561030460$ | $-39730608223677346860384031996$ | $11575205295270906144855313168$ | $22033597671818445531$ |
| 60:3 | $80971089962749900371615278135887424995$ | $15134541625032756840379193467801773336$ | $49703299664234887288993479243$ | $-16330468570158874385151786221$ | $2860824188568184349110746991$ | $1328694926234188112655273471$ | $22163857904698040731$ |
| 60:4 | $86932733327800885395557250216269688490$ | $-39426378157194434986833954380039366026$ | $668011397663891397535383133$ | $-110081427189846385757602515$ | $5091584799699504974802697393$ | $-828961260950034480563066302$ | $1777112605101164579$ |
| 60:5 | $89293853692395731036618720891736813452$ | $-59701353261914517940788629794555535768$ | $-781390622233360248261912055$ | $208616701219535322097999171$ | $-1996435722376301798536418266$ | $-74717801607946116908791312$ | $4937462165120022$ |
| 61:0 | $28697194261988409827669868636628566709$ | $25860703010947851150770308198884023032$ | $-27068261000313832712848078657$ | $9223241879449407331755715811$ | $-14512951487303084554477385984$ | $6146608630855302492693539927$ | $22246243260473692341$ |
| 61:1 | $36275635638332714422781804486715745100$ | $15890411713337928469803534498207354227$ | $-30885824996238044684977137265$ | $15128617577844883674190198458$ | $11483981079434797056643430336$ | $-388716495395086256185200042$ | $4148471443989240832$ |
| 61:2 | $78683435060717163593794399587073014146$ | $32742594674659599614569096437030699655$ | $74238002648235491049096880114$ | $-17076286584096220475140699802$ | $-39584379541124374150017344945$ | $11533256262474882876269853419$ | $21995625966963555508$ |
| 61:3 | $80889329412342052954050881533165053840$ | $15141134008928547039836927617666515993$ | $49725942381857798494115645381$ | $-16373847109955892240207460136$ | $2963725008231373769908372645$ | $1308311811597322274489631946$ | $21948690964983739423$ |
| 61:4 | $86932183466023003497888159421871505875$ | $-39430519085051721751874405017411127711$ | $666858045978805425982574014$ | $-109863398338726236600939637$ | $5082982240284215602845813522$ | $-827410642085016902295070748$ | $1784254200115129052$ |
| 61:5 | $89294896504795656490917537533448600635$ | $-59701726905854711174408099761607263811$ | $-780960583108090891347939533$ | $208508274323099665777123271$ | $-1995197471157506773674723837$ | $-74739754996557289641834852$ | $4933631193948950$ |
| 62:0 | $28743370385985205735189043970936356980$ | $25891466277731599895729378806426150622$ | $-27146785061150403550299263248$ | $9247241053202284863739597562$ | $-14561685845408133835895843077$ | $6158709855153854223355231991$ | $22324500984534163365$ |
| 62:1 | $36351403008171388880993582966967802819$ | $15888467228363339210670469622444424099$ | $-30948764647714526830139500052$ | $15178417230015223462482727276$ | $11479155096582059761687699374$ | $-389076761303544070345034084$ | $4134479442661453050$ |
| 62:2 | $78597988418394691639845779148219500623$ | $32800155422221461842921702532497565201$ | $74330664780624643010922294313$ | $-17102399030323805485654601911$ | $-39436483035205190336475324238$ | $11490990323515103092743939077$ | $21957594768126558577$ |
| 62:3 | $80807350529835148347563082621384551422$ | $15147625270353583394918769825441162345$ | $49749755732566867828973080568$ | $-16417802746483309949771539957$ | $3065050897302426056626553327$ | $1288245023402547951203641347$ | $21738659014356536538$ |
| 62:4 | $86931634692676233233808108944725709293$ | $-39434652271201011860173389207364990814$ | $665708243529241615875040149$ | $-109646054247104742508586237$ | $5074404290561914269013280682$ | $-825864574659278391856132037$ | $1791505783503661361$ |
| 62:5 | $89295938775294584917334655294585927595$ | $-59702100659270049836049759456663619098$ | $-780530942534303281215956721$ | $208399940800402112221072224$ | $-1993960965228226466037026643$ | $-74761591724923674438356918$ | $4929803048276192$ |
| 63:0 | $28789667007803023450174843718148437338$ | $25922290228064056394382436444713911046$ | $-27226048597013359865429067704$ | $9271441397917648585822344414$ | $-14610653915272619057479312316$ | $6170882218712796684082412762$ | $22403410983548170721$ |
| 63:1 | $36427420686949532292139540746395810184$ | $15886520952946267382041581144326984197$ | $-31012621495313391644169319538$ | $15228742679464253928601759376$ | $11474294657335466119246066121$ | $-389432694385104561247459747$ | $4120376198104750078$ |
| 63:2 | $78512410781314644890571279608740378183$ | $32857504057232896494781848023622188729$ | $74423907998070040232827474211$ | $-17128684937163161092836271122$ | $-39286942586076754360629056831$ | $11448411983648012370339462692$ | $21919512207235511345$ |
| 63:3 | $80725150409503070412025464222200548239$ | $15154016977309915711759902336551788043$ | $49774752838620926669398271433$ | $-16462343615327056184830770995$ | $3164828009709535021043276228$ | $1268489127082418351171880673$ | $21533611329035488364$ |
| 63:4 | $86931087004344234486285046361648036428$ | $-39438777738353201559855418623205006698$ | $664561974849231821847062497$ | $-109429391934816952643605809$ | $5065850851291094563367478440$ | $-824323040168989727636427381$ | $1798869431752783556$ |
| 63:5 | $89296980504359080367073672786076660206$ | $-59702474521578113842898019407138967736$ | $-780101699945518433133328207$ | $208291700529625227042539975$ | $-1992726200913788570751956075$ | $-74783312145311041446637040$ | $4925977729191121$ |
| 64:0 | $28836085139182994388439485530498279270$ | $25953175220178733394331573799646442968$ | $-27306059786766117238104718635$ | $9295845275238601681680089576$ | $-14659859688414196061050267785$ | $6183126738746907991994339139$ | $22482983836033145569$ |
| 64:1 | $36503691326724715593931630017739200259$ | $15884572908420935796580658436307276326$ | $-31077412455320910736630813181$ | $15279603191634024704333118519$ | $11469400302115026840707431834$ | $-389784426597669651683642882$ | $4106156612575321594$ |
| 64:2 | $78426701275397035880276504300517483206$ | $32914639028715021602993188729587083020$ | $74517741583357280489210053847$ | $-17155147020699037943317987600$ | $-39135781563617864348964744420$ | $11405525634282035146729977702$ | $21881386210836684657$ |
| 64:3 | $80642726104357401607260981893123549772$ | $15160310670887680354969331937295692897$ | $49800947272385663242128912065$ | $-16507478086903987977555985549$ | $3263082035780549078911680972$ | $1249038792134081266357673928$ | $21333402774911373178$ |
| 64:4 | $86930540397625526275305226922299342262$ | $-39442895509126910872392051898459477988$ | $663419224559689007936048136$ | $-109213408438353949309781025$ | $5057321823749504964784529777$ | $-822786020207384530866759786$ | $1806347276803012369$ |
| 64:5 | $89298021692455098378016191481283003516$ | $-59702848492198241584332511612581447135$ | $-779672854776409599861253059$ | $208183553389181016775627522$ | $-1991493174549622193750612787$ | $-74804916608843205367766505$ | $4922155237763362$ |
| 65:0 | $28882625803781961101711905722004321148$ | $25984121617430463528341982668881659272$ | $-27386826966793757541260791959$ | $9320455089959937936070277621$ | $-14709307205576635375459395951$ | $6195444446627461971773853413$ | $22563230321171741807$ |
| 65:1 | $36580217626442125363731079838823112938$ | $15882623115461832247409735803384136651$ | $-31143154852170719498291942614$ | $15331008257305591682603703078$ | $11464472565371005519654371503$ | $-390132089886790465958871904$ | $4091815429126503177$ |
| 65:2 | $78340859012900782159400079949211534949$ | $32971558807364392636531909861217808242$ | $74612174945429702257143838635$ | $-17181788029479731744153521368$ | $-38983022833496129723433975904$ | $11362335554422032074760488244$ | $21843224505246455045$ |
| 65:3 | $80560074624956814761767166347532842864$ | $15166507865780868572946389009538137317$ | $49828353068295715284576048195$ | $-16553214773087761098130964039$ | $3359838209743621176566985627$ | $1229888790301280689387906108$ | $21137893561801162838$ |
| 65:4 | $86929994869133403762852180004133821280$ | $-39447005606048967336780014663871533427$ | $662279977367810142163620936$ | $-108998100810748944489156692$ | $5048817109730795442721115075$ | $-821253496464132060103710527$ | $1813941507888126869$ |
| 65:5 | $89299062340047987120442267186099274428$ | $-59703222570551524222737233264583622803$ | $-779244406462799135893221979$ | $208075499257710335545281335$ | $-1990261882481223736424469626$ | $-74826405465506257004006931$ | $4918335575042902$ |
| 66:0 | $28929290037390558729048051943111608768$ | $26015129788367060345678345317558312525$ | $-27468358634321737130107810948$ | $9345273290961640041075571481$ | $-14759000558062068206164444020$ | $6207836388235075662458246109$ | $22644161423875525611$ |
| 66:1 | $36657002333079138137105052587743103419$ | $15880671594083628557902943528008917516$ | $-31209866431779625767493440734$ | $15382967599796453705374753640$ | $11459511975727937823691500928$ | $-390475816242956715904574819$ | $4077347224902882108$ |
| 66:2 | $78254883092258444503078461477083887100$ | $33028261884994534528850530727045751804$ | $74707217623384051616398811778$ | $-17208610745698390110230397037$ | $-38828688763149390947840499696$ | $11318845912084248201410509468$ | $21805034621633992378$ |
| 66:3 | $80477192938182658974403020550734041337$ | $15172610050794063299271762680964657031$ | $49856984735320840404265733035$ | $-16599562534107326385021771634$ | $3455121317168682056579011916$ | $1211033993779854999780378324$ | $20946949009856631743$ |
| 66:4 | $86929450415495855825094148173803975798$ | $-39451108051554886629789173437251175295$ | $661144218066483944659160086$ | $-108783466121464298469791504$ | $5040336611541189894986938424$ | $-819725450724714837431421005$ | $1821654373447821221$ |
| 66:5 | $89300102447602488539789176863984772305$ | $-59703596756060800015422452247731414694$ | $-778816354441655372435692730$ | $207967538014082293722637337$ | $-1989032321064122916817019961$ | $-74847779064152776829643594$ | $4914518742060191$ |
| 67:0 | $28976078888156029108260835757293908145$ | $26046200106802765215757198148641882912$ | $-27550663450829487632844957150$ | $9370302372168583186392731002$ | $-14808943889094595671147704647$ | $6220303624321258872855752872$ | $22725788340001498233$ |
| 67:1 | $36734048242826578234133659005966968058$ | $15878718363640810004059902689368305161$ | $-31277565375403408469650674086$ | $15435491182438640649043675144$ | $11454519056128940558152015912$ | $-390815737760171388468910586$ | $4062746404116292641$ |
| 67:2 | $78168772597905002730230993250060210943$ | $33084746773984472893946236795258686182$ | $74802879290555735910652472352$ | $-17235617986396792663251902022$ | $-38672801227676385802770654214$ | $11275060765680903327279016907$ | $21766823910582369281$ |
| 67:3 | $80394077965979345695636258743064541649$ | $15178618689340263498486034232657195439$ | $49886857269959733131534182680$ | $-16646530485730487823365813222$ | $3548955702345514029231740461$ | $1192469373447355031046850420$ | $20760439327429910777$ |
| 67:4 | $86928907033355483187191155743100474073$ | $-39455202867989350086330499687931317814$ | $660011931533703443766548465$ | $-108569501456279451935910664$ | $5031880231996184189890016553$ | $-818201864869811063075557110$ | $1829488183117726725$ |
| 67:5 | $89301142015582739496458409982857628570$ | $-59703971048150648657569703993995696108$ | $-778388698151089503086826876$ | $207859669537393668558132626$ | $-1987804486663848926717607470$ | $-74869037752506030671094343$ | $4910704739826249$ |
| 68:0 | $29022993416809900668040389556917014759$ | $26077332951893524345041940313227492191$ | $-27633750245561939580848350956$ | $9395544873537286861571135992$ | $-14859141395216345901254806438$ | $6232847230878959802909019294$ | $22808122481726860187$ |
| 68:1 | $36811358202308094739933159172929402088$ | $15876763442827008483132248932227017444$ | $-31346270314036980089798859779$ | $15488589216350522933305596623$ | $11449494323980436258968870312$ | $-391151986695891317874708182$ | $4048007190686176199$ |
| 68:2 | $78082526600100554767185566354469898109$ | $33141012006734110639085004096795880455$ | $74899169758696249584249571984$ | $-17262812604692410778124768093$ | $-38515381615631779932604092918$ | $11230984065373632865580784967$ | $21728599647866010554$ |
| 68:3 | $80310726584058077227987296012757017783$ | $15184535219929918081747999633890505278$ | $49917986169786262066778760330$ | $-16694128006745616022530441890$ | $3641365275594552576435944595$ | $1174189997117342321874535612$ | $20578239399741899250$ |
| 68:4 | $86928364719369417116175773190209703135$ | $-39459290077606679143778748122215681426$ | $658883102731983295060009687$ | $-108356203917179762984291436$ | $5023447874417269583493105193$ | $-816682720874681775568137247$ | $1837445309800476421$ |
| 68:5 | $89302181044452272902680752959517384955$ | $-59704345446247385646110641890348826274$ | $-777961437030352480169341299$ | $207751893706968316784286228$ | $-1986578375655896724029185846$ | $-74890181877164147582564697$ | $4906893569332778$ |
| 69:0 | $29070034696900671515597900734020752486$ | $26108528708214141644723728921681721702$ | $-27717628019142114805311912025$ | $9421003382070589830857154915$ | $-14909597327717102608992178629$ | $6245468299522411435289316648$ | $22891175483087645650$ |
| 69:1 | $36888935109839160384162797283199971414$ | $15874806849674032389220666635705574298$ | $-31416000343384607021616362907$ | $15542272168516118772300926111$ | $11444438291297424280516414784$ | $-391484695532418283913263683$ | $4033123620525689160$ |
| 69:2 | $77996144154746820459601126721282227783$ | $33197056135126292357558805489710888893$ | $74996098982245511423293983296$ | $-17290197491029592825180242888$ | $-38356450834720976866761047079$ | $11186619654395039913710977413$ | $21690368677852118513$ |
| 69:3 | $80227135620562392686947587238605362111$ | $15190361056651294070991452482885808603$ | $49950387447574183559412608135$ | $-16742364746755309893259568410$ | $3732373520506873163555867067$ | $1156191027818869210569417960$ | $20400228587739501308$ |
| 69:4 | $86927823470209238667404097829244298892$ | $-39463369702571306733871363822219603353$ | $657757716707781818674250896$ | $-108143570622246240621264314$ | $5015039442628681285063420109$ | $-815168000808562715039932658$ | $1845528191821686226$ |
| 69:5 | $89303219534674018856449294881023693631$ | $-59704719949779056664450933722475426377$ | $-777534570519831921673737280$ | $207644210402356589180089056$ | $-1985353984425693459785051817$ | $-74911211783604280003072235$ | $4903085231552261$ |

### 6.10 Cells 70 through 79

| $t:i$ | $M_r$ | $M_b$ | $A_{00}$ | $A_{01}$ | $A_{10}$ | $A_{11}$ | $R_\rho$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 70:0 | $29117203815031637592398628476685609863$ | $26139787765837354737925211731427013537$ | $-27802305947288054172117102112$ | $9446680532861156647203408033$ | $-14960315994098669399872019211$ | $6258167937876594548968877069$ | $22974959205687086771$ |
| 70:1 | $36966781916727265801805355495978664932$ | $15872848601550585722665158572764032022$ | $-31486775039427283706325473959$ | $15596550770186425368538084871$ | $11439351464849435034222755946$ | $-391813997039829597670940809$ | $4018089533453771822$ |
| 70:2 | $77909624303197327306761668596760607815$ | $33252877729995395310222023706399638716$ | $75093677062702009057618608052$ | $-17317775574455761086182134908$ | $-38196029317390399590975983049$ | $11141971270337667254790655300$ | $21652137800552814317$ |
| 70:3 | $80143301854693935660552082688215764281$ | $15196097589642306060631938291175550676$ | $49984077646027755198549178170$ | $-16791250634296542552894569599$ | $3822003501110131430701536375$ | $1138467722101587968650098709$ | $20226290536564881802$ |
| 70:4 | $86927283282560898480115475064018042993$ | $-39467441764958245645594100978718428525$ | $656635758590927710827764046$ | $-107931598705546166384187922$ | $5006654840954171946114699784$ | $-813657686834060847650140862$ | $1853739335174939666$ |
| 70:5 | $89304257486710305772530142480169390046$ | $-59705094558175431987950824590357461248$ | $-777108098061049028768378135$ | $207536619503334747088981942$ | $-1984131309368565039192870497$ | $-74932127816186746280198801$ | $4899279727438067$ |
| 71:0 | $29164501871104012398881941163965694533$ | $26171110520414883003291890771056021169$ | $-27887793384637473066946772430$ | $9472579010164758917408101594$ | $-15011301759575176534882082075$ | $6270947269976644836468211363$ | $23059485744579809118$ |
| 71:1 | $37044901628614957259675321547351583312$ | $15870888715160668503867396678129573271$ | $-31558614474615845716180403786$ | $15651436025618096748476164928$ | $11434234346307310132467414110$ | $-392140024340541735101226861$ | $4002898571651270154$ |
| 71:2 | $77822966072061150758603983820964490430$ | $33308475380602282459328616203142234194$ | $75191914253093806358327782323$ | $-17345549823923547820354902459$ | $-38034137026309192808515758642$ | $11097042546409741792753808295$ | $21613913645199389952$ |
| 71:3 | $80059222015296773170142696866567581425$ | $15201746185553936134076773661936204584$ | $50019073853147128633399146604$ | $-16840795885302617796560715332$ | $3910277868957517306065500223$ | $1121015428366885711920663093$ | $20056312993094548192$ |
| 71:4 | $86926744153124637117681043796120218225$ | $-39471506286753553882254956573790639435$ | $655517213594051385886146761$ | $-107720285317024595819670219$ | $4998293974213809850730938176$ | $-812151761206555509591054273$ | $1862081315860089684$ |
| 71:5 | $89305294901022861510560592332788206635$ | $-59705469270868000910074412368269131287$ | $-776682019096655513833093436$ | $207429120889904380882439093$ | $-1982910346889702816087568532$ | $-74952930318159155645467170$ | $4895477057924558$ |
| 72:0 | $29211929978565489595369110449388175642$ | $26202497373260498219367704854446936694$ | $-27974099868683668330839560684$ | $9498701548504310885168642103$ | $-15062559048610581136198601628$ | $6283807436677543742067170418$ | $23144767434338212318$ |
| 72:1 | $37123297306867444641050941701352491977$ | $15868927206541650082265421006121507925$ | $-31631539234719989675173370945$ | $15706939221165637315916262780$ | $11429087432390957729137771483$ | $-392462910975605477021024371$ | $3987544266550835545$ |
| 72:2 | $77736168473000076973019774114270046425$ | $33363847694115449881693472763009230131$ | $75290820962553632640820379192$ | $-17373523249619840318054478255$ | $-37870793459738533028657033836$ | $11051837012657083655426920549$ | $21575702674906496328$ |
| 72:3 | $79974892779398516823272506256448621037$ | $15207308188005375257871875321389743977$ | $50055393718258952906014311905$ | $-16891011011923104100797258432$ | $3997218870137058327039185726$ | $1103829585225395209333776615$ | $19890187632038249938$ |
| 72:4 | $86926206078614905948162309342593741851$ | $-39475563289854797035741270795302174068$ | $654402067012020905774758614$ | $-107509627622396731638175983$ | $4989956747720801587125128751$ | $-810650206273604129528559764$ | $1870556782319431576$ |
| 72:5 | $89306331778072814500244468427076981226$ | $-59705844087289966189120105116245346337$ | $-776256333070430538973193823$ | $207321714442291830361212551$ | $-1981691093404130420177907821$ | $-74973619631660515725779796$ | $4891677223927193$ |
| 73:0 | $29259489264664404778362803995963902835$ | $26233948731435170103675838241065406702$ | $-28061235123826337348622967843$ | $9525050933805676836742889469$ | $-15114092346494658049996346974$ | $6296749596074445303899898320$ | $23230816855307654536$ |
| 73:1 | $37201972070006589552622186819031874981$ | $15866964091062006425980070051528310457$ | $-31705570436365050747372980942$ | $15763071934744179971794375646$ | $11423911215018239355018129521$ | $-392782790972836232536867333$ | $3972019703993402998$ |
| 73:2 | $77649230502519050973484614177146677800$ | $33418993295098197940543137831523201500$ | $75390407761001439712551930537$ | $-17401698904322748301327943486$ | $-37706017656784953260306334026$ | $11006358097150608030131108341$ | $21537511191267544372$ |
| 73:3 | $79890310770706414001951168628020568307$ | $15212784918031018818078240469406103327$ | $50093055468744273083173482426$ | $-16941906831718807566895005382$ | $4082848352198865336609540832$ | $1086905719881188774092905486$ | $19727809890117619494$ |
| 73:4 | $86925669055760288560841632755917762345$ | $-39479612796071507700750197821635238701$ | $653290304221382454007002954$ | $-107299622803041160450994546$ | $4981643067278338982624439878$ | $-809153004474352488757573612$ | $1879168457976556918$ |
| 73:5 | $89307368118320694863654293628342195842$ | $-59706219006876238515445150896224600448$ | $-775831039427277664970985250$ | $207214400040947607086331339$ | $-1980473545336670716474771028$ | $-74994196097725322674900937$ | $4887880226342628$ |
| 74:0 | $29307180870709657917253642332986592489$ | $26265465007834340834656718340953239048$ | $-28149209065541112989506683192$ | $9551630004566307432578938156$ | $-15165906200958826834076493997$ | $6309774923934004504235666945$ | $23317646840057336537$ |
| 74:1 | $37280929095193171129932717087884393685$ | $15864999383418711945511533255388346470$ | $-31780729745290178483338363715$ | $15819846045680874608932887426$ | $11418706181455152057306399730$ | $-393099798916888784486167840$ | $3956317850427058225$ |
| 74:2 | $77562151141749767968861476635418163388$ | $33473910825001652817467089449255665367$ | $75490685383937984156569771711$ | $-17430079884787551812601673037$ | $-37539828202534291049342352916$ | $10960609127138879871607043953$ | $21499345409863983689$ |
| 74:3 | $79805472558056489267154979455975137709$ | $15218177674519450399444908458447153344$ | $50132077927497571553009376670$ | $-16993494477249797234208656713$ | $4167187770998155478676304007$ | $1070239446542923019151360447$ | $19569078807872318963$ |
| 74:4 | $86925133081303422714426781861398107044$ | $-39483654827125641951580181830995204719$ | $652181910679805312046089900$ | $-107090268055893945080855985$ | $4973352839176470086485716864$ | $-807660138338949478765001627$ | $1887919143882970421$ |
| 74:5 | $89308403922226435534649924125560264567$ | $-59706594029063430999097549217557335205$ | $-775406137613221810632075231$ | $207107177566545818631986768$ | $-1979257699121912896292389649$ | $-75014660056287634008509914$ | $4884086066048819$ |
| 75:0 | $29355005952336563324575547846164442601$ | $26297046621277384506398569893843162152$ | $-28238031804671767386387374593$ | $9578441653057803409597489508$ | $-15218005223833210723046032613$ | $6322884614137086436482732438$ | $23405270480034071229$ |
| 75:1 | $37360171619759419765708338866859020976$ | $15863033097634275844006547416821938832$ | $-31857039395363456783868000818$ | $15877273744973931030069672003$ | $11413472814467477705188464238$ | $-393414070021391624930495407$ | $3940431429375845090$ |
| 75:2 | $77474929356227260191746140326736485257$ | $33528598941663462379204575332241771589$ | $75591664737353168196452406414$ | $-17458669333162733878511470784$ | $-37372243233063053523085201806$ | $10914593330165210080152256470$ | $21461211253566150165$ |
| 75:3 | $79720374653813723585762328404082860659$ | $15223487734644549155448651901497113015$ | $50172480531152678507877296487$ | $-17045785406075509869840271217$ | $4250258197452113751542020739$ | $1053826464862166250765990830$ | $19413896878667350090$ |
| 75:4 | $86924598152000922812671521700193138860$ | $-39487689404652032903870559900723688281$ | $651076871925531296164363763$ | $-106881560593343564521791681$ | $4965085970188993987132402810$ | $-806171590487966316301577028$ | $1896811721477841147$ |
| 75:5 | $89309439190249373375423236697835711312$ | $-59706969153289853677769069847067957604$ | $-774981627075406222483966322$ | $207000046899983594752473068$ | $-1978043551204179699216926278$ | $-75035011846185124225902398$ | $4880294743905129$ |
| 76:0 | $29402965679778799632320220360404372779$ | $26328693996599309398416824969067109803$ | $-28327713651849193430135738511$ | $9605488826563548269169413363$ | $-15270394092746376044339247742$ | $6336079879133250013118622546$ | $23493701132426428545$ |
| 76:1 | $37439702942793906887210522883742445524$ | $15861065247053412395136742023685428188$ | $-31934522208391541917940426622$ | $15935367545979444275437489837$ | $11408211592474079957808652304$ | $-393725740203262372771375427$ | $3924352910615668669$ |
| 76:2 | $77387564095659325971881033426390345891$ | $33583056318811987860844463854555230770$ | $75693356902753053439159911052$ | $-17487470438437249852404901561$ | $-37203280440324161605351442486$ | $10868313835148806718097748731$ | $21423114564786393624$ |
| 76:3 | $79635013512221161179708624562730888738$ | $15228716354288857192941346460872298152$ | $50214283349113282087000846995$ | $-17098791411187041068294888736$ | $4332080324208865968443388654$ | $1037662558399107528081897858$ | $19262169904499266325$ |
| 76:4 | $86924064264623302903193635389582350644$ | $-39491716550198841383477932405726768896$ | $649975173576828613405237644$ | $-106673497643126693707149498$ | $4956842367570379252566210139$ | $-804687343631820176468028828$ | $1905849155466567739$ |
| 76:5 | $89310473922848250290178419578223069778$ | $-59707344378995508044983518981925957022$ | $-774557507262089454784633631$ | $206893007922380515455389912$ | $-1976831098037494765439985004$ | $-75055251805163123300968507$ | $4876506260752423$ |
| 77:0 | $29451061238146638066802892728041919090$ | $26360407564744762948728985516819458707$ | $-28418265122041435676505222518$ | $9632774528652596656357220109$ | $-15323077552869255524574960684$ | $6349361950407414995988891350$ | $23582952427247064041$ |
| 77:1 | $37519526426780982404301069255256916002$ | $15859095844339333925482320946019154889$ | $-32013201614763552885555287153$ | $15994140295547284755501706001$ | $11402922989702038650760794948$ | $-394034946159332513048782675$ | $3908074498797130587$ |
| 77:2 | $77300054293688641879333840428720066554$ | $33637281645575810470243592749600299896$ | $75795773142309648146996470097$ | $-17516486437920234537115611466$ | $-37032957076904188219135711023$ | $10821773673429516436244614804$ | $21385061043655326328$ |
| 77:3 | $79549385527695730417199057958753855137$ | $15233864768459344314988976309156063336$ | $50257507103427906290184832504$ | $-17152524631892880026636792813$ | $4412674472227033461725443618$ | $1021743593115816811704646146$ | $19113806858221416786$ |
| 77:4 | $86923531415954900195310765620021560104$ | $-39495736285228003724481469436429730569$ | $648876801331450095688538217$ | $-106466076448224815327007827$ | $4948621939052705784844473446$ | $-803207380570202204720530113$ | $1915034496824165528$ |
| 77:5 | $89311508120481214335957378818425077694$ | $-59707719705622081598434804812692887801$ | $-774133777622642359798983596$ | $206786060515078040973350635$ | $-1975620336085550117857767674$ | $-75075380269878638124631018$ | $4872720617413175$ |
| 78:0 | $29499293827711633365005658097489347958$ | $26392187762864401401417846056476753691$ | $-28509696939239212463734423960$ | $9660301820491052242855450136$ | $-15376060418704816353744356663$ | $6362732078959136861026309448$ | $23673038274641373331$ |
| 78:1 | $37599645499297060904340568734804286375$ | $15857124901469654619308310125816294898$ | $-32093101674971250640457562120$ | $16053605185628565624610760422$ | $11397607476343821289642098756$ | $-394341825445416899661996130$ | $3891588121482574902$ |
| 78:2 | $77212398867647392640124134828133150078$ | $33691273625998369741534769448863605042$ | $75898924904137760871116176622$ | $-17545720618754399084203822275$ | $-36861289960649342646703414447$ | $10774975779775709631600026148$ | $21347056250754839987$ |
| 78:3 | $79463487033068455845565573637073477427$ | $15238934191695708244917862983470761781$ | $50302173189551505716674024445$ | $-17206997565180571838086273715$ | $4492060597264523866974823996$ | $1006065515897199046536273824$ | $18968719751829165184$ |
| 78:4 | $86922999602793799092753056971023321541$ | $-39499748631115676718114835764088148013$ | $647781740966095771530692410$ | $-106259294266761656017599037$ | $4940424592842629881627384389$ | $-801731684191509869095327069$ | $1924370885929833114$ |
| 78:5 | $89312541783605820830619733369575812321$ | $-59708095132612942408389764312452290838$ | $-773710437607545088301290708$ | $206679204559638943626476995$ | $-1974411261821673773339719245$ | $-75095397575904356980484254$ | $4868937814691564$ |
| 79:0 | $29547664664197967966544323861864278119$ | $26424035034413688263228303387038737426$ | $-28602020041281548785151808226$ | $9688073822192218150791248548$ | $-15429347575925093887090839869$ | $6376191535794930446980822484$ | $23763972872430964445$ |
| 79:1 | $37680063654766173475290461645789652198$ | $15855152429731892567396159795712211407$ | $-32174247102049997268276119859$ | $16113775765378511082435266353$ | $11392265518716701995501368742$ | $-394646516557971153926716749$ | $3874885416562426623$ |
| 79:2 | $77124596718304247136006040306124161176$ | $33745030978557548272495632294957777003$ | $76002823827703411725831467320$ | $-17575176319464422376443766444$ | $-36688295479157575781915596283$ | $10727922993354878058604222070$ | $21309105611318555728$ |
| 79:3 | $79377314297766622811356146541027251976$ | $15243925818471349108475817342151918174$ | $50348303698038260845020593755$ | $-17262223077578099132235948733$ | $4570258296275383418936529817$ | $990624353099761369356164768$ | $18826823510465364589$ |
| 79:4 | $86922468821951755737149764751574621457$ | $-39503753609152679734229894402682631304$ | $646689978335879735276751825$ | $-106053148371901439325764183$ | $4932250237618372299888558323$ | $-800260237472283614342913261$ | $1933861555839428812$ |
| 79:5 | $89313574912679033457986833590653277114$ | $-59708470659413133706071120689195598836$ | $-773287486668384100261907161$ | $206572439937846741567998134$ | $-1973203871728797482573612678$ | $-75115304057732637134934028$ | $4865157853373577$ |

### 6.11 Cells 80 through 89

| $t:i$ | $M_r$ | $M_b$ | $A_{00}$ | $A_{01}$ | $A_{10}$ | $A_{11}$ | $R_\rho$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 80:0 | $29596174979080646658264786036516551939$ | $26455949829254187951123705774342712135$ | $-28695245584826325240380466470$ | $9716093714206854404326989879$ | $-15482943983257274590649705085$ | $6389741612434100517639855507$ | $23855770713900807078$ |
| 80:1 | $37760784456277324615398580354266286443$ | $15853178439718556745618787873656848474$ | $-32256663284987604501307486910$ | $16174665953779947790936933308$ | $11386897579424649682768465892$ | $-394949159018488307160900881$ | $3857957719013543254$ |
| 80:2 | $77036646729603502140788815721080841259$ | $33798552435690015355785315490069135545$ | $76107481749368497752064932841$ | $-17604856931541696251234858705$ | $-36513989594134289267744117531$ | $10680618058666525764952355698$ | $21271214419370402669$ |
| 80:3 | $79290863525935333703106086426654853141$ | $15248840823587157493740357276515378128$ | $50395921437212757230494470694$ | $-17318214417540170404902515643$ | $4647286813713694936298264835$ | $975416209128291804178581900$ | $18688035851824324838$ |
| 80:4 | $86921939070254123058224781899800024020$ | $-39507751240544934036706767555204331484$ | $645601499373801274161816099$ | $-105847636051747947930929444$ | $4924098782526729118947913691$ | $-798793023476647780048146245$ | $1943509835702984926$ |
| 80:5 | $89314607508157225370159199576038178017$ | $-59708846285469368491936346345837759012$ | $-772864924257849185676737682$ | $206465766531705134405308033$ | $-1971998162299424597897112991$ | $-75135100048779475622701582$ | $4861380734227108$ |
| 81:0 | $29644826019890745654381063275759514056$ | $26487932603757423347941235759180476790$ | $-28789384950470742610101193408$ | $9744364738754930684059867458$ | $-15536854674420577412859472988$ | $6403383621428555326660693025$ | $23948446595839302527$ |
| 81:1 | $37841811537466323488999625106229830645$ | $15851202941321804830498822511760311197$ | $-32340376313150975232317832373$ | $16236290052814133884195814024$ | $11381504117522919525829121359$ | $-395249893460794816045254555$ | $3840796046959758826$ |
| 81:2 | $76948547768396208507877156008909361164$ | $33851836743320139942593396952475072880$ | $76212910708076621185197734665$ | $-17634765901066840643362519872$ | $-36338387845609225911843141190$ | $10633063626436943409104775237$ | $21233387841802790573$ |
| 81:3 | $79204130854495765232225694091878018515$ | $15253680362558255853879490872135612115$ | $50445049956869508880271281119$ | $-17374985228386091947837242370$ | $4723165047743652591738564108$ | $960437265040529721761061232$ | $18552277170649168653$ |
| 81:4 | $86921410344539776326673426293455009609$ | $-39511741546413899314036171672476650928$ | $644516290090220213935047984$ | $-105642754609244387685633005$ | $4915970137180105202027958116$ | $-797330025355755745194360987$ | $1953319154334811975$ |
| 81:5 | $89315639570496180287016737556346884056$ | $-59709222010230024163768609418493771113$ | $-772442749829730495498168028$ | $206359184223437440688872176$ | $-1970794130035598068528931183$ | $-75154785881388463308119525$ | $4857606458002058$ |
| 82:0 | $29693619050527927176007034505071483481$ | $26519983820911368410328799802122185935$ | $-28884449748026904694901195700$ | $9772890201300318905153431367$ | $-15591084760115751335705043416$ | $6417118896897098053035246588$ | $24042015626840921845$ |
| 82:1 | $37923148604464896299673399601928452310$ | $15849225943727656935137892603876408364$ | $-32425413001783425284211765583$ | $16298662761207233211660552755$ | $11376085588685594951373167526$ | $-395548861721415467846523688$ | $3823391086992064398$ |
| 82:2 | $76860298684163087296954142599527449496$ | $33904882660393281344476529883562651998$ | $76319122951185209503231285175$ | $-17664906730371463651306821133$ | $-36161505356012199731440748690$ | $10585262254475462320823010058$ | $21195630922395770585$ |
| 82:3 | $79117112351137298849848467043391747389$ | $15258445571993833379599296690585784214$ | $50495713573053753427868153676$ | $-17432549561817490977584983293$ | $4797911556355080151825878701$ | $945683777179892916294940171$ | $18419470428032912797$ |
| 82:4 | $86920882641661039205729831249439615038$ | $-39515724547797007446113178756797749361$ | $643434336572336444190234741$ | $-105438501362074046113250965$ | $4907864211653570057553564582$ | $-795871226347239262006871808$ | $1963293043944197807$ |
| 82:5 | $89316671100151093592911054670925555832$ | $-59709597833145137164496383021997264241$ | $-772020962838915582626330755$ | $206252692895486037261410387$ | $-1969591771448868562615732064$ | $-75174361886834722302215524$ | $4853835025430431$ |
| 83:0 | $29742555351580437962510128221238581001$ | $26552103950429649496217976329855482206$ | $-28980451821957934485206572374$ | $9801673472069928970372057686$ | $-15645639430069078576915229210$ | $6430948795074710615097665365$ | $24136493235881483396$ |
| 83:1 | $38004799437920032297586480220243671928$ | $15847247455409749476495304469294562457$ | $-32511800918628760040546327110$ | $16361799188782444173469036719$ | $11370642445376341551262326919$ | $-395846206933186735390003040$ | $3805733178702944220$ |
| 83:2 | $76771898308729035800536607022538703669$ | $33957688958413264070860455262399574708$ | $76426130940449284403367440731$ | $-17695282979740702803314092125$ | $-35983356834105391880648017662$ | $10537216408491788161962025906$ | $21157948585778802694$ |
| 83:3 | $79029804012240550857803554777696146288$ | $15263137569970214759238653172046039525$ | $50547937393979618946695533632$ | $-17490921892045857040205829472$ | $4871544563383784093935700172$ | $931152075836313324001615590$ | $18289541045247902080$ |
| 83:4 | $86920355958483610297470896588858452156$ | $-39519700265648093528096667446288835732$ | $642355624983673584952805630$ | $-105234873642561738078284258$ | $4899780916481935903411478194$ | $-794416609774661942284326096$ | $1973435144035190072$ |
| 83:5 | $89317702097576573430559154635313855881$ | $-59709973753666397649658695235034559588$ | $-771599562741386452919786030$ | $206146292430511800459818804$ | $-1968391083060262715513995472$ | $-75193828395328826815149795$ | $4850066437226438$ |
| 84:0 | $29791636220652817816580164723925841549$ | $26584293468863531702602955456996948031$ | $-29077403256980260969455251963$ | $9830717987618852597349458919$ | $-15700523955132847940873764008$ | $6444874694877364915972614150$ | $24231895181176585661$ |
| 84:1 | $38086767895086670480619930594015000441$ | $15845267484122612460630133274093931564$ | $-32599568411741587310819393697$ | $16425714871449611112288894862$ | $11365175137022649522450559811$ | $-396142073622308889585190355$ | $3787812298386216208$ |
| 84:2 | $76683345455969015591407461241989759749$ | $34010254420983841201984388573565136667$ | $76533947358162473880067307814$ | $-17725898269158147565433479309$ | $-35803956578769993911886003381$ | $10488928462874014797958496858$ | $21120345641336768710$ |
| 84:3 | $78942201760728174445650372597494101071$ | $15267757456397303477818897306397951458$ | $50601747347145154927241378033$ | $-17550117130561685353242087057$ | $4944081964436247300639035572$ | $916838563935223116155708341$ | $18162416801841430482$ |
| 84:4 | $86919830291886490179938990917224748376$ | $-39523668720837824172005693624383947390$ | $641280141563566756474426013$ | $-105031868797576031420387210$ | $4891720162656857739359405537$ | $-792966159046976859795232374$ | $1983749205484467214$ |
| 84:5 | $89318732563226641792147759231591198085$ | $-59710349771247144174433394618567189744$ | $-771178548994216626184888296$ | $206039982711393549162329839$ | $-1967192061400251503729048262$ | $-75213185736020707523145286$ | $4846300694086586$ |
| 85:0 | $29840862972701552269199833416691904537$ | $26616552859716769232995054508510201990$ | $-29175316383837946452033094073$ | $9860027252443144526808080982$ | $-15755743689444341320365040598$ | $6458897998482918070071206218$ | $24328237559334178069$ |
| 85:1 | $38169057911996997995598795222950206998$ | $15843286036894452492540368621122926479$ | $-32688744638546991003305237565$ | $16490425786866090765242024101$ | $11359684110193857590808694612$ | $-396436607809038685381187704$ | $3769618041849821421$ |
| 85:2 | $76594638921505106546818689168005238672$ | $34062577843353948696395790781170698296$ | $76642585113461107921796779602$ | $-17756756280094809548386634708$ | $-35623318482645022640365106669$ | $10440400701426917058957976049$ | $21082826787068626002$ |
| 85:3 | $78854301443840142165136010999031254797$ | $15272306313378540494477954897927100017$ | $50657170207707350046833421000$ | $-17610150641578948470519061844$ | $5015541332718273303211406243$ | $902739715754725093566361765$ | $18038027737747562383$ |
| 85:4 | $86919305638761908931201452162057947877$ | $-39527629934154123106542810383983309104$ | $640207872626654414582816273$ | $-104829484188432245418253803$ | $4883681861623955234725887659$ | $-791519857657988232681685307$ | $1994239094806855428$ |
| 85:5 | $89319762497554735607657463132832744876$ | $-59710725885342358400146200693202847267$ | $-770757921055568207103301674$ | $205933763621227489673444565$ | $-1965994703008718743936484733$ | $-75232434237003539528624875$ | $4842537796689785$ |
| 86:0 | $29890236940378911764491169007999720323$ | $26648882613563401652487027397197599374$ | $-29274203785255167681077107913$ | $9889604840641937834517532709$ | $-15811304072645458514084964374$ | $6473020131928670657974534155$ | $24425536814812742899$ |
| 86:1 | $38251673505709805250479112993630975515$ | $15841303120019422777688034703006818076$ | $-32779359596216588284803972296$ | $16555948370804726577530838003$ | $11354169808783268956431519680$ | $-396729957112236765081168946$ | $3751139606286880502$ |
| 86:2 | $76505777482394502301216509565040102521$ | $34114658031966551015171725553906283470$ | $76752057348797494600453624495$ | $-17787860757343876095689702471$ | $-35441456035616161606914594557$ | $10391635318070116503640220082$ | $21045396613400001406$ |
| 86:3 | $78766098830830043583617373269364928724$ | $15276785205564519292944952675151917999$ | $50714233628184145309911813066$ | $-17671038258190701332096290918$ | $5085939924767285673129462587$ | $888852075670975951143087385$ | $17916306059176369137$ |
| 86:4 | $86918781996015254136500417309864744972$ | $-39531583926302594095454980471420141158$ | $639138804562374214326348798$ | $-104627717190796215023541315$ | $4875665925279956240471523268$ | $-790077689185817150172903091$ | $2004908798618639768$ |
| 86:5 | $89320791901013707830415892333958799880$ | $-59711102095408659820178701316545576808$ | $-770337678384688966057317998$ | $205827635043326662439207484$ | $-1964799004434929716514176088$ | $-75251574225317613991847834$ | $4838777745697437$ |
| 87:0 | $29939759474385228423129915453274791126$ | $26681283228168580842025271028369470145$ | $-29374078302073218950417305534$ | $9919454397630660652674219459$ | $-15867210632165191536412651057$ | $6487242545726190607950350739$ | $24523809749697076424$ |
| 87:1 | $38334618776643527515837193784342874693$ | $15839318739049360278929861957278730299$ | $-32871444153432166007687038893$ | $16622299534267010416314229285$ | $11348632674194688709262956278$ | $-397022270857997136051183632$ | $3732365771144014155$ |
| 87:2 | $76416759896808213721590140271202807071$ | $34166493804010876398786313244477590113$ | $76862377446588740119315065194$ | $-17819215510903055142128687883$ | $-35258382328152503029161650865$ | $10342634417495707141208443355$ | $21008059606852862574$ |
| 87:3 | $78677589610578748332870085945694512053$ | $15281195180500398434199704945458499958$ | $50772966169554612966258211550$ | $-17732796299273850058867137745$ | $5155294686088072492640615870$ | $875172256931808040264737107$ | $17797186048052067697$ |
| 87:4 | $86918259360564999374681628022304635780$ | $-39535530717906941194565130434365436352$ | $638072923834462865040318320$ | $-104426565194588813878214036$ | $4867672265969861736589765956$ | $-788639637292371308267729649$ | $2015762428309449675$ |
| 87:5 | $89321820774055828519888999399098194378$ | $-59711478400904300505193849312923751448$ | $-769917820441909429812821380$ | $205721596861220390585428825$ | $-1963604962237499913016035080$ | $-75270606026954193511918273$ | $4835020541753537$ |
| 88:0 | $29989431943829870462915404037509917311$ | $26713755208612516537653672623736677485$ | $-29474953039578672244422795867$ | $9949579641907195523470241857$ | $-15923468985567249657718267749$ | $6501566715494029961603589728$ | $24623073533804198664$ |
| 88:1 | $38417897910996799085270650284610881438$ | $15837332898784969020779291144709352160$ | $-32965030083612562130197368944$ | $16689496681381896015469853744$ | $11343073145533732514846948217$ | $-397313700192600248846923452$ | $3713284877923468929$ |
| 88:2 | $76327584903700237773038512718758882598$ | $34218083986977838044094444332250257139$ | $76973559036047754365723365463$ | $-17850824417906394598369261393$ | $-35074110054489071422050804058$ | $10293400015784918352741497389$ | $20970820153840967728$ |
| 88:3 | $78588769389121588727579267894241515609$ | $15285537268967252866246795349297389888$ | $50833397333832931126408254403$ | $-17795441587183498373821526273$ | $5223622256691842192433163033$ | $861696940458614714034978352$ | $17680603974780928820$ |
| 88:4 | $86917737729342633180125610662478426735$ | $-39539470329509386367431574448155973651$ | $637010216980459940344618741$ | $-104226025603891229201043228$ | $4859700796484132027711739670$ | $-787205685722818719397786028$ | $2026804224934175956$ |
| 88:5 | $89322849117132785921719591849247858741$ | $-59711854801289159867597899027789311223$ | $-769498346688639982019932203$ | $205615648958653730271494652$ | $-1962412572984363907021650421$ | $-75289529966859351334621218$ | $4831266185484767$ |
| 89:0 | $30039255736601183753267245064471522415$ | $26746299067417631540846597922797613061$ | $-29576841374029609079593595937$ | $9979984366872900036092033459$ | $-15980084842965230738689664708$ | $6515994142608987607164731796$ | $24723345715132489959$ |
| 89:1 | $38501515183260554700797151863754059180$ | $15835345603266427287737820632249005564$ | $-33060150099684248430656872083$ | $16757557728133283972416563785$ | $11337491659804278279842572992$ | $-397604398200046403799397907$ | $3693884808850162349$ |
| 89:2 | $76238251222466939530518931330869777350$ | $34269427418218435285548194920001865856$ | $77085616000203373370400483327$ | $-17882691424607538232266703307$ | $-34888651515653005952653396497$ | $10243934040983380009550384831$ | $20933682544290439744$ |
| 89:3 | $78499633687085007746413625875579065756$ | $15289812485317505374981848246757763101$ | $50895557598196564925901543880$ | $-17858991466279839912313552788$ | $5290938976538524716358152359$ | $848422873676526187666013308$ | $17566498014138347573$ |
| 89:4 | $86917217099292588476439021447055900487$ | $-39543402781571084479418467296538213740$ | $635950670611215606960951056$ | $-104026095836850981700514386$ | $4851751430055894001644567896$ | $-785775818305065361431532146$ | $2038038564337101125$ |
| 89:5 | $89323876930695687545022153302546902907$ | $-59712231296024739445158109719952089048$ | $-769079256587367973491551404$ | $205509791219586922852439886$ | $-1961221833252744347798836785$ | $-75308346368937794464127432$ | $4827514677500592$ |

### 6.12 Cells 90 through 99

| $t:i$ | $M_r$ | $M_b$ | $A_{00}$ | $A_{01}$ | $A_{10}$ | $A_{11}$ | $R_\rho$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 90:0 | $30089232259745679774913315597100072229$ | $26778915324679021018577227999493238209$ | $-29679756959387131640464400168$ | $10010672442710488525903580488$ | $-16037064009507833236520883864$ | $6530526354876598118499249643$ | $24824644230667750697$ |
| 90:1 | $38585474958825934818451807901042361252$ | $15833356855763395139479634430541858274$ | $-33156837890481207928128698398$ | $16826501121961938077744150867$ | $11331888652110456105734550261$ | $-397894520024442533232067787$ | $3674152964329853509$ |
| 90:2 | $76148757552596385078756774317918943605$ | $34320522944504926673910295482853720108$ | $77198562483116832528670794051$ | $-17914820548416462278336842321$ | $-34702018622331263236475712865$ | $10194238333634540033029850169$ | $20896650975250222753$ |
| 90:3 | $78410177937028396559726389845498912890$ | $15294021827804579704388985731521096027$ | $50959478450754193307146943074$ | $-17923463822333303682143499104$ | $5357260890882311220539365071$ | $835346869372907085895346995$ | $17454808164072168180$ |
| 90:4 | $86916697467372172478197984124524436266$ | $-39547328094472535689788110583496888106$ | $634894271410402236611689383$ | $-103826773325588683742079830$ | $4843824080358169267416858055$ | $-784350018949236731724171119$ | $2049469962521201977$ |
| 90:5 | $89324904215195061236942980441949830084$ | $-59712607884574157703695926879025466189$ | $-768660549601654842220212919$ | $205404023528194848841994093$ | $-1960032739629121076219060612$ | $-75327055556056670755195969$ | $4823766018393355$ |
| 91:0 | $30139362939856759465823629260102305514$ | $26811604508198313782776118803119409682$ | $-29783713734259667828098330372$ | $10041647818320859639921744528$ | $-16094412387936706803365628164$ | $6545164907221555186555234162$ | $24926987417560509404$ |
| 91:1 | $38669781696692487350364319702303638252$ | $15831366658764397257141550774871759365$ | $-33255128158865212312160601292$ | $16896345862290532195916034721$ | $11326264555864597269093507954$ | $-398184222997532934440229978$ | $3654076239119191080$ |
| 91:2 | $76059102573307352607708386687893184603$ | $34371369421594564554863720820140005890$ | $77312412897302140250588703049$ | $-17947215879991823022463414467$ | $-34514222897577675816890802966$ | $10144314647270767389715877588$ | $20859729554460470080$ |
| 91:3 | $78320397480686609991556483083581921128$ | $15298166278906917045776966160943745989$ | $51025192428044424188517724858$ | $-17988877102856598550059877511$ | $5422603755520476567326796799$ | $822465804584213495925118170$ | $17345476167226253687$ |
| 91:4 | $86916178830551497057068932876936659485$ | $-39551246288513995261255314545558042387$ | $633841006134029865632201575$ | $-103628055516105529067564412$ | $4835918661501122991228483883$ | $-782928271647163272259142188$ | $2061103081276416310$ |
| 91:5 | $89325930971080856254494622520541293912$ | $-59712984566402144858775734675299789215$ | $-768242225196133243093838109$ | $205298345768866483669344345$ | $-1958845288709200362368599309$ | $-75345657850049360062093803$ | $4820020208738371$ |
| 92:0 | $30189649223473273079542450123812992380$ | $26844367153621037054965502061685872747$ | $-29888725929067906698390600719$ | $10072914523321043706547948871$ | $-16152135981219647921452608132$ | $6559911382398807842022131921$ | $25030394024689566109$ |
| 92:1 | $38754439952281409810363335349167219689$ | $15829375013965554635569884889768129542$ | $-33355056661663522158383228843$ | $16967111522023682201016779892$ | $11320619803001590383257706817$ | $-398473666771683365450798351$ | $3633640997122483535$ |
| 92:2 | $75969284943177738136461710915468492770$ | $34421965713795678366563518791948841076$ | $77427181931358231678538086446$ | $-17979881585391135599214971615$ | $-34325275479357164098077929315$ | $10094164648861653771011859111$ | $20822922303881114424$ |
| 92:3 | $78230287566108397281326584404501384184$ | $15302246805646497806533239476695023589$ | $51092733154362250740748490953$ | $-18055250338415457225444811220$ | $5486983041945571932907555987$ | $809776619511256424597063903$ | $17238445434994408475$ |
| 92:4 | $86915661185813409568665811112251021379$ | $-39555157383915880806275090653095106082$ | $632790861609965467293813080$ | $-103429939868191507433595078$ | $4828035088029333250504921905$ | $-781510560471869632263952965$ | $2072942734081559613$ |
| 92:5 | $89326957198802444333673573922251053084$ | $-59713361340975037716309652826933268308$ | $-767824282836504187271171034$ | $205192757826204355222393804$ | $-1957659477097884264301172184$ | $-75364153571719249520044675$ | $4816277249094022$ |
| 93:0 | $30240092577488227283571830046822545721$ | $26877203804577589990106573090262798392$ | $-29994808073438538271544473996$ | $10104476670105537313196998808$ | $-16210240895261960793037732080$ | $6574767391726098816961748391$ | $25134883224627454015$ |
| 93:1 | $38839454380358843433864313613495868543$ | $15827381922258637039292868417212459503$ | $-33456660251527389393032245332$ | $17038818270078206473396395127$ | $11314954824200122469543854517$ | $-398763013458648170736312142$ | $3612833044723634345$ |
| 93:2 | $75879303299762060963582456414597605610$ | $34472310693535891386863018242454983271$ | $77542884557821127087620374476$ | $-18012821908281098436246839047$ | $-34135187122924851095198668252$ | $10043789919219004965598267066$ | $20786233163182945706$ |
| 93:3 | $78139843344685718138565998705489358084$ | $15306264359902010831212013053659991205$ | $51162135383016551280799972630$ | $-18122603164973268643731715081$ | $5550413942401110079018007367$ | $797276316462930112078359469$ | $17133660973920113356$ |
| 93:4 | $86915144530153424136535471464868591424$ | $-39559061400819176989167698607286866850$ | $631743824737456002195772315$ | $-103232423855334337604191440$ | $4820173274919080728039376703$ | $-780096869577067735016344474$ | $2084993892295537013$ |
| 93:5 | $89327982898808620755870134274375067325$ | $-59713738207760774531999229216981984128$ | $-767406721989534191177857394$ | $205087259585024003170328829$ | $-1956475301409240107380645444$ | $-75382543040843493034614463$ | $4812537140001848$ |
| 94:0 | $30290694489567962305608910689888560753$ | $26910115012827935161447398730182511938$ | $-30101975003835325699147784300$ | $10136338455973390529762410479$ | $-16268733341698923011391589951$ | $6589734575838747057019578506$ | $25240474626024235329$ |
| 94:1 | $38924829738074516056101514113853940291$ | $15825387383718406437836129214269490341$ | $-33559976920821574103767632098$ | $17111486895002500698244274895$ | $11309270049111314582353451743$ | $-399052427774471896997266560$ | $3591637602554741818$ |
| 94:2 | $75789156259197762125026467742287475107$ | $34522403240932253055159572448330700632$ | $77659536041244680458309883289$ | $-18046041172210476429308537576$ | $-33943968203037770061425163062$ | $9993191953357988182155674889$ | $20749665993203597884$ |
| 94:3 | $78049059868068629144886194224916863679$ | $15310219878716812574168837985257612108$ | $51233435039628761622727886962$ | $-18190955847328429430393198124$ | $5612911374840893379788373580$ | $784961958828477734697012653$ | $17031069314262129217$ |
| 94:4 | $86914628860579653389695777610259263678$ | $-39562958359285837703019476663975083974$ | $630699882486655212441576809$ | $-103035504964629112200134673$ | $4812333137575658569969023512$ | $-778687183196653615886309986$ | $2097261691654526455$ |
| 94:5 | $89329008071547605411579314757165181498$ | $-59714115166228889889535255622427444056$ | $-766989542123052435084313048$ | $204981850930353440058341306$ | $-1955292758266470083665261088$ | $-75400826576176755054038026$ | $4808799881986645$ |
| 95:0 | $30341456468582134017701724877845963174$ | $26943101338410121303186981403683862278$ | $-30210241871436409188987136252$ | $10168504165323515069964419056$ | $-16327619640772420682927959338$ | $6604814605467510657164631098$ | $25347188286426818587$ |
| 95:1 | $39010570888121334634372450634633314341$ | $15823391397589219820768548694020723576$ | $-33665045847662436537395806475$ | $17185138829747829510054588298$ | $11303565906595296095997893681$ | $-399342077190900320590041655$ | $3570039275595328282$ |
| 95:2 | $75698842415799976818940025019594195011$ | $34572242243363066257954043728641031504$ | $77777151946518881424882516309$ | $-18079543782948059291437078525$ | $-33751628715996784855098569087$ | $9942372160813874300829328684$ | $20713224579370923436$ |
| 95:3 | $77957932084960121732051202299599837491$ | $15314114284601819126208187862178364295$ | $51306669267590191720200989211$ | $-18260329303707161577771754318$ | $5674489987792154646579319798$ | $772830670078383704845456446$ | $16930618440549871159$ |
| 95:4 | $86914114174112740650183228332157716793$ | $-39566848279299185740133927985968831863$ | $629659021898154125667905006$ | $-102839180696688647974435824$ | $4804514591830702233075152073$ | $-777281485644207998985347038$ | $2109751439092916721$ |
| 95:5 | $89330032717467043861421633573899269541$ | $-59714492215850509597477307940969466139$ | $-766572742705947931226710052$ | $204876531747432614167386724$ | $-1954111844301880970787670556$ | $-75419004495454938699092408$ | $4805065475556551$ |
| 96:0 | $30392380045044848457522624888701414473$ | $26976163349792754878280879147833230732$ | $-30319624150267130873284694712$ | $10200978171920789623074092650$ | $-16386906224294948970329145877$ | $6620009182240402440395510159$ | $25455044725551797342$ |
| 96:1 | $39096682802021852720183127460310390012$ | $15821393962270857855861576612796084480$ | $-33771907444230073916024654266$ | $17259796177658552236377397861$ | $11297842824966298995650127964$ | $-399632132093701081286904797$ | $3548022021487980287$ |
| 96:2 | $75608360341644448905725477258778749896$ | $34621826595041186088592270414098868262$ | $77895748147435069353243999232$ | $-18113334230888319864981664207$ | $-33558178281516261793725436647$ | $9891331865913784195660467992$ | $20676912635096313735$ |
| 96:3 | $77866454837784968822496584820166709345$ | $15317948485833474490999287236594118376$ | $51381876475803362002166436953$ | $-18330745131578757922983272660$ | $5735164165122693224356181217$ | $760879632794001129847288906$ | $16832257723955550976$ |
| 96:4 | $86913600467785792567098912514446025252$ | $-39570731180764309974645199709128653255$ | $628621230082515235343221329$ | $-102643448565554535149162081$ | $4796717553939539148621055722$ | $-775879761312500580116556560$ | $2122468619906974994$ |
| 96:5 | $89331056837014008394482608031375271314$ | $-59714869356098345604734984330823539522$ | $-766156323208166701432589266$ | $204771301921712874131892079$ | $-1952932556156853969787868695$ | $-75437077115398898324723701$ | $4801333921203146$ |
| 97:0 | $30443466771567309448096788428226262744$ | $27009301624031542493361584276636628082$ | $-30430137645598078985836456537$ | $10233764941235651898205924223$ | $-16446599638704311821623285523$ | $6635320039509368123504068212$ | $25564064939030666071$ |
| 97:1 | $39183170563547884478456820347140725408$ | $15819395075303543785522547238783821254$ | $-33880603407488488651044692375$ | $17335481739752838161338686520$ | $11292101232246893766328487042$ | $-399922765948321358612269172$ | $3525569116947288400$ |
| 97:2 | $75517708586138242186016827297261795417$ | $34671155196588563557382655294369965186$ | $78015340835507832741800420105$ | $-18147417093527510805135736099$ | $-33363626144418939642842877712$ | $9840072308002815840325110109$ | $20640733805140605595$ |
| 97:3 | $77774622859226291206144658389963152817$ | $15321723376746939103976754958365709812$ | $51459096388841247019871646942$ | $-18402225634764755019784958701$ | $5794948030712193774145103841$ | $749106087726045124947747711$ | $16735937856312426749$ |
| 97:4 | $86913087738644312193673264172208582881$ | $-39574607083508460075745357598072870588$ | $627586494219810324097933690$ | $-102448306098608879514060196$ | $4788941940578558031646414189$ | $-774481994672997984037858575$ | $2135418905281500286$ |
| 97:5 | $89332080430634999083979715334780936414$ | $-59715246586446690934573184725907170697$ | $-765740283100708964212788707$ | $204666161338856435308361075$ | $-1951754890481814661358922077$ | $-75455044751718136587239518$ | $4797605219401538$ |
| 98:0 | $30494718223322353720055234259219513020$ | $27042516746930030830667797332817403213$ | $-30541798502618479373198893401$ | $10266869032859985902720888208$ | $-16506706548212499300987750850$ | $6650748943202776615539134661$ | $25674270412647171207$ |
| 98:1 | $39270039372279906699504593446111995486$ | $15817394733352114746956274458804377934$ | $-33991176772456952356247789944$ | $17412219043370316349493341785$ | $11286341556432032012215382510$ | $-400214155473339408930401122$ | $3502663122129303379$ |
| 98:2 | $75426885675577889171553553736234961172$ | $34720226954611804525283560627141526555$ | $78135946529063801584385603181$ | $-18181797038013057245706136184$ | $-33167981176153341210534614283$ | $9788594641623893840559834516$ | $20604691668955299201$ |
| 98:3 | $77682430768623185158194972331418353663$ | $15325439838024643301261833781577103328$ | $51538370099667487577564165008$ | $-18474793851918422539416578862$ | $5853855453027912600963606940$ | $737507332882107706851316878$ | $16641610785610073656$ |
| 98:4 | $86912575983746132503901423046843853863$ | $-39578476007281438769817709780200733541$ | $626554801559161897188834060$ | $-102253750836486731051849983$ | $4781187668842597666322903962$ | $-773088170275375364365714656$ | $2148608160201098837$ |
| 98:5 | $89333103498775944840265559021476405788$ | $-59715623906371414637064143265354032628$ | $-765324621855626331281556027$ | $204561109884735847887857362$ | $-1950578843936203079968168036$ | $-75472907719114486090486132$ | $4793879370610454$ |
| 99:0 | $30546135998521262292945323692478185274$ | $27075809313204675617714758784275831496$ | $-30654623215395513657767654565$ | $10300295103002237944359802076$ | $-16567233738052372826239662277$ | $6666297692704713577902195477$ | $25785683137087506075$ |
| 99:1 | $39357294547313285488078231401020991117$ | $15815392932189305339153029010560300214$ | $-34103671968185626570052255521$ | $17490032372268376841588664441$ | $11280564225763608060716307508$ | $-400506480822198492420882747$ | $3479285842818199175$ |
| 99:2 | $75335890112694603465645431486032490510$ | $34769040781278510749299894442670880345$ | $78257582082607995966472180501$ | $-18216478823769228167291741318$ | $-32971251876130955630663063722$ | $9736899936650645274254860491$ | $20568789744001901024$ |
| 99:3 | $77589873068222357843504967421984617880$ | $15329098736980351293644314487468099032$ | $51619740125070525195308895854$ | $-18548473586456230106723165392$ | $5911900049604906288889442924$ | $726080722643378061785726334$ | $16549229652798383660$ |
| 99:4 | $86912065200161350345332022380133515781$ | $-39582337971755991669610850516903542689$ | $625526139418288193537494315$ | $-102059780332989192918756829$ | $4773454656242354999643069674$ | $-771698272747031614758376758$ | $2162042451769204057$ |
| 99:5 | $89334126041882204461175942944494527459$ | $-59716001315349956759909291293916493937$ | $-764909338946019013466891700$ | $204456147445433466745379562$ | $-1949404413188443905319327072$ | $-75490666331285775684038667$ | $4790156375272335$ |

### 6.13 Cells 100 through 109

| $t:i$ | $M_r$ | $M_b$ | $A_{00}$ | $A_{01}$ | $A_{10}$ | $A_{11}$ | $R_\rho$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 100:0 | $30597721718903251865109466987129777617$ | $27109179926654376219377210203990903099$ | $-30768628636130617521626327261$ | $10334047907064826142568596046$ | $-16628188117825948151973449534$ | $6681968121762113051398287231$ | $25898325623225061167$ |
| 100:1 | $39444941531118786936202198257384014501$ | $15813389666678100732639924484867868413$ | $-34218134876599179744765944239$ | $17568946798254527644704273454$ | $11274769669016302838029669602$ | $-400799925773745966255633257$ | $3455418290275368218$ |
| 100:2 | $75244720376186166630595480876832943439$ | $34817595593894166346997824039285976040$ | $78380264696478872237149506562$ | $-18251467305202200549845116442$ | $-32773446372880294651409224339$ | $9684989178372565200745312541$ | $20533031489052297601$ |
| 100:3 | $77496944139276294710173461005866041517$ | $15332700927838882196425839318087372865$ | $51703250463975287976401257648$ | $-18623289438028640161427768838$ | $5969095191430959675863530039$ | $714823666910783245470172889$ | $16458748729731991202$ |
| 100:4 | $86911555384972260824622924916343030997$ | $-39586192996528194688432061949700811363$ | $624500495183051742115371012$ | $-101866392154997204671819991$ | $4765742820701812377363333882$ | $-770312286792608160325863180$ | $2175728057959565865$ |
| 100:5 | $89335148060398567679731519867624891189$ | $-59716378812861323337554392760088914710$ | $-764494433846033035973346823$ | $204351273907240923019174710$ | $-1948231594915916770623721708$ | $-75508320900929481486044435$ | $4786436233813425$ |
| 101:0 | $30649477030238065627665248646447805282$ | $27142629200334617724855693910342806379$ | $-30883831984724310891851326584$ | $10368132302307046218451874496$ | $-16689576724958233547988423729$ | $6697762099420807843393339544$ | $26012220917962498774$ |
| 101:1 | $39532985893565283262862798029508271184$ | $15811384930753113912725372621144313299$ | $-34334612894383670548631236614$ | $17648988214448352392101086625$ | $11268958315795528605211730548$ | $-401094677932137331410049327$ | $3431040638583677661$ |
| 101:2 | $75153374920235084506924778190680142002$ | $34865890314479329197175806224044809784$ | $78504011926803709937608909508$ | $-18286767434487768371717190104$ | $-32574572425014788894711430988$ | $9632863267531691851148868162$ | $20497420307473162637$ |
| 101:3 | $77403638237980031177398949746531500430$ | $15336247252011635826367949992887294393$ | $51788946658807584399076398081$ | $-18699266835623716026820111906$ | $6025454007236344706577603906$ | $703733630280799014292363419$ | $16370123358085978396$ |
| 101:4 | $86911046535273292122507814577905779067$ | $-39590041101117839057184211111410547081$ | $623477856307011431777642806$ | $-101673583882385993696762251$ | $4758052080555683757752637824$ | $-768930197193511298518637716$ | $2189671476826662628$ |
| 101:5 | $89336169554769256209201647048918178852$ | $-59716756398386081398521756073213181987$ | $-764079906030857462959675754$ | $204246489156658597413069449$ | $-1947060385804926687151529375$ | $-75525871739746362702973486$ | $4782718946643859$ |
| 102:0 | $30701403602842099291576223764323503141$ | $27176157756736367925024204262802037270$ | $-31000250858661635665453108000$ | $10402553250596821388080464662$ | $-16751406728260756769070188413$ | $6713681530991627593280123579$ | $26127392620655036929$ |
| 102:1 | $39621433336113049998307446092395880866$ | $15809378717400938749276624991977370747$ | $-34453154998104426482601569734$ | $17730183370273247518455949073$ | $11263130596848353112074150058$ | $-401390928936705046112211849$ | $3406132179305983183$ |
| 102:2 | $75061852174012591329468621951051099564$ | $34913923869346882779364348856927378570$ | $78628841695766509681254777372$ | $-18322384264445093504195589294$ | $-32374637422011340872182682852$ | $9580523020309965248569180831$ | $20461959550497501446$ |
| 102:3 | $77309949491238117105997015616027187072$ | $15339738538368072319514534888190078863$ | $51876875860098817827187310471$ | $-18776432072403668539649902101$ | $6080989387688508260311707924$ | $692808131251218715400835350$ | $16283309889072000765$ |
| 102:4 | $86910538648170940734847628191423746237$ | $-39593882304968813961917294293719228642$ | $622458210310978062973311329$ | $-101481353107940188851745310$ | $4750382354546879740310816221$ | $-767551988807438059048379209$ | $2203879436203354247$ |
| 102:5 | $89337190525437924785539046667449053637$ | $-59717134071406353990883686790846716171$ | $-763665754976721631393919254$ | $204141793080395095214930816$ | $-1945890782550674584536715785$ | $-75543319158444082318146693$ | $4779004514157753$ |
| 103:0 | $30753503132108515234057238903290055943$ | $27209766227969882345929745275833387476$ | $-31117903243230827488456386939$ | $10437315821254796718067493222$ | $-16813685431609099582470463473$ | $6729728359047724130484379932$ | $26243864900140005329$ |
| 103:1 | $39710289696186568381353748596670642981$ | $15807371018639427480147802281011679764$ | $-34573811812756118556168451492$ | $17812559908285290036085168167$ | $11257286944388346797861158851$ | $-401688874682435234773589409$ | $3380671273262114840$ |
| 103:2 | $74970150541168062622333545179991913569$ | $34961695188679099701670171875617542157$ | $78754772302201125867153005686$ | $-18358322951500047956800037710$ | $-32173648384796190249489095252$ | $9527969168266393737167587037$ | $20426652520486543632$ |
| 103:3 | $77215871892252844226151629065607007811$ | $15343175603503296166777558885872167587$ | $51967086894532103932292114883$ | $-18854812342381637092860712354$ | $6135713989491745427956886306$ | $682044741457210213904041223$ | $16201927367974165539$ |
| 103:4 | $86910031720783707136470582633884721634$ | $-39597716627449486819414294395751262374$ | $621441544782573350080887890$ | $-101289697437269590403173167$ | $4742733561823991248215635820$ | $-766177646567905552692317202$ | $2218358903916109704$ |
| 103:5 | $89338210972847662207193834588335199266$ | $-59717511831405815225801703904639701399$ | $-763251980160892394148668281$ | $204037185565366723024400807$ | $-1944722781857227966311998434$ | $-75560663466740812720530210$ | $4775292936733297$ |
| 104:0 | $30805777339051815570078790102760514263$ | $27243455255953576534439049975654317819$ | $-31236807522088427566338241875$ | $10472425193994438749116826104$ | $-16876420277738953332790486377$ | $6745904564454357048531999542$ | $26361662512398979505$ |
| 104:1 | $39799560951736303037288143484782174193$ | $15805361825495837864021379587801577059$ | $-34696635683960810155084912683$ | $17896146402954346787765069831$ | $11251427792435367325089761032$ | $-401988715551742331294366010$ | $3354635299212289526$ |
| 104:2 | $74878268399303379710137359890900323142$ | $35009203206104263659242828471433200931$ | $78881822432522940056654824080$ | $-18394588758741857192577673462$ | $-31971611966134573117782873688$ | $9475202358223100518286105569$ | $20391502474185307810$ |
| 104:3 | $77121399295924251073210609291629729636$ | $15346559252001897027649227119638678159$ | $52059630336645448578614228478$ | $-18934435779053761042847622264$ | $6189640239391864618802578129$ | $671441084938036973914536568$ | $16122800299359947953$ |
| 104:4 | $86909525750242031864534021306942171508$ | $-39601544087853081208181012631452836102$ | $620427847375792343437111372$ | $-101098614488725590389851443$ | $4735105621938791704834688036$ | $-764807155483783779127415626$ | $2233117098550319691$ |
| 104:5 | $89339230897440992372315446762459238741$ | $-59717889677869685339056398988166895276$ | $-762838581061671372299432150$ | $203932666498696967183081095$ | $-1943556380437491680152877558$ | $-75577904973368826344905910$ | $4771584214732836$ |
| 105:0 | $30858227970867363677226749062107493856$ | $27277225492608131095645459699144058084$ | $-31356982488184650200809504962$ | $10507886661961970014298113979$ | $-16939618852165413832916286382$ | $6762212167432428492653793816$ | $26480810818880112791$ |
| 105:1 | $39889253225999521282975168702475552142$ | $15803351127983791682844453138985407062$ | $-34821680754045543627572190757$ | $17980972401520937707458734234$ | $11245553577171372509425053039$ | $-402290656658282535132971052$ | $3328000599217124821$ |
| 105:2 | $74786204099431769716457950032668700517$ | $35056446858272591788484473282227813867$ | $79010011172012992741959174528$ | $-18431187059076922820416744972$ | $-31768534450820470488053428052$ | $9422223152099266684505157006$ | $20356512625975281642$ |
| 105:3 | $77026525414051823977038304715228504983$ | $15349890276698201687407253364875461494$ | $52154558584423427381280568379$ | $-19015331496109999446440916652$ | $6242780338085791962398328033$ | $660994837434869936193467810$ | $16045203935510872525$ |
| 105:4 | $86909020733688232018170473368747750070$ | $-39605364705398052472060997636950793710$ | $619417105810569240440643421$ | $-100908101893318237611272851$ | $4727498454843757546198235842$ | $-763440500638831864232250912$ | $2248161500800559767$ |
| 105:5 | $89340250299659875313350958519216266244$ | $-59718267610284725770493172074801120947$ | $-762425557158392216589207444$ | $203828235767715973900376238$ | $-1942391575013178802312444145$ | $-75595043986078071394150432$ | $4767878348502968$ |
| 106:0 | $30910856801506363290724177231883455707$ | $27311077600056001572881808462451621425$ | $-31478447355063463497672915877$ | $10543705634880145765720803307$ | $-17003288887230449362317975114$ | $6778653228657115158203298339$ | $26601335805509674167$ |
| 106:1 | $39979372792470860421366211153878089907$ | $15801338915078982433675121914631676107$ | $-34949003042248134447128048762$ | $18067068467061469061368544166$ | $11239664737313436193736265221$ | $-402594908103602097562540505$ | $3300742420424971065$ |
| 106:2 | $74693955965420625089145331275642759429$ | $35103425084431194318600758823801729246$ | $79139358016469134881548315626$ | $-18468123338483880378723352049$ | $-31564421755662541457402848988$ | $9369032026691928281458552244$ | $20321686151127787044$ |
| 106:3 | $76931243810327172906714921508778611459$ | $15353169458933093792474610853221059242$ | $52251925939025913020371792413$ | $-19097529630356260935435309256$ | $6295146264035994317226013626$ | $650703725720172084929714479$ | $15969103403724960785$ |
| 106:4 | $86908516668276438171209193053817180749$ | $-39609178499228461013549606482096613590$ | $618409307872346555423611012$ | $-100718157294633941494586437$ | $4719911980889606912871885870$ | $-762077667191237697582792922$ | $2263499865443217872$ |
| 106:5 | $89341269179945708229048258132054924548$ | $-59718645628139234261309430858938768699$ | $-762012907931417878022515771$ | $203723893259960031068235595$ | $-1941228362314781635731331513$ | $-75612080811639732713980670$ | $4764175338374623$ |
| 107:0 | $30963665632266824785655640755656520906$ | $27345012250826512155086918699958142593$ | $-31601221768552516365168364200$ | $10579887642300067299758325002$ | $-17067438266283702356718180840$ | $6795229850393007594447760340$ | $26723264102423265181$ |
| 107:1 | $40069926080094036811281361299296843662$ | $15799325174693565922101016038201139457$ | $-35078660529318394793325353697$ | $18154466223904324031612764879$ | $11233761714505232461368676673$ | $-402901685247476303053110018$ | $3272834853015965914$ |
| 107:2 | $74601522293417785950702570672966358579$ | $35150136825997803055090095042171027526$ | $79269882884239437882271337071$ | $-18505403199374134679275941118$ | $-31359279429262123043147111071$ | $9315629373402522472726114841$ | $20287026189061734926$ |
| 107:3 | $76835547895106273818422605737291724570$ | $15356397568807560556724674974287801656$ | $52351788688920947174311511603$ | $-19181061386990277367717158780$ | $6346749777189522317099134791$ | $640565526959197946808613162$ | $15894464369495783282$ |
| 107:4 | $86908013551172531694793028044725454132$ | $-39612985488414343293735577439472664146$ | $617404441411647618291258821$ | $-100528778348753809152929286$ | $4712346120822856366193798011$ | $-760718640373160941153495944$ | $2279140233971659879$ |
| 107:5 | $89342287538739326513872502316741781041$ | $-59719023730923039969109190670758448756$ | $-761600632862137887552349350$ | $203619638863171051758065775$ | $-1940066739081542821309818660$ | $-75629015755849777890150979$ | $4760475184663156$ |
| 108:0 | $31016656292401069723679623671728767688$ | $27379030128066719408783726509039702282$ | $-31725325818858756539131202631$ | $10616438336965423295100530673$ | $-17132075028002024153067619425$ | $6811944177667232285920590726$ | $26846623004448728354$ |
| 108:1 | $40160919678686829349637415820154845507$ | $15797309893649163029797283618653903727$ | $-35210713246802143881619520445$ | $18243198405550010470152775692$ | $11227844953728352515534760192$ | $-403211208992860019026912918$ | $3244250764008851422$ |
| 108:2 | $74508901351260746872189145620568294695$ | $35196581026132994541446265591259903049$ | $79401606128653813706150853525$ | $-18543032364062311843438681015$ | $-31153112651578951029531243320$ | $9262015497908011782448686246$ | $20252535846609616752$ |
| 108:3 | $76739430919949130570495587528640730479$ | $15359575365433128505027098507272794346$ | $52454205198708988463316088798$ | $-19265959087384367836965169321$ | $6397602422601386709934904924$ | $630578068104216139264199600$ | $15821252984374315069$ |
| 108:4 | $86907511379554082486738758535960355068$ | $-39616785691952080555654257879633712473$ | $616402494343652372233878857$ | $-100339962724172610005262410$ | $4704800795783395475350262789$ | $-759363405490279380517181115$ | $2295090947937097882$ |
| 108:5 | $89343305376481004784844247760309711634$ | $-59719401918127498600651361674206747979$ | $-761188731432965644823633286$ | $203515472465296059393116960$ | $-1938906702061426561831720184$ | $-75645849123532488637716993$ | $4756777887668431$ |
| 109:0 | $31069830639740347212981067572001399756$ | $27413131925758239779929850013633688536$ | $-31850780053086334081120419041$ | $10653363498293758144658190233$ | $-17197207370853393621997720214$ | $6828798399482100836375956370$ | $26971440492374442844$ |
| 109:1 | $40252360344612264686417023187219117277$ | $15795293057648399150220689142664399466$ | $-35345223371317233895937343432$ | $18333298905260200092137209839$ | $11221914903734926370859547068$ | $-403523706086441357088709759$ | $3214961726610957712$ |
| 109:2 | $74416091377868226960020526153221277972$ | $35242756629310627717064434855355335697$ | $79534548550870547638961600870$ | $-18581016678351274333591019103$ | $-30945926233280013758785401087$ | $9208190619775345476960857498$ | $20218218201295732465$ |
| 109:3 | $76642885971913915051454889183315858661$ | $15362703597179353537983807946954183183$ | $52559236002947638577444874857$ | $-19352256219539874574888316821$ | $6447715533961882116372862389$ | $620739225322134954129863141$ | $15749435833035220727$ |
| 109:4 | $86907010150610287104517055619402764466$ | $-39620579128764765287693796815184755634$ | $615403454647776441115646228$ | $-100151708101718362384665828$ | $4697275927302079123256075340$ | $-758011947921338590116179140$ | $2311360663041569736$ |
| 109:5 | $89344322693610457905807619373708658553$ | $-59719780189245487562218356890983057507$ | $-760777203127335715936982486$ | $203411393954486674589677777$ | $-1937748248011089958032309054$ | $-75662581218543977551612750$ | $4753083447674909$ |

### 6.14 Cells 110 through 119

| $t:i$ | $M_r$ | $M_b$ | $A_{00}$ | $A_{01}$ | $A_{10}$ | $A_{11}$ | $R_\rho$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 110:0 | $31123190561337159167186114998799750928$ | $27447318348940242512286591201888262780$ | $-31977605488194174892178485779$ | $10690669035979585006248909624$ | $-17262843657711135434537181190$ | $6845794750068903116238768180$ | $27097745255038369420$ |
| 110:1 | $40344255006709786837646949305485638466$ | $15793274651244899639218685133659736925$ | $-35482255324154596860030549764$ | $18424802829493139384832907400$ | $11215972017503139100200092207$ | $-403839409435866875164540317$ | $3184937944763603350$ |
| 110:2 | $74323090582613518372516197119737936980$ | $35288662580886209501583138015944155822$ | $79668731413155237286669907263$ | $-18619362115236563598388914954$ | $-30737724614866693004334129133$ | $9154154872017943239661206658$ | $20184076304630816537$ |
| 110:3 | $76545905967591789084212544601733891057$ | $15365783001918534194882288275445153545$ | $52666943905309724715119377654$ | $-19439987491390698827094485821$ | $6497100237027361505854342546$ | $611046923456289356100743719$ | $15678979879339026632$ |
| 110:4 | $86906509861541907298755932151102048092$ | $-39624365817702565443554165069286122142$ | $614407310367253437442051040$ | $-99964012174472536618219485$ | $4689771437298337380682414688$ | $-756664253117704884453140552$ | $3374943113425854302$ |
| 110:5 | $89345339490566842009136842712424069487$ | $-59720158543771401127531999970791166170$ | $-760366047429701140196699308$ | $203307403219098603660444505$ | $-1936591373695854456305115135$ | $-75679212343775690287421797$ | $4749391864951734$ |
| 111:0 | $31176737974125916208994798500547763725$ | $27481590113938817902682979909218325752$ | $-32105823624411441715396442294$ | $10728360993724391895070567535$ | $-17328992420624632879424606957$ | $6862935510184537674908157976$ | $27225566712275098494$ |
| 111:1 | $40436610772501115170297824540119319458$ | $15791254657811655078872774471183207119$ | $-35621875876563186501884001327$ | $18517746554376669391051178707$ | $11210016752717359744721877577$ | $-404158558444790468377103622$ | $3154148172504214912$ |
| 111:2 | $74229897144679003489677729431393699410$ | $35334297826662894968211747875834294950$ | $79804176452610465027039491223$ | $-18658074778735365091356169337$ | $-30528511865575072212279035879$ | $9099908300592808196076919524$ | $20150113185427397038$ |
| 111:3 | $76448483646867690620554740753302185122$ | $15368814307267820994463156315077332014$ | $52777394083433484838864878141$ | $-19529188887147122233247609941$ | $6545767452953841296754921837$ | $601499135523233283018519815$ | $15609852411651582512$ |
| 111:4 | $86906010509561208944199004518356694061$ | $-39628145777543086435118791643554827653$ | $613414049608720482101319594$ | $-99776872647690869117134683$ | $4682287248077802799535096527$ | $-755320306602921527322847063$ | $3409569578604596136$ |
| 111:5 | $89346355767788755514889434915932122170$ | $-59720536981201145623144055120821068779$ | $-759955263825530745807125277$ | $203203500147691128773461439$ | $-1935436075889677407545024059$ | $-75695742801157893240859030$ | $4745703139752817$ |
| 112:0 | $31230474825602571808442403902676536271$ | $27515947948602939479735340226969354933$ | $-32235456459129978477214075133$ | $10766445553098832315831168097$ | $-17395662365753024434528050314$ | $6880223008452753300814097265$ | $27354935038760075237$ |
| 112:1 | $40529434934686487830409145668257605675$ | $15789233059507664167354918140654187444$ | $-35764154261105857952363540078$ | $18612167785425069483031902239$ | $11204049572274741228971150496$ | $-404481399366989330514090339$ | $3122559627732417814$ |
| 112:2 | $74136509212391204884539206867137397343$ | $35379661312454821599508221990895319893$ | $79940905895375410063300128609$ | $-18697160907845333113768625518$ | $-30318291682044001749519920849$ | $9045450863836793845823772581$ | $20116331853140407424$ |
| 112:3 | $76350611566391373899295699353374302278$ | $15371798230828899182352310171711028700$ | $52890654199851770884181040531$ | $-19619897726886077789960713173$ | $6593727901532680058018257750$ | $592093882245474416980211794$ | $15542020987547617312$ |
| 112:4 | $86905512091891901365077052862856758586$ | $-39631919026991730914459887637228518521$ | $612423660541806907365605514$ | $-99590287238724782070713021$ | $4674823282329954977630302434$ | $-753980093972268171476308311$ | $3445063966517381652$ |
| 112:5 | $89347371525714240147414315577994013692$ | $-59720915501032134631229043286032830781$ | $-759544851801306474481626633$ | $203099684629026599760060027$ | $-1934282351375123736627668060$ | $-75712172891663146794118309$ | $4742017272316925$ |
| 113:0 | $31284403094523909338768332648484587881$ | $27550392592547247772549518988401373590$ | $-32366526501293760429775785207$ | $10804929037542648455656998979$ | $-17462862378468683621563333275$ | $6897659622751860587159895090$ | $27485881188792238467$ |
| 113:1 | $40622734977948058977888783284931050234$ | $15787209837242755585510017757739111521$ | $-35909162289503927859798671891$ | $18708105620722261682260288689$ | $11198070944820302951523921515$ | $-404808185680889877460241407$ | $3090137899929850427$ |
| 113:2 | $74042924902535704922856823324013953387$ | $35424751983647469526002719389717110363$ | $80078942471315533207315122533$ | $-18736626880638868949106461301$ | $-30107067386745202549758784223$ | $8990782431840462324742464882$ | $20082735301237768312$ |
| 113:3 | $76252282092741922203014483994430580774$ | $15374735480425427150626651741814316023$ | $53006794519417884806886951869$ | $-19712152729610356526418260265$ | $6640992104327422213592892263$ | $582829231621190389348040269$ | $15475453368421607874$ |
| 113:4 | $86905014605769077051878263438784487500$ | $-39635685584682056361061154236455196622$ | $611436131398726114924844345$ | $-99404253676943403392004251$ | $4667379463125782248743391356$ | $-752643600892323501375439562$ | $3481457354044212244$ |
| 113:5 | $89348386764780781949423066174631592389$ | $-59721294102763284209707348546978783254$ | $-759134810844520714928658959$ | $202995956552069927565255069$ | $-1933130196943337722027652644$ | $-75728502915309764196881236$ | $4738334262867762$ |
| 114:0 | $31338524791627185143632341796762105739$ | $27584924797401892852316300396730760680$ | $-32499056786306350384471178336$ | $10843817916508145654798370859$ | $-17530601528637609020845295991$ | $6915247781650861999359846084$ | $27618436922058491046$ |
| 114:1 | $40716518586078374729987053961114389754$ | $15785184970640483208833141343636748126$ | $-36056974477421644963634889496$ | $18805600617811713117746295055$ | $11192081345312675512646130015$ | $-405139178485955154512398563$ | $3056846851342113983$ |
| 114:2 | $73949142299651243181224346949890522343$ | $35469568784754731607229437092090342561$ | $80218309429223445553399793951$ | $-18776479218498715924257312292$ | $-29894841926169362829833053764$ | $8935902785757879405258400194$ | $20049326510605867691$ |
| 114:3 | $76153487395267795560293663521929752017$ | $15377626754338418263550373800134926526$ | $53125888033679149979050466124$ | $-19805994080017037690664901776$ | $6687570387710730671694500839$ | $573703298532076513622169143$ | $15410117467332907083$ |
| 114:4 | $86904518048439151766529162964555011007$ | $-39639445469176130490205524241277570163$ | $610451450473870561010044549$ | $-99218769703656181616718664$ | $4659955713915460353119360684$ | $-751310813100531051960723228$ | $3518782300133641166$ |
| 114:5 | $89349401485425312293532534044355765320$ | $-59721672785895008129626956784195475149$ | $-758725140443673645179520810$ | $202892315805988079334086744$ | $-1931979609394014885080700786$ | $-75744733171165256149424966$ | $4734654111614055$ |
| 115:0 | $31392841960370860510912979709153264557$ | $27619545327069682806537832656613830891$ | $-32633070891478393554516522519$ | $10883118809753322621558312506$ | $-17598889076084196742736379953$ | $6932989965896043529273787119$ | $27752634830425731266$ |
| 115:1 | $40810793649453102270389687339582438259$ | $15783158437998981483569742998152891238$ | $-36207668176678362213588637924$ | $18904694864552806371056352891$ | $11186081255622870818728938933$ | $-405474646922503943007944583$ | $3022648511085653411$ |
| 115:2 | $73855159455302269848974824860521846270$ | $35514110658972368701060300589886729451$ | $80359030552553104487080560483$ | $-18816724590501020235352160869$ | $-29681617868761836412667841615$ | $8880811617050594477622467126$ | $20016108452995094055$ |
| 115:3 | $76054219438583226432795256590826634517$ | $15380472741539759872982982705783922758$ | $53248010592685881793054203985$ | $-19901463499234863047716703498$ | $6733472885800147497644072994$ | $564714244390596530207498990$ | $15345981283445313937$ |
| 115:4 | $86904022417159805033024614095355185217$ | $-39643198698964884498340852896548944111$ | $609469606123409840943473877$ | $-99033833072036090510031192$ | $4652551958526047945031132205$ | $-749981716404768176615495578$ | $3557072934023519747$ |
| 115:5 | $89350415688084208891286944435024616165$ | $-59722051549929213129732504958129126208$ | $-758315840088270583722570012$ | $202788762280149575127427607$ | $-1930830585535373988397319524$ | $-75760863957349761154911507$ | $4730976818749639$ |
| 116:0 | $31447356677697186718147493134410837268$ | $27654254957990795768410087908582928964$ | $-32768592952038273556800691913$ | $10922838491791063602544751853$ | $-17667734476248232267531413490$ | $6950888709950170869230521949$ | $27888508365808625725$ |
| 116:1 | $40905568272868537722290345673486021299$ | $15781130216249659614937657285807363653$ | $-36361323715416154749507400064$ | $19005432054224679588660440842$ | $11180071165168642273338475266$ | $-405814868616661588629402741$ | $2987502961591975053$ |
| 116:2 | $73760974387329201788948815094052206839$ | $35558376547727516454264828619821456725$ | $80501130175710570421440421623$ | $-18857369817952307557547633858$ | $-29467397402601184615816158845$ | $8825508526663951149789664840$ | $19983084094510818860$ |
| 116:3 | $75954469974700425529179571389659147963$ | $15383274121924069991148331893963072691$ | $53373241044763375000170072975$ | $-19998604319811508684820985333$ | $6778709543291218016211069540$ | $555860276828040528467182140$ | $15283012836808925013$ |
| 116:4 | $86903527709199921010571336495164310050$ | $-39646945292468464161103039184195943395$ | $608490586764891845730732581$ | $-98849441547043418188400858$ | $4645168121159198795354278030$ | $-748656296682918137768904228$ | $3596365049779808154$ |
| 116:5 | $89351429373193296799667651802782032052$ | $-59722430394369294188150653881566490591$ | $-757906909268819349408839269$ | $202685295864123986260803817$ | $-1929683122184129142938102796$ | $-75776895571039461707587605$ | $4727302384453538$ |
| 117:0 | $31502071054817440135292722126974580045$ | $27689054479415324099740980705381196551$ | $-32905647677730203601957088955$ | $10962983896501117466588218350$ | $-17737147386042323576200897878$ | $6968946603586538474614295905$ | $28026091869163904072$ |
| 117:1 | $41000850783765880573916452780867588479$ | $15779100280913604365506082975062634056$ | $-36518024546794328969628896711$ | $19107857565181758741826307413$ | $11174051571587220832725567502$ | $-406160130152284666920715431$ | $2951368216745889439$ |
| 117:2 | $73666585079075594893986848275300279451$ | $35602365390223900406983175465701991385$ | $80644633200925708919444300488$ | $-18898421879087143627566912756$ | $-29252182332813415538953103969$ | $8769993024133765747471948908$ | $19950256399155483885$ |
| 117:3 | $75854230534775597938504571580133517984$ | $15386031566539099466656876716709553604$ | $53501661384818226782177540087$ | $-20097461565254928893202508422$ | $6823290118186289253951378499$ | $547139649424939339716032695$ | $15221180100193981809$ |
| 117:4 | $86903033921839529746335252378701891949$ | $-39650685268036578799543909132458250569$ | $607514380876846963584122983$ | $-98665592905350135615427882$ | $4637804126388890548494256080$ | $-747334539882445293835186246$ | $3636696207683934267$ |
| 117:5 | $89352442541187849425098629370066671938$ | $-59722809318720129811121130127998464781$ | $-757498347476827630094149737$ | $202581916447681435259809908$ | $-1928537216165462023263278861$ | $-75792828308469986383273040$ | $4723630808890051$ |
| 118:0 | $31556987238020638829579506314156441433$ | $27723944693683930843515415069589421956$ | $-33044260370025243723657301638$ | $11003562121911925488337079862$ | $-17807137669918404184814956242$ | $6987166293540231259497791811$ | $28165420600664714660$ |
| 118:1 | $41096649740865846141947228038202211497$ | $15777068606055551667921661674134264873$ | $-36677857406830113634549327698$ | $19212018545390623707570170451$ | $11168022981449455504057664301$ | $-406510727571857291909440691$ | $2914200091012791951$ |
| 118:2 | $73571989478591411702229445664346990356$ | $35646076122982406106708214994389827418$ | $80789565115730439350543458876$ | $-18939887913933583225140521028$ | $-29035974078714363713721230080$ | $8714264526621296552532313228$ | $19917628332427726723$ |
| 118:3 | $75753492420445186316124443079421806305$ | $15388745737814895647301094572059646370$ | $53633356911798160945784387629$ | $-20198082034458366673843483321$ | $6867224184417046367292461940$ | $538550661485543564777642534$ | $15160450927600492599$ |
| 118:4 | $86902541052369748804908531746264558892$ | $-39654418643948848129980314187209059114$ | $606540976998395299538067325$ | $-98482284935264839382088996$ | $4630459899159169894354874542$ | $-746016432019973356439754573$ | $3678105843050428263$ |
| 118:5 | $89353455192502589524955763920886884431$ | $-59723188322488077338703113734551054240$ | $-757090154204800359982982493$ | $202478623920792097425726264$ | $-1927392864312994190471591102$ | $-75808662464939797898165926$ | $4719962092208834$ |
| 119:0 | $31612107409506608308052866619681219428$ | $27758926416516910652458021079315993606$ | $-33184456939972021235289591528$ | $11044580435159715679517677800$ | $-17877715406152364439766892448$ | $7005550485219076362181631175$ | $28306530771111508595$ |
| 119:1 | $41192973943238904333321516813991329742$ | $15775035164235276846860628973101532149$ | $-36840912482057258626617241008$ | $19317964002205703247206759261$ | $11161985911018653790392313090$ | $-406866966908527628342690777$ | $2875952058781650507$ |
| 119:2 | $73477185497811526831786389895379859821$ | $35689507679376640242099029735780246607$ | $80935952011070417125028391546$ | $-18981775229353867440298250358$ | $-28818773670672218173776601412$ | $8658322357874305725812878887$ | $19885202864984775353$ |
| 119:3 | $75652246694727041313946017725020476989$ | $15391417289791952482465442822187867149$ | $53768416395976954076439940246$ | $-20300514391366479511670085234$ | $6910521134358578337901098444$ | $530091657858249463364177949$ | $15100792979033190124$ |
| 119:4 | $86902049098092725271637533732038260010$ | $-39658145438415147012751276522860809407$ | $605570363728856886585630536$ | $-98299515436658263732436402$ | $4623135364781914017374727708$ | $-744701959180866692132685241$ | $3720635383113418015$ |
| 119:5 | $89354467327571690206587990931636001481$ | $-59723567405180968267386977632315715445$ | $-756682328946237105639528163$ | $202375418173625704004978136$ | $-1926250063468759522346067220$ | $-75824398334813567201646451$ | $4716296234544980$ |

### 6.15 Cells 120 through 129

| $t:i$ | $M_r$ | $M_b$ | $A_{00}$ | $A_{01}$ | $A_{10}$ | $A_{11}$ | $R_\rho$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 120:0 | $31667433788244302055162301450723376712$ | $27794000477311960095271900376928487840$ | $-33326263926715291922614226085$ | $11086046277632658047929633773$ | $-17948890893356323700334146376$ | $7024101944476886829902324803$ | $28449459574639029452$ |
| 120:1 | $41289832439838295635833728748650781682$ | $15772999926456241940956468335969865949$ | $-37007283587731787943900481520$ | $19425744897771844939050548642$ | $11155940887057711323411567313$ | $-407229164751640630677688623$ | $2874203981836089762$ |
| 120:2 | $73382171011708574564892400468322788561$ | $35732658989163107500287831375925933989$ | $81083820600078396326890376419$ | $-19024091304268205035209327814$ | $-28600581746681746668700338282$ | $8602165747111888130569994138$ | $19852982976374661933$ |
| 120:3 | $75550484172459357007411938593599870636$ | $15394046868348581898971034470187272357$ | $53906932256793586316222886043$ | $-20404809260270580743568106425$ | $6953190181232464145224297433$ | $521761028804044819452395952$ | $15042173641092987527$ |
| 120:4 | $86901558056321578126977909377877528056$ | $-39661865669575948115041635762587499300$ | $604602529727364862030509337$ | $-98117282220889356846024601$ | $4615830448934608185981917802$ | $-743391107518814643037602476$ | $3764328372683730690$ |
| 120:5 | $89355478946828775923858273403885298169$ | $-59723946566308103589541712280271006675$ | $-756274871195629460631494547$ | $202272299096551046956104599$ | $-1925108810483176750226684089$ | $-75840036211525533668415295$ | $4712633236019107$ |
| 121:0 | $31722968630856322481113621021319437466$ | $27829167719450975577315171203510675048$ | $-33469708516711918572299239809$ | $11127967270308273490577946857$ | $-18020674657228536405487596380$ | $7042823499451730636449455024$ | $28594245222782289743$ |
| 121:1 | $41387234539524998044786760790397812274$ | $15770962862111326328443184819743205209$ | $-37177068357377318332368280681$ | $19535414250475350028018445552$ | $11149888447688443491629186670$ | $-407597648848329046630948907$ | $2922401743214856200$ |
| 121:2 | $73286943857419202747718198146505683105$ | $35775528978005615888071849612704822175$ | $81233198237538958021197850186$ | $-19066843795069871417629199363$ | $-28381398548641276480397083359$ | $8545793827830606286176201313$ | $19820971658845148508$ |
| 121:3 | $75448195410248186521599648823391421821$ | $15396635111427752165415580854644478987$ | $54049000752037905209808570004$ | $-20511019327154541458641821402$ | $6995240361396039901974669295$ | $513557209915257437796553737$ | $14984559942892996462$ |
| 121:4 | $86901067924380340989067950543212162626$ | $-39665579355502662502803504509590981639$ | $603637463712481583011191014$ | $-97935583110731916437948774$ | $4608545077658139347126671925$ | $-742083863255418841128695437$ | $3809230609348592623$ |
| 121:5 | $89356490050706923471212396181054489897$ | $-59724325805380249149628694801616897644$ | $-755867780448458448772410746$ | $202169266580135485307935217$ | $-1923969102215022102132373836$ | $-75855576387582851454959871$ | $4708973096737431$ |
| 122:0 | $31778714232530629904094449335714693778$ | $27864429000616211124220976171498390535$ | $-33614818563675366430736775023$ | $11170351219292710567365668937$ | $-18093077457551433181834903338$ | $7061718042472097625985514278$ | $28740927043394113878$ |
| 122:1 | $41485189821616017294171416576774279157$ | $15768923938925453492527762412067658852$ | $-37350368444531789555507743745$ | $19647027242901931493127630713$ | $11143829143307388664600521000$ | $-407972758743951361038805903$ | $2972006024959282589$ |
| 122:2 | $73191501833342754962110082986876432276$ | $35818116566993510600105462068867580340$ | $81384112940075811785223413977$ | $-19110040541240279658861576634$ | $-28161223918322976485339942704$ | $8489205636529327988085025547$ | $19789171930754254951$ |
| 122:3 | $75345370695892154620969986991937416247$ | $15399182649263650939887381488010462333$ | $54194722179244526691507116891$ | $-20619199447549766918527993996$ | $7036680536514642734389952335$ | $505478682087119180618976899$ | $14927918466758781773$ |
| 122:4 | $86900578699603905221735842346437984250$ | $-39669286514197978176680910103739486903$ | $602675154461817655413400752$ | $-97754415940301779786445663$ | $4601279177354605591846651466$ | $-740780212679783491070701195$ | $3855390289064144089$ |
| 122:5 | $89357500639638662975283516092842247566$ | $-59724705121909631017112786033284041388$ | $-755461056201191935928324213$ | $202066320515144453102701407$ | $-1922830935531402051657241155$ | $-75871019154568922085000367$ | $4705315816791856$ |
| 123:0 | $31834672927960471365769552275529115278$ | $27899785193116143004672779960041691591$ | $-33761622609281427589567205280$ | $11213206121570950677791244765$ | $-18166110295448835909535263374$ | $7080788532033984267376582482$ | $28889545362446909075$ |
| 123:1 | $41583708146989764841728222454104352868$ | $15766883122894912205236044965626939542$ | $-37527289737633860178316978243$ | $19760641336800618971627226952$ | $11137763537562746459267187054$ | $-408354846464414946515603632$ | $3023807263464280387$ |
| 123:2 | $73095842698211358549885541542165994234$ | $35860420672153323126192912509661608429$ | $81536593407094489615380005386$ | $-19153689571173123636120761101$ | $-27940057293026438995352363482$ | $8432400111350012244474675005$ | $19757586844996487565$ |
| 123:3 | $75242000037250592166194152029192710460$ | $15401690104608243883572770201375877959$ | $54344201090233106268950194742$ | $-20729406761398227537547420185$ | $7077519395613224743663528573$ | $497523971544911738291090047$ | $14872215253118170883$ |
| 123:4 | $86900090379337963405180805248390224446$ | $-39672987163596196566718274010717002209$ | $601715590811653850643481864$ | $-97573778554984563346529569$ | $4594032674785141359101001895$ | $-739480142148108596796185030$ | $3902858163078204514$ |
| 123:5 | $89358510714055978884040376979026768979$ | $-59725084515409930876002061310610344908$ | $-755054697951282050354944162$ | $201963460792540968917838583$ | $-1921694307307726172168272546$ | $-75886364803146713328228419$ | $4701661396260047$ |
| 124:0 | $31890847092313607552324883856308047573$ | $27935237184221403654088039412983065258$ | $-33910149904669594010023360269$ | $11256540170977474808505607388$ | $-18239784420913954964739301573$ | $7100037994852072038256184588$ | $29040141629962090100$ |
| 124:1 | $41682799669784893070242606020847424680$ | $15764840378223154540472351011169161517$ | $-37707942589071395680901679645$ | $19876316395597315781652516227$ | $11131692208397549709999879679$ | $-408744277243697854303560432$ | $3078263062651329938$ |
| 124:2 | $72999964170130349401222894147612012438$ | $35902440203953408122780750640374027361$ | $81690669042514958207394221855$ | $-19197799108217165391908530361$ | $-27717897700904981623051524240$ | $8375376090631529580905484958$ | $19726219421462815056$ |
| 124:3 | $75138073150518712544697808508252745022$ | $15404158092958114239794436427047045624$ | $54497546519817287566914179029$ | $-20841700815467206781727329893$ | $7117765457003285942080052944$ | $489691649929739256060258503$ | $14817415698924839902$ |
| 124:4 | $86899602960938953166592200345019447354$ | $-39676681321563567000509845280124835459$ | $600758761656565884989024122$ | $-97393668811363947156118978$ | $4586805497067758246376670595$ | $-738183638083286107231372394$ | $3951687707218096993$ |
| 124:5 | $89359520274390310953487067496948449763$ | $-59725463985396281430947801529609790130$ | $-754648705197162611531441033$ | $201860687303485146960264051$ | $-1920559214427680095834215167$ | $-75901613623062064436314088$ | $4698009835205518$ |
| 125:0 | $31947239142231964998999203745127962970$ | $27970785876511163648970752132725431753$ | $-34060430432776308267800578052$ | $11300361764397425787802992033$ | $-18314111340620379784317199870$ | $7119469527988340408233726239$ | $29192758497391564402$ |
| 125:1 | $41782474849731796851348587299065110210$ | $15762795667252835813166800098469327132$ | $-37892442059507306035132506830$ | $19994114815050983606297438580$ | $11125615749164650265981346622$ | $-409141430300186380123689829$ | $3134350815478052150$ |
| 125:2 | $72903863925587915319986362516468630949$ | $35944174066801125585808141073709478280$ | $81846369977330484041722357723$ | $-19242377576947738936063421885$ | $-27494743755953476929498973353$ | $8318132311373433890491385002$ | $19695072743091908817$ |
| 125:3 | $75033579447870610710259122841499392982$ | $15406587222781884759852255796388729069$ | $54654872229797466941104716693$ | $-20956143693908699383604632324$ | $7157427070080583797704504689$ | $481980334446280458860456152$ | $14763484448891176642$ |
| 125:4 | $86899116441774001367994520311596270332$ | $-39680369005898619159324847785670700529$ | $599804655949052036543906791$ | $-97214084577150499288560084$ | $4579597571675201296824393608$ | $-736890686974498956816167655$ | $4001935304687195427$ |
| 125:5 | $89360529321072555231922168613897197955$ | $-59725843531385261829836690068743563224$ | $-754243077438246567457267102$ | $201757999939333709726944424$ | $-1919425653783198577017686417$ | $-75916765903146977799821598$ | $4694361133677705$ |
| 126:0 | $32003851536862892239745067799557031076$ | $28006432188230357619758773243846487936$ | $-34212494931538238933222584396$ | $11344679508208830757314619247$ | $-18389102826028912688461288422$ | $7139086301061630369579408305$ | $29347439826764399625$ |
| 126:1 | $41882744465159089222374185192209513786$ | $15760748950393842630801548401735012559$ | $-38080908178700484587444772576$ | $20114101662699822559756187627$ | $11119534769819631965047639571$ | $-409546699665781116397230974$ | $3192140661564821492$ |
| 126:2 | $72807539598432788105268205948666655923$ | $35985621158532110005327116603854177317$ | $82003727093031002545581296269$ | $-19287433609677572853725971305$ | $-27270593652645868738010761295$ | $8260667407606424254477425135$ | $19664149925986106359$ |
| 126:3 | $74928508024427767071777549622645276970$ | $15408978095748540954805169178761701082$ | $54816296969455008862049210895$ | $-21072800157610786144090739900$ | $7196512416988533482151029677$ | $474388688076212359226557925$ | $14710385278728557342$ |
| 126:4 | $86898630819220868648629801379189276417$ | $-39684050234332493536621909848149241016$ | $598853262699163574922989650$ | $-97035023731111035652378499$ | $4572408826432820633922181236$ | $-735601275376822976695863340$ | $4053660443635712282$ |
| 126:5 | $89361537854533065041765106825984501102$ | $-59726223152894893102807478520427910673$ | $-753837814174923440378517940$ | $201655398591639502225594906$ | $-1918293622274438659564945244$ | $-75931821931322897089341023$ | $4690715291712051$ |
| 127:0 | $32060686778923252780434781403162524051$ | $28042177053658168028886475677044459097$ | $-34366374918005761115195079552$ | $11389502224977011374855121465$ | $-18464770921803772952163453555$ | $7158891558541859930327748688$ | $29504230734440433724$ |
| 127:1 | $41983619626720743535747910058986655381$ | $15758700186047034567682603144273733059$ | $-38273466224152897237941834738$ | $20236344826804930773461237922$ | $11113449898198355371412676748$ | $-409960495072095431574037677$ | $3251706664927117069$ |
| 127:2 | $72710988778818760084983578946465451931$ | $36026780369891151405754369544325652291$ | $82162772045931275169955056242$ | $-19332976053218096249080228737$ | $-27045445160209846387303879539$ | $8202979908666045876562676208$ | $19633454123847953189$ |
| 127:3 | $74822847644507354067801639207701518330$ | $15411331306956994034874727935251529949$ | $54981944753878845244089786517$ | $-21191737793048428725373071219$ | $7235029514141610898198879918$ | $466915419861372768244332616$ | $14658080969506001439$ |
| 127:4 | $86898146090667894319212371337880857352$ | $-39687725024529269913246306854425723458$ | $597904570974137979237001370$ | $-96856484162998510485496373$ | $4565239189516458315891277509$ | $-734315389910831652691429936$ | $4106925930907842753$ |
| 127:5 | $89362545875201651958957498428128041596$ | $-59726602849444633617624699889400811497$ | $-753432914908556780910508238$ | $201552883152151007749381284$ | $-1917163116809752947530112679$ | $-75946781994603971943811815$ | $4687072309330080$ |
| 128:0 | $32117747415797644889391605953997410891$ | $28078021423488199734694898617642003758$ | $-34522102713408979958364507179$ | $11434838960412906270923367483$ | $-18541127954552416019979770894$ | $7178888622132789647227035295$ | $29663177636774969086$ |
| 128:1 | $42085111791893295344471120602949364934$ | $15756649330523402342321465685159866917$ | $-38470247019039258476258666686$ | $20360915175565450034486177358$ | $11107361781386495205460936433$ | $-410383242898481477500941241$ | $3313127085837825338$ |
| 128:2 | $72614209012114743538501411379754977350$ | $36067650584004195424888115925577985803$ | $82323537292446274386388938555$ | $-19379013975902988926669791046$ | $-26819295616525419314467429528$ | $8145068237365978763801023291$ | $19602988532553672260$ |
| 128:3 | $74716586727100942561304082216849522041$ | $15413647445167243254379388606024453823$ | $55151945161580780834426801403$ | $-21313027171407650946519760276$ | $7272986213602403025707571058$ | $459559285261143926213195464$ | $14606533172139844480$ |
| 128:4 | $86897662253513941605413997430298694658$ | $-39691393394086293863484650285753544103$ | $596958569898034920040773851$ | $-96678463773482432937045105$ | $4558088589450350283303587613$ | $-733033017262203706382209875$ | $4991363563809593647$ |
| 128:5 | $89363553383507586789947239584761984659$ | $-59726982620555374551342321970182327037$ | $-753028379141481630523388504$ | $201450453512811865199523771$ | $-1916034134305662978872972234$ | $-75961646379100309268684648$ | $4683432186539483$ |
| 129:0 | $32175036040672098389784779113418742023$ | $28113966265220798268609939931887516842$ | $-34679711469220924252425574476$ | $11480698990607663834617493048$ | $-18618186541903974286531529806$ | $7199080893247444895793709471$ | $29824328297792712595$ |
| 129:1 | $42187232780296548406993920766313462518$ | $15754596337958320582682727390150966808$ | $-38671387251014668660640900945$ | $20487886727452904968482518953$ | $11101271087189160891635262597$ | $-410815387187074768602941792$ | $3376484675239100254$ |
| 129:2 | $72517197797779031074228883520486475136$ | $36108230675840950801911807177398680539$ | $82486056115358524840654867285$ | $-19425556674886369630014949322$ | $-26592141921633361471727582972$ | $8086930708067050293578718753$ | $19572756394874284819$ |
| 129:3 | $74609713330530154267684758160144864723$ | $15415927093033520921687227580822471536$ | $55326433652994766009878070889$ | $-21436742018830774763937967877$ | $7310390204305209055322845416$ | $452319086588999472545250753$ | $14555702260916045669$ |
| 129:4 | $86897179305168343237960418672066318200$ | $-39695055360534501306033887965819346312$ | $596015248651374981207886798$ | $-96500960474079805175290340$ | $4550956955105043274520616520$ | $-731754144181333475859349383$ | $5076779070356523527$ |
| 129:5 | $89364560379879600546263066517060985676$ | $-59727362465749435378190546028801320985$ | $-752624206377001992357781325$ | $201348109565760387949729994$ | $-1914906671686832701671810670$ | $-75976415370021211206240590$ | $4679794923334189$ |

### 6.16 Cells 130 through 139

| $t:i$ | $M_r$ | $M_b$ | $A_{00}$ | $A_{01}$ | $A_{10}$ | $A_{11}$ | $R_\rho$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 130:0 | $32218153712873158228246534006283198190$ | $28140991422913304614236236664181580962$ | $-34799172841757960770379327496$ | $11515443139538498952680685624$ | $-18676448637089930564244623876$ | $7214355294012589156412552883$ | $7390169692910754507$ |
| 130:1 | $42264243509979975009155385737250580791$ | $15753055162235016770735002374329140321$ | $-38825189021503915771459142286$ | $20584737581727517658448507680$ | $11096701789386640998422359557$ | $-411145939493178628547262102$ | $852308428172804319$ |
| 130:2 | $72444285968772640643786641467820654839$ | $36138474670305835109508282136878726476$ | $82609116519375304209671063664$ | $-19460800684493340075502609130$ | $-26421115560803545038122576675$ | $8043178265510070997260170847$ | $4858050342260158545$ |
| 130:3 | $74529148947907200790636588564739135605$ | $15417613229330628029548360581541525053$ | $55460330313833421972126073825$ | $-21531166096018748528433428082$ | $7338085016158675024115625665$ | $446964326755679876011652215$ | $3613706613479923882$ |
| 130:4 | $86896817675637054181438424949117612074$ | $-39697797643839169868976173923574201352$ | $595309509877508792966539695$ | $-96368171089642601580788867$ | $4545620633005725653560993389$ | $-730797278027845911506370179$ | $670912052187890188$ |
| 130:5 | $89365315291459579752921848475138689840$ | $-59727647397975608087161283249950745060$ | $-752321314725846992543514369$ | $201271407776259547075161518$ | $-1914062070301982697455408253$ | $-75987429682242934772901335$ | $1169128048580750$ |
| 131:0 | $32246971456575906886053773790512988902$ | $28159040107819256775142596914720081181$ | $-34879419408780907815841922474$ | $11538774428865185320671437635$ | $-18715516046544196816015057337$ | $7224601057961926711225683365$ | $7410420938435703235$ |
| 131:1 | $42315786918708071253181044626861505936$ | $15752027018488912576023959952437069804$ | $-38929161309065617148171361296$ | $20650096031813027119912414004$ | $11093655148582384912657847032$ | $-411369488237424731679491170$ | $860576614852866534$ |
| 131:2 | $72395604420915728709071077526990066998$ | $36158546078139469135179346527664598065$ | $82691722699134604891369938138$ | $-19484459437213420849589467025$ | $-26306782272328003579290781086$ | $8013938436645100438945877030$ | $4854397369059874426$ |
| 131:3 | $74475241482149262104335594599130123055$ | $15418726216474862923124352250924448773$ | $55551072102781289661091395515$ | $-21594914128672487892150102165$ | $7356379397349032296595260533$ | $443430125279734372496938588$ | $3607475447357010833$ |
| 131:4 | $86896576865693228533677401152019748193$ | $-39699623840823326605469542944943984963$ | $594839849211185146601518977$ | $-96279805343567100703575604$ | $4542068974914052176751982712$ | $-730160454016553657274594014$ | $674022164893375752$ |
| 131:5 | $89365818406089814042582962755145923040$ | $-59727837375696267861940033386155575921$ | $-752119500138681204199234589$ | $201220299972719327774920061$ | $-1913499476079993862129488677$ | $-75994742894502818829673662$ | $1168673990479571$ |
| 132:0 | $32275847698565323123151919006815074166$ | $28177114470527981955647766589015106707$ | $-34960155643638767306856174343$ | $11562241976131781453239870536$ | $-18754766215395902865152612300$ | $7234897611936744499946766951$ | $7430814548299995724$ |
| 132:1 | $42367494527630771041778490122659520569$ | $15750998312613751032677237414114052446$ | $-39034306044948691379313313610$ | $20716099479871622936654454981$ | $11090608259692782792469223197$ | $-411595653120763456260118385$ | $868978082759339499$ |
| 132:2 | $72346863561887975487810460676826574464$ | $36178544314562022357761138038649066744$ | $82774786771351634759501889550$ | $-19508249828781470440871677538$ | $-26192195800224999139662851944$ | $7984641095093640354537906696$ | $4850759339635405266$ |
| 132:3 | $74421173834850324017265855090692000017$ | $15419830403584490938082655492868412961$ | $55643017826690420916922241861$ | $-21659313065448617996188706980$ | $7374539781076939423616293574$ | $439924276862691573276550600$ | $3601282060989163848$ |
| 132:4 | $86896336276503580183241775041934367312$ | $-39701448446832166442788621656617419019$ | $594370852466546549994083271$ | $-96191567704908970150600844$ | $4538522018550832065666877895$ | $-729524497501960259315468785$ | $677169608502333765$ |
| 132:5 | $89366321392977245494245684313749464432$ | $-59728027371670339962021380627307510145$ | $-751917776023640213727840356$ | $201169213531753132763836685$ | $-1912937260106726030216076763$ | $-76002032417993767086432284$ | $1168220111076988$ |
| 133:0 | $32304782781047398164838463308848529313$ | $28195214638584651033219391331906969249$ | $-35041386022132910799281322232$ | $11585847032939198653637851131$ | $-18794200837120043508893436324$ | $7245245412951446995163125378$ | $7451352121530939185$ |
| 133:1 | $42419367962411038195824270343666768470$ | $15749969037990756961779282000154480142$ | $-39140642777967816797088077338$ | $20782758500391003221774438116$ | $11087561215184916550976870825$ | $-411824497112414393273263223$ | $877515889166700506$ |
| 133:2 | $72298063061028485779992155562649603996$ | $36198469235477123546489425728219593478$ | $82858313226932808314174869758$ | $-19532173112891406265439940273$ | $-26077355587521257153576978366$ | $7955285987922556823156897804$ | $4847136360800315918$ |
| 133:3 | $74366944365625666922974005226305794404$ | $15420925861376879051665627464686224984$ | $55736186887292881270944401077$ | $-21724373445986543345783461226$ | $7392567067990289609083352443$ | $436446649791518333136862254$ | $3595125054836909821$ |
| 133:4 | $86896095907748162028519009394546603762$ | $-39703271464032390032060472212936731483$ | $593902518312067448488601001$ | $-96103457916625277517741327$ | $4534979755153230099946132841$ | $-728889406851849045138238654$ | $680355031930048581$ |
| 133:5 | $89366824252175263777881097130333681703$ | $-59728217385838646621318306385765787278$ | $-751716142318998524863260804$ | $201118148439950900771835419$ | $-1912375422000796139541832438$ | $-76009298288031515131355883$ | $1167766410371518$ |
| 134:0 | $32333777049377394657004889474356232140$ | $28213340740683973733027294172770060594$ | $-35123115078660937080232059550$ | $11609590867148246781249236061$ | $-18833821625710939774694912864$ | $7255644923637913682681413529$ | $7472035280848679450$ |
| 134:1 | $42471408875451485892893411497105623425$ | $15748939187842009973781474230555547538$ | $-39248191511565996029592438304$ | $20850083911795099754031282037$ | $11084514109229993397659858443$ | $-412056084566457817854020681$ | $886193182129714582$ |
| 134:2 | $72249202584521965121800003659211313270$ | $36218320696146968802103966938051434648$ | $82942306615183644153517985124$ | $-19556230559413603704439875750$ | $-25962261048127096187869182351$ | $7925872854906235010863868476$ | $4843528540411788371$ |
| 134:3 | $74312551407437701006887981647653503403$ | $15422012660243956376444105068020460925$ | $55830599141970080019203871263$ | $-21790106054134745414384395598$ | $7410462148735235540380567921$ | $432997115433329467657335988$ | $3589002998490685464$ |
| 134:4 | $86895855759107668747212642032186595933$ | $-39705092894586622428843935237264048126$ | $593434845419667899336621135$ | $-96015475722335153940118062$ | $4531442175979575348824195201$ | $-728255180437958264045813640$ | $683579099302803993$ |
| 134:5 | $89367326983737225053379235625004285526$ | $-59728407418142098293626234503396890058$ | $-751514598963090613204244468$ | $201067104683914625757215225$ | $-1911813961381323867848062247$ | $-76016540539876249903148679$ | $1167312888361469$ |
| 135:0 | $32362830852100833058007045221582365753$ | $28231492906684357115384628625174725061$ | $-35205347407190490490643497236$ | $11633474763149859089420052186$ | $-18873630316019978887497021680$ | $7266096612337642994417626677$ | $7492865673110805859$ |
| 135:1 | $42523618946513266490060110054663074238$ | $15747908755226928175604940925143648198$ | $-39356972717459618080320190874$ | $20918086783727101425465405690$ | $11081467037767159449440753028$ | $-412290481265412316694985849$ | $895013203801265965$ |
| 135:2 | $72200281795357939776764217464703009181$ | $36238098551173994925185398775235458275$ | $83026771544788267314980101443$ | $-19580423454666891898301455957$ | $-25846911566572647708287852888$ | $7896401428449904412662297967$ | $4839935987413702086$ |
| 135:3 | $74257993265976397492202274668132601616$ | $15423090870259948058264874377748416024$ | $55926274917388998551665052711$ | $-21856521925231268899288812985$ | $7428225903969404012827555948$ | $429575548262503408189961069$ | $3582914428993447536$ |
| 135:4 | $86895615830263435143793251007077892950$ | $-39706912740653422965687033869919870993$ | $592967832464702658066299182$ | $-95927620866317707541913292$ | $4527909272309298132676556437$ | $-727621816635969296464698840$ | $686842490405863787$ |
| 135:5 | $89367829587716452000668624470820732009$ | $-59728597468521693513875619798402954434$ | $-751313145894310848336270484$ | $201016082250258342085687098$ | $-1911252877867930818165331479$ | $-76023759208732709026917885$ | $1166859545044938$ |
| 136:0 | $32391944540995160460534160396599754306$ | $28249671267622296721130889391943497513$ | $-35288087662252992187172478710$ | $11657500022140833307395153087$ | $-18913628664100099257499090989$ | $7276600953195741993245185597$ | $7513844969767006603$ |
| 136:1 | $42575999883353500852118012579752770324$ | $15746877733038640919631625804774632691$ | $-39467007349786210909851514840$ | $20986778444599934917635887019$ | $11078420098569782107681220344$ | $-412527754465435349680590698$ | $903979293894498364$ |
| 136:2 | $72151300353289289897988324395205207251$ | $36257802654482358595852007221649531468$ | $83111712684808751070908322245$ | $-19604753101696043053584779504$ | $-25731306497736603001813686122$ | $7866871433510955721113666764$ | $4836358811880558687$ |
| 136:3 | $74203268219021186690724654708871294981$ | $15424160561189179190696848537040911860$ | $56023235023641194130755650653$ | $-21923632353651691239040422920$ | $7445859204371886364647135786$ | $426181825889591151330172487$ | $3576857849087692536$ |
| 136:4 | $86895376120897434502156055894889177288$ | $-39708731004387295095260085488196244494$ | $592501478125950305749798120$ | $-95839893093509944672053403$ | $4524381035442867208452489855$ | $-726989313825494905152302056$ | $690145901147379043$ |
| 136:5 | $89368332064166233849798795508386184665$ | $-59728787536918518759632622185736996027$ | $-751111783051113416080945658$ | $200965081125608109733011153$ | $-1910692171080739705752841792$ | $-76030954329750279946833863$ | $1166406380419811$ |
| 137:0 | $32421118471112115800015010948839338583$ | $28267875955727005044318432125871783007$ | $-35371340559957766011084066461$ | $11681667962405222321512475001$ | $-18953818447557181900574961606$ | $7287158426256805996401004139$ | $7534974867324040729$ |
| 137:1 | $42628553422381930314217256024378762375$ | $15745846114000246448022847164519900427$ | $-39578316859776896248160595977$ | $21056170489425887427052522170$ | $11075373391314315114891738370$ | $-412767972943218723789696212$ | $913094893296556166$ |
| 137:2 | $72102257914790081961430416435578973675$ | $36277432859299216291047074469092968120$ | $83197134765704780577304722205$ | $-19629220820554888867566620811$ | $-25615445166567332889717669937$ | $7837282587518206849172744346$ | $4832797125062281185$ |
| 137:3 | $74148374515783639664948061417558073938$ | $15425221802493953316237613629234009430$ | $56121500768906590034747766331$ | $-21991448900636259938621953517$ | $7463362910649897986861896621$ | $422815829092088723684478514$ | $3570831725382662026$ |
| 137:4 | $86895136630692276943465732554070614853$ | $-39710547687938696204168998129548928452$ | $592035781085602416991621676$ | $-95752292149504698892169002$ | $4520857456701727178068359924$ | $-726357670390067528108624248$ | $693490044038886700$ |
| 137:5 | $89368834413139826410985840705034984303$ | $-59728977623273748312847358917916945877$ | $-750910510372012240872636441$ | $200914101296601999511187533$ | $-1910131840640373546599099106$ | $-76038125938023098856044818$ | $1165953394483770$ |
| 138:0 | $32450353000820805744130132972448695701$ | $28286107104435282113555384775750695913$ | $-35455110879027054125108779286$ | $11705979919601511544286938471$ | $-18994201465908514178206658293$ | $7297769517562733550186500310$ | $7556257087821301096$ |
| 138:1 | $42681281329337504354254070496884620882$ | $15744813890660950101289501146862884698$ | $-39690923210976677262152479987$ | $21126274787937649234302621788$ | $11072327017651866200498586850$ | $-413011207044654648070764917$ | $922363547841639309$ |
| 138:2 | $72053154133012686231563609297857209753$ | $36296989018135799757922808794563858815$ | $83283042580374134262843267929$ | $-19653827948595201406791869221$ | $-25499326867796221340832029778$ | $7807634600289074393532281501$ | $4829251039429918917$ |
| 138:3 | $74093310376230220361955802388265770349$ | $15426274663342510264683328398217524695$ | $56221093974665181883709551599$ | $-22059983402408475225023033241$ | $7480737873541994125698597131$ | $419477441847147088973136471$ | $3564834486437254549$ |
| 138:4 | $86894897359331207789169102472466825993$ | $-39712362793454047397552797181030785891$ | $591570740029252768461707046$ | $-95664817780548567683407980$ | $4517338527428236118840750970$ | $-725726884717127613020153234$ | $696875648693095768$ |
| 138:5 | $89369336634690452104621059985623786374$ | $-59729167727528644121849228671067811259$ | $-750709327795580908262085417$ | $200863142749890078318155120$ | $-1909571886167954847480405267$ | $-76045274068590149424316619$ | $1165500587234283$ |
| 139:0 | $32479648491851505905510797895024046542$ | $28304364848406633078462605425585647850$ | $-35539403461852431502345093559$ | $11730437247055723912356854596$ | $-19034779540948496360033444379$ | $7308434719252523433621686952$ | $7577693379317250950$ |
| 139:1 | $42734185399985648521590956517444948521$ | $15743781055392078566029573282213920254$ | $-39804848895036873469572323008$ | $21197103493013681220305876973$ | $11069281081282593577743741284$ | $-413257528735351944743845759$ | $931788912251532268$ |
| 139:2 | $72003988657744164672612791864918079637$ | $36316470982768281750950713736825960946$ | $83369440985214492763136367537$ | $-19678575840761479625784668457$ | $-25382950865643049427451143794$ | $7777927173944605544697844938$ | $4825720668722290383$ |
| 139:3 | $74038073990384363609202512434489379926$ | $15427319212617068268738344993248906247$ | $56322036991480973738378665515$ | $-22129247978598022867321156261$ | $7497984933817722790816953408$ | $416166551366297346190280650$ | $3558864520753892570$ |
| 139:4 | $86894658306498105929156441178477090664$ | $-39714176323075743254568998464392096656$ | $591106353645886587797968994$ | $-95577469733539856838840974$ | $4513824238985603435043005027$ | $-725096955198011993064592596$ | $700303462339691160$ |
| 139:5 | $89369838728871299991242762646963807561$ | $-59729357849624555663588802375968118496$ | $-750508235260452587546762465$ | $200812205472134394410952090$ | $-1909012307285104797573715757$ | $-76052398756435361323867105$ | $1165047958668617$ |

### 6.17 Cells 140 through 149

| $t:i$ | $M_r$ | $M_b$ | $A_{00}$ | $A_{01}$ | $A_{10}$ | $A_{11}$ | $R_\rho$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 140:0 | $32509005309340202377001098715223919812$ | $28322649323538637816019326426033459317$ | $-35624223215573142719474564015$ | $11755041316060597429710905966$ | $-19075554517121766274811553542$ | $7319154529664101673793370528$ | $7599285516387025410$ |
| 140:1 | $42787267460836990253432724314643268811$ | $15742747600382965432690524442378850596$ | $-39920116948105270158358526454$ | $21268669049421476314250048824$ | $11066235688033064287518394970$ | $-413507011653086127353299360$ | $941374754252244681$ |
| 140:2 | $71954761135361914360659003703129686660$ | $36335878604218426626262067734054883839$ | $83456334901207099568226446406$ | $-19703465869891786685200662281$ | $-25266316393513261252524401269$ | $7748160002822324129818584730$ | $4822206127993597239$ |
| 140:3 | $73982663517607101278136024138477325776$ | $15428355518921955496702437441443951479$ | $56424352715383710436337740649$ | $-22199255040981625879141377118$ | $7515104922273588797217498161$ | $412883048132273218808872363$ | $3552920174678301638$ |
| 140:4 | $86894419471877482195052233141829521263$ | $-39715988278942161554870016436250728249$ | $590642620627869842703847424$ | $-95490247756026532508361422$ | $4510314582757827929673077231$ | $-724467880227942303905865090$ | $703774250359920585$ |
| 140:5 | $89370340695735525801471280953227281100$ | $-59729547989502919806125776865762046499$ | $-750307232705319954527701355$ | $200761289450008962702292508$ | $-1908453103613942461620414381$ | $-76059500036487708553863034$ | $1164595508783828$ |
| 141:0 | $32538423821873888956252208051637223002$ | $28340960666982577693203504668572276920$ | $-35709575113176899335813687866$ | $11779793516180984275576027242$ | $-19116528261903922229979860704$ | $7329929453438227902315028279$ | $7621035300631498156$ |
| 141:1 | $42840529369888355002830624164475261379$ | $15741713517636703119513638463460764296$ | $-40036750967840876077930129252$ | $21340984202892986710458804293$ | $11063190945936714525205856366$ | $-413759731162271437548891393$ | $951124958875909571$ |
| 141:2 | $71905471208788551083905845172616977049$ | $36355211732734020269243872961305200603$ | $83543729315022812375305026149$ | $-19728499427024787329317258054$ | $-25149422653686938511155026187$ | $7718332773386843112550513314$ | $4818707533662043796$ |
| 141:3 | $73927077085855424129641831229491531520$ | $15429383650591836352515862189299539002$ | $56528064604875299143404988069$ | $-22270017302556086676652907764$ | $7532098659725195776488569672$ | $409626825938017231024270838$ | $3546999750199847780$ |
| 141:4 | $86894180855154477738616283131085461953$ | $-39717798663187672976173370825597777545$ | $590179539670938570067265869$ | $-95403151596204180863144241$ | $4506809550149636095524912860$ | $-723839658206013441709632851$ | $707288796840767307$ |
| 141:5 | $89370842535336251965907254395220559530$ | $-59729738147105260671362488580831186426$ | $-750106320068935114392573091$ | $200710394670199750080513216$ | $-1907894274777083974637564608$ | $-76066577943621307564046583$ | $1164143237576766$ |
| 142:0 | $32567904401536635804232142065457265658$ | $28359299017159324747384505903174016624$ | $-35795464194623691446642128511$ | $11804695255565624731413911464$ | $-19157702666190029451554754817$ | $7340760001624531772074747834$ | $7642944561198122815$ |
| 142:1 | $42893973017386881703442662707321766383$ | $15740678798965755992842491637803593046$ | $-40154775131081588185525449581$ | $21414062009547233090307643174$ | $11060146965317559660891758562$ | $-414015764410547573788028067$ | $961043532957627223$ |
| 142:2 | $71856118517446017439989680646513342022$ | $36374470217769073710479462943595087919$ | $83631629280151099440327349214$ | $-19753677921713138815491684476$ | $-25032268816999305226474808239$ | $7688445164138194469440313205$ | $4815225003559497517$ |
| 142:3 | $73871312790917530254792966189997714093$ | $15430403675700038115197585848893328545$ | $56633196698589218120904646322$ | $-22341547786958535666704599514$ | $7548966956995425366691018937$ | $406397781927961624052061832$ | $3541101502646746291$ |
| 142:4 | $86893942456014862415236176133515641494$ | $-39719607477942650763028031635987416005$ | $589717109474188244928259105$ | $-95316181002913975346888117$ | $4503309132586420624659823100$ | $-723212287535182062010375448$ | $710847905149551039$ |
| 142:5 | $89371344247726567644993242982238632570$ | $-59729928322373189498022485737108500145$ | $-749905497290109524724747873$ | $200659521119404660752845412$ | $-1907335820397641738173205860$ | $-76073632512655515177957117$ | $1163691145044078$ |
| 143:0 | $32597447423956445670806387987198484883$ | $28377664513775498674507214867791130107$ | $-35881895567993182801078462315$ | $11829747961265453553417644837$ | $-19199079644691100530375554636$ | $7351646691789731587836481734$ | $7665015155313868186$ |
| 143:1 | $42947600326618145113122279261181675815$ | $15739643435987429276054085105053871370$ | $-40274214212194550984606355528$ | $21487915845675900794223215820$ | $11057103858877309701101335463$ | $-414275190387578765509223772$ | $971134609837521082$ |
| 143:2 | $71806702697208899350050821698395724282$ | $36393653907963794660619416365234824256$ | $83720039918052551018754445468$ | $-19779002782343393257838400037$ | $-24914854022512578914104881521$ | $7658496845517825912945381648$ | $4811758656982227204$ |
| 143:3 | $73815368695624072508094610997501622295$ | $15431415662066983723454023876076062856$ | $56739773633632699469512866100$ | $-22413859838249690951184762404$ | $7565710614898504700160767466$ | $403195816641680001010407899$ | $3535223638270099077$ |
| 143:4 | $86893704274145033172492159680199478935$ | $-39721414725333480366878821036461020623$ | $589255328740063189123374084$ | $-95229335725640651481226511$ | $4499813321514179135378586939$ | $-722585766622255119261861407$ | $714452398529840892$ |
| 143:5 | $89371845832959528758838727821300456855$ | $-59730118515248404504873658526870605977$ | $-749704764307713918638098145$ | $200608668784333521611965400$ | $-1906777740099223618102271705$ | $-76080663778355026316212717$ | $1163239231182203$ |
| 144:0 | $32627053268352914220222880253909553097$ | $28396057297839897147331556588677382957$ | $-35968874410656275189471153850$ | $11854953079558600930682516644$ | $-19240661136338745763656992087$ | $7362590048128088784888320855$ | $7687248968830576323$ |
| 144:1 | $43001413254719213125581340111106394051$ | $15738607420119188088779318811337542063$ | $-40395093602140576098999597609$ | $21562559417908563876317551528$ | $11054061741786054473281797959$ | $-414538089986168063908400652$ | $981402454278889144$ |
| 144:2 | $71757223380356934509017988847624759942$ | $36412762651124321066584055286744981849$ | $83808966419335492295068002665$ | $-19804475456462573758850806279$ | $-24797177377178978974791788897$ | $7628487479812212435643472069$ | $4808308614742756791$ |
| 144:3 | $73759242829034476783883161389569945239$ | $15432419677268736757683963898105702079$ | $56847820664643050723171425588$ | $-22486967131076769823755753669$ | $7582330424219804723118597819$ | $400020834060010921703427846$ | $3529364311710336739$ |
| 144:4 | $86893466309232012443775603757288892230$ | $-39723220407482569057530371243035459414$ | $588794196174346019435789812$ | $-95142615514510489192851661$ | $4496322108399453115799234443$ | $-721960093877878446903639100$ | $718103120719608272$ |
| 144:5 | $89372347291088158017008557124910735618$ | $-59730308725672690754195428080771774042$ | $-749504121060678228037295738$ | $200557837651708067625779105$ | $-1906220033505932143959715501$ | $-76087671775429971520314760$ | $1162787495987377$ |
| 145:0 | $32656722317585711400480048049630340695$ | $28414477511680205121977415243891617650$ | $-36056405970471444651505019617$ | $11880312076282254830008335193$ | $-19282449104698194858479457413$ | $7373590601574153418473509849$ | $7709647916783082779$ |
| 145:1 | $43055413793517609838912822020055791003$ | $15737570742573820694051137149767526875$ | $-40517439328285661220441101348$ | $21638006773775064430231888405$ | $11051020731776691876708133736$ | $-414804546065795255545402574$ | $991851467613993267$ |
| 145:2 | $71707680195526695879832108168667226610$ | $36431796294202210659516059753204297560$ | $83898414044957301041639794669$ | $-19830097411111591361179501308$ | $-24679237955494697485345059661$ | $7598416721054029106762013188$ | $4804874999222873955$ |
| 145:3 | $73702933185597360287637884793842223939$ | $15433415788645664931528106511236498618$ | $56957363683591153666699931084$ | $-22560883681233579193670073403$ | $7598827165691202766088712210$ | $396872741653760218866999119$ | $3523521623339233616$ |
| 145:4 | $86893228560963446546942274425530165410$ | $-39725024526508355506111720040965837572$ | $588333710486147135080938586$ | $-95056020120289302630054228$ | $4492835484729267083149672138$ | $-721335267716525377776959116$ | $721800936592594089$ |
| 145:5 | $89372848622165444948274895675100954324$ | $-59730498953587920015489496076592717243$ | $-749303567487991507003356673$ | $200507027708261927250395037$ | $-1905662700242363709807437660$ | $-76094656538536014277437625$ | $1162335939455633$ |
| 146:0 | $32686454958203901223543175798970359025$ | $28432925298959988930893991653026543199$ | $-36144495567006469453417037413$ | $11905826437171556341444985045$ | $-19324445538389897222607932628$ | $7384648889917857404936794746$ | $7732213943960448952$ |
| 146:1 | $43109603970397200152069810992006210008$ | $15736533394354439752733243249216337245$ | $-40641278074994422936683085161$ | $21714272312683514928781866062$ | $11047980949243282172108258827$ | $-415074643518692679332632000$ | $1002486193129732575$ |
| 146:2 | $71658072767662432915773699104356831572$ | $36450754683273680328998796651048586107$ | $83988388127451050639423982103$ | $-19855870133165674662651130373$ | $-24561034799144631747370451734$ | $7568284214920829959134650995$ | $4801457934427834082$ |
| 146:3 | $73646437724284033972283577252928825191$ | $15434404063311228679329300232758665243$ | $57068429240366954126376840836$ | $-22635623856636252427909036655$ | $7615201609961833103007345021$ | $393751450435094696853461226$ | $3517693616470227091$ |
| 146:4 | $86892991029027604087981737816520857145$ | $-39726827084525319339642210106557918406$ | $587873870387894244358243220$ | $-94969549294380437436538691$ | $4489353442011067957888494471$ | $-720711286556485404724322160$ | $725546732823913704$ |
| 146:5 | $89373349826244345930332735658369889122$ | $-59730689198936050629433658033878141301$ | $-749103103528701855304187799$ | $200456238940740607866240520$ | $-1905105739933607776631617223$ | $-76101618102274448146664410$ | $1161884561582799$ |
| 147:0 | $32716251580496117758589984398994564201$ | $28451400804695981104251135364412081652$ | $-36233148592786187751082513451$ | $11931497668205704609806521155$ | $-19366652451519914014479947929$ | $7395765457922013885181959557$ | $7754949025490667477$ |
| 147:1 | $43163985849192059064780433890655616234$ | $15735495366249315091162840105439918795$ | $-40766637205042142171667393703$ | $21791370797333389260919289506$ | $11044942517343521516662781213$ | $-415348469338579464376700671$ | $1013311321706199304$ |
| 147:2 | $71608400717966052759272851787577792656$ | $36469637663518589018106594574104341751$ | $84078894072178117055991976287$ | $-19881795129681988906456548775$ | $-24442566916637671954908140227$ | $7538089598631176160262034133$ | $4798057546041801521$ |
| 147:3 | $73589754367694025905804880014012585466$ | $15435384568160901715258847086690139091$ | $57181044564183640713248770616$ | $-22711202388734098046309688567$ | $7631454517564038949984914096$ | $390656875011746125679913202$ | $3511878274429304241$ |
| 147:4 | $86892753713113374369684291327949227471$ | $-39728628083643990667298944745699839155$ | $587414674595321930300412526$ | $-94883202788822775450531227$ | $4485875971772664651771486479$ | $-720088148819852881207624456$ | $729341418580974980$ |
| 147:5 | $89373850903377784219479026673270777000$ | $-59730879461659127372078184484337764442$ | $-748902729121916342029889927$ | $200405471335901481237276074$ | $-1904549152205246076267059023$ | $-76108556501192293687128342$ | $1161433362364502$ |
| 148:0 | $32746112578541615588313273409885072484$ | $28469904175275662009769129011109327462$ | $-36322370514566941416308428991$ | $11957327295961453072267202397$ | $-19409071884119321265211991779$ | $7406940857442282764051019040$ | $7777855167439212987$ |
| 148:1 | $43218561531109438831701879425125811750$ | $15734456648826531178449870086676883396$ | $-40893544781884121560015906308$ | $21869317365584227647342551578$ | $11041905562105538833788720919$ | $-415626112692181330812779655$ | $1024331697721919538$ |
| 148:2 | $71558663663846223217169922836633897228$ | $36488445079199157689726541254946873640$ | $84169937358607406931682897838$ | $-19907873928254626491070143892$ | $-24323833282932331149095634142$ | $7507832500838154963433095175$ | $4794673961484571499$ |
| 148:3 | $73532881001131512361788391950996310860$ | $15436357369881230745362596635473162987$ | $57295237585839211095818519971$ | $-22787634384376085204647327329$ | $7647586638874328419335374424$ | $387588933644151082998848543$ | $3506073517478413007$ |
| 148:4 | $86892516612910265805286898603364030244$ | $-39730427525970959578485641064212484346$ | $586956121827461255152560490$ | $-94796980356288746797352558$ | $4482403065562167868985461957$ | $-719465852932515761780646350$ | $733185926240839614$ |
| 148:5 | $89374351853618649980255482599778190062$ | $-59731069741699281319284275355594802734$ | $-748702444206800929352572757$ | $200354724880513768993262967$ | $-1903992936683351816845176180$ | $-76115471769782395188518356$ | $1160982341796165$ |
| 149:0 | $32776038350262213439203614993777284761$ | $28488435558475144553298605143484757388$ | $-36412166874638381678349732667$ | $11983316867974184026868434894$ | $-19451705902592849728192415177$ | $7418175647549664217563095155$ | $7800934407421822410$ |
| 149:1 | $43273333155682999827050265589243098820$ | $15733417232428462183309866103144989453$ | $-41022029592823179123765039939$ | $21948127542801605945486837669$ | $11038870212539231684248648203$ | $-415907664993670135286033250$ | $1035552325240441443$ |
| 149:2 | $71508861218866578850941610904841609171$ | $36507176773638419766151777739919429300$ | $84261523541621883093994421604$ | $-19934108077377156146936913114$ | $-24204832839052498233249230390$ | $7477512541520229181893025201$ | $4791307309969617583$ |
| 149:3 | $73475815471651490719687936399925550398$ | $15437322534959041836390589709266747397$ | $57411036960876249430577955638$ | $-22864935338154616232508318174$ | $7663598714069125314739180855$ | $384547548305659250963323853$ | $3500277199743988727$ |
| 149:4 | $86892279728108404337079684256982628608$ | $-39732225413608885612802311912349215621$ | $586498210806629403514233181$ | $-94710881750082349343783170$ | $4478934714947930119475198778$ | $-718844397324144382252399518$ | $737081212135216011$ |
| 149:5 | $89374852677019800315055122907211713641$ | $-59731260038998729711404094050592381586$ | $-748502248722580396410437395$ | $200303999561358528135039035$ | $-1903437092994488889762236211$ | $-76122363942483517204406162$ | $1160531499873011$ |

### 6.18 Cells 150 through 159

| $t:i$ | $M_r$ | $M_b$ | $A_{00}$ | $A_{01}$ | $A_{10}$ | $A_{11}$ | $R_\rho$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 150:0 | $32806029297475150171110851275759126250$ | $28506995103477368339174556564916862472$ | $-36502543292153332044238886223$ | $12009467953106754037609729025$ | $-19494556600176993663698626737$ | $7429470394655583755633215184$ | $7824188815231901161$ |
| 150:1 | $43328302901757526581750522486375145116$ | $15732377107166057135594637680472897404$ | $-41152121173118360834259917683$ | $22027817254703215620798587172$ | $11035836600752369126236408998$ | $-416193219982164826297003345$ | $1046978374493854082$ |
| 150:2 | $71458992992693011045478579385412088522$ | $36525832589198395291053058723617397697$ | $84353658252853083626583342719$ | $-19960499146812923505581584053$ | $-24085564491693088217871049876$ | $7447129331869355118785538226$ | $4787957722563511111$ |
| 150:3 | $73418555587074472656407602299254398457$ | $15438280129690801286068749571761291993$ | $57528472093682996799974189902$ | $-22943121145249432261412784868$ | $7679491473075093279679213530$ | $381532644745950273351188183$ | $3494487105575387598$ |
| 150:4 | $86892043058398531859954623292782238821$ | $-39734021748656507202014800192134871653$ | $586040940258419363978241610$ | $-94624906724137175482702375$ | $4475470911518485943593328618$ | $-718223780428180279378613791$ | $741028257324333355$ |
| 150:5 | $89375353373634059293692605865395113341$ | $-59731450353499775818201888846720590850$ | $-748302142608538263315882844$ | $200253295365228636562757994$ | $-1902881620765711078164507482$ | $-76129233053680440888850874$ | $1160080836590062$ |
| 151:0 | $32836085825946872799687984780498168888$ | $28525582960890609850643785840035986027$ | $-36593505464486424433720044323$ | $12035782141926308345329956012$ | $-19537626097407827534743820518$ | $7440825672639634283053520832$ | $7847620493482964259$ |
| 151:1 | $43383472988506409143550646174919498802$ | $15731336262912927353675609934894885295$ | $-41283849831080355420091571263$ | $22108402840729171828036140540$ | $11032804862071702670706594050$ | $-416482873802443433726153540$ | $1058615188679805493$ |
| 151:2 | $71409058591040022431148770627931198474$ | $36544412367257981905442683957417805967$ | $84446347202044351086115287335$ | $-19987048727973301448115378338$ | $-23966027112815357044311263378$ | $7416682474176305015926806864$ | $4784625332246760681$ |
| 151:3 | $73361099114968417422997558197428321731$ | $15439230220192139199599356038444863804$ | $57647573162581197291491507369$ | $-23022208114795769147918864117$ | $7695265635513798640070028802$ | $378544152557807252169900253$ | $3488700945729466692$ |
| 151:4 | $86891806603472004649878138771736916429$ | $-39735816533208651084122783271606970297$ | $585584308911689649101008488$ | $-94539055033014446216635906$ | $4472011646882492347207112386$ | $-717604000681825049919406204$ | $745028068401011537$ |
| 151:5 | $89375853943514217982938411011888115716$ | $-59731640685144808804015710377513536476$ | $-748102125804016715287393402$ | $200202612278928778627047548$ | $-1902326519624561266946951162$ | $-76136079137704060136736157$ | $1159630351942138$ |
| 152:0 | $32866208345447776728020171050922901493$ | $28544199282767315376655075657500551673$ | $-36685059168622245622118742268$ | $12062261047089268306639020952$ | $-19580916542598776584088812787$ | $7452242062980042518374526333$ | $7871231578266534553$ |
| 152:1 | $43438845676483231876646521868455283931$ | $15730294689299227914297948009625372916$ | $-41417246674201648254275198116$ | $22189901067962018967255497895$ | $11029775135169340412137425497$ | $-416776725089024185458587548$ | $1070468291089644445$ |
| 152:2 | $71359057615616125530639762752609195257$ | $36562915948190555567001507711807533491$ | $84539596178443509612412273236$ | $-20013758434304094470972750327$ | $-23846219539231641290097836016$ | $7386171561713128153175973330$ | $4781310273976121428$ |
| 152:3 | $73303443781596563034750295063034691278$ | $15440172872407544357869361417753946473$ | $57768371145948755829963158084$ | $-23102212983802232819774776211$ | $7710921910640463255505536114$ | $375582005247403446254560835$ | $3482916354170325924$ |
| 152:4 | $86891570363020791797269399503653197520$ | $-39737609769356241689624461304354048083$ | $585128315498554053539942107$ | $-94453326431901052508999147$ | $4468556912668669446400085252$ | $-716985056526029248901932470$ | $749081678326310445$ |
| 152:5 | $89376354386713034476016928116542549464$ | $-59731831033876303593159235095595314305$ | $-747902198248416526904964446$ | $200151950289275430703041717$ | $-1901771789199070654262112302$ | $-76142902228831477528293606$ | $1159180045923862$ |
| 153:0 | $32896397269807918881317558527507497712$ | $28562844222623263582162942235284832413$ | $-36777210262573752953093302664$ | $12088906303734701932849585349$ | $-19624430112328594489446065549$ | $7463720154886929111176391661$ | $7895024239825933789$ |
| 153:1 | $43494423268708877270181154019806106484$ | $15729252375705324535140612582749191444$ | $-41552343636372168253516179620$ | $22272329145623341530807297781$ | $11026747562194654306592631108$ | $-417074875053782858814316644$ | $1082543392586441835$ |
| 153:2 | $71308989664068264983961284468295594821$ | $36581343171341273774988688012371177449$ | $84633411052225749540634413928$ | $-20040629901680307354217790282$ | $-23726140572179275779906136671$ | $7355596178612682734950215613$ | $4778012684748425633$ |
| 153:3 | $73245587270829747750755792285001391123$ | $15441108152120239365420851385818415373$ | $57890897849427960980982020504$ | $-23183152931645301627252491916$ | $7726460997276543749347123708$ | $372646140308267763766018481$ | $3477130883870490622$ |
| 153:4 | $86891334336737473645266187382699017570$ | $-39739401459186310500075741196041113586$ | $584672958754371450194151510$ | $-94367720676607603871974647$ | $4465106700525741320910586383$ | $-716366946405481326927574651$ | $753190147298215042$ |
| 153:5 | $89376854703283233922068509773304728855$ | $-59732021399636820735563205748434873012$ | $-747702359881196986488824642$ | $200101309383096846787242901$ | $-1901217429117757964535872004$ | $-76149702361286100078264942$ | $1158729918529655$ |
| 154:0 | $32926653016973724971504463591711547412$ | $28581517935457064794992031374438657873$ | $-36869964686831740889715103114$ | $12115719569886293854595075208$ | $-19668169011939808763102137113$ | $7475260545438433845469547819$ | $7919000683246416397$ |
| 154:1 | $43550208111795621488538575265169213243$ | $15728209311255236810673886089965007547$ | $-41689173506234074253983759619$ | $22355704740175419276942611050$ | $11023722288912006445881619752$ | $-417377427577283075059469762$ | $1094846399452861003$ |
| 154:2 | $71258854329925242171504497311438057674$ | $36599693875004073890732356706884174744$ | $84727797775947501725409329275$ | $-20067664788809494669329533530$ | $-23605788976883434605046401202$ | $7324955899745168638893104502$ | $4774732703665987984$ |
| 154:3 | $73187527223021745056000165272079369839$ | $15442036124962245492110245513175031727$ | $58015185934272918480946175120$ | $-23265045595168894503451238519$ | $7741883583735857558473606731$ | $369736499299104255598417434$ | $3471342002641986179$ |
| 154:4 | $86891098524315240232860281450480046755$ | $-39741191604782005379041327781932819024$ | $584218237417735624185613637$ | $-94282237523566484160113317$ | $4461661002122377075453198565$ | $-715749668768596606363968448$ | $757354563654889910$ |
| 154:5 | $89377354893277508555575544638110940763$ | $-59732211782369006272656001028410747861$ | $-747502610641875820601213166$ | $200050689547233044117169303$ | $-1900663439009628662986731077$ | $-76156479569237734790154400$ | $1158279969753741$ |
| 155:0 | $32956976009065712667388521718531313143$ | $28600220577770004263409127173431682052$ | $-36963328465846163344642568910$ | $12142702526863137503325240498$ | $-19712135476047902282602217001$ | $7486863839719779433110232302$ | $7943163149162110440$ |
| 155:1 | $43606202597109771510880051067413778197$ | $15727165484809848287484411551531306821$ | $-41827769956732408044378576637$ | $22440045991057996489995631702$ | $11020699464844597111821700894$ | $-417684489304006474431834816$ | $1107383421630148030$ |
| 155:2 | $71208651202540120505678137101873133969$ | $36617967896398358966238568466577297702$ | $84822762386032107153822533227$ | $-20094864777643914126728655144$ | $-23485163482108633282101955952$ | $7294250290591588971345502258$ | $4771470472003640769$ |
| 155:3 | $73129261233846062245141571070682319130$ | $15442956856424647073069248123252510895$ | $58141268946892921971721734734$ | $-23347909084419074464095054430$ | $7757190347743959255917446385$ | $366853027925651060316812980$ | $3465547088744549262$ |
| 155:4 | $86890862925447889742884382859448856583$ | $-39742980208222599875534735470891833468$ | $583764150230465144518695369$ | $-94196876729829914538898637$ | $4458219809147132108073111820$ | $-715133222067506296262919209$ | $761576044814118865$ |
| 155:5 | $89377854956748517725752608220902055249$ | $-59732402182015591603482847685696112131$ | $-747302950470029118670971075$ | $200000090768535788813743432$ | $-1900109818504174171645303867$ | $-76163233886802684016021533$ | $1157830199590146$ |
| 156:0 | $32987366672437253011381427848796660336$ | $28618952307586236825028842080454445309$ | $-37057307709540140897392487273$ | $12169856879699578986189517445$ | $-19756331769061507320267446746$ | $7498530650965349588763894568$ | $7967513914480245338$ |
| 156:1 | $43662409161974471030615873865177747848$ | $15726120884959873384409830453042626487$ | $-41968167575921623923448469056$ | $22525371527091972599069038711$ | $11017679243424755467097074416$ | $-417996169741680613141874444$ | $1120160781370910358$ |
| 156:2 | $71158379867031589095833629923374983547$ | $36636165071645363310580440084690347578$ | $84918311004288111586109932849$ | $-20122231573801713446490623467$ | $-23364262779698621748477611839$ | $7263478907114066172485984159$ | $4768226133277456217$ |
| 156:3 | $73070786853092575384422142621212525731$ | $15443870411868065808709466090396347025$ | $58269181349651770110338262996$ | $-23431761999045694491654158885$ | $7772381956350452474816196027$ | $363995676126775169645513522$ | $3459743426257127851$ |
| 156:4 | $86890627539829826954832681624576961107$ | $-39744767271583502500043837162121439203$ | $583310695937593273256721275$ | $-94111638053068023597662296$ | $4454783113308389584687393129$ | $-714517604758046545845997540$ | $765855738250632119$ |
| 156:5 | $89378354893748887925900748029215953149$ | $-59732592598519393351063189516560959551$ | $-747103379305291257740706512$ | $199949513033868581546377506$ | $-1899556567231371086870709337$ | $-76169965348043840622263490$ | $1157380608032697$ |
| 157:0 | $33017825437734393006027613862638546334$ | $28637713284473340619719465621163481114$ | $-37151908614857506999203390482$ | $12197184357574349044336071820$ | $-19800760185713896691042062164$ | $7510261600703859339811676263$ | $7992055293123161673$ |
| 157:1 | $43718830290914384094155140733325099367$ | $15725075500018570653841751454812709273$ | $-42110401899091504215250163459$ | $22611700483583673602831471173$ | $11014661782151013034548962813$ | $-418312581364914052781056331$ | $1133185022329852854$ |
| 157:2 | $71108039904224261908391880437442956447$ | $36654285235744189835257397295586250432$ | $85014449839461039950082437882$ | $-20149766906997387347087150180$ | $-23243085524104389589239206625$ | $7232641295622936138090736656$ | $4764999833315215306$ |
| 157:3 | $73012101583422291620090445711145502897$ | $15444776856533355811832743085286835136$ | $58398958552986538796323453967$ | $-23516623445404645026633714939$ | $7787459065833903414564995267$ | $361164398165011026788147815$ | $3453928200197862397$ |
| 157:4 | $86890392367156061702497242394607070762$ | $-39746552796936265973238172641273349182$ | $582857873287357912055061484$ | $-94026521251566924576387990$ | $4451350906334302118971091508$ | $-713902815299747536400343262$ | $770194822513115602$ |
| 157:5 | $89378854704331212822725959750501990558$ | $-59732783031823313228985728760859922355$ | $-746903897087354827336293973$ | $199898956330106643220711687$ | $-1899003684821680398360554721$ | $-76176673986970782961834635$ | $1156931195075025$ |
| 158:0 | $33048352739956762893460053843841846171$ | $28656503669563237676966215585817122472$ | $-37247137467344773115344812763$ | $12224686714249226635110230349$ | $-19845423051606065170799360516$ | $7522057318906697863500303722$ | $8016789636788614661$ |
| 158:1 | $43775468516944052049501046660363185893$ | $15724029318014191341537810615872301405$ | $-42254509442279702756958155194$ | $22699052520165339110651354143$ | $11011647242752320727624854108$ | $-418633839723360520690107956$ | $1146462919118253031$ |
| 158:2 | $71057630890587888943712187421241866873$ | $36672328222547511025457059233547984206$ | $85111185188819531059379414525$ | $-20177472531481748395348389306$ | $-23121630331899996305448171957$ | $7201736992640541471984651620$ | $4761791720328684495$ |
| 158:3 | $72953202879078443211042835115667185846$ | $15445676255552530784299628262272677922$ | $58530636948913049846817684339$ | $-23602513054396337653800684034$ | $7802422321599001247072375475$ | $358359152721763392186668737$ | $3448098525617800616$ |
| 158:4 | $86890157407122207336402462447849974317$ | $-39748336786348596447453845902746939937$ | $582405681031191585890993457$ | $-93941526084226799676087606$ | $4447923179972733656750034155$ | $-713288852155822611427940498$ | $774594508282794882$ |
| 158:5 | $89379354388548053285621911050239439315$ | $-59732973481870337908240656560739642773$ | $-746704503755970554458468413$ | $199848420644136900688961172$ | $-1898451170906046709651215391$ | $-76183359837539869653350263$ | $1156481960710567$ |
| 159:0 | $33078949018519592268946993718989136804$ | $28675323625573489411886526071780721255$ | $-37343000642768419493912531837$ | $12252365728517485075140991258$ | $-19890322723761703161515441341$ | $7533918444139526562531482397$ | $8041719335728899759$ |
| 159:1 | $43832326422901811068410403738916050086$ | $15722982326682151631210705522538045473$ | $-42400527737242141443518132337$ | $22787447839409567588789941127$ | $11008635791359792221667285630$ | $-418960063554647265828157922$ | $1160001487349691061$ |
| 159:2 | $71007152398175455332694978778373724047$ | $36690293864736925183913450304930750468$ | $85208523439776739959552985583$ | $-20205350226491662855253863933$ | $-22999895781285930558488989357$ | $7170765524761642550469668360$ | $4758601944987764061$ |
| 159:3 | $72894088144552025970794170309725917937$ | $15446568673959935273189079894368009558$ | $58664253945989260525116177092$ | $-23689451000078167351912519546$ | $7817272358065588662104741855$ | $355579902997408171434629961$ | $3442251360132380406$ |
| 159:4 | $86889922659424479191019930723402323526$ | $-39750119241884362701051449915413928590$ | $581954117923711463831366563$ | $-93856652310559991422580705$ | $4444499925991201564066075172$ | $-712675713793157444892356791$ | $779056039475589963$ |
| 159:5 | $89379853946451937415916969453131096510$ | $-59733163948603538884288590247967121260$ | $-746505199250947228696275517$ | $199797905962857972482828259$ | $-1897899025115897460105122826$ | $-76190022933654334167519944$ | $1156032904932559$ |

### 6.19 Cells 160 through 169

| $t:i$ | $M_r$ | $M_b$ | $A_{00}$ | $A_{01}$ | $A_{10}$ | $A_{11}$ | $R_\rho$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 160:0 | $33109614717316859806546685492094326858$ | $28694173316828975273979812649028574831$ | $-37439504608768445913529463568$ | $12280223204662379333358142417$ | $-19935461591194373706846232443$ | $7545845623717217592246246841$ | $8066846819549346408$ |
| 160:1 | $43889406642831254644284435175662236204$ | $15721934513456916354861150624507641878$ | $-42548495367956737402900021195$ | $22876907206257712593970703311$ | $11005627598686380007760866490$ | $-419291374902316882181512443$ | $1173807994206415413$ |
| 160:2 | $70956603994560143618757821730958736369$ | $36708181993797959387631354321065665708$ | $85306471071547942864096252370$ | $-20233401796709810323140334266$ | $-22877880411579693146465440007$ | $7139726408510362564251738908$ | $4755430660496574091$ |
| 160:3 | $72834754733199797665987561018854698276$ | $15447454176703672558126434656444076738$ | $58799848005812050823734981489$ | $-23777458019090945871382150152$ | $7832009798549162186839220468$ | $352826616816539061590576105$ | $3436383540526630248$ |
| 160:4 | $86889688123759693056746091938831197385$ | $-39751900165603605305742068240018685012$ | $581503182722709416679869249$ | $-93771899690689101053654117$ | $4441081136176818918084443777$ | $-712063398682299247407665529$ | $783580694389947524$ |
| 160:5 | $89380353378095360576085590665083388282$ | $-59733354431966072344365736339758406273$ | $-746305983512151627462139986$ | $199747412273180154568935618$ | $-1897347247083142148381780789$ | $-76196663309164379221354954$ | $1155584027734046$ |
| 161:0 | $33140350284785602031200336414061326342$ | $28713052909283963008944012268416688908$ | $-37536655926549145385783363130$ | $12308260972925940980491890111$ | $-19980842075487213403292756403$ | $7557839513862220640786805236$ | $8092174558026744054$ |
| 161:1 | $43946711863412328421108577497057868855$ | $15720885865463581307953829641816243148$ | $-42698452008740480810977172889$ | $22967451968304626225775527428$ | $11002622840214915666324828116$ | $-419627899239046989779793514$ | $1187889969557732680$ |
| 161:2 | $70905985242771133834017244973567791242$ | $36725992439994710384926293202731001799$ | $85405034656845308260685282614$ | $-20261629072734733852366536535$ | $-22755582722693288975938505861$ | $7108619150193580101441330252$ | $4752278022671546580$ |
| 161:3 | $72775199945812648966044008349294122351$ | $15448332828657302359802511417572283037$ | $58937458681127427844337670575$ | $-23866555430941702255705426505$ | $7846635255132416667596607392$ | $350099266738623004110727699$ | $3430491801233434870$ |
| 161:4 | $86889453799825263656625194721779671675$ | $-39753679559562545766976015608590462266$ | $581052874189142111346465355$ | $-93687267985345093899723581$ | $4437666802336237000016703890$ | $-711451905297446010214993440$ | $788169786902574375$ |
| 161:5 | $89380852683530785418924123584374649528$ | $-59733544931901179035024799232583685477$ | $-746106856479508441348314249$ | $199696939562025406126737104$ | $-1896795836440171557389238066$ | $-76203280997867270980593008$ | $1155135329107877$ |
| 162:0 | $33171156173971407248042924077775821630$ | $28731962570544579216722921137676769238$ | $-37634461252608093409056639732$ | $12336480889988355494904655059$ | $-20026466631385487520488222913$ | $7569900779866448441454607765$ | $8117705061948283471$ |
| 162:1 | $44004244825444253874250485323337488437$ | $15719836369509140627581936788549544589$ | $-42850438464064738004013952982$ | $23059104076984714493803671514$ | $10999621696394972865076161283$ | $-419969765595428326850712985$ | $1202255217663972441$ |
| 162:2 | $70855295701228215301570804242052566584$ | $36743725032344114440793222067710663054$ | $85504220863610827383489077057$ | $-20290033911561455461730840421$ | $-22633001174597303472928995735$ | $7077443245750680143733997377$ | $4749144190021594637$ |
| 162:3 | $72715421029132150373597602829963748102$ | $15449204694631822237172918427373195621$ | $59077126655639021271762082859$ | $-23956765159187814989202976145$ | $7861149328527381282767634811$ | $347397830174343609938479249$ | $3424572748859716223$ |
| 162:4 | $86889219687319203127800077197563838791$ | $-39755457425813595637488594079877004328$ | $580603191087121141782328664$ | $-93602756955865411728263674$ | $4434256916295587989236681768$ | $-710841232116435786792853696$ | $792824667714420514$ |
| 162:5 | $89381351862810641916691088141353189106$ | $-59733735448352184129911156690148577783$ | $-745907818093000199604470544$ | $199646487816327335348862513$ | $-1896244792819856980712754253$ | $-76209876033507433070782453$ | $1154686809046707$ |
| 163:0 | $33202032842595121437000129359852163259$ | $28750902469891689118590296178143052626$ | $-37732927340504376027636180933$ | $12364884839458205104469983756$ | $-20072337747402339751888259089$ | $7582030096256774267413791526$ | $8144688527898684011$ |
| 163:1 | $44062008325382593170033639694257873682$ | $15718786012073424969012944672435891276$ | $-43004496710158845582494343727$ | $23151886109707015540640999229$ | $10996624352849040465095508173$ | $-420317106694599096880828823$ | $1216911829501908156$ |
| 163:2 | $70804534923675183398001641128983968624$ | $36761379598589836912336454968784766797$ | $85604036456788427899410575649$ | $-20318618197072940399777622648$ | $-22510134186771228718521742106$ | $7046198180599571563403306388$ | $4746029323830432422$ |
| 163:3 | $72655415174312962759784412651582639643$ | $15450069839387947260126826385074224930$ | $59218893785604934981059855171$ | $-24048109753570186500962110945$ | $7875552607927665525486617281$ | $344722289507929026288376416$ | $3418622855422520309$ |
| 163:4 | $86888985785940119507673417629613135119$ | $-39757233766405365604096757680641600167$ | $580154132183903196324363222$ | $-93518366364192092022415828$ | $4430851469900427857770542995$ | $-710231377620736011948140135$ | $797546725649392614$ |
| 163:5 | $89381850915987327390211981997195599159$ | $-59733925981262497097773824325610474486$ | $-745708868292667195736199838$ | $199596057023031185263852835$ | $-1895694115855549450517403303$ | $-76216448449776540397466869$ | $1154238467542997$ |
| 164:0 | $33232980753120793639597777849378431377$ | $28769872778304194682766092930591415115$ | $-37832061042667111684319627627$ | $12393474732373869121893028238$ | $-20118457946438087477540709328$ | $7594228146964237526549489409$ | $8174057901840947343$ |
| 164:1 | $44120005216932890439272790902365866005$ | $15717734779299695448529938912164099786$ | $-43160669938497614880898173912$ | $23245821292989949553085215922$ | $10993631000588524061433183677$ | $-420670059093051919740645690$ | $1231868195750027598$ |
| 164:2 | $70753702459111993790891109237873866094$ | $36778955965175772102631545156973287512$ | $85704488300136326385243677203$ | $-20347383840542702312798273825$ | $-22386980137639694083347011565$ | $7014883429478876327623674872$ | $4742933588241122222$ |
| 164:3 | $72595179515328676220709511398901948802$ | $15450928327648703308474303095548674416$ | $59362803143318573503233970762$ | $-24140612413146108648466564379$ | $7889845670850302600727674164$ | $342072632225779233725552336$ | $3412638451195929089$ |
| 164:4 | $86888752095387215224762151506498037376$ | $-39759008583382674547840196521284890897$ | $579705696249880261294151306$ | $-93434095972869894164326991$ | $4427450455015679464346004772$ | $-709622340295432858235369370$ | $802337389008419790$ |
| 164:5 | $89382349843113206537948672023692888736$ | $-59734116530575611570710732379091374489$ | $-745510007018607413224181621$ | $199545647169093819581242605$ | $-1895143805181078966921367646$ | $-76222998280313612775909914$ | $1153790304589016$ |
| 165:0 | $33264000372824889106096958617137228710$ | $28788873668482760502043617784926738817$ | $-37931869312245354708619022086$ | $12422252507716382818097257016$ | $-20164829786413424247476687099$ | $7606495625497056542474120811$ | $8203666342999107520$ |
| 165:1 | $44178238412703455208078450917231396211$ | $15716682656984877505122887771079521305$ | $-43319002601274311046187360074$ | $23340933526649533802552421729$ | $10990641836240127456332248531$ | $-421028763327949552678471467$ | $1247133020474757148$ |
| 165:2 | $70702797851725645924464729747404838698$ | $36796453957219143700700532546819871844$ | $85805583358080708021427222201$ | $-20376332781148850549569789189$ | $-22263537363994245257865194773$ | $6983498456286192635093164260$ | $4739857150342927893$ |
| 165:3 | $72534711127318511463815269383051233559$ | $15451780224112350160076877542249212410$ | $59508899062575006949388241481$ | $-24234297010475612415067128068$ | $7904029082966644458873138097$ | $339448851051727592367182644$ | $3406615717143013685$ |
| 165:4 | $86888518615360285594227829910226137480$ | $-39760781878786558577559971226340286664$ | $579257882058569860696921127$ | $-93349945545044432493913505$ | $4424053863525575847189454234$ | $-709014118629220629552465059$ | $807198126981643503$ |
| 165:5 | $89382848644240611465033426377716769115$ | $-59734307096235105212647839189703015764$ | $-745311234210976451363789100$ | $199495258241483708558946088$ | $-1894593860430753728836683820$ | $-76229525558705108370799108$ | $1153342320176839$ |
| 166:0 | $33295092173866799235372486398929853156$ | $28807905314873977068439996444673588042$ | $-38032359205000502300420517328$ | $12451220132934065287332739930$ | $-20211455860916902402024536180$ | $7618833235117550680340326593$ | $8233516939467315433$ |
| 166:1 | $44236710885919992374205002630425138560$ | $15715629630569417966935575321353857092$ | $-43479540458967038068531020985$ | $23437247409098223972756359479$ | $10987657062283201143766401288$ | $-421393364071306779449958402$ | $1262715335561670774$ |
| 166:2 | $70651820640819766761723670058621585141$ | $36813873398483195867009145168925532728$ | $85907328697611855940665247623$ | $-20405466986499890242927653211$ | $-22139804160400304317327224443$ | $6952042713912331123988238023$ | $4736800180260556938$ |
| 166:3 | $72474007024872179288420898038560494476$ | $15452625593465651394244073273632048734$ | $59657227186230805099615601427$ | $-24329188116918462774779763738$ | $7918103397921727056393333971$ | $336850944089292701980877996$ | $3400550676905127511$ |
| 166:4 | $86888285345559717318065767087391679615$ | $-39762553654654280037007450136683539901$ | $578810688386605331866872568$ | $-93265914844460316213885973$ | $4420661687333603714763508457$ | $-708406711114391191762082483$ | $812130451121663233$ |
| 166:5 | $89383347319421841712267642875950146370$ | $-59734497678184639588051606856614409310$ | $-745112549809987451224894910$ | $199444890227180914892904120$ | $-1894044281239359366274208666$ | $-76236030318485016946366116$ | $1152894514298351$ |
| 167:0 | $33326256633360678128194960596966229105$ | $28826967893694971349232536179115677526$ | $-38133537881242362096853950018$ | $12480379604479236501280226369$ | $-20258338799867080349058344938$ | $7631241689023077157398442398$ | $8263612832282077383$ |
| 167:1 | $44295425672204930478786769502957672604$ | $15714575685126747686756796766110339802$ | $-43642330630113284232105188901$ | $23534788263815151598866064454$ | $10984676887298683069792035641$ | $-421764010291418627974194932$ | $1278624515938875916$ |
| 167:2 | $70600770360742865002707702631927160828$ | $36831214111349464767772097914169754990$ | $86009731490223887892428556724$ | $-20434788453172595549927977257$ | $-22015778778588931806478753258$ | $6920515644071420095823098678$ | $4733762851245876570$ |
| 167:3 | $72413064160250046363642282230282742194$ | $15453464500397509054818809770241040769$ | $59807834515972094493078129252$ | $-24425311029102568346161266467$ | $7932069157141486197890643676$ | $334278914971299416270173237$ | $3394439188318760866$ |
| 167:4 | $86888052285686486989935897879545730742$ | $-39764323913019336485575925111582475771$ | $578364114013726136905941404$ | $-93182003635459296112011389$ | $4417273918362447133641297199$ | $-707800116246823440188171714$ | $817135916880939761$ |
| 167:5 | $89383845868709164285085329267643942695$ | $-59734688276367960030874365676174293545$ | $-744913953755911021731642935$ | $199394543113177079628948516$ | $-1893495067242158174109583199$ | $-76242512593134952927359953$ | $1152446886945243$ |
| 168:0 | $33357494233448636387610391737518969788$ | $28846061582958474836187173752236048242$ | $-38235412607810073896463357976$ | $12509732948357353840983977860$ | $-20305481270189731033568982672$ | $7643721710531091172442585543$ | $8293957216564917334$ |
| 168:1 | $44354385871424456727791911859363176492$ | $15713520805352331130281817881693359387$ | $-43807421643414698406345247633$ | $23633582167052396487740008115$ | $10981701526230297938144416287$ | $-422140855421939492730738015$ | $1294870295643185746$ |
| 168:2 | $70549646540815225185043115819873229901$ | $36848475916789620097103915515886219641$ | $86112799013899294365561458168$ | $-20464299207262286521968287687$ | $-21891459426832999763812719554$ | $6888916677126772392492988713$ | $4730745339772192369$ |
| 168:3 | $72351879421535598802919084313554437328$ | $15454297009612981994653555267455813310$ | $59960769464412908314065184268$ | $-24522691796628444504535826089$ | $7945926889627163258458415381$ | $331732773017272280756774511$ | $3388276934427927510$ |
| 168:4 | $86887819435442159604618338053713725731$ | $-39766092655911469652746906875835175892$ | $577918157722768209763820549$ | $-93098211682978418071728490$ | $4413890548553931412717475145$ | $-707194332525972803838174165$ | $822216125216639305$ |
| 168:5 | $89384344292154813682481390895586130795$ | $-59734878890728895513732095031759681149$ | $-744715445989075165861952398$ | $199344216886475408096841076$ | $-1892946218074888347306979308$ | $-76248972416084248271308416$ | $1151999438109019$ |
| 169:0 | $33388805461375323638823365395979563730$ | $28865186562498359515610160145866537739$ | $-38337990760099116909993533607$ | $12539282220688908848887883830$ | $-20352885976510520578397605508$ | $7656274033268441399926085974$ | $8324553342694772098$ |
| 169:1 | $44413594649606433941963394494812674741$ | $15712464975552283257061185057912071908$ | $-43974863492302016494142893318$ | $23733655976846083590446926072$ | $10978731200658725388033686155$ | $-422524057539043942873824282$ | $1311462784783383440$ |
| 169:2 | $70498448705254410233763121390395362542$ | $36865658634336865853390045041039646651$ | $86216538655139510101334828274$ | $-20494001304945850527749973748$ | $-21766844269307372112050988353$ | $6857245231912403139151011928$ | $4727747825631181551$ |
| 169:3 | $72290449630717028310434892674800738143$ | $15455123185847707863737538167835410735$ | $60116081909653747770691877671$ | $-24621357251078519225570529384$ | $7959677111736195977628381113$ | $329212533399030881631006229$ | $3382059413957612377$ |
| 169:4 | $86887586794528887072076712610212305073$ | $-39767859885356674366342727711100235928$ | $577472818299654338807791090$ | $-93014538752548183342371257$ | $4410511569868967182959676843$ | $-706589358454860786201940222$ | $827372724266395159$ |
| 169:5 | $89384842589810991925904781128137685899$ | $-59735069521211358517314149499864676003$ | $-744517026449865206966520908$ | $199293911534090655866444294$ | $-1892397733373763217597422507$ | $-76255409820710045152501912$ | $1151552167780989$ |

### 6.20 Cells 170 through 179

| $t:i$ | $M_r$ | $M_b$ | $A_{00}$ | $A_{01}$ | $A_{10}$ | $A_{11}$ | $R_\rho$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 170:0 | $33420190809563932106302773709352794919$ | $28884343013995652491359849722932887821$ | $-38441279824135673063906999808$ | $12569029508284435773136836827$ | $-20400555661863578963635138714$ | $7668899401365016428297144323$ | $8355404517511945036$ |
| 170:1 | $44473055240932552090752013473524091448$ | $15711408179631532922344637733861866266$ | $-44144707692098482948074081917$ | $23835037363405549053109329873$ | $10975766139089494736163184687$ | $-422913779547128138295920509$ | $1328412487458884702$ |
| 170:2 | $70447176373099340161626115024766598867$ | $36882762082056889354877239318806675578$ | $86320957911042790081001795166$ | $-20523896833057859979941260606$ | $-21641931425432675903422752670$ | $6825500715550084018899268540$ | $4724770492032576379$ |
| 170:3 | $72228771541694588198473352938382300466$ | $15455943093882749811727046110329684355$ | $60273823252438699263227313039$ | $-24721335036404526190117966855$ | $7973320326948842101190270827$ | $326718217314944747301047691$ | $3375781931211160316$ |
| 170:4 | $86887354362649406736112388834685001868$ | $-39769625603377207454676707872060031418$ | $577028094533384584731645995$ | $-92930984610290715540393708$ | $4407136974287494671907814485$ | $-705985192540064542479144890$ | $832607411098669847$ |
| 170:5 | $89385340761729868588116569838103400422$ | $-59735260167759344900024460019979178345$ | $-744318695078723715207093655$ | $199243627043049114725980991$ | $-1891849612775470491608491904$ | $-76261824840337388458132746$ | $1151105075952277$ |
| 171:0 | $33451650775693654478703258215573260077$ | $28903531121005040286453364723036937505$ | $-38545287398699657456162695820$ | $12598976929232994697852146099$ | $-20448493108416397963964335912$ | $7681598569651861382921497597$ | $8386514105549376104$ |
| 171:1 | $44532770949808256087461865210179569274$ | $15710350401081510843378458783499432347$ | $-44317007339929162318066853145$ | $23937754840958605289515414014$ | $10972806577255414926203605706$ | $-423310189373541014733910258$ | $1345730320696437532$ |
| 171:2 | $70395829058132913727838662665682263154$ | $36899786076518347189082094513382140638$ | $86426064391430701640268420478$ | $-20553987909680149336051158582$ | $-21516718969202233507314410967$ | $6793682523261816071655781778$ | $4721813525706696956$ |
| 171:3 | $72166841838210177553525520551035365456$ | $15456756798559890157095281809169929191$ | $60434046476058501697066677950$ | $-24822653640771014799729855050$ | $7986857025619732646267941687$ | $324249852173335696238603652$ | $3369439585351608792$ |
| 171:4 | $86887122139507039897592822206452094298$ | $-39771389811991596622691772408278624988$ | $576583985216026733653715661$ | $-92847549022917934353126569$ | $4403766753808428172132286578$ | $-705381833291706493087664091$ | $837921933541620994$ |
| 171:5 | $89385838807963580822012985097362531297$ | $-59735450830316933767853741057043029795$ | $-744120451816150434113766503$ | $199193363400388598682340186$ | $-1891301855917171490442206606$ | $-76268217508239318097021789$ | $1150658162613814$ |
| 172:0 | $33483185862778630213629547485523708376$ | $28922751068981874151716978128188458710$ | $-38650021197497769111333897077$ | $12629126633504503682191773223$ | $-20496701138211505396800918191$ | $7694372303863887766952230704$ | $8417885530302898462$ |
| 172:1 | $44592745153014192948090850656170506427$ | $15709291622967338910664299285127174181$ | $-44491817177533262472396079382$ | $24041837801136077434132205224$ | $10969852758434403170991860813$ | $-423713460172866911518921996$ | $1363427634472194190$ |
| 172:2 | $70344406268803138941216393644300123013$ | $36916730432762876490868468973971945780$ | $86531865821024586405601220707$ | $-20584276684745225971248005929$ | $-21391204928491711945302134758$ | $6761790038177599203857682353$ | $4718877117009936480$ |
| 172:3 | $72104657131695410404183992206489868363$ | $15457564364797394535015960286226145283$ | $60596806209156684979510666965$ | $-24925342429938149269490494855$ | $8000287684713496673554192596$ | $321807471785548050134428533$ | $3363027259023841227$ |
| 172:4 | $86886890124805690342237294277708356555$ | $-39773152513214649302178037082573528250$ | $576140489142706785254726795$ | $-92764231757729735916733168$ | $4400400900449600702865814263$ | $-704779279223443973306056354$ | $843318092094609278$ |
| 172:5 | $89386336728564233389413483149584425954$ | $-59735641508828287344482235763705608588$ | $-743922296602702207261091234$ | $199143120593158429983386605$ | $-1890754462436500390697915687$ | $-76274587857636961121363365$ | $1150211427756345$ |
| 173:0 | $33514796579248415385304338905587486471$ | $28942003045309688022396395967768775934$ | $-38755489051387958763921448002$ | $12659480803566306384275260978$ | $-20545182613925379069012893503$ | $7707221380847303484039664557$ | $8449522275530626493$ |
| 173:1 | $44652981301943136175714589165142171227$ | $15708231827914496277315190430268256223$ | $-44669193657147051465859102713$ | $24147316547984313545232442489$ | $10966904933783634839029973641$ | $-424123770541316294224305384$ | $1381516232891583101$ |
| 173:2 | $70292907508142737342347540027708649193$ | $36933594964274619634611439651010395540$ | $86638370041673389324059900675$ | $-20614765340653901572262847925$ | $-21265387284351031194914797952$ | $6729822631138372652516952443$ | $4715961460033306072$ |
| 173:3 | $72042213959034211984970998672502308035$ | $15458365857606271380346719528595803606$ | $60762158791606361077122263324$ | $-25029431682272498977938060960$ | $8013612767523540335100965101$ | $319391116569242122840352108$ | $3356539606271038176$ |
| 173:4 | $86886658318249842872943392299647001407$ | $-39774913709057461476159515787520258800$ | $575697605111599475806944549$ | $-92681032582612179840167845$ | $4397039406247708864027251780$ | $-704177528852458918903973210$ | $848797741926737990$ |
| 173:5 | $89386834523583898689813901616996967933$ | $-59735832203237650841612532225281876673$ | $-743724229378992905062751730$ | $199092898608419425162231334$ | $-1890207431971563466937016808$ | $-76280935921699623661918047$ | $1149764871370426$ |
| 174:0 | $33546483439030012159915227585626073926$ | $28961287239328241086114525577628377857$ | $-38861698910656755577551900951$ | $12690041655014374140852786464$ | $-20593940439645078666678344474$ | $7720146588771894080450083319$ | $8481427886587978534$ |
| 174:1 | $44713482924926574335008789570573841092$ | $15707170998094936221525394449364379085$ | $-44849195010636206400704281406$ | $24254222334700321359461410446$ | $10963963362691000792644427086$ | $-424541304741818879921604781$ | $1400008396604935767$ |
| 174:2 | $70241332273687186017178668108432303409$ | $36950379482949250106396906518116139839$ | $86745585014634297232190563270$ | $-20645456092907543194471361057$ | $-21139263970278058378301518889$ | $6697779660493996560954571251$ | $4713066752714150478$ |
| 174:3 | $71979508780235755087973299416666475657$ | $15459161342107053037108942143236286548$ | $60930162343636505387756400582$ | $-25134952625480472687476771345$ | $8026832723372999261331300662$ | $317000833762504063740747956$ | $3349971039695204339$ |
| 174:4 | $86886426719544561846637650694071320027$ | $-39776673401527426477539737264507211406$ | $575255331923918835946762416$ | $-92597951266035682847075482$ | $4393682263258257881859328497$ | $-703576580699447587614996633$ | $854362794967082254$ |
| 174:5 | $89387332193074616789104750791060267201$ | $-59736022913489352329531984943181385732$ | $-743526250085693351684580407$ | $199042697433243881103421236$ | $-1889660764160938335586336503$ | $-76287261733544882677081980$ | $1149318493446427$ |
| 175:0 | $33578246961631494996938774873160861969$ | $28980603842362097258404914183301335225$ | $-38968658847350941549316279074$ | $12720811437219554428080093208$ | $-20642977561663089232121287494$ | $7733148727348290466838153030$ | $8513605971798311000$ |
| 175:1 | $44774253629655395323057005055577583783$ | $15706109115212626241328951077848477457$ | $-45031881322068553339000686633$ | $24362587402190591295826815311$ | $10961028313144927030733254622$ | $-424966252940454035715650595$ | $1418916906542826758$ |
| 175:2 | $70189680057391160280493813336211760979$ | $36967083799062486992337051976239730216$ | $86853518822907676246120186150$ | $-20676351190755356076900616058$ | $-21012832871473599303960979306$ | $6665660471896140588445343284$ | $4710193196951150320$ |
| 175:3 | $71916537976013304953072140608337847948$ | $15459950883547126318645499098497908241$ | $61100876838398686900048926932$ | $-25241937475165456147342989592$ | $8039947987296814656686761176$ | $314636677649405709769448282$ | $3343315716807521221$ |
| 175:4 | $86886195328395489715633844454298991906$ | $-39778431592628243762095696015763609085$ | $574813668383908783043615099$ | $-92514987577053219007705233$ | $4390329463555506845405871995$ | $-702976433288610316307073397$ | $860015222091552994$ |
| 175:5 | $89387829737088395448254697751023865193$ | $-59736213639527802607904276782704725614$ | $-743328358663531252075684713$ | $198992517054715561131004798$ | $-1889114458643673200277013022$ | $-76293565326238677516260208$ | $1148872293974529$ |
| 176:0 | $33610087672227271721242890218383595998$ | $28999953047749754205638930589515073798$ | $-39076377057665110921479280445$ | $12751792433989291061906763626$ | $-20692296969290885837651818511$ | $7746228608050362757717696907$ | $8546060203860275840$ |
| 176:1 | $44835297105699359012719810271401623782$ | $15705046160488482199677257955426948946$ | $-45217314603931217216509647998$ | $24472445019561568259903931880$ | $10958100062123685563493869458$ | $-425398811454897044556375214$ | $1438255069061609250$ |
| 176:2 | $70137950345543338920833957535474616853$ | $36983707721238085178432746345852247039$ | $86962179673627845823033271530$ | $-20707452917857123741239277361$ | $-20886091824077182816525209270$ | $6633464398085941085885924687$ | $4707340998722731175$ |
| 176:3 | $71853297845264279977889741271789338582$ | $15460734547318641980756968109570831475$ | $61274364178178265510065156962$ | $-25350419475316615445982444863$ | $8052958979703809350437329397$ | $312298709797691836126890013$ | $3336567525509885642$ |
| 176:4 | $86885964144508845573482494208978527434$ | $-39780188284359927655909201060253817292$ | $574372613298833748018796477$ | $-92432141285298526533045391$ | $4386980999232414133057635194$ | $-702377085147641313706384284$ | $865757055411647941$ |
| 176:5 | $89388327155677210151959297948712204083$ | $-59736404381297495076789657678460277353$ | $-743130555053291119117454071$ | $198942357459929681118432239$ | $-1888568515059286098615730504$ | $-76299846732795401297970420$ | $1148426272944727$ |
| 177:0 | $33642006101745018691473559056630421562$ | $29019335050873334909899695149624605837$ | $-39184861864386702298994384697$ | $12782986964245255428244903670$ | $-20741901695691745619357971787$ | $7759387054342884406002062395$ | $8578794321293053111$ |
| 177:1 | $44896617127130330036731070161372481157$ | $15703982114644665583176531281147190078$ | $-45405558877210281840879642833$ | $24583829526657176909986102861$ | $10955178896005405431969789734$ | $-425839183015606993381108758$ | $1458036742596724973$ |
| 177:2 | $70086142618679532817282250248133417997$ | $37000251056415288005589153051919115866$ | $87071575900511277715510406810$ | $-20738763592961844830792356446$ | $-20759038614383116807956521640$ | $6601190758676283818049873430$ | $4704510368209004500$ |
| 177:3 | $71789784602446556437141516595977466180$ | $15461512398977034321812050695460936101$ | $61450688274468156003076724807$ | $-25460432940844770592600496694$ | $8065866106017560015584537642$ | $309986999309319369220937394$ | $3329720068644207342$ |
| 177:4 | $86885733167591423705295211998622821857$ | $-39781943478718816077324326610576159436$ | $573932165478969336468467884$ | $-92349412160984321103519407$ | $4383636862400583028399405410$ | $-701778534807718488531150633$ | $871590390670670707$ |
| 177:5 | $89388824448893004137255028792489599262$ | $-59736595138743005607893397455260820612$ | $-742932839195814200890218100$ | $198892218635992895620247736$ | $-1888022933047764150385161104$ | $-76306105986177992103102377$ | $1147980430346831$ |
| 178:0 | $33674002786954330406410630970742835970$ | $29038750049188855136647864579157522687$ | $-39294121719400143425828023007$ | $12814397382717342484023102894$ | $-20791794818733350501349101276$ | $7772624901914615517535290710$ | $8611812129920651868$ |
| 178:1 | $44958217555254540900957632531733725662$ | $15702916957888211060622531409322338373$ | $-45596680255566252491764345809$ | $24696776378766833935322766976$ | $10952265111000079211358672767$ | $-426287577040532941919787976$ | $1478276365929091609$ |
| 178:2 | $70034256351494096621949488729744464252$ | $37016713609815728759978347882205688657$ | $87181715966363860289897059642$ | $-20770285570602720594478620557$ | $-20631670978036277529021047093$ | $6568838859928564493319555044$ | $4701701519917370446$ |
| 178:3 | $71725994374845746981265065408362201405$ | $15462284504260183998067959266414552684$ | $61629915132138450648687172886$ | $-25572013302288772698008300471$ | $8078669756294775294807895770$ | $307701623084624040945990719$ | $3322766647540814657$ |
| 178:4 | $86885502397350592142527585799010651357$ | $-39783697177697579233519310831382773881$ | $573492323737593023945841245$ | $-92266799974900515704715435$ | $4380297045190207524594609684$ | $-701180780803493312892541859$ | $877517389753351114$ |
| 178:5 | $89389321616787688422098679658201830733$ | $-59736785911808992416041991184222423437$ | $-742735211031998408057327534$ | $198842100570023284025531785$ | $-1887477712249562807170479535$ | $-76312343119298023983757254$ | $1147534766170466$ |
| 179:0 | $33706078270557125043955032501802541152$ | $29058198242257080544302897583659210837$ | $-39404165206251802784630655668$ | $12846026080654500262170804894$ | $-20841979461860741746553948829$ | $7785942998916959113313765670$ | $8645117504396515653$ |
| 179:1 | $45020102341459474895068711663278299295$ | $15701850669893949517985349810231370008$ | $-45790747033855016296904305700$ | $24811322193636048753262610661$ | $10949359013604953786249180331$ | $-426744209924170010549185437$ | $1498988988178284787$ |
| 179:2 | $69982291012749582048608947003915744584$ | $37033095184909767003513722278287235453$ | $87292608465648922886554696623$ | $-20802021241808961911144472400$ | $-20503986599207075987030668550$ | $6536407994523774466980576496$ | $4698914672811917807$ |
| 179:3 | $71661923199727863404834644588286074511$ | $15463050929108259148988375528652229132$ | $61812112937951595019406090774$ | $-25685197152824485983493976274$ | $8091370304819796075582366003$ | $305442666100944955680927266$ | $3315700244491611479$ |
| 179:4 | $86885271833494291222204369479891815661$ | $-39785449383285228291780892571758035656$ | $573053086890974885258217169$ | $-92184304498412446942753490$ | $4376961539750018316547148886$ | $-700583821673080720820505283$ | $883540283315177223$ |
| 179:5 | $89389818659413141833912152649976112212$ | $-59736976700440195930886656552914967381$ | $-742537670502798241366429721$ | $198792003249150336733051751$ | $-1886932852305605103408822278$ | $-76318558165015797788089968$ | $1147089280405072$ |

### 6.21 Cells 180 through 189

| $t:i$ | $M_r$ | $M_b$ | $A_{00}$ | $A_{01}$ | $A_{10}$ | $A_{11}$ | $R_\rho$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 180:0 | $33738233101279848618567094788798556113$ | $29077679831774987565575528163798911369$ | $-39515001042777498435050347621$ | $12877875486552877169254121497$ | $-20892458794990205941230835842$ | $7799342206208349172434131226$ | $8678714389769713736$ |
| 180:1 | $45082275530181300076207801807144105185$ | $15700783229786689594086850143163448224$ | $-45987829781261717178314842959$ | $24927504800921078227007544187$ | $10946460921084795299345345154$ | $-427209305341856450301492093$ | $1520190300645404416$ |
| 180:2 | $69930246065184590116368935671735516827$ | $37049395583382245361308373578155924525$ | $87404262127117771145781807361$ | $-20833973034834900303395668943$ | $-20375983109745026697901478304$ | $6503897441327753906901121981$ | $4696150050446761798$ |
| 180:3 | $71597567021371432368366108044169875825$ | $15463811739684272076854432046722778078$ | $61997352153690533268277401499$ | $-25800022297717840043248868718$ | $8103968109673732995889742494$ | $303210221706596978217529531$ | $3308513504067392132$ |
| 180:4 | $86885041475731032150570813213423657181$ | $-39787200097467124025568721335915172410$ | $572614453758368357635249930$ | $-92101925503459107812025221$ | $4373630338247228980083693008$ | $-699987655958049041772993908$ | $889661373538154063$ |
| 180:5 | $89390315576821211038092728329083987013$ | $-59737167504581438668833663784812465389$ | $-742340217549224719267711128$ | $198741926660514941348078800$ | $-1886388352857280908858571502$ | $-76324751156140431801576534$ | $1146643973039902$ |
| 181:0 | $33770467833967521673751542245407247967$ | $29097195021607842593998764387575612014$ | $-39626638083794372882059018516$ | $12909948066901787507689177475$ | $-20943236035424691184692774878$ | $7812823397604534544366756107$ | $8712606803094045968$ |
| 181:1 | $45144741261999151754624493813662584004$ | $15699714616122618434267869800961524535$ | $-46188001439334122389118405784$ | $25045363294239224656161932094$ | $10943571161978627658922606470$ | $-427683094570267032416661906$ | $1541896670638522708$ |
| 181:2 | $69878120965419778466096585893176931255$ | $37065614605097651982167933373168272075$ | $87516685816504542594473852987$ | $-20866143415906903531621124238$ | $-20247658088310324849625101137$ | $6471306465150449443026536405$ | $4693407881103466062$ |
| 181:3 | $71532921687972766604190820049273234002$ | $15464567002395391029037456178487658766$ | $62185705614186399332931239397$ | $-25916527806373541438252703603$ | $8116463512276646731235039305$ | $301004391931145137126519835$ | $3301198713191898646$ |
| 181:4 | $86884811323769895571154037346223508441$ | $-39788949322224985435457122760001670371$ | $572176423162001037625499402$ | $-92019662762551386888171608$ | $4370303432867482337403151796$ | $-699392282203409968987718690$ | $895883037020137944$ |
| 181:5 | $89390812369063710566488850524632020002$ | $-59737358324177625105201039696969820429$ | $-742142852112345305648879788$ | $198691870791269368900829485$ | $-1885844213546446182485351524$ | $-76330922125429952205127355$ | $1146198844064029$ |
| 182:0 | $33802783029679673698078794898383636677$ | $29116744017821914426101338016275402636$ | $-39739085323859003357181399412$ | $12942246326948012410101600184$ | $-20994314448791372142630553132$ | $7826387460134928272972613057$ | $8746798835081437682$ |
| 182:1 | $45207503776862953393720648179821088396$ | $15698644806869879905189107239809119757$ | $-46391337425222788245684791160$ | $25164938085977318899831557098$ | $10940690076634662622740641906$ | $-428165816825127664698830572$ | $1564125177424538465$ |
| 182:2 | $69825915163861978595017522566617569161$ | $37081752048064673473932068786818016852$ | $87629888539287252375347383449$ | $-20898534889988613112809515190$ | $-20119009059482818001049377148$ | $6438634316499007856571122570$ | $4690688397932701249$ |
| 182:3 | $71467982948417701654013324093963751725$ | $15465316783915049102613100398796751499$ | $62377248630553061122886429968$ | $-26034754067141986308968659172$ | $8128856836901057934463025827$ | $298825287813004819850041348$ | $3293747779877736248$ |
| 182:4 | $86884581377320530137218420423590463386$ | $-39790697059536898345041150489300510969$ | $571738993927065511579014436$ | $-91937516048770313919293436$ | $4366980815814797008043498702$ | $-698797698957608562536199382$ | $902207727805360972$ |
| 182:5 | $89391309036192422845841484235642389463$ | $-59737549159173741546601188535818632528$ | $-741945574133283837686661121$ | $198641835628577260086490344$ | $-1885300434015422227761633343$ | $-76337071105591383350466310$ | $1145753893466342$ |
| 183:0 | $33835179255788211767808037799095138938$ | $29136327028717835340555217128932863754$ | $-39852351900093679796852922388$ | $12974772811478970767561338066$ | $-21045697350002003262446393923$ | $7840035294305197535159239670$ | $8781294651801051756$ |
| 183:1 | $45270567417461886817178636535653300290$ | $15697573779388285858705123049152638285$ | $-46597915740457778816963139243$ | $25286270965032788656416625086$ | $10937818017775268116472666897$ | $-428657719617251499155090900$ | $1586893650463203558$ |
| 183:2 | $69773628104606376539949839003698038919$ | $37097807708400122687322394994179524611$ | $87743879443516961897156037820$ | $-20931150001565038501219997551$ | $-19990033492847737753806180031$ | $6405880231324531692680338981$ | $4687991839100298751$ |
| 183:3 | $71402746448912687205982970383890111229$ | $15466061151205894943388335429156435285$ | $62572059098958270909447349022$ | $-26154742845058773860448601932$ | $8141148390154945013095281142$ | $296673029745466904837604515$ | $3286152210521079587$ |
| 183:4 | $86884351636093151088599039406067609802$ | $-39792443311377323971893505591281393813$ | $571302164881710219574372914$ | $-91855485135765311788518275$ | $4363662479311514144619571927$ | $-698203904772513286940532253$ | $908637980564260501$ |
| 183:5 | $89391805578259098226191100530119017892$ | $-59737740009514856003548973279235848731$ | $-741748383553220453814581106$ | $198591821159613611526783972$ | $-1884757013906994949376850529$ | $-76343198129280837853194390$ | $1145309121235546$ |
| 184:0 | $33867657086077271278065179658116700137$ | $29155944264864626640935123184018850976$ | $-39966447095082848112118705304$ | $13007530105625312793414109293$ | $-21097388104236720874245368565$ | $7853767814366275273008380907$ | $8816098496425597642$ |
| 184:1 | $45333936632741074460549850999877842868$ | $15696501510408113181359538095023881830$ | $-46807817085616013264074644844$ | $25409405157674560145189293349$ | $10934955351093961041712423552$ | $-429159059128078482642351883$ | $1610220710092147937$ |
| 184:2 | $69721259225336709180356894634694802029$ | $37113781380292225279350444373069359768$ | $87858667822717068489608622292$ | $-20963991335446060726276494028$ | $-19860728802057535364254222085$ | $6373043430762316792867510512$ | $4685318447937864674$ |
| 184:3 | $71337207729467670254823272025740493281$ | $15466800171543632760020882008255375603$ | $62770217615285497073983803763$ | $-26276537342704068796236627080$ | $8153338460432248285764446715$ | $294547747842328674999559328$ | $3278403085643128580$ |
| 184:4 | $86884122099798538832897267148809091973$ | $-39794188079717107473658556487447343393$ | $570865934857030352649280874$ | $-91773569797752454821175885$ | $4360348415598244352588904387$ | $-697610898203406083213933835$ | $915176413931265637$ |
| 184:5 | $89392301995315455009250342242964104552$ | $-59737930875146118063294802138603198264$ | $-741551280313391521806811241$ | $198541827371564762053035128$ | $-1884213952864414111354937451$ | $-76349303229103606503955579$ | $1144864527360165$ |
| 185:0 | $33900217100845098029428424483083364626$ | $29175595939134404949003044991468094150$ | $-40081380339841784166049322886$ | $13040520835683507618865012572$ | $-21149390127951977145143030994$ | $7867585948589980698820235687$ | $8851214691026372087$ |
| 185:1 | $45397615981574521703722337359345869563$ | $15695427976007936301909431812416205123$ | $-47021124981259692125076051434$ | $25534385391724973013190005618$ | $10932102455886562431206596611$ | $-429670100605988918958026933$ | $1634125810846026104$ |
| 185:2 | $69668807957223426927121823569320171579$ | $37129672855963248529737816197646717462$ | $87974263118854781964190140895$ | $-20997061517589917035821245027$ | $-19731092343869142972854996805$ | $6340123120865385631483529549$ | $4682668473098125955$ |
| 185:3 | $71271362220222722009941575484696858021$ | $15467533912541802235296640450084592611$ | $62971807596066886977446816252$ | $-26400182264382992357726946581$ | $8165427317328747410894861743$ | $292449582324399985071190229$ | $3270491033956423840$ |
| 185:4 | $86883892768148037531022698924901470976$ | $-39795931366523486469369345832438881287$ | $570430302687058783194506556$ | $-91691769809512733409961477$ | $4357038616933814793306044752$ | $-697018677808972475186757388$ | $921825734009770661$ |
| 185:5 | $89392798287413179476742424171114224878$ | $-59738121756012758762882266037450173286$ | $-741354264355089566977850299$ | $198491854251628379010695522$ | $-1883671250531392596576208481$ | $-76355386437614247998121586$ | $1144420111828541$ |
| 186:0 | $33932859887008012389458997391942004766$ | $29195282266737786011248177563954297997$ | $-40197161216859634318057772540$ | $13073747669959015795321562766$ | $-21201706889913311952502440737$ | $7881490639551442187461213269$ | $8886647638418623539$ |
| 186:1 | $45461610136602888909187612270088481783$ | $15694353151591441534259967033689819167$ | $-47237925895554875629417304910$ | $25661257964279006343123765288$ | $10929259725718817577811429498$ | $-430191118784757819727230938$ | $1658629287608571380$ |
| 186:2 | $69616273724819772109883942483664515735$ | $37145481925631455410628265059062586925$ | $88090674925386924420253444388$ | $-21030363215947257570062940636$ | $-19601121417155958985306811673$ | $6307118492331123994201516938$ | $4680042168715187643$ |
| 186:3 | $71205205237609838888355360404040573173$ | $15468262442177552208932453765458898087$ | $63176915406096433508772647567$ | $-26525723883843339679585581040$ | $8177415211021014166390778368$ | $290378683928250375905969283$ | $3262406204623312884$ |
| 186:4 | $86883663640853553687065646166572040959$ | $-39797673173760099536073125804149345054$ | $569995267208757028371595136$ | $-91610084946390324931593047$ | $4353733075595216469629224416$ | $-696427242151291709980313085$ | $928588738054146737$ |
| 186:5 | $89393294454603925918705321361003934049$ | $-59738312652060090462429873883466489192$ | $-741157335619663200497818326$ | $198441901787013444585286022$ | $-1883128906552105667700504492$ | $-76361447787316678484410975$ | $1143975874628834$ |
| 187:0 | $33965586038206507751034600483476550174$ | $29215003465260003273370903430738999112$ | $-40313799463219031571422578503$ | $13107213319630657813184479389$ | $-21254341912253692730456840856$ | $7895482844418522649788952861$ | $8922401824058891819$ |
| 187:1 | $45525923888245223775353905231958154777$ | $15693277011863166087394627040878253437$ | $-47458309379010374409714890162$ | $25790070813193532237598938795$ | $10926427569132962984373963191$ | $-430722398325621356011425143$ | $1683752404813521260$ |
| 187:2 | $69563655945955720873083440080745982649$ | $37161208377472366420530153450505711065$ | $88207912990382262808258985262$ | $-21063899141326385324599550427$ | $-19470813261893832106182882978$ | $6274028720220821945875752278$ | $4677439794569887820$ |
| 187:3 | $71138731980340786945354742496497766592$ | $15468985828818465549370626480881055953$ | $63385630493163505158074489071$ | $-26653210115763339773295881476$ | $8189302371605963393161439175$ | $288335214338667374696851728$ | $3254138237561963439$ |
| 187:4 | $86883434717627554742484501674794185113$ | $-39799413503386994680850619885467376777$ | $569560827262006246415476207$ | $-91528514984290870928595197$ | $4350431783877551693346600463$ | $-695836589795826932491453873$ | $935468318339312271$ |
| 187:5 | $89393790496939316661761798980437447667$ | $-59738503563233506718636433488189148458$ | $-740960494048517047823138898$ | $198391969964940242149715119$ | $-1882586920571190229488540595$ | $-76367487310664260932857168$ | $1143531815749027$ |
| 188:0 | $33998396154913537063228831820602331324$ | $29234759754697758986122636655145664011$ | $-40431304973794572390894146119$ | $13140920539636810770208970459$ | $-21307298771558177262217320158$ | $7909563535248454315360433536$ | $8958481817996036833$ |
| 188:1 | $45590562148894388400878703851262991460$ | $15692199530803100755509796435702515209$ | $-47682368206810904294725752679$ | $25920873592597158921975209685$ | $10923606410395917079622968983$ | $-431264234284540395283764249$ | $1709517408929224032$ |
| 188:2 | $69510954031629734836605372629628528931$ | $37176851997579311187293381917761968160$ | $88325987219722659788033106450$ | $-21097672048280311682709882303$ | $-19340165058120293563145676721$ | $6240852963671913189564904916$ | $4674861616260444458$ |
| 188:3 | $71071937525211255309501103587270919883$ | $15469704141250496447740115875992551139$ | $63598045530380690781896151854$ | $-26782690591260019919583672915$ | $8201089008398329772506531838$ | $286319346646409904152615561$ | $3245676231642230513$ |
| 188:4 | $86883205998183067674592346309857638134$ | $-39801152357360637788313867408539571508$ | $569126981689598265683738846$ | $-91447059699679760529967274$ | $4347134734093981733692662502$ | $-695246719311415393751516719$ | $942467466229102819$ |
| 188:5 | $89394286414470942097355337164154866408$ | $-59738694489478482158509627023522075314$ | $-740763739583111677242386108$ | $198342058772640342632932581$ | $-1882045292233744092518396667$ | $-76373505040059894322538719$ | $1143087935176918$ |
| 189:0 | $34031290844545042817945768582241052764$ | $29254551357496826132052958307264460282$ | $-40549687804532518266188213621$ | $13174872129584087169263302656$ | $-21360581099975680278679151579$ | $7923733699291896953217437383$ | $8994892276877734871$ |
| 189:1 | $45655529957306565784293324840992680496$ | $15691120681640091186652672830525621258$ | $-47910198529255217751721737421$ | $26053717752690637662634249963$ | $10920796690291984202073644681$ | $-431816932606369820241936183$ | $1735947584482459482$ |
| 189:2 | $69458167385898267169082353131869722771$ | $37192412569923251321346472397639320248$ | $88444907680385407424294532214$ | $-21131684736016281642207147481$ | $-19209173924866261127572081758$ | $6207590365602699806882428999$ | $4672307905378596647$ |
| 189:3 | $71004816822710933860663509369022305597$ | $15470417448707085479429041752676401308$ | $63814256566616671117191032153$ | $-26914216737688148606779208947$ | $8212775309183185505856830609$ | $284331265832964446689455828$ | $3237008710599265996$ |
| 189:4 | $86882977482233677599327232624685831966$ | $-39802889737633921043667166888028010521$ | $568693729337226646315008281$ | $-91365718869580420084618509$ | $4343841918575674646228731704$ | $-694657629270258693023833465$ | $949589276455457940$ |
| 189:5 | $89394782207250360709952004119817960808$ | $-59738885430740572353317330936440398102$ | $-740567072164963528537073291$ | $198292168197356590909877312$ | $-1881504021185325238294099835$ | $-76379501007856102649484223$ | $1142644232900129$ |

## 7. Two closed crossing cells and their endpoint inequalities

Let the event cells be

$$
V_x=[143750631793/10^9,143750631794/10^9],\qquad
V_y=[145067443732/10^9,145067443733/10^9].
\tag{7.1}
$$

Their designated branches are respectively two and three.
Each row below uses the identical seven-integer scales (5.1), with
$v_c,h_v$ taken from its event cell rather than (5.2).
All six sources are included so that their ordering and branch
identification use the same exhaustion argument as the strip cells.

| Event and branch | $M_r$ | $M_b$ | $A_{00}$ | $A_{01}$ | $A_{10}$ | $A_{11}$ | $R_\rho$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| x:0 | $27514751545012906588024730250844468933$ | $25066838374732410868533695025588600325$ | $-25232852919362192990505338770$ | $8653609572815294067327587803$ | $-13294457388427039127712241553$ | $5848771954120240631848809968$ | $7962$ |
| x:1 | $34351753411403323511263078625547136054$ | $15941173449239650213359923656815667861$ | $-29502811336073707539811307761$ | $13973747814344426567389241209$ | $11597222552908504072838280670$ | $-377132132805836655379435244$ | $1790$ |
| x:2 | $80901699436820873790365021832021285121$ | $31146752776128891890084564384443553013$ | $71965732655382725150451438491$ | $-16439052901859089368833664947$ | $-42808704795613623064010766087$ | $12520760038101818777868613610$ | $9035$ |
| x:3 | $82989467326221645483318550409687078430$ | $14926870125434604870365109059873157622$ | $49489390315991606642160593039$ | $-15398960734702247054631336515$ | $-385553430462506360651060598$ | $1974330437886880894657655420$ | $11849$ |
| x:4 | $86947126155679790812285592001093703456$ | $-39318151297559229769979165734815369463$ | $698655151237691833097098477$ | $-115879145332410884193953653$ | $5319467101059655051743523244$ | $-870078221725568792247120247$ | $639$ |
| x:5 | $89267090779706801667441915105739999604$ | $-59691868856482607773661962924596069708$ | $-792487493460345126053609082$ | $211412116876945853979272946$ | $-2028596190403029926373042095$ | $-74117774149359913723935881$ | $4$ |
| y:0 | $28690226297717188325923262172498270328$ | $25856059157776977941428823352699007781$ | $-27056457842728444596484827580$ | $9219632348979014943372420865$ | $-14505606572534762880082079650$ | $6144785954178752662438762856$ | $8682$ |
| y:1 | $36264206877297146092838927938761107229$ | $15890705417210783487690800552231376273$ | $-30876391963496234974080895870$ | $15121136755841628753018125896$ | $11484707376687569230506635719$ | $-388661664972058512021292322$ | $1653$ |
| y:2 | $78696336874095482334445835733501068821$ | $32733877434362989570190439052964691123$ | $74224049022124248748904384711$ | $-17072355251636804600766823621$ | $-39606585976099306577442475428$ | $11539616264530087602216646236$ | $8670$ |
| y:3 | $80901699437686502523351461564777744426$ | $15140144257880504436701272120053887466$ | $49722445722142263860665349478$ | $-16367254693273928099342353158$ | $2948275756901855078432472179$ | $1311371791578317721908383165$ | $8704$ |
| y:4 | $86932266494176858904158448116294771819$ | $-39429893783018385994024670428883148373$ | $667032118614615661828294755$ | $-109896304028899348253567760$ | $5084280724091857709763345559$ | $-827644687502938641089710180$ | $698$ |
| y:5 | $89294738944177510022153221091176410651$ | $-59701670431747025620633048854648793554$ | $-781025547343070222565526227$ | $208524654383477641772815019$ | $-1995384490267235983167081628$ | $-74736444774670959854510810$ | $3$ |

**Proposition 7.1 (Strict event signs).** Put
$\alpha_L=809016994374947424102293417182/10^{30}$ and
$\alpha_U=\alpha_L+10^{-30}$.
Then $\Psi_2(\alpha_L)<0<\Psi_2(\alpha_U)$.
For the designated record define

$$
\delta_L=m_r+L_0(v_L-v_c)-\rho-\alpha_U,\qquad
\delta_U=\alpha_L-m_r-L_0(v_U-v_c)-\rho.
\tag{7.2}
$$

The event guards and self-map inequalities of Proposition 5.3 hold.
The following table gives strict upper bounds with denominator
$10^{10}$ for $\widehat q,\widehat\theta$ over all six records, and strict lower
bounds with denominator $10^{14}$ for the designated margins.

| Event | upper $10^{10}\widehat q$ | upper $10^{10}\widehat\theta$ | lower $10^{14}\delta_L$ | lower $10^{14}\delta_U$ |
| --- | --- | --- | --- | --- |
| x | $26$ | $4999409911$ | $148$ | $1495$ |
| y | $30$ | $4999172053$ | $1010$ | $626$ |

Proof. The two polynomial signs use the explicit quadratic $\Psi_2$,
with rational endpoints. Substituting the event records into
(4.2)–(5.5) gives the first two columns; substitution into (7.2)
gives the last two by exact rational subtraction. The latter
margins are positive, uniformly on $K$, because the affine boxes
already include every $p\in K$ in their Banach bound.
Therefore the designated source has $r>\alpha$ at the lower
endpoint and $r<\alpha$ at the upper endpoint. The strict derivative
sign supplied by Proposition 5.3 gives one crossing, as proved in
strip Theorem 8.2. This does not count every root of $Q$ in these
intervals. ∎

## 8. The two entire singular lines

For the strict roots of $\Phi$, use the closed rational intervals

$$
I_-=[149383/1108052,182914/1356769],\qquad
I_+=[1412683/1565387,1774115/1965888].
\tag{8.1}
$$

Their global and local root counts follow from the Sturm chain
specified in strip Lemma 6.1; these intervals exhaust all strict
zeros. Evaluate on each entire interval in the order

$$
\begin{aligned}
j&=1/8+8r(1-r),\qquad n=j+r,\\
A_5&=1+(n+5/4)(4-15/j+160/9-10/n),\\
a_6&=50-36/j-20/n,\qquad
\epsilon=([p_c-h_p,p_c+h_p]-24)/A_5,\\
s&=24+\epsilon+(5/2+n)(24+\epsilon a_6).
\end{aligned}
\tag{8.2}
$$

All operations use Definition 4.1. The unrounded expression for
$A_5$, rather than its coarser displayed guard, is used in the
subsequent division.

**Proposition 8.1 (Singular fifth-response lifts and sixth responses).**
The interval enclosures from (8.2) are contained strictly in

| Source interval | $A_5$ guard | Actual sixth-response enclosure |
| --- | --- | --- |
| $I_-$ | $(-908,-907)/10^3$ | $(1198704988168,1198704988252)/10^{10}$ |
| $I_+$ | $(-5217,-5216)/10^3$ | $(1387528570299,1387528570311)/10^{10}$ |

Proof. The first two interval expressions have positive $j,n$.
The next expression excludes zero by the displayed $A_5$ guards,
so the remaining division is defined. Substitution into the rational
endpoint rules gives the stated bounds. At the actual root,
$p=24+\epsilon A_5$ fixes exactly one entire world on its singular
line, by strip Lemma 3.1. The last line of (8.2) uses this world's
same gain and drift and the original sixth-M trace.
Both enclosures are below $142$; no singular world contributes
to the closed strip. ∎

## 9. Proof scope and mathematical sources

The finite inputs consist exactly of the owning integer polynomial
table, formulas (1.1)–(8.2), the twenty projected-root rows, the 190
six-source cells and the two six-source event cells.
There are 1152 rational source records. Every guard and enclosure
has a stated rational reconstruction, and every interval covers
all real points between its endpoints.

The mathematical implications are standard Descartes/Bernstein root
bounds and positive de Casteljau subdivision (Sections 2–3),
outward interval arithmetic and differentiation (Sections 4–5),
Banach contraction, and the implicit function theorem after source
Jacobian invertibility. The strip volume supplies their ordinary
proofs and bibliographic sources, as well as the exact Sylvester
and base-corank correspondence. Its cited owning Section 30 supplies
the separate Rouché and resultant argument for the nonzero necessary
polynomial; the present tables do not replace that supplier.

This companion proves the finite inequalities for the uniform strip
and its two designated crossings. It neither decides outside-strip
collisions nor claims Lean verification, a global cardinality
classification or a physical conclusion.

## 追加锚（本行以下为增补区）
