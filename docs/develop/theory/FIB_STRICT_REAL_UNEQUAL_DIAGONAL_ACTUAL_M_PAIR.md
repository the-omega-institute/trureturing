# An exact unequal-diagonal pair for the original terminal M response

## 1. Original worlds and the common-base question

**Definition 1.1 (Complete original world).** A world is a triple $W=(P,g,d)$ with

$$
P=P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},\qquad
0<r<1,\quad b>0,\quad d\in\mathbb R,\quad
0\ne g\in\mathbb R[s],\quad\deg g\le3.
$$

The two actions are

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
$$

A chronological word acts by left multiplication: $Q_0=I$ and $Q_i=E_iQ_{i-1}$. Its reading at the literal clock $i$ is

$$
y_i(W)=d+g(i)\operatorname{tr}(Q_iP).
$$

Each world uses its own one fixed drift and one whole gain polynomial at every clock, including alternative terminal actions. There is no reset or additional port. Neither the off-diagonal entries nor the drift are bounded in the original domain. Zero drift, vanishing gain samples, repeated gain roots and degrees below three are admitted, provided the whole gain is nonzero.

**Definition 1.2 (The entire acquired child).** Let $C(p,v)$ be the set of all complete original worlds having the chronological acquired word $J,M,J,M,M,M$ and the seven readings

$$
(y_0,y_1,y_2,y_3,y_4,y_5,y_6)
=(0,24,147/5,24,18,p,v).
$$

If $Q_6$ is the acquired product, write

$$
a(W)=d+g(7)\operatorname{tr}(JQ_6P),\qquad
m(W)=d+g(7)\operatorname{tr}(MQ_6P).
$$

The unrestricted common-base question asks for $p\ne24,v$ and independently selected pairs in this same entire child such that

$$
\begin{gathered}
W_0,W_1,W_2,W_3\in C(p,v),\\
W_0\ne W_1,\quad a(W_0)=a(W_1),\qquad
W_2\ne W_3,\quad m(W_2)=m(W_3).
\end{gathered}
$$

The pairs may overlap, and no equality between their two common terminal answers is required. The theorem below supplies the M pair at an exact base. The independent J pair at that base remains an additional obligation.

**Theorem 1.3 (A strict actual M pair).** There exist exact real algebraic numbers $p_*,v_*,m_*$ with $p_*\ne24$ and distinct complete original worlds $W_2,W_3\in C(p_*,v_*)$ satisfying

$$
r(W_2)=2/5<r(W_3),\qquad m(W_2)=m(W_3)=m_*.
$$

Their terminal J readings satisfy

$$
-\frac{15384444413}{500000000}
\le a(W_2)-a(W_3)
\le-\frac{1230755553}{40000000}<0.
$$

In particular these two worlds themselves do not constitute a J collision pair. The proof and exact definitions occupy Sections 2–6.

## 2. Polynomial coordinates and the entire gain

**Definition 2.1 (Polynomial circuit).** For independent source coordinates $(r,b)$ put

$$
\begin{aligned}
\mathcal J&=b^2+r(1-r),&\mathcal N&=\mathcal J+rb,\\
T&=1+b,&U&=1+2b,&S&=(8b-1)(2+5b),\\
\widehat D&=5\{(b^2+8b+4)\mathcal J\mathcal N
                  -2TUb(\mathcal J+\mathcal N)\},\\
\widehat C_0&=-24\widehat D+3S\mathcal J\mathcal N,\\
\widehat C_1&=3S\mathcal N b,\\
\widehat C_2&=3(49b+34)\mathcal J\mathcal N
                 -54Ub(\mathcal J+\mathcal N),\\
\widehat C_3&=3S\mathcal J b,\\
\widehat C_4&=-\widehat C_0+4\widehat C_1-6\widehat C_2+4\widehat C_3,\\
\widehat B_5&=-4\widehat C_0+15\widehat C_1-20\widehat C_2+10\widehat C_3,\\
\widehat B_6&=-10\widehat C_0+36\widehat C_1-45\widehat C_2+20\widehat C_3,\\
\widehat B_7&=-20\widehat C_0+70\widehat C_1-84\widehat C_2+35\widehat C_3.
\end{aligned}
$$

The response numerators and common denominator are

$$
\begin{aligned}
H&=b\widehat D,\\
P_p&=-b\widehat C_0+(bU+\mathcal N)\widehat B_5,\\
P_v&=-b\widehat C_0+(2bU+\mathcal N)\widehat B_6,\\
P_m&=-b\widehat C_0+(3bU+2\mathcal N)\widehat B_7,\\
P_a&=-b\widehat C_0+(bT+2\mathcal J+4br)\widehat B_7.
\end{aligned}
$$

On $b>0,0<r<1,\widehat D\ne0$, define

$$
\begin{gathered}
(p,v,m,a)=(P_p,P_v,P_m,P_a)/H,\qquad
d=-\widehat C_0/\widehat D,\\
\ell_i(s)=\prod_{\substack{0\le k\le3\\k\ne i}}\frac{s-k}{i-k},\qquad
g(s)=\frac{1}{\widehat D}\sum_{i=0}^3\widehat C_i\ell_i(s),\\
W(r,b)=(P(r,b),g,d),\qquad
j=\mathcal J/b,\quad n=\mathcal N/b,\quad
\Lambda=\frac{2\widehat D}{5TU\mathcal J\mathcal N}.
\end{gathered}
$$

The symbol $P(r,b)$ denotes the source matrix, while $P_p,P_v,P_m,P_a$ are scalar polynomials. The cardinal polynomials use only the fixed distinct nodes $0,1,2,3$.

**Lemma 2.2 (Exact original-row identities).** This circuit gives the required first five original readings, and its responses $p,v,a,m$ are the literal original responses.

Proof. The following are polynomial identities in $r,b$:

$$
\begin{aligned}
-\widehat C_0+\widehat C_0&=0,\\
-b\widehat C_0+\mathcal J\widehat C_1&=24b\widehat D,\\
-\widehat C_0+T\widehat C_2&=(147/5)\widehat D,\\
-b\widehat C_0+\mathcal N\widehat C_3&=24b\widehat D,\\
-\widehat C_0+U\widehat C_4&=18\widehat D.
\end{aligned}
$$

The odd-row identities follow immediately from the two factors $\mathcal J,\mathcal N$ in $\widehat C_0+24\widehat D$. For the row at clock two, set $A=b^2+8b+4$ and use

$$
T(49b+34)-S=9A.
$$

Substitution of $\widehat D$ then cancels the coefficient of $b(\mathcal J+\mathcal N)$ and gives the displayed identity. For the row at clock four, substituting $\widehat C_4$ reduces its difference from $18\widehat D$ to the sum of $\mathcal J\mathcal N$ times

$$
5(6+24U)A-3(1+U)S-18U(49b+34)=0
$$

and $Ub(\mathcal J+\mathcal N)$ times

$$
-10(6+24U)T+12S+324U=0.
$$

Both are elementary identities in $b$. Thus none of these row equalities is an assertion of numerical closeness.

The evaluations of the same four cardinal polynomials are

$$
\begin{array}{c|rrrr}
s&\ell_0(s)&\ell_1(s)&\ell_2(s)&\ell_3(s)\\ \hline
4&-1&4&-6&4\\
5&-4&15&-20&10\\
6&-10&36&-45&20\\
7&-20&70&-84&35
\end{array}.
$$

Consequently $\widehat Dg(4)=\widehat C_4$ and $\widehat Dg(i)=\widehat B_i$ for $i=5,6,7$. In particular these samples belong to one polynomial of degree at most three.

Direct multiplication of the literal action matrices gives

$$
\begin{array}{c|c|c}
\text{word}&Q&\operatorname{tr}(QP)\\ \hline
\varnothing&I&1\\
J&\begin{pmatrix}0&1\\1&0\end{pmatrix}&j\\
JM&\begin{pmatrix}1&0\\1&1\end{pmatrix}&T\\
JMJ&\begin{pmatrix}1&1\\1&0\end{pmatrix}&n\\
JMJM&\begin{pmatrix}1&0\\2&1\end{pmatrix}&U\\
JMJMM&\begin{pmatrix}2&1\\3&1\end{pmatrix}&U+n\\
JMJMMM&\begin{pmatrix}3&1\\5&2\end{pmatrix}&2U+n\\
JMJMMMJ&\begin{pmatrix}5&2\\3&1\end{pmatrix}&T+2j+4r\\
JMJMMMM&\begin{pmatrix}5&2\\8&3\end{pmatrix}&3U+2n
\end{array}.
$$

Divide the first five identities by their nonzero $b\widehat D$ or $\widehat D$ as appropriate, and use these traces. This gives exactly the first five readings in Definition 1.2. Substituting the remaining traces gives precisely the four quotients in Definition 2.1 at clocks five, six and seven. If the whole gain were zero, the first two readings would both equal $d$, contrary to $0\ne24$. Thus the constructed gain is nonzero. All four entries of the source matrix are positive; its determinant is zero and its trace is one. It is therefore a valid rank-one source. ∎

## 3. Exact rational box and preconditioner

**Definition 3.1 (The transverse equations).** Fix only the first diagonal parameter $r_0=2/5$. For $x=(b_0,r_1,b_1)$ set

$$
F(x)=\begin{pmatrix}
p(2/5,b_0)-p(r_1,b_1)\\
v(2/5,b_0)-v(r_1,b_1)\\
m(2/5,b_0)-m(r_1,b_1)
\end{pmatrix},\qquad \rho=10^{-38}.
$$

Let $c=(c_1,c_2,c_3)$ be the exact rational center

$$
\begin{aligned}
c_1&=\frac{2039147952441419202632153181257224702552874458857650091406952613561780673772487932009}{50000000000000000000000000000000000000000000000000000000000000000000000000000000000000}\\
c_2&=\frac{6375033978214738667594335994587431421676713827650888392964909894052987634591944798563}{10000000000000000000000000000000000000000000000000000000000000000000000000000000000000}\\
c_3&=\frac{4091698421060610059422739287384503573541827251561253278343342658415925434482704952889}{100000000000000000000000000000000000000000000000000000000000000000000000000000000000000}
\end{aligned}
$$

and let $X=\prod_{i=1}^3[c_i-\rho,c_i+\rho]$. In the following rational preconditioner each ordered triple specifies one row:

$$

\begin{aligned}
C_{1,\bullet}&=\left(\frac{4760752792724642838056360064936246839152300259290879391502414280443802317835630321279}{100000000000000000000000000000000000000000000000000000000000000000000000000000000000},\;\frac{-4084595358566180170236201926494966219425147105733117947400282420330794487052553864347}{100000000000000000000000000000000000000000000000000000000000000000000000000000000000},\;\frac{6597316950300814141221327149499933526034628701315530535426688189527160540945635381841}{1000000000000000000000000000000000000000000000000000000000000000000000000000000000000}\right)\\[4pt]
C_{2,\bullet}&=\left(\frac{4452822096166368128429083785020269806535776806628826279501411542541466278035625295973}{100000000000000000000000000000000000000000000000000000000000000000000000000000000000},\;\frac{-3815845619806274487590185019107924354624163408131864384154574693319517079851253933851}{100000000000000000000000000000000000000000000000000000000000000000000000000000000000},\;\frac{3082884553568573400957171854986651197936819111189265500197929779999846537045801321017}{500000000000000000000000000000000000000000000000000000000000000000000000000000000000}\right)\\[4pt]
C_{3,\bullet}&=\left(\frac{599000793277819466249971680386890018147383944878919294651771695250452329556954802653}{12500000000000000000000000000000000000000000000000000000000000000000000000000000000},\;\frac{-2055819906555504678700940955905733157061319809584648426194748085565409275003733030071}{50000000000000000000000000000000000000000000000000000000000000000000000000000000000},\;\frac{6640938320144992400824219907657706571334416694028687851585889807915099861354130002381}{1000000000000000000000000000000000000000000000000000000000000000000000000000000000000}\right)
\end{aligned}
$$

These numbers, the circuit in Definition 2.1 and the order of the three equations completely determine the inclusion below.

## 4. Rational inclusion and existence

**Definition 4.1 (Outward interval arithmetic).** Let $\sigma=10^{110}$. Represent an interval by an integer pair $[L,U]/\sigma$, including a rational $t$ by

$$
\operatorname{enc}(t)=\frac1\sigma
[\lfloor\sigma t\rfloor,\lceil\sigma t\rceil].
$$

Addition and negation are exact on integer endpoints. For multiplication and reciprocal use

$$
\begin{aligned}
\frac{[L,U]}\sigma\frac{[V,W]}\sigma
&\subseteq\frac1\sigma\left[
\left\lfloor\frac{\min(LV,LW,UV,UW)}\sigma\right\rfloor,
\left\lceil\frac{\max(LV,LW,UV,UW)}\sigma\right\rceil\right],\\
\left(\frac{[L,U]}\sigma\right)^{-1}
&\subseteq\frac1\sigma\left[
\left\lfloor\frac{\sigma^2}{U}\right\rfloor,
\left\lceil\frac{\sigma^2}{L}\right\rceil\right],\qquad LU>0.
\end{aligned}
$$

Each operation encloses its real interval value. To carry derivatives, attach the three unit vectors to $b_0,r_1,b_1$, respectively, and attach a zero derivative to every constant. Propagate componentwise by

$$
D(f+h)=Df+Dh,\quad D(fh)=hDf+fDh,\quad
D(1/f)=-Df/(ff).
$$

All scalar and derivative operations in this prescription are interval operations. In particular, it encloses the derivatives on the entire box, rather than derivatives at just the center.

Evaluate Definition 2.1 in its displayed factored order, from left to right for unparenthesized sums and products, with each power of two evaluated as a product. First form the two endpoint circuits, then subtract in the order of Definition 3.1. Evaluate the center by the same interval operations at $[c_i,c_i]$. Form each matrix dot product in increasing index order from zero. This gives an unambiguous finite rational inclusion with outward rounding at every operation.

**Lemma 4.2 (Finite contraction bounds).** The entire box $X$ contains no circuit pole. If $[DF(X)]$ is the derivative enclosure obtained above and

$$
[E]=I-C[DF(X)],\qquad
q_i=\sum_{k=1}^3\max\{|\inf[E_{ik}]|,|\sup[E_{ik}]|\},
$$

then the following rational upper bounds hold:

| Row $i$ | Upper bound for $|[CF(c)]_i|$ | Upper bound for $q_i$ |
| --- | --- | --- |
| 1 | $10^{-80}$ | $572\cdot10^{-32}$ |
| 2 | $10^{-80}$ | $535\cdot10^{-32}$ |
| 3 | $10^{-80}$ | $576\cdot10^{-32}$ |

Here the absolute value of an interval means the maximum absolute value of its endpoints. In particular

$$
\|CF(c)\|_\infty\le10^{-80}<10^{-70},\qquad
\sup_{x\in X}\|I-CDF(x)\|_\infty
\le576\cdot10^{-32}<6\cdot10^{-30}<10^{-20}.
$$

Proof. Apply Definition 4.1 to the three equations and their forward derivatives. The entries of $C$, $c$ and $\rho$ have exact grid encodings; divisions within the circuit are rounded outward by the displayed reciprocal formula. The three center upper bounds are the ceilings of the resulting maximum endpoint magnitudes on the $10^{-80}$ grid. The three derivative upper bounds are the ceilings of the interval row sums on the $10^{-32}$ grid. The pole separations are given in Section 5. Every step uses only integer addition, multiplication, ordered comparison and integer floor or ceiling division, so the tabulated inclusions are reproducible from the printed rational data. ∎

**Theorem 4.3 (Unique exact zero).** There is exactly one zero $x_*=(b_{0*},r_{1*},b_{1*})$ of $F$ in $X$, and it lies in the interior of $X$.

Proof. Put $T_F(x)=x-CF(x)$, $\eta=10^{-80}$ and $q=576\cdot10^{-32}$. Since the box is convex and pole-free, the derivative bound and the fundamental theorem of calculus along segments give

$$
\|T_F(x)-T_F(z)\|_\infty\le q\|x-z\|_\infty\qquad(x,z\in X).
$$

Furthermore

$$
\|T_F(x)-c\|_\infty
\le\eta+q\rho
=10^{-80}+576\cdot10^{-70}<10^{-38}=\rho.
$$

Thus $T_F$ maps $X$ into its interior and is a strict contraction. Starting with any point of $X$, successive iterates have differences bounded by a geometric series with ratio $q<1$. Completeness of the closed box gives a limit in $X$; continuity makes it a fixed point. Two fixed points would have their distance at most $q$ times itself, so they coincide. The strict self-map bound puts the fixed point in the interior.

To obtain a zero of $F$, rather than just a fixed point, note that $\|I-CDF(c)\|_\infty<1$. The geometric series in $I-CDF(c)$ is an inverse of $CDF(c)$. Since these are square matrices, $C$ is invertible as well. Therefore $CF(x)=0$ is equivalent to $F(x)=0$. This proves existence and uniqueness of the exact zero, without an inference from numerical residuals or overlapping response intervals.

The coordinates are real algebraic. Indeed, with $H_0=H(2/5,b_0)$ and $H_1=H(r_1,b_1)$, clear denominators to obtain

$$
\begin{aligned}
G_p&=P_p(2/5,b_0)H_1-P_p(r_1,b_1)H_0,\\
G_v&=P_v(2/5,b_0)H_1-P_v(r_1,b_1)H_0,\\
G_m&=P_m(2/5,b_0)H_1-P_m(r_1,b_1)H_0.
\end{aligned}
$$

These have rational coefficients and exactly the same zero set as $F$ on $X$, since both denominators are separated from zero there. Together with the rational box inequalities they define a singleton semialgebraic over $\mathbb Q$. Its coordinate projections are semialgebraic over $\mathbb Q$ by Tarski–Seidenberg. A one-dimensional singleton defined over $\mathbb Q$ must lie at a root of a nonzero rational polynomial: otherwise the signs of the finitely many polynomials in a quantifier-free description would be locally constant. Each coordinate is therefore real algebraic. Rational evaluation gives the same property for $p_*,v_*,m_*$. ∎

## 5. Denominators, strict guards and terminal separation

All endpoints in the following tables are exact rationals. The intervals are outward inclusions for the indicated endpoint circuits on the whole box $X$, rather than estimates made only at $x_*$. The notation $\widehat D$ refers to the polynomial denominator in Definition 2.1; it is $b^2$ times the unscaled denominator of Section 7.

| Quantity | $W(2/5,b_0)$ | $W(r_1,b_1)$ |
| --- | --- | --- |
| $b$ | $[\frac{40782959}{1000000000},\frac{509787}{12500000}]$ | $[\frac{5114623}{125000000},\frac{8183397}{200000000}]$ |
| $r$ | $[\frac{2}{5},\frac{2}{5}]$ | $[\frac{637503397}{1000000000},\frac{318751699}{500000000}]$ |
| $\widehat D$ | $[\frac{1119712451}{1000000000},\frac{279928113}{250000000}]$ | $[\frac{26940989}{25000000},\frac{1077639561}{1000000000}]$ |
| $H$ | $[\frac{45665187}{1000000000},\frac{11416297}{250000000}]$ | $[\frac{137793}{3125000},\frac{44093761}{1000000000}]$ |
| $\Lambda$ | $[\frac{6382086513}{1000000000},\frac{3191043257}{500000000}]$ | $[\frac{15882699}{2500000},\frac{6353079601}{1000000000}]$ |
| $\mathcal J$ | $[\frac{241663249}{1000000000},\frac{966653}{4000000}]$ | $[\frac{46553403}{200000000},\frac{29095877}{125000000}]$ |
| $\mathcal N$ | $[\frac{257976433}{1000000000},\frac{128988217}{500000000}]$ | $[\frac{258851731}{1000000000},\frac{64712933}{250000000}]$ |
| $T$ | $[\frac{1040782959}{1000000000},\frac{13009787}{12500000}]$ | $[\frac{130114623}{125000000},\frac{208183397}{200000000}]$ |
| $U$ | $[\frac{540782959}{500000000},\frac{1081565919}{1000000000}]$ | $[\frac{67614623}{62500000},\frac{1081833969}{1000000000}]$ |
| $j$ | $[\frac{5925593811}{1000000000},\frac{1481398453}{250000000}]$ | $[\frac{5688762739}{1000000000},\frac{284438137}{50000000}]$ |
| $n$ | $[\frac{6325593811}{1000000000},\frac{1581398453}{250000000}]$ | $[\frac{6326266137}{1000000000},\frac{3163133069}{500000000}]$ |

Every displayed denominator interval is strictly positive. Positivity of $b,\mathcal J,\mathcal N$ also gives $j=\mathcal J/b>0$ and $n=\mathcal N/b>0$; positivity of $b$ gives $T,U>0$. Thus the original source division by $b$, the gain and drift division by $\widehat D$, the response division by $H$, and the displayed expression for $\Lambda$ all have nonzero denominators. The interpolation denominators are fixed nonzero integers. The diagonal guards satisfy $0<r<1$ at both endpoints, and the second diagonal interval lies strictly above $2/5$. No saturation or denominator clearing can introduce a spurious solution inside $X$.

The response and drift inclusions are

| Quantity | $W(2/5,b_0)$ | $W(r_1,b_1)$ |
| --- | --- | --- |
| $p$ | $[\frac{902856331}{500000000},\frac{1805712663}{1000000000}]$ | $[\frac{902856331}{500000000},\frac{1805712663}{1000000000}]$ |
| $v$ | $[\frac{5382724003}{31250000},\frac{172247168097}{1000000000}]$ | $[\frac{5382724003}{31250000},\frac{172247168097}{1000000000}]$ |
| $m$ | $[\frac{211019008913}{200000000},\frac{527547522283}{500000000}]$ | $[\frac{211019008913}{200000000},\frac{527547522283}{500000000}]$ |
| $a$ | $[\frac{48202563557}{50000000},\frac{964051271141}{1000000000}]$ | $[\frac{198964031993}{200000000},\frac{497410079983}{500000000}]$ |
| $d$ | $[\frac{24248021973}{1000000000},\frac{12124010987}{500000000}]$ | $[\frac{12124369917}{500000000},\frac{4849747967}{200000000}]$ |

In particular both endpoint $p$ intervals are disjoint from $24$. Subtracting the two terminal J interval evaluations before rounding to the $10^{-9}$ grid gives the sharper direct difference enclosure

$$
a(W(2/5,b_0))-a(W(r_1,b_1))
\in\left[-\frac{15384444413}{500000000},
         -\frac{1230755553}{40000000}\right].
$$

This interval excludes zero on the whole box. Its role is a strict J inequality; equality of the two M responses instead follows from the exact zero in Theorem 4.3.

## 6. Complete original realization

Proof of Theorem 1.3. Define, using the unique exact zero from Theorem 4.3,

$$
\begin{gathered}
W_2=W(2/5,b_{0*}),\qquad W_3=W(r_{1*},b_{1*}),\\
p_*=p(2/5,b_{0*}),\quad v_*=v(2/5,b_{0*}),\quad
m_*=m(2/5,b_{0*}).
\end{gathered}
$$

All divisions are legitimate by Section 5. Lemma 2.2 supplies the first five original readings, valid source matrices and nonzero whole gains of degree at most three. It also identifies $p,v,m,a$ with the literal readings using those same matrices, drifts and whole gains.

The first two coordinates of $F(x_*)=0$ give $p(W_3)=p_*$ and $v(W_3)=v_*$. Hence both worlds belong to the same entire original child $C(p_*,v_*)$. The third coordinate gives $m(W_3)=m_*$. The $p$ guard gives $p_*\ne24$. The separated diagonal parameters give $P(W_2)\ne P(W_3)$, so the complete triples are distinct. Their separately reconstructed drifts remain fixed through all eight clocks. The terminal J difference interval proves the final inequality in Theorem 1.3. This proves every assertion. ∎

For orientation, the common responses lie near $p_*=1.80571266239$, $v_*=172.24716809632$ and $m_*=1055.09504456528$. These approximations do not define the worlds or supply their equalities; the exact box, rational equations and unique-zero theorem do.

## 7. Correspondence with the reused ordinary sources

The complete-world domain, literal left-product convention and traces agree with [Common Parent Geometry](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md), Definitions 1.1 and 1.3. Its Theorem 2.1 gives the full parent converse, and Definition 7.1 gives the regular lift. The circuit here is the polynomial rescaling of [Support XI](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_XI.md), Definition 6.2.1, equations (6.2.1)–(6.2.3).

Explicitly, for that source's quantities $D,C_i,B_i$, the parameter correspondence is

$$
\mathcal J=bj,\quad\mathcal N=bn,\quad
\widehat D=b^2D,\quad\widehat C_i=b^2C_i,\quad
\widehat B_i=b^2B_i.
$$

Therefore the gain and drift agree identically, and multiplying each response numerator and denominator by $b$ after this rescaling gives precisely Definition 2.1. To verify the parent equation directly, one has the polynomial identity

$$
\begin{aligned}
2\widehat D=5\{&TU\mathcal J\mathcal N
 +6U\mathcal J\mathcal N+T\mathcal J\mathcal N\\
 &-4bTU\mathcal N-4bTU\mathcal J\}.
\end{aligned}
$$

It follows that

$$
\Lambda=1+6/T+1/U-4/j-4/n.
$$

With $\epsilon=d-24$ and $B=6/T-2/U=2(2+5b)/(TU)$, the chosen drift gives

$$
\epsilon=-\frac{3S\mathcal J\mathcal N}{\widehat D},\qquad
\epsilon\Lambda=-\frac{6S}{5TU},\qquad
\frac{24}{5}(b-1/8)B=\frac{6S}{5TU}.
$$

Thus the reused full-parent condition $\epsilon\Lambda+(24/5)(b-1/8)B=0$ holds exactly. Together with the first four gain samples this identifies the same whole-world lift. The regularity condition is a means of constructing these two worlds; it is no restriction on the entire child in Definition 1.2.

The fixed-node interpolation is the classical cardinal formula also used in those sources; see J.-P. Berrut and L. N. Trefethen, *Barycentric Lagrange Interpolation*, SIAM Review 46 (2004), 501–517, Section 2, [doi:10.1137/S0036144502417715](https://doi.org/10.1137/S0036144502417715). The contraction proof is given in full in Theorem 4.3. The singleton projection argument is the standard Tarski–Seidenberg consequence used in Common Parent Geometry, Definition 7.2; see J. Bochnak, M. Coste and M.-F. Roy, *Real Algebraic Geometry*, Springer, for semialgebraic projection. The contribution here is the exact transverse M incidence with its explicit original-world realization; the parent converse and response-map reduction are reused results.

## 8. The independent same-base J obligation

At the particular exact base $(p_*,v_*)$ constructed above, completing the unrestricted common-base target still requires distinct complete worlds

$$
W_0,W_1\in C(p_*,v_*),\qquad a(W_0)=a(W_1).
$$

No equality between $m(W_0)$ and $m(W_1)$ is required, and their M readings need not be $m_*$. They may overlap the constructed M pair. Their full gains and independent fixed drifts must realize every acquired original row at this exact base. A J pair at a different base, or at rounded approximations to this base, does not satisfy this obligation.

The inequality for $a(W_2)-a(W_3)$ eliminates only the use of these two selected worlds as that J pair. It supplies no exclusion concerning independently chosen companions. In particular there is no inventory of the entire child, no uniqueness statement outside the defining local box, and no global exclusion. Singular and exceptional sources, zero drift, vanishing gain samples, repeated gain roots and lower-degree gains remain in the unrestricted question. The result is an actual M pair and partial progress toward the independent-pair target; it does not settle the independent J obligation.

## 追加锚（本行以下为增补区）

## 9. The analytic M family and an exact response determinant

**Definition 9.1 (The reused analytic family).** Write
$\Phi(r,b)=(p(r,b),v(r,b))$ for the two acquired responses in
Definition 2.1 and put $\lambda _0=2/5$. Theorem 7.2 in
[AURIC–Langlands 语境与谱重构理论](AURIC_LANGLANDS_CONTEXT_AND_SPECTRAL_RECONSTRUCTION_THEORY.md),
Section 7, “真实碰撞对的一参数延拓”, supplies a real analytic family
through the exact zero of Theorem 4.3:

$$
\begin{aligned}
x(\lambda)&=(b_0(\lambda),r_1(\lambda),b_1(\lambda)),&
x(\lambda _0)&=(b_{0*},r_{1*},b_{1*}),\\
W_2(\lambda)&=W(\lambda,b_0(\lambda)),&
W_3(\lambda)&=W(r_1(\lambda),b_1(\lambda)),\\
\beta(\lambda)&=(p(\lambda),v(\lambda))
=\Phi(\lambda,b_0(\lambda)).
\end{aligned}
$$

On a connected open interval $I$ containing $\lambda _0$, that theorem
ensures

$$
\begin{gathered}
W_2(\lambda),W_3(\lambda)\in C(\beta(\lambda)),\qquad
W_2(\lambda)\ne W_3(\lambda),\qquad p(\lambda)\ne24,\\
m(W_2(\lambda))=m(W_3(\lambda)),\qquad
a(W_2(\lambda))<a(W_3(\lambda)).
\end{gathered}
$$

The family is the branch of the three equations equating $p,v,m$,
with $r(W_2)=\lambda$; it is not a new interpolation of readings.
The gains and fixed drifts are exactly those of Definition 2.1.
The domain of every entire child remains Definition 1.2.

**Definition 9.2 (An enclosing rational segment).** Define

$$
I_b=\left[\frac{40782959048828}{10^{15}},
             \frac{40782959048829}{10^{15}}\right],\qquad
S_0=\{2/5\}\times I_b.
$$

The rational center and radius of Definition 3.1 satisfy

$$
\frac{40782959048828}{10^{15}}<c_1-\rho
<c_1+\rho<\frac{40782959048829}{10^{15}}.
$$

Consequently $(2/5,b_{0*})\in S_0$, by Theorem 4.3.

The derivative enclosures and strict determinant bound in Lemma 9.3,
and the resulting quantitative motion and local injectivity in Theorem
10.1, are model-specific ordinary derivations in this repository
(`repo-derived`), with no claim of literature priority. The chain
rule, local monotonicity and real analytic identity principle used
below are classical intermediate inputs.

**Lemma 9.3 (Whole-segment derivative separation).** The response
circuit is pole-free on $S_0$. With columns ordered as $(r,b)$, its
ambient partial derivatives have the following rational enclosures
throughout $S_0$. Every endpoint numerator in the table is divided
by $10^6$.

| Derivative | Lower endpoint numerator | Upper endpoint numerator |
| --- | ---: | ---: |
| $p_r$ | $-17691121$ | $-17691120$ |
| $p_b$ | $725498392$ | $725498393$ |
| $v_r$ | $103013504$ | $103013505$ |
| $v_b$ | $-1673536106$ | $-1673536105$ |

In particular

$$
-45130<\Delta(r,b):=\det D\Phi(r,b)<-45129
\qquad ((r,b)\in S_0).
$$

Proof. The enclosing-segment comparisons in Definition 9.2 are
exact rational comparisons using
the printed value of $c_1$ and $\rho=10^{-38}$. The following finite
integer prescription gives the derivative table directly from
Definition 2.1.

Put $\sigma=10^{80}$ and enclose a rational $t$ by
$[\lfloor\sigma t\rfloor,\lceil\sigma t\rceil]/\sigma$.
Addition and negation use exact integer endpoints. Use the outward
operations

$$
\begin{aligned}
([L,U]/\sigma)([V,W]/\sigma)
&\subseteq\frac1\sigma\left[
\left\lfloor\frac{\min(LV,LW,UV,UW)}\sigma\right\rfloor,
\left\lceil\frac{\max(LV,LW,UV,UW)}\sigma\right\rceil\right],\\
([L,U]/\sigma)^{-1}
&\subseteq\frac1\sigma\left[
\left\lfloor\frac{\sigma^2}{U}\right\rfloor,
\left\lceil\frac{\sigma^2}{L}\right\rceil\right]
\qquad(LU>0).
\end{aligned}
$$

Attach derivatives $(1,0)$ to the value interval $[2/5,2/5]$ for
$r$, derivatives $(0,1)$ to $I_b$ for $b$, and zero derivatives to
constants. Propagate values and both derivative components by these
interval operations and

$$
D(f+h)=Df+Dh,\qquad D(fh)=hDf+fDh,\qquad
D(f^{-1})=-Df/(ff).
$$

Evaluate Definition 2.1 in its displayed factored order, from left to
right in unparenthesized sums and products. In $\mathcal J$ use
$b^2=bb$ and $r(1-r)$, and evaluate $p=P_pH^{-1}$ and $v=P_vH^{-1}$.
The value interval for $r$ is a singleton, but its derivative vector
still computes both ambient partial derivatives.

The denominator value enclosures, rounded outward to the
$10^{-6}$ grid, are

$$
\widehat D(S_0)\subseteq[1119712,1119713]/10^6,\qquad
H(S_0)\subseteq[45665,45666]/10^6.
$$

They are positive, as is $b$. Also $r(1-r)=6/25>0$, so
$\mathcal J,\mathcal N,T,U$ are positive there. Thus the displayed
circuit and the world lift have no pole on this segment. Rounding
the four derivative intervals outward to the same grid gives the
table. The value and derivative inclusions follow inductively from
the interval operations and the differentiation rules. They cover
the whole segment, including the exact algebraic root, rather than
just a rational approximation to that root.

Finally the derivative signs give the integer bounds

$$
\begin{aligned}
10^{12}\Delta
&\ge17691120\cdot1673536105-725498393\cdot103013505\\
&=-45129404276909865>-45130\cdot10^{12},\\
10^{12}\Delta
&\le17691121\cdot1673536106-725498392\cdot103013504\\
&=-45129401757170742<-45129\cdot10^{12}.
\end{aligned}
$$

This proves the strict determinant separation. ∎

## 10. Local injectivity of the acquired base

**Theorem 10.1 (Motion of the actual M-collision base).** For the
analytic family in Definition 9.1,

$$
\|\beta'(2/5)\|_\infty>18.
$$

After restricting $I$ to a smaller connected open interval about
$2/5$, the map $\beta$ is injective. It therefore gives an analytic
arc of pairwise different acquired children. Every child on this arc
contains the two distinct complete worlds $W_2(\lambda),W_3(\lambda)$
with equal actual terminal-M readings at clock $7$.

Proof. The parameter is the first world's diagonal coordinate, so
its derivative is exactly $1$. At $\lambda _0$, the chain rule gives

$$
\begin{pmatrix}p'\\v'\end{pmatrix}
=D\Phi(2/5,b_{0*})\begin{pmatrix}1\\b_0'\end{pmatrix},
\qquad
v_b p'-p_b v'=p_rv_b-p_bv_r=\Delta.
$$

Lemma 9.3 implies $|\Delta|>45129$ and

$$
|v_b|+|p_b|\le\frac{1673536106+725498393}{10^6}<2400.
$$

Consequently

$$
45129<|\Delta|
\le(|v_b|+|p_b|)\max(|p'|,|v'|)
<2400\|\beta'(2/5)\|_\infty.
$$

Since $45129/2400=15043/800>18$, the asserted bound follows.
At least one component of $\beta'$ is nonzero at $2/5$. Its derivative
is continuous, so it keeps a strict sign on a smaller interval.
That component is strictly monotone there, proving injectivity of
$\beta$. The strict guards and exact equalities in Definition 9.1
hold on this restriction. Distinct base labels give different
acquired readings and hence different children by Definition 1.2.
Every constructed world continues to use its own entire nonzero
polynomial gain and its own fixed drift at all acquired and terminal
clocks. ∎

## 11. The independent J requirement along the arc

**Definition 11.1 (The unchanged independent-pair target).** The target
is the predicate in Definition 1.2: there exist $p\ne24,v$ and
independently selected distinct pairs of complete worlds in the
entire $C(p,v)$, one pair with equal $a$ and one pair with equal $m$.
Overlap between the pairs is allowed. Their two common terminal
values need not agree. Every world's own drift is fixed, and every
world has one nonzero whole real polynomial gain of degree at most
three. Acquired clocks are $0,\ldots,6$ and both terminal alternatives
use clock $7$. Gain zeros, lower degrees, repeated roots, zero drift
and singular companions remain in this domain.

For the arc of Theorem 10.1, the additional sufficient requirement is

$$
\exists\lambda\in I\ \exists W_0,W_1\in C(\beta(\lambda)):
\quad W_0\ne W_1,\quad a(W_0)=a(W_1).
$$

**Proposition 11.2 (Same-base sufficiency and its extent).** Satisfaction
of the additional requirement in Definition 11.1 implies the unchanged
independent-pair target. The inequality
$a(W_2(\lambda))<a(W_3(\lambda))$ rules out just these two selected
worlds as the J pair; it supplies no exclusion of independently
selected J companions.

Proof. At the selected parameter, Theorem 10.1 supplies the distinct
M pair at precisely the base of $W_0,W_1$, and $p(\lambda)\ne24$.
Thus all four complete worlds satisfy Definition 1.2. No relation
between the two common values is needed. An inequality for the two
selected M worlds is not a statement about any other pair. Searching
this arc is a sufficient route; no assertion that every possible
joint witness lies on it is required or established. ∎

**Proposition 11.3 (Necessary analytic candidate condition).** Let
$B,P_J,P_M\in\mathbb Q[p,v]$ be the exceptional and collision
polynomials of [Singular Response Children Exclusion](FIB_SINGULAR_RESPONSE_CHILDREN_EXCLUSION.md),
Definition 11.4, with the whole-child necessary cover of its
Theorem 11.5. Put

$$
h(\lambda)=B(\beta(\lambda))P_J(\beta(\lambda)).
$$

Every actual J collision at a base on this arc satisfies $h(\lambda)=0$.
Either $h\equiv0$ on $I$, or its zeros are isolated and there are
finitely many in every compact subinterval contained in $I$.
Furthermore

$$
B\circ\beta\not\equiv0\quad\Longrightarrow\quad
P_M\circ\beta\equiv0.
$$

Proof. The cited Theorem 11.5 concerns the entire original child,
including its exceptional strata. Its J-collision inclusion gives
$B=0$ or $P_J=0$, which proves the first assertion. The polynomial
compositions are real analytic. The identity theorem on the connected
open interval $I$ says that a nonidentically-zero analytic function
has isolated zeros. Infinitely many zeros in a compact subinterval
would have an accumulation point inside $I$, contradicting that
theorem.

The actual M pair exists at every parameter, so the same necessary
cover gives $(B\circ\beta)(P_M\circ\beta)\equiv0$. If the first
factor is not identically zero, it is nonzero on some open subinterval.
The second factor vanishes there and hence identically on $I$.
This implication is also the exceptional-layer constraint in
[AURIC–Langlands 语境与谱重构理论](AURIC_LANGLANDS_CONTEXT_AND_SPECTRAL_RECONSTRUCTION_THEORY.md),
Section 7, Corollary 7.3.

Nonconstancy of $\beta$ does not imply $h\not\equiv0$: the nonconstant
arc $t\mapsto(t,0)$ lies wholly in the zero set of the nonzero
polynomial $Y$. No value of $B\circ\beta$ or $P_J\circ\beta$ is
established by the determinant bound. Thus this proposition does not
assert a finite global candidate set or actual J feasibility. The
necessary cover gives no converse realization. In particular its
$B=0$ layer retains every exceptional or singular companion; it is
not removed by the regular construction of the selected M pair. The
independent same-base J requirement in Definition 11.1 remains open. ∎

## 追加锚（本行以下为增补区）

## 12. A response rectangle and its entire acquired children

**Definition 12.1 (Exact local rectangle).** Retain every world and
response in Definitions 1.1–1.2. Set $h=10^{-34}$ and

$$
\begin{aligned}
p_c&=1.8057126623901333037270156505198680057908325822025720781026746024314,\\
v_c&=172.2471680963226343182328451692107608678057809948093894185154845004338,\\
\mathcal U&=[p_c-h,p_c+h]\times[v_c-h,v_c+h].
\end{aligned}
$$

Every terminating decimal in Sections 12–18 denotes its exact rational
value. In particular this definition specifies a closed rectangle,
not a rounded algebraic base.

**Theorem 12.2 (Entire-child local J injectivity).** For every
$(p,v)\in\mathcal U$, the entire acquired child $C(p,v)$ contains at
most two complete worlds, and its terminal map $a$ is injective.
The exact base $(p_*,v_*)$ of Theorem 1.3 lies in the interior of
$\mathcal U$. Its child consists exactly of the two M worlds of that
theorem. On a sufficiently small connected open interval about $2/5$,
the analytic arc of Theorem 10.1 also lies in this interior, and each
entire child on the arc consists exactly of its two supplied M worlds.
Thus no distinct J-collision pair exists in any of these children.

The proof occupies Sections 13–17. The complete-world quantifiers
include arbitrary constant real drift, all legal gain zeros, gains
of lower degree, repeated gain roots, and singular or exceptional
sources. No bound on an original positive offdiagonal is assumed.

## 13. Polynomial projection and five regular root intervals

**Definition 13.1 (Inherited elimination interface).** Use exactly
[Common Parent Geometry](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md),
Definitions 12.1, 20.1 and 24.1. In that notation

$$
\begin{gathered}
X=b^2+r-r^2,\quad N=X+br,\quad T=1+b,\quad U=1+2b,\\
D_\Lambda=(b^2+8b+4)XN-2bTU(X+N),\\
\mathsf A=5b(p-24)D_\Lambda+3(8b-1)H(r,b),\qquad
\mathsf B=5bD_\Lambda v-\mathsf N_u(r,b).
\end{gathered}
$$

Here $H$ is precisely that source's sextic (12.2), and
$\mathsf N_u$ is its polynomial (20.1), including the exact division
by $1+b$. Retain the fixed ordered Sylvester identity

$$
\operatorname{Res}_b(\mathsf A,\mathsf B)
=52488000r^{11}(r-1)^9\Psi_2\Psi_4\Phi R(r,p,v),
$$

where

$$
\begin{aligned}
\Psi_2&=4r^2-2r-1,\\
\Psi_4&=625r^4-1000r^3+50r^2+260r+36,\\
\Phi&=438272r^4-931328r^3+540800r^2-50728r-853.
\end{aligned}
$$

The symbol $R$ denotes exactly the degree-eighteen polynomial with
the 668 integer coefficients of that source's Definition 24.1.
Neither its scale nor its sign is changed. Theorem 20.2 there implies
that every actual regular world projects to a zero of
$R\Psi_2\Psi_4\Phi$. This is a necessary implication only. Its fixed
determinant form remains necessary at degree drops; furthermore the
leading $b$ coefficients $5p+216$ and $5v+1125$ are positive on
$\mathcal U$.

**Lemma 13.2 (Uniform finite root inventory).** Put $e=10^{-22}$ and
$I_i=[c_i-e,c_i+e]$ with the following centers. For every
$(p,v)\in\mathcal U$, $R(r,p,v)$ has exactly one simple root in each
$I_i$ and has no other root in $(0,1)$.

| $i$ | $c_i$ | Uniform Bernstein signs |
| --- | --- | --- |
| 1 | $0.4$ | `+++++++++?---------` |
| 2 | $0.6375033978214738667594335994587431421677$ | `---------?+++++++++` |
| 3 | $0.6761493960676857788415044796582458167041$ | `+++++++++?---------` |
| 4 | $0.8634273078193894254581303621214043355746$ | `---------?+++++++++` |
| 5 | $0.9092947326986637649117323875453000752997$ | `+++++++++?---------` |

Proof. Expand the specified integer polynomial at the rational
parameter center:

$$
R(r,p_c+x,v_c+y)=\sum_{i,j,k}A_{ijk}r^ix^jy^k,\qquad
E=\sum_i\sum_{j+k>0}|A_{ijk}|h^{j+k}.
$$

In terms of its integer coefficients $c_{iuv}$, every coefficient is
explicitly

$$
A_{ijk}=\sum_{u\ge j,\,v\ge k}
 c_{iuv}\binom uj\binom vk p_c^{u-j}v_c^{v-k}.
$$

For $[a,b]\subseteq[0,1]$, define

$$
\begin{aligned}
t_\ell&=\sum_{i=\ell}^{18}A_{i00}\binom i\ell
                 a^{i-\ell}(b-a)^\ell,\\
\beta_k&=\sum_{\ell=0}^k t_\ell
                 \frac{\binom k\ell}{\binom{18}\ell},
                 \qquad 0\le k\le18.
\end{aligned}
$$

The degree-eighteen Bernstein coefficients of $r^i$ on such an
interval lie in $[0,1]$: under $r=a+(b-a)t$, the coefficients can
also be written as the averages of products of $i$ entries chosen
from $18-k$ copies of $a$ and $k$ copies of $b$. Hence the full
parameter-dependent coefficient lies in $[\beta_k-E,\beta_k+E]$.
This bound retains all mixed parameter terms.

The finite rational comparisons from these formulas give

$$
\frac{10098}{10^8}<E<\frac{10099}{10^8}.
$$

For additional explicit margins, the following integers $m$ satisfy
$|\beta_k|>mE$ for every indicated sign in the corresponding row.
The coefficient with index nine is omitted only in the five root
rows. The other eighteen coefficients have exactly the displayed
signs.

| Interval | $m$ | Signs |
| --- | ---: | --- |
| $I_1$ | $43180449$ | `+++++++++?---------` |
| $I_2$ | $5746247$ | `---------?+++++++++` |
| $I_3$ | $5696077$ | `+++++++++?---------` |
| $I_4$ | $22570264$ | `---------?+++++++++` |
| $I_5$ | $42371792$ | `+++++++++?---------` |
| $[0,c_1-e]$ | $388624041$ | $+^{19}$ |
| $[c_1+e,c_2-e]$ | $51716227$ | $-^{19}$ |
| $[c_2+e,c_3-e]$ | $51264701$ | $+^{19}$ |
| $[c_3+e,c_4-e]$ | $51264701$ | $-^{19}$ |
| $[c_4+e,c_5-e]$ | $203132376$ | $+^{19}$ |
| $[c_5+e,1]$ | $381346130$ | $-^{19}$ |

These are comparisons of the rational numbers defined above; in
particular every listed margin exceeds $10^4E$. In each root row,
any sign or zero for the middle coefficient leaves variation one.
The endpoint signs are opposite. Substitution
$r=(a+bt)/(1+t)$ and multiplication by $(1+t)^{18}$ turn the
Bernstein coefficients into ordinary coefficients multiplied by
positive binomial factors. Descartes' rule therefore bounds the
number of roots, counting multiplicity, by one. The intermediate
value theorem supplies a root, which is consequently unique and
simple. Every gap row has variation zero and nonzero endpoints.
The five intervals and six gaps cover $[0,1]$. This proves the
inventory uniformly on the entire closed response rectangle. ∎

## 14. Exact lift bounds and terminal J separation

**Definition 14.1 (Coefficient matrix and rational enclosures).** Form
the $12\times13$ matrix $\mathcal M=(L\mid z)$ with ordered rows
$b^5\mathsf A,\ldots,\mathsf A,b^5\mathsf B,\ldots,\mathsf B$ and
ordered columns $b^{12},\ldots,1$. Its first twelve columns form
$L$. For any one of the projection centers $c$ used here or in
Section 15, put $L_0=L(c,p_c,v_c)$ and $C=L_0^{-1}$.

The following explicit centered bounds fix the rational evaluation
of these matrices. For an entry polynomial $f(r,p,v)$, expand

$$
f(c+x,p_c+y,v_c+z)=\sum_{i,j,k}f_{ijk}x^iy^jz^k,
\qquad
\varepsilon_f=\sum_{i+j+k>0}|f_{ijk}|e^ih^{j+k}.
$$

Its value lies in $f_{000}+[-\varepsilon_f,\varepsilon_f]$ on the
whole box. Denote the nonnegative entrywise error matrix by
$\mathcal E_L$ and the analogous last-column vector by
$\mathcal E_z$. Thus a rational upper bound for
$\|I-CL\|_\infty$ is

$$
Q=\max_i\sum_{j=1}^{12}\sum_{k=1}^{12}
                   |C_{ij}|(\mathcal E_L)_{jk}.
$$

For a fixed rational $\bar b$ put
$w=(\bar b^{12},\ldots,\bar b)^t$ and $z_0=z(c,p_c,v_c)$. A rational
residual bound is

$$
\eta=\max_i\left(
 |(C(L_0w+z_0))_i|
 +\sum_{j=1}^{12}|C_{ij}|
       \left\{(\mathcal E_z)_j+
          \sum_{k=1}^{12}(\mathcal E_L)_{jk}|w_k|\right\}\right).
$$

All coefficient expansions in this definition are finite binomial
expansions of the polynomials of Definition 13.1. The inverse is
exactly $\operatorname{adj}(L_0)/\det L_0$, not a rounded inverse.

**Lemma 14.2 (Five necessary lifts).** Each center matrix in the
following table is nonsingular. With $Q,\eta$ as just defined, the
table gives strict rational upper bounds on $Q$ and
$\eta/(1-Q)$ throughout $I_i\times\mathcal U$.

| $i$ | Exact $\bar b$ | $Q$ upper bound | $\eta/(1-Q)$ upper bound |
| --- | --- | --- | --- |
| 1 | $0.04078295904882838405264306362514449405106$ | $4\cdot10^{-18}$ | $12\cdot10^{-23}$ |
| 2 | $0.04091698421060610059422739287384503573542$ | $2\cdot10^{-18}$ | $43\cdot10^{-24}$ |
| 3 | $-3.176868004886463132107916325401810483894$ | $25\cdot10^{-10}$ | $309\cdot10^{-6}$ |
| 4 | $-0.4358328034096036222134460606876310285942$ | $2\cdot10^{-15}$ | $43\cdot10^{-19}$ |
| 5 | $-0.5819863165350697596394747517356607978584$ | $8\cdot10^{-15}$ | $128\cdot10^{-18}$ |

Every actual finite common root in the corresponding box therefore
has respectively the following necessary $b$ enclosure:

$$
\begin{array}{c|c}
i&b\\\hline
1&(0.0407829590488283,0.0407829590488285)\\
2&(0.0409169842106060,0.0409169842106062)\\
3&(-3.178,-3.176)\\
4&(-0.436,-0.435)\\
5&(-0.583,-0.581).
\end{array}
$$

Proof. The exact determinant comparisons at the five rational
centers are

$$
10^{k_i}\le-\det L_0<10^{k_i+1},\qquad
(k_1,k_2,k_3,k_4,k_5)=(32,31,20,26,23).
$$

They follow by expansion of the coefficient matrix, and the
adjugate identity gives $CL_0=I$. Substitution into Definition 14.1
then gives the table's rational inequalities. In particular $Q<1$
on each whole box, so $CL$ and $L$ are invertible there.

For a common root $b$, evaluation of every matrix row gives

$$
L u+z=0,\qquad u=(b^{12},\ldots,b)^t.
$$

Subtract the fixed vector $w$ and multiply by $C$. The geometric
series inverse estimate yields

$$
\|u-w\|_\infty
\le\frac{\|C(Lw+z)\|_\infty}{1-\|I-CL\|_\infty}
\le\frac{\eta}{1-Q}.
$$

The last coordinate gives the displayed enclosures. Rows three
through five violate $b>0$. In each remaining row, Lemma 13.2
permits only one $r$, and invertibility of $L$ permits at most one
$b$. Common Parent Geometry, Theorem 12.3, then gives at most one
complete world at that source. No projected root is being asserted
to have a legal lift. ∎

**Lemma 14.3 (Disjoint terminal J images).** Any actual worlds from
rows one and two respectively satisfy

$$
\begin{array}{c|cc}
 &1&2\\\hline
\widehat D/b^2&(673,674)&(643,644)\\
a&(964,965)&(994,995).
\end{array}
$$

Proof. Evaluate the polynomial circuit of Definition 2.1 on
$I_i$ times the corresponding positive $b$ interval of Lemma 14.2.
Exact interval addition, negation, endpoint multiplication and
reciprocal yield the sharper rational outer bounds

$$
\begin{array}{c|cc}
&1&2\\\hline
\widehat D/b^2&(6732076478185,6732076478186)/10^{10}
 &(6436744834752,6436744834754)/10^{10}\\
a&(9640512711405,9640512711406)/10^{10}
 &(9948201599656,9948201599658)/10^{10}.
\end{array}
$$

The expressions are evaluated in the displayed factored order of
Definition 2.1. Both $b$ and $\widehat D$ are positive throughout
these boxes, so the quotients have no pole. Lemma 2.2 identifies
these values with the literal terminal readings of the same entire
gains and fixed drifts. The two J intervals are disjoint. ∎

## 15. Exceptional projections and the exhaustive singular branch

**Lemma 15.1 (All exceptional projected roots).** The following
centers, with radius $e=10^{-22}$, isolate all the roots of the
indicated factors in $(0,1)$. At any actual common root their forced
$b$ values are as listed.

| Factor | Center | Forced $b$ |
| --- | --- | --- |
| $\Psi_2$ | $0.8090169943749474241022934171828190588602$ | $-1/2$ |
| $\Psi_4$ | $0.8685711315796832210935933386297551290576$ | $-2/5$ |
| $\Phi$ | $0.1348158750676386533670177160610812651109$ | $1/8$ |
| $\Phi$ | $0.9024496817720562653778726512965428561863$ | $1/8$ |

Proof. Use the Sturm sequence $f,f',-\operatorname{rem}(f,f'),\ldots$.
Its exact endpoint sign words are

| Factor or root | At $0$ | At $1$ | At center minus $e$ | At center plus $e$ |
| --- | --- | --- | --- | --- |
| $\Psi_2$ | `--+` | `+++` | `-++` | `+++` |
| $\Psi_4$ | `++--+` | `--+++` | `+--++` | `---++` |
| lower $\Phi$ | `--+-+` | `--+++` | `-+--+` | `++--+` |
| upper $\Phi$ | `--+-+` | `--+++` | `+--++` | `---++` |

The total variation drops are respectively one, one and two, with
one root in each displayed interval. This proves exhaustiveness.
For the four center matrices of Definition 14.1, in the same order,
the determinant comparisons are

$$
10^{k_i}\le-\det L_0<10^{k_i+1},\qquad
(k_1,k_2,k_3,k_4)=(27,26,29,26).
$$

The same centered matrix bounds give $Q<2\cdot10^{-15}$ on each
interval times $\mathcal U$. Thus $L$ is invertible on every
exceptional projection box.

In the notation of Common Parent Geometry, (20.5),
$\det L=\Delta_1=72900r^6(r-1)^4\mathcal L_1$.
Consequently $\mathcal L_1\ne0$ there. Its polynomial identities
(21.4) and the necessary common-root relation (20.10) are

$$
\begin{gathered}
\mathcal L_1b+\mathcal L_0=0,\\
\mathcal L_0-\tfrac12\mathcal L_1\equiv0\pmod{\Psi_2},\qquad
\mathcal L_0-\tfrac25\mathcal L_1\equiv0\pmod{\Psi_4},\\
\mathcal L_0+\tfrac18\mathcal L_1\equiv0\pmod\Phi.
\end{gathered}
$$

They force exactly the listed values. The first two are illegal
because $b>0$. The last two have $b=1/8$ and $\Lambda=0$, by that
source's (4.9), and hence contribute no regular world. ∎

**Lemma 15.2 (No singular world over the rectangle).** No world in
$C(p,v)$ over $\mathcal U$ has $\Lambda=0$.

Proof. The zero-safe parent equation, Common Parent Geometry,
Theorem 12.3, forces $b=1/8$ for every actual singular source.
Its Theorems 4.2 and 29.2 exhaust this branch by the two strict roots
$r_-,r_+$ of $\Phi$. They include every legal fifth-response lift,
with no gain or drift nonvanishing condition. At either root put

$$
\begin{aligned}
j&=1/8+8r(1-r),\qquad n=j+r,\qquad T=9/8,\\
A_5&=1+(n+5/4)(4-15/j+20/T-10/n),\\
a_6&=10-36/j+45/T-20/n,\\
s_r(p)&=24+24(5/2+n)
       +\frac{p-24}{A_5}\{1+(5/2+n)a_6\}.
\end{aligned}
$$

Theorem 29.2 identifies $s_r(p)$ with the actual acquired sixth-M
response of that unique singular fifth-response lift. Exact interval
evaluation on the two $\Phi$ intervals of Lemma 15.1 and the full
$p$ interval gives

$$
\begin{array}{c|cc}
&r_-&r_+\\\hline
A_5&(-908,-907)/10^3&(-5217,-5216)/10^3\\
s_r(p)&(65,67)&(40,42).
\end{array}
$$

All divisions are legitimate; in particular $A_5$ is separated from
zero. Neither sixth-response interval meets
$[v_c-h,v_c+h]\subset(172,173)$. This excludes the exhaustive
singular branch without deleting its world strata. ∎

## 16. The whole-child implication

Proof of the uniform assertion in Theorem 12.2. Let $W$ be any
complete world in any child over $\mathcal U$. If $\Lambda=0$,
Lemma 15.2 excludes it. Otherwise the necessary resultant projection
of Definition 13.1 applies. Since $0<r<1$, its projection is a root
of $R$ or one of the three exceptional factors. Lemma 15.1 excludes
all regular exceptional lifts. Lemmas 13.2 and 14.2 leave only the
first two $R$ projections, with at most one complete world at each.
Thus there are at most two worlds in the entire child.

If two distinct worlds remain, they occupy different rows, and
Lemma 14.3 places their terminal J readings in disjoint intervals.
Thus $a$ is injective. The argument divides by no drift or gain
sample. The only chart division for regular sources is justified by
$\Lambda\ne0$, and the complementary singular case was evaluated
separately. Gain degree drops, repeated gain roots, sampled zeros
and zero drift were never excluded. ∎

## 17. The actual seed and a small analytic M arc

**Lemma 17.1 (Containment of the algebraic seed).** The exact base
$(p_*,v_*)$ of Theorem 1.3 belongs to $\operatorname{int}\mathcal U$.

Proof. Let $c_b=c_1$ be the first rational coordinate of Definition
3.1; it is distinct from the root-interval centers of Lemma 13.2.
Exact rational evaluation of Definition 2.1 at $(2/5,c_b)$ gives

$$
|p(2/5,c_b)-p_c|<10^{-65},\qquad
|v(2/5,c_b)-v_c|<10^{-65}.
$$

Theorem 4.3 supplies $|b_{0*}-c_b|\le10^{-38}$.
The whole segment between them lies in Definition 9.2's $I_b$,
since its printed rational endpoints strictly enclose
$[c_b-10^{-38},c_b+10^{-38}]$. Lemma 9.3 gives on that entire
segment

$$
|p_b|<726,\qquad |v_b|<1674.
$$

These bounds can also be obtained directly by interval
differentiation of Definition 2.1 on $S_0$: the resulting intervals
lie strictly inside
$[725498392,725498393]/10^6$ and
$[-1673536106,-1673536105]/10^6$, respectively. The mean value
theorem therefore yields

$$
\begin{aligned}
|p_*-p_c|&<726\cdot10^{-38}+10^{-65}<10^{-34},\\
|v_*-v_c|&<1674\cdot10^{-38}+10^{-65}<10^{-34}.
\end{aligned}
$$

This proves strict containment for the actual algebraic base,
rather than for its rational approximation. ∎

**Corollary 17.2 (Exact child and locally exhaustive M arc).** The
child $C(p_*,v_*)$ is exactly the two-world set from Theorem 1.3.
There is a connected open interval $I_0$ about $2/5$ on which the
analytic base map $\beta$ of Theorem 10.1 is injective, takes values
in $\operatorname{int}\mathcal U$, and every $C(\beta(\lambda))$
consists exactly of $W_2(\lambda),W_3(\lambda)$. No distinct J pair
exists in any of those entire children.

Proof. Theorem 1.3 supplies two actual distinct worlds at the seed;
Theorem 12.2 bounds the entire child by two. Lemma 17.1 and
continuity of $\beta$ place a sufficiently small open parameter
interval inside the rectangle. Intersect it with the injectivity
interval supplied by Theorem 10.1. The two actual distinct M worlds
persist there and exhaust each child by the same uniform bound.
J injectivity excludes any independently selected J pair there.
This completes all assertions of Theorem 12.2. ∎

## 18. Mathematical sources and the remaining independent-pair question

Sections 12–17 are ordinary model-specific repository-derived
mathematics (`repo-derived`). They add the full-rectangle source
inventory, its entire-child J injectivity, and the exhaustion of the
small M arc. The algebraic seed and its analytic motion are reused
from Sections 2–10. The real analytic family agrees with
[AURIC–Langlands Context and Spectral Reconstruction](AURIC_LANGLANDS_CONTEXT_AND_SPECTRAL_RECONSTRUCTION_THEORY.md),
Section 7; the present conclusion uses only its local branch.

[Common Parent Geometry](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md),
Theorem 12.3, supplies zero-safe fixed-source uniqueness; Sections
20–21 supply the ordered elimination identity, linear minors and
exceptional remainder identities; Definition 24.1 supplies the exact
668-term polynomial; Theorems 4.2 and 29.2 supply the exhaustive
singular branch. The response circuit is Definition 2.1 here, with
the same original-world interpretation established in Lemma 2.2.

Descartes' sign rule, the Bernstein change of basis, Sturm's root
count, the adjugate identity, the geometric-series inverse estimate,
and the intermediate and mean value theorems are classical tools.
For the univariate algebraic methods, see Basu, Pollack and Roy,
*Algorithms in Real Algebraic Geometry*; for ordinary resultant and
subresultant elimination, see Cox, Little and O'Shea, *Ideals,
Varieties, and Algorithms*, Chapter 3. Their use here is the stated
finite rational specialization, not an additional general principle.

The independent J obligation at the particular seed and on this
small arc has a negative answer by Corollary 17.2. The original
existence question remains Definition 1.2 over arbitrary
$p\ne24,v$: the two distinct equal-J worlds and the two distinct
equal-M worlds are independently selected in one entire child,
may overlap, and may have unrelated common terminal values. Each
world retains its own constant real drift and one nonzero whole
real polynomial gain of degree at most three, with acquired clocks
$0,\ldots,6$ and terminal clock $7$.

Any joint witness on a further continuation of this M branch must
have base outside $\mathcal U$. No continuation to such a base is
established here. Neither existence of an unrestricted joint witness
nor its exclusion outside this rectangle follows from this local
absence theorem. No sufficiency of a polynomial necessary cover is
used.

## 追加锚（本行以下为增补区）
