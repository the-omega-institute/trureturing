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


## 9. The entire child at the strict M-pair base

**Definition 9.1 (A full-base rectangle).** Retain the exact worlds $W_2,W_3$ and base $(p_*,v_*)$ of Theorem 1.3. The following terminating decimals are exact rationals:

$$
\begin{aligned}
p_c&=1.8057126623901333037270156505198680057908,\\
v_c&=172.2471680963226343182328451692107608678058,\\
\delta&=10^{-24},\qquad
\mathcal B_*=[p_c-\delta,p_c+\delta]\times[v_c-\delta,v_c+\delta].
\end{aligned}
\tag{9.1}
$$

**Theorem 9.2 (Entire-child inventory and J separation).** One has $(p_*,v_*)\in\mathcal B_*$. For every $(p,v)\in\mathcal B_*$, the entire original child $C(p,v)$ has at most two worlds, and its actual terminal-J response is injective. At the exact M-pair base,

$$
\boxed{C(p_*,v_*)=\{W_2,W_3\}.}
\tag{9.2}
$$

Consequently the independently selected J pair required in Section 8 does not exist at this particular M-pair base. This conclusion concerns the whole original domain over $\mathcal B_*$, with no fixed terminal-M value and no restriction on gain degree, gain samples, drift, singular sources, exceptional sources or source width. It makes no exclusion outside this rectangle.

**Definition 9.3 (The reused unsaturated carrier).** Use exactly $x=n/U$, the tail interpolant, $a_0,a_1,a_2$, $f,\mathcal K,A,B_f,C_f$, and $\alpha,\zeta,F_0,R$ of [Support X, equations (12.8)–(12.12)](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_X.md). In particular

$$
\begin{gathered}
D=x(x+1)(x+2),\\
F_0=405x^3+(975-18p+5v)x^2+(90-36p+5v)x-480,\\
\operatorname{Res}_d(f,\mathcal K)=256D^8F_0^2R,\\
f\mid A^3\mathcal K-(\alpha d+\zeta).
\end{gathered}
\tag{9.3}
$$

The normalization of $R$ is the exact quotient in that source; its $x$-degree is eighteen. Every actual world has $x>0$, satisfies $f=\mathcal K=0$, and therefore satisfies

$$
F_0(x,p,v)R(x,p,v)=0,\qquad \alpha(x,p,v)d+\zeta(x,p,v)=0.
\tag{9.4}
$$

The factor $F_0$ is retained, including its zero-drift possibility. Neither the regular-source denominator nor the fixed-terminal inverse's quartic $K$ is divided out in (9.4).

The all-world necessity is also immediate from the supplied original equations. For the tail interpolant $H=Ug$, clock zero gives $dU=-H_0$, and clock two gives $B_0U=H_2$, where $B_0=294/5-2d-H_2$. These imply $f=0$. Substituting $H_0=-dU$ and $xH_1-(24-d)=rH_1/U$ into $\mathcal K$ expresses it as the cleared original rank-one source relation. This proves $\mathcal K=0$ without division by $d$, so (9.4) applies also when $d=0$ and on singular sources.

**Lemma 9.4 (Uniform exhaustive root rectangles).** Put $\rho=10^{-12}$ and $\sigma=10^{-24}$. In the following table each row specifies the exact Gaussian-rational centre $c=\operatorname{Re}c+i\operatorname{Im}c$. On every real $(p,v)\in\mathcal B_*$, the indicated polynomial has exactly one zero in the rectangle

$$
|\operatorname{Re}(x-c)|\le\rho,\qquad
|\operatorname{Im}(x-c)|\le\rho.
\tag{9.5}
$$

For a real centre this zero is real. Each zero lies in the smaller rectangle with $\rho$ replaced by $\sigma$. The eighteen $R$ rectangles exhaust all its complex roots, and the three $F_0$ rectangles exhaust all its complex roots.

| Polynomial | Index | $\operatorname{Re}c$ | $\operatorname{Im}c$ |
| --- | --- | --- | --- |
| $R$ | 0 | $-4.4456018496430476255084308867226941368478$ | $0$ |
| $R$ | 1 | $-1.3960913833252000635532565337091008407111$ | $0$ |
| $R$ | 2 | $-1.3367773229729508691137384013103149327534$ | $0$ |
| $R$ | 3 | $-1.3317500199574795120070031691555736550906$ | $0$ |
| $R$ | 4 | $-1.1918275779629799043040789640343846279088$ | $0$ |
| $R$ | 5 | $-1.1318389558362942853399530198752644616268$ | $0$ |
| $R$ | 6 | $-1.0946327270963536193480655459922145687844$ | $0$ |
| $R$ | 7 | $-0.3979561498320068203790677829921342455391$ | $0$ |
| $R$ | 8 | $0.3549410397767158302233672842010199020803$ | $0$ |
| $R$ | 9 | $0.4799723815645249004417903320577171426405$ | $0$ |
| $R$ | 10 | $1.2236055502512175044814340191249725198430$ | $0$ |
| $R$ | 11 | $1.4448053440162424804958404016071704680738$ | $0$ |
| $R$ | 12 | $5.8477237005395326611385391944777539159123$ | $0$ |
| $R$ | 13 | $5.8485513508859666460210391010131406006945$ | $0$ |
| $R$ | 14 | $0.6972289686840034189043663693248429197356$ | $-0.1161110933488964046141522395468234074515$ |
| $R$ | 15 | $0.6972289686840034189043663693248429197356$ | $0.1161110933488964046141522395468234074515$ |
| $R$ | 16 | $0.8620293017101553026663874107927443949746$ | $-0.0326900792590044079795851745687301165823$ |
| $R$ | 17 | $0.8620293017101553026663874107927443949746$ | $0.0326900792590044079795851745687301165823$ |
| $F0$ | 0 | $-3.7947042767818410754177515062671600311838$ | $0$ |
| $F0$ | 1 | $-0.9782331943877242154258535040382862156920$ | $0$ |
| $F0$ | 2 | $0.3192757117656374584384742840419988882714$ | $0$ |

Proof. For $\mathscr P\in\{R,F_0\}$ and a displayed centre, form the exact finite expansion

$$
\mathscr P(c+z,p_c+u,v_c+w)=\sum_{\ell,j,k}a_{\ell jk}z^\ell u^j w^k.
\tag{9.6}
$$

For a real rational $q$, define

$$
\operatorname{rnd}_{100}(q)=10^{-100}\lfloor10^{100}q+1/2\rfloor,
$$

and extend it componentwise to Gaussian rationals. Set $\gamma=\operatorname{rnd}_{100}(1/a_{100})$, use $|a+ib|_1=|a|+|b|$, and put $s=\rho$ at real centres and $s=2\rho$ otherwise. The finite rational sums

$$
\begin{aligned}
\eta&=\sum_{j,k}|\gamma a_{0jk}|_1\delta^{j+k},\\
q&=|1-\gamma a_{100}|_1+
\sum_{\substack{\ell\ge1,j,k\ge0\\(\ell,j,k)\ne(1,0,0)}}
\ell|\gamma a_{\ell jk}|_1s^{\ell-1}\delta^{j+k}
\end{aligned}
\tag{9.7}
$$

satisfy, at every one of the twenty-one centres,

$$
\eta<2\cdot10^{-25},\qquad q<3\cdot10^{-9},\qquad
\eta+q\rho<\rho,\qquad \frac{\eta}{1-q}<\sigma.
\tag{9.8}
$$

These are rational inequalities obtained from (9.3), (9.6) and the printed centres. The coefficient of $x^{18}$ in $R$ is uniformly enclosed by

$$
1873044541936855184250
\le[x^{18}]R\le1873044541936855184251,
\tag{9.9}
$$

and the leading coefficient of $F_0$ is $405$.

For fixed real $(p,v)\in\mathcal B_*$, apply the map $x\mapsto x-\gamma\mathscr P(x,p,v)$ to the real interval $[c-\rho,c+\rho]$ when $c$ is real, and to the rectangle (9.5) otherwise. In each case (9.7) bounds its centre displacement and its derivative's induced maximum norm, so (9.8) makes it a contraction into the interior. For a complex rectangle, $|z|_1\le2\rho$ explains the value of $s$; complex multiplication has maximum-norm operator bound $|\cdot|_1$. The contraction argument of Theorem 4.3 therefore gives one zero in each specified set, real at every real centre, with displacement at most $\eta/(1-q)$.

All eighteen $R$ rectangles are pairwise disjoint, as are the three $F_0$ rectangles: for every two relevant centres, at least one coordinate differs by more than $2\rho$. Since the degrees remain eighteen and three by (9.9), these distinct zeros exhaust the roots and give exactly one complex zero in each rectangle, including those with real centres. In particular this conclusion is not inferred from an incomplete list of numerical roots. ∎

**Lemma 9.5 (Whole-source filters and separated J answers).** Over $\mathcal B_*$, only the $R$ roots with indices 12 and 13 can represent original worlds. Each determines at most one entire world. The possible terminal-J values at these two roots satisfy

$$
\begin{aligned}
994.82015996&\le a_{12}\le994.82015997,\\
964.05127114&\le a_{13}\le964.05127115,\\
-30.76889&\le a_{13}-a_{12}\le-30.76888<0.
\end{aligned}
\tag{9.10}
$$

Proof. The first eight $R$ rectangles and first two $F_0$ rectangles have negative real roots. The last four $R$ rectangles are nonreal, since their imaginary coordinate intervals exclude zero. The remaining seven real roots have positive $x$.

At every one of these positive-root boxes, evaluation gives the uniform pole separations

$$
|\alpha|>10^{14},\qquad \chi>40,\qquad
|H_1|>1/25,\qquad |U|>1/10.
\tag{9.11}
$$

Here, with $d=-\zeta/\alpha$, use exactly the zero-safe inverse of Support X, (12.8)–(12.9):

$$
\begin{gathered}
h_3=(24-d)/x,\quad h_4=18-d,\quad
h_5=(p-d)/(x+1),\quad h_6=(v-d)/(x+2),\\
H_0=20h_3-45h_4+36h_5-10h_6,\\
H_1=10h_3-20h_4+15h_5-4h_6,\\
H_2=4h_3-6h_4+4h_5-h_6,\quad
H_7=-h_3+4h_4-6h_5+4h_6,\\
B_0=294/5-2d-H_2,\qquad \chi=d^2+B_0^2,\\
U=(-dH_0+B_0H_2)/\chi,\quad b=(U-1)/2,\\
j=U(24-d)/H_1,\qquad r=xU-j,\\
a=d+\left(\frac{1+1/U}{2}+2x+\frac{2r}{U}\right)H_7.
\end{gathered}
\tag{9.12}
$$

The last expression is the actual terminal J response because $H_7=Ug(7)$. In particular it uses the same whole gain as the acquired rows.

All following endpoints are exact rationals and enclose the entire smaller root boxes of Lemma 9.4, uniformly over $\mathcal B_*$. The strict source tests eliminate every positive candidate except indices 12 and 13:

| Polynomial | Index | $b$ enclosure | $r$ enclosure | Source test |
| --- | --- | --- | --- | --- |
| $R$ | 8 | $[27.49075770,27.49075771]$ | $[34.55368867,34.55368868]$ | r>1 |
| $R$ | 9 | $[-3.17686801,-3.17686800]$ | $[0.67614939,0.67614940]$ | b<0 |
| $R$ | 10 | $[-0.43583281,-0.43583280]$ | $[0.86342730,0.86342731]$ | b<0 |
| $R$ | 11 | $[-0.55207424,-0.55207423]$ | $[-0.29745094,-0.29745093]$ | b<0 |
| $R$ | 12 | $[0.04091698,0.04091699]$ | $[0.63750339,0.63750340]$ | retained |
| $R$ | 13 | $[0.04078295,0.04078296]$ | $[0.39999999,0.40000001]$ | retained |
| $F0$ | 2 | $[-1.45169779,-1.45169778]$ | $[-0.21103470,-0.21103469]$ | b<0 |

For explicit finite interval evaluation of (9.11)–(9.12), use the endpoint operations of Definition 4.1 with grid denominator $10^{120}$. For $\alpha$ and $\zeta$, first enclose their centre values and apply

$$
P(y)\in P(y_c)+\sum_{k=1}^3(y_k-y_{c,k})\,\partial_kP(Y),
\quad
Y=[c-\sigma,c+\sigma]\times\mathcal B_*,\quad
 y_c=(c,p_c,v_c).
\tag{9.13}
$$

Evaluate each polynomial by multivariate Horner evaluation in the variable order $x,p,v$, with coefficients accumulated in decreasing power order. Formula (9.13) follows from the fundamental theorem of calculus on the convex box and retains the dependence needed for these enclosures. Then evaluate the displayed rational inverse in its factored order. The nonzero lower bounds in (9.11), together with $x>0$, permit every reciprocal. This gives the table and (9.10) by outward rational interval operations.

Every actual endpoint satisfies (9.4). Thus $\alpha\ne0$ fixes its drift at its root, including the retained $F_0$ branch. The four tail samples then fix its entire polynomial $H$, and (9.12) fixes $U,b,r$ and $g=H/U$. Hence there is at most one entire original world at each retained root, with no extra drift branch at any candidate root. ∎

Proof of Theorem 9.2. Evaluate the first-source circuit of Definition 2.1 on the originally defining box $X$ of Section 3. The resulting inclusions give

$$
|p(2/5,b_0)-p_c|<10^{-30},\qquad
|v(2/5,b_0)-v_c|<10^{-30}
\quad\text{throughout }X.
\tag{9.14}
$$

Therefore the exact $(p_*,v_*)$ lies in $\mathcal B_*$. This assertion concerns the exact root of Section 4, rather than a rounded replacement base.

For any $(p,v)\in\mathcal B_*$ one has $p\ne24$. Every complete original world in its entire child supplies an $x>0$ satisfying (9.4), regardless of its terminal-M response. Lemmas 9.4–9.5 leave only two root slots, each representing at most one whole world, and their actual J values are disjoint by (9.10). Thus $|C(p,v)|\le2$ and the terminal J map is injective on the whole child.

At $(p_*,v_*)$, Theorem 1.3 already supplies the two distinct entire worlds $W_2,W_3$. The upper bound proves (9.2). Their diagonal intervals identify $W_2$ with slot 13 and $W_3$ with slot 12. Consequently no independently chosen equal-J pair can be supplied by any other companion at that base. ∎

The new `repo-derived` content is the full-base root cover, its guarded two-slot inventory and J separation on $\mathcal B_*$. The parent, literal response circuit, zero-safe inverse and carrier identities are reused with their original assumptions. Fixed-node interpolation and the contraction argument are the classical tools already cited in Section 7. The proof neither applies the seven-world bound with a free M response nor prescribes a common M response for the inventory.

This strengthens the selected-pair statement of Section 8 to an entire-child exclusion at its particular exact base. The unrestricted independent-pair question still has both $p\ne24$ and $v$ free outside $\mathcal B_*$. The longer-history reconstruction of [the literal cubic matrix-polynomial frame](FIB_LITERAL_CLOCK_CUBIC_MATRIX_POLYNOMIAL_FRAME.md), Problem 6.5, does not settle that remaining same-seven-read incidence.

## 追加锚（本行以下为增补区）
