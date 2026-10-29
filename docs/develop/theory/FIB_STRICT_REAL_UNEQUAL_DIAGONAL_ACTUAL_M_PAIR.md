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
## 19. The full parent and the two coordinate descriptions

**Definition 19.1 (Boundary coordinates).** Retain the entire original
world domain and independent pair predicate of Definitions 1.1–1.2.
The rectangle $\mathcal U$, center $q_c=(p_c,v_c)$ and $h=10^{-34}$
remain Definition 12.1. In the additions use $\mathcal R=(p,v)$ for
the regular-source map of Definition 2.1; denote Definition 13.1's
exceptional quartic $\Phi$ by $\varphi_{\rm sing}$. Thus response-map
and exceptional-polynomial symbols are distinct. Retain $H=b\widehat D$
for the circuit denominator. On the full strict source domain put

$$
\begin{gathered}
c_{\rm src}=r(1-r)/b,\quad j=b+c_{\rm src},\quad n=j+r,\quad
T=1+b,\quad U=1+2b,\quad V=U+n,\quad\epsilon=d-24,\\
\Lambda=1+6/T+1/U-4/j-4/n,\qquad
B_{\rm par}=6/T-2/U=2(2+5b)/(TU)>0,\\
F_{\rm par}=\epsilon\Lambda+(24/5)(b-1/8)B_{\rm par}.
\end{gathered}
\tag{19.1}
$$

[Common Parent Geometry](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md),
Theorem 2.1, gives the bijection between the full five-row parent and
$0<r<1,b>0,F_{\rm par}=0$. The entire gain is the unique polynomial
of degree at most three with samples

$$
(g_0,g_1,g_2,g_3)=(-24-\epsilon,-\epsilon/j,
                         (27/5-\epsilon)/T,-\epsilon/n).
\tag{19.2}
$$

For the boundary calculations use the literal fifth and sixth responses

$$
\begin{aligned}
K_5&=V(96-108/T),&A_5&=1+V(4-15/j+20/T-10/n),\\
K_6&=(2U+n)(240-243/T),&
A_6&=1+(2U+n)(10-36/j+45/T-20/n),\\
P_5&=24+K_5+\epsilon A_5,&P_6&=24+K_6+\epsilon A_6.
\end{aligned}
\tag{19.3}
$$

These follow from Lemma 2.2's extrapolation weights. On actual worlds
$P_5=p,P_6=v$; eliminating $\epsilon$ where $\Lambda\ne0$ gives
$\mathcal R$. Common Parent Geometry, Lemma 12.2 and Theorem 12.3,
give $\Lambda^2+A_5^2>0$ on every strict source and unique whole-world
lifting at fixed source and fifth response, including $\Lambda=0$.
These premises are reused, together with the complete regular,
exceptional and singular inventory of Sections 13–16. They impose
no bound on positive offdiagonals, no nonzero drift or gain sample,
no exact degree and no simple gain roots. Every world keeps one fixed
drift and one whole nonzero real gain. The unequal first two readings
exclude only the identically zero gain.

## 20. Bounded responses bound drift and gain

**Lemma 20.1.** If $P_5$ ranges in a bounded interval over the parent,
then $d$ and all four coefficients of $g$ are uniformly bounded.

**Proof.** Suppose instead that $|\epsilon|\to\infty$ along a
sequence with bounded $P_5$. Take subsequences of $r\in[0,1]$ and
$b\in[0,\infty]$.

If $b\to\infty$, then $j,n\ge b$, $\Lambda\to1$ and
$(24/5)(b-1/8)B_{\rm par}\to24$. Equation $F_{\rm par}=0$ forces
$\epsilon\to-24$, a contradiction.

If $b\to b_0\in(0,\infty)$, all source coefficients have finite
limits. Equations (19.1) and (19.3) would force $\Lambda,A_5\to0$.
The strict-source inequality in Definition 19.1 excludes an interior limiting $r$. At the endpoints their
limits are
$$
\begin{array}{c|cc}
r&\Lambda&A_5\\\hline
0&2(b^3-8b-4)/(b(b+1)(2b+1))
 &(12b^3+2b^2-75b-25)/(b(b+1))\\
1&2(b^3-4b-2)/(b(b+1)(2b+1))
 &2(6b^3+3b^2-23b-15)/(b(b+1)).
\end{array}
\tag{20.1}
$$
The resultants of these numerator pairs, including their displayed
constant factors, are $-186152$ and $-8896$. Neither pair vanishes
simultaneously.

If $b\to0$, pass to a limit of $j$ in $[0,\infty]$. For
$j\to\infty$, $n/j\to1$ and $\Lambda\to8$, forcing
$\epsilon\to3/10$. For $j\to0$, $\Lambda\to-\infty$ and
$\epsilon\to0$. For $j\to z\in(0,\infty)$,
$r(1-r)=b(j-b)$ implies $r\to0$ or $1$. The limiting pairs are
$$
\begin{array}{c|cc}
r&\Lambda&A_5\\\hline
0&8(z-1)/z&(24z^2-25)/z\\
1&4(2z^2-1)/(z(z+1))&2(12z^3+24z^2-8z-15)/(z(z+1)).
\end{array}
\tag{20.2}
$$
Their numerator resultants are $-64,14336$. Again simultaneous
vanishing is impossible. These cases exhaust a hypothetical divergent
drift sequence, so the drift is bounded.

For gain coefficients, let $q$ be the quadratic interpolating
$$
q(0)=-d,\qquad q(2)=(147/5-d)/T,\qquad q(4)=(18-d)/U.
$$
Its coefficients are bounded because $T,U\ge1$. Write
$g(s)=q(s)+\kappa s(s-2)(s-4)$. The equal odd readings give
$jg(1)=ng(3)$, hence
$$
\kappa=\frac{nq(3)-jq(1)}{3(j+n)},\qquad
|\kappa|\le\frac13\max(|q(1)|,|q(3)|).
\tag{20.3}
$$
The strictly positive sum $j+n$ permits this estimate even along
sequences where both odd traces vanish. Every coefficient of $g$ is
therefore bounded. ∎

## 21. Exhaustive finite escape responses

Define the following rational curves, omitting poles:
$$
\begin{aligned}
R_0(z)&=\left(\frac{-3(72z^3+746z^2+465z+130)}{5(z^3-8z-4)},
\frac{-3(375z^3+4431z^2+2486z+344)}{5(z^3-8z-4)}\right),\\
R_1(z)&=\left(\frac{-6(36z^4+61z^3+221z^2+181z+30)}{5(z+1)(z^3-4z-2)},
\frac{-3(375z^4+881z^3+2486z^2+1706z+266)}{5(z+1)(z^3-4z-2)}\right),\\
\mathcal B_0(z)&=\left(\frac{-3(16z^2-80z+65)}{10(z-1)},
\frac{3(45z^2+125z-172)}{10(z-1)}\right),\\
\mathcal B_1(z)&=\left(\frac{-6(8z^3-24z^2-2z+15)}{5(2z^2-1)},
\frac{3(45z^3+215z^2-33z-133)}{5(2z^2-1)}\right).
\end{aligned}
\tag{21.1}
$$
Use $z>0$ for $R_i$ and $z\ge0$ for $\mathcal B_i$. Also put
$q_\infty=(-216/5,-225)$.

**Theorem 21.1.** A parent sequence with finite limiting responses and
no subsequence converging to a strict parent world has, after a
subsequence, a limiting response on one of (21.1) or at $q_\infty$.

**Proof.** Lemma 20.1 bounds drift and all gain coefficients. If
$b\to b_0>0$ is finite and $r$ has an interior limit, the source,
drift and gain have a strict parent limit. Its gain is nonzero by the
unequal first two readings. The remaining limits with such $b_0$
have $r\to0$ or $1$. A zero limiting $\Lambda$ would force
$b_0=1/8$ by $F_{\rm par}=0$, but the cubics in (20.1) are nonzero there.
Solving for $\epsilon$ and substituting in (19.3) gives exactly
$R_0(b_0),R_1(b_0)$.

If $b\to\infty$, then $d\to0$. Use the scaled polynomial
$g_{\rm sc}=Ug$. Its samples at nodes $1,2,3,4$ converge to
$(48,294/5,48,18)$, since $j/U,n/U,T/U\to1/2$.
Fixed-node interpolation gives $g_{\rm sc}(5)\to-144/5$,
$g_{\rm sc}(6)\to-90$. Since $V/U\to3/2$ and $(2U+n)/U\to5/2$,
the limiting response is $q_\infty$. This argument scales the whole
gain and does not assume its unscaled coefficients vanish at a rate.

If $b\to0,j\to\infty$, then $d\to243/10$ and the samples
(19.2) give $g(5)\to-24/5$. Since $V\to\infty$, bounded $P_5$
is impossible. Otherwise let $j\to z\ge0$; then $r\to0$ or $1$.
For $z>0$, (20.2) gives respectively
$$
\epsilon\to\frac{3z}{10(z-1)},\qquad
\epsilon\to\frac{3z(z+1)}{5(2z^2-1)}.
$$
The poles are excluded by bounded drift. Substitution gives $\mathcal B_0(z)$
or $\mathcal B_1(z)$.

At $z=0$ one must retain the rates of vanishing traces. If $r\to0$,
$$
0\le r/j\le b/(1-r)\to0,\quad n/j\to1,\quad
\Lambda j\to-8,\quad\epsilon/j\to-3/10.
$$
If $r\to1$, then $n\to1$, $\Lambda j\to-4$ and
$\epsilon/j\to-3/5$. Equation (19.2) and the extrapolation weights of Lemma 2.2, without division by
a limiting zero, give respectively
$$
(39/2,258/5)=\mathcal B_0(0),\qquad(18,399/5)=\mathcal B_1(0).
$$
These cases exhaust all escaping source sequences. ∎

## 22. A closed barrier and a proper map

The primitive integer implicit polynomials of (21.1), with positive
lexicographic leading coefficient in $p,v$, are
$$
\begin{aligned}
E_0={}&51072900p^3-38068700p^2v-1933224270p^2+8423500pv^2
+601454235pv+10167680250p\\
&-581725v^3-45839880v^2-1393526691v+136430551152,\\
E_1={}&1055100p^4-1141850p^3v-116130990p^3+416900p^2v^2
+79145580p^2v+273455568p^2\\
&-63500pv^3-17883810pv^2-175084740pv-9069191838p
+3475v^4+1327830v^3+23513292v^2\\
&+2292881202v-50360535,\\
E_2={}&9000p^2-1300pv-175350p-1600v^2+225120v-6050961,\\
E_3={}&5356125p^3-471600p^2v-197333550p^2-592800pv^2
+93450960pv-635417028p\\
&+89600v^3-8052480v^2-277806240v+17962000344.
\end{aligned}
\tag{22.1}
$$
More precisely, write each coordinate in (21.1) as its displayed
numerator over denominator and take the primitive positive-leading
part of $\operatorname{Res}_z(N_p-pD_p,N_v-vD_v)$.
Expanding the Sylvester determinant gives (22.1). Direct substitution
and clearing denominators also give $E_i(R_i)=0$ or $E_i(\mathcal B_{i-2})=0$.
These are polynomial identities, not converse realization assertions.

Put
$$
\begin{gathered}
\mathcal E_{\rm esc}=E_0E_1E_2E_3\{(5p+216)^2+(v+225)^2\},\\
O=\{(p,v)\in\mathbb R^2:p\ne24,\ \mathcal E_{\rm esc}(p,v)\ne0\},\\
\mathcal S=\{(r,b,\epsilon):0<r<1,b>0,F_{\rm par}=0,P_5\ne24\},
\quad \mathscr A=(P_5,P_6),\quad\mathcal S_O=\mathscr A^{-1}(O).
\end{gathered}
\tag{22.2}
$$

**Theorem 22.1.** The full-world response map
$\mathscr A:\mathcal S_O\to O$ is proper.

**Proof.** Take a sequence over a compact subset of $O$ and a
subsequence whose labels converge in that compact subset. Its fifth
responses are bounded. If there were no strict parent convergent
subsequence, Theorem 21.1 would put its limiting label in $\mathcal E_{\rm esc}=0$,
a contradiction. A strict limit satisfies all rows and still has
$P_5\ne24,\mathcal E_{\rm esc}\ne0$. It belongs to $\mathcal S_O$. Sequential
compactness proves compactness of the inverse image. This is
properness relative to $O$, not properness over the whole plane. ∎

## 23. Source-surface regularity and response critical values

**Theorem 23.1 (The parent surface and its regular response covering).**
The surface $\mathcal S$ of (22.2) is smooth and real analytic. Define

$$
H_{\rm reg}=\det\frac{\partial(F_{\rm par},P_5,P_6)}
 {\partial(r,b,\epsilon)},\qquad
D_{\rm crit}=\mathscr A(\{s\in\mathcal S_O:H_{\rm reg}(s)=0\}).
\tag{23.1}
$$

Then $D_{\rm crit}$ is closed relative to $O$. For every connected
component $\Omega$ of $O\setminus D_{\rm crit}$ with nonempty inverse
image, $\mathscr A:\mathscr A^{-1}(\Omega)\to\Omega$ is a finite
covering with constant positive fiber cardinality. Continuous paths
lift uniquely from a specified initial world; analytic paths have
analytic lifts.

**Proof.** Where $\Lambda\ne0$, $(F_{\rm par})_\epsilon\ne0$.
Where $\Lambda=0$, (19.1) forces $b=1/8$. The exhaustive singular
roots cited in Section 15 satisfy
$\Lambda=\varphi_{\rm sing}/(960jn)$ at that width. They are simple:
at fixed $b$, $j''=n''=-2/b$ gives

$$
(1/j)''=2(j')^2/j^3+2/(bj^2)>0,\qquad
(1/n)''=2(n')^2/n^3+2/(bn^2)>0.
$$

Hence $\Lambda''<0$. The inherited opposite signs at the two root
isolations put positive values between the roots; concavity forces
strictly positive derivative at the lower root and strictly negative
derivative at the upper one. Thus $\Lambda_r\ne0$. At $b=1/8$,
$K_5=0$, so $P_5\ne24$ implies $\epsilon\ne0$ and
$(F_{\rm par})_r=\epsilon\Lambda_r\ne0$. This proves smoothness
including every allowed singular source. Smoothness of this surface
is distinct from regularity of the response differential: adjoining
$dF_{\rm par}$ to $dP_5,dP_6$ proves that $H_{\rm reg}\ne0$ is
exactly invertibility of the response map on the tangent plane.

A convergent sequence of critical labels inside $O$ has a convergent
subsequence of critical preimages by Theorem 22.1. Its strict limit
is still critical, proving relative closedness. Apply the classical
proper local diffeomorphism covering argument to this particular map.
Each regular fiber is discrete and compact, hence finite. Choose
disjoint inverse neighborhoods at its finitely many points. Additional
preimages at arbitrarily nearby labels would, by properness, have a
subsequential limit in that same fiber, a contradiction. A smaller
neighborhood is evenly covered. The image is open by local inversion
and closed by properness, so it is the whole connected component.
Cardinality is locally constant and therefore constant. Inverse charts
give unique lifts; properness prevents termination at an interior path
time. Analytic inverse charts give analytic lifts. ∎

## 24. Two source boxes and the complete-state coordinates

**Definition 24.1 (Local domains, coordinates and norms).** Put

$$
\begin{gathered}
\mathcal V=q_c+(-2h,2h)^2,\qquad t_x=10^{-30},\\
z_1=(0.4,\;0.04078295904882838405264306362514449405106),\\
z_2=(0.6375033978214738667594335994587431421677,\;
0.04091698421060610059422739287384503573542),\qquad
B_i=z_i+[-t_x,t_x]^2.
\end{gathered}
\tag{24.1}
$$

Every terminating decimal in Sections 19 onward denotes an exact
rational. Vector norms are unweighted infinity norms. Matrix infinity
norms are induced norms, the largest absolute row sum. Scalar derivative
row norms are absolute coefficient sums; maximum-entry bounds are
identified separately. Use Definition 2.1's circuit, and put
$u_i=\widehat C_i/\widehat D$ for $0\le i\le3$. Its monomial gain
coefficients and complete state are

$$
\begin{aligned}
\alpha_0&=u_0,&\alpha_1&=(-11u_0+18u_1-9u_2+2u_3)/6,\\
\alpha_2&=(2u_0-5u_1+4u_2-u_3)/2,&
\alpha_3&=(-u_0+3u_1-3u_2+u_3)/6,\\
g(s)&=\sum_{k=0}^3\alpha_ks^k,&
\Theta&=(r,b,c_{\rm src},d,\alpha_0,\alpha_1,\alpha_2,\alpha_3).
\end{aligned}
\tag{24.2}
$$

These are coefficients of the same cardinal interpolant of Lemma 2.2.
The state norm uses all eight displayed coordinates without weights.
Only $p,v$ vary; all five earlier rows, literal clocks and actions
remain exact. The open $\mathcal V$ supplies analytic neighborhoods;
entire-child and error statements below use the closed $\mathcal U$
unless explicitly given a different domain.

## 25. Finite rational differential inequalities

**Lemma 25.1.** On each $B_i$, $0<r<1$, $b>0$ and

$$
1<\widehat D<6/5,\quad .04<H<.05,\quad .23<\mathcal J<.25,\quad .25<\mathcal N<.27.
$$

With derivative columns $(r,b)$, the entries of $D\mathcal R$ lie strictly
between the following endpoints, all divided by $10^6$:

| Box | $p_r$ | $p_b$ | $v_r$ | $v_b$ |
| --- | --- | --- | --- | --- |
| $B_1$ | $[-17691121,-17691120]$ | $[725498392,725498393]$ | $[103013504,103013505]$ | $[-1673536106,-1673536105]$ |
| $B_2$ | $[16740247,16740248]$ | $[705190458,705190459]$ | $[-101110471,-101110470]$ | $[-1568667529,-1568667528]$ |

The determinants lie respectively in
$(-45129404,-45129403)/10^3$ and
$(45042256,45042257)/10^3$.
Let

$$
K_1=\begin{pmatrix}
.037083053954745515&.016075957923158333\\
.002282624997885133&.000392008731375771
\end{pmatrix},\quad
K_2=\begin{pmatrix}
-.034826575389614269&-.015656197514671509\\
.002244791436258976&.000371656511668806
\end{pmatrix}.
$$

Then $\|K_i\|_\infty<.054$ and
$\sup_{B_i}\|(D\mathcal R)^{-1}\|_\infty<.054$. More precisely,

| Box | $\sup\|I-K_iD\mathcal R\|_\infty$ less than | $\|K_i(\mathcal R(z_i)-q_c)\|_\infty$ less than |
| --- | --- | --- |
| $B_1$ | $9.101\cdot10^{-16}$ | $2.511\cdot10^{-42}$ |
| $B_2$ | $2.778\cdot10^{-16}$ | $2.862\cdot10^{-41}$ |

The absolute row sums of $D\Theta(D\mathcal R)^{-1}$ are strictly less
than the following constants:

| Coordinate | $B_1$ | $B_2$ |
| --- | ---: | ---: |
| $r$ | $.053160$ | $.050483$ |
| $b$ | $.002675$ | $.002617$ |
| $c_{\rm src}$ | $.169790$ | $.129707$ |
| $d$ | $.006671$ | $.006985$ |
| $\alpha_0$ | $.006671$ | $.006985$ |
| $\alpha_1$ | $.001773$ | $.000856$ |
| $\alpha_2$ | $.006916$ | $.007510$ |
| $\alpha_3$ | $.002279$ | $.002353$ |

For $G_a=Da(D\mathcal R)^{-1}$ and $G_m=Dm(D\mathcal R)^{-1}$ the component
intervals below, divided by $10^{12}$, enclose their values:

| Box | $(G_a)_p$ | $(G_a)_v$ |
| --- | --- | --- |
| $B_1$ | $[-3670060067454,-3670060067453]$ | $[8059538465730,8059538465731]$ |
| $B_2$ | $[-12809349369649,-12809349369648]$ | $[3979838493604,3979838493605]$ |

| Box | $(G_m)_p$ | $(G_m)_v$ |
| --- | --- | --- |
| $B_1$ | $[-7215988701689,-7215988701688]$ | $[6191296762938,6191296762939]$ |
| $B_2$ | $[-7216195354246,-7216195354245]$ | $[6191297749276,6191297749277]$ |

In particular their induced row norms are less than seventeen and
fourteen, respectively.

**Proof by finite rational inclusions.** Here are exact finite
arithmetic definitions for the inequalities, including correlations
needed for the small preconditioned residual. Put $\sigma=10^{110}$.
Encode $x\in\mathbb Q$ by
$[\lfloor\sigma x\rfloor,\lceil\sigma x\rceil]/\sigma$.
Negation and addition use exact endpoint operations. For two grid
intervals use

$$
\begin{aligned}
([L,U]/\sigma)([V,W]/\sigma)&\subseteq
[\lfloor\min(LV,LW,UV,UW)/\sigma\rfloor,
\lceil\max(LV,LW,UV,UW)/\sigma\rceil]/\sigma,\\
([L,U]/\sigma)^{-1}&\subseteq
[\lfloor\sigma^2/U\rfloor,\lceil\sigma^2/L\rceil]/\sigma
\quad(LU>0).
\end{aligned}
$$

Attach derivatives $(1,0)$ to $r$, $(0,1)$ to $b$, and zero to
constants. Addition and multiplication use their differentiation
rules; reciprocal uses $D(f^{-1})=-Df/(ff)$ with interval operations.
Evaluate Definition 2.1, then (24.2), in
that order, left to right within sums and products. Squares are
products. Each operation preserves inclusion, so this gives bounds
on entire boxes and their derivatives.

Retaining all grid digits, form $A=D\mathcal R$,
$\delta=A_{11}A_{22}-A_{12}A_{21}$ and

$$
A^{-1}=\delta^{-1}
\begin{pmatrix}A_{22}&-A_{12}\\-A_{21}&A_{11}\end{pmatrix}.
$$

Finite endpoint comparisons give the guard intervals, derivative and
determinant intervals above. Multiplication by the exact $K_i$, before
rounding to the printed derivative grid, gives the two strict
preconditioned bounds. Singleton center evaluation gives the two
residual bounds. Finally multiply the coordinate and terminal derivative
rows by this inverse and sum their maximum absolute endpoints. These
sums are less than the printed coordinate constants; terminal endpoints
lie within the printed grid intervals. For example the source-$c_{\rm src}$
row sums are less than $.169789052$ and $.129706357$, and the drift
row sums less than $.006670211$ and $.006984248$. All comparisons are
rational integer floor/ceiling comparisons under the formulas above.
Thus the tables express full-box inclusions, with no sampling or
floating-point error assumption. ∎

## 26. Actual inverse roots and quantitative recovery

**Theorem 26.1.** Each $q\in\mathcal V$ has exactly one inverse
$x_i(q)\in B_i$ under $\mathcal R$. It is interior and real analytic, with

$$
\|x_i(q)-z_i\|_\infty<1.1\cdot10^{-35}.
$$

The constructed worlds $W_i(q)$ are lawful members of $C(q)$. On the
closed rectangle the complete statement is

$$
C(q)=\{W_1(q),W_2(q)\},\quad W_1(q)\ne W_2(q),
\qquad q\in\mathcal U.
$$

The labels are the disjoint source boxes, equivalently increasing $r$.
For $q,q'\in\mathcal U$ and $\varepsilon=\|q-q'\|_\infty$,

$$
\begin{gathered}
\|x_i(q)-x_i(q')\|_\infty\le .054\varepsilon,\qquad
\|\Theta_i(q)-\Theta_i(q')\|_\infty\le .17\varepsilon,\\
|d_i(q)-d_i(q')|\le .007\varepsilon,\qquad
\|\alpha_i(q)-\alpha_i(q')\|_\infty\le .008\varepsilon,\\
\max_{k,l}|(P_i(q)-P_i(q'))_{kl}|\le .17\varepsilon,\qquad
\|P_i(q)-P_i(q')\|_\infty\le .223\varepsilon,\\
\sup_{0\le s\le7}|g_i(q;s)-g_i(q';s)|\le3.2\varepsilon,\\
|a_i(q)-a_i(q')|\le17\varepsilon,\qquad
|m_i(q)-m_i(q')|\le14\varepsilon.
\end{gathered}
$$

**Proof.** Define $T_{i,q}(x)=x-K_i(\mathcal R(x)-q)$.
Its derivative norm is less than $\kappa=10^{-15}$. On the complete,
convex box $B_i$ it is therefore a contraction, and

$$
\|T_{i,q}(x)-z_i\|_\infty
<3\cdot10^{-41}+.054(2\cdot10^{-34})+10^{-15}10^{-30}
<10^{-30}.
$$

The last comparison is strict even with the closed source box and
all $q$ in the specified open record square. Thus it maps $B_i$ into
its interior. Banach's theorem gives a unique fixed point. Since
$\|I-K_iD\mathcal R\|<1$, its geometric series proves $K_iD\mathcal R$
invertible, hence $K_i$ invertible. A fixed point is exactly a zero
of $\mathcal R(x)-q$. Its displacement is bounded by

$$
\frac{3\cdot10^{-41}+.054(2\cdot10^{-34})}{1-10^{-15}}
<1.1\cdot10^{-35}.
$$

Lemma 2.2 proves lawful whole-world realization and all acquired rows.
Disjoint boxes make the two worlds distinct. The entire-child
bound of Theorem 12.2 and Sections 13–16 then proves equality of the complete sets on
$\mathcal U$, including every original world stratum.

The analytic inverse theorem applies because the rational circuit is
pole-free and its Jacobian nonsingular. Local analytic inverses agree
by uniqueness in $B_i$, defining analytic branches on $\mathcal V$.
Implicit differentiation gives $Dx_i=(D\mathcal R)^{-1}$ and
$D\Theta_i=D\Theta(D\mathcal R)^{-1}$. Integrating on the straight segment
in the convex $\mathcal U$ proves all the coordinate bounds and the
terminal bounds of Lemma 25.1.

The matrix entries are $r,b,c_{\rm src},1-r$; this proves the stated
maximum-entry bound. For the induced matrix norm the first row is
bounded by $(.053160+.002675)\varepsilon$ and the second by
$(.169790+.053160)\varepsilon<.223\varepsilon$ on branch one.
The corresponding branch-two sums are $.053100\varepsilon$ and
$.180190\varepsilon$. This proves the induced norm assertion, without
confusing it with the maximum-entry estimate. Finally
$1+7+49+343=400$, so the gain coefficient bound gives
$.008\cdot400\varepsilon=3.2\varepsilon$. ∎

## 27. A sharper enclosure of the existing exact M seed

**Lemma 27.1 (The displacement of the same algebraic zero).** Let
$F,c,X$ be exactly Definition 3.1, with $\rho=10^{-38}$ and unique
zero $x_*$ from Theorem 4.3. Use the grid $\sigma=10^{110}$ and
arithmetic of Lemma 25.1 to evaluate $[DF(c)]$ at the singleton
center, carrying derivatives in the order $(b_0,r_1,b_1)$. Let $L_s$
be its entrywise endpoint-midpoint matrix and put
$K_s=\operatorname{adj}(L_s)/\det L_s$. Then

$$
\begin{gathered}
6827359736/10^6<\det L_s<6827359737/10^6,\\
\sup_X\|I-K_sDF\|_\infty<5.758\cdot10^{-30},\qquad
\|K_sF(c)\|_\infty<3.616\cdot10^{-86},\\
\|x_*-c\|_\infty<3.617\cdot10^{-86},\qquad
|p_*-p_c|<10^{-65},\quad|v_*-v_c|<10^{-65}.
\end{gathered}
\tag{27.1}
$$

The two worlds are the two branches of Theorem 26.1 at this record,
and their terminal M readings are exactly equal.

**Proof.** No new seed equations or center are introduced. Each response
row for $f\in\{p,v,m\}$ in $DF$ is

$$
(f_b(2/5,b_0),-f_r(r_1,b_1),-f_b(r_1,b_1)).
$$

Apply Lemma 25.1's arithmetic with three derivative coordinates and
the displayed circuit order of Definition 2.1. Compute $L_s$ from
singleton endpoint midpoints, then its exact adjugate quotient. The
finite determinant comparison is the first line of (27.1). Multiplying
this exact quotient into the full-grid derivative and center enclosures,
with matrix dot products in increasing index order, gives the next
two comparisons. Singleton response evaluation also gives

$$
|p(2/5,c_1)-p_c|<3.617\cdot10^{-70},\qquad
|v(2/5,c_1)-v_c|<1.796\cdot10^{-68}.
\tag{27.2}
$$

These are finite rational endpoint comparisons under that prescription.
The center differences from the source centers of (24.1) are less
than $10^{-38}$, so every endpoint source over $X$ lies in $B_1$ or
$B_2$, since $2\cdot10^{-38}<t_x$. All denominators are therefore
separated from zero by Lemma 25.1.

For the already existing zero, put $T_s(x)=x-K_sF(x)$. Integration
along the segment from $c$ to $x_*$ gives

$$
\|x_*-c\|_\infty
\le3.616\cdot10^{-86}
 +(5.758\cdot10^{-30})\|x_*-c\|_\infty,
$$

and hence

$$
\|x_*-c\|_\infty
<\frac{3.616\cdot10^{-86}}{1-5.758\cdot10^{-30}}
<3.617\cdot10^{-86}.
$$

The first-endpoint derivative bounds $|p_b|<726,|v_b|<1674$ on
the whole intervening segment and (27.2) prove the claimed response
enclosures. The equalities are the existing $F(x_*)=0$ equalities of
Sections 4–6. Inverse uniqueness in Theorem 26.1 identifies the two
worlds with its two branches; no equality follows merely from small
residuals or overlapping intervals. ∎

## 28. The seed regular component and its entire two-world children

**Theorem 28.1 (The component containing the realized rectangle).**
Let $q_*=(p_*,v_*)$ be the existing exact seed, and let $\Omega_*$
be the connected component of $O\setminus D_{\rm crit}$ containing
it. Then $\mathcal U\subset\Omega_*$. Every entire child over
$\Omega_*$ has exactly two complete worlds. Transport of both seed
worlds along any path in $\Omega_*$ exhausts its terminal fiber.

**Proof.** On the entire closed rectangle, the four explicit polynomials
(22.1) satisfy the finite inequalities

| Polynomial | Enclosure on $\mathcal U$ |
| --- | --- |
| $E_0$ | $(-3807159123283,-3807159123282)$ |
| $E_1$ | $(9406089304480,9406089304481)$ |
| $E_2$ | $(-15436842,-15436841)$ |
| $E_3$ | $(184377462718,184377462719)$ |

For these comparisons use Lemma 25.1's grid operations, evaluate
monomials in descending lexicographic order in $(p,v)$, sum from zero,
and round endpoints outward to integers. Each comparison is strict.
Also $p\ne24$ on $\mathcal U$ and $q_\infty\notin\mathcal U$.
Thus $\mathcal U\subset O$.

Theorem 26.1 supplies both actual worlds at every point and exhausts
the entire child using Theorem 12.2. Lemma 25.1 gives nonzero response
determinants on both boxes. Also
$\Lambda=2\widehat D/(5TU\mathcal J\mathcal N)>0$ there. Eliminating
$\epsilon$ in the parent equation gives
$H_{\rm reg}=\Lambda\det D\mathcal R$ at either world. Hence neither
is critical, and exhaustion excludes all additional critical preimages,
including singular or exceptional ones. Thus
$\mathcal U\cap D_{\rm crit}=\varnothing$. Connectedness and seed
containment from Lemma 17.1 put the rectangle in one component.
Theorem 23.1 gives constant cardinality on that component, equal to
two by Corollary 17.2. The two lifts cannot meet: reversing the path
would violate unique lifting from the meeting world. They exhaust the
terminal fiber. No path-independent ordering of the sheets is needed. ∎

**Definition 28.2 (Collision functions independent of sheet labels).**
For any local analytic labels $W^+,W^-$ define

$$
J_\Delta=(a(W^+)-a(W^-))^2,\qquad
M_\Delta=(m(W^+)-m(W^-))^2.
\tag{28.1}
$$

Sheet permutations leave both expressions unchanged; they are therefore
global real analytic functions on $\Omega_*$. In this component the
original independently chosen pair predicate is equivalent to
$J_\Delta=M_\Delta=0$, because every distinct pair in a two-element
entire child is that whole unordered child. This deduction imposes no
new pair restriction on Definition 1.2.

A continuous path leaving this component while preserving $p\ne24$
must meet $\mathcal E_{\rm esc}=0$ or $D_{\rm crit}$: a path remaining
in the open complement stays in its initial connected component.
Critical crossings need not change cardinality, and barrier zeros need
not be realizable escapes. The barrier is an algebraic overestimate
of finite escape, not an exact realization assertion. The seed has
$M_\Delta=0,J_\Delta>0$. Neither $J_\Delta>0$ throughout $\Omega_*$
nor existence or absence of a common zero of (28.1) is established.

## 29. The entire full-height terminal M graph

On $\mathcal V$ write $f(p,v)=m_2(p,v)-m_1(p,v)$.
The terminal interval rows in Section 25 give

$$
\begin{aligned}
f_p&\in[-206652558,-206652556]/10^{12}
\subset(-.000206653,-.000206652),\\
f_v&\in[986337,986339]/10^{12}
\subset(.0000009863,.0000009864),\\
\|Df\|_\infty&<.000208,\qquad
.00477<-f_v/f_p<.00478.
\end{aligned}
$$

Here the derivative norm is the induced norm of a row. Both worlds
are evaluated at the same record. Uniform enclosures can be subtracted
without any claim that unrelated extreme values occur simultaneously.

**Theorem 29.1.** There is a unique real analytic graph
$p=\chi(v)$ over the whole closed interval $[v_c-h,v_c+h]$ such that

$$
f(p,v)=0\quad\Longleftrightarrow\quad p=\chi(v)
\qquad((p,v)\in\mathcal U).
$$

It extends analytically to an open interval containing this closed
interval, and throughout it

$$
|\chi(v)-p_c|<4.781\cdot10^{-37}<8\cdot10^{-36},\qquad
.00477<\chi'(v)<.00478.
$$

For every point of the closed rectangle,

$$
.000206652\,|p-\chi(v)|
\le |m_2(p,v)-m_1(p,v)|
\le .000206653\,|p-\chi(v)|.
$$

Both inequalities are strict off the graph; both become equalities
at zero on the graph. In addition,

$$
|m_2(p,v)-m_1(p,v)|<2.077\cdot10^{-38}<4.16\cdot10^{-38}.
$$

**Proof.** Lemma 27.1 gives an actual seed with $f(p_*,v_*)=0$.
Let $k=.00478$, $L=|v-v_*|$ for any specified closed-interval height.
The test points $p_*\pm kL$ remain in the interior horizontal interval,
since

$$
|p_*-p_c|+k(h+|v_*-v_c|)
<k h+(1+k)10^{-65}<4.781\cdot10^{-37}<h.
$$

The vertical mean value bound is
$|f(p_*,v)|\le.0000009864L$.
Since $f_p<-.000206652$ and
$.000206652k>.0000009864$, the left test value is nonnegative and
the right nonpositive. For $L>0$ their signs are strict; for $L=0$
the test point itself is the seed zero. The intermediate value theorem
and strict horizontal monotonicity give exactly one root. The displayed
location bound follows from its bracket. In particular the values at
the full rectangle's left and right edges have strictly positive and
strictly negative signs, including the endpoint heights.

The real analytic implicit function theorem applies because $f_p\ne0$;
local graphs agree by uniqueness, and $\chi'=-f_v/f_p$.
At the endpoint heights the roots remain interior to the open
$\mathcal V$, so their analytic neighborhoods extend past both
endpoints. Shrinking these endpoint neighborhoods preserves the strict
location and slope bounds by continuity. This proves the claimed open
extension and slope interval.

For fixed $v$, integrate $f_p$ from $\chi(v)$ to $p$. Its strict sign
and strict uniform bounds give exactly the weak inequalities shown,
and strictness whenever the integration interval has positive length.
The sharper uniform gap follows from

$$
|f(p,v)|<.000206653(h+4.781\cdot10^{-37})
=2.07641007993\cdot10^{-38}<2.077\cdot10^{-38}.
$$

Alternatively the original $4.16\cdot10^{-38}$ bound follows from
$\|Df\|<.000208$ and the seed-to-record distance less than $2h$.
All bounds include the closed rectangle's edges. ∎

## 30. Exact-record interpretation and unresolved scope

An exact record in $\mathcal U$ determines exactly the unordered pair
of complete worlds above. Increasing-$r$ labels give consistent
correspondence between the pairs at two nearby records. These labels
do not identify which member generated the acquired record. The terminal
M reading cannot resolve that ambiguity uniformly: the full-height
graph gives exact M collisions of the two distinct worlds. The terminal
J readings lie in the disjoint intervals $(964,965)$ and $(994,995)$,
so a terminal J value separates the two local alternatives.

The Lipschitz bounds compare two exact records in the specified
rectangle, varying only $p,v$. They are not estimates for arbitrary
errors in all seven acquired readings. The $.17$ bound for a source
matrix is a maximum-entry bound; the induced infinity norm bound
proved here is $.223$. Full-state, drift and gain-coefficient bounds
refer to the displayed coordinates, not to an additional unobserved
raw factorization of the source. Finite-digit input alone does not
specify an exact real number, and no computability assertion follows
merely from inverse uniqueness.

The entire-child cardinality conclusion uses Theorem 12.2, on
$\mathcal U$ only. The analytic constructions on $\mathcal V$ do not
assert a global upper bound on all children outside $\mathcal U$.
No unrestricted common-base result, global strategy depth, physical
realization, or access to both counterfactual terminal actions in one
experimental history follows. Original singular and exceptional sources
remain part of the quantified model and were excluded locally only
by the exhaustive inherited argument in Sections 13–16.

The general contraction argument is Banach's theorem; analyticity uses
the real analytic inverse and implicit function theorems. The original-row realization is Lemma 2.2. It supplies the whole-world
meaning of the two-box differential inequalities, recovery constants,
sharper enclosure of the same seed and transverse collision graph.


The source surface is smooth also at its allowed $\Lambda=0$ sources;
this is distinct from avoidance of response critical values. Properness
is relative to the explicit $O$ of (22.2), avoiding the algebraic escape
overestimate and $p=24$. The entire two-world covering applies only to
$\Omega_*$, not to all bases. Whole-child J injectivity is local to
$\mathcal U$. The double-zero condition (28.1) on the full component,
continuation of the M branch to any specified remote base, and the
original unrestricted independent-pair target remain unresolved.

The full parent, exact seed and whole-domain exceptional inventory
remain the owning results in Sections 1–18 and Common Parent Geometry,
as cited in Definition 19.1; no second seed or eliminant inventory is
introduced. The new boundary argument supplies bounded drift and whole
gain, finite-escape curves, their explicit barrier and relative
properness hypotheses. Classical covering, contraction, inverse and
implicit function tools are reused with these model-specific hypotheses
and the displayed quantitative bounds; their generic bindings are not
additional mathematical contributions.

## 追加锚（本行以下为增补区）

## 31. Common whole-world coordinates for the fold and J incidence

Retain Definitions 1.1–1.2 without restricting their domain or pair predicate.
In particular the two distinct-world pairs may overlap, and their common
terminal values need not agree. All gains are entire nonzero polynomials
of degree at most three, each with its own one fixed real drift and the
literal acquired and alternative clocks already specified.

The full-parent bijection is (19.1)–(19.2), inherited from
[Common Parent Geometry](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md),
Theorem 2.1. Its parameters are $\beta=1/8$ and $a_{\rm parent}=24/5$;
the latter is unrelated to the terminal reading $a(W)$. That bijection includes its $\Lambda=0$ branch; Lemma 2.2 supplies the
complete original-world realization on the pole-free source chart.

For Sections 32–38 use the following local aliases for exactly the
polynomials and map of Definition 2.1 and Definition 19.1:

$$
\begin{gathered}
X=\mathcal J,\quad N=\mathcal N,\quad K=S,\quad D=\widehat D,\quad
C_i=\widehat C_i\ (0\le i\le4),\quad B_i=\widehat B_i\ (i=5,6,7),\\
(N_p,N_v,N_a,N_m)=(P_p,P_v,P_a,P_m),\quad H=bD,\quad
A=(p,v)=\mathcal R.
\end{gathered}
\tag{31.1}
$$

Thus $D$ is a scalar source denominator, not the critical-value set
$D_{\rm crit}$ of (23.1). The polynomial $N$ in this correspondence is
not the whole-world neighborhood $\mathcal N_{\rm f}$ below. The source
box $\mathcal B_{\rm f}$ and fixed-response chart below are new local
domains; neither is the record rectangle $\mathcal U$ of Definition 12.1
or the record neighborhood $\mathcal V$ of Definition 24.1. In all charts
$\Lambda$ remains the scalar coefficient of $\epsilon$ in (19.1).

The correspondence includes the same entire gain, drift and responses:

$$
W(r,b)\text{ is Definition 2.1's complete world},\qquad
(p,v,a,m)=(N_p,N_v,N_a,N_m)/H.
\tag{31.2}
$$

In particular the regular-source identities are

$$
j=X/b,\quad n=N/b,\quad
\Lambda=2D/(5TUXN),\qquad \epsilon=-3KXN/D.
\tag{31.3}
$$

The fold arithmetic uses Definition 2.1's displayed factored expressions
with the aliases and assignment order specified here. For reproducibility
compute $X=b\cdot b+(r-r\cdot r)$, then $N=X+rb$, then $T,U,K,D$,
then $C_0,C_1,C_2,C_3,C_4,B_5,B_6,B_7,H,N_p,N_v,N_a,N_m$.
This specifies the interval expression as well as its exact polynomial.
The first five rows, entire gain, and four literal response meanings are
already proved by Lemma 2.2. Only $b,D$ and the positive parent traces
are divided by; no gain sample, leading coefficient, root difference or
drift is cancelled.

For the J-incidence arithmetic in Section 40 use a second expression
for the same rational responses, denoted $R_p=p,R_v=v,R_a=a,R_m=m$.
In the displayed order set

$$
\begin{gathered}
c_{\rm src}=r(1-r)/b,\quad j=b+c_{\rm src},\quad n=j+r,\quad
T=1+b,\quad U=1+2b,\\
\Lambda=1+6/T+1/U-4/j-4/n,\quad B_{\rm par}=6/T-2/U,\quad
\epsilon=-\frac{24}{5}(b-1/8)B_{\rm par}/\Lambda,\\
z_0=-24-\epsilon,\quad z_1=-\epsilon/j,\quad
z_2=(27/5-\epsilon)/T,\quad z_3=-\epsilon/n,\quad d=24+\epsilon,\\
t_5=-4z_0+15z_1-20z_2+10z_3,\quad
t_6=-10z_0+36z_1-45z_2+20z_3,\\
t_7=-20z_0+70z_1-84z_2+35z_3,\\
R_p=d+(U+n)t_5,\quad R_v=d+(2U+n)t_6,\\
R_a=d+(T+2j+4r)t_7,\quad R_m=d+(3U+2n)t_7.
\end{gathered}
\tag{31.4}
$$

Here $z_i=g(i)$ are exactly (19.2), and $t_i=g(i)$ by Lemma 2.2's
fixed-node interpolation rows. Hence (31.4) and (31.1)–(31.3) are the
same complete-world chart wherever $\Lambda\ne0$, rather than merely
numerically matching response lists. This second expression fixes the
arithmetic order for the seven-variable interval proof. The zero-safe
parent itself is still $F_{\rm par}=0$: at $b\ne1/8$ it forces
$\Lambda\ne0$; at $b=1/8,\Lambda\ne0$ it forces $\epsilon=0$; and at
$b=1/8,\Lambda=0$ every real $\epsilon$ remains allowed with its own
whole gain from (19.2). No chart assertion removes those exceptional
worlds from any entire child.

## 32. The determinant polynomial and an isolated algebraic source

For $f=p,v$ define polynomial derivative numerators
$$
 U_{f,r}=H\partial_rN_f-N_f\partial_rH,\qquad
 U_{f,b}=H\partial_bN_f-N_f\partial_bH.
$$
The bivariate determinant polynomial is specified without numerical
interpolation by the finite coefficient formula
$$
 \mathscr K(r,b)=U_{p,r}U_{v,b}-U_{p,b}U_{v,r}.
 \tag{32.1}
$$
It satisfies $\det DA=\mathscr K/H^4$. At $b=1$ set
$$
 Q(r)=13r^4-39r^3+24r^2+3r-11.
$$
The explicit degree-fifteen critical polynomial is
$$
 \begin{aligned}
 \Phi_{\rm f}(r)={}&1335360r^{15}-16024320r^{14}+91908080r^{13}
 -330185604r^{12}+798510927r^{11}\\
 &-1292187068r^{10}+1284776451r^9-476294549r^8
 -610032429r^7+1012598771r^6\\
 &-495508869r^5-152421889r^4+265749570r^3
 -59836247r^2-33422962r+10386802.
 \end{aligned}
 \tag{32.2}
$$
Exact polynomial expansion and cancellation give
$$
 D(r,1)=5Q(r),\qquad
 \mathscr K(r,1)=-225Q(r)\Phi_{\rm f}(r),\qquad
 \det DA(r,1)=-\frac{9\Phi_{\rm f}(r)}{25Q(r)^3}.
 \tag{32.3}
$$
These formulas specify both the determinant orientation, using input
order $(r,b)$ and output order $(p,v)$, and the polynomial scale.
Zeros of $Q$ are poles of this chart and cannot be accepted as roots
of its response determinant. No assertion is made that $\Phi_{\rm f}$ is the
minimal polynomial of the selected root.

Let
$$
 I_0=\left(\frac{31379336181}{10^{11}},
                \frac{31379336182}{10^{11}}\right).
$$
There is exactly one zero $\alpha_{\rm f}$ of $\Phi_{\rm f}$ in $I_0$.
More narrowly, put
$$
 L_{\rm f}=313793361813579284608955011483891013811213350270349554597836.
$$
Then the exact algebraic specification is
$$
 \Phi_{\rm f}(\alpha_{\rm f})=0,\qquad
 \frac{L_{\rm f}}{10^{60}}<\alpha_{\rm f}<\frac{L_{\rm f}+1}{10^{60}}.
 \tag{32.4}
$$

**Proof of isolation.** Rational Horner evaluation gives
$\Phi_{\rm f}(31379336181/10^{11})>0$ and
$\Phi_{\rm f}(31379336182/10^{11})<0$. On their closed interval,
outward rational interval evaluation of the derivative gives
$$
 -21289867<\Phi_{\rm f}'(r)<-21289866.
 \tag{32.5}
$$
The intermediate value theorem and strict decrease prove existence and
uniqueness. Exact rational evaluation also gives
$\Phi_{\rm f}(L_{\rm f}/10^{60})>0>\Phi_{\rm f}((L_{\rm f}+1)/10^{60})$, proving (32.4).
These tests are on the printed polynomial, rather than on an approximate
root's residual. ∎

Define exact algebraic values
$$
 (p_{\rm f},v_{\rm f},a_{\rm f},m_{\rm f})=(p,v,a,m)(\alpha_{\rm f},1),\qquad d_{\rm f}=d(\alpha_{\rm f},1).
 \tag{32.6}
$$
The following strict rational enclosures hold:
$$
 \begin{array}{c|cc}
 \text{quantity}&\text{lower numerator}&\text{upper numerator}\\\hline
 p_{\rm f}&82766464368943&82766464368944\\
 v_{\rm f}&444178429468760&444178429468761\\
 a_{\rm f}&815368979291905&815368979291906\\
 m_{\rm f}&1695320121161200&1695320121161201\\
 d_{\rm f}&30226790237556&30226790237557.
 \end{array}
 \tag{32.7}
$$
Every entry is divided by $10^{12}$. In particular $p_{\rm f}\ne24$.
Decimal illustrations, carrying no extra exactness claim, are
$$
 \alpha_{\rm f}\approx0.3137933618135793,\quad
 p_{\rm f}\approx82.76646436894354,\quad
 v_{\rm f}\approx444.1784294687601.
$$

## 33. Uniform exact differential inequalities

Put
$$
 r_{\rm f,c}=313793361815/10^{12},\qquad
 \mathcal B_{\rm f}=[r_{\rm f,c}-10^{-6},r_{\rm f,c}+10^{-6}]\times[1-10^{-6},1+10^{-6}].
 \tag{33.1}
$$
The closed box lies in the strict source domain and contains
$(\alpha_{\rm f},1)$ in its interior. For a function $f$, write
$$
 \begin{gathered}
 t=-p_r/p_b,\qquad \mathcal{L}f=f_r+tf_b,\\
 T_f=f_{rr}+2tf_{rb}+t^2f_{bb},\\
 \kappa=T_v-(v_b/p_b)T_p,\\
 \zeta=\{v_{rb}+tv_{bb}-(v_b/p_b)(p_{rb}+tp_{bb})\}/p_b.
 \end{gathered}
 \tag{33.2}
$$
Here $T_f$ denotes a quadratic form with the value of $t$ at the
point; it does not differentiate $t$. All the following inequalities
hold throughout the whole box, not just at its center:

| Quantity | Strict lower bound | Strict upper bound |
| --- | ---: | ---: |
| $D$ | $-44$ | $-43$ |
| $H$ | $-44$ | $-43$ |
| $d$ | $30$ | $31$ |
| $p$ | $82$ | $83$ |
| $v$ | $444$ | $445$ |
| $p_r$ | $7$ | $8$ |
| $p_b$ | $96$ | $97$ |
| $v_r$ | $44$ | $46$ |
| $v_b$ | $553$ | $557$ |
| $t$ | $-82/1000$ | $-79/1000$ |
| $\kappa$ | $111$ | $130$ |
| $\mathcal{L}a$ | $556$ | $561$ |
| $\mathcal{L}m$ | $133$ | $141$ |
| $\zeta$ | $-1$ | $0$ |

**Exact-arithmetic specification of the bounds.** The following finite
integer computation proves the table and makes its precision explicit.
Set $\sigma_{\rm f}=10^{80}$ and encode a rational $q$ by
$$
 [\lfloor \sigma_{\rm f}q\rfloor,\lceil \sigma_{\rm f}q\rceil]/\sigma_{\rm f}.
$$
Addition and negation act on endpoints exactly. For multiplication and
reciprocal use
$$
 \begin{aligned}
 ([l,u]/\sigma_{\rm f})([v,w]/\sigma_{\rm f})&\subseteq
 [\lfloor\min(lv,lw,uv,uw)/\sigma_{\rm f}\rfloor,
   \lceil\max(lv,lw,uv,uw)/\sigma_{\rm f}\rceil]/\sigma_{\rm f},\\
 ([l,u]/\sigma_{\rm f})^{-1}&\subseteq
 [\lfloor \sigma_{\rm f}^2/u\rfloor,\lceil \sigma_{\rm f}^2/l\rceil]/\sigma_{\rm f}\quad(lu>0).
 \end{aligned}
 \tag{33.3}
$$
Attach to each scalar its two first derivatives and symmetric two by two
Hessian. Independent $r,b$ carry the respective unit first derivatives
and zero Hessians; constants carry zero derivatives. Use
$$
 \begin{aligned}
 (xy)_i&=x_i y+x y_i,\\
 (xy)_{ij}&=x_{ij}y+x_i y_j+x_j y_i+x y_{ij},\\
 (x^{-1})_i&=-x_i(x^{-1})^2,\\
 (x^{-1})_{ij}&=2x_i x_j(x^{-1})^3-x_{ij}(x^{-1})^2.
 \end{aligned}
 \tag{33.4}
$$
All operations on the right are interval operations (33.3), including
repeated multiplications. Evaluate (31.1) in displayed factored order,
left to right within unparenthesized sums and products; use $r-r^2$
as $r-r\cdot r$. Form (31.2) by a reciprocal followed by multiplication.
Then evaluate (33.2), with $t^2=t\cdot t$. Endpoint comparisons give the
strict bounds in the table. For scale, the unrounded enclosures for
$\kappa,\mathcal{L}a,\mathcal{L}m$ lie respectively inside the rational intervals
$$
 (111214/1000,129280/1000),\quad
 (556915/1000,560340/1000),\quad
 (133004/1000,140491/1000).
 \tag{33.5}
$$
The coarse integer table follows directly from these interval operations;
it is not obtained by combining only its rounded derivative rows.
Apply the same circuit to the root bracket (32.4) with $b=1$ for (32.7),
and apply Horner's rule to $\Phi_{\rm f}'$ on $\overline I_0$ for (32.5).
Thus the specification involves only integer arithmetic, ordered
comparisons and integer floor or ceiling division. Each operation is an
outer inclusion, so the table applies at every real point of the box.

In particular $D,H\ne0$ throughout $\mathcal B_{\rm f}$, justifying every chart
and response division. Positivity of $b,X,N,T,U$ justifies (31.3).

**Theorem 33.1 (Rank and null curvature).** At $(\alpha_{\rm f},1)$,
$$
 \det DA=0,\qquad \operatorname{rank}DA=1,
 \qquad 96<p_b<97.
 \tag{33.6}
$$
With the specified normalization
$$
 k=(1,-p_r/p_b),\qquad \lambda=(-v_b/p_b,1),
$$
we have
$$
 DA\,k=0,\qquad \lambda DA=0,\qquad
 111<\lambda D^2A[k,k]=\kappa(\alpha_{\rm f},1)<130.
 \tag{33.7}
$$
Consequently the weaker bounds $110<\kappa<131$ also hold.

**Proof.** Equation (32.3) and $\Phi_{\rm f}(\alpha_{\rm f})=0$ give zero determinant.
The strict $p_b$ bound gives rank at least one, hence exactly one.
The displayed kernel and cokernel vectors then follow by substitution.
Their second derivative contraction is precisely (33.2). The interval
table proves its positive lower and upper bounds. This curvature uses
$dr=1$; rescaling the null vector would rescale it quadratically. ∎

The values
$\kappa(\alpha_{\rm f},1)\approx120.212450343622$,
$\mathcal{L}a(\alpha_{\rm f},1)\approx558.633655878502$, and
$\mathcal{L}m(\alpha_{\rm f},1)\approx136.761630337034$
are consistent illustrations of the exact inequalities, not their proof.

## 34. A quantitative fixed-response chart

Let
$$
 \eta=10^{-6},\qquad R=1/(2\cdot10^6),\qquad
 I_p=(p_{\rm f}-\eta,p_{\rm f}+\eta),\qquad I_r=(\alpha_{\rm f}-R,\alpha_{\rm f}+R).
 \tag{34.1}
$$
For every $(q,r)\in I_p\times I_r$ there is a unique
$\beta_{\rm f}(q,r)\in(1-10^{-6},1+10^{-6})$ satisfying
$$
 p(r,\beta_{\rm f}(q,r))=q.
 \tag{34.2}
$$
The function $\beta_{\rm f}$ is real analytic. Its two-variable notation
distinguishes it from the fixed parent parameter $\beta=1/8$.

**Proof.** At $b=1$, integration of $7<p_r<8$ gives
$|p(r,1)-p_{\rm f}|<8R=4\cdot10^{-6}$. Integrating $p_b>96$ from
$b=1$ to either horizontal box edge shows that the corresponding
endpoint responses lie below $p_{\rm f}-92\cdot10^{-6}$ and above
$p_{\rm f}+92\cdot10^{-6}$. They bracket all of $I_p$.
Strict increase in $b$, the intermediate value theorem and the
analytic implicit function theorem give existence, uniqueness and
analyticity. The relevant segments stay in $\mathcal B_{\rm f}$; (32.4) and (33.1)
put the whole closed $r$-strip inside its vertical extent. ∎

Write
$$
 h(q,r)=v(r,\beta_{\rm f}(q,r)),\quad
 a_q(r)=a(r,\beta_{\rm f}(q,r)),\quad m_q(r)=m(r,\beta_{\rm f}(q,r)).
$$
Implicit differentiation of (34.2) gives
$$
 \beta_{\rm f}_r=-p_r/p_b=t,\qquad \beta_{\rm f}_q=1/p_b,
 \qquad h_r=v_r-v_b p_r/p_b=-\det DA/p_b.
$$
A second differentiation at fixed $q$, using
$\beta_{\rm f}_{rr}=-T_p/p_b$, gives
$$
 h_{rr}=\kappa,\qquad h_{rq}=\zeta,
 \qquad a_q'(r)=\mathcal{L}a,\qquad m_q'(r)=\mathcal{L}m.
 \tag{34.3}
$$
Consequently the exact bounds
$$
 110<h_{rr}<131,\quad -1<h_{rq}<0,\quad
 556<a_q'<561,\quad133<m_q'<141
 \tag{34.4}
$$
hold on this whole chart. Also
$h_r(p_{\rm f},\alpha_{\rm f})=0$ by (32.3).

For each $q\in I_p$, there is a unique critical point
$\chi_{\rm f}(q)\in I_r$ of $r\mapsto h(q,r)$. It is analytic and
$$
 \chi_{\rm f}(p_{\rm f})=\alpha_{\rm f},\qquad
 |\chi_{\rm f}(q)-\alpha_{\rm f}|\le|q-p_{\rm f}|/110<\eta/110<R/2.
 \tag{34.5}
$$
The first comparison in (34.5) is strict when $q\ne p_{\rm f}$. Indeed $|h_r(q,\alpha_{\rm f})|\le|q-p_{\rm f}|$, while increasing $r$ changes
$h_r$ at rate greater than 110. Its signs at the two ends of $I_r$
are opposite because $110R>\eta$. Strict increase gives a unique
zero, the implicit function theorem gives analyticity, and integration
of the derivative lower bound gives (34.5). This also proves
$0<\chi_{\rm f}'(q)<1/110$.

## 35. The actual fold and its inverse branches

Put
$$
 h_0(q)=h(q,\chi_{\rm f}(q)),\qquad
 w(q,r)=\int_0^1(1-u)h_{rr}(q,\chi_{\rm f}(q)+u(r-\chi_{\rm f}(q)))\,du.
$$
Taylor's integral identity gives
$$
 h(q,r)-h_0(q)=(r-\chi_{\rm f}(q))^2w(q,r),\qquad
 55<w(q,r)<131/2.
 \tag{35.1}
$$
Define a source coordinate
$$
 z(q,r)=(r-\chi_{\rm f}(q))\sqrt{w(q,r)}.
 \tag{35.2}
$$
It is real analytic, and $z_r>0$. Away from the critical point,
$2zz_r=h_r$, with $z$ and $h_r$ of the same sign; at the
critical point $z_r=\sqrt{h_{rr}/2}>0$. Therefore
$(q,r)\mapsto(q,z)$ is an analytic coordinate change onto its image.
The target change $(q,v)\mapsto(q,v-h_0(q))$ is also analytic and
invertible. Together with (34.2) these give the **actual** response map
in the form
$$
 (q,z)\longmapsto(q,z^2).
 \tag{35.3}
$$
This proves a nondegenerate fold of the given whole-world source map;
no realization hypothesis about a generic fold is being inserted.

For clarity, let $\mathcal N_{\rm f}$ be the set of whole worlds
$$
 \mathcal N_{\rm f}=\{W(r,\beta_{\rm f}(q,r)):q\in I_p,\ r\in I_r\}.
 \tag{35.4}
$$
It is an open parent neighborhood. Distinct source points give distinct
whole worlds because their matrices retain both $r$ and $b$.
Conversely the zero-safe parent equations and $D\ne0$ show that this
chart has the entire whole-world lift of every source in its image.

The fixed-response functions extend to the closed $r$-interval by the
same endpoint-bracketing and strict derivative inequalities of Section 34.
At either $r$-endpoint, (34.5)–(35.1) give
$$
 h(q,r)-h_0(q)>55(R/2)^2
 =\frac{55}{16\cdot10^{12}}>2\cdot10^{-12}.
 \tag{35.5}
$$
Thus, for every $q\in I_p$ and
$0<\nu<2\cdot10^{-12}$, the base $(q,h_0(q)+\nu)$ has exactly
two worlds in $\mathcal N_{\rm f}$. They are defined without a numerical
solver by the two inverse branches
$$
 \begin{aligned}
 r_\pm(q,\nu)&=z_q^{-1}(\pm\sqrt\nu),\\
 b_\pm(q,\nu)&=\beta_{\rm f}(q,r_\pm(q,\nu)),\\
 W_\pm(q,\nu)&=W(r_\pm(q,\nu),b_\pm(q,\nu)),
 \end{aligned}
 \tag{35.6}
$$
where $z_q$ is the strictly increasing function (35.2). Both branches
are analytic for $\nu>0$; in the coordinate $s=\sqrt\nu$ they
extend analytically through the common fold world. At $\nu=0$ the
local child has one world. At negative $\nu$ it has none. These are
counts in $\mathcal N_{\rm f}$ only. The entire child may contain additional
worlds, including sources on other charts or on the singular parent
branch of (19.1).

## 36. Two exact worlds at the specified displacement

Fix
$$
 q=p_{\rm f},\qquad \nu=10^{-12},\qquad
 \widehat v_{\rm f}=v_{\rm f}+10^{-12},\qquad W_\pm=W_\pm(p_{\rm f},10^{-12}).
 \tag{36.1}
$$
Because $\chi_{\rm f}(p_{\rm f})=\alpha_{\rm f}$ and $h_0(p_{\rm f})=v_{\rm f}$, (35.6) places both
worlds in the exact same acquired child $C(p_{\rm f},\widehat v_{\rm f})$.
They are distinct and all source guards remain strict.

More precisely, put $s_-=\alpha_{\rm f}-r_->0$ and
$s_+=r_+-\alpha_{\rm f}>0$. From (34.4) and Taylor's identity,
$$
 55s_\pm^2<10^{-12}<(131/2)s_\pm^2.
$$
The exact rational comparisons
$$
 (131/2)(123/10^9)^2<10^{-12}
 <55(135/10^9)^2
$$
therefore give
$$
 123/10^9<s_-,s_+<135/10^9.
 \tag{36.2}
$$
Integration of $-82/1000<\beta_{\rm f}_r<-79/1000$ also gives
$$
 \begin{aligned}
 1+9717/10^{12}&<b_-<1+11070/10^{12},\\
 1-11070/10^{12}&<b_+<1-9717/10^{12}.
 \end{aligned}
 \tag{36.3}
$$
In particular the sources are unequal and strictly legal.

These exact worlds are algebraic, as well as analytic constructions.
For example $r_-$ is the unique real $r\in I_r$, $r<\alpha_{\rm f}$,
for which some $b\in(1-10^{-6},1+10^{-6})$ satisfies
$$
 N_p(r,b)-p_{\rm f}H(r,b)=0,\qquad
 N_v(r,b)-\widehat v_{\rm f}H(r,b)=0;
 \tag{36.4}
$$
use $r>\alpha_{\rm f}$ for $r_+$. Each sign selects exactly one source by
Section 35. The algebraic coefficient field is the real algebraic field
containing $\alpha_{\rm f},p_{\rm f},v_{\rm f}$. A singleton semialgebraic set over that
field has algebraic coordinates: projection and real quantifier
elimination reduce a singleton to polynomial sign conditions; away from
all polynomial roots such signs are locally constant and cannot isolate
a point. This standard real-algebraic argument proves algebraicity of
$r_\pm,b_\pm$, hence of their drifts and gain coefficients. The strict
pole bounds show that clearing denominators in (36.4) introduces no extra
world in the specified box.

Here are the whole gains and drifts explicitly. For each sign evaluate
all polynomials (31.1) at its single source $(r_\pm,b_\pm)$, and denote
the evaluations by a sign subscript. Set
$$
 \begin{aligned}
 d_\pm&=-C_{0,\pm}/D_\pm,\\
 g_\pm(s)&=D_\pm^{-1}\bigg[
 -\frac{C_{0,\pm}}6(s-1)(s-2)(s-3)
 +\frac{C_{1,\pm}}2s(s-2)(s-3)\\
 &\hspace{28mm}-\frac{C_{2,\pm}}2s(s-1)(s-3)
 +\frac{C_{3,\pm}}6s(s-1)(s-2)\bigg].
 \end{aligned}
 \tag{36.5}
$$
This is one complete polynomial for each world, with its own one fixed
real drift; no per-clock parameter is chosen. The gains have degree at
most three and cannot vanish identically by the unequal first two rows.
In fact $30<d_\pm<31$, but this property of the constructed worlds
does not restrict the original drift domain.

For either sign, all seven acquired readings and both alternatives are
as follows. Every entry in the gain column belongs to the same (36.5).

| Clock | Action | Gain sample | Trace | Reading |
| --- | --- | --- | --- | --- |
| 0 | initial | $C_{0,\pm}/D_\pm$ | $1$ | $0$ |
| 1 | $J$ | $C_{1,\pm}/D_\pm$ | $X_\pm/b_\pm$ | $24$ |
| 2 | $M$ | $C_{2,\pm}/D_\pm$ | $T_\pm$ | $147/5$ |
| 3 | $J$ | $C_{3,\pm}/D_\pm$ | $N_\pm/b_\pm$ | $24$ |
| 4 | $M$ | $C_{4,\pm}/D_\pm$ | $U_\pm$ | $18$ |
| 5 | $M$ | $B_{5,\pm}/D_\pm$ | $U_\pm+N_\pm/b_\pm$ | $p_{\rm f}$ |
| 6 | $M$ | $B_{6,\pm}/D_\pm$ | $2U_\pm+N_\pm/b_\pm$ | $\widehat v_{\rm f}$ |
| 7 | alternative $J$ | $B_{7,\pm}/D_\pm$ | $T_\pm+2X_\pm/b_\pm+4r_\pm$ | $a_\pm=N_{a,\pm}/H_\pm$ |
| 7 | alternative $M$ | $B_{7,\pm}/D_\pm$ | $3U_\pm+2N_\pm/b_\pm$ | $m_\pm=N_{m,\pm}/H_\pm$ |

The readings follow from Lemma 2.2, (34.2), and the exact branch
definitions. Equality of the acquired responses is not inferred from
overlapping numerical intervals.

## 37. Terminal separation and the outside-companion obligation

**Theorem 37.1.** At the base (36.1), the exact terminal differences satisfy
$$
 \frac{136776}{10^9}<a_+-a_-<\frac{151470}{10^9},\qquad
 \frac{32718}{10^9}<m_+-m_-<\frac{38070}{10^9}.
 \tag{37.1}
$$
In particular both terminal readings are distinct between the two local
worlds.

**Proof.** Equation (36.2) gives
$$
 246/10^9<r_+-r_-<270/10^9.
$$
Integrating the two terminal derivative bounds in (34.4) along the single
fixed-$p_{\rm f}$ curve gives
$$
 556(r_+-r_-)<a_+-a_-<561(r_+-r_-),
$$
and the analogous inequalities with 133 and 141 for $m$.
Multiplication gives exactly (37.1). ∎

For orientation only, the two sources and terminal responses are
approximately
$$
 \begin{array}{c|cc}
 &-&+\\\hline
 r&0.31379323282826445&0.31379349079889706\\
 b&1.0000000103951462&0.9999999896048728\\
 a&815.3689072363648&815.3690513474424\\
 m&1695.3201035209611&1695.3201388014454.
 \end{array}
$$
The rational inequalities and exact definitions, not these rounded
illustrations, establish existence, equality of acquired readings and
terminal separation.

**Corollary 37.2 (Precise outside requirement).** For any base with two
local worlds as in Section 35, every distinct terminal collision pair in
the entire child, for either $J$ or $M$, has at least one member
outside $\mathcal N_{\rm f}$. If both pairs in Definition 1.2 exist at (36.1), the entire
child has at least three worlds.

**Proof.** For a fixed $q$, each of $a_q,m_q$ is strictly increasing
on $I_r$ by (34.4). Thus two distinct worlds of $\mathcal N_{\rm f}$ with
the same acquired base cannot collide for either terminal action. Any
collision pair in the entire child must therefore have a member outside
$\mathcal N_{\rm f}$. At (36.1), the two local worlds already belong to that
child, so even one such pair forces a third world. ∎

This is a necessary condition, not an existence assertion. A collision
pair could consist of one local and one outside world, or of two outside
worlds. Neither local world is individually guaranteed a companion.
Independent $J$ and $M$ pairs can share an outside member, use
different outside members, or have other allowed overlaps. The argument
imposes no equality between their common terminal values and does not
exclude all outside realizations.

## 38. Global and exceptional-source boundaries

Within $\mathcal N_{\rm f}$ the counts are zero below the fold, one at
the fold, and two above it, for the target strip of Section 35. This proves only a lower bound of two
for the entire child at (36.1). No upper bound on that entire child is
established here. The two-world statement of Theorem 28.1 for $\Omega_*$ cannot be transferred to these bases without proving
component membership and the required continuation.

Boundary properness, where available, is relative to an explicitly
excluded escape barrier. It can prevent a lift from escaping over a
compact subset of that region. It does not construct a path from a seed,
prove that two specified bases share a regular component, or supply
missing terminal collision worlds. The fold value itself is critical,
so a covering theorem for regular values does not include it. No path to
the previously studied M-collision seed component is assumed or proved.

The entire child still quantifies over all strict original sources,
including unbounded off-diagonal parameters, all regular charts and the
singular branch in Section 31. Sampled gain zeros, degree drops, repeated
roots and zero drift remain legal throughout the original problem.
Our construction divides by none of them. Positivity and pole separation
justify only the explicit source chart in use; they do not delete
exceptional worlds elsewhere. Original strict boundaries $r=0,1$
and $b=0$ remain excluded as before, without imposing a positive
uniform distance from them on all worlds.

The fold is specified by the exact
polynomial (32.2), root (32.4), base enclosures (32.7), rank (33.6) and curvature
(33.7). The terminal separation at the specified positive displacement is (37.1). The degree-fifteen polynomial is a critical
polynomial on the slice $b=1$, not a claim about a minimal polynomial
or the entire critical set. Nothing here solves the unrestricted
independent-pair existence question of Definition 1.2.


## 39. Mathematical attribution for the two response geometries

The model, full-parent converse and literal response circuit are reused
from Sections 1–2 and 19 and
[Common Parent Geometry](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md),
Theorem 2.1. The actual-source fold geometry is the model-specific result
of *An actual source fold with separated terminal responses*; Sections
32–38 retain its exact determinant, isolated algebraic source, full-box
differential inequalities, actual inverse branches and terminal bounds.
The four-world J geometry is the model-specific result of *A four-world
acquired child with a genuine terminal-J collision*, retained in Sections
40–41 with its exact incidence and interval proof.

Fixed-node interpolation and finite differences are classical; see
Berrut and Trefethen, *Barycentric Lagrange Interpolation*, SIAM Review 46
(2004), 501–517. The contraction, intermediate, analytic inverse and
implicit function theorems, Taylor's integral formula and interval
inclusion arithmetic are standard. The analytic fold normal form belongs
to Whitney's theory of plane-to-plane mappings; (35.1)–(35.3) also give
the required form directly for this map. Real-algebraic projection and
singleton algebraicity follow from real quantifier elimination; see
Basu, Pollack and Roy, *Algorithms in Real Algebraic Geometry*. Neither the general fold theorem nor the general contraction
principle is an additional model-specific result.

## 40. Exact four-world J incidence

For $x=(x_1,\ldots,x_7)$ set

$$
A=(1/4,x_1),\quad B=(x_2,x_3),\quad
C=(x_4,x_5),\quad D=(x_6,x_7),
$$

where each ordered pair denotes $(r,b)$. These are source-point labels
local to this section: $A$ is not the fold map, and $D$ is not the scalar
denominator of (31.1). The center $c_{\rm J}$, box $X_{\rm J}$ and
preconditioner $L_{\rm J}$ below are seven-dimensional; they are unrelated
to the fold root-bracket integer $L_{\rm f}$ or the source entry $c_{\rm src}$. Define the rational map

$$
F_{\rm J}(x)=\begin{pmatrix}
R_p(A)-R_p(B)\\ R_v(A)-R_v(B)\\ R_a(A)-R_a(B)\\
R_p(A)-R_p(C)\\ R_v(A)-R_v(C)\\
R_p(A)-R_p(D)\\ R_v(A)-R_v(D)
\end{pmatrix}.                                                   \tag{40.1}
$$

Let $\rho_{\rm J}=10^{-11}$, and let $X_{\rm J}=\prod_{i=1}^7[c_i-\rho_{\rm J},c_i+\rho_{\rm J}]$,
where $c_{\rm J}=(c_1,\ldots,c_7)$ and the following finite decimals
are exact rationals:

$$
\begin{aligned}
c_1&=0.114833501729356886661759878705,\\
c_2&=0.761645896941701624224642579302,\\
c_3&=0.311543071675176747899101662302,\\
c_4&=0.861370986265965317403298544212,\\
c_5&=0.117268362691626034293752321772,\\
c_6&=0.243164373867715015960168619826,\\
c_7&=0.217520896522692033906895429321,\\
\end{aligned}                                                    \tag{40.2}
$$

Define the exact rational matrix

$$
L_{\rm J}=\begin{pmatrix}
0.005593917741 & -0.000569413986 & -0.000371337599 & 0.000000000000 & 0.000000000000 & 0.000000000000 & 0.000000000000\\
-0.035864955659 & 0.013565514774 & -0.002123235634 & 0.000000000000 & 0.000000000000 & 0.000000000000 & 0.000000000000\\
0.023656485976 & -0.010018941343 & 0.001312265481 & 0.000000000000 & 0.000000000000 & 0.000000000000 & 0.000000000000\\
0.007036346633 & -0.000716241170 & -0.000467089469 & -0.018406315740 & 0.007518312548 & 0.000000000000 & 0.000000000000\\
0.004915382645 & -0.000500344795 & -0.000326294821 & -0.008343876383 & 0.000299728792 & 0.000000000000 & 0.000000000000\\
-0.007874252954 & 0.000801533017 & 0.000522711688 & 0.000000000000 & 0.000000000000 & 0.020280074021 & -0.008064625967\\
-0.005203066005 & 0.000529628552 & 0.000345391929 & 0.000000000000 & 0.000000000000 & 0.014078333191 & -0.006072527092
\end{pmatrix}.                                                   \tag{40.3}
$$

**Proposition 40.1.** There is a unique $x_*\in X_{\rm J}$ satisfying $F_{\rm J}(x_*)=0$.
The four associated worlds $W_A,W_B,W_C,W_D$ are distinct legal worlds in
one entire $C(p_{\rm J},v_{\rm J})$, where

$$
\frac{2293}{100}<p_{\rm J}<\frac{2294}{100},\qquad
\frac{12780}{100}<v_{\rm J}<\frac{12781}{100}.                           \tag{40.4}
$$

They satisfy

$$
a(W_A)=a(W_B),\qquad
\frac{44766}{100}<a(W_A)<\frac{44767}{100},                       \tag{40.5}
$$

and their four terminal-M readings are pairwise distinct, with order
$m(W_D)<m(W_B)<m(W_C)<m(W_A)$.
In particular terminal J is not injective on all acquired children with
$p\ne24$.

**Proof.** All arithmetic bounds used here are specified over rational
intervals. This also gives a finite reproduction of the existence proof.
For a rational interval $I=[l,u]$, let

$$
\operatorname{rnd}_{36}(I)=10^{-36}
 [\lfloor10^{36}l\rfloor,\lceil10^{36}u\rceil].                  \tag{40.6}
$$

After each addition, multiplication or reciprocal take $\operatorname{rnd}_{36}$ of
the usual enclosing interval. Negation is exact. Products use the minimum
and maximum of their four endpoint products. Reciprocals use
$[1/u,1/l]$ and are used only when $0\notin I$. Division is multiplication
by this reciprocal. Constants and input intervals are their exact
rational intervals. For derivatives use seven-component interval jets:

$$
\begin{aligned}
(v,q)+(w,t)&=(v+w,q+t),\\
(v,q)(w,t)&=(vw,qw+vt),\\
(v,q)^{-1}&=(v^{-1},-qv^{-1}v^{-1}).
\end{aligned}                                                    \tag{40.7}
$$

Each operation on the right is the rounded interval operation just
defined. Each variable $x_i$ begins with the $i$th unit derivative;
constants have zero derivatives. Evaluate (31.4) through $\epsilon$,
then $z_0,z_1,z_2,z_3,d$,
then $t_5,t_6,t_7$, then the responses in (31.4), in displayed order.
Within a sum evaluate terms from left to right. Evaluate (40.1) in row
order. These rules enclose the map and its true first derivatives
throughout the box, by induction on the displayed arithmetic expressions.

The resulting strict rational comparisons are as follows. In the first
table, the $i$th bound is for
$\sum_j\sup_{x\in X_{\rm J}}|(I-L_{\rm J}DF_{\rm J}(x))_{ij}|$; compute each matrix product in
increasing summation index starting at zero.

| Row | Strict rational upper bound |
| --- | --- |
| 1 | $32\cdot10^{-8}$ |
| 2 | $30\cdot10^{-7}$ |
| 3 | $21\cdot10^{-7}$ |
| 4 | $51\cdot10^{-8}$ |
| 5 | $31\cdot10^{-8}$ |
| 6 | $62\cdot10^{-6}$ |
| 7 | $46\cdot10^{-6}$ |

Evaluating $L_{\rm J}F_{\rm J}(c_{\rm J})$ by the same operations gives

$$
\|L_{\rm J}F_{\rm J}(c_{\rm J})\|_\infty<10^{-20},\qquad
\sup_{x\in X_{\rm J}}\|I-L_{\rm J}DF_{\rm J}(x)\|_\infty<10^{-4}.                       \tag{40.8}
$$

The following additional enclosing intervals are obtained by the same
expressions on the entire box; every endpoint is an exact rational.
Only the common $p,v$ bounds in (40.4) are needed from the first world.

| World | $\Lambda$ | $d$ | $g(7)$ | $a$ | $m$ |
| --- | --- | --- | --- | --- | --- |
| $A$ | $(2.90,2.91)$ | $(24.06,24.07)$ | $(75.50,75.51)$ | $(447.66,447.67)$ | $(604.27,604.29)$ |
| $B$ | $(-0.70,-0.69)$ | $(28.28,28.30)$ | $(68.22,68.24)$ | $(447.66,447.67)$ | $(586.46,586.48)$ |
| $C$ | $(1.65,1.66)$ | $(24.08,24.09)$ | $(75.35,75.36)$ | $(539.05,539.07)$ | $(604.13,604.15)$ |
| $D$ | $(-0.20,-0.19)$ | $(31.96,31.97)$ | $(78.70,78.71)$ | $(371.76,371.78)$ | $(576.49,576.52)$ |

These tables are finite inequalities obtained from (31.4) and
(40.2)–(40.7), not rounded root assertions. All source intervals satisfy
$b>0$ and $0<r<1$. Hence $j,n,T,U>0$ before division. The listed
$\Lambda$ bounds justify the remaining divisions. In particular the
interval evaluations do not cross an unhandled pole.

To derive existence from the comparisons, set $N_{\rm J}(x)=x-L_{\rm J}F_{\rm J}(x)$.
The mean-value estimate on the convex box gives

$$
\|N_{\rm J}(x)-c_{\rm J}\|_\infty
\le \|L_{\rm J}F_{\rm J}(c_{\rm J})\|_\infty+10^{-4}\|x-c_{\rm J}\|_\infty
<10^{-20}+10^{-4}\rho_{\rm J}<\rho_{\rm J}.                                    \tag{40.9}
$$

Thus $N_{\rm J}$ maps $X_{\rm J}$ into its interior and is a contraction with constant
less than $10^{-4}$. The classical contraction principle gives one
unique fixed point $x_*\in X_{\rm J}$.
The norm bound at $c_{\rm J}$ also makes $L_{\rm J}DF_{\rm J}(c_{\rm J})$ invertible by its Neumann
series, so $L_{\rm J}$ is invertible. Therefore $N_{\rm J}(x_*)=x_*$ is equivalent to
$F_{\rm J}(x_*)=0$; every zero of $F_{\rm J}$ in $X_{\rm J}$ is this fixed point.

Equations (40.1) now give one shared acquired $p_{\rm J},v_{\rm J}$ for all four
worlds and the terminal-J equality for $A,B$. The disjoint $r$ intervals
in (40.2), together with $r_A=1/4$, make all four source matrices and
complete triples distinct. The actual realization in Section 31 proves
membership in the entire child; membership does not require that child
to have only four worlds. The response bounds give (40.4)–(40.5) and the
strict M ordering. In particular $p_{\rm J}\ne24$. This proves the
proposition. $\square$

**Corollary 40.2.** A local real analytic family of four-world incidences
as in Proposition 40.1 exists when $r_A$ varies through an open interval
containing $1/4$. Every member has $p\ne24$, a distinct-world J pair,
and the same strict ordering of the four listed M responses.

**Proof.** The responses are rational without poles in neighborhoods
of the four source boxes. Inequality (40.8) implies that $D_xF_{\rm J}(x_*)$
is invertible. Regard $r_A$ as an additional free parameter in (40.1).
The classical analytic implicit-function theorem supplies the local
family. All source, distinctness, $p\ne24$ and M-ordering inequalities
are strict, so continuity preserves them on a smaller open interval.
Each family member lifts by (31.4) to its own one entire gain and fixed
drift. $\square$

## 41. Four-world scope and the original independent pairs

The record rectangle $\mathcal U$ of Definition 12.1 lies
inside $172<v<173$; Proposition 40.1 has $127.80<v_{\rm J}<127.81$ and therefore
lies outside that rectangle. The new incidence includes both signs of
$\Lambda$, without claiming that those signs classify all collisions.
The construction disproves global terminal-J injectivity on the full
strict parent, by actual complete-world collisions rather than critical
response points.

The four listed M responses are different. This does not prove
terminal-M injectivity on their entire child: an additional world could
share one of these responses, or two additional worlds could form a
pair. It also does not exclude a different base with both required
collision pairs. The unresolved original obligation is still to
produce one entire $C(p,v)$ with $p\ne24$ containing a J pair and a
possibly different M pair, or to prove impossibility for all such bases.

The zero-safe parent theorem and the literal response formulas are
reused at their stated scope from Section 19 and Lemma 2.2. The seven-variable incidence, exact rational isolating box,
its actual J pair, four distinct M images and resulting local family
are the model-specific derivation here. The contraction and implicit
function theorems are classical tools used in that derivation. The pole-free existential
construction licenses no universal exclusion of $\Lambda=0$,
zero gain samples, lower degrees, repeated roots or zero drift.


**Corollary 41.1 (Separation from the inherited two-world component).**
The base $(p_{\rm J},v_{\rm J})$ of Proposition 40.1 lies outside
$\Omega_*$ of Theorem 28.1. The same holds for every member of the
local family of Corollary 40.2.

**Proof.** Proposition 40.1 and Corollary 40.2 give at least four distinct
complete worlds in each respective entire child. Every entire child over
$\Omega_*$ has exactly two worlds by Theorem 28.1. Membership would
contradict these cardinalities. $\square$

This argument proves neither an exact count for the new child nor
regularity of its base, a four-sheet covering component, or any collision
involving worlds outside the four listed ones. In particular four
pairwise different listed $m$ values exclude M collisions only among those
four worlds. They do not exclude an outside world sharing one of those
values or two outside worlds sharing another value. There is no asserted
connection between the fold chart and $\Omega_*$. The unrestricted
all-base question of Definition 1.2 remains unresolved: a J pair and an M
pair must occur at one common base with $p\ne24$, with the original
allowed overlaps and without requiring equal common terminal values.

## 42. An isolated ordered J/M intersection at the forbidden base

Retain the complete-world domain, clocks, entire child and independent
pair predicate of Definitions 1.1–1.2. The zero-safe parent and its
whole-world converse remain (19.1)–(19.2); all response functions in
Sections 42–46 are exactly the rational circuit (31.4), with the same
whole gain and fixed drift supplied by Lemma 2.2. Only the local
construction uses the regular chart $\Lambda\ne0$. The singular branch
of the parent remains part of every entire-child quantifier.

The notation for this local intersection is independent of Section 40.
Here $A=(r_A,b_A),B=(r_B,b_B),C=(r_C,b_C)$ are three variable sources;
in particular $r_A$ is not fixed at $1/4$. They are not the four sources
of Proposition 40.1, and $A$ is not the fold map of (31.1). The response
symbols $p,v,a,m$ below equal $R_p,R_v,R_a,R_m$ in (31.4). In the
local-intersection source, $e,B_0,c$ correspond respectively to
$\epsilon,B_{\rm par},c_{\rm src}$ here. Its boxes $Y,X$ are denoted
$Y_{\cap},X_{\cap}$ here; neither is $X_{\rm J}$, $\mathcal B_{\rm f}$,
$\mathcal U$ or $\mathcal V$. The reduced map $G$, six-variable map $F$,
centers $\bar u,\bar x$ and matrices $L_3,L_6$ are local to these
sections. The root symbols $u_{\cap},x_{\cap}$ replace that source's
$u_*,x_*$ and do not denote Section 40's $x_*$. That source's common
base reading $v_*$ is written $v_{\cap}$. The interval scale
$\sigma_{\cap}$ below replaces that source's $S$; it is not the
polynomial $S$ of Definition 2.1.

The reflection used in the construction is inherited parent geometry.
At $b=1/8$ on the regular chart, (19.1)–(19.2) give

$$
\epsilon=0,\qquad d=24,\qquad
 g=h,\quad h(s)=\frac85(s-1)(s-3)(s-5),\qquad p=24.
\tag{42.1}
$$

For $1/8<r<1$ the reflected source has $r'=9/8-r$, and

$$
n(r)=1/8+9r-8r^2=n(9/8-r),\qquad U=5/4,\qquad
h(5)=0,\quad h(6)=24,\quad h(7)=384/5.
\tag{42.2}
$$

Thus the two regular sources $(r,1/8),(9/8-r,1/8)$ have equal
$p,v,m$, by (31.4); both are strict. This reflection is context for
the isolated intersection, rather than an additional result.

**Theorem 42.1 (Exact isolated ordered intersection).** The rational
boxes of Section 43 determine three pairwise distinct strict complete
worlds $W_A,W_B,W_C$ in one entire $C(24,v_{\cap})$ such that

$$
a(W_A)=a(W_B),\qquad m(W_A)=m(W_C),\qquad
131.70<v_{\cap}<131.71.
\tag{42.3}
$$

Among regular-chart ordered source triples in $X_{\cap}$, this is the
unique solution of the six incidence equations (43.3). Consequently
there is no solution of that specified ordered pairing in $X_{\cap}$
with common $p\ne24$. The first five equations of (43.3) have rank five
at the solution; the sixth, the M-incidence, has a nonzero derivative
along their one-dimensional local solution manifold.

The exclusion quantifies only over this ordered box and the pairing
$J(A,B),M(A,C)$. It is not an exclusion for an entire child, for other
ordered triples, for four-world pairings or for all bases. The base in
(42.3) differs from the $p_{\rm J}\ne24$ base of Proposition 40.1.

## 43. Exact reduced and six-variable incidence boxes

Let $u=(u_1,u_2,u_3)$ and define

$$
G(u)=\begin{pmatrix}
p(u_2,u_3)-24\\
v(u_1,1/8)-v(u_2,u_3)\\
a(u_1,1/8)-a(u_2,u_3)
\end{pmatrix}.                                                   \tag{43.1}
$$

The three-dimensional center is

$$
\begin{aligned}
\bar u_1&=0.27338493277692062938117277534807800955236853281519814794646125,\\
\bar u_2&=0.76858321041873328473685419579892559444456508936103355669942409,\\
\bar u_3&=0.31244505105258409809358114188258746424822666166861670395489154.
\end{aligned}
$$

Set $Y_{\cap}=\prod_{i=1}^3[\bar u_i-10^{-18},\bar u_i+10^{-18}]$ and let

$$
L_3=
\begin{pmatrix}
0.0148348466405305112715002370425455877288525820242097124 & 0.001595973632781291204866457466223520184051910701934427588 & 0.0009521894654311845886993058140527158340971697523235428547\\
0.0409433875069983875230771566542029743624506006471315168 & 0.01382949714192748321484577446060447768304433602399625629 & -0.001776763661709536065741327507163935947637147054756316927\\
-0.02375354484127071359214480282544269170827479249122335487 & -0.01007490838149822698449187123245238935534370450477117623 & 0.001294387707925291542246101550653191761187478889209669875
\end{pmatrix}.                                                         \tag{43.2}
$$

For $x=(r_A,b_A,r_B,b_B,r_C,b_C)$ set

$$
F(x)=\begin{pmatrix}
p(A)-p(B)\\v(A)-v(B)\\a(A)-a(B)\\
p(A)-p(C)\\v(A)-v(C)\\m(A)-m(C)
\end{pmatrix}.                                                   \tag{43.3}
$$

Its center $\bar x$ is, in this exact order,

$$
\begin{pmatrix}
0.27338493277692062938117277534807800955236853281519814794646125\\
0.125\\
0.76858321041873328473685419579892559444456508936103355669942409\\
0.31244505105258409809358114188258746424822666166861670395489154\\
0.85161506722307937061882722465192199044763146718480185205353875\\
0.125
\end{pmatrix}.                                                   \tag{43.4}
$$

Let $X_{\cap}=\prod_{i=1}^6[\bar x_i-10^{-15},\bar x_i+10^{-15}]$. Its
preconditioner is

$$
L_6=
\begin{pmatrix}
-0.0148348466405305112715002370425455877288525820242097124 & 0.001595973632781291204866457466223520184051910701934427588 & 0.0009521894654311845886993058140527158340971697523235428547 & -1.675214974905602584232591400689200183609183079419768849 & 0.9627143002571723238712916751412270949566073019892996227 & -0.1504241094151831756048893242408167335869698909358280661\\
6.221834270730115390399741610875572884420105710871997137e-90 & -6.693620557216069629674742558202614454360347928375600537e-91 & -3.993546540657781035642059723774355727066762442369061296e-91 & -0.7259007552162769624652793691869324513976421505265814575 & 0.4171614079879926858442412224924629580763734863194251997 & -0.06518146999812385716316269101444733719943335723741018745\\
-0.0409433875069983875230771566542029743624506006471315168 & 0.01382949714192748321484577446060447768304433602399625629 & -0.001776763661709536065741327507163935947637147054756316927 & -0.5157877126990621834066327641546026776357813247690060419 & 0.2964134241578790486236768409175529403501811916541811019 & -0.04631459752466860134744950639336764692971581119596579717\\
0.02375354484127071359214480282544269170827479249122335487 & -0.01007490838149822698449187123245238935534370450477117623 & 0.001294387707925291542246101550653191761187478889209669875 & -0.08020071048150680908146114128650884129707532712435023758 & 0.04608982848645001782116605455718993368116528299481826203 & -0.007201535701007815284557196024560927137682075467940353443\\
0.0148348466405305112715002370425455877288525820242097124 & -0.001595973632781291204866457466223520184051910701934427588 & -0.0009521894654311845886993058140527158340971697523235428547 & 0.6699363987796279985932108768705520486903590396822276861 & -0.3896998044356373868550036421739968974813367535915469922 & 0.06229799615884507213437111800204389786621167867995978019\\
4.70982190574306410877656683658548392574108564831530061e-90 & -5.066956038578134156479035140820693180467839961551904701e-91 & -3.023046285125058259192687195643417835355272090064059659e-91 & -0.5568145716742213643665383145146666578538354687938672624 & 0.3157840360382837413407137722697281216273506028611158468 & -0.04934125563098183458448652691714501900427353169704935106
\end{pmatrix}.                                                         \tag{43.5}
$$

These matrices are rational matrices, rather than unspecified numerical
inverses. Their entries and all the centers above are finite decimals. In the
scientific notation in $L_6$, an entry written $q\mathrm e{-k}$ denotes
the exact rational $q\cdot10^{-k}$.

## 44. Full-box rational interval inequalities

Use $\sigma_{\cap}=10^{70}$ and represent an interval by $[L,U]/\sigma_{\cap}$. Encode a rational
$t$ by $[\lfloor \sigma_{\cap}t\rfloor,\lceil \sigma_{\cap}t\rceil]/\sigma_{\cap}$. Addition and negation
are exact. For multiplication use

$$
[L,U][V,W]/\sigma_{\cap}^2\ \subseteq\
[\lfloor\min(LV,LW,UV,UW)/\sigma_{\cap}\rfloor,
 \lceil\max(LV,LW,UV,UW)/\sigma_{\cap}\rceil]/\sigma_{\cap}.
$$

For a reciprocal, require $0\notin[L,U]$ and use

$$
([L,U]/\sigma_{\cap})^{-1}\subseteq
[\lfloor \sigma_{\cap}^2/U\rfloor,\lceil \sigma_{\cap}^2/L\rceil]/\sigma_{\cap}.
$$

Division means multiplication by this reciprocal. These rounding rules
apply after every multiplication or reciprocal, including operations
inside derivative propagation. Use interval jets $(v,q)$ with

$$
(v,q)+(w,t)=(v+w,q+t),\quad
(v,q)(w,t)=(vw,qw+vt),\quad
(v,q)^{-1}=(v^{-1},-qv^{-1}v^{-1}).
$$

Variables start with their unit derivative vectors and constants with
zero derivatives. Use the same response circuit (31.4), with
$c_{\rm src},j,n,T,U,\Lambda$ followed by $\epsilon$, then
$z_0,z_1,z_2,z_3,d$, then $t_5,t_6,t_7,p,v,a,m$. For this interval
expression put $o=0r+1$, evaluate $j=b+r(1-r)/b$, $T=o+b$, $U=o+2b$,
and use the following explicitly associated forms for the same scalars:

$$
\epsilon=-24(b-o/8)(6/T-2/U)/5/\Lambda,\qquad
z_2=(27o/5-\epsilon)/T.
\tag{44.1}
$$

The other expressions are exactly (31.4). All products,
divisions and sums are associated from left to right, with each written
pair of parentheses evaluated first. In $G$, construct its constant
second source coordinate as $(0u_1+1)/8$. Form the indicated differences
in (43.1) and (43.3). Matrix products sum in increasing column index,
starting at zero. This finite rational arithmetic gives the following
strict bounds. Row $i$ bounds
$\sum_j\sup|(I-L_kD\mathcal H)_{ij}|$ for the indicated map $\mathcal H$ and box.

| Dimension and map | Row | Strict upper bound |
| --- | --- | --- |
| 3, $G$ on $Y_{\cap}$ | 1 | $7\cdot10^{-14}$ |
| 3, $G$ on $Y_{\cap}$ | 2 | $24\cdot10^{-14}$ |
| 3, $G$ on $Y_{\cap}$ | 3 | $16\cdot10^{-14}$ |
| 6, $F$ on $X_{\cap}$ | 1 | $13\cdot10^{-10}$ |
| 6, $F$ on $X_{\cap}$ | 2 | $6\cdot10^{-10}$ |
| 6, $F$ on $X_{\cap}$ | 3 | $7\cdot10^{-10}$ |
| 6, $F$ on $X_{\cap}$ | 4 | $3\cdot10^{-10}$ |
| 6, $F$ on $X_{\cap}$ | 5 | $6\cdot10^{-10}$ |
| 6, $F$ on $X_{\cap}$ | 6 | $4\cdot10^{-10}$ |

At both centers the corresponding interval matrix product satisfies

$$
\|L_3G(\bar u)\|_\infty<10^{-50},\qquad
\|L_6F(\bar x)\|_\infty<10^{-50}.                               \tag{44.2}
$$

The same interval circuit on $X_{\cap}$ gives the following enclosing open
rational intervals. Each displayed interval strictly contains the
computed closed enclosure.

| World | $\Lambda$ | $d$ | $g(7)$ | $v$ | $a$ | $m$ |
| --- | --- | --- | --- | --- | --- | --- |
| A | $(2.787,2.788)$ | $(23.999,24.001)$ | $(76.799,76.801)$ | $(131.70,131.71)$ | $(457.67,457.69)$ | $(617.28,617.30)$ |
| B | $(-0.774,-0.773)$ | $(27.886,27.887)$ | $(69.882,69.884)$ | $(131.70,131.71)$ | $(457.67,457.69)$ | $(599.19,599.21)$ |
| C | $(1.599,1.600)$ | $(23.999,24.001)$ | $(76.799,76.801)$ | $(131.70,131.71)$ | $(546.49,546.50)$ | $(617.28,617.30)$ |

The source intervals satisfy $b>0$, $0<r<1$, hence $j,n,T,U>0$.
The displayed $\Lambda$ intervals justify the remaining reciprocals.
The three $r$ intervals lie respectively in $(.273,.274)$,
$(.768,.769)$ and $(.851,.852)$; they are disjoint.
For $G$ on $Y_{\cap}$, its first source box lies inside the A box of $X_{\cap}$ and
its second inside the B box, so their denominator guards follow as well.

Each arithmetic operation is an outer inclusion. Induction through
the circuit therefore encloses the true values and derivatives at every
real point of the indicated full box. The row inequalities and center
bounds follow by the displayed integer endpoint comparisons.

## 45. Reflected exact root and transverse uniqueness

For either $(\mathcal H,L,c,Z,\rho)=(G,L_3,\bar u,Y_{\cap},10^{-18})$ or
$(F,L_6,\bar x,X_{\cap},10^{-15})$, Section 44 gives

$$
\sup_Z\|I-LD\mathcal H\|_\infty<10^{-7},\qquad
\|L\mathcal H(c)\|_\infty<10^{-50}.
$$

Thus $\mathscr T(z)=z-L\mathcal H(z)$ maps the closed box into its interior, since

$$
\|\mathscr T(z)-c\|_\infty
<10^{-50}+10^{-7}\rho<\rho,
$$

and is a contraction. The contraction principle gives its unique fixed
point. Also $LD\mathcal H(c)$ is invertible by the Neumann-series criterion.
As these are square matrices, $L$ and $D\mathcal H(c)$ are invertible. Hence
fixed points of $\mathscr T$ are precisely zeros of $\mathcal H$. This proves existence
and uniqueness of a zero in each indicated box.

Let $u_{\cap}$ be the zero of $G$ in $Y_{\cap}$ and define the exact six-tuple

$$
x_{\cap}=(u_{\cap,1},1/8,u_{\cap,2},u_{\cap,3},9/8-u_{\cap,1},1/8).              \tag{45.1}
$$

Inspection of the printed finite decimals shows
$|\bar x_5-(9/8-\bar u_1)|<10^{-61}$, with the other corresponding
coordinates equal. Therefore $10^{-18}+10^{-61}<10^{-15}$ implies
$x_{\cap}\in X_{\cap}$. (42.1)–(42.2) give identical $p,v,m$ for A and C, with
$p_A=p_C=24$. Equation $G(u_{\cap})=0$ gives $p_B=24$ and equality of the
A/B $v$ and $a$ responses. It follows that $F(x_{\cap})=0$ exactly.
The unique zero of $F$ in $X_{\cap}$ must consequently be (45.1), proving that
its common $p$ is exactly 24, rather than merely close to 24.

Section 31 and Lemma 2.2 lift all three sources to complete worlds.
Their equal acquired responses place them in the same entire child. Disjoint source intervals give distinct
complete triples. The interval table proves the remaining bounds in
Theorem 42.1.

Finally the same derivative bound at the zero implies that $DF(x_{\cap})$
is invertible. Its first five rows are linearly independent, so the
implicit-function theorem makes their local common zero set a smooth
one-dimensional manifold. If the sixth row vanished on its tangent
line, $DF(x_{\cap})$ would have a nonzero kernel. This is impossible.
Thus the M-incidence is transverse on this local J-incidence curve.
This proves Theorem 42.1. $\square$

## 46. Scope of the ordered intersection and mathematical attribution

The original common-base question retains exactly the quantifiers of
Definition 1.2: one entire $C(p,v)$ with $p\ne24$ and distinct
$W_{J0},W_{J1}$ and distinct $W_{M0},W_{M1}$ satisfying

$$
a(W_{J0})=a(W_{J1}),\qquad m(W_{M0})=m(W_{M1}).
\tag{46.1}
$$

The pairs are independently selected, may overlap, and their common
terminal values need not agree. Theorem 42.1 supplies these two pair
incidences at the excluded value $p=24$, with a shared member $W_A$;
it does not supply a solution of (46.1) at an allowed base. The full-box
bounds even separate their common terminal readings:
$a(W_A)\in(457.67,457.69)$ and $m(W_A)\in(617.28,617.30)$.
Its $p\ne24$ exclusion concerns only (43.3) on $X_{\cap}$.
It supplies no exclusion farther along a continuation, on another
branch, for another ordered pairing, or for arbitrary independent
pairs in an entire child.

Proposition 40.1 instead supplies a J pair at an allowed base
$22.93<p_{\rm J}<22.94$, with four pairwise distinct listed M values.
Those inequalities are not M injectivity on the entire child.
The reflected forbidden-base intersection is not that four-world
incidence, and neither construction establishes a component connection,
an entire-child upper bound at its new base, or a solution of (46.1).
Pairwise different gain directions, if established for any collection,
would not by themselves imply joint linear independence or either
missing collision incidence. No gain-direction condition is imposed
on (46.1).

A global impossibility theorem for (46.1) would have to cover every
allowed base and every independent choice of pairs, including singular
parent strata. An existence theorem would require exact legal worlds
at one allowed common base. These alternatives remain the original
question. Sampled gain zeros, lower degrees, repeated roots, zero drift
and singular parent sources remain in its domain. Positivity and the
$\Lambda$ bounds here justify only the specified regular-chart
construction and its local uniqueness.

The model, zero-safe parent and whole-world realization are those of
Sections 1–2, 19 and 31 and
[Common Parent Geometry](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md),
Definitions 1.1–1.3 and Theorem 2.1. The reflection at $b=1/8$ is
inherited from that parent geometry. The exact reduced root, the
six-variable rational box, its isolated ordered $J(A,B)/M(A,C)$
intersection and transverse local uniqueness are the result of
*A certified local forbidden-base intersection for actual J and M
pairs*, expressed here in the common notation. Sections 32–38 and
40–41 retain the distinct fold and four-world J geometries attributed
in Section 39. Fixed-node interpolation, the contraction principle,
the Neumann-series criterion and the implicit-function theorem are
classical tools, applied with the displayed model-specific hypotheses.

## 追加锚（本行以下为增补区）

## 47. Equal-width terminal-M collisions in the entire child

**Definition 47.1 (An equal-width M pair).** Retain exactly the complete
worlds and entire children of Definitions 1.1–1.2. In particular the
literal acquired word is $J,M,J,M,M,M$, its clocks are $0,\ldots,6$,
its readings are $(0,24,147/5,24,18,p,v)$, and both alternatives use
clock seven. For $p\ne24$, an equal-width M pair consists of

$$
W_1,W_2\in C(p,v),\quad W_1\ne W_2,\qquad m(W_1)=m(W_2),\qquad
b(W_1)=b(W_2)=b>0.
\tag{47.1}
$$

Equality of widths is a condition on these two worlds, not on every
world of the entire child. Write $r_i,j_i,n_i,d_i,\epsilon_i$ for their
coordinates, where $\epsilon_i=d_i-24$. Throughout the following
sections $T=1+b$ and $U=1+2b$ at a common width. Define

$$
\begin{aligned}
H_0(b)&=50b^4-1137b^3-842b^2-1442b-1262,\\
H_1(b)&=2000b^4-13092b^3-74938b^2-88421b-33300,\\
H_2(b)&=11209b+37242,\\
H_3(b)&=1289b^3-12511b^2-66211b-38698,\\
\mathcal B_b(x,y)&=H_3(b)xy+TUH_2(b)(x+y)+UH_1(b),\\
F_{\rm w}(b)&=5289b^5+8141b^4-12957b^3
                  -44608b^2-80537b-33300.
\end{aligned}
\tag{47.2}
$$

The polynomials $H_i$ here are distinct from the circuit denominator
$H=b\widehat D$ of Definition 2.1.

**Theorem 47.2 (Fixed-width necessary identities and exclusion).** Every
pair in (47.1) satisfies the two exact necessary identities

$$
\boxed{H_3(b)n_1n_2+TUH_2(b)(n_1+n_2)+UH_1(b)=0}
\tag{47.3}
$$

and

$$
\boxed{3T H_2(b)(n_1-n_2)=5H_0(b)(d_1-d_2)}.
\tag{47.4}
$$

Both distinctions

$$
d_1\ne d_2,\qquad n_1\ne n_2
\tag{47.5}
$$

are consequences of (47.1), rather than extra hypotheses. The
polynomial $F_{\rm w}$ has a unique positive real root $\rho$, with
$2<\rho<3$. Every such pair has $b<\rho$; equivalently, no pair in
(47.1) has common width $b\ge\rho$. Moreover

$$
(n_1-n_2)(d_1-d_2)<0.
\tag{47.6}
$$

These are necessary conditions at equal widths. The bound $b<\rho$
is not an existence assertion for any common width below $\rho$.
The proof occupies Sections 48–52.

## 48. Full-parent reconstruction without a regular-chart restriction

Use the source coordinates of (19.1):

$$
\begin{gathered}
c_{\rm src}=r(1-r)/b,\quad j=b+c_{\rm src},\quad n=j+r,\quad
T=1+b,\quad U=1+2b,\quad\epsilon=d-24,\\
\Lambda=1+6/T+1/U-4/j-4/n,\\
B_{\rm par}=6/T-2/U=2(2+5b)/(TU)>0,\\
D_{\rm par}=\frac{24}{5}(b-1/8)B_{\rm par}.
\end{gathered}
\tag{48.1}
$$

The symbol $D_{\rm par}$ is the constant term in the parent equation,
not the regular-chart denominator of Section 31.

**Lemma 48.1 (The zero-safe parent and its actual-world lift).** The full
five-row parent consists exactly of $b>0$, $0<r<1$, $\epsilon\in\mathbb R$
satisfying

$$
\epsilon\Lambda+D_{\rm par}=0.
\tag{48.2}
$$

Its corresponding complete world has $P=P(r,b)$, $d=24+\epsilon$, and

$$
\begin{gathered}
z_0=-24-\epsilon,\quad z_1=-\epsilon/j,\quad
z_2=(27/5-\epsilon)/T,\quad z_3=-\epsilon/n,\\
g(s)=\sum_{i=0}^3 z_i\ell_i(s),\qquad
\ell_i(s)=\prod_{\substack{0\le k\le3\\ k\ne i}}\frac{s-k}{i-k}.
\end{gathered}
\tag{48.3}
$$

This is a bijection with complete worlds, including every source with
$\Lambda=0$.

**Proof.** All of $j,n,T,U$ are strictly positive on the source domain.
The literal traces, already obtained in Lemma 2.2, are

$$
\begin{array}{c|rrrrrrrrr}
\text{clock/action}&0&1,J&2,M&3,J&4,M&5,M&6,M&7,J&7,M\\ \hline
\text{trace}&1&j&T&n&U&U+n&2U+n&T+2j+4r&3U+2n.
\end{array}
\tag{48.4}
$$

The first four original readings therefore force exactly the four
samples in (48.3). A polynomial of degree at most three is uniquely
determined by these samples. The fixed-node weights give

$$
\begin{array}{c|rrrr}
s&\ell_0(s)&\ell_1(s)&\ell_2(s)&\ell_3(s)\\ \hline
4&-1&4&-6&4\\
5&-4&15&-20&10\\
6&-10&36&-45&20\\
7&-20&70&-84&35.
\end{array}
\tag{48.5}
$$

Substitution of the first row into the fifth original reading gives

$$
d+Ug(4)-18=U(\epsilon\Lambda+D_{\rm par}).
\tag{48.6}
$$

After division of this residual by $U$, its constant term is
$6/U+24-162/(5T)=D_{\rm par}$, and its coefficient of $\epsilon$
is $\Lambda$. Hence (48.2) is both necessary and sufficient. The source
matrix is legal because $b>0$, $0<r<1$, and (48.3) has degree at most
three. Its whole gain cannot vanish identically: otherwise the first
two readings would both be $d$, contrary to $0\ne24$. Conversely every
parent world fixes $(b,r,\epsilon)$ and these samples, proving the
bijection. This is the target-parent correspondence of Section 19 and
*FIB common-parent geometry and two exact mixed children*, Theorem 2.1,
with its reconstruction displayed in the present notation. $\square$

In particular $\Lambda=0$ forces $D_{\rm par}=0$, hence $b=1/8$.
At any source with $b=1/8$ and $\Lambda=0$, every real $\epsilon$ is
allowed by (48.2), including $\epsilon=-24$, which gives zero drift.
The reconstruction divides by positive source traces and fixed
interpolation-node differences, never by $\Lambda$, a gain sample,
a leading coefficient or a difference of gain roots.

**Lemma 48.2 (The original $p\ne24$ condition).** Every world of
$C(p,v)$ with $p\ne24$ has $\epsilon\ne0$.

**Proof.** If $\epsilon=0$, then (48.2) and $B_{\rm par}>0$ force
$b=1/8$. The four samples in (48.3) then give exactly

$$
g(s)=h(s)=\frac85(s-1)(s-3)(s-5),\qquad d=24.
\tag{48.7}
$$

Since $h(5)=0$, the literal fifth response is $p=24$, a contradiction.
Thus $\epsilon\ne0$ is a derived consequence of the required base,
not a restriction on the original world domain. In particular it does
not require $d\ne0$. $\square$

## 49. A zero-safe affine lift of three actual responses

For $b>0$ define the following functions of the width alone:

$$
\begin{aligned}
\mathsf C_5&=\frac{3(b+2)(8b-1)}{2TU},&
\mathsf A_5&=\frac{b^2-16b-12}{2TU},\\
\mathsf C_6&=\frac{3(80b^2+192b+31)}{5TU},&
\mathsf A_6&=\frac{2b^2-24b-17}{TU},\\
\mathsf C_7&=\frac{3(200b^2+503b+114)}{5TU},&
\mathsf A_7&=\frac{5b^2-52b-36}{TU}.
\end{aligned}
\tag{49.1}
$$

These symbols denote gain coefficients; they are not the response
coefficients $A_5,A_6$ of (19.3). Put

$$
L_{\rm w}(b)=
\begin{pmatrix}
\mathsf C_5&\mathsf A_5&6+U\mathsf A_5&5U\\
\mathsf C_6&\mathsf A_6&17+2U\mathsf A_6&32U\\
2\mathsf C_7&2\mathsf A_7&71+3U\mathsf A_7&105U
\end{pmatrix}.
\tag{49.2}
$$

**Lemma 49.1 (Full-parent affine response identity).** On every full
parent world the literal responses after fifth M, sixth M and terminal
M satisfy

$$
\begin{pmatrix}p-24\\v-24\\m-24\end{pmatrix}
=
\begin{pmatrix}U\mathsf C_5\\2U\mathsf C_6\\3U\mathsf C_7\end{pmatrix}
+L_{\rm w}(b)
\begin{pmatrix}n\\\epsilon n\\\epsilon\\\epsilon/n\end{pmatrix}.
\tag{49.3}
$$

This identity also holds when $\epsilon=0$ or $\Lambda=0$.

**Proof.** Rearranging (48.2), without dividing by either of those
quantities, gives

$$
\frac{\epsilon}{j}
=\frac{\epsilon}{4}(1+6/T+1/U)-\frac{\epsilon}{n}
 +\frac{D_{\rm par}}4.
\tag{49.4}
$$

Insert (49.4) in the last three interpolation rows (48.5).
Collection of the constant and $\epsilon$ coefficients yields

$$
\begin{aligned}
g(5)&=\mathsf C_5+\mathsf A_5\epsilon+5\epsilon/n,\\
g(6)&=\mathsf C_6+\mathsf A_6\epsilon+16\epsilon/n,\\
g(7)&=\mathsf C_7+\mathsf A_7\epsilon+35\epsilon/n.
\end{aligned}
\tag{49.5}
$$

Explicitly, the same coefficients before simplification are

$$
\begin{aligned}
\mathsf C_5&=96-108/T-15D_{\rm par}/4,&
\mathsf A_5&=(1-10/T-15/U)/4,\\
\mathsf C_6&=240-243/T-9D_{\rm par},&
\mathsf A_6&=1-9/T-9/U,\\
\mathsf C_7&=480-2268/(5T)-35D_{\rm par}/2,&
\mathsf A_7&=5/2-21/T-35/(2U).
\end{aligned}
\tag{49.6}
$$

Substituting (48.1) simplifies these to (49.1). Multiply (49.5),
respectively, by $U+n$, $2U+n$ and $3U+2n$, and add $d=24+\epsilon$.
The results are exactly (49.2)–(49.3). Thus these three readings belong
to the same complete world with its one whole gain and one fixed drift.
Only positive $j,n,T,U$ have been divided out. $\square$

## 50. The everywhere rank-three cofactor line

**Lemma 50.1 (Rank and kernel at every positive width).** For every
$b>0$, $L_{\rm w}(b)$ has rank three, and

$$
\ker L_{\rm w}(b)=\mathbb R K_{\rm w}(b),\qquad
K_{\rm w}(b)=
\begin{pmatrix}
-5UH_0(b)\\3UH_1(b)\\-3TUH_2(b)\\3H_3(b)
\end{pmatrix}.
\tag{50.1}
$$

**Proof.** The determinant of the three columns numbered one, two and
four of (49.2) is

$$
-\frac{3H_2(b)}{10T}\ne0,
\tag{50.2}
$$

since $H_2(b)=11209b+37242>0$. More explicitly, delete column $i$
and multiply its maximal minor by $(-1)^{i+1}$. In column order the
four signed minors are

$$
\left(
-\frac{H_0}{2T^2},\quad
\frac{3H_1}{10T^2},\quad
-\frac{3H_2}{10T},\quad
\frac{3H_3}{10T^2U}
\right).
\tag{50.3}
$$

These equalities follow by substituting (49.1) into (49.2) and
expanding the three-by-three determinants. Each row annihilates this
cofactor vector, by expansion of the determinant with that row
repeated. Multiplication of (50.3) by the positive scalar $10T^2U$
gives $K_{\rm w}$. The nonzero minor proves rank three, so this
nonzero kernel vector spans the entire kernel. No width at which
$H_0$, $H_1$ or $H_3$ vanishes is deleted. $\square$

## 51. Pair identities and distinctions forced by actual worlds

Suppose (47.1) holds. Subtracting (49.3) at the common width gives

$$
L_{\rm w}(b)\delta=0,\qquad
\delta=
\begin{pmatrix}
n_1-n_2\\
\epsilon_1n_1-\epsilon_2n_2\\
\epsilon_1-\epsilon_2\\
\epsilon_1/n_1-\epsilon_2/n_2
\end{pmatrix}.
\tag{51.1}
$$

First $\delta\ne0$. Otherwise $n_1=n_2$ and
$\epsilon_1=\epsilon_2=\epsilon\ne0$ by Lemma 48.2. Equation (49.4)
then gives the same $\epsilon/j$ in both worlds, hence the same $j$.
Thus $r=n-j$ is also the same. The fixed width, source and drift
coincide, and (48.3) fixes the same entire gain, contradicting
$W_1\ne W_2$. The use of $\epsilon\ne0$ here is justified by
$p\ne24$; it is not required for the affine lift.

Lemma 50.1 now gives a real $t\ne0$ such that

$$
\delta=tK_{\rm w}(b).
\tag{51.2}
$$

Its third coordinate is nonzero because $T,U,H_2$ are positive.
Consequently $\epsilon_1\ne\epsilon_2$, or $d_1\ne d_2$.
Comparing its first and third coordinates yields (47.4).
For (47.3) use the exact algebraic identity

$$
(\epsilon_1n_1-\epsilon_2n_2)
+n_1n_2(\epsilon_1/n_1-\epsilon_2/n_2)
=(n_1+n_2)(\epsilon_1-\epsilon_2).
\tag{51.3}
$$

Substitute (51.2) and cancel the known nonzero scalar $3t$ to obtain

$$
UH_1+H_3n_1n_2+TUH_2(n_1+n_2)=0.
\tag{51.4}
$$

No gain value, root difference, drift or $\Lambda$ is cancelled in
this step.

The distinction $n_1\ne n_2$ follows from the actual-world hypotheses
as well. For $0<b\le3$ one has

$$
H_0(b)=(50b-1137)b^3-842b^2-1442b-1262<0.
\tag{51.5}
$$

If $n_1=n_2$, equation (47.4) and $d_1\ne d_2$ would force
$H_0(b)=0$, so $b>3$. At a fixed such width the function

$$
n(r)=b+\frac{(b+1)r-r^2}{b},\qquad
\frac{dn}{dr}=\frac{b+1-2r}{b}>0\quad(0<r<1)
\tag{51.6}
$$

is strictly increasing. Hence equal $n$ forces equal $r$, and both
worlds have the same source. Since $b>3$, $D_{\rm par}\ne0$;
(48.2) therefore forces $\Lambda\ne0$ at that source.
Subtracting their two parent equations gives
$(\epsilon_1-\epsilon_2)\Lambda=0$, contradicting their different
drifts. This proves both assertions of (47.5) without assuming them.

## 52. A positive-root range excluding every common-width M pair

For $b\ge1$ every strict source has

$$
b<n<b+1.
\tag{52.1}
$$

Indeed $n-b=r(b+1-r)/b>0$ and
$b+1-n=(1-r)(b-r)/b>0$. The three different corner values of
$\mathcal B_b$ on $[b,b+1]^2$ are

$$
\begin{aligned}
\mathcal B_b(b,b)=F_{\rm w}(b)
 &=5289b^5+8141b^4-12957b^3-44608b^2-80537b-33300,\\
\mathcal B_b(b,b+1)=\mathcal B_b(b+1,b)=G_{\rm w}(b)
 &=5289b^5+9430b^4-3050b^3-2708b^2+3700b+3942,\\
\mathcal B_b(b+1,b+1)=H_{\rm w}(b)
 &=5289b^5+10719b^4+8146b^3+26681b^2+21726b+2486.
\end{aligned}
\tag{52.2}
$$

The descending coefficient signs of $F_{\rm w}$ have exactly one
change. Descartes' rule of signs gives at most one positive root,
counted with multiplicity. The exact evaluations

$$
F_{\rm w}(2)=-176958<0,\qquad F_{\rm w}(3)=918426>0
\tag{52.3}
$$

and the intermediate value theorem give such a root
$\rho\in(2,3)$. It is the unique positive root. Since the leading
coefficient is positive, $F_{\rm w}(b)\ge0$ for $b\ge\rho$.
The exact shifted expansion

$$
G_{\rm w}(2+u)=5289u^5+62320u^4+283950u^3
              +628432u^2+681148u+296238
\tag{52.4}
$$

is positive for $u\ge0$. All coefficients of $H_{\rm w}$ in
(52.2) are positive, so $H_{\rm w}(b)>0$ for $b>0$.

Let $b\ge\rho$. For $x,y\in(b,b+1)$ put $s=x-b$, $t=y-b$.
Bilinear interpolation gives exactly

$$
\mathcal B_b(x,y)
=(1-s)(1-t)F_{\rm w}(b)
+\{s(1-t)+(1-s)t\}G_{\rm w}(b)
+stH_{\rm w}(b).
\tag{52.5}
$$

Here $0<s,t<1$. The first term is nonnegative, and the last two
are positive, including at $b=\rho$. Thus
$\mathcal B_b(x,y)>0$ throughout this open square. By (52.1) the
actual $n_1,n_2$ lie in it, contradicting (47.3). Hence every pair
in (47.1) has $b<\rho$.

For such a pair $b<\rho<3$, so (51.5) gives $H_0(b)<0$.
Multiplication of (47.4) by $d_1-d_2$ now gives

$$
3T H_2(b)(n_1-n_2)(d_1-d_2)
=5H_0(b)(d_1-d_2)^2<0.
\tag{52.6}
$$

This proves (47.6) and completes Theorem 47.2. $\square$

## 53. Independent-pair scope and comparison with the parent results

The original question of Definition 1.2 retains the full predicate

$$
\begin{gathered}
\exists p,v\in\mathbb R,\quad p\ne24,\quad
\exists W_{J0},W_{J1},W_{M0},W_{M1}\in C(p,v):\\
W_{J0}\ne W_{J1},\qquad a(W_{J0})=a(W_{J1}),\\
W_{M0}\ne W_{M1},\qquad m(W_{M0})=m(W_{M1}).
\end{gathered}
\tag{53.1}
$$

The two pairs may overlap, and their common terminal readings may
differ. No source coordinate or gain direction is an acquired
observation.

**Corollary 53.1 (The equal-width alternative for an independent M
pair).** If (53.1) holds, its independently chosen M pair either has
unequal widths, or has a common width $0<b<\rho$ satisfying
(47.3)–(47.6). This assertion imposes no equality of widths on the
J pair and no relation between the two common terminal readings.

**Proof.** If the two M widths agree, that pair satisfies exactly
Definition 47.1, so Theorem 47.2 applies. Otherwise it is in the
unequal-width alternative. The J pair does not enter that theorem's
hypotheses or proof. $\square$

For the four worlds of Proposition 40.1, the source intervals (40.2)
give, with exact rational decimal endpoints,

$$
\begin{gathered}
b_A\in(0.1148,0.1149),\qquad b_C\in(0.1172,0.1173),\\
b_D\in(0.2175,0.2176),\qquad b_B\in(0.3115,0.3116).
\end{gathered}
\tag{53.2}
$$

These intervals are pairwise disjoint. Consequently none of the six
pairs among those four worlds meets the equal-width hypothesis.
The fixed-width exclusion supplies no obstruction to that J
construction, no assertion about its continuations, and no exclusion
of additional companions in its entire child. Its listed M readings
remain pairwise distinct by Proposition 40.1; that finite comparison
is not injectivity of M on the entire child.

The preceding results differ from the relevant parent theorems in
*FIB common-parent geometry and two exact mixed children* as follows.
Its Theorem 3.2 concerns equal projective gain directions on the
five-row parent: outside the saturated direction each direction has
at most one complete world. When $p\ne24$ the saturated direction
is absent. That theorem compares proportional whole gains; it does
not impose equal widths or compare the three shared actual responses
$p,v,m$ of arbitrary distinct worlds. The affine response kernel and
identities (47.3)–(47.4) supply those latter constraints without a
proportional-gain hypothesis.

Its Theorem 4.1 describes the exceptional slice $b=\beta$ at the
parent parameter $\beta$; at the present parent $\beta=1/8$.
Its Theorem 5.1 excludes full fifth-M $L_2$ supports contained in that
exceptional slice and supplies the associated direction restrictions.
A fifth-M $L_2$ support requires both sixth actions and their
continuations; a single terminal-M pair after the specified sixth M
is a different assertion. In addition an arbitrary common width here
need not equal $1/8$. Thus neither the exceptional-slice result nor
its full-support exclusion gives (47.3), (47.4), or the range
$b\ge\rho$ for actual M pairs at arbitrary common widths. The new
identities apply also at the exceptional width when their actual-world
hypotheses hold.

The zero-safe parent and complete-world meaning are inherited from
Sections 1–2, 19 and 31 and the cited Common Parent Theorem 2.1.
The model-specific affine reduction, cofactor line, fixed-width
identities and corner exclusion are those of *A zero-safe fixed-width
obstruction for the independent-pair problem*, expressed here with
that whole-world correspondence. Section 51 also derives
$n_1\ne n_2$ from the stated hypotheses, rather than adding it as a
restriction. Fixed-node polynomial interpolation, the cofactor
identity, bilinear interpolation, Descartes' rule and the intermediate
value theorem are the classical tools within these proofs.

The necessary identities do not themselves supply legal sources,
their full parent lifts, or a shared acquired child. No sufficiency
or sharp existence threshold at $\rho$ follows. The exclusion is
confined to equal widths at least $\rho$; it does not exclude
unequal-width M pairs or establish any realizable equal-width pair
below $\rho$. The existence of the independent pairs in (53.1), or
a global impossibility theorem for them, remains unresolved.

Every universal full-parent identity above retains $\Lambda=0$,
vanishing sampled gains, lower degrees, repeated gain roots and zero
drift wherever the original rows permit them. The original entire
child still contains all legal worlds of Definitions 1.1–1.2,
including its singular and degenerate strata. The distinctions of
(47.5) and the nonzero $\epsilon$ of Lemma 48.2 are forced only under
the explicitly stated collision and $p\ne24$ hypotheses; they are
not replacements for the unrestricted domain.

## 追加锚（本行以下为增补区）

## 54. All-width reconstruction and the exact parent correspondence

Retain the entire child and complete worlds of Definitions 1.1–1.2.
The chronological acquired word is literally $J,M,J,M,M,M$, with
readings $(0,24,147/5,24,18,p,v)$ at clocks $0,\ldots,6$.
The alternative terminal actions $J$ and $M$ both occur at clock seven.
Each world has its own fixed source $P(r,b)$, one fixed real drift $d$
and one whole nonzero real polynomial $g$ of degree at most three.
There is no restriction to a regular source chart or a particular
component of the entire child.

Fix real $p\ne24,v,w$. The variable $w$ prescribes the terminal-M
answer, so the object to reconstruct is

$$
\{W\in C(p,v):m(W)=w\}.
\tag{54.1}
$$

The width $b>0$ is allowed to vary over all positive real numbers.
Widths, $r,j,n$, gain coefficients and drift coordinates are defined
source parameters, not additional acquired observations. In particular
prescribing $w$ selects a terminal-response fiber; it does not add a
source port to the acquired experiment.

**Definition 54.1 (Notation and reused identities).** Use exactly
$T,U,j,n,\epsilon,D_{\rm par},\Lambda$ from (48.1), and put

$$
\mathcal A_{\rm par}=1+6/T+1/U,\qquad
\Lambda=\mathcal A_{\rm par}-4/j-4/n.
\tag{54.2}
$$

The parent and full-world reconstruction are Lemma 48.1, with
$\epsilon=d-24$, $D_{\rm par}=\frac{24}{5}(b-1/8)B_{\rm par}$ and
the four samples (48.3). The affine identity to be used is precisely
(49.3), with the coefficients $\mathsf C_i,\mathsf A_i$ of (49.1)
and matrix $L_{\rm w}$ of (49.2). The rank and cofactor line are
Lemma 50.1. None of these results requires $\Lambda\ne0$.

For explicit correspondence with *Exact cross-width reconstruction of
a terminal-M response triple*, its symbols have the following meanings
in the present volume:

$$
\begin{array}{c|c}
\text{cross-width notation}&\text{present notation}\\ \hline
e&\epsilon=d-24\\
\mathcal A&\mathcal A_{\rm par}\\
D&D_{\rm par}\\
C_i,A_i&\mathsf C_i,\mathsf A_i\quad(i=5,6,7)\\
L,V&L_{\rm w},\mathsf V\\
\alpha,\beta,\gamma&\alpha_{\rm w},\beta_{\rm w},\gamma_{\rm w}\\
\kappa,\eta&\kappa_{\rm rec},\eta_{\rm rec}\\
Q,R,\Delta&Q_{\rm rec},R_{\rm rec},\Delta_{\rm rec}\\
q,q_0,\varrho&q_{\rm rec},q_{\rm s},\chi_{\rm src}\\
F,G&F_{\rm rec},G_{\rm rec}.
\end{array}
\tag{54.3}
$$

The width slope $\alpha_{\rm w}$ is unrelated to the isolated fold
coordinate $\alpha_{\rm f}$ or the gain coefficients $\alpha_i$.
The slope $\beta_{\rm w}$ is not the parent parameter $\beta=1/8$.
The scalar $D_{\rm par}$ is neither the chart denominator
$\widehat D$ nor the local alias $D$ of Section 31.
The symbols $\kappa_{\rm rec},\eta_{\rm rec}$ below are response
consistency coefficients, not the fold curvature or a chart radius.
In Sections 55–60, $X,Y,Z$ denote transformed response coordinates,
not the source polynomial $X=\mathcal J$ used in Sections 32–38.
Finally $\chi_{\rm src}$ is a reconstruction numerator, not the
positive width cutoff $\rho$ of Theorem 47.2; and $Q_{\rm rec}$ is a
scalar polynomial, not an action product $Q_i$.

The full-parent literal formulas needed below, directly from
(48.4), (49.3) and (49.5), are

$$
\begin{aligned}
g(5)&=\mathsf C_5+\mathsf A_5\epsilon+5\epsilon/n,\\
g(6)&=\mathsf C_6+\mathsf A_6\epsilon+16\epsilon/n,\\
g(7)&=\mathsf C_7+\mathsf A_7\epsilon+35\epsilon/n,\\
p(W)&=24+\epsilon+(U+n)g(5),\\
v(W)&=24+\epsilon+(2U+n)g(6),\\
m(W)&=24+\epsilon+(3U+2n)g(7),\\
a(W)&=24+\epsilon+(T+2j+4r)g(7).
\end{aligned}
\tag{54.4}
$$

These are responses of the same complete world at the specified
literal clocks. Lemma 48.2 gives $\epsilon\ne0$ whenever $p\ne24$.
This is a consequence of the prescribed base, not a prohibition on
zero drift: $d=0$ means $\epsilon=-24$ and remains admitted whenever
the original equations hold. The parent, interpolation and cofactor
proofs in Sections 48–50 are reused with this exact correspondence.

## 55. An explicit inverse at every positive width

**Definition 55.1 (Width slopes and response transform).** With exactly
the polynomials $H_0,H_1,H_2,H_3$ of (47.2), set

$$
\alpha_{\rm w}=\frac{5H_0}{3TH_2},\qquad
\beta_{\rm w}=-\frac{H_1}{TH_2},\qquad
\gamma_{\rm w}=-\frac{H_3}{TUH_2}.
\tag{55.1}
$$

Let $\mathsf V$ consist of columns one, two and four of $L_{\rm w}$:

$$
\mathsf V=
\begin{pmatrix}
\mathsf C_5&\mathsf A_5&5U\\
\mathsf C_6&\mathsf A_6&32U\\
2\mathsf C_7&2\mathsf A_7&105U
\end{pmatrix}.
\tag{55.2}
$$

For the prescribed triple $(p,v,w)$ define

$$
q_{\rm rec}=
\begin{pmatrix}
p-24-U\mathsf C_5\\
v-24-2U\mathsf C_6\\
w-24-3U\mathsf C_7
\end{pmatrix},\qquad
\begin{pmatrix}X\\Y\\Z\end{pmatrix}=\mathsf V^{-1}q_{\rm rec}.
\tag{55.3}
$$

The inverse is completely explicit: its three rows are

$$
\begin{aligned}
(\mathsf V^{-1})_{1,\bullet}
&=\frac1{3H_2}\bigl(
10(110b^2-808b-519),\quad
25(b^2-128b-108),\quad
-10(6b^2-136b-107)\bigr),\\
(\mathsf V^{-1})_{2,\bullet}
&=\frac1{H_2}\bigl(
-2(4400b^2+12032b+4041),\quad
-5(40b^2-437b-666),\quad
30(4b-3)(4b+7)\bigr),\\
(\mathsf V^{-1})_{3,\bullet}
&=\frac1{UH_2}\bigl(
-12(99b+274),\quad32(31b+108),\quad-(139b+542)\bigr).
\end{aligned}
\tag{55.4}
$$

Every defining denominator here is positive for $b>0$, since
$T=1+b>0$, $U=1+2b>0$ and $H_2=11209b+37242>0$.
No zero of $H_0,H_1$ or $H_3$ is excluded.

**Lemma 55.2 (The affine solution line in drift coordinates).** For a
full-parent world of width $b>0$, the equations
$p(W)=p,v(W)=v,m(W)=w$ are equivalent to

$$
n=X+\alpha_{\rm w}\epsilon,\qquad
\epsilon n=Y+\beta_{\rm w}\epsilon,\qquad
\epsilon/n=Z+\gamma_{\rm w}\epsilon.
\tag{55.5}
$$

**Proof.** By (50.2),
$\det\mathsf V=-3H_2/(10T)\ne0$ at every positive width.
Substitution of (49.1) in (55.2) and multiplication by (55.4)
gives the identity matrix, proving the displayed inverse.
Dividing the kernel vector (50.1) by its nonzero third coordinate
$-3TUH_2$ gives

$$
\frac{K_{\rm w}}{-3TUH_2}
=(\alpha_{\rm w},\beta_{\rm w},1,\gamma_{\rm w})^{\mathsf T},
\qquad
\mathsf V
\begin{pmatrix}\alpha_{\rm w}\\\beta_{\rm w}\\\gamma_{\rm w}\end{pmatrix}
=-(L_{\rm w})_{\bullet,3}.
\tag{55.6}
$$

Thus (49.3) says exactly that

$$
\mathsf V(n,\epsilon n,\epsilon/n)^{\mathsf T}
=q_{\rm rec}-\epsilon(L_{\rm w})_{\bullet,3}.
$$

Applying (55.4) gives (55.5). Reversing these equalities proves the
converse. This uses the existing cofactor line, without a new parent
or cofactor argument. $\square$

## 56. Multiplicative consistency and the exhaustive exceptional branch

**Definition 56.1 (Two consistency equations).** Set

$$
\begin{gathered}
\kappa_{\rm rec}=\alpha_{\rm w}Z+\gamma_{\rm w}\beta_{\rm w}-1,
\qquad
\eta_{\rm rec}=XZ+\gamma_{\rm w}Y,\\
Q_{\rm rec}(E)=\alpha_{\rm w}E^2+(X-\beta_{\rm w})E-Y,\\
R_{\rm rec}(E)=(X+\alpha_{\rm w}E)(Z+\gamma_{\rm w}E)-E.
\end{gathered}
\tag{56.1}
$$

The variable $E$ is a candidate value of $\epsilon$, not an action.
All the coefficients in (56.1) are defined for every $b>0$.

**Lemma 56.2 (Exact consistency reduction).** The two polynomial
identities required to turn the affine line into actual products are
equivalent to

$$
Q_{\rm rec}(E)=0,\qquad
\kappa_{\rm rec}E+\eta_{\rm rec}=0.
\tag{56.2}
$$

More precisely, put $n=X+\alpha_{\rm w}E$ and $t=Z+\gamma_{\rm w}E$.
If (56.2) holds and $n>0$, then

$$
En=Y+\beta_{\rm w}E,\qquad t=E/n.
\tag{56.3}
$$

**Proof.** For every real $E$,

$$
\begin{aligned}
Q_{\rm rec}(E)&=(X+\alpha_{\rm w}E)E-(Y+\beta_{\rm w}E),\\
R_{\rm rec}(E)-\gamma_{\rm w}Q_{\rm rec}(E)
&=\kappa_{\rm rec}E+\eta_{\rm rec}.
\end{aligned}
\tag{56.4}
$$

The first identity gives the first equation in (56.3). The second
shows that (56.2) is exactly $Q_{\rm rec}(E)=R_{\rm rec}(E)=0$.
With $n>0$, the latter equation is $nt=E$ and gives $t=E/n$.
Conversely both product identities make both polynomials vanish,
so (56.2) follows. $\square$

**Lemma 56.3 (A positive remainder prevents an infinite branch).**
For every $b>0$, $\alpha_{\rm w}=0$ implies $\kappa_{\rm rec}>0$,
independently of $(p,v,w)$. Hence

$$
\kappa_{\rm rec}=0\quad\Longrightarrow\quad\alpha_{\rm w}\ne0.
\tag{56.5}
$$

**Proof.** Define the polynomial
$P_*=H_1H_3-T^2UH_2^2$. Its exact division identity is

$$
\begin{aligned}
31250P_*={}&H_0\bigl(1611250000b^3+10453832500b^2
                  +67037081050b+1318823177377\bigr)\\
&+1544327184292999b^3+1181902158153034b^2\\
&+1962712091375234b+1661282250974774.
\end{aligned}
\tag{56.6}
$$

Multiplying the polynomials in (47.2) proves this identity coefficient
by coefficient. If $\alpha_{\rm w}=0$, the positive denominator in
(55.1) implies $H_0=0$. Every coefficient of the displayed remainder
is strictly positive, so $P_*>0$ for $b>0$. In this case the term
$\alpha_{\rm w}Z$ vanishes and

$$
\kappa_{\rm rec}=\gamma_{\rm w}\beta_{\rm w}-1
=\frac{P_*}{T^2UH_2^2}>0.
\tag{56.7}
$$

This proves (56.5). In particular, simultaneous vanishing of the
linear consistency equation's coefficients cannot leave an
identically zero quadratic. $\square$

## 57. Complete strict-source filters and the whole-gain converse

**Definition 57.1 (Legal candidate at a prescribed width).** Given
real $p,v,w$ with $p\ne24$, a width $b>0$ and a real solution $E$
of (56.2), form in order

$$
\begin{gathered}
n=X+\alpha_{\rm w}E,\qquad t=Z+\gamma_{\rm w}E,\\
q_{\rm s}=\mathcal A_{\rm par}E+D_{\rm par}-4t,\qquad
j=4E/q_{\rm s},\qquad r=n-j.
\end{gathered}
\tag{57.1}
$$

The expression for $j$ is evaluated only after checking
$q_{\rm s}\ne0$. The candidate is retained exactly when

$$
\boxed{\begin{gathered}
E\ne0,\qquad n>0,\qquad q_{\rm s}\ne0,\\
j>b,\qquad 0<r<1,\qquad b(j-b)=r(1-r).
\end{gathered}}
\tag{57.2}
$$

These tests enforce the original strict source domain as well as
its nonlinear source relation. They are not optional filters on an
eliminant root. A retained candidate has $j>b>0$, so all source
trace divisions in (48.3) are lawful.

**Theorem 57.2 (Exact reconstruction at every positive width).** Fix
any real $p\ne24,v,w$. At each $b>0$, the complete worlds in (54.1)
of width $b$ are in bijection with the retained candidates of
Definition 57.1. The exhaustive candidate list is as follows.

1. If $\kappa_{\rm rec}\ne0$, there is just one possible candidate,
   $E=-\eta_{\rm rec}/\kappa_{\rm rec}$. It is retained exactly when
   $Q_{\rm rec}(E)=0$ and all of (57.2) hold.
2. If $\kappa_{\rm rec}=0$ and $\eta_{\rm rec}\ne0$, there are no
   candidates and hence no worlds of this width in (54.1).
3. If $\kappa_{\rm rec}=\eta_{\rm rec}=0$, define

$$
\Delta_{\rm rec}=(X-\beta_{\rm w})^2+4\alpha_{\rm w}Y.
\tag{57.3}
$$

   If $\Delta_{\rm rec}<0$, there are no candidates. If
   $\Delta_{\rm rec}\ge0$, the candidates are exactly

$$
E=\frac{\beta_{\rm w}-X\pm\sqrt{\Delta_{\rm rec}}}
          {2\alpha_{\rm w}}.
\tag{57.4}
$$

   A repeated root is counted once; each real root is retained
   exactly when (57.2) holds. Lemma 56.3 guarantees that the
   denominator $2\alpha_{\rm w}$ in this case is nonzero.

Every retained candidate determines the entire world, not just its
source or its sampled responses. Its drift is $d=24+E$, its source
is $P(r,b)$, and its one whole gain is exactly

$$
\begin{gathered}
z_0=-24-E,\quad z_1=-E/j,\quad
z_2=(27/5-E)/T,\quad z_3=-E/n,\\
g(s)=\sum_{i=0}^3z_i\ell_i(s),
\qquad\ell_i\text{ as in (48.3)}.
\end{gathered}
\tag{57.5}
$$

The criterion applies at arbitrary widths independently, including
widths different from those of any other reconstructed world.
It has no hypothesis $\Lambda\ne0$.

**Proof.** Let $W$ be an actual world in (54.1). Lemma 48.2 supplies
$\epsilon\ne0$, and Lemmas 55.2 and 56.2 give (56.2) with
$E=\epsilon$ and $t=\epsilon/n$. The parent equation (48.2) gives

$$
q_{\rm s}=\mathcal A_{\rm par}\epsilon+D_{\rm par}
             -4\epsilon/n=4\epsilon/j\ne0.
\tag{57.6}
$$

Therefore (57.1) recovers precisely the world's $j$ and $r$.
The actual strict source has $n>0$, $j>b$ and
$b(j-b)=r(1-r)$, so it passes every test in (57.2).

Conversely, take any retained candidate. By Lemma 56.2,
$t=E/n$ and $En=Y+\beta_{\rm w}E$. Its definition of $j$ gives
$4E/j=q_{\rm s}$, with no division by a zero quantity, and hence

$$
\begin{aligned}
E(\mathcal A_{\rm par}-4/j-4/n)+D_{\rm par}
&=\mathcal A_{\rm par}E-q_{\rm s}-4t+D_{\rm par}\\
&=0.
\end{aligned}
\tag{57.7}
$$

The last equation in (57.2), together with $b>0$, gives exactly
$j=b+r(1-r)/b$. Also $n=j+r$ by (57.1), and $0<r<1$ is strict.
Thus the reconstructed source is an original legal source, and
(57.7) is exactly its full parent equation (48.2).

Lemma 48.1 applied to this source and $E$ supplies the whole gain
(57.5), of degree at most three, with the first five prescribed
readings. Lemma 56.2 gives all three equalities in (55.5), so
Lemma 55.2, now on this full parent, gives precisely $p,v,w$ at
clocks five, six and terminal seven with M. The gain cannot be
identically zero, because then clocks zero and one would both read
$d$, contrary to their readings $0$ and $24$. This constructs a
complete world in the entire $C(p,v)$ with $m=w$.

For a fixed candidate, $b,E,n,j,r$ are fixed, so (57.5) determines
its unique gain and drift. Conversely an actual world recovers its
own $E$ by (57.6). This proves the bijection. Finally the three cases
are the exhaustive solution of a quadratic and a linear equation
(56.2); Lemma 56.3 supplies the nonzero quadratic leading coefficient
in case 3. No fourth case or infinite exceptional family is omitted.
$\square$

**Corollary 57.3 (Multiplicity at one width).** For a fixed
$(p,v,w)$ with $p\ne24$ and a fixed $b>0$, there are at most two
complete worlds in (54.1). There are two distinct worlds exactly
when $\kappa_{\rm rec}=\eta_{\rm rec}=0$,
$\Delta_{\rm rec}>0$ and both roots in (57.4) pass (57.2).

**Proof.** The rational case has at most one world, the inconsistent
linear case has none, and case 3 has at most two roots. Two distinct
roots that pass the filter give different $E$, hence different
drifts and complete worlds. A repeated root gives only one world.
$\square$

The construction includes the parent singularity $\Lambda=0$:
(48.2) then forces $D_{\rm par}=0$ and $b=1/8$, but neither (57.1)
nor (57.5) divides by $D_{\rm par}$ or $\Lambda$. Vanishing sampled
gains, a vanishing cubic coefficient, lower gain degrees and repeated
gain roots are preserved wherever the original rows permit them.
No gain sample, leading coefficient or gain-root difference has been
cancelled. The necessary $E\ne0$ in (57.2) is exactly the consequence
of $p\ne24$ from Lemma 48.2; in particular $E=-24$ is not removed.

## 58. Two rational width equations and their exact guards

**Definition 58.1 (Rational branch functions).** On the branch
$\kappa_{\rm rec}\ne0$ define

$$
\begin{aligned}
\nu&=X\kappa_{\rm rec}-\alpha_{\rm w}\eta_{\rm rec},\\
\theta&=Z\kappa_{\rm rec}-\gamma_{\rm w}\eta_{\rm rec},\\
\omega&=D_{\rm par}\kappa_{\rm rec}
          -\mathcal A_{\rm par}\eta_{\rm rec}-4\theta,\\
\chi_{\rm src}&=\nu\omega+4\eta_{\rm rec}\kappa_{\rm rec},\\
F_{\rm rec}&=\alpha_{\rm w}\eta_{\rm rec}^2
 -(X-\beta_{\rm w})\eta_{\rm rec}\kappa_{\rm rec}
 -Y\kappa_{\rm rec}^2,\\
G_{\rm rec}&=b(-4\eta_{\rm rec}-b\omega)
                 \kappa_{\rm rec}^2\omega
 -\chi_{\rm src}(\kappa_{\rm rec}\omega-\chi_{\rm src}).
\end{aligned}
\tag{58.1}
$$

These are rational functions of $b$ for each fixed $(p,v,w)$.
Their defining denominators are products of positive numerical
constants and positive powers of $T,U,H_2$. Their numerator equations
can therefore be used on $b>0$ without introducing a positive-width
pole. They are different from $F_{\rm w},G_{\rm w}$ in Section 52.

**Theorem 58.2 (Exact rational-branch width criterion).** Fix real
$p\ne24,v,w$. A width $b>0$ with $\kappa_{\rm rec}\ne0$ supports a
complete world in (54.1) if and only if

$$
\boxed{\begin{gathered}
F_{\rm rec}=G_{\rm rec}=0,\qquad
\eta_{\rm rec}\ne0,\qquad\omega\ne0,\\
\frac{\nu}{\kappa_{\rm rec}}>0,\qquad
-\frac{4\eta_{\rm rec}}{\omega}>b,\qquad
0<\frac{\chi_{\rm src}}{\kappa_{\rm rec}\omega}<1.
\end{gathered}}
\tag{58.2}
$$

All rational expressions in these tests are evaluated with the
stated nonzero denominators. The unique resulting world at that
width has

$$
\begin{gathered}
\epsilon=-\eta_{\rm rec}/\kappa_{\rm rec},\qquad
n=\nu/\kappa_{\rm rec},\qquad t=\theta/\kappa_{\rm rec},\\
q_{\rm s}=\omega/\kappa_{\rm rec},\qquad
j=-4\eta_{\rm rec}/\omega,\qquad
r=\chi_{\rm src}/(\kappa_{\rm rec}\omega),
\end{gathered}
\tag{58.3}
$$

and the gain and drift in (57.5). For each fixed $b>0$,
$F_{\rm rec}$ has total degree at most three in $(p,v,w)$.

**Proof.** Substitute $E=-\eta_{\rm rec}/\kappa_{\rm rec}$ into
(57.1). Its first two affine expressions give $n=\nu/\kappa_{\rm rec}$
and $t=\theta/\kappa_{\rm rec}$. Its third gives
$q_{\rm s}=\omega/\kappa_{\rm rec}$. If $\omega\ne0$, the definitions
of $j$ and $r=n-j$ give exactly the last two formulas in (58.3).
These formulas yield the exact identities

$$
\begin{aligned}
\kappa_{\rm rec}^2
 Q_{\rm rec}(-\eta_{\rm rec}/\kappa_{\rm rec})&=F_{\rm rec},\\
\kappa_{\rm rec}^2\omega^2
 \{b(j-b)-r(1-r)\}&=G_{\rm rec}.
\end{aligned}
\tag{58.4}
$$

Thus the equations in (58.2) are exactly the quadratic consistency
and original source relation, with only nonzero factors cleared.
The guard $E\ne0$ becomes $\eta_{\rm rec}\ne0$, and
$q_{\rm s}\ne0$ becomes $\omega\ne0$. The other tests in (57.2)
become exactly the three inequalities in (58.2). Both directions,
including the full gain and all original readings, now follow from
Theorem 57.2.

For the degree assertion, $X,Y,Z$ are affine in $(p,v,w)$, whereas
the width slopes are constants at fixed $b$. The apparently
fourth-degree contributions in
$\alpha_{\rm w}\eta_{\rm rec}^2-X\eta_{\rm rec}\kappa_{\rm rec}$
are $\alpha_{\rm w}X^2Z^2$ with opposite signs, and cancel.
An exact expression displaying the remaining degree bound is

$$
\begin{aligned}
F_{\rm rec}={}&(XZ+\gamma_{\rm w}Y)
 \bigl[(1-\gamma_{\rm w}\beta_{\rm w})(X-\beta_{\rm w})
       +\alpha_{\rm w}\gamma_{\rm w}Y
       +\alpha_{\rm w}\beta_{\rm w}Z\bigr]\\
&-Y(\alpha_{\rm w}Z+\gamma_{\rm w}\beta_{\rm w}-1)^2.
\end{aligned}
\tag{58.5}
$$

The first factor has degree at most two and its bracket at most one;
the last term has degree at most three. Affine substitution preserves
this bound. Finally the positive defining denominators noted in
Definition 58.1 justify numerator clearing on $b>0$. $\square$

Theorem 58.2 treats the rational branch only. To obtain the complete
width reconstruction one must also retain the exceptional quadratic
case 3 of Theorem 57.2; case 2 contributes no world. Even on the
rational branch, common numerator roots of $F_{\rm rec},G_{\rm rec}$
are not worlds until $b>0$, $\kappa_{\rm rec}\ne0$, both remaining
nonzero guards and all strict inequalities in (58.2) have been checked.
A projected eliminant can lose these guards or contain roots from an
exceptional branch, so an eliminant root alone is never a sufficient
world criterion.

## 59. The original independent J and M pairs over all widths

**Definition 59.1 (All-width reconstruction set).** Let
$\mathcal R(p,v,w)$ consist of every retained reconstruction of
Theorem 57.2 over all $b>0$, with its complete source, drift and gain.
Write $x\sim y$ when their triples $(b,r,\epsilon)$ coincide.
By Lemma 48.1 this is exactly equality of complete worlds; it is
not equality of an acquired observable or an extra experiment.
For such a reconstruction put

$$
\mathfrak a(x)=24+\epsilon+(T+2j+4r)
 (\mathsf C_7+\mathsf A_7\epsilon+35t).
\tag{59.1}
$$

Here $t=\epsilon/n$ by Lemma 56.2. By (54.4), $\mathfrak a(x)$
is the literal terminal-J reading at clock seven of the same whole
gain used in every other row.

**Theorem 59.2 (Full independent-pair equivalence).** The original
predicate (53.1) is equivalent to the existence of real
$p\ne24,v,w_0,w_1,w_*$ and reconstructions satisfying

$$
\begin{gathered}
x_0\in\mathcal R(p,v,w_0),\qquad
x_1\in\mathcal R(p,v,w_1),\\
x_2,x_3\in\mathcal R(p,v,w_*),\\
x_0\not\sim x_1,\qquad x_2\not\sim x_3,\qquad
\mathfrak a(x_0)=\mathfrak a(x_1).
\end{gathered}
\tag{59.2}
$$

There is no condition between the two pairs. In particular they may
overlap, $w_0,w_1$ need not be equal to one another or to $w_*$, and
the J pair's common value need not equal $w_*$. Their acquired
readings share exactly the same $p,v$ and the same specified earlier
record. Width equality within or between the pairs is not imposed.

**Proof.** Starting from (53.1), set
$w_0=m(W_{J0})$, $w_1=m(W_{J1})$ and
$w_*=m(W_{M0})=m(W_{M1})$. Apply Theorem 57.2 at each world's
own width to obtain $x_0,x_1,x_2,x_3$. Its bijection preserves
complete-world distinctness, and (59.1) is the original J reading,
so every condition in (59.2) follows.

Conversely, each reconstruction in (59.2) gives a complete world
in the same entire $C(p,v)$ by Theorem 57.2. The two stipulated
inequivalences give the two distinct-world pairs, and (59.1) gives
the J collision. The last two reconstructions have the same terminal-M
value $w_*$ by their definition. These are exactly (53.1), with
no identification between the two pairs and no equality required
between their common terminal answers. $\square$

Thus an M pair at arbitrary widths is specified exactly by two
inequivalent legal reconstructions for one shared $(p,v,w)$.
Different widths already imply inequivalence. At the same width,
Corollary 57.3 gives the exact two-root test. In either case the
independent J pair remains the separate condition in (59.2), with
its own two terminal-M values $w_0,w_1$ retained independently.

## 60. Fixed-width information, all-width coverage and mathematical sources

Theorem 47.2 adds necessary actual-pair identities at a common width,
the derived distinctions $d_1\ne d_2$ and $n_1\ne n_2$, their sign
relation, and the exclusion of every common width $b\ge\rho$.
These are consequences for distinct worlds sharing $p,v,m$, without
a proportional-gain assumption. They neither give a sufficient
source construction below $\rho$ nor exclude unequal-width M pairs.
For an equal-width pair reconstructed in Section 57, all those
necessary identities still apply, in addition to its complete
source filters. No cutoff is imposed on an individual world or
on the arbitrary-width reconstruction set.

Theorems 57.2 and 58.2 instead give exact source-compatible
reconstruction for every width $b>0$ and every prescribed
$p\ne24,v,w$, with both necessity and the complete-world converse.
They include equal and unequal widths, the full $\Lambda=0$ parent
branch, sampled gain zeros, repeated gain roots, lower degrees and
zero drift wherever the original rows permit them. Positivity of
$T,U,H_2$, the rational branch guards, the exceptional quadratic
case and the strict source tests are all part of this assertion.
No whole gain is replaced by independently chosen samples.

The remaining existence question is satisfiability of (59.2).
Neither a new actual witness for its independent pairs nor a global
obstruction is supplied by the reconstruction criteria. In
particular no M crossing is asserted on the four-world J locus of
Section 40. The J-separation and same-pair double-zero questions for
the known two-world component are not settled by these criteria.
The local forbidden-base intersection of Sections 42–46 remains
confined to its stated scope and does not make $p=24$ admissible
in (59.2).

The complete-world convention, traces and zero-safe parent are those
of *FIB common-parent geometry and two exact mixed children*,
Definitions 1.1–1.3 and Theorem 2.1, with parent parameters
$\beta=1/8$ and $a_{\rm parent}=24/5$. Their precise specialization
is already given in Sections 48–49. The affine lift, $H_i$,
positive-width rank and cofactor line are exactly Sections 49–50;
the fixed-width information remains Theorem 47.2 and Sections 51–53.
These results are used through (54.2)–(55.6), rather than repeated
as separate parent or cofactor proofs.

The explicit inverse, product consistency equations, positive
polynomial remainder, exhaustive strict-source reconstruction,
rational width equations and cubic total-response-degree cancellation
are those of *Exact cross-width reconstruction of a terminal-M
response triple*, Sections 3–5, under the correspondence (54.3).
Its Section 6 gives the independent-pair formulation expressed in
(59.2). Fixed-node interpolation and elementary matrix and polynomial
identities suffice for the displayed reconstruction proofs. The
criteria concern exactly the original complete worlds and literal
clock readings; source coordinates are never acquired observations.

## 追加锚（本行以下为增补区）

## 61. Exceptional reconstruction in the existing whole-world coordinates

Keep the complete original domain of Definitions 1.1–1.2 and the full parent of Lemma 48.1. All statements below use the chronological left-product word $J,M,J,M,M,M$, clocks $0,\ldots,6$ with record $(0,24,147/5,24,18,p,v)$, and both alternatives at clock seven. The source is strictly $P(r,b)$ with $0<r<1,b>0$; each world retains its single whole nonzero real gain of degree at most three and its fixed real drift. No regular-chart or gain-genericity assumption is added.

Use $T,U,j,n,\epsilon,\Lambda,D_{\rm par}$ from Section 48, $\mathsf C_i,\mathsf A_i$ from Section 49, $H_i$ from (47.2), and $\alpha_{\rm w},\beta_{\rm w},\gamma_{\rm w},X,Y,Z,\kappa_{\rm rec},\eta_{\rm rec}$ from Sections 55–56. Introduce only the following source-polynomial notation:

$$
\begin{gathered}
\mathcal J=b^2+r(1-r)=bj,\qquad \mathcal N=\mathcal J+rb=bn,\\
S=(8b-1)(2+5b),\qquad
\Pi=(b^2+8b+4)\mathcal J\mathcal N-2TUb(\mathcal J+\mathcal N).
\end{gathered}
\tag{61.1}
$$

Here $\mathcal N$ is the source polynomial called $N$ in Sections 31–38; the degree-ten polynomial below is instead $N_{\rm exc}$. Precisely, $\Pi=\widehat D/5=D_\Lambda$, where $\widehat D$ is Definition 2.1's circuit denominator and $D_\Lambda$ is Section 13's denominator. Thus the local scalar alias $D$ in Section 31 is $5\Pi$, and its $H=bD$ is $5b\Pi$. None of these is $D_{\rm par}$. The parameter $\beta_{\rm w}$ is a width slope, not the parent parameter $\beta=1/8$.

Multiplying the already proved parent equation (48.2) by positive source factors gives, without cancelling $\Pi$,

$$
\Lambda=\frac{2\Pi}{TU\mathcal J\mathcal N},\qquad
D_{\rm par}=\frac{6S}{5TU},\qquad
\epsilon\Pi=-\frac35S\mathcal J\mathcal N.
\tag{61.2}
$$

Its converse and the entire gain remain exactly (48.3), including $\Pi=0$. For an actual parent world, take the response transform (55.3) with $(p,v,w)=(p(W),v(W),m(W))$ and set

$$
K(W)=\alpha_{\rm w}\epsilon(1/n-\gamma_{\rm w})
       +\gamma_{\rm w}\beta_{\rm w}-1.
\tag{61.3}
$$

This scalar is unrelated to the kernel vector $K_{\rm w}$ of Section 50 or the source alias $K=S$ of Section 31. Under the notation of *Two width graphs for the actual exceptional terminal-M reconstruction*, its $(e,\alpha,\beta,\gamma,V,C_i,A_i,\kappa,\eta)$ are respectively $(\epsilon,\alpha_{\rm w},\beta_{\rm w},\gamma_{\rm w},\mathsf V,\mathsf C_i,\mathsf A_i,\kappa_{\rm rec},\eta_{\rm rec})$ here. Lemma 55.2 gives

$$
X=n-\alpha_{\rm w}\epsilon,\quad
Y=\epsilon n-\beta_{\rm w}\epsilon,\quad
Z=\epsilon/n-\gamma_{\rm w}\epsilon;\qquad
\kappa_{\rm rec}=K(W),\quad \eta_{\rm rec}=-\epsilon K(W).
\tag{61.4}
$$

The last equality follows by expanding $XZ+\gamma_{\rm w}Y$. Thus an actual world is in the exceptional reconstruction case $\kappa_{\rm rec}=\eta_{\rm rec}=0$ exactly when $K(W)=0$. These identities reuse Sections 48–56; they do not introduce another parent or response transform. In particular the definition of $K$ makes sense also when $p=24$ or $\epsilon=0$.

## 62. A degree-ten polynomial and its two simple width graphs

Define

$$
N_{\rm exc}(b,r)=\sum_{i=0}^{10}c_i(r)b^i,
\tag{62.1}
$$

with the following exact coefficients:

$$
\begin{aligned}
c_0={}&-295618904r^2(r-1)^2,\\
c_1={}&-56r(r-1)(56840601r^2-62119510r+5344533),\\
c_2={}&-2r(2061224799r^3-5713986426r^2+5060221231r-1505782768),\\
c_3={}&-2(1228278046r^4-4517780891r^3+3830122638r^2-1149025595r-149646924),\\
c_4={}&-2(1288200024r^4-3804678094r^3+1799167195r^2+1079818433r-1555269056),\\
c_5={}&-2(275975799r^4-1840151622r^3+1701917076r^2+1004193479r-2132156621),\\
c_6={}&3(10277197r^4+163429472r^3+391180106r^2-927087035r+895942616),\\
c_7={}&-30831591r^3+538008065r^2-2450563658r+2732038598,\\
c_8={}&-28933182r^2-439223240r+881739723,\\
c_9={}&25675591r+44775124,\qquad c_{10}=-1898409.
\end{aligned}
\tag{62.2}
$$

**Theorem 62.1 (Two simple positive width roots).** For every $0<r<1$, $N_{\rm exc}(\cdot,r)$ has exactly two positive roots counted with multiplicity. Both are simple. They define real analytic functions on $(0,1)$ with

$$
0<b_-(r)<1<24<b_+(r)<64.
\tag{62.3}
$$

**Proof.** For any polynomial $f$ of degree at most $d$, write its Bernstein expansion as

$$
f(r)=\sum_{j=0}^d B_j^{(d)}(f)\binom dj r^j(1-r)^{d-j},\qquad
B_j^{(d)}(f)=\sum_{i=0}^j\frac{\binom ji}{\binom di}[r^i]f.
\tag{62.4}
$$

The basis weights are nonnegative and sum to one on $[0,1]$. The degree-four coefficient vectors for $c_3,\ldots,c_9$, in increasing Bernstein index, are

$$
\begin{array}{c|l}
 c_3&(299293848,1747613291/2,171611897,451600048,1516105452)\\
 c_4&(3110538112,5141257791/2,4292991842/3,3187964629/2,2385522996)\\
 c_5&(4264313242,7524433005/2,2692814071,3952363517/2,1980443778)\\
 c_6&(2687827848,7970050287/4,2985574697/2,5244897129/4,1601227068)\\
 c_7&(2732038598,4238795367/2,9578548679/6,4621647957/4,788651414)\\
 c_8&(881739723,771933913,657305906,537855702,413583301)\\
 c_9&(44775124,204776087/4,115225839/2,256127269/4,70450715).
\end{array}
\tag{62.5}
$$

Their respective minima are $171611897$, $4292991842/3$, $3952363517/2$, $5244897129/4$, $788651414$, $413583301$, $44775124$, all positive. For $c_2$, use the two half-interval substitutions. The degree-four Bernstein vectors in $u$ for $c_2(u/2)$ and $c_2((1+u)/2)$ are exactly

$$
\begin{aligned}
&(0,376445692,3974475377/12,1771247359/8,1172125273/8),\\
&(1172125273/8,573003187/8,379742861/12,126046231,196646328).
\end{aligned}
\tag{62.6}
$$

On the first half, at every $r>0$ some positive-coefficient basis weight is positive; on the second half all five coefficients are positive. Consequently $c_i(r)>0$ for $2\le i\le9$ and $0<r<1$. Also $c_0(r)<0$ and $c_{10}<0$. In descending width powers the signs therefore have exactly two changes, regardless of the sign or vanishing of $c_1$. Descartes' rule bounds the total multiplicity of positive roots by two.

For completeness the endpoint Bernstein vectors $\bigl(B_j^{(4)}(N_{\rm exc}(w,\cdot))\bigr)_{j=0}^4$ are

$$
\begin{aligned}
w=1:\quad &(14018628086,25935013341/2,14774821713/2,28579017491/4,8950732643),\\
w=24:\quad &(108058548295265882112,109982226112023108240,\\
&\hspace{12mm}335457005514538140692/3,113564937595636352256,115216701333695424000),\\
w=64:\quad &(-1121726995611910666190848,-1039744754329513585587840,\\
&\hspace{12mm}-958712655450236766356196,-878655155132242056408064,-799595227342287555297280).
\end{aligned}
\tag{62.7}
$$

Thus at width one the coefficient range is $[28579017491/4,14018628086]$; at width $24$ it is $[108058548295265882112,115216701333695424000]$; at width $64$ it is $[-1121726995611910666190848,-799595227342287555297280]$. Formula (62.4) applied to (62.2) verifies every entry of (62.5)–(62.7) directly. In particular $N_{\rm exc}(1,r)>0$, $N_{\rm exc}(24,r)>0$, and $N_{\rm exc}(64,r)<0$. Since $N_{\rm exc}(0,r)=c_0(r)<0$, the intermediate value theorem gives a root in $(0,1)$ and one in $(24,64)$. The bound counting multiplicity forces precisely these two roots, each of multiplicity one. The analytic implicit-function theorem then gives local analytic root functions; uniqueness in the disjoint intervals identifies them on overlaps, giving the two analytic graphs throughout $(0,1)$. $\square$

## 63. The zero-safe exceptional identity and actual-world multiplicity

**Lemma 63.1 (Actual exceptional identity).** Every complete parent world satisfies

$$
N_{\rm exc}(b,r)=TH_2(b)^2\Pi(b,r)K(W),
\tag{63.1}
$$

including the singular sources $\Pi=0$.

**Proof.** Substitution of (55.1) in the following expression and collection in powers of $b$ gives exactly the eleven coefficients in (62.2):

$$
N_{\rm exc}=TH_2^2\left\{\Pi(\gamma_{\rm w}\beta_{\rm w}-1)
 -\frac35\alpha_{\rm w}S\mathcal J\mathcal N(1/n-\gamma_{\rm w})\right\}.
\tag{63.2}
$$

This is a rational identity with only positive-width denominators, and its right side simplifies to the displayed polynomial. In an actual world, (61.2) replaces $-(3/5)S\mathcal J\mathcal N$ by $\epsilon\Pi$. The resulting expression is $TH_2^2\Pi K(W)$. No division by $\Pi$, $\epsilon$ or any gain sample occurs. $\square$

**Theorem 63.2 (Candidate graphs and actual multiplicities).** Every actual exceptional parent world has $b=b_-(r)$ or $b=b_+(r)$. For each fixed $0<r<1$ there are at most two such complete worlds, with at most one above either candidate width. There is exactly one above the upper candidate width $b_+(r)$.

**Proof.** An actual $K(W)=0$ implies $N_{\rm exc}=0$ by (63.1), so Theorem 62.1 gives the two candidate widths. At any source with $\Pi\ne0$, (61.2) fixes the unique real number

$$
\epsilon=-\frac{3S\mathcal J\mathcal N}{5\Pi}.
\tag{63.3}
$$

Lemma 48.1 then fixes its complete world. Conversely at a candidate root with $\Pi\ne0$ this world is exceptional by (63.1), since $T,H_2,\Pi$ are nonzero.

If an actual source has $\Pi=0$, (61.2) and $\mathcal J\mathcal N>0$ force $S=0$, hence $b=1/8$. All real $\epsilon$ remain allowed at this singular parent source by Lemma 48.1, but the exceptional equation (61.3) is affine in $\epsilon$. Its constant at this width is

$$
\left.(\gamma_{\rm w}\beta_{\rm w}-1)\right|_{b=1/8}
=-\frac{207798820547}{2293695144600}\ne0.
\tag{63.4}
$$

Substituting the $H_i$ and $T,U$ in (55.1) gives this fraction. Therefore the affine equation has at most one solution even if its slope $\alpha_{\rm w}(1/n-\gamma_{\rm w})$ vanishes; in that event it has none. This controls all singular actual sources without cancelling $\Pi$. It proves the asserted upper bound at each candidate and hence the bound of two at fixed $r$.

For $b\ge24$, the strict source inequalities give $j>b$ and $n>j>b$, so

$$
\Lambda=1+6/T+1/U-4/j-4/n>1-8/b>0,
\qquad \Pi>0.
\tag{63.5}
$$

At $b_+(r)\in(24,64)$, (63.3) therefore constructs exactly one complete world and (63.1) makes it exceptional. Lemma 48.1 ensures a strict source and a whole nonzero gain of degree at most three, with its one fixed drift. The lower graph is only a candidate graph at singular sources; no assertion that both roots always support actual worlds is needed or made. $\square$

In particular an actual exceptional world has neither $1\le b\le24$ nor $b\ge64$. A root of $N_{\rm exc}$ alone is not an unrestricted sufficient world criterion at a singular source: its parent equation and the affine $K$ equation remain necessary there.

## 64. Literal interpolation and a negative fifth response at every large width

**Theorem 64.1 (Negative response for $b\ge24$).** Every complete parent world with $b\ge24$ has its literal fifth-M response $p(W)<0$.

**Proof.** Positivity (63.5) justifies division by $\Pi$. Use the following explicit interpolation circuit, with local symbols $D_i^{\rm int}$ distinct from $D_{\rm par}$:

$$
\begin{aligned}
D_0^{\rm int}&=-120\Pi+3S\mathcal J\mathcal N,&
D_1^{\rm int}&=3S\mathcal N b,\\
D_2^{\rm int}&=3(49b+34)\mathcal J\mathcal N-54Ub(\mathcal J+\mathcal N),&
D_3^{\rm int}&=3S\mathcal J b,\\
B_5^{\rm int}&=-4D_0^{\rm int}+15D_1^{\rm int}-20D_2^{\rm int}+10D_3^{\rm int},\\
P_p^{\rm int}&=-bD_0^{\rm int}+(bU+\mathcal N)B_5^{\rm int}.
\end{aligned}
\tag{64.1}
$$

Precisely $D_i^{\rm int}=\widehat C_i$ for $0\le i\le3$, $B_5^{\rm int}=\widehat B_5$ and $P_p^{\rm int}=P_p$ of Definition 2.1, because $\widehat D=5\Pi$. Substituting (63.3) into the samples (48.3) yields

$$
d=-\frac{D_0^{\rm int}}{5\Pi},\qquad
 g(i)=\frac{D_i^{\rm int}}{5\Pi}\ (0\le i\le3),\qquad
 g(5)=\frac{B_5^{\rm int}}{5\Pi},\qquad
 p(W)=\frac{P_p^{\rm int}}{5b\Pi}.
\tag{64.2}
$$

The clock-five interpolation weights are literally $(-4,15,-20,10)$ from (48.5), and the trace is $U+n=(bU+\mathcal N)/b$. Thus (64.2) computes the original response of the same whole gain, rather than a shifted-clock or independently sampled model.

Write $P_p^{\rm int}(24+u,r)=\sum_{k=0}^7q_k(r)u^k$. The correct uniform degree bound in $r$ is six. In fact the high-degree part of this numerator is exactly

$$
[r^5]P_p^{\rm int}=96(2b+3)(8b-1),\qquad
[r^6]P_p^{\rm int}=-96(8b-1).
\tag{64.3}
$$

In particular a degree-four Bernstein expansion of the full $q_0,q_1,q_2$ is unavailable. To distinguish a degree-four truncation from the full coefficient, set $\widetilde q_k=\sum_{i=0}^4[r^i]q_k\,r^i$. Expansion of (64.1) gives

$$
q_0-\widetilde q_0=935136r^5-18336r^6,\quad
q_1-\widetilde q_1=75840r^5-768r^6,\quad
q_2-\widetilde q_2=1536r^5;\qquad q_k=\widetilde q_k\ (k\ge3).
\tag{64.4}
$$

Here are both the degree-four truncation maxima and the valid full degree-six Bernstein maxima, computed by (62.4):

| $k$ | $\max_j B_j^{(4)}(\widetilde q_k)$ | $\max_j B_j^{(6)}(q_k)$ |
| --- | ---: | ---: |
| $0$ | $-1071543670080$ | $-1071542753280$ |
| $1$ | $-308693734464$ | $-308693659392$ |
| $2$ | $-38126986656$ | $-38126985120$ |
| $3$ | $-2617160436$ | $-2617160436$ |
| $4$ | $-107831886$ | $-107831886$ |
| $5$ | $-2666766$ | $-2666766$ |
| $6$ | $-36654$ | $-36654$ |
| $7$ | $-216$ | $-216$ |

The complete degree-six coefficient vectors, making the sign certificate explicit, are

$$
\begin{aligned}
q_0:\quad &(-1429603540992,-1368180995904,-6536864982144/5,\\
&-6236219379768/5,-5939280021888/5,-1129269632256,-1071542753280),\\
q_1:\quad &(-398205517824,-382920178128,-1838838438848/5,\\
&-1763793047784/5,-1689516284352/5,-323211681024,-308693659392),\\
q_2:\quad &(-47450375424,-45865673021,-221462179566/5,\\
&-427313143281/10,-41182947938,-39647965604,-38126985120),\\
q_3:\quad &(-3135061440,-6094902039/2,-14801672339/5,\\
&-57474591417/20,-13938269829/5,-2702125141,-2617160436),\\
q_4:\quad &(-124013550,-242578899/2,-592879842/5,-1158732891/10,\\
&-113181594,-221002131/2,-107831886),\\
q_5:\quad &(-2936403,-5782471/2,-14230796/5,-28011741/10,\\
&-13781401/5,-5422955/2,-2666766),\\
q_6:\quad &(-38526,-38214,-37902,-37590,-37278,-36966,-36654),\\
q_7:\quad &(-216,-216,-216,-216,-216,-216,-216).
\end{aligned}
\tag{64.5}
$$

To verify these entries using only the displayed circuit, expand (64.1), substitute $b=24+u$, and apply $B_j^{(6)}(q_k)=\sum_{i=0}^j\binom ji[r^iu^k]P_p^{\rm int}(24+u,r)/\binom6i$. All seven coefficients in each row are strictly negative, so each $q_k(r)<0$ on $[0,1]$. For $u\ge0$ the sum $\sum q_k(r)u^k$ is strictly negative, already because $q_0<0$. The denominator $5b\Pi$ in (64.2) is positive by (63.5). Therefore $p(W)<0$ for all $b\ge24$. $\square$

## 65. Nonnegative bases, rational reconstruction and the remaining joint target

**Corollary 65.1 (Exceptional-width and rational-branch cut).** The unique actual exceptional world above $b_+(r)$ has $p(W)<0$. In any entire acquired child $C(p,v)$ with real $p\ge0,v$, every exceptional world has $0<b<1$. If in addition $p\ne24$, then for every real terminal value $w$ and every actual world $W\in C(p,v)$ with $m(W)=w$ and $b(W)\ge1$, its Section 55 transform satisfies

$$
\kappa_{\rm rec}\ne0,\qquad
\epsilon=-\eta_{\rm rec}/\kappa_{\rm rec}.
\tag{65.1}
$$

**Proof.** The upper existence is Theorem 63.2, and its width exceeds $24$, so Theorem 64.1 makes its fifth response negative. The same theorem excludes every actual parent of width $b\ge24$ from a nonnegative fifth response. Theorem 63.2 leaves only the lower graph for an exceptional world in $C(p,v)$, hence $b<1$. An actual world with $b\ge1$ is consequently nonexceptional; (61.4) gives $\kappa_{\rm rec}=K(W)\ne0$, and its actual consistency equation (56.2) yields (65.1). $\square$

The hypotheses $p\ge0$ and $p\ne24$ in the rational-branch conclusion are both retained: the former excludes the actual upper exceptional graph; the latter is the base hypothesis for the exhaustive reconstruction of Sections 57–58. Formula (65.1) never replaces the equations and strict source filters of Theorem 57.2 or (58.2). In particular $b>0$, the nonzero rational denominators, $\eta_{\rm rec}\ne0$, $\omega\ne0$, $n>0$, $j>b$, $0<r<1$, and the source relation must still hold as specified there. A polynomial root or a rational value without those tests is not a world. Exceptional reconstruction below width one is not excluded at nonnegative bases. For negative bases both candidate graphs must remain available, subject to actual-world conditions; lower-graph existence at every $r$ is not asserted.

The complete-world parent and traces are those of [*FIB common-parent geometry and two exact mixed children*](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md), Definitions 1.1–1.3 and Theorem 2.1, specialized exactly as in Sections 48–49. The all-width slopes, transform, consistency equations and strict filters are Sections 54–60. The new exceptional polynomial, two-root sign argument, affine treatment of singular sources and upper-world construction are the mathematical content of *Two width graphs for the actual exceptional terminal-M reconstruction*. Its literal interpolation circuit is (64.1); the full degree-six coefficient certificate (64.3)–(64.5) supplies the negative-response proof with all high-degree terms retained. Descartes' rule, Bernstein convexity and the analytic implicit-function theorem are the classical tools used here. No literature-priority or formal-kernel claim is part of these ordinary results.

The original target is still exactly (53.1), equivalently (59.2): some real $p\ne24,v$ and independently distinct J and M pairs in one entire $C(p,v)$, with overlap permitted and independent common terminal values. The cut above provides neither a joint witness nor a global obstruction, and does not establish a terminal-M collision on the known J locus. The full singular parent and all gain-degenerate actual worlds remain in the unrestricted statements, with the exceptional affine case, polynomial-root multiplicities and all source/pole guards retained. No source parameter becomes an acquired observation, and no port, reset, copy or clock change is introduced.

## 追加锚（本行以下为增补区）


## 66. The entire child at the strict M-pair base

**Definition 66.1 (A full-base rectangle).** Retain the exact worlds $W_2,W_3$ and base $(p_*,v_*)$ of Theorem 1.3. The following terminating decimals are exact rationals:

$$
\begin{aligned} p_c&=1.8057126623901333037270156505198680057908,\\ v_c&=172.2471680963226343182328451692107608678058,\\ \delta&=10^{-24},\qquad \mathcal B_*=[p_c-\delta,p_c+\delta]\times[v_c-\delta,v_c+\delta]. \end{aligned} \tag{66.1}
$$

**Theorem 66.2 (Entire-child inventory and J separation).** One has $(p_*,v_*)\in\mathcal B_*$. For every $(p,v)\in\mathcal B_*$, the entire original child $C(p,v)$ has at most two worlds, and its actual terminal-J response is injective. At the exact M-pair base,

$$
\boxed{C(p_*,v_*)=\{W_2,W_3\}.} \tag{66.2}
$$

Consequently the independently selected J pair required in Section 8 does not exist at this particular M-pair base. This conclusion concerns the whole original domain over $\mathcal B_*$, with no fixed terminal-M value and no restriction on gain degree, gain samples, drift, singular sources, exceptional sources or source width. It makes no exclusion outside this rectangle.

**Definition 66.3 (The reused unsaturated carrier).** Use exactly $x=n/U$, the tail interpolant, $a_0,a_1,a_2$, $f,\mathcal K,A,B_f,C_f$, and $\alpha,\zeta,F_0,R$ of [Support X, equations (12.8)–(12.12)](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_X.md). In particular

$$
\begin{gathered} D=x(x+1)(x+2),\\ F_0=405x^3+(975-18p+5v)x^2+(90-36p+5v)x-480,\\ \operatorname{Res}_d(f,\mathcal K)=256D^8F_0^2R,\\ f\mid A^3\mathcal K-(\alpha d+\zeta). \end{gathered} \tag{66.3}
$$

The normalization of $R$ is the exact quotient in that source; its $x$-degree is eighteen. Every actual world has $x>0$, satisfies $f=\mathcal K=0$, and therefore satisfies

$$
F_0(x,p,v)R(x,p,v)=0,\qquad \alpha(x,p,v)d+\zeta(x,p,v)=0. \tag{66.4}
$$

The factor $F_0$ is retained, including its zero-drift possibility. Neither the regular-source denominator nor the fixed-terminal inverse's quartic $K$ is divided out in (66.4).

The all-world necessity is also immediate from the supplied original equations. For the tail interpolant $H=Ug$, clock zero gives $dU=-H_0$, and clock two gives $B_0U=H_2$, where $B_0=294/5-2d-H_2$. These imply $f=0$. Substituting $H_0=-dU$ and $xH_1-(24-d)=rH_1/U$ into $\mathcal K$ expresses it as the cleared original rank-one source relation. This proves $\mathcal K=0$ without division by $d$, so (66.4) applies also when $d=0$ and on singular sources.

**Lemma 66.4 (Uniform exhaustive root rectangles).** Put $\rho=10^{-12}$ and $\sigma=10^{-24}$. In the following table each row specifies the exact Gaussian-rational centre $c=\operatorname{Re}c+i\operatorname{Im}c$. On every real $(p,v)\in\mathcal B_*$, the indicated polynomial has exactly one zero in the rectangle

$$
|\operatorname{Re}(x-c)|\le\rho,\qquad |\operatorname{Im}(x-c)|\le\rho. \tag{66.5}
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
\mathscr P(c+z,p_c+u,v_c+w)=\sum_{\ell,j,k}a_{\ell jk}z^\ell u^j w^k. \tag{66.6}
$$

For a real rational $q$, define

$$
\operatorname{rnd}_{100}(q)=10^{-100}\lfloor10^{100}q+1/2\rfloor,
$$

and extend it componentwise to Gaussian rationals. Set $\gamma=\operatorname{rnd}_{100}(1/a_{100})$, use $|a+ib|_1=|a|+|b|$, and put $s=\rho$ at real centres and $s=2\rho$ otherwise. The finite rational sums

$$
\begin{aligned} \eta&=\sum_{j,k}|\gamma a_{0jk}|_1\delta^{j+k},\\ q&=|1-\gamma a_{100}|_1+ \sum_{\substack{\ell\ge1,j,k\ge0\\(\ell,j,k)\ne(1,0,0)}} \ell|\gamma a_{\ell jk}|_1s^{\ell-1}\delta^{j+k} \end{aligned} \tag{66.7}
$$

satisfy, at every one of the twenty-one centres,

$$
\eta<2\cdot10^{-25},\qquad q<3\cdot10^{-9},\qquad \eta+q\rho<\rho,\qquad \frac{\eta}{1-q}<\sigma. \tag{66.8}
$$

These are rational inequalities obtained from (66.3), (66.6) and the printed centres. The coefficient of $x^{18}$ in $R$ is uniformly enclosed by

$$
1873044541936855184250 \le[x^{18}]R\le1873044541936855184251, \tag{66.9}
$$

and the leading coefficient of $F_0$ is $405$.

For fixed real $(p,v)\in\mathcal B_*$, apply the map $x\mapsto x-\gamma\mathscr P(x,p,v)$ to the real interval $[c-\rho,c+\rho]$ when $c$ is real, and to the rectangle (66.5) otherwise. In each case (66.7) bounds its centre displacement and its derivative's induced maximum norm, so (66.8) makes it a contraction into the interior. For a complex rectangle, $|z|_1\le2\rho$ explains the value of $s$; complex multiplication has maximum-norm operator bound $|\cdot|_1$. The contraction argument of Theorem 4.3 therefore gives one zero in each specified set, real at every real centre, with displacement at most $\eta/(1-q)$.

All eighteen $R$ rectangles are pairwise disjoint, as are the three $F_0$ rectangles: for every two relevant centres, at least one coordinate differs by more than $2\rho$. Since the degrees remain eighteen and three by (66.9), these distinct zeros exhaust the roots and give exactly one complex zero in each rectangle, including those with real centres. In particular this conclusion is not inferred from an incomplete list of numerical roots. ∎

**Lemma 66.5 (Whole-source filters and separated J answers).** Over $\mathcal B_*$, only the $R$ roots with indices 12 and 13 can represent original worlds. Each determines at most one entire world. The possible terminal-J values at these two roots satisfy

$$
\begin{aligned} 994.82015996&\le a_{12}\le994.82015997,\\ 964.05127114&\le a_{13}\le964.05127115,\\ -30.76889&\le a_{13}-a_{12}\le-30.76888<0. \end{aligned} \tag{66.10}
$$

Proof. The first eight $R$ rectangles and first two $F_0$ rectangles have negative real roots. The last four $R$ rectangles are nonreal, since their imaginary coordinate intervals exclude zero. The remaining seven real roots have positive $x$.

At every one of these positive-root boxes, evaluation gives the uniform pole separations

$$
|\alpha|>10^{14},\qquad \chi>40,\qquad |H_1|>1/25,\qquad |U|>1/10. \tag{66.11}
$$

Here, with $d=-\zeta/\alpha$, use exactly the zero-safe inverse of Support X, (12.8)–(12.9):

$$
\begin{gathered} h_3=(24-d)/x,\quad h_4=18-d,\quad h_5=(p-d)/(x+1),\quad h_6=(v-d)/(x+2),\\ H_0=20h_3-45h_4+36h_5-10h_6,\\ H_1=10h_3-20h_4+15h_5-4h_6,\\ H_2=4h_3-6h_4+4h_5-h_6,\quad H_7=-h_3+4h_4-6h_5+4h_6,\\ B_0=294/5-2d-H_2,\qquad \chi=d^2+B_0^2,\\ U=(-dH_0+B_0H_2)/\chi,\quad b=(U-1)/2,\\ j=U(24-d)/H_1,\qquad r=xU-j,\\ a=d+\left(\frac{1+1/U}{2}+2x+\frac{2r}{U}\right)H_7. \end{gathered} \tag{66.12}
$$

The last expression is the actual terminal J response because $H_7=Ug(7)$. In particular it uses the same whole gain as the acquired rows.

All following endpoints are exact rationals and enclose the entire smaller root boxes of Lemma 66.4, uniformly over $\mathcal B_*$. The strict source tests eliminate every positive candidate except indices 12 and 13:

| Polynomial | Index | $b$ enclosure | $r$ enclosure | Source test |
| --- | --- | --- | --- | --- |
| $R$ | 8 | $[27.49075770,27.49075771]$ | $[34.55368867,34.55368868]$ | r>1 |
| $R$ | 9 | $[-3.17686801,-3.17686800]$ | $[0.67614939,0.67614940]$ | b<0 |
| $R$ | 10 | $[-0.43583281,-0.43583280]$ | $[0.86342730,0.86342731]$ | b<0 |
| $R$ | 11 | $[-0.55207424,-0.55207423]$ | $[-0.29745094,-0.29745093]$ | b<0 |
| $R$ | 12 | $[0.04091698,0.04091699]$ | $[0.63750339,0.63750340]$ | retained |
| $R$ | 13 | $[0.04078295,0.04078296]$ | $[0.39999999,0.40000001]$ | retained |
| $F0$ | 2 | $[-1.45169779,-1.45169778]$ | $[-0.21103470,-0.21103469]$ | b<0 |

For explicit finite interval evaluation of (66.11)–(66.12), use the endpoint operations of Definition 4.1 with grid denominator $10^{120}$. For $\alpha$ and $\zeta$, first enclose their centre values and apply

$$
P(y)\in P(y_c)+\sum_{k=1}^3(y_k-y_{c,k})\,\partial_kP(Y), \quad Y=[c-\sigma,c+\sigma]\times\mathcal B_*,\quad y_c=(c,p_c,v_c). \tag{66.13}
$$

Evaluate each polynomial by multivariate Horner evaluation in the variable order $x,p,v$, with coefficients accumulated in decreasing power order. Formula (66.13) follows from the fundamental theorem of calculus on the convex box and retains the dependence needed for these enclosures. Then evaluate the displayed rational inverse in its factored order. The nonzero lower bounds in (66.11), together with $x>0$, permit every reciprocal. This gives the table and (66.10) by outward rational interval operations.

Every actual endpoint satisfies (66.4). Thus $\alpha\ne0$ fixes its drift at its root, including the retained $F_0$ branch. The four tail samples then fix its entire polynomial $H$, and (66.12) fixes $U,b,r$ and $g=H/U$. Hence there is at most one entire original world at each retained root, with no extra drift branch at any candidate root. ∎

Proof of Theorem 66.2. Evaluate the first-source circuit of Definition 2.1 on the originally defining box $X$ of Section 3. The resulting inclusions give

$$
|p(2/5,b_0)-p_c|<10^{-30},\qquad |v(2/5,b_0)-v_c|<10^{-30} \quad\text{throughout }X. \tag{66.14}
$$

Therefore the exact $(p_*,v_*)$ lies in $\mathcal B_*$. This assertion concerns the exact root of Section 4, rather than a rounded replacement base.

For any $(p,v)\in\mathcal B_*$ one has $p\ne24$. Every complete original world in its entire child supplies an $x>0$ satisfying (66.4), regardless of its terminal-M response. Lemmas 66.4–66.5 leave only two root slots, each representing at most one whole world, and their actual J values are disjoint by (66.10). Thus $|C(p,v)|\le2$ and the terminal J map is injective on the whole child.

At $(p_*,v_*)$, Theorem 1.3 already supplies the two distinct entire worlds $W_2,W_3$. The upper bound proves (66.2). Their diagonal intervals identify $W_2$ with slot 13 and $W_3$ with slot 12. Consequently no independently chosen equal-J pair can be supplied by any other companion at that base. ∎

The new `repo-derived` content is the full-base root cover, its guarded two-slot inventory and J separation on $\mathcal B_*$. The parent, literal response circuit, zero-safe inverse and carrier identities are reused with their original assumptions. Fixed-node interpolation and the contraction argument are the classical tools already cited in Section 7. The proof neither applies the seven-world bound with a free M response nor prescribes a common M response for the inventory.

This strengthens the selected-pair statement of Section 8 to an entire-child exclusion at its particular exact base. The unrestricted independent-pair question still has both $p\ne24$ and $v$ free outside $\mathcal B_*$. The longer-history reconstruction of [the literal cubic matrix-polynomial frame](FIB_LITERAL_CLOCK_CUBIC_MATRIX_POLYNOMIAL_FRAME.md), Problem 6.5, does not settle that remaining same-seven-read incidence.

## 追加锚（本行以下为增补区）
