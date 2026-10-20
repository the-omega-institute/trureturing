# FIB entire singular-response children and terminal-M injectivity

## 1. The original worlds and the two exact children

**Definition 1.1 (Inherited model and notation).** Let
[O](https://github.com/the-omega-institute/trureturing/blob/3185602855df9c3f79f19ae165404ef1885777c3/docs/develop/theory/FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md)
denote *FIB common-parent geometry and two exact mixed children* at the
specified revision. References to its entries retain their original
numbering. A complete legal world is exactly the triple of O,
Definitions 1.1–1.3:

$$
W=(P(r,b),g,d),\qquad
P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},\qquad
0<r<1,\quad b>0,\quad
0\ne g\in\mathbb R[s],\quad\deg g\le3,\quad d\in\mathbb R.
\tag{1.1}
$$

There is no upper bound on either positive offdiagonal $b$ or
$c=r(1-r)/b$. Each world has one entire polynomial $g$ and one fixed
drift $d$. Different worlds may have different gains and drifts.
Lower degrees, sampled zeros, repeated gain roots and zero drift
are included. The action matrices and original readings are

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
Q_0=I,\quad Q_i=E_iQ_{i-1},\quad
y_i=d+g(i)\operatorname{tr}(Q_iP),\quad E_i\in\{J,M\}.
\tag{1.2}
$$

The clocks are $0,\ldots,7$, with the initial read included. Write
$\mathcal F(H)$ for all complete legal worlds realizing the literal
history $H$, and fix throughout

$$
H_4=(0,J,24,M,147/5,J,24,M,18).
\tag{1.3}
$$

Put $j=b+c$, $n=j+r$, $T=1+b$ and $U=1+2b$. The actual functions
after the fifth action M are precisely O (1.7):

$$
\begin{aligned}
p(W)&=d+(U+n)g(5),\\
u_M(W)&=d+(2U+n)g(6),\\
f_{MJ}(W)&=d+(T+2j+4r)g(7),\\
f_{MM}(W)&=d+(3U+2n)g(7).
\end{aligned}
\tag{1.4}
$$

Thus $f_{MJ}$ and $f_{MM}$ follow the acquired sixth action M.
All four functions use the same $P,g,d$ of their argument.
The inherited singularity coordinate is
$\Lambda=1+6/T+1/U-4/j-4/n$ (O (2.1)); a source is called
nonsingular when $\Lambda\ne0$.

**Definition 1.2 (Exact inherited parameter).** Let $z_J$ be the
unique zero of the six-coordinate system $F_J$ of O (8.1) in its
original rational box $\mathcal B_J$. Set

$$
p_J=p(W_0(z_J)),
\tag{1.5}
$$

exactly as in O (8.4). Its existence and uniqueness are the premises
of O, Theorem 8.1. The interval transport of O, Theorem 26.2, concerns
this same number. No rational center or interval is substituted
for (1.5).

**Definition 1.3 (Singular-response children).** Let $r_-,r_+$ be
exactly the two strict roots designated by O, Theorem 4.2, of

$$
\Phi(t)=438272t^4-931328t^3+540800t^2-50728t-853.
\tag{1.6}
$$

For $\sigma\in\{-,+\}$ retain the exact function $s_\sigma(p)$ of
O, Definition 29.1, evaluated at $r_\sigma$. Define

$$
\mathcal C_v=\mathcal F(H_4,M,p_J,M,v),\qquad
\mathcal C_\sigma=\mathcal C_{s_\sigma(p_J)}.
\tag{1.7}
$$

Let $S_\sigma(p)$ denote the unique complete fifth-response lift at
$(r_\sigma,1/8)$ supplied by O, Theorems 12.3 and 29.2. In particular
$u_M(S_\sigma(p))=s_\sigma(p)$. This is an equality of actual
responses, rather than a choice of a center from a response interval.

**Definition 1.4 (Original simultaneous-pair predicate).** For a real
$v$, let $\mathfrak W(v)$ mean

$$
\begin{gathered}
\exists W_0,W_1,W_2,W_3\in\mathcal C_v:\qquad
W_0\ne W_1,\quad W_2\ne W_3,\\
f_{MJ}(W_0)=f_{MJ}(W_1),\qquad
f_{MM}(W_2)=f_{MM}(W_3).
\end{gathered}
\tag{1.8}
$$

Labels in different pairs may coincide. This is the complete-world
same-child obligation of O (32.1), with the two within-pair
distinctness guards retained. The original existence question is
$\exists v\in\mathbb R:\mathfrak W(v)$.

## 2. Exact rational parameters and singular-response enclosures

**Definition 2.1 (Parameter and response boxes).** Use exactly the
parameter interval of O, Definition 26.1:

$$
\begin{gathered}
p_c=\frac{2744214237392974691433531179656369993836520133001835}{10^{50}},
\qquad h_p=10^{-40},\qquad K=[p_c-h_p,p_c+h_p],\\
h_v=10^{-32},\qquad V_\sigma=[v_{c,\sigma}-h_v,v_{c,\sigma}+h_v].
\end{gathered}
\tag{2.1}
$$

The centers $v_{c,\sigma}$ are the following exact rational numbers.

| $\sigma$ | Numerator of $v_{c,\sigma}$, denominator $10^{40}$ |
| --- | --- |
| $-$ | $1198704988209101765516388199570039880582574$ |
| $+$ | $1387528570305159695377932790043712687263296$ |

O, Theorem 26.2, supplies $p_J\in K$. The two boxes $V_-,V_+$ are
disjoint and both are below $142$. They serve as enclosures only.

**Definition 2.2 (Rational inclusion operations).** For intervals with
rational endpoints use

$$
\begin{aligned}
[a,b]+[c,d]&=[a+c,b+d],&-[a,b]&=[-b,-a],\\
[a,b][c,d]&=[\min(ac,ad,bc,bd),\max(ac,ad,bc,bd)],\\
1/[c,d]&=[1/d,1/c]&&\text{only when }cd>0.
\end{aligned}
\tag{2.2}
$$

Every operation is rational and exact. Polynomial expressions are
expanded before evaluation. For $Q(r,p,v)$ use descending-power
Horner evaluation in $v$ inside $p$ inside $r$; for $Q(r,b)$ use
$b$ inside $r$; and for $Q(t,p)$ use $p$ inside $t$. Insert every
missing zero coefficient. These orders mean, for example, evaluating
$\sum_a r^a\sum_b p^b\sum_c q_{abc}v^c$ from the innermost sum
outwards. Exact polynomial divisions in a definition precede interval
evaluation. For displayed factored rational expressions use their
displayed parentheses and sum unparenthesized terms from left to
right. A coarser displayed denominator guard establishes
nonvanishing; subsequent division uses the interval of the original
expression unless a coarsened input box is explicitly prescribed.

**Definition 2.3 (Fine brackets for the two singular sources).** For
the following integers $n_\sigma$ put

$$
J_\sigma=[n_\sigma/10^{45},(n_\sigma+1)/10^{45}].
\tag{2.3}
$$

| $\sigma$ | $n_\sigma$ | Signs of $\Phi$ at the lower and upper endpoints |
| --- | --- | --- |
| $-$ | $134815875067638653367017716061081265110899687$ | $-,+$ |
| $+$ | $902449681772056265377872651296542856186276499$ | $+,-$ |

Each interval lies inside its corresponding designated interval in
O (4.6). For $t\in J_\sigma$, $p\in K$, define in this order

$$
\begin{aligned}
j(t)&=1/8+8t(1-t),&n(t)&=j(t)+t,\\
A_5(t)&=1+(n(t)+5/4)(4+160/9-15/j(t)-10/n(t)),\\
e(t,p)&=(p-24)/A_5(t),\\
a_6(t)&=50-36/j(t)-20/n(t),\\
s(t,p)&=24+24(5/2+n(t))
        +e(t,p)\{1+(5/2+n(t))a_6(t)\}.
\end{aligned}
\tag{2.4}
$$

The positive $j,n$ and the nonzero $A_5$ guards in Lemma 2.4 precede
their reciprocals. At $t=r_\sigma$, (2.4) is exactly O (29.1), since
$T=9/8$ and $10+45/T=50$.

**Lemma 2.4 (Actual response enclosures).** Each $r_\sigma$ lies in
the interior of $J_\sigma$, and

$$
s_\sigma(p_J)\in\operatorname{int}V_\sigma.
\tag{2.5}
$$

More generally (2.2) applied to (2.4) on the full $J_\sigma\times K$
gives positive $j,n$, the following $A_5$ guards, and an interval
strictly inside $V_\sigma$ for $s$.

| $\sigma$ | Strict enclosing interval for $A_5$ | Enclosure for $s$ |
| --- | --- | --- |
| $-$ | $(-908/1000,-907/1000)$ | $\operatorname{int}V_-$ |
| $+$ | $(-5217/1000,-5216/1000)$ | $\operatorname{int}V_+$ |

Proof. Descending-power rational evaluation of the quartic (1.6) at
the two endpoints of each interval (2.3) gives the signs in its
table. These intervals lie strictly inside O (4.6); O, Theorem 4.2,
identifies their interior roots with the designated $r_-,r_+$.

For the interval inclusions, substitute the two rational endpoints
from (2.3) into the rules (2.2), in the order (2.4). The intervals
are inside $(0,1)$, so $j=1/8+8t(1-t)>0$ and $n=j+t>0$; the same
interval operations also give positive lower endpoints. Compute
$A_5$ before $e$. Its resulting interval is strictly between the
endpoints displayed in the corresponding row, and excludes zero.
Use its uncoarsened interval in $e$, then compute $a_6$ and $s$.
The resulting lower endpoint exceeds $v_{c,\sigma}-10^{-32}$ and
the upper endpoint is less than $v_{c,\sigma}+10^{-32}$. Equations
(2.1)–(2.4) and the integers in Definition 2.3 specify all the
rational operations and strict comparisons in these inclusions.
Specialize at the unchanged $p_J\in K$ and $t=r_\sigma$ to obtain
(2.5). ∎

## 3. Inherited elimination and an exact specialization identity

**Definition 3.1 (Fixed inherited polynomials).** Throughout, use
exactly $\mathsf A,\mathsf B,D_\Lambda$ of O (20.1),
$\mathcal L_0,\mathcal L_1$ of its ordered minors (20.4)–(20.5),
and $R=R_{18}$ of its Definition 24.1. Thus $R$ has the $668$
specified integer monomials $c_{abc}r^ap^bv^c$, with coordinate
degrees $(18,7,7)$; its scale and sign are fixed by O (20.3).
There is no primitive-part or sign renormalization. Put

$$
\begin{gathered}
\Psi_2(r)=4r^2-2r-1,\qquad
\Psi_4(r)=625r^4-1000r^3+50r^2+260r+36,\\
E(r)=\Psi_2(r)\Psi_4(r)\Phi(r).
\end{gathered}
\tag{3.1}
$$

In particular the fixed polynomial identity is

$$
\operatorname{Res}_b(\mathsf A,\mathsf B)
=52488000r^{11}(r-1)^9E(r)R(r,p,v).
\tag{3.2}
$$

O, Theorem 20.2, supplies, for every actual nonsingular world of
$\mathcal F(H_4,M,p,M,v)$, the necessary relations

$$
\mathsf A(r,b,p)=\mathsf B(r,b,v)=0,\qquad
E(r)R(r,p,v)=0,\qquad
\mathcal L_1(r,p,v)b+\mathcal L_0(r,p,v)=0.
\tag{3.3}
$$

The fixed determinants and minors in that theorem remain valid
under every coefficient specialization. Their common-finite-root
implications divide only by $72900r^6(r-1)^4\ne0$ in the strict
domain, as shown in O (20.10). Sylvester elimination is the
standard method of Cox–Little–O'Shea,
*[Ideals, Varieties, and Algorithms](https://doi.org/10.1007/978-3-319-16721-3)*,
Chapter 3; the actual polynomial and minor normalizations here
are the cited definitions of O.

**Definition 3.2 (Cubic response representative).** Define

$$
\begin{aligned}
D={}&1731744020342106665,\\
A_s(t)={}&13656112734222647296t^3
 -33583101098863014400t^2\\
&+20502976421172725312t-3401342974535580372,\\
B_s(t)={}&-327746705621343535104t^3
 +916826043674607172160t^2\\
&-616757003572777087368t+31411654798932835643,\\
\widehat s(t,p)={}&-\frac{3\{pA_s(t)+B_s(t)\}}D.
\end{aligned}
\tag{3.4}
$$

This $D$ is the positive integer in (3.4), distinct from
$D_\Lambda$ and from other chart denominators in O.

**Lemma 3.3 (Exact singular projection).** For either designated
strict $\Phi$ root and every real $p$,

$$
\widehat s(r_\sigma,p)=s_\sigma(p),\qquad
R(r_\sigma,p,s_\sigma(p))=0.
\tag{3.5}
$$

The polynomial certificate for the second equality is

$$
\operatorname{rem}_r\bigl(D^7R(r,p,\widehat s(r,p)),\Phi(r)\bigr)=0
\quad\text{in }\mathbb Q[p][r].
\tag{3.6}
$$

Proof. Use the polynomials $j(t),n(t)$ of (2.4), and form

$$
\begin{aligned}
F_5(t)&=j(t)n(t)+(n(t)+5/4)
       \{(196/9)j(t)n(t)-15n(t)-10j(t)\},\\
F_6(t)&=j(t)n(t)+(n(t)+5/2)
       \{50j(t)n(t)-36n(t)-20j(t)\},\\
F_0(t)&=84+24n(t).
\end{aligned}
\tag{3.7}
$$

Then $F_5=jnA_5$, and the source expression is

$$
s(t,p)=F_0(t)+(p-24)F_6(t)/F_5(t).
\tag{3.8}
$$

At the designated roots $j,n>0$ and $A_5\ne0$ by O,
Theorems 4.2 and 29.2, also with the explicit guards of Lemma 2.4.
Thus this division is defined.

For an explicit remainder convention reduce every occurrence of
$t^4$ by

$$
t^4\equiv
\frac{931328t^3-540800t^2+50728t+853}{438272}\pmod\Phi,
\tag{3.9}
$$

in descending order of degree. Equivalently, let $q_0=1,q_1=t$,
$q_2=t^2,q_3=t^3$, and for $m\ge4$ put

$$
q_m=\frac{931328q_{m-1}-540800q_{m-2}
                  +50728q_{m-3}+853q_{m-4}}{438272}.
\tag{3.10}
$$

The remainder of $\sum_m a_mt^m$ is $\sum_m a_mq_m$.
Substitution of (3.4) and (3.7) gives the following coefficient
vectors of remainders, in the order $(1,t,t^2,t^3)$:

| Polynomial | Remainder vector modulo $\Phi$ |
| --- | --- |
| $DF_6+3A_sF_5$ | $(0,0,0,0)$ |
| $D(F_0F_5-24F_6)+3B_sF_5$ | $(0,0,0,0)$ |

These two rational polynomial reductions give, respectively, the
coefficient of $p$ and the constant coefficient of
$DF_5(s-\widehat s)$. Since $DF_5\ne0$ at the two roots, they
prove the first equality of (3.5).

For the other reduction, use exactly the integer table of O,
Definition 24.1, and form the polynomial

$$
\mathcal P(r,p)=
\sum_{a,b,c}c_{abc}r^ap^b
 [-3\{pA_s(r)+B_s(r)\}]^cD^{7-c}.
\tag{3.11}
$$

All indices here range over the supplied $668$ nonzero terms.
Their $b+c\le7$, so $\deg_p\mathcal P\le7$.
Expansion followed by (3.10) gives the complete remainder table

| Power $\ell$ | Remainder vector of $[p^\ell]\mathcal P$ |
| --- | --- |
| $0$ | $(0,0,0,0)$ |
| $1$ | $(0,0,0,0)$ |
| $2$ | $(0,0,0,0)$ |
| $3$ | $(0,0,0,0)$ |
| $4$ | $(0,0,0,0)$ |
| $5$ | $(0,0,0,0)$ |
| $6$ | $(0,0,0,0)$ |
| $7$ | $(0,0,0,0)$ |

Equations (3.4), (3.10)–(3.11) fix every rational addition and
multiplication in this table. Since $\mathcal P=D^7R(r,p,\widehat s)$,
the table proves (3.6) identically in $p$. Evaluation at $r_\sigma$
and division by the nonzero integer $D^7$ prove the second equality
of (3.5). This argument uses the exact source response at the exact
root. ∎

## 4. Exhaustive strict roots of the specialized eliminant

**Definition 4.1 (Centered coefficients and their Bernstein bounds).**
For each sign expand the inherited polynomial exactly as

$$
R(r,p_c+x,v_{c,\sigma}+y)=\sum_{i,j}A_{ij,\sigma}(r)x^iy^j.
\tag{4.1}
$$

In terms of O's integer coefficients this means

$$
A_{ij,\sigma}(r)=
\sum_{\substack{a\ge0\\b\ge i,\ c\ge j}}c_{abc}
 \binom bi p_c^{b-i}\binom cj v_{c,\sigma}^{c-j}r^a.
\tag{4.2}
$$

Every mixed parameter term is retained. For each closed interval
$[a,b]$ in Lemma 4.2, write

$$
\begin{gathered}
A_{ij,\sigma}(a+(b-a)t)
 =\sum_{\ell=0}^{18}a_{ij\ell,\sigma}t^\ell,\\
\beta_{ijk,\sigma}=\sum_{\ell=0}^k
 a_{ij\ell,\sigma}\frac{\binom k\ell}{\binom{18}\ell},
\qquad
e_{k,\sigma}=\sum_{i+j>0}
 |\beta_{ijk,\sigma}|h_p^ih_v^j.
\end{gathered}
\tag{4.3}
$$

Degree eighteen is used even if a specialized polynomial has lower
degree. For a parameter pair in $K\times V_\sigma$, the $k$th
Bernstein coefficient lies in
$[\beta_{00k,\sigma}-e_{k,\sigma},
  \beta_{00k,\sigma}+e_{k,\sigma}]$.

**Lemma 4.2 (Complete parameter-uniform projected-root cover).**
For every $(p,v)\in K\times V_-$, $R(r,p,v)$ has exactly four
strict real roots. For every $(p,v)\in K\times V_+$ it has exactly
six. Each root is simple. The following tables give their exhaustive
partition certificates. A word lists the signs of all nineteen
Bernstein coefficients in increasing $k=0,\ldots,18$ order.

| $\sigma=-$: closed interval | Sign word | Variation |
| --- | --- | --- |
| $[0,1/8]$ | `-------------++++++` | $1$ |
| $[1/8,1/4]$ | `++-----------------` | $1$ |
| $[1/4,1/2]$ | `-------------------` | $0$ |
| $[1/2,3/4]$ | `-------------------` | $0$ |
| $[3/4,7/8]$ | `-------------------` | $0$ |
| $[7/8,113/128]$ | `-++++++++++++++++++` | $1$ |
| $[113/128,57/64]$ | `++++++++++---------` | $1$ |
| $[57/64,29/32]$ | `-------------------` | $0$ |
| $[29/32,15/16]$ | `-------------------` | $0$ |
| $[15/16,1]$ | `-------------------` | $0$ |

| $\sigma=+$: closed interval | Sign word | Variation |
| --- | --- | --- |
| $[0,1/4]$ | `-----------------++` | $1$ |
| $[1/4,1/2]$ | `+++----------------` | $1$ |
| $[1/2,3/4]$ | `-------------------` | $0$ |
| $[3/4,7/8]$ | `-----------------++` | $1$ |
| $[7/8,57/64]$ | `+++++++++++++------` | $1$ |
| $[57/64,115/128]$ | `---++++++++++++++++` | $1$ |
| $[115/128,29/32]$ | `++++++++++---------` | $1$ |
| $[29/32,15/16]$ | `-------------------` | $0$ |
| $[15/16,1]$ | `-------------------` | $0$ |

For each entry the corresponding rational inequalities are

$$
\begin{cases}
\beta_{00k,\sigma}>e_{k,\sigma},&\text{for a }+,\\
\beta_{00k,\sigma}<-e_{k,\sigma},&\text{for a }-,
\end{cases}
\qquad
|\beta_{00k,\sigma}|>10^{20}e_{k,\sigma}.
\tag{4.4}
$$

Proof. Form (4.2) from O, Definition 24.1, substitute each pair of
rational interval endpoints into (4.3), and compare the resulting
rationals. This gives exactly the nineteen-character words and all
$361$ strict inequalities (4.4). Thus every coefficient has its
displayed sign throughout the full independent parameter box.

To obtain the root inference, use the standard Bernstein identity

$$
R(a+(b-a)t,p,v)=\sum_{k=0}^{18}
 B_k\binom{18}k t^k(1-t)^{18-k}.
\tag{4.5}
$$

Substitution $t=z/(1+z)$, equivalently $r=(a+bz)/(1+z)$, makes
the coefficients of $(1+z)^{18}R((a+bz)/(1+z),p,v)$ equal to
$\binom{18}kB_k$. These binomial factors are positive. Descartes'
rule therefore bounds the number of roots in $(a,b)$, counting
multiplicity, by the variation of the row. In every variation-one
row, $B_0$ and $B_{18}$ have opposite signs, so the intermediate
value theorem gives a root. The multiplicity bound makes it unique
and simple. Variation-zero rows have no root. Endpoints are
nonzero because their values are $B_0,B_{18}$.

The partitions cover $[0,1]$, so their four and six variation-one
rows exhaust the strict real roots. This is the coefficient
transformation of O (21.1)–(21.2) applied with the different boxes
(2.1). Bernstein conversion and Descartes' rule are standard
univariate real-root tools; see Basu–Pollack–Roy,
*[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2)*,
on univariate root counting. Their use here requires only the
displayed transformation and the finite rational inequalities. ∎

**Definition 4.3 (Narrow intervals and root labels).** For each row
below define

$$
I_{\sigma,k}=[N_{\sigma,k}/10^{25},(N_{\sigma,k}+1)/10^{25}].
\tag{4.6}
$$

The label $k$ increases with $r$. Let
$\alpha_{\sigma,k}(p,v)$ denote the root from Lemma 4.2 in the
corresponding variation-one row.

| $\sigma$ | $k$ | $N_{\sigma,k}$ | Lower, upper endpoint signs |
| --- | --- | --- | --- |
| $-$ | $1$ | $870374766460419822450684$ | $-,+$ |
| $-$ | $2$ | $1348158750676386533670177$ | $+,-$ |
| $-$ | $3$ | $8751593064408970016673663$ | $-,+$ |
| $-$ | $4$ | $8868850192203220901114316$ | $+,-$ |
| $+$ | $1$ | $2356956036283584824292879$ | $-,+$ |
| $+$ | $2$ | $2812331876017891114204072$ | $+,-$ |
| $+$ | $3$ | $8701168059907408538202362$ | $-,+$ |
| $+$ | $4$ | $8860263567063972994346931$ | $+,-$ |
| $+$ | $5$ | $8915857857158046936407412$ | $-,+$ |
| $+$ | $6$ | $9024496817720562653778726$ | $+,-$ |

**Lemma 4.4 (Narrow localization and exact root identification).**
Uniformly on $K\times V_\sigma$, each
$\alpha_{\sigma,k}(p,v)$ lies in the interior of
$I_{\sigma,k}$. At the exact parameters,

$$
\alpha_{-,2}(p_J,s_-(p_J))=r_-,\qquad
\alpha_{+,6}(p_J,s_+(p_J))=r_+.
\tag{4.7}
$$

Proof. Each narrow interval lies strictly inside its corresponding
variation-one row of Lemma 4.2, by rational endpoint comparisons.
At an endpoint $x$ of (4.6), evaluate $A_{00,\sigma}(x)$ exactly
and form

$$
\varepsilon_\sigma(x)=\sum_{i+j>0}
 |A_{ij,\sigma}(x)|h_p^ih_v^j.
\tag{4.8}
$$

For all twenty endpoints, $\varepsilon_\sigma(x)<
|A_{00,\sigma}(x)|$, and the latter value has the sign specified
in Definition 4.3. Equations (4.2), (4.6), (4.8) are the exact
rational endpoint certificate. The signs hold on the full parameter
box. Opposite signs and the uniqueness in Lemma 4.2 place the
one root inside each narrow interval.

Rational endpoint comparisons also give
$J_-\subset\operatorname{int}I_{-,2}$ and
$J_+\subset\operatorname{int}I_{+,6}$. Lemma 3.3 makes
$r_\sigma$ an exact $R$ root at $(p_J,s_\sigma(p_J))$;
Lemma 2.4 places this parameter pair in $K\times V_\sigma$.
The uniqueness just proved gives (4.7). ∎

## 5. All base-factor roots and every possible linear lift

**Definition 5.1 (Strict base-root boxes).** The four strict roots
of $E$ are enclosed by the following closed intervals
$B_\eta=[c_\eta/10^{40}-10^{-30},c_\eta/10^{40}+10^{-30}]$.
These are exactly the strict-root boxes in the parameter-independent
$E$ certificate of O, Theorem 30.2; only those root boxes are used.

| $\eta$ | Factor | $c_\eta$ |
| --- | --- | --- |
| $\Phi_-$ | $\Phi$ | $1348158750676386533670177160610812651109$ |
| $\Psi_2$ | $\Psi_2$ | $8090169943749474241022934171828190588602$ |
| $\Psi_4$ | $\Psi_4$ | $8685711315796832210935933386297551290576$ |
| $\Phi_+$ | $\Phi$ | $9024496817720562653778726512965428561863$ |

O, Theorem 21.2, supplies the strict-root counts $1,1,2$ for
$\Psi_2,\Psi_4,\Phi$, respectively. Thus these four boxes cover
every strict root of $E$, independently of $p,v$.

**Lemma 5.2 (Nonzero base minors and forced source widths).**
For every $r\in B_\eta$, $p\in K$, $v\in V_\sigma$, the
following bounds hold:

$$
\ell\,10^q<\mathcal L_1(r,p,v)<u\,10^q.
\tag{5.1}
$$

| $\sigma$ | $\eta$ | $\ell$ | $u$ | $q$ |
| --- | --- | --- | --- | --- |
| $-$ | $\Phi_-$ | $-393$ | $-392$ | $24$ |
| $-$ | $\Psi_2$ | $-877$ | $-876$ | $20$ |
| $-$ | $\Psi_4$ | $-655$ | $-654$ | $19$ |
| $-$ | $\Phi_+$ | $-388$ | $-387$ | $20$ |
| $+$ | $\Phi_-$ | $419$ | $420$ | $25$ |
| $+$ | $\Psi_2$ | $-159$ | $-158$ | $20$ |
| $+$ | $\Psi_4$ | $-127$ | $-126$ | $18$ |
| $+$ | $\Phi_+$ | $902$ | $903$ | $19$ |

No nonsingular world in either $\mathcal C_\sigma$ can have
$E(r)=0$.

Proof. Expand the determinant-defined $\mathcal L_1$ of O
(20.4)–(20.5) and evaluate it on each entire
$B_\eta\times K\times V_\sigma$ by Definition 2.2. Its rational
lower and upper endpoints are strictly between the corresponding
bounds (5.1). Every interval excludes zero before any quotient is
taken. These eight calculations are specified by the fixed minors,
the four rational boxes and (2.1)–(2.2).

At the exact base roots use the inherited polynomial identities
O (21.4), valid for arbitrary $p,v$:

$$
\begin{aligned}
\mathcal L_0-\tfrac12\mathcal L_1&\equiv0\pmod{\Psi_2},\\
\mathcal L_0-\tfrac25\mathcal L_1&\equiv0\pmod{\Psi_4},\\
\mathcal L_0+\tfrac18\mathcal L_1&\equiv0\pmod\Phi.
\end{aligned}
\tag{5.2}
$$

Together with (3.3) and the nonzero minors, they force
$b=-1/2,-2/5,1/8$, respectively. The first two are illegal.
For the third, O (4.9) gives
$\Lambda=\Phi(r)/(960jn)=0$, contrary to nonsingularity.
All strict $E$ roots are covered, so none remains in that branch. ∎

**Lemma 5.3 (All projected-root lift bounds).** On each entire
$I_{\sigma,k}\times K\times V_\sigma$, the following table gives
strict bounds $\ell10^q<\mathcal L_1<u10^q$ and a closed enclosing
interval $[B_L,B_U]/10^6$ for $-\mathcal L_0/\mathcal L_1$.
The bounds require no root or legality premise.

| $\sigma$ | $k$ | $\ell$ | $u$ | $q$ | $B_L$ | $B_U$ |
| --- | --- | --- | --- | --- | --- | --- |
| $-$ | $1$ | $-550$ | $-549$ | $21$ | $189704$ | $189705$ |
| $-$ | $2$ | $-393$ | $-392$ | $24$ | $124999$ | $125001$ |
| $-$ | $3$ | $-510$ | $-509$ | $19$ | $-353252$ | $-353251$ |
| $-$ | $4$ | $267$ | $268$ | $17$ | $-595468$ | $-595467$ |
| $+$ | $1$ | $848$ | $849$ | $24$ | $223805$ | $223806$ |
| $+$ | $2$ | $-141$ | $-140$ | $25$ | $161056$ | $161057$ |
| $+$ | $3$ | $-108$ | $-107$ | $18$ | $-388368$ | $-388367$ |
| $+$ | $4$ | $104$ | $105$ | $17$ | $247293$ | $247294$ |
| $+$ | $5$ | $-944$ | $-943$ | $14$ | $-596556$ | $-596555$ |
| $+$ | $6$ | $902$ | $903$ | $19$ | $124999$ | $125001$ |

Proof. Expand $\mathcal L_0,\mathcal L_1$ with their exact
ordered-minor definitions, retaining their prescribed divisor.
Descending Horner evaluation by Definition 2.2 on each full box
gives the displayed strict $\mathcal L_1$ bounds. Each excludes
zero, so apply the reciprocal rule to the uncoarsened
$\mathcal L_1$ interval and multiply it by the negated
$\mathcal L_0$ interval. The quotient interval is contained in
the displayed $[B_L,B_U]/10^6$. Thus every row is a finite rational
inclusion from the fixed inherited polynomials and the explicitly
listed endpoints, without a nonvanishing assumption at an
unspecified root. ∎

## 6. Exhaustive coverage of complete worlds in each selected child

**Theorem 6.1 (Singular worlds and all possible regular companions).**
The entire child $\mathcal C_-$ contains exactly the singular world
$S_-(p_J)$ among its $\Lambda=0$ members and at most one
nonsingular world. Any such nonsingular world has source coordinate
$r=\alpha_{-,1}(p_J,s_-(p_J))$ and width in
$[189704,189705]/10^6$.

The entire child $\mathcal C_+$ contains exactly $S_+(p_J)$ among
its $\Lambda=0$ members. Every nonsingular member belongs to one
of the three categories $k=1,2,4$, with
$r=\alpha_{+,k}(p_J,s_+(p_J))$ and its width in the corresponding
interval of Lemma 5.3. Each category contains at most one complete
world. Consequently

$$
|\mathcal C_-|\le2,\qquad |\mathcal C_+|\le4.
\tag{6.1}
$$

These are upper bounds; no existence assertion for any regular
projected candidate is included.

Proof. Let $W$ be any member of one selected child. Write
$e=d-24$ and use the zero-safe parent equation of O, Theorem 2.1:

$$
e\Lambda+\frac{24}{5}(b-1/8)B_{\rm coef}=0,\qquad
B_{\rm coef}=\frac{2(2+5b)}{TU}>0.
\tag{6.2}
$$

First suppose $\Lambda=0$. Positivity forces $b=1/8$, and
O (4.9) gives $\Phi(r)=0$. O, Theorem 29.2, identifies every
complete fifth-response lift at this stratum as exactly
$S_-(p_J)$ or $S_+(p_J)$, with actual acquired sixth-M responses
$s_-(p_J)$ and $s_+(p_J)$. Lemma 2.4 puts these responses in
disjoint boxes. Hence only $S_\sigma(p_J)$ belongs to
$\mathcal C_\sigma$, and it does belong by its actual response
equality. The cited reconstruction provides a legal source, one
entire gain and one fixed drift, with a nonzero entire gain forced
by the unequal original $0,24$ rows. This uses actual $u_M$,
not merely the vanishing of $\mathsf A,\mathsf B$ at a singular
base point.

Now suppose $\Lambda\ne0$. O, Theorem 20.2, gives (3.3), including
the necessary finite-root projection under specialization. Since
$0<r<1$, (3.2) leaves $E(r)R(r,p_J,s_\sigma(p_J))=0$.
Lemma 5.2 excludes every strict base-factor possibility in this
nonsingular branch. Thus $r$ is one of the four or six strict $R$
roots exhausted by Lemmas 4.2 and 4.4.

At every one of these roots Lemma 5.3 excludes
$\mathcal L_1=0$ and (3.3) forces the unique possible width
$b=-\mathcal L_0/\mathcal L_1$. The negative-width rows
$(-,3),(-,4),(+,3),(+,5)$ violate $b>0$.
At the exact parameter pair, Lemma 4.4 identifies the rows
$(-,2)$ and $(+,6)$ exactly with $r_-$ and $r_+$.
The $\Phi$ identity (5.2) and the same nonzero minor force
$b=1/8$ at these roots. O (4.9) then forces $\Lambda=0$.
Thus these two projected categories contribute no nonsingular
companion; their actual singular member has already been counted
by its acquired response.

The only possible remaining regular categories are $(-,1)$ and
$(+,1),(+,2),(+,4)$. Each has exactly one projected $r$ coordinate
and at most one $b$. O, Theorem 12.3, gives at most one complete
world at that strict source. With $A_5$ as in O (12.1), its
squared-norm denominator $Z=\Lambda^2+A_5^2>0$ is justified
by O, Lemma 12.2; no auxiliary inverse-chart denominator is
required. It fixes the drift and all four coefficients of the
entire polynomial. In particular it includes every lower-degree,
sampled-zero, repeated-root and zero-drift possibility.

The two branches exhaust all legal worlds. No drift, gain sample,
gain leading coefficient, root difference or specialized minor
has been cancelled without a guard. The determinant implication
holds for every finite real $b$ and therefore covers arbitrarily
large positive $b,c$. The illegal endpoints $r=0,1$ are outside
the original domain. This proves the coverage and the upper
bounds (6.1). ∎

## 7. Separation of all possible actual terminal-M images

**Definition 7.1 (Inherited regular image and singular image).**
For the regular categories use exactly the integer polynomials
$N_m,D_m$ of O (27.1), with $D_m=5bD_\Lambda$ and no common
rescaling. O, Theorem 27.2, identifies their quotient with the
actual terminal function $f_{MM}$ at every nonsingular world.
For the singular sources use (2.4) and put

$$
\begin{aligned}
a_7(t)&=20-70/j(t)+224/3-35/n(t),\\
m_s(t,p)&=24+e(t,p)
 +(15/4+2n(t))\{384/5+e(t,p)a_7(t)\}.
\end{aligned}
\tag{7.1}
$$

At $t=r_\sigma$ this is the actual
$f_{MM}(S_\sigma(p))$. Indeed the one interpolant of O,
Theorem 4.1, gives $g(7)=384/5+e\,a_7$, and the original
seventh-M trace is $3U+2n=15/4+2n$.
The extrapolation is fixed-node Lagrange interpolation with nodes
$0,1,2,3$, as in O (18.3)–(18.4); see Berrut–Trefethen,
*[Barycentric Lagrange Interpolation](https://doi.org/10.1137/S0036144502417715)*,
§2. No independent late gain value is introduced.

**Lemma 7.2 (Guarded response intervals for every retained category).**
For the four possible regular categories, the following bounds
hold on the entire indicated $r,b$ boxes. The columns for the
$b$ input interval and $D_m$ guard are divided by $10^6$.

| $\sigma$ | $k$ | $b$ input interval numerators | $D_m$ guard numerators | Strict interval for $N_m/D_m$ |
| --- | --- | --- | --- | --- |
| $-$ | $1$ | $[189704,189705]$ | $[-65867,-65864]$ | $(487,488)$ |
| $+$ | $1$ | $[223805,223806]$ | $[-29605,-29595]$ | $(601,603)$ |
| $+$ | $2$ | $[161056,161057]$ | $[67164,67174]$ | $(621,623)$ |
| $+$ | $4$ | $[247293,247294]$ | $[-157947,-157782]$ | $(611,613)$ |

On the entire $J_\sigma\times K$, the singular expression (7.1)
satisfies

$$
m_s(J_-,K)\subset(510,512),\qquad
m_s(J_+,K)\subset(624,626).
\tag{7.2}
$$

Proof. For each regular row expand the exact inherited $N_m,D_m$
after the polynomial division by $T$ in O (27.1). Evaluate them
in the $b$-inside-$r$ Horner order of Definition 2.2 on the
closed box $I_{\sigma,k}\times[B_L,B_U]/10^6$ from the row.
The resulting $D_m$ interval is contained in its displayed guard,
which excludes zero. Divide the uncoarsened numerator and
denominator intervals only after this check. The quotient has
lower endpoint strictly above the displayed lower response bound
and upper endpoint strictly below the upper bound. This specifies
all four rational range calculations from O (27.1) and the
displayed input endpoints.

For each singular row compute $j,n,A_5,e$ on $J_\sigma\times K$
in the order (2.4), with the nonzero guards of Lemma 2.4 preceding
division. Compute $a_7$ and then (7.1) by (2.2). The resulting
lower and upper endpoints are strictly inside the two intervals
(7.2). Thus these are whole-box inclusions for the exact
expressions, with all inversions guarded.

For actual retained regular worlds, O, Theorem 27.2, makes these
quotients their actual $f_{MM}$. For the actual singular lift,
Definition 7.1 gives the same conclusion. All responses therefore
come from the original clock-seven reading of a complete world. ∎

## 8. Injectivity on both entire original children

**Theorem 8.1 (Entire-child terminal-M injectivity).** For each
$\sigma\in\{-,+\}$ and all complete legal worlds
$W,W'\in\mathcal C_\sigma$,

$$
f_{MM}(W)=f_{MM}(W')\quad\Longrightarrow\quad W=W'.
\tag{8.1}
$$

The statement includes every regular companion of the singular
world and every legal stratum of the original model (1.1).
It is source-specific repository-derived mathematics
(`repo-derived`), using the named ordinary mathematical results
of O and the standard tools cited at their uses above.

Proof. Theorem 6.1 covers every world of $\mathcal C_-$ by the
one possible regular category $k=1$ and the one singular world
$S_-(p_J)$. By Lemma 7.2 the actual terminal-M values of these
two categories lie in $(487,488)$ and $(510,512)$, respectively.
The intervals are disjoint. Each category has at most one complete
world, so equal $f_{MM}$ values force the same category and then
the identical complete triple.

For $\mathcal C_+$, Theorem 6.1 covers every world by the three
possible regular categories $k=1,2,4$ and $S_+(p_J)$. Their actual
terminal-M intervals, in category order, are

$$
(601,603),\qquad(621,623),\qquad(611,613),\qquad(624,626).
\tag{8.2}
$$

These four intervals are pairwise disjoint. Every regular category
has at most one complete world by the unique projected root,
guarded linear lift and O, Theorem 12.3. The singular category
contains exactly its one actual fifth-response lift. Thus equality
of actual terminal-M values again forces the same category and
the same complete triple.

The coverage uses both branches of the zero-safe parent, all strict
base roots and the complete strict $R$ root partitions. It imposes
no bounded-offdiagonal, common-gain-across-worlds or
common-drift-across-worlds hypothesis. The exact specialization
(3.5) identifies the singular projected roots; the root intervals
alone are not used for that equality. No existence or exact count
of the possible regular lifts is required. This proves (8.1) on
each entire acquired child. ∎

**Corollary 8.2 (All supports fail the simultaneous terminal guards).**
For each $\sigma\in\{-,+\}$, $\mathfrak W(s_\sigma(p_J))$ is
false. More precisely, for either sign and
every finite or infinite $S\subseteq\mathcal C_\sigma$,

$$
\neg L_1(S,(H_4,M,p_J,M,s_\sigma(p_J))),
\tag{8.3}
$$

where $L_k$ is the original recursion of O, Definition 1.2.

Proof. By Theorem 8.1 every actual terminal-M response fiber in
$S$ has at most one complete world. Hence every such fiber fails
$L_0$, whose guard is cardinality at least two. The terminal-M
conjunct in the definition of $L_1$ fails. Empty and singleton
supports fail its initial nonsingleton guard as well.
In (1.8) the required distinct pair $W_2,W_3$ with equal
$f_{MM}$ therefore cannot exist. The argument permits the two
terminal pairs to overlap and makes no four-distinct-world
assumption. It covers pairs not involving the singular world
because Theorem 8.1 covers the entire child. ∎

## 9. The precise remaining original obligation

**Corollary 9.1 (Every hypothetical witness child is nonsingular).**
If $\mathfrak W(v)$ holds for a real $v$, then

$$
\begin{gathered}
v\notin\{s_-(p_J),s_+(p_J)\},\qquad Q(p_J,v)=0,\\
\Lambda(W)\ne0\quad\text{for every }W\in\mathcal C_v,
\end{gathered}
\tag{9.1}
$$

where $Q$ is exactly the determinant-defined polynomial of O,
Definition 28.1. The universal quantifier in the last line covers
the entire hypothetical acquired child, including worlds outside
the four labeled witnesses.

Proof. Corollary 8.2 excludes the two displayed actual responses.
If any world in the entire remaining $\mathcal C_v$ had
$\Lambda=0$, O, Theorem 29.2, would make its actual sixth-M
response one of exactly $s_-(p_J),s_+(p_J)$, contradicting its
membership in this child. Thus every world there is nonsingular.
The terminal-M pair required by $\mathfrak W(v)$ satisfies the
premise of O, Theorem 31.1. Its two exceptional-response
alternatives have just been excluded, so that theorem gives
$Q(p_J,v)=0$. No further real root is excluded by this argument. ∎

**Definition 9.2 (Scope of the remaining existence question).**
The unresolved original question is the existence of one real
$v$ and complete worlds satisfying (1.8), equivalently O (32.1).
Corollary 9.1 restricts any such witness to the necessary set

$$
\{v\in\mathbb R:Q(p_J,v)=0\}
 \setminus\{s_-(p_J),s_+(p_J)\},
\tag{9.2}
$$

with all its actual worlds in the $\Lambda\ne0$ branch. It does
not assert feasibility or infeasibility at another response, an
exact number of remaining $Q$ roots, or an exact regular-world
cardinality. O, Theorem 23.1, concerns its separately defined
$v_\star$. The uniform statement in
[FIB exact response strip and exclusion of joint collisions](FIB_EXACT_RESPONSE_STRIP_AND_JOINT_COLLISION_EXCLUSION.md),
Theorem 1.3, has $v\in[142,150]$; its singular-response
enclosures are in the
[rational-certificate companion](FIB_EXACT_RESPONSE_STRIP_RATIONAL_CERTIFICATE.md),
Proposition 8.1. The present two exact responses lie below that
strip by Lemma 2.4, and Theorem 8.1 supplies their entire-child
exclusion with their regular companions included.

The inherited finite necessary polynomial uses separating rational
images as explained in O, Section 32; the general method has the
literature background of Rouillier,
*[Solving Zero-Dimensional Systems Through the Rational Univariate Representation](https://doi.org/10.1007/s002000050114)*.
The model-specific specialization (3.5), exhaustive coverage in
Theorem 6.1 and image separation in Theorem 8.1 are the consequences
proved here, without a global-priority assertion. The original
all-real-$v$ existence question, other fifth responses, earlier
ancestors, same-parent $L_3$, root $L_7$, unrestricted cubic
eight-versus-nine recovery or impossibility and full-domain
nine-read sufficiency retain their unresolved scope. No physical
realization or regularity of a strategy is inferred from these
algebraic consequences.

## 追加锚（本行以下为增补区）
