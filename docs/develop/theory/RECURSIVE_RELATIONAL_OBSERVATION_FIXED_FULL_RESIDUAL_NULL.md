# An exact null for the original 155-coefficient full-residual family

## 1. The fixed family and the supported parameter

**Assumption 1.1 (original source and certificate).** Use the original source,
complete carriers, projections, outer domains and certificate system of
[PAIR, Sections 2 and 16.5][PAIR]. In particular,

$$
a=\frac13,\qquad b=\frac25,\qquad
\rho_p=\frac{1116529}{22781250},\qquad
\rho_\beta=\frac{239}{6750},\qquad
C=\frac{11758471}{22781250},\qquad H=\frac{5261}{6750}.
\tag{1.1}
$$

The prior $\mu$ is any fixed finite or countable probability distribution
with $\mu(1),\mu(2)>0$. Whenever the certificate is used for an original
supported target, choose any $k_\star\ge3$ with $\mu(k_\star)>0$ and put
$r_\star=F_{k_\star+1}/F_{k_\star+3}$. Here $F_0=0$, $F_1=1$ and
$F_{n+2}=F_{n+1}+F_n$. The construction below works for every real

$$
r_\star\in I:=\left[\frac38,\frac5{13}\right],
\tag{1.2}
$$

so it applies to every such supported Fibonacci ratio. It does not require
$\mu(3)>0$ or a maximizing supported depth.

The original source draws $K$ once, before the first paid Read. Its
$(m,d,\ell,n)=(2,1,2,4)$ control, both seeds, paid rejections, partial
parses, every finite return, marker triples, held records, third write
before latch, fourth completion and matching Stop are those of [PAIR].
Configuration TV precedes averaging. The compatible-law interpretation
uses entire-descriptor conditioning and common **unweighted** acquired
marginals, with the same acquired and synthetic kernels. COMPLETE includes
the installed program, numerical representation, sampler states,
workspace and persistent randomness. The measures constructed here are
analytical measures on the certificate's original products; no observer
installation or additional source operation is part of the construction.

**Definition 1.2 (coordinates and the retained tests).** Write

$$
w_{j,0}=(\beta\alpha)^j\alpha,\qquad
w_{j,1}=(\beta\alpha)^j\beta\beta.
$$

The complete p carrier consists of these words and $\infty_p$; the
suspended carrier consists of $\beta$, the words $\alpha w_{j,i}$ and
$\infty_\beta$. Every tail $T_s(j)$ includes the phase's infinite outcome.
The native laws are

$$
P_{p,r}(w_{j,0})=r[r(1-r)]^j,\qquad
P_{p,r}(w_{j,1})=(1-r)^2[r(1-r)]^j,
$$

$$
P_{\beta,r}(\beta)=1-r,\qquad
P_{\beta,r}(\alpha w_{j,i})=rP_{p,r}(w_{j,i}),
\tag{1.3}
$$

with zero infinite masses. These are [PAIR, (17.1)].

Let $\pi_L$ retain the atoms of depth less than $L$ and the whole remaining
tail, as well as standalone $\beta$ at suspension. Thus $\pi_5Q$ has eleven
cells and $\pi_5W$ has twelve. The atom $\alpha=w_{0,0}$ is counted once.
The complete level-four output partitions $\mathscr F_p,\mathscr F_\beta$
have nine and ten cells, respectively.

For a p descriptor $Q$ and a suspended descriptor $W$, set

$$
\begin{gathered}
u=Q(\alpha),\quad v=1-W(\beta),\quad
f=Q(w_{0,1})+Q(w_{1,1})+Q(w_{2,1}),\\
h=W(\beta)+W(\alpha w_{0,1}),\quad
q=Q(w_{0,1}),\quad z=W(\alpha\alpha),
\end{gathered}
$$

and use the original ordered feature vectors

$$
\mathbf p(Q)=(1,u,u^2,f,uf,q,Q(w_{3,1})),
\qquad
\mathbf s(W)=(1,v,v^2,h,vh,z,W(\alpha w_{3,1})).
\tag{1.4}
$$

The outer domains $Z_p,Z_\beta$ impose normalization, nonnegativity,
the native endpoint interval on each level-five cell, $a\le u,v\le b$,
and every retained tail bound of [PAIR, Section 16.5]. For every output
cell, the original raw residuals are

$$
b_E(Q,W)=Q(\beta E)-(1-u)W(E),\qquad
a_F(W,Q)=W(\alpha F)-vQ(F).
\tag{1.5}
$$

The original losses are

$$
\ell_{p,r}(Q)=\operatorname{TV}(\pi_4Q,\pi_4P_{p,r})-\rho_p,
\qquad
\ell_{\beta,r}(W)=\operatorname{TV}(\pi_4W,\pi_4P_{\beta,r})-\rho_\beta.
\tag{1.6}
$$

In the fixed family, $P,\chi_E$ are arbitrary linear combinations of
$\mathbf p$, and $S,\xi_F$ of $\mathbf s$. There are two event coefficients,
six nonnegative risk coefficients, and the original total of
$14+70+63+2+6=155$ scalar coefficients. Its original $\ell^1$ bound is one;
the two thresholds are separate. No basis element, coefficient or tail
cell is removed below.

## 2. Four rational complete descriptors

**Definition 2.1 (the four laws).** Put

$$
t=\frac29,\qquad x_j=\frac13t^j,\qquad y_j=\frac49t^j,
\qquad v=\frac7{19},
$$

$$
q=1-\frac{1-H}{v}=\frac{18959}{47250},\qquad
U=\frac{q}{1-v}=\frac{360221}{567000},\qquad
u=1-U=\frac{206779}{567000},\qquad
c=Uv=\frac{18959}{81000}.
\tag{2.1}
$$

Define

$$
\begin{aligned}
d_B&=C-q-cq=\frac{80300447}{3827250000},\\
s_B&=1-C-(1+c)u-x_3-(1+c)y_3-x_4-t^5
     =\frac{84713716643}{3720087000000},\\
d_A&=C-q-y_2=\frac{7411336}{79734375},\\
s_A&=1-u-C+y_2-t^2=\frac{58511437}{637875000}.
\end{aligned}
\tag{2.2}
$$

The p laws are given by the following table, by
$Q_B(w_{j,0})=Q_A(w_{j,0})=x_j$ and
$Q_B(w_{j,1})=Q_A(w_{j,1})=y_j$ for $j\ge5$, and by zero infinite masses.

| $(j,i)$ | $Q_B(w_{j,i})$ | $Q_A(w_{j,i})$ |
|---|---:|---:|
| $(0,0)$ | $u$ | $u$ |
| $(0,1)$ | $q$ | $q$ |
| $(1,0)$ | $cu$ | $s_A$ |
| $(1,1)$ | $cq$ | $d_A$ |
| $(2,0)$ | $s_B$ | $x_2$ |
| $(2,1)$ | $d_B$ | $y_2$ |
| $(3,0)$ | $x_3$ | $x_3$ |
| $(3,1)$ | $y_3$ | $y_3$ |
| $(4,0)$ | $x_4$ | $x_4$ |
| $(4,1)$ | $cy_3$ | $y_4$ |

The suspended laws have $W_B(\beta)=W_A(\beta)=1-v$ and, for $0\le j<4$,

$$
W_B(\alpha w_{j,i})=\frac{Q_B(w_{j+1,i})}{U},
\qquad
W_A(\alpha w_{j,i})=vQ_A(w_{j,i}).
\tag{2.3}
$$

Their remaining coordinates are

$$
\begin{aligned}
W_B(\alpha w_{4,0})&=\frac{u}{U}t^5
                      =\frac{6616928}{21270689829},\\
W_A(\alpha w_{4,0})&=(v-t)t^4=\frac{400}{1121931},\\
W_B(\alpha w_{4,1})&=W_A(\alpha w_{4,1})=a y_4,\\
W_B(\alpha w_{j,0})&=W_A(\alpha w_{j,0})=a x_j\quad(j\ge5),\\
W_B(\alpha w_{j,1})&=W_A(\alpha w_{j,1})=a y_j\quad(j\ge5),\\
W_B(\infty_\beta)&=W_A(\infty_\beta)=0.
\end{aligned}
\tag{2.4}
$$

**Lemma 2.2 (exact membership, including every tail).** The four objects
in Definition 2.1 are normalized nonnegative complete laws. Every atom
lies in its native endpoint interval, their emissions lie in $[a,b]$,
and they obey all the complete tail bounds defining
$\mathcal K_p,\mathcal K_\beta$. In particular,

$$
\pi_5Q_B,\pi_5Q_A\in Z_p,\qquad
\pi_5W_B,\pi_5W_A\in Z_\beta.
\tag{2.5}
$$

**Proof.** The geometric tails satisfy

$$
\sum_{j\ge J}(x_j+y_j)=t^J,
\qquad a(y_4+t^5)=t^5.
\tag{2.6}
$$

The definitions of $s_A,s_B$ therefore normalize $Q_A,Q_B$. In particular,
$Q_A(T_p(4))=t^4$ and both p tails at level five equal $t^5$.
Equations (2.3)--(2.6) give

$$
W_B(T_\beta(4))=\frac{t^5}{U},\qquad
W_A(T_\beta(4))=vt^4,
\qquad W_B(T_\beta(5))=W_A(T_\beta(5))=at^5.
\tag{2.7}
$$

Also $q=U(1-v)$. Hence the mass of $W_B$ through depth three, including
standalone beta, is

$$
\frac{q+\sum_{j=1}^{4}\sum_iQ_B(w_{j,i})}{U}
=1-\frac{t^5}{U}.
$$

Together with (2.7), this normalizes $W_B$. The mass of $W_A$ through
depth three is $1-v+v(1-t^4)$, which normalizes $W_A$ as well.

Here is a finite rational enclosure of every exceptional endpoint-box
comparison. For a phase cell with native endpoint masses $l<h$, let
$\theta(D)=(D-l)/(h-l)$. Each entry is an enclosure of $10000\theta(D)$;
a single integer denotes equality. The suspended entries in row $(j,i)$
refer to $\alpha w_{j,i}$. Every entry follows from (2.1)--(2.4) by
positive-denominator cross multiplication.

| Cell | $Q_B$ | $Q_A$ | $W_B$ | $W_A$ |
|---|---:|---:|---:|---:|
| standalone $\beta$ | — | — | $[4736,4737]$ | $[4736,4737]$ |
| $(0,0)$ | $[4703,4704]$ | $[4703,4704]$ | $[4755,4756]$ | $[4755,4756]$ |
| $(0,1)$ | $[4884,4885]$ | $[4884,4885]$ | $[9229,9230]$ | $[9229,9230]$ |
| $(1,0)$ | $[5147,5148]$ | $[8051,8052]$ | $[8135,8136]$ | $[6640,6641]$ |
| $(1,1)$ | $[6079,6080]$ | $[5297,5298]$ | $[630,631]$ | $[8076,8077]$ |
| $(2,0)$ | $[9592,9593]$ | $0$ | $[726,727]$ | $[1548,1549]$ |
| $(2,1)$ | $[2023,2024]$ | $10000$ | $[3690,3691]$ | $[7870,7871]$ |
| $(3,0)$ | $0$ | $0$ | $[606,607]$ | $[1293,1294]$ |
| $(3,1)$ | $0$ | $0$ | $[4690,4691]$ | $[4690,4691]$ |
| $(4,0)$ | $0$ | $0$ | $[1543,1544]$ | $[3292,3293]$ |
| $(4,1)$ | $[5223,5224]$ | $0$ | $0$ | $0$ |
| level-five tail | $0$ | $0$ | $0$ | $0$ |

All finite endpoint masses are positive. The table proves nonnegativity
and endpoint-box membership for every exceptional coordinate, including
$a<u,v<b$. Every coordinate at depth at least five is its native
$a$ coordinate; infinity has mass zero in both native laws and in the
four constructed laws. Thus the full endpoint boxes hold.

For completeness, put $t_b=6/25$. On the p zero branch the larger
endpoint is always $b$. On its one branch the larger endpoint is $a$
for $j=0,1,2$ and $b$ for $j\ge3$: the endpoint ratio is
$(81/100)(27/25)^j$. On the suspended one branch the ratio is
$(243/250)(27/25)^j$, so the larger endpoint is $b$ for $j\ge1$;
the suspended zero branch also has larger endpoint $b$.
Consequently either p law obeys

$$
\begin{aligned}
Q(T_p(1))&\le t_b+(y_1-P_{p,b}(w_{1,1}))
                         +(y_2-P_{p,b}(w_{2,1}))
 =\frac{2888404}{11390625}<\frac4{15},\\
Q(T_p(2))&\le t_b^2+y_2-P_{p,b}(w_{2,1})
 =\frac{669904}{11390625}<\left(\frac4{15}\right)^2,\\
Q(T_p(j))&\le t_b^j<\left(\frac4{15}\right)^j\quad(j\ge3).
\end{aligned}
\tag{2.8}
$$

For either suspended law, $W(T_\beta(0))=v<b$ and
$W(T_\beta(j))\le b t_b^j<b(4/15)^j$ for $j\ge1$.
The p tail at level zero is one. These estimates include all longer
words and infinity, and prove every required tail inequality.
The level-five tail intervals follow either from (2.7) or by summing the
same-order endpoint intervals beyond that level. $\square$

## 3. The exact representing measures

**Theorem 3.1 (two unit atoms annihilate the original moment vector).**
On the original ordered products, define the nonnegative probability measures

$$
\Gamma_B=\delta_{(\pi_5Q_B,\pi_5W_B)},\qquad
\Gamma_A=\delta_{(\pi_5W_A,\pi_5Q_A)}.
\tag{3.1}
$$

Their fourteen potential moments match, all seventy B input-output
moments and all sixty-three A input-output moments vanish, and both
centered event moments vanish. These assertions use exactly the bases
and partitions in Definition 1.2.

**Proof.** The two common feature vectors are explicitly

$$
\mathbf p(Q_B)=\mathbf p(Q_A)=(1,u,u^2,C,uC,q,y_3),
$$

$$
\mathbf s(W_B)=\mathbf s(W_A)=(1,v,v^2,H,vH,vu,vy_3).
\tag{3.2}
$$

Indeed, $q+cq+d_B=C=q+d_A+y_2$, and
$1-v+vq=H$. Equation (2.3) gives the suspended alpha mass $vu$ in
both cases, while $Q_B(w_{4,1})=cy_3$ gives
$W_B(\alpha w_{3,1})=vy_3=W_A(\alpha w_{3,1})$.
All remaining entries of (3.2) follow immediately from the definitions.
Thus the integrals of every original potential cancel, separately for
all seven p features and all seven suspended features. The event means
are exactly $C,H$.

The raw B residual at standalone beta is
$q-U(1-v)=0$. At each of its eight retained prefixed atoms it is zero
by (2.3). Its complete tail residual is, by (2.7),

$$
Q_B(T_p(5))-U W_B(T_\beta(4))=t^5-U\frac{t^5}{U}=0.
\tag{3.3}
$$

The eight retained atomic A residuals vanish by (2.3), and its complete
tail residual is

$$
W_A(T_\beta(4))-vQ_A(T_p(4))=vt^4-vt^4=0.
\tag{3.4}
$$

Thus the entire ten-entry B residual vector and the entire nine-entry A
residual vector are zero at their respective nodes. Multiplication by
each of the seven original input features gives the claimed seventy and
sixty-three zero moments. No division by a vanishing continuation factor
occurs: $U>3/5$ and $v>1/3$. Lemma 2.2 supplies exact node membership;
each measure in (3.1) has its single weight equal to one. $\square$

**Lemma 3.2 (all six losses, uniformly on the interval).** For (3.1), all
four endpoint losses are zero, and for every $r\in I$,

$$
\operatorname{TV}(\pi_4Q_B,\pi_4P_{p,r})<\frac3{100}<\rho_p,
\qquad
\operatorname{TV}(\pi_4W_A,\pi_4P_{\beta,r})<\frac1{50}<\rho_\beta.
\tag{3.5}
$$

In particular the two remaining integrated losses are strictly negative
for every allowed $r_\star$, with slack greater than
$866183/45562500$ and $52/3375$, respectively.

**Proof.** Inside the endpoint boxes the positive-difference events are
$E_p=\{w_{0,1},w_{1,1},w_{2,1}\}$ and
$E_\beta=\{\beta,\alpha w_{0,1}\}$. The endpoint event differences
have half-widths $\rho_p,\rho_\beta$ and midpoints $C,H$.
Equation (3.2) and the endpoint TV identity of [PAIR, (11.30)] therefore
give both endpoint distances exactly. Grouping the level-four tail
loses no endpoint TV: all its finite atoms have the same endpoint order,
and the infinite masses are zero. This proves the four endpoint claims
on the prescribed complete projection.

Here is a uniform bound that retains all TV sign changes. Set
$r_-=3/8$, $r_+=5/13$. For a phase $s$ and a fixed descriptor $D$, put

$$
B_s(D)=\frac12\sum_{e\in\mathscr F_s}
 \max\{|D(e)-P_{s,r_-}(e)|,\ |D(e)-P_{s,r_+}(e)|\}.
\tag{3.6}
$$

Every native cell mass in these partitions is monotone on $I$.
For a monomial $r^m(1-r)^n$ its derivative, after a positive factor is
removed, has sign $m-(m+n)r$. At p the exponents are $(j+1,j)$ and
$(j,j+2)$ for $0\le j<4$, and $(4,4)$ for the complete tail.
At suspension they are $(0,1)$ for beta, $(j+2,j)$ and $(j+1,j+2)$
for the prefixed atoms, and $(5,4)$ for the complete tail.
None of these derivative signs changes in the interior of $I$;
the p cell $(3,1)$ has its turning point at the left boundary.
Thus every native cell lies between its two boundary values, and

$$
\operatorname{TV}(\pi_4D,\pi_4P_{s,r})\le B_s(D)\qquad(r\in I).
\tag{3.7}
$$

Absolute values and their ties are retained in (3.6); no open sign-cell
restriction occurs. Substitution of (2.1)--(2.4) gives the exact bounds

$$
B_p(Q_B)=
\frac{1823868392951336233193569}{63639949162687538135040000}
<\frac3{100},
\qquad
B_\beta(W_A)=\frac{272417}{14829750}<\frac1{50}.
\tag{3.8}
$$

These are finite positive-denominator rational comparisons. The tail
summands are the full level-four cells, including infinity. Finally,
subtracting the radii gives the stated rational slacks. $\square$

## 4. Resolution of the original coefficient alternative

**Theorem 4.1 (infeasibility of the original 155-coefficient family).**
For every $r_\star\in I$, the rational system [PAIR, (16.18)--(16.22)]
has no solution. The same conclusion holds if its coefficients and
thresholds are allowed to be real. In particular it holds with the
original $155$-coefficient $\ell^1$ budget at most one, six nonnegative
risk weights, and rational thresholds with positive sum.

**Proof.** Let a proposed tuple have the original potentials, multipliers,
event terms and nonnegative risk weights. Evaluate its B expression at
$(\pi_5Q_B,\pi_5W_B)$ and its A expression at
$(\pi_5W_A,\pi_5Q_A)$. Theorem 3.1 cancels all potential terms and
annihilates all residual and centered event terms. Hence the sum is exactly

$$
\begin{aligned}
&G_B(\pi_5Q_B,\pi_5W_B)+G_A(\pi_5W_A,\pi_5Q_A)\\
&\quad=\sum_{r\in\{a,b,r_\star\}}
 \bigl[\lambda_{p,r}\ell_{p,r}(Q_B)
       +\lambda_{\beta,r}\ell_{\beta,r}(W_A)\bigr]\le0,
\end{aligned}
\tag{4.1}
$$

by Lemma 3.2. Both product nodes belong to their original outer domains,
including their boundary faces and complete tails. The two universal
inequalities would instead make (4.1) at least
$\delta_B+\delta_A>0$. This is impossible.

The argument bounds no coefficient and discards no coefficient: the
original norm restriction is simply unnecessary for this obstruction.
It applies to the absolute-value expressions themselves. If those
expressions are represented by all nonempty closed TV sign cells, each
node belongs to such a cell, and the same contradiction holds on that
representation, including all ties and boundary faces. $\square$

**Corollary 4.2 (increasing input-multiplier degree alone cannot suffice).**
Keep the original potential spaces, output partitions and centered events.
Replacing the input multipliers by arbitrary real-valued functions defined
at the two relevant input nodes still permits no positive-sum pair of
universal inequalities with nonnegative risk weights as in Theorem 4.1.

**Proof.** Equations (3.3)--(3.4) and their atomic counterparts say that
every retained raw residual is zero pointwise at its node. Its product
with any real-valued input multiplier is therefore zero. The potential,
event and risk terms still satisfy (4.1). $\square$

## 5. The lost relation and the exact consumer boundary

**Proposition 5.1 (the null has unequal full marginals and omitted residuals).**
The measures in (3.1) are not a compatible pair in the sense of
[PAIR, Sections 11 and 20]. Their p and suspended full marginals differ,
and their complete-law extensions in Definition 2.1 fail residual
identities beyond the retained partition.

**Proof.** Although (3.2) matches the prescribed features, the next p
zero-branch coordinate and its suspended counterpart give

$$
Q_B(w_{1,0})-Q_A(w_{1,0})
=-\frac{292500403}{45927000000}\ne0,
\tag{5.1}
$$

$$
W_B(\alpha w_{1,0})-W_A(\alpha w_{1,0})
=\frac{151337393407}{73856561906250}\ne0.
\tag{5.2}
$$

Thus even their level-five marginals are different. In addition, the
first omitted one-branch atoms have the raw residuals

$$
W_A(\alpha w_{4,1})-vQ_A(w_{4,1})
=(a-v)y_4=-\frac{128}{3365793}\ne0,
\tag{5.3}
$$

$$
Q_B(w_{5,1})-UW_B(\alpha w_{4,1})
=y_5-Uay_4=\frac{142232}{12555293625}\ne0.
\tag{5.4}
$$

These nonzero coordinates cancel within the aggregate tail residuals
(3.3)--(3.4). The full descriptor equations therefore do not follow from
the finite output partitions, and the common feature values do not give
common unweighted descriptor marginals. $\square$

**Corollary 5.2 (scope of the obstruction).** Theorem 4.1 resolves the fixed
family of [PAIR, Open problem 16.5]. Its
specific obstruction consists of the four rational laws, their identical
seven-feature values, their two exact retained residual vectors and the
simultaneous loss bounds. Proposition 5.1 supplies the relation that the
fixed tests fail to distinguish. The six-cell pair of [PAIR, Section 17]
has nonzero B moments and is not the representing pair (3.1).

**Proof.** The compatible-law compactness, source correspondence and regeneration
of [PAIR, Sections 11 and 20] and [PAID, Sections 16--18][PAID] keep their
full common-marginal and entire-descriptor hypotheses. Their criterion
for the original value $j_c$ cannot be applied to (3.1), by (5.1)--(5.4).
In particular, Theorem 4.1 implies neither $j_c=0$ nor $j_c>0$, and does
not exclude the larger certificate families of [PAID, Section 18]. The
positive-certificate implication [PAIR, Proposition 16.4] remains a
conditional implication; the present theorem rules out its fixed
155-coefficient premise. Definition 2.1 supplies four individually specified complete laws with
finite rational descriptions and geometric tails. It does not supply a
single compatible pair or a finite stationary same-update table.
Consequently it supplies no original-source installation, represented
sampler for such a table, observation acquisition, training attainment
or generalization assertion. $\square$

The finite-dimensional convex-order theorem of Leskelä and Vihola,
[Theorem 1.2(i)][LV], concerns random vectors with finite first moments
and all convex test functions; its parameterized version, Theorem 1.3(i),
concerns probability kernels with finite first moments at every parameter.
The bounded projected vectors here satisfy those integrability conditions,
but equality of the seven prescribed features supplies neither the full
convex-order tests nor the prescribed entire marginals required in
[PAIR, Theorem 20.2]. These classical results provide no assertion that
(3.1) is a compatible full flow. The construction and contradiction above
are direct deductions for the specified source and coefficient family;
no new coupling-existence or general moment-duality theorem is asserted.

[PAIR]: https://github.com/the-omega-institute/trureturing/blob/f9c2c807f401b5ddd0556da6842a0849648feef4/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PAIRED_CALIBRATION_OBSERVABILITY.md
[PAID]: https://github.com/the-omega-institute/trureturing/blob/f9c2c807f401b5ddd0556da6842a0849648feef4/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md
[LV]: https://arxiv.org/html/1404.0999v3

## 追加锚（本行以下为增补区）
