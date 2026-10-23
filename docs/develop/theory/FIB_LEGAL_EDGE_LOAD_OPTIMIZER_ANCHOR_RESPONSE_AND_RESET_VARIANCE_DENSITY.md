# FIB harmonic-edge load: optimizer anchor response and reset-variance density

The full finite optimizer admits a reset-slice Euler equation whose boundary terms are the responses of the two occupied anchors. Its mean and covariance identities characterize exactly when the reset-conditioned center posterior is constant. Nonnegative probes of specified exterior coordinates give a quantitative lower certificate for the same optimizer's reset variance. A separate symbolic insertion comparison gives a strict per-site ceiling and rules out the variance threshold test at every length through $98$.

All posteriors, exterior masses, means, responses and probes in the finite arguments belong to one actual optimizer $\pi_n$ at the indicated length. The response shortfalls needed for a positive density certificate, a crossing of the threshold, and the original finite-hidden attainment alternative remain unproved. The results are ordinary mathematical statements with handwritten proofs; no kernel-verification claim is made.

## 1. The complete finite objective and its actual posteriors

**Definition 1.1 (Open legal words and harmonic load).** For $n\ge1$ let

$$
B_n=\{w\in\{0,1\}^n:w_jw_{j+1}=0\ (1\le j<n)\}.
$$

$B_0$ consists of the empty word. The graph $\Gamma_n$ has every vertex in $B_n$ and every legal Hamming-one edge. For endpoint insertions use $w_0=w_{n+1}=0$; the endpoints are not joined. Set

$$
h(s,t)=
\begin{cases}
st/(s+t),&s+t>0,\\
0,&s=t=0,
\end{cases}
\qquad
\Phi_n(p)=\sum_{\{u,v\}\in E(\Gamma_n)}h(p_u,p_v),
\qquad
\kappa_n=\max_{p\in\mathcal P(B_n)}\Phi_n(p).
\tag{1.1}
$$

The domain is the entire probability simplex. A zero mass does not remove a word, an edge or a seam constraint. The all-zero word and every legal endpoint one remain present.

**Premise 1.2 (Canonical optimizer and growth interfaces).** Write $\pi_n$ for the strictly positive optimizer supplied by [Positive unique optimizer, Theorem 3.1][O], as collected in [Universal, Convention 1.3][U]. On each legal insertion edge $u\to v$ it satisfies

$$
\Phi_n(\pi_n)=\kappa_n,\qquad
\frac13\pi_n(u)\le\pi_n(v)\le\pi_n(u).
\tag{1.2}
$$

[Growth, Lemma 3.1 and Theorems 3.2 and 5.2][G], through the same Universal interface, supplies continuity, concavity and degree-one homogeneity of $h$, and

$$
c_\star=\lim_{n\to\infty}\frac{\kappa_n}{n},\qquad
nc_\star\le\kappa_n\le(n+1)c_\star,\qquad
\frac{\kappa_n}{n+1}\longrightarrow c_\star.
\tag{1.3}
$$

[Guarded, Definition 1.1] supplies the ceiling $c_\star\le\bar c:=3-2\sqrt2$. Define the fixed threshold

$$
\tau=2\bar c-\frac1{24}=2(3-2\sqrt2)-\frac1{24}.
\tag{1.4}
$$

These are supplied interfaces. Optimizer existence, uniqueness, the insertion bounds, the growth theorem and the original whole-simplex square-discrepancy identity retain their canonical source attribution.

**Definition 1.3 (Full-complement posterior and reset variance).** Throughout the finite arguments fix $n$ and let $W\sim\pi_n$. For $1\le j\le n$ put

$$
\mathcal G_{n,j}=\sigma(W_k:1\le k\le n,\ k\ne j),\qquad
a_{n,j}=\mathbb E_{\pi_n}[W_j\mid\mathcal G_{n,j}].
\tag{1.5}
$$

Every extendible complement has positive mass. On a legal two-point fiber its posterior is the one-word mass divided by the sum of its two masses; on a forced singleton it is zero. Thus (1.2) gives

$$
\frac14\le a_{n,j}\le\frac12\quad\hbox{on free fibers},\qquad
a_{n,j}=0\quad\hbox{on forced fibers}.
\tag{1.6}
$$

For each reset index $3\le i\le n-2$ define

$$
\begin{aligned}
E_i&=\{W_{i-2}=W_{i+2}=1\},&
M_i&=\pi_n(E_i),\\
c_i&=\mathbb E_{\pi_n}[a_{n,i}\mid E_i],&
v_i&=M_i\operatorname{Var}_{\pi_n}(a_{n,i}\mid E_i),\\
V_2(n)&=\sum_{i=3}^{n-2}v_i.
\end{aligned}
\tag{1.7}
$$

For $n<5$ the last sum is empty and equals zero. The event $E_i$ is measurable in $\mathcal G_{n,i}$, is nonempty and has positive mass. Its two neighbors of the center are zero. Conditional expectation therefore gives

$$
c_i=\pi_n(W_i=1\mid E_i),\qquad \frac14\le c_i\le\frac12.
\tag{1.8}
$$

Every conditional variance in (1.7) conditions the full-complement posterior on the indicated event. It is not the variance of a posterior computed from only five coordinates.

## 2. Euler balance in the entire probability simplex

**Proposition 2.1 (Finite vertex-score equation).** If $p$ is strictly positive on $B_n$, let $a_{p,j}$ denote its full-complement posterior. Extend $\Phi_n$ to positive mass vectors by the same edge sum. Its derivative with respect to a word mass is

$$
L_p(w):=\frac{\partial\Phi_n}{\partial p_w}
=\sum_{v:\{w,v\}\in E(\Gamma_n)}\frac{p_v^2}{(p_w+p_v)^2}
=\sum_{j=1}^n(w_j-a_{p,j}(w_{-j}))^2.
\tag{2.1}
$$

For the supplied positive optimizer,

$$
L_{\pi_n}(w)=\kappa_n\qquad(w\in B_n).
\tag{2.2}
$$

Proof. For $s,t>0$, $\partial_s h(s,t)=t^2/(s+t)^2$. At a free coordinate of $w$, if $w_j=0$ the corresponding derivative is the squared posterior; if $w_j=1$ it is the squared complementary posterior. A forced coordinate of a legal word equals zero, its posterior equals zero, and it has no flip edge. This accounts for every term of (2.1), including endpoint terms.

At $\pi_n$, transferring a sufficiently small signed mass from any vertex to any other vertex stays in the positive simplex. The derivative in this direction vanishes at a maximum. Hence all $L_{\pi_n}(w)$ have the same value. Multiplication by $\pi_n(w)$ and summation identifies this value: an edge with masses $s,t$ contributes

$$
s\frac{t^2}{(s+t)^2}+t\frac{s^2}{(s+t)^2}=h(s,t).
$$

The common value is $\Phi_n(\pi_n)=\kappa_n$. This is elementary finite-simplex differentiation of the original objective. $\square$

Only positivity, normalization and full-simplex optimality are used for the variation. Nearby varied laws need not satisfy the optimizer's insertion inequalities. Imposing such inequalities on the admissible directions would change the variational problem.

## 3. Coupled event mass and mean: the obstruction through length 98

**Lemma 3.1 (Symbolic five-site insertion comparison).** At every reset index of the same $\pi_n$,

$$
M_i\le\frac9{49-13c_i}.
\tag{3.1}
$$

Proof. Fix the complete exterior $\eta$ of $[i-2,i+2]$. Only exteriors allowing both anchors to equal one can contribute to $E_i$. For each such exterior, the immediately adjacent exterior bits, when present, are zero. Consequently every legal five-site word can be inserted into this fixed exterior. Define the unnormalized masses

$$
u_\eta=\pi_n(\eta,10001)>0,\qquad
t_\eta=\pi_n(\eta,10101)>0.
$$

The notation specifies the exterior and the five middle bits together, hence one complete length-$n$ word. All the following comparisons take place in this same exterior and use (1.2).

First consider the disjoint words $a0x0b$, $a,b,x\in\{0,1\}$. For $x=0$, deleting either or both anchor ones from $10001$ shows that each of the four masses is at least $u_\eta$. For $x=1$, the same deletions from $10101$ give four masses at least $t_\eta$. Their total is at least $4(u_\eta+t_\eta)$.

The two words $0100b$, $b\in\{0,1\}$, have total mass at least $2u_\eta/3$: each precursor $0000b$ has mass at least $u_\eta$, and inserting the second bit is legal and retains at least a third of that mass. Likewise the two words $a0010$ have total mass at least $2u_\eta/3$. Finally $00000$ has mass at least $u_\eta$; successive legal insertions at its second and fourth positions give mass at least $u_\eta/9$ to $01010$.

The four families are disjoint: their second and fourth bits are respectively $00$, $10$, $01$ and $11$. Each is legal with the fixed exterior. Their union need not be given any independent probabilistic structure. Its mass alone proves

$$
\pi_n(W_{[1,n]\setminus[i-2,i+2]}=\eta)
\ge4(u_\eta+t_\eta)+\frac{13}{9}u_\eta.
\tag{3.2}
$$

Sum (3.2) over exteriors compatible with $E_i$. Their total probability is at most one; the sums of $u_\eta+t_\eta$ and $u_\eta$ are respectively $M_i$ and $M_i(1-c_i)$ by (1.8). Hence

$$
1\ge4M_i+\frac{13}{9}M_i(1-c_i)
=\frac{49-13c_i}{9}M_i.
$$

The denominator is positive on the band, proving (3.1). Incompatible exteriors contribute nothing to $E_i$ and are never divided by. A missing exterior bit at an open endpoint imposes no extra constraint. This is a symbolic disjoint-event comparison, not an evaluation of an optimizer or a substitution of $\pi_5$. $\square$

**Lemma 3.2 (A rational per-site variance ceiling).** Every reset site satisfies

$$
0\le v_i\le
\frac{9(c_i-\tfrac14)(\tfrac12-c_i)}{49-13c_i}
<\frac1{312}.
\tag{3.3}
$$

Proof. Under $\pi_n(\cdot\mid E_i)$ set $Q=a_{n,i}$, with mean $c=c_i$. The pointwise inequality $(Q-\tfrac14)(\tfrac12-Q)\ge0$ gives

$$
\mathbb E Q^2\le\frac34c-\frac18,
\qquad
\operatorname{Var}(Q)\le(c-\tfrac14)(\tfrac12-c).
\tag{3.4}
$$

This is the classical interval-variance inequality, here proved directly. Multiply by (3.1). For the strict rational ceiling, compute symbolically

$$
\begin{aligned}
49-13c-2808(c-\tfrac14)(\tfrac12-c)
&=2808c^2-2119c+400\\
&=\frac{(5616c-2119)^2+2639}{11232}>0.
\end{aligned}
\tag{3.5}
$$

Since $49-13c>0$, (3.5) is exactly the strict comparison of the middle expression in (3.3) with $1/312$. If $c$ is either endpoint of its band, (3.4) already makes the variance zero. No sharpness is claimed. $\square$

**Theorem 3.3 (Exact finite-size obstruction).** For $n\ge5$,

$$
V_2(n)<\frac{n-4}{312}.
\tag{3.6}
$$

For every $1\le n\le98$,

$$
V_2(n)<\tau.
\tag{3.7}
$$

Thus a successful strict threshold test $V_2(n)>\tau$ requires $n\ge99$.

Proof. There are $n-4$ reset indices, so summing the strict bound (3.3) gives (3.6). For $5\le n\le98$,

$$
V_2(n)<\frac{94}{312}=\frac{47}{156}.
$$

The exact comparison with the threshold is

$$
\tau-\frac{47}{156}=\frac{1765}{312}-4\sqrt2>0,
\tag{3.8}
$$

because $1765,1248>0$ and $1765^2-2\cdot1248^2=217>0$. For $n<5$, $V_2(n)=0$, and (3.8) also proves $\tau>0$. This covers every stated length without computing any $\pi_n$. The necessary length bound asserts neither positivity nor a threshold crossing at length $99$. $\square$

**Proposition 3.4 (Empty and singleton reset cases).** For $n<5$ there is no reset index. At $n=5$ and $n=6$, the full-complement space on each reset event is a singleton, and $V_2(n)=0$.

Proof. At $n=5$ the anchors at $1,5$ force bits $2,4$ to zero, specifying every bit except the center. At $n=6$, the reset at $i=3$ has anchors at $1,5$, which also force bit $6$ to zero; the reset at $i=4$ is the reflected case. Thus the full-complement posterior is constant on each such event. A variance on a singleton is zero. $\square$

## 4. The reset graph, its internal edge deficit and anchor response

**Definition 4.1 (The actual reset complement).** Fix a reset index $i$. Let $S_i$ consist of every full complement $y=(w_j)_{j\ne i}$ compatible with $E_i$. Both completions $w^0(y)$ and $w^1(y)$, with center $0$ or $1$, are legal. Define

$$
m_y=\pi_n(w^0(y))+\pi_n(w^1(y)),\qquad
q_y=\frac{\pi_n(w^1(y))}{m_y}.
\tag{4.1}
$$

They satisfy

$$
m_y>0,\quad q_y\in[1/4,1/2],\quad
\sum_{y\in S_i}m_y=M_i,\quad
\sum_y m_yq_y=M_ic_i,\quad
\sum_y m_y(q_y-c_i)^2=v_i.
\tag{4.2}
$$

For a function $g$ on $S_i$ write

$$
\langle g\rangle_i=\frac1{M_i}\sum_y m_yg_y.
\tag{4.3}
$$

This is precisely expectation over the full complement under $\pi_n(\cdot\mid E_i)$. Covariances and variances with subscript $i$ below use this probability, and no other law.

Join two elements of $S_i$ when they differ by one legal flip at an exterior coordinate, preserving both anchor ones. Denote this graph by $\mathcal G_i$ and its edges by $\mathcal E_i^{\mathrm{int}}$. The notation for these finite edges is distinct from the infinite exterior sigma-field in §8.

**Lemma 4.2 (Connectivity and coordinate matchings).** The graph $\mathcal G_i$ is connected. For any fixed coordinate $k\ne i$, its edges labelled by a flip at $k$ form a matching.

Proof. Delete every one other than the two fixed anchors. Each deletion is legal and preserves $E_i$. This reaches the complement with just those anchors equal to one. Reverse such a deletion path to reach any other complement. Empty exterior sides and the singleton case satisfy the same assertion. At a fixed coordinate a complement has at most one possible flipped neighbor, proving the matching claim. $\square$

**Definition 4.3 (Anchor-deletion masses and response).** For $j\in\{i-2,i+2\}$ and $x\in\{0,1\}$ define

$$
\begin{aligned}
\beta_{j,x}(y)&=\pi_n(w^x(y)-e_j),\\
u_{j,x}(y)&=a_{n,j}((w^x(y))_{-j})
=\frac{\pi_n(w^x(y))}{\pi_n(w^x(y))+\beta_{j,x}(y)},\\
H_i(y)&=\sum_{j\in\{i-2,i+2\}}
\bigl[(1-u_{j,0}(y))^2-(1-u_{j,1}(y))^2\bigr].
\end{aligned}
\tag{4.4}
$$

Deleting an anchor always produces a legal word outside $E_i$, so each $\beta_{j,x}(y)>0$. Both neighbors of each occupied anchor are zero when present. Thus each anchor fiber is free and $u_{j,x}\in[1/4,1/2]$, also when the anchor is an endpoint. The scalar $H_i$ is the decrease in the two occupied-anchor squared losses as the center changes from zero to one. The predictors used in both losses are the fixed full-complement functions of $\pi_n$. In particular the deleted-word masses are not replaced by marginals of a five-site law.

**Lemma 4.4 (Internal edge deficit, convexity and derivatives).** For $e=\{y,z\}\in\mathcal E_i^{\mathrm{int}}$ set

$$
a=m_y,\quad b=m_z,\quad A=a+b,\quad
\alpha=\frac aA,\quad C_e=\frac{a^2b^2}{A^3}.
$$

For $0<r,s<1$ set $\vartheta=\alpha r+(1-\alpha)s$ and define

$$
J_e(r,s)=h(a,b)-h(a(1-r),b(1-s))-h(ar,bs).
\tag{4.5}
$$

Then

$$
J_e(r,s)=C_e\frac{(r-s)^2}{\vartheta(1-\vartheta)}\ge0.
\tag{4.6}
$$

It is convex in $(r,s)$ for fixed $a,b$; for every $0<c<1$, $J_e(c,c)=0$ and $\nabla J_e(c,c)=0$. Writing $\delta=r-s$ and $d=\vartheta(1-\vartheta)$, its derivatives are

$$
\begin{aligned}
\partial_rJ_e&=C_e\left(\frac{2\delta}{d}
-\frac{\alpha\delta^2(1-2\vartheta)}{d^2}\right),\\
\partial_sJ_e&=C_e\left(-\frac{2\delta}{d}
-\frac{(1-\alpha)\delta^2(1-2\vartheta)}{d^2}\right),\\
\partial_rJ_e+\partial_sJ_e
&=-C_e\frac{\delta^2(1-2\vartheta)}{d^2}.
\end{aligned}
\tag{4.7}
$$

Proof. Divide (4.5) by $ab/A$. The remaining difference is

$$
1-\frac{rs}{\vartheta}-\frac{(1-r)(1-s)}{1-\vartheta}
=\frac{(\vartheta-s)(r-\vartheta)}{\vartheta(1-\vartheta)}
=\frac{\alpha(1-\alpha)(r-s)^2}{\vartheta(1-\vartheta)}.
$$

Multiplication back gives (4.6). Convexity follows directly from concavity of $h$: each of the two subtracted terms in (4.5) is a concave function of affine coordinates $(r,s)$. The displayed formula shows the value and gradient vanish on the diagonal. Differentiating (4.6), with $\partial_r\vartheta=\alpha$ and $\partial_s\vartheta=1-\alpha$, gives (4.7). All denominators are positive. Formula (4.5) also gives a continuous extension to the closed square, without interpreting a $0/0$ in (4.6). $\square$

At the actual point write

$$
\delta_e=q_y-q_z,\qquad
\theta_e=\alpha q_y+(1-\alpha)q_z\in[1/4,1/2],\qquad
d_e=\theta_e(1-\theta_e).
\tag{4.8}
$$

## 5. Full-simplex split variations and every boundary term

**Theorem 5.1 (Exact reset-split decomposition).** For any vector $r=(r_y)_{y\in S_i}\in(0,1)^{S_i}$ define a law $p^r$ on the complete $B_n$ by

$$
p^r(w^1(y))=m_yr_y,\qquad
p^r(w^0(y))=m_y(1-r_y),
\tag{5.1}
$$

and leave every word outside $E_i$ at its original $\pi_n$ mass. Then $p^r$ is positive and normalized, and for a constant $K_i$ independent of $r$,

$$
\begin{aligned}
\Phi_n(p^r)
={}&K_i+\sum_{y\in S_i}m_yr_y(1-r_y)\\
&+\sum_{e=\{y,z\}\in\mathcal E_i^{\mathrm{int}}}
\bigl[h(m_y,m_z)-J_e(r_y,r_z)\bigr]\\
&+\sum_{y\in S_i}\sum_{j\in\{i-2,i+2\}}
\bigl[h(m_y(1-r_y),\beta_{j,0}(y))
+h(m_yr_y,\beta_{j,1}(y))\bigr].
\end{aligned}
\tag{5.2}
$$

The function in (5.2) is strictly concave in $r$. At $r=q$ its derivative vanishes in every coordinate and gives

$$
m_y\bigl(1-2q_y-H_i(y)\bigr)
=\sum_{e\ni y}\partial_{q_y}J_e(q_y,q_z)
\qquad(y\in S_i).
\tag{5.3}
$$

Proof. Each pair in (5.1) retains its sum $m_y$, so the total mass remains one; every displayed mass is positive. The law therefore defines a legitimate full-simplex variation through $\pi_n$, with every non-reset mass fixed.

Partition all original edges as follows. Edges with no endpoint in $E_i$ have unchanged masses and make up $K_i$. An edge at coordinate $i$ joins $w^0(y)$ to $w^1(y)$ and contributes $m_yr_y(1-r_y)$. A legal flip at any other coordinate that preserves both anchors gives an edge $\{y,z\}$ of $\mathcal G_i$. It is legal with either central value: the sites adjacent to the center cannot flip because they have an occupied anchor as a neighbor. The two center-slice contributions are exactly $h(m_y,m_z)-J_e(r_y,r_z)$.

An edge leaving $E_i$ from one of its words must delete one of the two anchor ones. These are exactly the last line of (5.2). Their other endpoints have the fixed masses $\beta_{j,x}(y)$. No edge inserting an anchor can join two words inside $E_i$, since both anchors there are already one. There are no additional boundary edges at the center's neighbors, which are blocked, or at the open ends, where the original endpoint convention still applies. Each original edge has thus been counted exactly once.

The center sum is strictly concave because $m_y>0$ for every $y$. The internal sums and boundary terms are concave by concavity of $h$ and the affine dependence on $r$. Their sum is strictly concave. Since $\pi_n$ maximizes the full objective, $r=q$ maximizes this restriction; it lies in its open cube and hence has zero derivative in every $r_y$.

For the boundary terms, differentiation at $r=q$ gives exactly

$$
\begin{aligned}
&\left.\frac{\partial}{\partial r_y}
\sum_{j\in\{i-2,i+2\}}
\bigl[h(m_y(1-r_y),\beta_{j,0})+h(m_yr_y,\beta_{j,1})\bigr]
\right|_{r=q}\\
&\quad=m_y\sum_j
\left[-\frac{\beta_{j,0}^2}{(m_y(1-q_y)+\beta_{j,0})^2}
+\frac{\beta_{j,1}^2}{(m_yq_y+\beta_{j,1})^2}\right]
=-m_yH_i(y).
\end{aligned}
\tag{5.4}
$$

Together with the center derivative $m_y(1-2q_y)$ and the internal derivatives $-\partial J_e$, this proves (5.3). In particular anchor-deletion edges are present, with their sign fixed by (5.4). $\square$

The strict concavity concerns this restriction with the actual masses and actual deletion boundaries held fixed. It does not give permission to prescribe arbitrary boundary responses or replace the restricted problem by a smaller stand-alone optimizer. Equation (5.3) is also the difference of the two full vertex-score equations (2.2), multiplied by $m_y$.

## 6. Mean, covariance and exact screening

**Theorem 6.1 (Mean anchor-response identity).** For every reset index,

$$
M_i\bigl(\langle H_i\rangle_i-(1-2c_i)\bigr)
=\sum_{e\in\mathcal E_i^{\mathrm{int}}}
C_e\frac{\delta_e^2(1-2\theta_e)}{\theta_e^2(1-\theta_e)^2}
\ge0.
\tag{6.1}
$$

Proof. Sum (5.3) over $y$. Its left side is $M_i(1-2c_i-\langle H_i\rangle_i)$. Each internal edge contributes both partial derivatives; the last line of (4.7) identifies their sum. Change signs to get (6.1). Every term is nonnegative because $\theta_e\le1/2$. No exterior-context averaging is interchanged with a limit. $\square$

**Theorem 6.2 (Covariance identity and variance upper bound).** With covariance and variance under (4.3),

$$
-M_i\operatorname{Cov}_i(q,H_i)
=2v_i+
\sum_{e=\{y,z\}\in\mathcal E_i^{\mathrm{int}}}
\nabla J_e(q_y,q_z)\mathbin{\cdot}(q_y-c_i,q_z-c_i).
\tag{6.2}
$$

Every summand after $2v_i$ is nonnegative, and

$$
v_i\le\frac{M_i}{4}\operatorname{Var}_i(H_i).
\tag{6.3}
$$

Proof. Multiply (5.3) by $q_y-c_i$ and sum. Since $\sum_y m_y(q_y-c_i)=0$, the resulting left side is

$$
-2\sum_y m_y(q_y-c_i)^2-\sum_y m_y(q_y-c_i)H_i(y)
=-2v_i-M_i\operatorname{Cov}_i(q,H_i).
$$

Combining the two endpoints of each edge gives (6.2). Convexity of $J_e$ and $J_e(c_i,c_i)=0$ imply the tangent-plane inequality

$$
\nabla J_e(q_y,q_z)\mathbin{\cdot}(q_y-c_i,q_z-c_i)
\ge J_e(q_y,q_z)\ge0.
\tag{6.4}
$$

Consequently Cauchy--Schwarz gives

$$
2v_i\le-M_i\operatorname{Cov}_i(q,H_i)
\le\sqrt{v_iM_i\operatorname{Var}_i(H_i)}.
$$

For $v_i>0$ divide and square; if $v_i=0$, (6.3) is immediate. $\square$

**Theorem 6.3 (Equivalent screening conditions).** For the actual optimizer, the following conditions are equivalent:

1. $v_i=0$.
2. $q_y=c_i$ for every $y\in S_i$.
3. $H_i$ is constant on $S_i$.
4. $H_i(y)=1-2c_i$ for every $y\in S_i$.
5. $\langle H_i\rangle_i=1-2c_i$.

Proof. Positivity of every $m_y$ makes the first two equivalent. If $q$ is constant, all internal gradients vanish by Lemma 4.4, and (5.3) forces the fourth condition. The fourth implies the third and fifth. If $H_i$ is constant, its covariance with $q$ is zero; (6.2) and nonnegativity give $v_i=0$.

Finally suppose the fifth condition holds. The sum in (6.1) is then zero. If $q_y\ne q_z$ on some edge, its weighted average $\theta_e$ is strictly less than $1/2$, because both entries are at most $1/2$ and both weights are strictly positive. That edge would have a strictly positive summand in (6.1). Hence $q_y=q_z$ on every edge. Connectivity from Lemma 4.2 makes $q$ constant on $S_i$. This proof also covers a singleton, whose edge sum is empty. $\square$

The mean excess in (6.1) detects nonconstancy, but its sign is the opposite of a positive context-free lower certificate in §7. Neither this equivalence nor the variance upper bound asserts a positive variance at any particular length.

## 7. Nonnegative coordinate probes and the response-density certificate

**Definition 7.1 (Actual response shortfall).** A probe is a function $f:S_i\to[0,1]$. It depends on at most $s$ specified exterior coordinates if there is a set $K\subseteq[1,n]\setminus\{i\}$ with $|K|\le s$ such that $f_y$ is a function only of $(y_k)_{k\in K}$. Dependence on coordinates fixed by the reset is allowed. Define

$$
d_i(f)=\bigl[\langle f(1-2c_i-H_i)\rangle_i\bigr]_+,
\qquad [t]_+=\max\{t,0\}.
\tag{7.1}
$$

The notation measures a signed conditional shortfall under the actual reset-complement distribution. The probe is not a newly chosen conditional law.

**Theorem 7.2 (Uniform bound for $s$-coordinate probes).** For every integer $s\ge1$ and every probe $f:S_i\to[0,1]$ depending on at most $s$ specified exterior coordinates as in Definition 7.1,

$$
v_i\ge\frac{M_i\,d_i(f)^2}{(1+4s/3)^2}.
\tag{7.2}
$$

For a one-coordinate probe, in particular $f_y=\mathbf1_{\{y_k=b\}}$ with $k\ne i$ and $b\in\{0,1\}$,

$$
v_i\ge\frac9{49}M_i\,d_i(f)^2.
\tag{7.3}
$$

Proof. Suppress $i$ temporarily, writing $M,c,v,H$ for the corresponding quantities. Multiply (5.3) by $f_y$ and sum. Rearranging gives

$$
M\langle f(1-2c-H)\rangle_i
=2\sum_y m_yf_y(q_y-c)
+\sum_{e=\{y,z\}}\nabla J_e(q_y,q_z)\mathbin{\cdot}(f_y,f_z).
\tag{7.4}
$$

By (4.7), each edge contribution on the right is exactly

$$
\frac{2C_e\delta_e(f_y-f_z)}{d_e}
-\frac{C_e\delta_e^2(1-2\theta_e)
[\alpha f_y+(1-\alpha)f_z]}{d_e^2}.
\tag{7.5}
$$

The second displayed term is subtracted and is nonnegative before subtraction: $f\ge0$ and $\theta_e\le1/2$. Thus it may be dropped in an upper bound for (7.4). This is the sign that requires a nonnegative probe; the argument does not assert the same bound for arbitrary signed probes.

Since the weighted mean of $q-c$ is zero, and a variable in $[0,1]$ has variance at most $1/4$,

$$
2\left|\sum_y m_yf_y(q_y-c)\right|
=2M|\operatorname{Cov}_i(f,q)|
\le2\sqrt{Mv\operatorname{Var}_i(f)}
\le\sqrt{Mv}.
\tag{7.6}
$$

For the internal edges, $C_e/h(a,b)=ab/(a+b)^2\le1/4$ and $d_e\ge3/16$, hence

$$
\frac{2C_e}{d_e}\le\frac83h(m_y,m_z).
\tag{7.7}
$$

Let $\mathcal E_K$ consist of all internal edges whose flipped coordinate belongs to $K$. Outside this set $f_y=f_z$; inside it $|f_y-f_z|\le1$. For each one of these coordinates its edges form a matching. Since $h(a,b)\le(a+b)/4$, summing over at most $s$ such matchings gives

$$
\sum_{e\in\mathcal E_K}h(m_y,m_z)\le\frac{sM}{4}.
\tag{7.8}
$$

For any real $u,v'$ and positive $a,b$,

$$
au^2+b(v')^2-\frac{ab}{a+b}(u-v')^2
=\frac{(au+bv')^2}{a+b}\ge0.
$$

Apply this with $u=q_y-c$, $v'=q_z-c$. A vertex occurs at most once in each coordinate matching, so

$$
\sum_{e\in\mathcal E_K}h(m_y,m_z)(q_y-q_z)^2\le sv.
\tag{7.9}
$$

Weighted Cauchy--Schwarz applied to (7.8)--(7.9) gives

$$
\sum_{e\in\mathcal E_K}h(m_y,m_z)|q_y-q_z|
\le\frac s2\sqrt{Mv}.
\tag{7.10}
$$

After dropping the nonpositive part of (7.5), bound its remaining term above by its absolute value and use (7.7) and (7.10). Together with (7.6), equation (7.4) yields

$$
M\langle f(1-2c-H)\rangle_i
\le(1+4s/3)\sqrt{Mv}.
\tag{7.11}
$$

The right side is nonnegative. Taking the positive part on the left and squaring, using $M>0$, proves (7.2), including the case $v=0$. Setting $s=1$ gives (7.3). The estimates use matchings and the actual masses, not any independence or product structure. $\square$

**Lemma 7.3 (Uniform reset-event floor).** For every actual reset index,

$$
M_i\ge\frac1{256}.
\tag{7.12}
$$

Proof. From (1.6), the full-complement posterior at every coordinate is at most $1/2$, including forced fibers. For any event $A$ depending only on the other coordinates,

$$
\pi_n(A,W_j=0)=\mathbb E_{\pi_n}[\mathbf1_A(1-a_{n,j})]
\ge\frac12\pi_n(A).
\tag{7.13}
$$

If $A$ also forces both existing neighbors of $j$ to be zero, the lower band gives

$$
\pi_n(A,W_j=1)=\mathbb E_{\pi_n}[\mathbf1_Aa_{n,j}]
\ge\frac14\pi_n(A).
\tag{7.14}
$$

First prescribe zero at every existing site in

$$
\{i-3,i-1,i+1,i+3\}\cap[1,n].
$$

There are at most four distinct such sites. Successive applications of (7.13) give the resulting event probability at least $2^{-4}$. Now prescribe one first at $i-2$ and then at $i+2$. Each current conditioning event is external to the site being specified and makes all its existing neighbors zero. Two applications of (7.14) give probability at least $2^{-4}4^{-2}=1/256$ to an event contained in $E_i$. Missing neighbors at open endpoints reduce the number of zero prescriptions and do not weaken the bound. This establishes an event floor, not a positive posterior variance. $\square$

**Corollary 7.4 (Finite same-optimizer certificate).** For any subset $I_n\subseteq\{3,\ldots,n-2\}$, choose a one-coordinate probe $f_i$ at each of its sites and put $d_i=d_i(f_i)$. Then

$$
V_2(n)\ge\frac9{49}\sum_{i\in I_n}M_id_i^2
\ge\frac9{12544}\sum_{i\in I_n}d_i^2.
\tag{7.15}
$$

In particular,

$$
\sum_{i\in I_n}d_i^2>\frac{12544}{9}\tau
\quad\Longrightarrow\quad V_2(n)>\tau.
\tag{7.16}
$$

If $J=|I_n|$ and every $d_i\ge\varepsilon>0$, the sufficient condition is $J\varepsilon^2>(12544/9)\tau$.

Proof. Sum (7.3) over these sites, use nonnegativity of the omitted site variances, and then use (7.12). Each summand is a distinct site term of the original $V_2(n)$. Overlap between reset events or probe events creates no double counting of a site and needs no independence assumption. All quantities in the sum refer to this same $\pi_n$. The strict comparisons follow directly. $\square$

For probes of at most $s$ coordinates the same argument gives

$$
V_2(n)\ge\frac1{256(1+4s/3)^2}
\sum_{i\in I_n}d_i(f_i)^2.
\tag{7.17}
$$

**Corollary 7.5 (Conditional response-density consumer).** Suppose there are constants $\beta,\varepsilon>0$ and an unbounded set of lengths $n$ such that the actual $\pi_n$ at each of these lengths has at least $\beta n$ reset indices with one-coordinate probes satisfying $d_i(f_i)\ge\varepsilon$. At every such length,

$$
V_2(n)\ge\frac9{12544}\beta\varepsilon^2 n.
\tag{7.18}
$$

It follows that some finite length has $V_2(n)>\tau$.

Proof. Apply (7.15) separately at each of the stated lengths. Since the coefficient in (7.18) is positive and the set of lengths is unbounded, one exceeds $12544\tau/(9\beta\varepsilon^2)$. No convergence, stationarity, projectivity or independence of the sequence of optimizers is used. The premise asserts the quantitative response density; the conclusion does not establish that premise. $\square$

**Proposition 7.6 (The constant probe has the wrong sign).** For every reset site,

$$
d_i(1)=0.
\tag{7.19}
$$

Every nonnegative constant probe, including a probe of a bit fixed under $E_i$, also has zero shortfall.

Proof. Theorem 6.1 says $1-2c_i-\langle H_i\rangle_i\le0$. Take its positive part, or multiply it by any nonnegative constant first. $\square$

The nearest exterior coordinates that can vary under a reset are $i-4$ and $i+4$, when present: the intervening anchor and its neighboring sites are fixed. Their availability does not prove a positive probe. Strictly positive word probabilities, a positive mean excess in (6.1), or one finite nonzero $v_i$ do not supply the quantitative premise of Corollary 7.5. The one-coordinate probes are sufficient detectors; failure of these detectors is not a proof that the variance threshold can never be crossed.

## 8. The conditional endpoint consumer on the whole exact-real domain

**Definition 8.1 (All finite hidden producers and one actual law).** For each $N\ge1$ retain

$$
\Theta_N=\left\{(\lambda,M_0,M_1):
\begin{array}{l}
\lambda\ge0,\quad\lambda\mathbf1=1,\quad M_0,M_1\ge0,\\
A=M_0+M_1,\quad A\mathbf1=\mathbf1,\quad\lambda A=\lambda,\\
\lambda M_1^2\mathbf1=0
\end{array}\right\}.
\tag{8.1}
$$

Here $\lambda$ is a row and the matrices are $N\times N$, with arbitrary exact-real entries. Zero stationary masses, structural zeros, reducibility and periodicity are all allowed. The legality condition is scalar, not entrywise $M_1^2=0$.

For $\theta\in\Theta_N$, [Universal, Definition 4.1 and Proposition 4.2][U] supplies the actual stationary joint law $J_\theta$ of hidden states $\mathsf H_j$ and visible bits $X_j$ with

$$
J_\theta(\mathsf H_a=h_a,\ldots,\mathsf H_{b+1}=h_{b+1},
X_a=x_a,\ldots,X_b=x_b)
=\lambda_{h_a}\prod_{j=a}^b M_{x_j}(h_j,h_{j+1}).
\tag{8.2}
$$

Let $X_j(x)=x_j$ and let $[w]_a$ specify $X_a\cdots X_{a+|w|-1}=w$. With $M_w=M_{w_1}\cdots M_{w_m}$ and $M_\varepsilon=I$, the visible marginal $P_\theta$ satisfies

$$
P_\theta([w]_a)=\lambda M_w\mathbf1,
\qquad
\mathsf X=\{x\in\{0,1\}^{\mathbb Z}:x_jx_{j+1}=0\ \forall j\},
\qquad P_\theta(\mathsf X)=1.
\tag{8.3}
$$

Every seam uses the ordered product of the same matrices. The time unit is one original emitted bit. The scalar response $H_i$ in (4.4) is unrelated to the hidden-state symbol $\mathsf H_j$ in this definition.

**Definition 8.2 (The three extra endpoint premises).** For a stationary legal law $P$ write $\mathcal E_j=\sigma(X_k:k\ne j)$, $F_j=\{X_{j-1}=X_{j+1}=0\}$ and $(Tx)_j=x_{j+1}$. Choose an exterior Borel version of $q_0^P=\mathbb E_P[X_0\mid\mathcal E_0]$, set $q_j^P=q_0^P\circ T^j$, and put $\ell_j^P=(X_j-q_j^P)^2$. The posterior band is

$$
\mathsf B(P):\quad q_j^P=0\text{ on }F_j^c,\qquad
\frac14\le q_j^P\le\frac12\text{ on }F_j,
\quad P\text{-almost surely for every }j.
\tag{8.4}
$$

The one-sided erasure errors and their required sum are

$$
\begin{aligned}
p_r^L&=\mathbb E_P[X_0\mid X_{-r},\ldots,X_{-1},X_1,X_2,\ldots],&
e_L(r)&=\mathbb E_P(q_0^P-p_r^L)^2,\\
p_r^R&=\mathbb E_P[X_0\mid\ldots,X_{-2},X_{-1},X_1,\ldots,X_r],&
e_R(r)&=\mathbb E_P(q_0^P-p_r^R)^2,\\
A_P&=\sum_{r\ge0}(\sqrt{e_L(r)}+\sqrt{e_R(r)}).&&
\end{aligned}
\tag{8.5}
$$

At $r=0$ each field still contains the entire opposite half-line. Under the band and $A_P<\infty$, [Guarded, Lemma 2.2] supplies a Borel conull set saturated under legal finite modifications on which

$$
\Delta_P(x,z)=\sum_{j\in\mathbb Z}
\bigl(\ell_j^P(x)-\ell_j^P(z)\bigr)
\tag{8.6}
$$

is absolutely convergent whenever $x,z$ differ at finitely many sites. Every loss remains the fixed original-$P$ function even after a modification. Strong zero, $\mathsf Z_\Delta(P)$, asserts that this sum is zero for every such pair on a saturated conull set. This is a pathwise extra premise, not merely a vanishing expected first variation.

The three premises in the consumer are all of $\mathsf B(P)$, $A_P<\infty$ and $\mathsf Z_\Delta(P)$. They do not redefine $\Theta_N$.

**Definition 8.3 (The inherited global rank discrepancy).** For a positive law $r$ on $B_n$, let $r_j(w_{-j})$ be its full-complement posterior, zero at forced fibers. Extend $r$ by zero to every illegal binary word. At an internal cut define

$$
\mathsf F_k(r)(s,t)=r(st),\qquad
s\in\{0,1\}^k,\quad t\in\{0,1\}^{n-k}.
\tag{8.7}
$$

Let $\mathscr F_{N,n}^{0,0}$ be the probabilities satisfying the insertion bounds on every legal edge and having nonnegative rank at most $N$ at every cut (8.7). Nonnegative rank is the least number of nonnegative rank-one summands. The insertion bounds imply positivity on the connected legal graph, as in [Guarded, Lemma 3.3]. The family is compact and, when nonempty, its continuous discrepancy attains its minimum by [Guarded, Definition 6.3]. Put

$$
\mathcal D_{B_n}(\pi_n\Vert r)
=\sum_{j=1}^n\mathbb E_{\pi_n}(a_{n,j}-r_j)^2,
\qquad
\mathcal R_{N,n}=\min_{r\in\mathscr F_{N,n}^{0,0}}
\mathcal D_{B_n}(\pi_n\Vert r),
\tag{8.8}
$$

with $\min\varnothing=+\infty$. At $n=1$ there are no internal cuts. A singleton conditional completion graph has its unique law and zero discrepancy; a zero-mass conditioning event has zero weighted contribution and no conditional denominator. Illegal seam entries are retained as zeros in (8.7).

Each candidate $r$ in (8.8) is one global law. Its different conditionals cannot be fitted independently. Such rank families are necessary relaxations and are not asserted to characterize stationary producers or common-matrix representations.

**Premise 8.4 (Credited reset and guarded-budget interfaces).** [Global/local rank compatibility, Lemmas 2.1--2.2 and Theorem 2.3][R] supplies the ordinary-rank-two reset necessity and the resulting lower bound

$$
\mathcal R_{2,n}\ge V_2(n).
\tag{8.9}
$$

The mechanism is that rank at most two at every cut of a positive no11 law forces conditional independence across each occupied one. On $E_i$, its center posterior is therefore constant across the entire distant complement. Projecting the actual $a_{n,i}$ onto such a constant costs at least $v_i$. Nonnegative rank at most two implies the ordinary rank condition needed for this direction. No converse or realization equivalence is used.

For the same actual $J_\theta/P_\theta$, [Guarded, Theorem 6.2] supplies the cut-rank bound for its guarded conditional kernels. [Guarded, Theorem 5.1 and Corollary 6.4] supplies

$$
\begin{gathered}
\mathsf B(P_\theta),\quad A_{P_\theta}<\infty,\quad
\mathsf Z_\Delta(P_\theta)\\
\Longrightarrow\quad d(P_\theta)=c_\star,\qquad
\mathcal R_{N,n}\le(n+2)c_\star-\kappa_n-\frac1{24}
\le\tau\quad\text{for every }n.
\end{gathered}
\tag{8.10}
$$

Writing $P_{[1,n]}$ for the actual length-$n$ marginal, the density supplied by [Universal, (1.5)][U] is

$$
d(P)=\lim_{n\to\infty}\frac{\Phi_n(P_{[1,n]})}{n}
=\mathbb E_P(X_0-q_0^P)^2\le c_\star.
\tag{8.11}
$$

The finite $\pi_n$ used in (8.8)--(8.10) is unchanged. The guarded kernels come from the one actual producer law; they do not replace $\pi_n$ in the reset variances.

**Corollary 8.5 (Conditional dimension-two exclusion).** A strict threshold crossing $V_2(n)>\tau$ at any length, including one obtained from (7.16) or Corollary 7.5, excludes the simultaneous three premises in (8.10) for every $\theta\in\Theta_2$.

Proof. Such a producer would satisfy $V_2(n)\le\mathcal R_{2,n}\le\tau$ by (8.9)--(8.10). This contradicts the stated strict crossing. The argument requires all three extra premises and does not turn their conjunction into a definition of the producer domain. $\square$

Theorem 3.3 rules out the trigger of this particular consumer through length $98$. It does not exclude a different rank-discrepancy certificate at those lengths, and neither that theorem nor Corollary 8.5 establishes any trigger at a larger length.

## 9. Unresolved quantitative and original attainment questions

**Open Question 9.1 (Actual-optimizer response and threshold).** Does some $n\ge99$ satisfy $V_2(n)>\tau$? In particular, do the actual responses $H_i$ admit probes for which the sum in (7.16) crosses its stated threshold, or a family meeting the positive-density premise of Corollary 7.5?

No positive shortfall $d_i(f)$, no positive variance at a specified length $n\ge7$, and no uniform density of either are established here. The equations characterize the quantities to be controlled, but do not construct or evaluate an optimizer. The fixed-exterior comparison in §3 is an upper bound and cannot be used as a lower bound. The event floor in Lemma 7.3 supplies only event frequency. The mean and covariance identities supply neither independently prescribable anchor data nor an obstruction to every possible future growth proof.

[Global/local rank compatibility, Theorems 4.4 and 5.1][R] exhibits one coherent comparison process whose independently fitted fixed-block defects vanish while its global rank-two discrepancy grows. Those results concern that process's marginals, not $\pi_n$. They warn against deducing accumulated defects from finite positivity. They do not answer this actual-optimizer question, prove a bulk limit for $\pi_n$, or disprove the global relaxation on $\pi_n$.

**Open Question 9.2 (Attainment versus the extra endpoint premises).** [Universal, Theorem 3.1][U] makes the band necessary for any stationary attainer. It remains unproved here that every hypothetical finite-hidden attainer has $A_P<\infty$, or that attainment or its first-order balances imply the strong pathwise property $\mathsf Z_\Delta(P)$.

Neither structural zeros, zero stationary masses, reducibility nor periodicity is removed to obtain a generic forgetting assertion. An exclusion of the three-premise endpoint becomes a nonattainment theorem only after these missing bridges, or after a different complete exclusion argument. The implication in (8.10) is from the three premises to attainment; reversing it is not justified.

**Open Question 9.3 (The original whole-domain finite-attainment alternative).** On the entire exact-real $\Theta_N$ in (8.1), define

$$
\begin{aligned}
D_r(P)&=\mathbb E_P\left(X_0-
\mathbb E_P[X_0\mid X_{-r},\ldots,X_{-1},X_1,\ldots,X_r]\right)^2,\\
C_N&=\sup_{\theta\in\Theta_N}d(P_\theta),\qquad
U_{N,r}=\max_{\theta\in\Theta_N}D_r(P_\theta),\qquad r\ge1.
\end{aligned}
\tag{9.1}
$$

Still decide whether some finite $N$ and $\theta\in\Theta_N$ attain $d(P_\theta)=c_\star$, or whether $C_N<c_\star$ for every finite $N$. [Universal, Theorem 6.2][U] supplies attainment of each $C_N$, the identity $C_N=\inf_rU_{N,r}$, and the equivalence of the negative alternative with

$$
\forall N\ge1\ \exists r,m\ge1:\qquad
U_{N,r}<\frac{\kappa_m}{m+1}.
\tag{9.2}
$$

The compact domain includes the zero-mass and reducible presentations; it is not restricted to full-support parameters. An attained visible law has full support by the supplied attained-law theorem. Padding by zero-mass hidden states preserves the law, so the finite-budget existence quantifier is unchanged.

The response-density route here addresses a sufficient test at dimension two and supplies no all-$N$ separation pairs. No actual finite attaining $J_\theta/P_\theta$ is constructed. Even a future dimension-two endpoint exclusion would leave (9.2) unpaid. At $N=1$ scalar legality forces $M_1=0$, so the visible law is all zero and fails the free-site band; this boundary observation does not settle arbitrary finite $N$.

## 10. Sources, mathematical ownership and scope

The finite-size comparison, the reset-slice internal-edge and anchor identities, and the nonnegative-probe inequalities in §§3--7 are the substantive source-level development of this volume. Their proofs retain the full finite objective and its original law. The endpoint result in Corollary 8.5 is a conditional composition of supplied interfaces. It adds no new rank-to-producer or attainment-to-strong-zero implication.

| Canonical source | Exact interface used and its scope |
| --- | --- |
| [FIB legal-edge-load growth constant][G], `FIB_LEGAL_EDGE_LOAD_GROWTH_CONSTANT.md` | Lemma 3.1 and Theorems 3.2 and 5.2, as supplied in Universal Convention 1.3: the elementary properties of $h$ and the original growth bounds. |
| [FIB legal-edge-load positive unique optimizer][O], `FIB_LEGAL_EDGE_LOAD_POSITIVE_UNIQUE_OPTIMIZER.md` | Theorem 3.1 and equation (3.11), as identified in Universal Convention 1.3 and Lemma 2.1: optimizer positivity, insertion inequalities and the original whole-simplex square-gap identity. Existence, uniqueness and that identity are not new claims of this volume. |
| [FIB 合法边调和负载：普适后验缺陷与有限隐藏维数分离][U], `FIB_LEGAL_EDGE_LOAD_UNIVERSAL_POSTERIOR_DEFECT_AND_FINITE_HIDDEN_SEPARATION.md` | Definition 1.1, Convention 1.3 and Lemma 2.1: complete objective and optimizer interfaces. Equation (1.5), Theorem 3.1, Definition 4.1 and Proposition 4.2: density, necessary band, entire parameter domain and actual joint/visible law. Theorem 6.2 and Open Problem 7.4: the unchanged compact-domain separation alternative. |
| [Guarded] *FIB harmonic-edge load: guarded replacement, attainment and conditional-rank obstruction* | Definition 1.1: the ceiling $\bar c$. Definitions 2.1 and 2.3 and Lemma 2.2: band, erasure sum and strong-zero cocycle. Lemma 3.3 and Definition 6.3: rank families. Theorem 6.2: conditional rank from the actual matrices. Theorem 5.1, Corollaries 5.3 and 6.4: the sufficient endpoint and finite discrepancy budget, including the $1/24$ guard cost. Theorem 7.1 keeps all conditionals tied to one optimizer. |
| [FIB harmonic-edge load: global and local rank compatibility and the reset-variance obstruction][R], `FIB_LEGAL_EDGE_LOAD_GLOBAL_LOCAL_RANK_COMPATIBILITY_AND_RESET_VARIANCE_OBSTRUCTION.md` | Lemmas 2.1--2.2, Theorem 2.3 and Corollary 2.4: the rank-two reset necessity, $\mathcal R_{2,n}\ge V_2(n)$ and its conditional threshold consumer. Theorems 4.4 and 5.1: the coherent comparison-process warning, used only within that process's stated scope. |

Finite-simplex differentiation, concavity, the interval-variance bound, conditional least squares, convex tangent inequalities, graph matchings and weighted Cauchy--Schwarz are classical tools. The needed finite calculations are displayed here. This source-level synthesis makes no claim of worldwide originality, exhaustive literature coverage, independently diverse priors, empirical learning benefit, formal verification or completion of the original attainment problem.

[G]: FIB_LEGAL_EDGE_LOAD_GROWTH_CONSTANT.md
[O]: FIB_LEGAL_EDGE_LOAD_POSITIVE_UNIQUE_OPTIMIZER.md
[U]: FIB_LEGAL_EDGE_LOAD_UNIVERSAL_POSTERIOR_DEFECT_AND_FINITE_HIDDEN_SEPARATION.md
[R]: FIB_LEGAL_EDGE_LOAD_GLOBAL_LOCAL_RANK_COMPATIBILITY_AND_RESET_VARIANCE_OBSTRUCTION.md

## 追加锚（本行以下为增补区）
