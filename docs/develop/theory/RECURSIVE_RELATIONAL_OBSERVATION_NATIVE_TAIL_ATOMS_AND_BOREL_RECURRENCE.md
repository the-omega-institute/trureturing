# Native tail atoms and endpoint recurrence on Borel common flows

## 1. The original common-flow problem

**Convention 1.1 (source and scope).** Fix the original prior supported
exactly on $\{1,2,3\}$, with all three masses positive, and the original
parameters $m=2,d=1,\ell=2,n=4$. The source samples $K$ once before any
paid Read. Conditional on this same $K$, seed and payload letters have
alpha probabilities $r_1=a=1/3$, $r_2=b=2/5$, $r_3=3/8$. Equal seed pairs
remain paid rejections; both accepted unequal seeds remain. A payload
alpha at p completes marker 0, a beta suspends, and at suspension an alpha
returns to p while a beta completes marker 1.

The full original control retains the parser, selectors, marker tree,
bare and held records, write and latch flags, permissions, completion
and delivery. The third write precedes its latch in the same update.
Fourth completion enables its matching Stop, and neither terminal permits
a Read. Every positive finite paid rejection, partial parse and return
history remains in the risk domain. The current-record renderer retains
every future letter and its original operation block, including the
infinite noncompletion outcome. It is the complete-law TV isometry of
[PAIR, Section 2] and [PAID, Definition 1.2].

Initialization is source-independent. Acquired and synthetic letters use
identical update kernels. COMPLETE includes the original control,
installed program and numbers, selectors, addresses, labels, output
cursors, sampling states, workspace and persistent randomness. No source
reset, newly sampled depth, clock, posterior port or readable probability
row is available. All operators and path laws below are analysis objects.

**Definition 1.2 (full laws and compatible flows).** Put

$$
z_a=a(1-a)=\frac29,\qquad z_b=b(1-b)=\frac6{25},\qquad
c_a=(1-a)^2=\frac49,\qquad c_b=(1-b)^2=\frac9{25}.
\tag{1.1}
$$

The p carrier consists of
$w_{n,0}=(\beta\alpha)^n\alpha$,
$w_{n,1}=(\beta\alpha)^n\beta\beta$, $n\ge0$, and $\infty_p$.
The suspended carrier consists of beta, the words $\alpha w_{n,i}$,
and $\infty_\beta$. The native laws are

$$
P_{p,r}(w_{n,0})=r[r(1-r)]^n,\qquad
P_{p,r}(w_{n,1})=(1-r)^2[r(1-r)]^n,\qquad
P_{\beta,r}=(1-r)\delta_\beta+r\alpha P_{p,r}.
\tag{1.2}
$$

Their infinite masses are zero. Use the exact regular descriptor spaces
of [PAIR, (11.1)--(11.2)], with $\lambda=4/15$:

$$
\begin{aligned}
T_p(j)&=\{w_{n,i}:n\ge j,\ i=0,1\}\cup\{\infty_p\},\\
T_\beta(j)&=\{\alpha w_{n,i}:n\ge j,\ i=0,1\}
                       \cup\{\infty_\beta\},\\
\mathcal K_p&=\{Q:a\le Q(\alpha)\le b,\
                       Q(T_p(j))\le\lambda^j\text{ for all }j\ge0\},\\
\mathcal K_\beta&=\{W:a\le1-W(\beta)\le b,\
                       W(T_\beta(j))\le b\lambda^j\text{ for all }j\ge0\}.
\end{aligned}
\tag{1.3}
$$

Every descriptor is a normalized probability law; both spaces carry
complete-law TV. Write

$$
u(Q)=Q(\alpha),\qquad v(W)=1-W(\beta),\qquad
\mathcal R_B(Q)=\frac{Q(\beta\,\cdot)}{1-u(Q)},\qquad
\mathcal R_A(W)=\frac{W(\alpha\,\cdot)}{v(W)}.
\tag{1.4}
$$

A pair in the original domain $\mathfrak C$ consists of Borel probability
flows $\Gamma_B$ on $\mathcal K_p\times\mathcal K_\beta$ and $\Gamma_A$
on the reversed product, with

$$
(\Gamma_B)_1=(\Gamma_A)_2=\nu_p,\qquad
(\Gamma_B)_2=(\Gamma_A)_1=\nu_\beta,
\tag{1.5}
$$

whose disintegrations $B(Q,dW)$ and $A(W,dQ')$ satisfy

$$
\mathcal R_B(Q)=\int W\,B(Q,dW),\qquad
\mathcal R_A(W)=\int Q'\,A(W,dQ')
\tag{1.6}
$$

almost surely, as equalities of full measures. These condition on the
entire input descriptor. Equivalently, each complete-coordinate residual
vanishes against every bounded Borel input test. Infinite coordinates
remain among the tests. The two margins in (1.5) are unweighted acquired
margins, not synthetic survival margins.

**Definition 1.3 (the boxed class and the unchanged objective).** Denote
by $\mathfrak C_{\rm box}$ the pairs in $\mathfrak C$ satisfying both
full endpoint boxes:

$$
\min\{P_{s,a}(e),P_{s,b}(e)\}
\le D_s(e)\le
\max\{P_{s,a}(e),P_{s,b}(e)\}
\quad\text{for every complete atom }e,\quad \nu_s\text{-a.s.}
\tag{1.7}
$$

Here $D_p=Q$ and $D_\beta=W$. The original three-depth objective remains

$$
\begin{aligned}
\mathcal J(\Gamma_B,\Gamma_A)
 &=\max_{s\in\{p,\beta\},\,k\in\{1,2,3\}}
       \left\{\int\operatorname{TV}(D_s,P_{s,r_k})\,d\nu_s-\rho_s\right\},\\
\rho_p&=\frac{1116529}{22781250},\qquad
\rho_\beta=\frac{239}{6750},\qquad
j_c=\min_{\mathfrak C}\mathcal J.
\end{aligned}
\tag{1.8}
$$

TV is inside the configuration integral. Zero $\mathcal J$ means zero
excess over these nonzero phase benchmarks, not zero raw prediction error.
[PAIR, Section 11.8] supplies (1.7) at zero excess and the two means

$$
\begin{aligned}
E_p&=\{w_{0,1},w_{1,1},w_{2,1}\},&
\int Q(E_p)\,d\nu_p&=\frac{11758471}{22781250},\\
E_\beta&=\{\beta,\alpha w_{0,1}\},&
\int W(E_\beta)\,d\nu_\beta&=\frac{5261}{6750}.
\end{aligned}
\tag{1.9}
$$

Both depth-3 losses in (1.8) remain required. The results below do not
replace that unrestricted minimum by a minimum over a recurrence class.

## 2. The upper tail reads an actual native atom

**Theorem 2.1 (upper-endpoint tail atom).** For every pair in
$\mathfrak C_{\rm box}$, with arbitrary Borel phase marginals, put

$$
m_b=\nu_p(\{P_{p,b}\}),\qquad
d_n=\int Q(w_{n,1})\,d\nu_p(Q).
\tag{2.1}
$$

Then

$$
\lim_{n\to\infty}\frac{Q(w_{n,1})}{z_b^n}
 =c_b\,\mathbf1_{\{P_{p,b}\}}(Q)
\quad(\nu_p\text{-a.e. }Q),\qquad
\lim_{n\to\infty}\frac{d_n}{z_b^n}=c_bm_b.
\tag{2.2}
$$

No finite-support, deterministic-successor, reversibility, mixing,
eventual-recurrence or zero-excess hypothesis is imposed. In particular
$m_b=0$ implies $d_n=o(z_b^n)$, not a strictly smaller exponential
growth rate.

**Proof.** All almost-everywhere equations may be placed on full-measure
sets closed under the acquired transitions: remove the null exceptional
sets, then their positive-probability predecessors, countably many times.
Stationarity in (1.5) keeps the removed sets null. Weighted kernels below
have the same null sets because all their weights are strictly positive.

Let $C=BA$ be the unweighted acquired return kernel on p descriptors.
Thus $\nu_pC=\nu_p$. Define the positive kernel and completion function

$$
\begin{aligned}
L(Q,dQ')&=(1-u(Q))\int v(W)A(W,dQ')\,B(Q,dW),\\
g(Q)&=Q(w_{0,1})
 =(1-u(Q))\int(1-v(W))\,B(Q,dW).
\end{aligned}
\tag{2.3}
$$

Iteration of the original full residual equations, with Tonelli for
nonnegative terms, gives

$$
Q(w_{n,1})=(L^ng)(Q),\qquad
Q(w_{n,0})=(L^nu)(Q).
\tag{2.4}
$$

This is a conditional path integral on the one common acquired chain;
it makes no claim about boxes on individual sampled path products.
Regularity gives

$$
c_b\le g\le c_a,\qquad
\frac15C\le L\le\frac4{15}C.
\tag{2.5}
$$

The upper endpoint at $w_{3,1}$ is $c_bz_b^3$, since

$$
c_bz_b^3-c_az_a^3=\frac{254584}{2562890625}>0.
$$

Consequently (1.7) gives $L^3g\le c_bz_b^3$.
Write $T=L/z_b$, $e=g-c_b\ge0$, and set

$$
h=\frac{g+Tg+T^2g}{3},\qquad
\delta=h-Th=\frac{g-T^3g}{3}\ge\frac e3.
\tag{2.6}
$$

The measurable function $h$ has bounds $0<h_-\le h\le h_+<\infty$.
For example $h_-=c_b/3$ is valid, while (2.5) bounds the other terms.
Thus

$$
M(Q,dQ')=T(Q,dQ')\frac{h(Q')}{h(Q)}
\tag{2.7}
$$

is a substochastic kernel. Its one-step killing probability is

$$
k(Q)=1-M\mathbf1(Q)=\frac{\delta(Q)}{h(Q)}
 \ge\frac{e(Q)}{3h_+}.
\tag{2.8}
$$

This finite-block construction of $h$ needs no eigenfunction theorem.

There is also a pointwise kernel domination tied to the same $e$.
Since $v\le b$ and $g\ge(1-u)(1-b)$,

$$
T\le\frac{1-u}{1-b}\,C
 \le\frac g{c_b}\,C
 =\left(1+\frac e{c_b}\right)C.
\tag{2.9}
$$

The cost of changing path measure is therefore controlled by the
quantity which pays for killing in (2.8).

Consider the killed chain with kernel $M$ and initial law $\nu_p$,
and let $\mathsf I$ be its event of surviving forever. Its row mass is
strictly positive, by (2.5) and the bounds on $h$. Normalize each row of
$M$ to a Markov kernel and apply the row masses as survival probabilities.
Conditional on an infinite path of that normalized kernel, survival
forever has probability $\prod_{i\ge0}(1-k(Q_i))$. This product is zero
if $\sum_i k(Q_i)=\infty$. Equation (2.8) proves

$$
\sum_{i\ge0}e(Q_i)<\infty
\quad\text{almost surely on }\mathsf I.
\tag{2.10}
$$

Let $\mathbb P_C$ be the stationary, unweighted $C$-path law.
For any $n$, the distribution of the first $n$ surviving steps of $M$
is absolutely continuous with respect to the corresponding $C$ path.
The Radon--Nikodym product, using (2.7)--(2.9), is bounded by

$$
\frac{h(Q_n)}{h(Q_0)}
 \prod_{i<n}\left(1+\frac{e(Q_i)}{c_b}\right)
\le
\frac{h_+}{h_-}
\exp\left(\frac1{c_b}\sum_{i<n}e(Q_i)\right).
\tag{2.11}
$$

For an integer $R\ge1$, restrict the immortal-path measure to
$\sum_i e(Q_i)\le R$. On every event depending on finitely many
coordinates, (2.11) bounds this finite measure by
$(h_+/h_-)\exp(R/c_b)\mathbb P_C$. The inequality extends from the
cylinder algebra to the full path sigma algebra by the monotone class
theorem. Taking the increasing union in $R$, and using (2.10), shows
that the entire immortal-path measure is absolutely continuous with
respect to $\mathbb P_C$, and is supported on

$$
\mathsf E=\left\{\sum_{i\ge0}e(Q_i)<\infty\right\}.
\tag{2.12}
$$

We now identify this event under the stationary acquired law. It is
invariant under deleting the first path coordinate. If
$\mathbb P_C(\mathsf E)>0$, conditioning on $\mathsf E$ therefore
preserves stationarity. On $\mathsf E$ the time averages of the bounded
nonnegative function $e(Q_i)$ tend to zero. Bounded convergence and
conditional stationarity imply
$\mathbb E_C[e(Q_0)\mid\mathsf E]=0$. Hence $e(Q_i)=0$ for every
$i\ge0$, almost surely on $\mathsf E$. The assertion is empty if that
event has probability zero.

To recover the full descriptor, define
$f(Q)=\mathbb P_C(\mathsf E\mid Q_0=Q)$. The Markov property and the
invariance of (2.12) give $Cf=f$ almost surely. Since $0\le f\le1$,
stationarity gives the exact identity

$$
\mathbb E_C[(f(Q_1)-f(Q_0))^2]
=2\int f^2\,d\nu_p-2\int f\,Cf\,d\nu_p=0.
\tag{2.13}
$$

Also $f=0$ almost everywhere on $\{e>0\}$ by the preceding paragraph.
Thus $H=\{f>0\}$ is, up to null sets, a $C$-closed set on which
$g=c_b$. On $H$, equality in the lower bound for $g$ in (2.5) forces
$u=b$ and $v=b$ on every conditional positive B successor, almost surely.
The composition $BA$ stays in $H$, so on this set $L=z_b C$ and
$u=b$, $g=c_b$. Formula (2.4) now gives every finite coordinate of
$P_{p,b}$, and (1.3) supplies the zero infinite coordinate. Hence

$$
Q=P_{p,b}\quad\text{for }\nu_p\text{-almost every }Q\in H.
\tag{2.14}
$$

As $\mathbb P_C(\mathsf E,Q_0\notin H)=0$, the immortal $M$-path
measure can start only at the native singleton, by absolute continuity.
It follows that $M^n\mathbf1(Q)\downarrow0$ for almost every
nonnative $Q$ under $\nu_p$. The identity

$$
T^ng(Q)=h(Q)\,M^n(g/h)(Q)
\tag{2.15}
$$

then gives $T^ng(Q)\to0$ at every such input, outside one null set.
At $Q=P_{p,b}$, (2.4) and the known native coordinates give
$T^ng(Q)=c_b$ for every $n$. This proves the pointwise assertion.
For $n\ge3$, the full p boxes give $0\le T^ng\le c_b$.
Dominated convergence proves the mean assertion in (2.2).
$\square$

**Mathematical citation 2.2 (the operator comparison).** The killed
kernel and multiplication by a positive function are standard
Feynman--Kac and Doob-transform constructions. The load-bearing
source-specific step is the simultaneous pair of inequalities
(2.8)--(2.9), obtained from the same completion coordinate and the
upper complete-word box. The path comparison uses that pair to exclude
escape of surviving mass into nonnative stationary configurations.
It does not invoke finite Perron vectors, primitivity, a spectral gap,
Feller regularity or a minorization condition.

## 3. Eventual endpoint recurrence without finite support

**Theorem 3.1 (Borel endpoint-recurrence rigidity).** Let a pair belong
to $\mathfrak C_{\rm box}$. Assume, additionally, that for some finite
integer $N\ge0$ its averaged marker-one sequence satisfies

$$
d_{n+2}-(z_a+z_b)d_{n+1}+z_az_b d_n=0
\qquad(n\ge N).
\tag{3.1}
$$

Then for one $\theta\in[0,1]$ both original marginals and both original
flows are

$$
\begin{aligned}
\nu_p&=(1-\theta)\delta_{P_{p,a}}+\theta\delta_{P_{p,b}},\\
\nu_\beta&=(1-\theta)\delta_{P_{\beta,a}}+\theta\delta_{P_{\beta,b}},\\
\Gamma_B&=(1-\theta)\delta_{(P_{p,a},P_{\beta,a})}
             +\theta\delta_{(P_{p,b},P_{\beta,b})},\\
\Gamma_A&=(1-\theta)\delta_{(P_{\beta,a},P_{p,a})}
             +\theta\delta_{(P_{\beta,b},P_{p,b})}.
\end{aligned}
\tag{3.2}
$$

There is no atomicity assumption at either phase. The coefficients of
the eventual recurrence determine every earlier word and both entire
flows. The exact recurrence (3.1) remains an added condition.

**Proof.** Because $z_a\ne z_b$, solving the scalar recurrence gives
real constants $A_0,B_0$ such that

$$
d_n=A_0z_a^n+B_0z_b^n\qquad(n\ge N).
\tag{3.3}
$$

Theorem 2.1 identifies $B_0=c_bm_b$.

We use the native-isolation argument of [PAIR, (19.11)--(19.13)].
That part of its proof uses only (1.5)--(1.7), not the zero-risk
budgets or the midpoint means. On a positive p native singleton,
the B conditional barycentre is its suspended native law. Each of
that law's complete coordinates is an endpoint of its box, so the
conditional suspended law must equal that endpoint at every coordinate.
Countability of the complete carrier gives equality of the entire
laws simultaneously. Repeating at A gives equal native masses in the
two phases and no incoming or outgoing nonnative mass.
In particular, the two native b unit flows occur with exactly mass
$m_b$, and can be subtracted from the original flows.

If $m_b=1$, their mass already exhausts the pair, giving (3.2).
Otherwise subtract these two subflows and normalize by $1-m_b$.
This preserves compatibility and both full boxes. No assertion of
preserving the midpoint means or the loss budgets is needed here.
Call the resulting pair the remainder. Its own averaged sequence is

$$
\widetilde d_n=\frac{A_0}{1-m_b}z_a^n
\qquad(n\ge N).
\tag{3.4}
$$

Apply the definitions $C,L,g$ of (2.3) to this one remainder.
Its p lower box at $w_{3,1}$ and its regular emissions give

$$
L^3g\ge c_az_a^3,\qquad g\le c_a,\qquad
\Delta:=L^3g-z_a^3g\ge z_a^3(c_a-g)\ge0.
\tag{3.5}
$$

For any integer $n\ge N$, (3.4) implies

$$
0=\widetilde d_{n+3}-z_a^3\widetilde d_n
 =\int L^n\Delta\,d\widetilde\nu_p.
\tag{3.6}
$$

Since $L\ge(1/5)C$, positivity gives
$L^n\Delta\ge(1/5)^n C^n\Delta$. The original unweighted
stationarity of this remainder therefore yields

$$
0\ge\left(\frac15\right)^n
       \int\Delta\,d\widetilde\nu_p\ge0.
\tag{3.7}
$$

It follows from (3.5) that $g=c_a$ almost surely. Equality in the
upper regular bound
$g=(1-u)B(1-v)\le(1-a)^2$ forces $u=a$ and $v=a$ on B edges.
The common marginals make these assertions hold almost everywhere at
both phases. Iterating the full equations gives exactly the native a
laws on the remainder. All its flows are consequently the native a
unit flows. Restoring the removed b subflows proves (3.2) with
$\theta=m_b$ and also
$A_0=c_a(1-m_b)$. No finite realization or quadrature was used.
$\square$

**Corollary 3.2 (three-depth exclusion on the exact recurrence branch).**
No pair satisfying (3.1) has $\mathcal J=0$ in the unchanged fixed
positive-three-depth problem. If it also has both midpoint means
(1.9), its p loss at the supported depth 3 satisfies

$$
\int\operatorname{TV}(Q,P_{p,3/8})\,d\nu_p
\ge\rho_p+\frac{\delta_3}{2}>\rho_p,\qquad
\delta_3=\frac{344076471}{6553600000000}.
\tag{3.8}
$$

**Proof.** The endpoint p event values are distinct, so (1.9) and
(3.2) force $\theta=1/2$. At $w_{3,1}$ the depth-3 target exceeds
the larger endpoint mass by the supplied complete-word gap
$\delta_3$ [SEVEN, (3.3)--(3.4)]. The coordinate triangle identity
then gives (3.8). A zero-excess pair would supply both boxes and both
means while requiring the contrary depth-3 budget. The suspended
depth-3 condition remains part of the original problem; violation
of the p budget alone is sufficient for this exclusion.
$\square$

**Corollary 3.3 (late endpoint tails fix both event means).** If a
pair in $\mathfrak C_{\rm box}$ has, for all sufficiently large $n$,

$$
d_n=(1-\vartheta)c_az_a^n+\vartheta c_bz_b^n
\quad\text{for some }\vartheta\in[0,1],
\tag{3.9}
$$

then its original flows are (3.2) with $\theta=\vartheta$ and

$$
\int Q(E_p)\,d\nu_p=M_p+(1-2\vartheta)\rho_p,\qquad
\int W(E_\beta)\,d\nu_\beta=M_\beta+(1-2\vartheta)\rho_\beta.
\tag{3.10}
$$

Here $M_p,M_\beta$ are the means in (1.9). In particular arbitrary
Borel support enlargement cannot repair two incorrect midpoint means
while preserving this exact eventual averaged tail.

**Proof.** Equation (3.9) implies (3.1). Theorem 2.1 gives
$m_b=\vartheta$, and Theorem 3.1 identifies the original complete
flows. Their endpoint event values are $M_s+\rho_s$ at a and
$M_s-\rho_s$ at b, which gives (3.10).
$\square$

## 4. A nonatomic boundary-rate counterexample

**Proposition 4.1 (zero native mass with maximal tail growth).** There
is a nonatomic pair in $\mathfrak C_{\rm box}$ with $m_b=0$ for which

$$
\lim_{n\to\infty}d_n^{1/n}=z_b,\qquad
\frac{d_n}{z_b^n}\sim
 \frac{c_bz_b}{z_b-x_0}\frac1n,\qquad x_0=\frac{239}{1000}.
\tag{4.1}
$$

Its averaged sequence violates (3.1) at every index. Thus the
$o(z_b^n)$ conclusion of Theorem 2.1 cannot be replaced by an
exponential bound $O(r^n)$ with any $r<z_b$, even for one fixed
boxed pair. This pair is not a common zero-excess witness.

**Proof.** Use the singleton complete-law parametrization
[REV, (11.22)] as a supplied construction, with

$$
q=c_bz_b^3=\frac{1944}{390625},\qquad
x\in[x_0,z_b],\qquad
g_x=\frac q{x^3},\quad
u_x=1-g_x-x,\quad
v_x=\frac x{g_x+x}.
\tag{4.2}
$$

The two singleton acquired kernels are identity kernels. Their own laws
are

$$
Q_x(w_{n,0})=u_xx^n,\qquad
Q_x(w_{n,1})=g_xx^n,\qquad
W_x=(1-v_x)\delta_\beta+v_x\alpha Q_x.
\tag{4.3}
$$

Indeed $(1-u_x)v_x=x$ and $(1-u_x)(1-v_x)=g_x$.
Also $u_x+g_x=1-x$, so the completed masses sum to one,
and the infinite coordinates are zero.

Here is an all-coordinate check of both boxes on the entire interval.
One has

$$
c_b\le g_x<\frac{73}{200},\qquad
u'_x=\frac{3q}{x^4}-1>0,\qquad
v_x=\frac{x^4}{q+x^4}\ \text{is strictly increasing}.
\tag{4.4}
$$

For the first upper bound it suffices to check
$q/x_0^3=4976640/13651919<73/200$.
Thus
$u_x\ge1-73/200-z_b=79/200>a$ and
$v_x\ge x_0/(73/200+z_b)=239/605>a$.
Their maxima are $u_{z_b}=v_{z_b}=b$.
The derivative bound follows from
$3q/x^4\ge3c_b/z_b>1$.
In particular all emissions are regular.

The marker-zero p and suspended masses lie in their endpoint intervals
for every $n$, since $u_x,v_x\in[a,b]$ and $x\in[z_a,z_b]$.
For p marker one at $n=0,1,2$, the functions
$g_xx^n=q/x^{3-n}$ have lower endpoint $c_bz_b^n$ and satisfy

$$
g_xx^n\le\frac{73}{200}z_b^n<c_az_a^n
\qquad(n=0,1,2),
\tag{4.5}
$$

where each of the three final inequalities is a rational comparison.
At $n=3$ their common value is $q$, the upper endpoint.
From index 3 onward the p endpoint ordering is fixed, and the next
actual mass multiplies by $x\in[z_a,z_b]$. Induction proves all
remaining p marker-one boxes.

At suspension put
$m(x)=v_xg_x=qx/(q+x^4)$. It is decreasing on the interval because
$q<3x_0^4$, whereas $xm(x)$ is increasing because $q>z_b^4$:

$$
m'(x)=\frac{q(q-3x^4)}{(q+x^4)^2}<0,\qquad
(xm(x))'=\frac{2qx(q-x^4)}{(q+x^4)^2}>0.
\tag{4.6}
$$

Consequently

$$
bc_b\le m(x)\le b\frac{73}{200}=\frac{73}{500}<ac_a,
\qquad
ac_az_a<bc_bx_0\le xm(x)\le bc_bz_b.
\tag{4.7}
$$

These are the suspended marker-one boxes at indices 0 and 1.
Their endpoint ordering is fixed from index 1 onward; multiplication
by $x\in[z_a,z_b]$ proves all later boxes. The beta coordinate is
boxed by $v_x\in[a,b]$. The complete tails are $x^j$ and $v_xx^j$,
so (1.3) holds, with infinity still included. This proves all boxes,
without substituting a finite-prefix problem.

Choose $x$ with normalized Lebesgue law on $[x_0,z_b)$.
Push it forward to $(Q_x,W_x)$ for $\Gamma_B$ and to $(W_x,Q_x)$
for $\Gamma_A$. Each constituent is a compatible singleton pair,
so both common margins and both full conditional equations hold.
There is no resampling of $x$ at successive returns in these
analysis flows. Coordinate continuity and the uniform geometric tail
bound give TV continuity of both descriptor maps.
Strict increase of $u_x$ and $v_x$ makes both maps injective.
Their pushforward marginals are therefore nonatomic. As $x<z_b$
almost surely, neither native b singleton has positive mass.

For $n\ge3$, exact integration yields

$$
d_n=\frac{q}{z_b-x_0}
       \frac{z_b^{n-2}-x_0^{n-2}}{n-2},
\qquad
\frac{d_n}{z_b^n}
=\frac{q}{(z_b-x_0)z_b^2}
  \frac{1-(x_0/z_b)^{n-2}}{n-2}.
\tag{4.8}
$$

This proves both limits in (4.1). The recurrence residual is

$$
d_{n+2}-(z_a+z_b)d_{n+1}+z_az_bd_n
=\frac1{z_b-x_0}\int_{x_0}^{z_b}
        g_xx^n(x-z_a)(x-z_b)\,dx<0
\tag{4.9}
$$

for every $n\ge0$. The integrand is strictly negative in the
interior. Thus an endpoint spectral growth rate is insufficient
for the exact recurrence conclusion.

The pair is a residual-graph pair, with no native endpoint laws
almost surely. Its p event mean satisfies the explicit bound

$$
\int Q(E_p)\,d\nu_p
\le\frac{73}{200}(1+z_b+z_b^2)
<\frac{11758471}{22781250}=M_p.
\tag{4.10}
$$

Thus it fails the original p midpoint equation. It is not a
zero-excess pair, and it supplies no finite COMPLETE realization
of its nonatomic marginals.
$\square$

**Proposition 4.2 (the atom-missing predicate is not closed on the
boxed class).** Within $\mathfrak C_{\rm box}$ the condition $m_b=0$
is not weakly closed. This statement does not assert nonclosedness
after an additional restriction to $\mathcal J=0$.

**Proof.** In (4.2)--(4.3) let $x$ increase to $z_b$ through values
strictly below it, and use the corresponding unit singleton flows.
Each has $m_b=0$. Their descriptors converge in TV to
$P_{p,b},P_{\beta,b}$, by coordinate convergence and the same uniform
geometric tail control. Hence both flows converge weakly to the
native b unit flows, which have $m_b=1$. Every member satisfies
both full boxes, as proved above. No member was asserted to
satisfy the zero-excess budgets or the midpoint means.
$\square$

## 5. Source correspondence and the remaining decision

**Mathematical citation 5.1 (repository suppliers and the new
implication).** All repository references below use the immutable
snapshot
$\mathtt{f022384d6e4a8b9e457f646f377ac2f0398b0c6f}$.

| Source | Exact role and boundary |
| --- | --- |
| [PAIR], Section 11 | Supplies the compact descriptor spaces, full-descriptor residual equations, common unweighted flows, zero-face geometry, regeneration and atomicity criteria. No new compactness or quadrature theorem is asserted here. |
| [PAIR], Section 18 | Proves eventual endpoint-tail rigidity under finite p support. Its finite Perron argument does not supply Theorem 2.1 for arbitrary Borel marginals. Theorem 3.1 removes that support condition while retaining the exact eventual recurrence. |
| [PAIR], Section 19 | Supplies native singleton isolation and equal native masses between the two phases. Its zero-face equal-a-and-b excision preserves midpoints and budgets. The proof of Theorem 3.1 removes only b to analyze a remainder and makes no midpoint-preservation claim for that operation. |
| [SEVEN], entire volume | Supplies $V=0$ rigidity, the strict enlargement beyond full residual graphs, and $J=0\Rightarrow V>0$. Theorem 2.1 allows positive $V$ and uses no pathwise replacement of a residual mean by a sampled successor. |
| [REV], Section 11.6 and Section 16 | Supplies singleton formulas and the deterministic complete-successor chord theorem. The singleton formulas are used only in the boundary counterexample. The Borel tail theorem imposes no deterministic-successor premise. |
| [SURVIVAL], Section 3 | Supplies the stationary acquired descriptor path and its weighted word recursion. Those identities are reused in operator notation in (2.3)--(2.4). Its signed finite-window charges and free return-weight dispersion are not set to zero here. |
| [RETURN], Section 15 | Gives the minimum returned suspended-cut count for a prescribed finite admissible triple, subject to its full incoming-pair equations and exact-service conditions. No prescribed triple, cut-count optimum or sampler theorem is inferred from the Borel tail classification. |
| [PAID], Definitions 1.1--2.1 and Lemma 2.1.1 | Supplies the source/control contract, all-history meaning, and original product realization of a supplied finite table. Analysis kernels in Theorem 2.1 are not installed as observer registers. |

The source-relative mathematical addition is (2.2), its proof by
the source-specific killing/distortion comparison (2.8)--(2.9), and
the consequent Borel classification (3.2). The finite residual
identity (3.5)--(3.7) completes the lower-endpoint step after the
upper native atom is identified. Proposition 4.1 exhibits the
boundary-rate behavior that prevents a direct transfer of the
finite Perron maximum argument to arbitrary marginals.
These are repo-derived statements; no global priority claim is made.

**Mathematical citation 5.2 (bounded primary comparison).** The
following primary results delimit the mature tools used in the
argument.

| Primary source | Correspondence |
| --- | --- |
| Ferré, Rousset and Stoltz, *More on the long time stability of Feynman--Kac semigroups*, [arXiv:1807.00390v3](https://arxiv.org/html/1807.00390v3), Section 2, Assumptions 1--3 and Lemma 2 | Positive kernels and multiplication by a positive function are the mature operator frame. Their spectral conclusion uses Lyapunov, minorization/irreducibility and local regularity hypotheses. Those hypotheses are not supplied for the arbitrary disintegrations here, and their spectral theorem is not invoked. Formula (2.6) constructs the needed bounded superharmonic function directly. |
| Li and Schneider, *Applications of Perron--Frobenius Theory to Population Dynamics*, [arXiv:math/0109008v1](https://arxiv.org/html/math/0109008v1), Theorems 2.1 and 2.3 | Positive left and right Perron vectors apply to finite irreducible matrices; normalized-power convergence in Theorem 2.3 requires primitivity. These are suppliers for finite-matrix comparisons, not a theorem about the arbitrary Borel kernel used here. Proposition 4.1 has upper boundary growth without a native boundary atom. |
| Leskelä and Vihola, *Conditional convex orders and measurable martingale couplings*, [arXiv:1404.0999v3](https://arxiv.org/html/1404.0999v3), Theorems 1.2--1.4 | Bounded finite-coordinate projections satisfy their first-moment requirement. Conditional barycentric couplings do not turn each successor into its barycentre or supply a stationary law for a synthetically weighted kernel. The proof retains both original full-descriptor equations and constructs its killed analysis kernel explicitly. |

The Markov path construction, conditioning, positive-kernel iteration,
bounded convergence and the monotone class theorem are standard
measure-theoretic tools. Their uses are proved at the points where the
source-specific conclusion depends on them. No new general martingale
coupling, ergodic theorem or Doob-transform theorem is claimed.

**Definition 5.3 (remaining original obligation).** The original
decision is still $j_c=0$ versus $j_c>0$ on all of $\mathfrak C$,
with both full boxes, both midpoint means, both supported depth-3
configuration bounds and both full residual equations on the same
phase marginals. Theorems 2.1 and 3.1 show that any zero pair must
have an averaged marker-one tail which fails (3.1) at arbitrarily
large indices. They neither construct such a pair nor exclude it.

PAIR19 permits an equal-native-endpoint excision from a zero pair;
one or both native masses can already be absent. Theorem 2.1 applies
whether those masses vanish or not. In the b-atom-missing case it
gives only $d_n=o(z_b^n)$, and Proposition 4.1 explains why no
smaller uniform exponential rate follows. That proposition belongs
to the boxed class, not the zero face. No weak-closed or compact
atom-missing zero-domain replacement is inferred.

Finite abstract atomicity, exact represented sampling and the
entire charged COMPLETE carrier remain distinct requirements.
If a pair is classified by Theorem 3.1, its abstract laws have at
most two atoms, but an arbitrary real mixture weight still needs
an allowed finite exact sampler for represented attainment.
For the fixed positive-three-depth prior the classified pair
cannot attain zero excess by Corollary 3.2.
The nonatomic construction of Proposition 4.1 is an analysis pair;
it is not itself a finite observer.

The kernel $L$, the killed kernel $M$, its cemetery state and its
path-measure comparison add no actual operation to the source.
No clipping property is used or asserted. No hard resource or
defect budget is preserved by an unproved bridge. There is no
unrestricted positive gap, full-code-whitebox impossibility,
universal ML classification, practical performance improvement
or fixed-resource optimum in these conclusions.

[PAIR]: https://github.com/the-omega-institute/trureturing/blob/f022384d6e4a8b9e457f646f377ac2f0398b0c6f/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PAIRED_CALIBRATION_OBSERVABILITY.md
[SEVEN]: https://github.com/the-omega-institute/trureturing/blob/f022384d6e4a8b9e457f646f377ac2f0398b0c6f/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FINITE_WORD_BRANCHING_NECESSITY.md
[REV]: https://github.com/the-omega-institute/trureturing/blob/f022384d6e4a8b9e457f646f377ac2f0398b0c6f/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_REVERSIBLE_COMMON_GENERATOR_CONSTRAINTS.md
[SURVIVAL]: https://github.com/the-omega-institute/trureturing/blob/f022384d6e4a8b9e457f646f377ac2f0398b0c6f/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RETURN_SURVIVAL_DISPERSION.md
[RETURN]: https://github.com/the-omega-institute/trureturing/blob/f022384d6e4a8b9e457f646f377ac2f0398b0c6f/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RETURN_P_EMISSION_VARIATION.md
[PAID]: https://github.com/the-omega-institute/trureturing/blob/f022384d6e4a8b9e457f646f377ac2f0398b0c6f/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md

## 追加锚（本行以下为增补区）

## 6. Uniform stability in the normalized word-return coordinate

**Assumption 6.1 (the full boxed Borel domain).** In Sections 6--8 use
exactly [LATE, Definitions 1.2--1.3 and Assumption 1.1][LATE15403]. Thus
$a=1/3$, $b=2/5$, $z_r=r(1-r)$, $c_r=(1-r)^2$, and $\lambda=4/15$.
The complete carriers, native laws, regular TV spaces, and endpoint
coordinate boxes are (1.2)--(1.7) above. Both infinite outcomes remain
in their carriers. The phase marginals have arbitrary Borel support.
The two disintegrations satisfy the entire-measure equations

$$
\begin{aligned}
Q&=u(Q)\delta_\alpha+(1-u(Q))\beta\!\int W\,B(Q,dW),\\
W&=(1-v(W))\delta_\beta+v(W)\alpha\!\int Q'\,A(W,dQ'),\\
\nu_pB&=\nu_\beta,\qquad \nu_\beta A=\nu_p.
\end{aligned}
\tag{6.1}
$$

Conditioning is on the whole input descriptor. The last line uses the
original unweighted marginals; no continuation or survival factor is
inserted into either marginal.

The prior $\mu$ is any fixed finite or countable probability distribution
with $\mu(1),\mu(2)>0$. One $K$ is drawn before the first paid Read;
conditional on that same $K=k$, letters have alpha probability
$r_k=F_{k+1}/F_{k+3}$. Every supported $k$ remains a target. This includes
the three-depth source of Section 1 as its corresponding special case.
The source parameters remain $(m,d,\ell,n)=(2,1,2,4)$; a subscript $n$
below counts word returns and does not change a source parameter.
Both accepted seeds, all positive finite paid rejections, partial parses
and returns, marker triples, bare and held records, selectors, write
and latch flags, permissions, third write before its latch, fourth
completion, delivery and matching Stop retain their original meaning.
Terminal states permit no Read. Initialization is source-independent;
acquired and synthetic letters use identical updates. The complete-record
renderer of [PAIR, Section 2][PAIR-STABILITY] retains future letters,
operation blocks and noncompletion, and preserves TV. COMPLETE charges
the original control, installed program and numbers, selectors, addresses,
labels, output cursors, sampler states, workspace and persistent randomness.
The descriptors and operators in (6.1) are analytical coordinates, not
additional observer ports, resets or newly sampled depths.

**Definition 6.2 (normalized slack and the constant).** Retain the
notation of [LATE, Theorem 6.1][LATE15403]:

$$
\begin{aligned}
d_n&=\int Q(w_{n,1})\,d\nu_p(Q),\\
e_{a,n}&=d_n-c_az_a^n,&e_{b,n}&=c_bz_b^n-d_n,\\
E_r&=\max_{s\in\{p,\beta\}}
       \int\operatorname{TV}(D,P_{s,r})\,d\nu_s(D),\\
\kappa&=\frac15,&
M_r&=1+z_r+z_r^2+(1+z_r)\lambda+\lambda^2,\\
H_r&=M_rc_r\kappa^{-3}z_r^3
                  \sum_{j=0}^2(\lambda/z_r)^j.
\end{aligned}
\tag{6.2}
$$

Here TV is half the complete-carrier $\ell^1$ distance, evaluated at each
configuration before integration. In particular $E_r$ is neither TV
between descriptor distributions nor a loss obtained by replacing each
configuration law by the phase barycentre.

**Theorem 6.3 (uniform normalized complete-configuration stability).**
For every pair satisfying Assumption 6.1, both $r\in\{a,b\}$ and every
integer $n\ge4$, one has

$$
E_r\le H_r\frac{e_{r,n}}{c_rz_r^n},\qquad
H_a=\frac{9839648}{2657205},\qquad
H_b=\frac{20723912}{5859375}.
\tag{6.3}
$$

The same constants apply to every such pair and every word-return index.
No finite-support, recurrence, deterministic-successor, reversibility,
mixing or additional observation hypothesis is imposed.

**Proof.** Marginal transport in (6.1) gives
$\int B|f|\,d\nu_p=\int|f|\,d\nu_\beta$ and
$\int A|h|\,d\nu_\beta=\int|h|\,d\nu_p$ for bounded Borel functions.
A null set at either phase therefore has zero conditional mass from
almost every input at the other phase. The kernels and their bounded
positive weighted compositions act on functions modulo the respective
marginal null sets. Coordinate equations and boxes hold simultaneously
there because the complete carriers are countable; a countable union
also accommodates every iterate below. Thus no conditional version at
a null input affects an identity or inequality. The regular tail bounds
force both infinite masses to zero by continuity from above, without
removing those coordinates or conditioning on completion.

Use the full-word recursion of [LATE, (6.4)--(6.5)][LATE15403], on
these same quotients:

$$
\begin{gathered}
P=BA,\qquad Lf=(1-u)B(vAf),\qquad
 g=(1-u)B(1-v),\qquad w=L\mathbf1=1-u-g,\\
q_j(Q):=Q(w_{j,1})=L^jg(Q),\qquad
c_b\le g\le c_a,\qquad \nu_pP=\nu_p,\\
\kappa Pf\le Lf\le\lambda Pf\quad(f\ge0),\qquad
\kappa^j\!\int f\,d\nu_p
 \le\int L^jf\,d\nu_p
 \le\lambda^j\!\int f\,d\nu_p\quad(f\ge0).
\end{gathered}
\tag{6.4}
$$

The last comparison follows by positive-kernel iteration and
$\nu_pP^j=\nu_p$, not by stationarity of $L$. Neither commutation of
$P,L$ nor an invariant probability for $L$ is required.

Fix $r,n$, and abbreviate $c=c_r,z=z_r$. Put $\sigma=1$ for $r=a$
and $\sigma=-1$ for $r=b$, and define

$$
F=\sigma(c-g),\quad \Phi=\int F\,d\nu_p,\quad
h_j=\sigma(q_j-cz^j),\quad V=\sigma(w-z).
\tag{6.5}
$$

Here $F\ge0$. The ratio of the two native marker-one masses is
$(81/100)(27/25)^j$, which exceeds one for $j\ge3$. The complete
boxes therefore give $h_j\ge0$ for $j\ge3$ and
$\int h_n\,d\nu_p=e_{r,n}$. In particular, the predecessor at
$n-1\ge3$ and positivity of $L$ imply

$$
0\le Lh_{n-1}
 =h_n-cz^{n-1}V,\qquad
 V\le\frac{h_n}{cz^{n-1}}.
\tag{6.6}
$$

This is an order bound on a possibly signed $V$; it asserts no
nonnegativity of $V$.

Use a block of exactly three returns, independently of $n$. Finite
telescoping gives
$L^3\mathbf1-z^3\mathbf1=\sum_{j=0}^2z^{2-j}L^j(w-z)$.
Since $q_3=L^3g$, it follows that

$$
\begin{aligned}
L^3F
 &=c\sum_{j=0}^2z^{2-j}L^jV-h_3\\
 &\le c\sum_{j=0}^2z^{2-j}L^jV\\
 &\le z^{3-n}\sum_{j=0}^2z^{-j}L^jh_n.
\end{aligned}
\tag{6.7}
$$

The first inequality uses the actual index-three box $h_3\ge0$;
the second applies the positive operators $L^j$ to (6.6).
Apply (6.4) to the nonnegative $F$ and $h_n$ and integrate:

$$
\kappa^3\Phi\le\int L^3F\,d\nu_p
 \le z^{3-n}\sum_{j=0}^2(\lambda/z)^j e_{r,n}.
\tag{6.8}
$$

Only three powers of the lower comparison constant occur. This yields
an estimate uniform in $n$ after division by the native word mass.

To pass from $\Phi$ to the two entire configuration losses, reuse the
complete-TV conversion of [LATE, (6.10)--(6.15)][LATE15403]. Its exact
hypotheses are present here: normalization, both full boxes, both full
residuals and the same unweighted marginal transport. More explicitly,
the endpoint-a-positive events on the entire carriers are

$$
E_p=\{w_{0,1},w_{1,1},w_{2,1}\},\qquad
E_\beta=\{\beta,\alpha w_{0,1}\}.
\tag{6.9}
$$

Every other finite coordinate has the opposite endpoint ordering, and
the infinite coordinates have zero difference. Inside the boxes, the
signs of every coordinate difference from either endpoint are fixed.
Normalization identifies complete TV with the corresponding signed
event difference; (6.9) is not a truncation of the laws.

For clarity, the conversion uses $x=|u-r|$, $y=|v-r|$ and the identities

$$
F=(1-r)x+(1-u)By=(1-r)By+B(1-v)x,
\qquad F\ge(1-r)x,\quad F\ge(1-r)By.
\tag{6.10}
$$

Writing $f_j=\sigma(cz^j-q_j)$ for $j=0,1,2$, its p identities are
$\operatorname{TV}(Q,P_{p,r})=f_0+f_1+f_2$ and
$f_{j+1}=Lf_j+cz^j(x-F)$ for $j=0,1$. As
$c(x-F)\le zF$, these give the supplied pointwise bound

$$
\operatorname{TV}(Q,P_{p,r})
 \le(1+z+z^2)F+(1+z)LF+L^2F.
\tag{6.11}
$$

At suspension the exact conversion is
$\operatorname{TV}(W,P_{\beta,r})=(1-c)y+vAF$.
Consequently (6.4), (6.10) and both marginal transports give

$$
\begin{aligned}
\int\operatorname{TV}(Q,P_{p,r})\,d\nu_p&\le M_r\Phi,\\
\int\operatorname{TV}(W,P_{\beta,r})\,d\nu_\beta
 &\le\left(\frac{1-c}{1-r}+b\right)\Phi\le M_r\Phi.
\end{aligned}
\tag{6.12}
$$

The middle suspended coefficient is $37/30$ for a and $22/15$ for b;
its differences from $M_a,M_b$ are respectively $1763/4050$ and
$1309/5625$. All TV expressions have thus been evaluated on complete
configuration laws before taking expectations. Combining (6.8) and
(6.12) gives exactly (6.3).

Finally $M_a=3379/2025$, $M_b=9559/5625$, and the two three-term sums
in (6.2) are $91/25$ and $271/81$. Thus the rational values in (6.3)
follow from

$$
\begin{aligned}
H_a&=\frac{3379}{2025}\frac49\,125
           \left(\frac29\right)^3\frac{91}{25}
       =\frac{9839648}{2657205},\\
H_b&=\frac{9559}{5625}\frac9{25}\,125
           \left(\frac6{25}\right)^3\frac{271}{81}
       =\frac{20723912}{5859375}.
\end{aligned}
\tag{6.13}
$$

The proof treats both signs and all $n\ge4$ on one original pair.
$\square$

## 7. The all-supported-depth consumer and necessary lower-tail repairs

**Definition 7.1 (the original risk and the separate midpoint condition).**
For the source of Assumption 6.1 use exactly
[PAIR, (11.9)][PAIR-STABILITY]:

$$
\mathcal J=\max_{s\in\{p,\beta\}}
 \left\{\sup_{k:\mu(k)>0}
       \int\operatorname{TV}(D,P_{s,r_k})\,d\nu_s(D)-\rho_s\right\},
\qquad
\rho_p=\frac{1116529}{22781250},\quad
\rho_\beta=\frac{239}{6750}.
\tag{7.1}
$$

A compatible zero-excess pair means $\mathcal J=0$, with every supported
target still present. Separately, a boxed p-midpoint pair means a pair
satisfying Assumption 6.1 and

$$
\int Q(E_p)\,d\nu_p=C_p,\qquad
C_p=\frac{11758471}{22781250}.
\tag{7.2}
$$

This second condition asserts neither the suspended midpoint nor the
supported-target loss budgets.

**Corollary 7.2 (a uniform necessary normalized correction).** For every
boxed compatible pair of Assumption 6.1, both endpoints and all $n\ge4$,

$$
\mathcal J+H_r\frac{e_{r,n}}{c_rz_r^n}\ge\rho_p.
\tag{7.3}
$$

Every compatible pair with $\mathcal J=0$, and separately every boxed
p-midpoint pair, therefore satisfies simultaneously

$$
\frac{e_{r,n}}{c_rz_r^n}\ge\frac{\rho_p}{H_r}>0
\quad(r=a,b,\ n\ge4).
\tag{7.4}
$$

Equivalently, on either of those two classes,

$$
c_az_a^n\left(1+\frac{\rho_p}{H_a}\right)
 \le d_n\le
c_bz_b^n\left(1-\frac{\rho_p}{H_b}\right)
\quad(n\ge4).
\tag{7.5}
$$

**Proof.** The complete endpoint distance at p is $2\rho_p$; its
endpoint-positive event is (6.9), with endpoint values $C_p+\rho_p$
and $C_p-\rho_p$. Given $r$, the opposite endpoint $r^{\rm opp}$ is
an original supported target since $\mu(1),\mu(2)>0$. The triangle
inequality on each complete configuration law gives

$$
\begin{aligned}
\mathcal J
 &\ge\int\operatorname{TV}(Q,P_{p,r^{\rm opp}})\,d\nu_p-\rho_p\\
 &\ge\rho_p-\int\operatorname{TV}(Q,P_{p,r})\,d\nu_p\\
 &\ge\rho_p-E_r.
\end{aligned}
\tag{7.6}
$$

Apply Theorem 6.3. Taking one supported target as a lower bound in
(7.6) does not remove any other target from (7.1).

For a compatible pair with $\mathcal J=0$, the full boxes need not be
assumed separately. At each phase both endpoint losses are at most
$\rho_s$ and their sum is at least
$\operatorname{TV}(P_{s,a},P_{s,b})=2\rho_s$. Thus both equal
$\rho_s$. Equality in the integrated coordinate triangle inequality
forces its nonnegative slack to vanish almost surely at each complete
atom. Countability gives the full boxes simultaneously; their signed
event formula also gives both midpoint means. This is the exact
zero-face implication of [PAIR, (11.29)--(11.30)][PAIR-STABILITY].
Hence (7.3) applies to that same pair and proves (7.4).

Under the separate boxed p-midpoint assumption, the complete-TV event
formula directly gives

$$
\int\operatorname{TV}(Q,P_{p,a})\,d\nu_p
 =C_p+\rho_p-C_p=\rho_p,
\qquad
\int\operatorname{TV}(Q,P_{p,b})\,d\nu_p
 =C_p-(C_p-\rho_p)=\rho_p.
\tag{7.7}
$$

Thus $E_r\ge\rho_p$ for both endpoints, and Theorem 6.3 again gives
(7.4). Substitution of the two definitions of slack gives (7.5).
$\square$

**Corollary 7.3 (no subnative-order NULL155 lower-tail repair).** The two
p descriptors in [NULL155, Definition 2.1][NULL-STABILITY] have the same
marker-one masses $c_az_a^n$ for every $n\ge5$. Let a proposed repair
supply a single compatible pair in the original domain, satisfying
either $\mathcal J=0$ or the separate boxed p-midpoint condition of
Definition 7.1. If its corrected mean is
$d_n=c_az_a^n+\Delta_n$ for $n\ge5$, then

$$
\Delta_n\ge\frac{c_a\rho_p}{H_a}z_a^n>0
\qquad(n\ge5).
\tag{7.8}
$$

In particular $\Delta_n=o(z_a^n)$ is impossible, even if that
asymptotic condition is required only along an unbounded subsequence.
The conclusion allows arbitrary changes to support, mixture weights,
earlier coordinates and conditional branching, subject to the same
complete compatibility and face hypotheses.

**Proof.** Every probability mixture of those two specified p laws has
the displayed original tail means. For any repaired pair with the stated
hypotheses, $\Delta_n=e_{a,n}$, and (7.4) gives (7.8). If
$n_j\to\infty$, then every $n_j\ge5$ obeys
$\Delta_{n_j}/z_a^{n_j}\ge c_a\rho_p/H_a>0$, which contradicts
convergence of that ratio to zero. The same bound also applies termwise
to a family of proposed repairs, each satisfying the stated hypotheses,
when the return indices tend to infinity across the family.

The NULL155 measures themselves fail common full marginals and omitted
complete residual equations [NULL155, Proposition 5.1][NULL-STABILITY].
They are not inputs to Theorem 6.3. The conclusion constrains their
proposed compatible repairs, not merely their retained feature moments.
Meeting (7.8) alone supplies none of the remaining compatibility or
loss conditions. $\square$

## 8. Supplier correspondence and unresolved realization

**Mathematical citation 8.1 (source-specific inference and mature tools).**
[LATE, Sections 6--9][LATE15403] is used at the exact source revision
$\mathtt{e0b3be330ba79b298ea9e02d67ff3ddea04b75a3}$.
Its positive-kernel comparison, two complete-TV conversions and original
risk consumer supply (6.4), (6.10)--(6.12) and the triangle argument.
Its coefficient $C_{r,n}$ is finite at each fixed index. The additional
source-specific implication here is (6.7)--(6.8): the index-three box
and a late predecessor box control $L^3F$, regardless of the distance
to that predecessor. This gives the constants $H_r$ independent of the
word-return index, and the simultaneous necessary bound (7.4).
Neither an eventual recurrence nor positive mass at a native descriptor
is assumed. This is a repo-derived ordinary mathematical
deduction relative to the cited suppliers, without a global originality
or optimal-constant claim.

Positive-kernel order, integration against an invariant probability,
finite telescoping and the complete-measure triangle inequality are
mature intermediate tools. Ferré, Rousset and Stoltz, *More on the long
time stability of Feynman--Kac semigroups*,
[Section 2, Assumptions 1--3 and Lemma 2](https://arxiv.org/html/1807.00390v3),
study positive kernels with Lyapunov, minorization/irreducibility and
local regularity hypotheses for their spectral conclusions. None of
those extra hypotheses is supplied here; (6.8) instead uses the given
stationary unweighted probability for $P$ and three positive comparisons.
Li and Schneider, *Applications of Perron--Frobenius Theory to Population
Dynamics*, [Theorems 2.1(a) and 2.3](https://arxiv.org/html/math/0109008v1),
require a finite irreducible matrix for their positive Perron vectors
and primitivity for normalized-power convergence. Neither conclusion
is used to replace the arbitrary Borel kernels. Leskelä and Vihola,
*Conditional convex orders and measurable martingale couplings*,
[Theorems 1.2(i) and 1.3(i)](https://arxiv.org/html/1404.0999v3),
supply finite-first-moment vector and measurable-kernel coupling results.
Bounded word projections meet that integrability premise, but do not
by themselves supply two compatible full-law flows or this stability
estimate. [PAIR, Theorem 20.2][PAIR-STABILITY] retains the entire
prescribed marginals in its compatibility criterion; they are not
replaced here by separately chosen finite projections.

**Mathematical citation 8.2 (distinct suppliers and boundary controls).**
The all-source [cut-partition classification][CUT-STABILITY] concerns
finite prefix-free cuts: factorization between realized images of the
entire literal row maps is equivalent to a common suffix decomposition.
Its source-free decoder and absent-cut and empty/root clauses concern
those original tree rows. They supply neither the stochastic residual
identities (6.1) nor the unweighted law comparison (6.8).
The [arbitrary-family lexicographic supplier, Theorem 41.2][LEX-STABILITY]
assumes linear forms on one finite-dimensional real input space and
finite feasibility. Its polynomial witnesses have constraintwise
thresholds. No such full-law parameterization with both residuals,
common marginals and every supported budget is established here, and
those constraintwise thresholds supply no simultaneous complete-law
application or replacement for (6.8).

The native endpoint flows, half-native mixture and index-three nonnative
contact remain the supplied controls of [LATE, Section 8][LATE15403].
At a native r flow, both sides of (6.3) vanish. The half-native mixture
retains its own two-endpoint zero-excess scope and its supported
nonendpoint obstruction; its midpoint conditions alone do not imply
all other supported budgets. The nonnative upper contact has
$e_{b,3}=0$ and positive complete TV, so a universal finite-coefficient
extension to $n=3$ remains false. These are supplier consistency
conditions, not substitutes for the proof over arbitrary Borel supports.

**Definition 8.3 (remaining feasibility and operational bridges).** The
simultaneous feasibility problem still asks for one pair with both full
residual equations, the common unweighted marginals, both complete boxes,
both midpoint means and every supported configuration-loss budget.
Theorem 6.3 and Corollaries 7.2--7.3 are necessary constraints; they
construct no such pair and determine no general value of $j_c$.
Uniformity in (7.4) is in the normalized word-return coordinate.
The absolute lower correction in (7.8) tends to zero with $n$; no
uniform absolute correction, uniform source-depth risk gap or general
positive value of $j_c$ is asserted.

The operational bridge additionally requires an admissible finite
representation, allowed exact samplers, source-independent installation,
actual paid acquisition and execution with identical acquired/synthetic
updates, matching Stop and all COMPLETE charges. Analytical kernels
and their bounds add no observable register, posterior port, clock,
reset or free randomness. Neither finite representation, exact sampling,
installation, physical attainment nor any fixed-resource optimum follows
from the necessary normalized estimate. The original common source,
both seeds and every paid history remain part of those obligations.

[LATE15403]: https://github.com/the-omega-institute/trureturing/blob/e0b3be330ba79b298ea9e02d67ff3ddea04b75a3/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_LATE_CONTACT_RIGIDITY.md
[PAIR-STABILITY]: https://github.com/the-omega-institute/trureturing/blob/f5f879b599ff134790bedfb493cac21cd0fe6f53/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PAIRED_CALIBRATION_OBSERVABILITY.md
[NULL-STABILITY]: https://github.com/the-omega-institute/trureturing/blob/f5f879b599ff134790bedfb493cac21cd0fe6f53/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FIXED_FULL_RESIDUAL_NULL.md
[CUT-STABILITY]: https://github.com/the-omega-institute/trureturing/blob/f5f879b599ff134790bedfb493cac21cd0fe6f53/Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionClassification.md
[LEX-STABILITY]: https://github.com/the-omega-institute/trureturing/blob/f5f879b599ff134790bedfb493cac21cd0fe6f53/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md

## 追加锚（本行以下为增补区）
