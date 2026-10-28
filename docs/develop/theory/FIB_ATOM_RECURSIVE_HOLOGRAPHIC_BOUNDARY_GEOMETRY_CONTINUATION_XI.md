# FIB atomic recursive holographic boundary geometry XI: original joint histories and the same-law reflection quotient

## 270. Stationary histories of the original all-occurrence heat chains

**Definition 270.1 (source, clock and fixed observables).** Retain precisely
[IV, Definitions 92.1–92.2 and 98.1](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_IV.md).
Thus $T_0=\alpha$, $T_1=\beta$ and
$T_n=\langle T_{n-1},T_{n-2}\rangle$ for $n\ge2$, with the original
ordered labels and all distinct occurrence addresses. Write

$$
\begin{gathered}
N_n=2F_{n+1}-1,\qquad
\mu_n=N_n^{-1}\sum_{x\in V_{T_n}}\delta_x,\qquad
(L_nu)(x)=\sum_{y\sim x}(u(x)-u(y)),\\
S_n(s)=e^{-N_nsL_n},\qquad s\ge0,\\
\Omega=\{L,R\}^{\mathbb N},\quad
\varphi=(1+\sqrt5)/2,\quad a=\varphi^{-1},\quad b=\varphi^{-2},\\
M([p])=a^{\#_L(p)}b^{\#_R(p)}=\varphi^{-\#_L(p)-2\#_R(p)}.
\end{gathered}
\tag{270.1}
$$

The finite energy is the original sum of squared differences on unit
edges, with no root killing term. In the normalized inner product,
$\langle u,N_nL_nu\rangle_{\mu_n}$ is exactly that energy.
The root, every interior node and every terminal have mass $1/N_n$.
The variable $s$ is the supplied comparison clock. Each $T_n$ is a
separately supplied original source, not a replacement of INITIAL in
one native execution.

Put $\mathscr H=\ell^2(\{L,R\}^+;\mathbb R)$ and
$\mathscr G=L^2(\Omega,M;\mathbb R)$. Use the original path sums
$J_n,J$, covariance operators $\Sigma_n,\Sigma$, vectors $v_n,v$,
and $\mathscr K=(\ker\Sigma)^\perp$ of IV, §§98–99. Use exactly the
free-root form $(\mathcal E,\mathcal D)$, operator $H$ and Markov
semigroup $T(s)=e^{-sH}$ of IV, Theorems 111.2–111.3.
For a nonempty word $p$, let
$\chi_{n,p}(x)=\mathbf1_{\{p\preceq x\}}$ on actual nodes and
$\chi_p=\mathbf1_{[p]}$ on $\Omega$; an absent finite address gives
$\chi_{n,p}=0$. For a pair $u=(c,z)$ with $c\in\mathbb R$ and
finitely supported $z\in\mathscr H$, set

$$
f_{u,n}=c\mathbf1+J_nz=c\mathbf1+\sum_pz_p\chi_{n,p},\qquad
F_u=c\mathbf1+Jz=c\mathbf1+\sum_pz_p\chi_p,
\qquad B_u=|c|+\sum_p|z_p|.
\tag{270.2}
$$

Both fields are bounded in absolute value by $B_u$. The pair specifies
its finite extension, including root value $c$, rather than just its
boundary equivalence class. Write $\mathsf M_f$ for bounded
multiplication by $f$ on the indicated $L^2$ space.

**Theorem 270.2 (exact address products and shallow discrepancies).**
For fixed pairs $u=(c,z)$ and $u'=(d,y)$, define the finite increment
vector $w$ by

$$
w_r=cy_r+dz_r+
 \sum_{\substack{p,q\text{ comparable by prefix}\\
                  \max_{\preceq}(p,q)=r}}z_py_q.
\tag{270.3}
$$

Then, for every $n$, including $n=0,1$,

$$
f_{u,n}f_{u',n}=cd\mathbf1+J_nw,\qquad
F_uF_{u'}=cd\mathbf1+Jw.
\tag{270.4}
$$

If instead $F_u=F_{u'}$ in $L^2(M)$, and both increment supports have
depth at most $h$, the corresponding finite fields agree on every
actual node of depth at least $h$, but may differ on shallower nodes.
With $D_{u,u'}=|c-d|+\sum_p|z_p-y_p|$,

$$
\|f_{u,n}-f_{u',n}\|_{L^2(\mu_n)}
 \le D_{u,u'}\sqrt{\frac{2^h-1}{N_n}}\longrightarrow0.
\tag{270.5}
$$

*Proof.* On each actual finite tree, the intersection of two descendant
sets is empty for incomparable addresses and is the deeper descendant
set otherwise. This is also the intersection rule for boundary
cylinders, including $p=q$. Expanding the product proves (270.3)–(270.4)
without using a partition identity at a finite branching node.
For the second assertion, both boundary functions are constant on
length-$h$ cylinders. Every such cylinder has positive $M$-mass, so
almost-everywhere equality is equality on each of them. The finite
value at depth at least $h$ is the value on its length-$h$ prefix
cylinder. Thus only the at most $2^h-1$ shallower actual nodes can
differ, each with mass $1/N_n$ and discrepancy at most $D_{u,u'}$.
This proves (270.5).

For example, $\chi_L+\chi_R=\mathbf1$ on the boundary, whereas
$\chi_{n,L}+\chi_{n,R}=\mathbf1-\mathbf1_{\{\varnothing\}}$
on every finite source. The discrepancy has norm $N_n^{-1/2}$;
for the two singleton sources its value is the entire constant one.
These are retained actual root values, not an exact finite partition
of the source into its two child cylinders. $\square$

**Theorem 270.3 (uniform transported propagation and multiplication).**
There are isometric embeddings

$$
\iota_n:L^2(\mu_n)\longrightarrow
   \mathscr X:=\mathbb R\oplus\mathscr H,\qquad
\iota:\mathscr G\longrightarrow\mathscr X,
\tag{270.6}
$$

onto $\mathbb R\oplus\mathscr E_n$ and
$\mathscr X_0:=\mathbb R\oplus\mathscr K$, respectively, where
$\mathscr E_n$ is the space of actual edges extended by zero.
They satisfy

$$
\iota_nf_{u,n}=(c+\langle v_n,z\rangle,\Sigma_n^{1/2}z)
 \longrightarrow
\iota F_u=(c+\langle v,z\rangle,\Sigma^{1/2}z).
\tag{270.7}
$$

Extend operators to $\mathscr X$ by the adjoints of these embeddings:

$$
\begin{aligned}
A_n(s)&=\iota_nS_n(s)\iota_n^*,&
 A(s)&=\iota T(s)\iota^*,\\
D_{u,n}&=\iota_n\mathsf M_{f_{u,n}}\iota_n^*,&
 D_u&=\iota\mathsf M_{F_u}\iota^*.
\end{aligned}
\tag{270.8}
$$

For every $x\in\mathscr X_0$,

$$
\sup_{s\ge0}\|A_n(s)x-A(s)x\|\longrightarrow0,
\qquad \|D_{u,n}x-D_ux\|\longrightarrow0.
\tag{270.9}
$$

Both convergences are uniform as $x$ ranges over any compact subset
of $\mathscr X_0$. They also apply to compatible vectors $x_n\to x$
by the common contraction and multiplication bounds.
No operator norm convergence of $A_n(0)$ on all of $\mathscr X$ is
asserted.

*Proof.* Let $\Pi_n$ subtract the $\mu_n$-mean and $\Pi$ subtract
the $M$-mean. The polar decompositions supplied in IV, Theorems 111.3–111.4
are $C_n=\Pi_nJ_n=W_n\Sigma_n^{1/2}$ and
$C=\Pi J=W\Sigma^{1/2}$. Here $W_n$ is unitary from
$\mathscr E_n$ onto the finite mean-zero node space, and $W$ is
unitary from $\mathscr K$ onto $\mathbf1^\perp\subset\mathscr G$.
Define

$$
\iota_nf=(\langle\mathbf1,f\rangle_{\mu_n},W_n^*\Pi_nf),\qquad
\iota F=(\langle\mathbf1,F\rangle_M,W^*\Pi F).
\tag{270.10}
$$

These are the claimed isometries, also when the finite centered space
is zero. IV, Theorem 98.2 gives $v_n\to v$ and $\Sigma_n\to\Sigma$
in norm. Continuous square-root calculus proves (270.7).
For $s\ge0$ set

$$
g_s(x)=\begin{cases}\sqrt{x}e^{-s/x},&x>0,\\0,&x=0.\end{cases}
\qquad g_0(x)=\sqrt{x}.
\tag{270.11}
$$

The exact original generator correspondence in IV, (111.15) gives

$$
\begin{aligned}
\iota_nS_n(s)f_{u,n}
  &=(c+\langle v_n,z\rangle,g_s(\Sigma_n)z),\\
\iota T(s)F_u
  &=(c+\langle v,z\rangle,g_s(\Sigma)z).
\end{aligned}
\tag{270.12}
$$

This includes $s=0$; it does not replace the zero-time edge identity
by a positive-time limiting projection. Choose $M_*>0$ bounding all
$\|\Sigma_n\|$ and $\|\Sigma\|$. On $[0,M_*]$,

$$
\|g_s-g_t\|_\infty\le\sqrt{|s-t|},\qquad
\|g_s\|_\infty\le\sqrt{M_*}e^{-s/M_*}.
\tag{270.13}
$$

For $t=s+d$, the first bound follows from
$\sqrt{x}e^{-s/x}(1-e^{-d/x})\le
\min(\sqrt{x},d/\sqrt{x})\le\sqrt d$; symmetry handles $t<s$.
The second bound follows by monotonicity in $x$.
For each fixed $s$, continuous functional calculus and polynomial
approximation give $g_s(\Sigma_n)\to g_s(\Sigma)$ in norm.
A finite time net using the first bound, followed by the second bound
for large $s$, proves this uniformly over $s\ge0$.

The operators $A_n(s),A(s)$ have norm at most one. By (270.7) and
(270.12), (270.9)'s first limit holds on the dense subset
$\{\iota F_u:u=(c,z),\ z\text{ finite}\}$ of $\mathscr X_0$.
Indeed replacing $\iota F_u$ by $\iota_nf_{u,n}$ in the finite
term costs at most their norm difference, uniformly in $s$.
Density follows from density of the cylinder functions, already
supplied by IV, Theorem 111.2. Contraction extends the limit to every
$x\in\mathscr X_0$.

For multiplication, $\|D_{u,n}\|,\|D_u\|\le B_u$. On the same
dense subset, (270.4) and (270.7) give
$D_{u,n}\iota_nf_{u',n}\to D_u\iota F_{u'}$.
Replacing the input by $\iota F_{u'}$ costs at most $B_u$ times its
norm discrepancy. Density proves the second limit in (270.9).
A finite norm net in a compact input set and the uniform operator
bounds prove both compact-uniform assertions. Replacing $x$ by
$x_n$ adds at most $\|x_n-x\|$ or $B_u\|x_n-x\|$.
The scalar calculus and polar decomposition are mature intermediate
tools; see Teschl, [*Mathematical Methods in Quantum Mechanics*, online 2009 edition,
§3.1, Theorem 3.7 and the functional calculus preceding it](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf).
Their use here keeps the exact actual-node covariance and the original
factor $N_n$ in the clock. $\square$

**Theorem 270.4 (one stationary joint law and uniform finite-history convergence).**
Fix any integer $k\ge0$ and fixed pairs $u_j=(c_j,z_j)$,
$0\le j\le k$, as in Definition 270.1. Write $f_{j,n}=f_{u_j,n}$,
$F_j=F_{u_j}$ and, for $\delta\in[0,\infty)^k$, set
$t_0=0$, $t_j=\sum_{i=1}^j\delta_i$. Define

$$
\begin{aligned}
Q_n(\delta)
 &=\langle\mathbf1,\mathsf M_{f_{0,n}}S_n(\delta_1)
       \mathsf M_{f_{1,n}}\cdots
       S_n(\delta_k)\mathsf M_{f_{k,n}}\mathbf1\rangle_{\mu_n},\\
Q(\delta)
 &=\langle\mathbf1,\mathsf M_{F_0}T(\delta_1)
       \mathsf M_{F_1}\cdots
       T(\delta_k)\mathsf M_{F_k}\mathbf1\rangle_M.
\end{aligned}
\tag{270.14}
$$

For $k=0$ these mean just the corresponding single expectation.
For each $n$, let $X^{(n)}$ be the stationary heat chain on the complete
original $V_{T_n}$, with initial law $\mu_n$ and backward semigroup
$S_n$. There is one two-sided stationary reversible Markov law
$\mathbb P$ on $\Omega^{\mathbb R}$ with coordinate process $X_t$,
marginal $M$, and backward semigroup $T(s)$. The sigma algebra here is
the one generated by finite-time coordinates. These actual joint laws
satisfy

$$
Q_n(\delta)=\mathbb E_{\mu_n}\prod_{j=0}^kf_{j,n}(X^{(n)}_{t_j}),
\qquad
Q(\delta)=\mathbb E_{\mathbb P}\prod_{j=0}^kF_j(X_{t_j}),
\qquad
\sup_{\delta\in[0,\infty)^k}|Q_n(\delta)-Q(\delta)|\longrightarrow0.
\tag{270.15}
$$

Moreover, the complete joint distributions of these fixed finite-valued
readouts converge in total variation uniformly over the same gap set,
using a common finite alphabet that includes their shallow finite-node
values. Every zero gap is included and means repeated observation of
the same state, with ordinary multiplication of its fields.

*Proof.* The finite chain has rate $N_n$ on each existing unit edge in
the comparison parameter $s$, and invariant probability $\mu_n$ by
symmetry and zero row sums. Its transition from $x$ to $y$ is
$(S_n(s)\mathbf1_{\{y\}})(x)$. Conditioning successively on its
states proves the first nested expectation. It neither deletes interior
occurrences nor identifies equal subtree values.

For the boundary law, the mature Markov reconstruction supplies its
existence and uniqueness on the coordinate sigma algebra: Jorgensen–Neeb–Ólafsson,
[*Reflection Positive Stochastic Processes Indexed by Lie Groups*,
arXiv:1510.07445v3, SIGMA 12 (2016), 058, Definition 3.4,
Theorem 3.22 and Remark 3.23](https://arxiv.org/pdf/1510.07445v3),
with $(G,S,\tau)=(\mathbb R,\mathbb R_+,-\mathrm{id})$ and
$(\Omega,M,T,L^\infty(M),\mathbf1)$ in their standard case.
Here are the necessary hypothesis correspondences. The actual $\Omega$
is compact metrizable, hence Polish with its Borel sigma algebra.
By IV, Theorem 111.3, $T$ is a strongly continuous self-adjoint Markov
contraction, fixes $\mathbf1$, and preserves $M$. Its restriction to
$L^\infty(M)$ preserves positivity and one. It is normal there:
for $0\le h_\ell\uparrow h\le C$, dominated convergence in $L^2(M)$
and boundedness of $T(s)$ identify $T(s)h$ as the increasing limit of
$T(s)h_\ell$. Involutivity is self-adjointness, since $s^\sharp=s$.
Strong continuity in measure follows from $L^2$ continuity and
$M(|T(s)h-T(t)h|>\epsilon)\le\epsilon^{-2}\|T(s)h-T(t)h\|_2^2$.
The semigroup is total because $\mathbb R=\mathbb R_+\cup(-\mathbb R_+)$.
In the Hilbert version, $\mathbf1$ is a unit vector cyclic for the
time-zero multiplication algebra, and every nested product of positive
multipliers and Markov operators has nonnegative integral. The subgroup
$S\cap(-S)=\{0\}$ adds no normalization condition beyond the identity.
Thus no Feller property or pointwise kernel identity for all uncountably
many times is being assumed.

The cited Polish-space realization yields $\mathbb P$ on
$\Omega^{\mathbb R}$ with exactly (270.14) for all bounded Borel
observables and ordered times. Its usual finite-dimensional kernel
construction is also described in that source's Appendix B and
Remark 3.24. Conservativity gives consistency on deleting a time;
$T(0)=I$ gives coincident times. Self-adjointness reverses the nested
integral, proving reversibility; dependence only on gaps proves
stationarity. Cylinder probabilities determine the coordinate law
uniquely. In particular all the $F_j$ in (270.15) belong to this one
joint source law, not to separately matched marginals.

It remains to establish the finite-source convergence; the reconstruction
theorem alone does not give it. In the notation of (270.8), the moments
are the scalar products against $e=(1,0)=\iota_n\mathbf1=\iota\mathbf1$
of the alternating products of $D_{u_j,n},A_n(\delta_i)$ and of
$D_{u_j},A(\delta_i)$ applied to $e$.
The boundary semigroup extends strongly to $s=\infty$ by
$T(\infty)=P_{\mathbf1}$. In fact IV, (111.8) gives

$$
\|T(s)-P_{\mathbf1}\|\le e^{-s/\|\Sigma\|}\quad(s\ge0).
\tag{270.16}
$$

Here $\|\Sigma\|>0$; the inverse formula on $\mathscr K$ supplies
the positive gap, without a new spectral-counting argument.
Consequently $s\mapsto T(s)F$ is norm-continuous on the compact
interval $[0,\infty]$ for each $F\in\mathscr G$.
For every suffix of the boundary alternating product, its set of
values as the remaining gaps range over $[0,\infty]$ is compact in
$\mathscr X_0$. This follows inductively from bounded multiplication
and joint continuity of $(s,x)\mapsto A(s)x$ on that subspace: at a
point it follows from strong continuity and
$\|A(s)(x-y)\|\le\|x-y\|$.

Start at the rightmost $D_{u_k,n}e\to D_{u_k}e$. At each propagation
step, if $x_n(\eta)$ approximates a boundary suffix $x(\eta)$ uniformly,
then

$$
\begin{aligned}
\|A_n(s)x_n(\eta)-A(s)x(\eta)\|
 &\le\|x_n(\eta)-x(\eta)\|
       +\|(A_n(s)-A(s))x(\eta)\|,\\
\|D_{u,n}x_n(\eta)-D_ux(\eta)\|
 &\le B_u\|x_n(\eta)-x(\eta)\|
       +\|(D_{u,n}-D_u)x(\eta)\|.
\end{aligned}
\tag{270.17}
$$

The second terms tend to zero uniformly by the compact-input assertions
of Theorem 270.3. Induction through finitely many factors and then
scalar product with $e$ prove (270.15) on the entire unbounded gap set.
For $k=0$, (270.7) already proves it.

For the complete readout laws, fix a common support depth $h$ and
put $a_j(p)=c_j+\sum_{q\preceq p}z_{j,q}$ for $|p|\le h$,
including $a_j(\varnothing)=c_j$. Every value of the finite field,
for every $n$, and every value of its boundary field belong to the
finite alphabet $\mathcal B_j=\{a_j(p):|p|\le h\}$.
For any function $\psi:\mathcal B_j\to\mathbb R$, put

$$
d=\psi(c_j),\qquad
w_p=\psi(a_j(p))-\psi(a_j(p^-))\ (1\le|p|\le h),\qquad
w_p=0\ (|p|>h).
\tag{270.18}
$$

Telescoping on every actual root path and on every boundary path gives
$\psi(f_{j,n})=d\mathbf1+J_nw$ and
$\psi(F_j)=d\mathbf1+Jw$. Choose $\psi$ to be each singleton
indicator. Applying (270.15) to their products gives uniform convergence
of every atom in the finite product alphabet $\prod_j\mathcal B_j$.
The total variation distance is half the finite sum of the absolute
atom discrepancies, so it also tends to zero uniformly.
In particular shallow-node outputs were not discarded: stationarity
bounds the probability of any one of the $k+1$ sampled nodes having
depth below $h$ by $(k+1)(2^h-1)/N_n$, independently of the gaps.
$\square$

**Definition 270.5 (quantifiers of the comparison).** Theorems 270.2–270.4
concern each fixed finite family of original increment fields, with
fixed $k$ and depth. The supremum in (270.15) permits arbitrary
nonnegative gap choices depending on $n$, but does not assert a rate
uniform in growing $k$, growing depth, changing observables or their
bounds. It asserts neither derivatives at zero nor convergence in a
path topology. IV, Theorem 111.5 already distinguishes the two ordered
zero-time derivative limits. The processes for different $n$ have not
been coupled on one native execution; the common objects are their
specified addressed observables and the limiting joint law
$(\Omega,M,T,\mathbb P)$.

## 271. The reflection quotient of that same joint law

**Definition 271.1 (future space, reflection and quotient).** Use exactly
$\mathbb P$ from Theorem 270.4 on
$\mathcal W=\Omega^{\mathbb R}$. Let
$\mathcal F_+=\sigma(X_t:t\ge0)$,
$\mathcal F_0=\sigma(X_0)$ and
$\mathcal F_-=\sigma(X_t:t\le0)$, completed under this law.
On $\mathscr E=L^2(\mathcal W,\mathbb P;\mathbb R)$ put
$\mathscr E_+=L^2(\mathcal F_+;\mathbb R)$ and

$$
(\vartheta\omega)(t)=\omega(-t),\qquad
(\Theta G)(\omega)=G(\vartheta\omega),\qquad
[G,K]_{\rm OS}=\langle\Theta G,K\rangle_{\mathscr E}.
\tag{271.1}
$$

Let $rG$ be the unique $L^2(M)$ class specified by
$\mathbb E[G\mid\mathcal F_0]=(rG)(X_0)$.
The null quotient, once positivity is established, is the completion
of $\mathscr E_+/\mathcal N$, where
$\mathcal N=\{G:[G,G]_{\rm OS}=0\}$; write $qG$ for its classes.
For a bounded real Borel $F$ on $\Omega$, time-zero multiplication on
future functions is $G\mapsto F(X_0)G$. Positive shifts are
$V_sG(\omega)=G(\omega(\,\cdot+s))$, $s\ge0$.

**Theorem 271.2 (the original joint histories in their same-law quotient).**
For the law that is the uniform joint-history limit of the original
$T_n$ chains in Theorem 270.4, the quotient above has the identification

$$
\begin{gathered}
[G,K]_{\rm OS}=\langle rG,rK\rangle_M,
\qquad \mathcal N=\ker r,\qquad
\mathcal U:qG\longmapsto rG\text{ is onto and isometric},\\
\mathcal Uq\mathbf1=\mathbf1,\qquad
\mathcal U\widehat{\mathsf M}_F\mathcal U^{-1}=\mathsf M_F,\qquad
\mathcal U\widehat V_s\mathcal U^{-1}=T(s).
\end{gathered}
\tag{271.2}
$$

Here the hats denote the induced bounded operators on the quotient;
$\|\widehat{\mathsf M}_F\|=\|F\|_{L^\infty(M)}$, and
$\widehat V_s$ is a strongly continuous symmetric contraction
semigroup with nonnegative self-adjoint generator unitarily identified
with the original $H$. In particular, for the original fixed fields
of Theorem 270.4,

$$
\sup_{\delta\in[0,\infty)^k}
\left|Q_n(\delta)-
\left\langle q\mathbf1,
\widehat{\mathsf M}_{F_0}\widehat V_{\delta_1}
 \widehat{\mathsf M}_{F_1}\cdots
 \widehat V_{\delta_k}\widehat{\mathsf M}_{F_k}q\mathbf1
\right\rangle_{\rm OS}\right|\longrightarrow0.
\tag{271.3}
$$

The operator and form domains, under $\mathcal U$, are precisely

$$
\begin{aligned}
\operatorname{Dom}(H)
 &=\mathbb R\mathbf1\oplus W\operatorname{ran}\Sigma_{\mathscr K},\\
\operatorname{Dom}(H^{1/2})=\mathcal D
 &=\mathbb R\mathbf1\oplus W\operatorname{ran}\Sigma_{\mathscr K}^{1/2},\\
H\mathbf1&=0,\qquad
 H|_{\mathbf1^\perp}=W\Sigma_{\mathscr K}^{-1}W^*,\qquad
\mathcal E(F)=\|H^{1/2}F\|_2^2,
\end{aligned}
\tag{271.4}
$$

where $\Sigma_{\mathscr K}=\Sigma|_{\mathscr K}$. No additional modes
are obtained from $\ker\Sigma$.

*Proof.* The reconstruction and Markov quotient facts used here are
attributed intermediate applications of Jorgensen–Neeb–Ólafsson,
Proposition 3.3, Lemma 3.16(a–f), Theorem 3.22 and Remark 3.23, in the
version and exact parameter correspondence specified in Theorem 270.4.
They are not a new general reconstruction theorem. Their identification
with the joint limit of these original finite sources is (271.3).
For completeness the conditional-expectation computation fixes which
law, null space and state occur in this application.

Under $\mathbb P$, past and future are conditionally independent given
$X_0$. This follows first from its ordered Markov cylinder integrals
and then by the monotone class theorem. Time reflection preserves
$\mathbb P$ and fixes $X_0$, by reversibility. For $G,K\in\mathscr E_+$,
conditioning the past factor $\Theta G$ and future factor $K$ at
$X_0$ therefore gives
$\mathbb E[(\Theta G)K]=\mathbb E[(rG)(X_0)(rK)(X_0)]$.
First use bounded cylinder functions; conditional expectation is an
$L^2$ contraction and Cauchy–Schwarz extends the identity to all such
$G,K$. It proves reflection positivity and the null-space identity.
Every $F\in L^2(M;\mathbb R)$ is $r(F(X_0))$, so the quotient is
already complete after this identification and $\mathcal U$ is onto.
As $M$ is a probability, $\|q\mathbf1\|_{\rm OS}=1$.

Conditional expectation gives
$r(F(X_0)G)=F\,rG$ for bounded $F$, proving descent and the
multiplication identity. Its operator norm is exactly the essential
supremum, tested on time-zero functions. Similarly the same Markov
law gives $rV_sG=T(s)rG$: condition at time $s$ and then at time zero,
first for future cylinders and then by $L^2$ approximation.
Thus shifts preserve $\mathcal N$ and induce exactly the supplied
$T(s)$, with its positivity, symmetry, conservativity and continuity.
The full path shifts form a measure-preserving orthogonal group; its
strong continuity follows on bounded one-time functions from

$$
\|F(X_{t+h})-F(X_t)\|_{L^2(\mathbb P)}^2
 =2\|F\|_2^2-2\langle F,T(|h|)F\rangle_M\longrightarrow0.
\tag{271.5}
$$

For bounded products use telescoping and their uniform bounds;
finite cylinder functions are dense in the path $L^2$ space.
This also checks the time-action continuity required in the cited
reconstruction, without postulating sample-path continuity.

The time-zero algebra, state and positive shifts now give exactly
$Q(\delta)$ by (271.2). Substituting (270.15) proves (271.3), including
coincident times and the original shallow finite-node fields.
Finally (271.4) is the existing domain and polar description of IV,
Theorem 111.3. The actual free-root form and operator are also supplied
in `BiasedBoundaryFreeRootForm.free_root_least_energy`,
`BiasedBoundaryFreeRootForm.free_root_variational_graph`,
`BiasedBoundaryOperator.actual_self_adjoint_realization`,
`actual_compact_resolvent` and `actual_positive_spectral_exhaustion`,
under `D5/S3/Arith/FibonacciAtomic/Geometry/`.
The complete positive spectrum and its source-specific counting are
supplied by [*Biased boundary spectral counting*, Theorem 2.1](FIB_ATOM_BIASED_BOUNDARY_SPECTRAL_COUNTING.md).
Only the existing operator is identified here; neither its form nor
its spectral/counting results are reproved. $\square$

**Definition 271.3 (real carrier, optional complexification and clocks).**
The real quotient in (271.2) is $\mathscr G$, with real time-zero
multipliers and symmetric heat contractions. Its optional
complexification is $\mathscr G_{\mathbb C}=L^2(M;\mathbb C)$, with
$H_{\mathbb C}(F+iG)=HF+iHG$ on
$\operatorname{Dom}(H)+i\operatorname{Dom}(H)$ and form domain
$\mathcal D+i\mathcal D$. The complexified form has
$\mathcal E_{\mathbb C}(F+iG)=\mathcal E(F)+\mathcal E(G)$ for real
$F,G$. It has the additional bounded multiplication algebra
$L^\infty(M;\mathbb C)$ and normalized vector $\mathbf1$.
The cited complex Hilbert reconstruction can equivalently be applied
after this complexification; complex conjugation leaves its real
subspace and all preceding real formulas fixed.

Spectral calculus supplies the strongly continuous unitary group
$U(\tau)=e^{-i\tau H_{\mathbb C}}$, $\tau\in\mathbb R$.
It preserves the operator and form domains and fixes $\mathbf1$.
It is distinct from both the full path-shift group and the induced
heat semigroup. The parameter $s$ in the probability law is Euclidean
comparison time; $\tau$ is a parameter in this optional mathematical
unitary representation. Neither their identification nor physical-time
calibration is a consequence of (271.2). The choice of complexification
does not provide a native phase reference or coherent preparations.

## 272. The specified same-generator unitary readout fails on the same clock

**Assumption 272.1 (one operational candidate).** Work on exactly the
complexification of Definition 271.3, with the same $H_{\mathbb C}$,
state $\psi=\mathbf1$, and the two orthogonal cylinder projections
$P_L=\mathsf M_{F_L}$, $P_R=\mathsf M_{F_R}$, where
$F_L=\mathbf1_{[L]}$, $F_R=\mathbf1_{[R]}$.
Thus $P_L+P_R=I$, $P_RP_L=0$, and $\|\psi\|=1$.
Supply, as candidate mathematical operations, the unitary wait
$U(\tau)=e^{-i\tau H_{\mathbb C}}$ and the complete two-outcome
Lüders instrument $\rho\mapsto(P_L\rho P_L,P_R\rho P_R)$.
This instrument and the initial pure state are assumptions for testing
the candidate, not operations inferred from the original native menu.
Compare its unconditional recorded event “first $L$, then $R$” with
the same event of the boundary Markov law, using exactly
$\tau=\kappa s$ for one fixed finite real $\kappa\ne0$.

**Theorem 272.2 (the cylinder transfer excludes that candidate).**
Under Assumption 272.1, for every such $\kappa$,

$$
\begin{aligned}
p_{\rm U}(s)
 &=\|P_R e^{-i\kappa sH_{\mathbb C}}P_L\mathbf1\|_2^2=o(s),\\
p_{\rm M}(s)
 &=\mathbb P(X_0\in[L],X_s\in[R])
   =\langle F_L,T(s)F_R\rangle_M
   =\frac{s}{4}+o(s),\\
\lim_{s\downarrow0}\frac{p_{\rm M}(s)-p_{\rm U}(s)}s&=\frac14.
\end{aligned}
\tag{272.1}
$$

In particular these readouts cannot reproduce the joint histories of
Theorem 270.4 with this generator, state, projections and linear clock,
even just for this one pair event for all sufficiently small positive
$s$. Conditional on the first $L$, both probabilities are divided by
the same positive $a=M([L])$, so the conditional mismatch persists.

*Proof.* IV, Theorem 111.5 supplies, for these exact biased cylinders,
$F_L,F_R\in\mathcal D$, energies $1/4$, mixed energy $-1/4$,
and the second line of (272.1). Symmetry of $T$ identifies its ordering
with the $c(s)$ of that theorem. The same-law identification in §271
ensures this is the history law obtained from the original chains.

For the first line, write $\nu_L(B)=\|\mathbf1_B(H_{\mathbb C})F_L\|^2$.
The existing form domain gives
$\int_0^\infty\lambda\,d\nu_L(\lambda)=\mathcal E(F_L)=1/4$.
The mature spectral theorem and form-domain calculus used here are
Teschl, §3.1, Theorem 3.7 and (3.50)–(3.51); no twice differentiable
vector assumption is imported. For $t\ne0$,

$$
\begin{aligned}
\frac{\|(e^{-itH_{\mathbb C}}-I)F_L\|_2^2}{|t|}
 &=\int_0^\infty
   \frac{4\sin^2(t\lambda/2)}{|t|}\,d\nu_L(\lambda),\\
0\le\frac{4\sin^2(t\lambda/2)}{|t|}
 &\le\min(|t|\lambda^2,4/|t|)\le2\lambda.
\end{aligned}
\tag{272.2}
$$

The integrand tends to zero for each finite $\lambda$. Dominated
convergence by the integrable $2\lambda$ shows that (272.2) tends
to zero as $t\to0$. Since $P_RF_L=0$ and $\|P_R\|\le1$,

$$
\|P_R e^{-itH_{\mathbb C}}F_L\|_2^2
 =\|P_R(e^{-itH_{\mathbb C}}-I)F_L\|_2^2=o(|t|).
\tag{272.3}
$$

Substituting $t=\kappa s$ proves $p_{\rm U}(s)=o(s)$ for fixed
finite nonzero $\kappa$. The Lüders branch formula in Assumption 272.1
is exactly this squared norm, since its first unnormalized branch
is $P_L\psi=F_L$. Subtracting the supplied Markov asymptotic proves
the last line of (272.1). The first outcome has probability
$\|F_L\|^2=a>0$ in both models, giving the conditional assertion.
Only finite first spectral moment was used; no $O(s^2)$ estimate,
operator-domain membership of $F_L$, or second spectral moment is
asserted. $\square$

**Definition 272.3 (scope, attribution and remaining origin conditions).**
The repo-derived consequences here are the exact multiplication
correspondence with its shallow-node discrepancy, the uniform full
finite-history/readout-law limit for the original all-occurrence
Fibonacci chains, its identification with the same-law quotient, and
the incompatibility (272.1) for the specified operational candidate.
The Markov path construction, reflection positivity, null quotient,
Hilbert reconstruction and spectral calculus are literature-attested
intermediate supplies, with conditions and primary sources stated
in §§270–272. The source correspondence is with the golden biased
$M$, original unit-edge free-root energy and exactly $N_ns$; neither
the fair tree harmonic law nor a rescaled replacement generator is
used. These are conditional ordinary mathematical proofs; no fresh
Lean verification or claim of worldwide novelty is attached to them.

The obstruction in Theorem 272.2 quantifies only over the stated
same-generator, state-$\mathbf1$, cylinder-projection, Lüders candidate
and fixed finite nonzero linear comparison factor. It does not exclude
other instruments, states, auxiliary carriers, dilations, nonlinear
clocks or physical quantum representations. IV, Theorem 111.7 still
excludes only its direct local form-preserving class with the stated
domain and disjoint-support hypotheses. Nothing here broadens that
locality obstruction.

A native quantum interpretation retains all of IV, Assumption 111.8:
original $\mathsf{Read}$, $\mathsf{ApplyRho}$, $\mathsf{Halt}$ and
absorbing Stop, immutable INITIAL, reached-address guards, retention,
control, refusal, references and resource permissions. An ensemble law
and a unitary obtained by spectral calculus install none of these
operations. The further mathematical bridge must supply, on one common
source and operation model, available preparations and coherent
control; complex scalar/phase and reference compatibility; calibrated
Born probabilities and complete instruments including conditional
poststates; retained joint records and lawful composition with the
required reference systems; and executable original operations with
their original costs and an established clock correspondence.
The squared norms in the candidate are supplied Born/Lüders rules,
not a derivation of those rules. State $\mathbf1$ and a commutative
time-zero algebra alone do not specify all density inputs, quantum
instruments or a composition law. Their acquisition and compatibility,
a physical realization and physical time remain open obligations of
the full quantum-origin programme.

## 追加锚（本行以下为增补区）
