# Original passive words, observable geometry and source-boundary recovery

## 1. The original source and the exact-law premise

**Assumption 1.1 (the owning analytic source).** Use the source of
[RRO diffusion phase-cover rigidity, Definitions 1.1, 7.1 and 8.1][R],
with its analytic suppliers [E, §§109–112] and [S, §§115–117, 133].
All statements below are conditional on these source theorems. In
particular, retain the original product, identity and raw Haar measure

$$
\begin{gathered}
G=H^1\times\mathbb R,\qquad e=(0,0,0,0),\qquad
pp'=(x+x',y+y',z+z',w+w'+xy'),\\
d\mu=dx\,dy\,dz\,dw,\qquad
X_1=\partial_x,\quad X_2=\partial_y+x\partial_w,\quad
X_3=\partial_z,\qquad L=-\sum_{j=1}^3X_j^2,\\
L\Gamma=\delta_e,\qquad
\Gamma\circ\delta_s=s^{-3}\Gamma,\qquad
\delta_s(x,y,z,w)=(sx,sy,sz,s^2w).
\end{gathered}
\tag{1.1}
$$

The Green field is the fixed unit-source field. For finite
$a,\eta>0$ let

$$
\begin{gathered}
S_{a,\eta}=(aL-\eta\partial_w^2-16\sqrt{a\eta}\,\Gamma)
       |_{\mathcal D_0},\qquad
\mathcal D_0=C_c^\infty(G\setminus\{e\};\mathbb C),\\
\ker S_{a,\eta}^*=\mathbb Cw_*,\qquad
C(w_*)=1,\qquad h=w_*/\|w_*\|_{L^2(\mu)},\qquad
c_h=C(h)>0,\qquad \rho=A(h)/C(h).
\end{gathered}
\tag{1.2}
$$

Here $A,C$ are exactly the parameter-dependent maximal-domain
coefficients of [E, (109.1)–(109.3), (112.2)–(112.5)]. The entire
complex endpoint is

$$
\begin{gathered}
D(H)=\{u\in D(S_{a,\eta}^*):A(u)=\rho C(u)\}
     =D(\overline S_{a,\eta})\dotplus\mathbb Ch,\qquad Hu=S_{a,\eta}^*u,\\
H\ge0,\quad \ker H=\mathbb Ch,\qquad
F\ge0,\quad D(F)=\{u\in D(S_{a,\eta}^*):C(u)=0\},\quad H\ne F,\\
m=h^2\mu,\quad m(G)=1,\quad m(\{e\})=0,\qquad
J_hv=hv,\quad K=J_h^{-1}HJ_h,\quad T_t=e^{-tK}.
\end{gathered}
\tag{1.3}
$$

The representative of $h$ is real, smooth and strictly positive off
$e$. No ordinary value $h(e)$ is assigned. On
$\mathcal H=L^2(G,m;\mathbb C)$, $T_t$ is a self-adjoint Markov
contraction, $T_t1=1$, and $\ker K=\mathbb C1$. Its full form is

$$
\begin{gathered}
\mathscr V=D(K^{1/2})=\mathscr V_0\dotplus\mathbb C1,\qquad
\operatorname{tr}(v_0+z1)=z,\\
\mathscr E[v,u]=\int_Gh^2\left(
 a\sum_{j=1}^3\overline{X_jv}X_ju+
 \eta\overline{\partial_wv}\partial_wu\right)d\mu.
\end{gathered}
\tag{1.4}
$$

The subspace $\mathscr V_0$ is the form-norm closure of
$\mathcal D_0$ in $L^2(m)$, $J_h\mathscr V_0=D(F^{1/2})$, and
$\operatorname{tr}$ is continuous for every positively shifted form
norm. It is quasi-continuous evaluation at the nonpolar point $e$.
The actual conservative continuous-path process starts at $e$; its
positive-time entrance classes obey

$$
\begin{gathered}
\mathbb P_e(Z_t\in dx)=g_t(x)m(dx),\qquad
g_t\in L^2(m),\quad g_t>0\text{ a.e.},\quad \langle1,g_t\rangle_m=1,\\
g_{t+s}=T_sg_t\quad(t>0,s\ge0),\qquad
\operatorname{tr}(T_tv)=\langle g_t,v\rangle_m
       \quad(v\in\mathcal H,t>0),\qquad
g_t\in L^\infty(m)\quad(t>0).
\end{gathered}
\tag{1.5}
$$

Inner products are antilinear in the first slot. Equations
(1.3)–(1.5) retain the full endpoint, rather than replacing it by
the killed or Friedrichs endpoint.

**Definition 1.2 (the unchanged passive words).** Fix finite $d>0$.
Write $b=g_d$ as an $m$-class and retain exactly

$$
\begin{gathered}
P=T_d,\qquad
c=\frac1{4(1+\|g_d\|_\infty)},\qquad
\mathcal L=\{0,1,3,B\},\\
f_3=cb,\qquad f_B=\frac14,\qquad
f_0=f_1=\frac{3/4-f_3}{2}.
\end{gathered}
\tag{1.6}
$$

Every allowed Borel repair in [R, Definition 8.1] is permitted.
The hidden state at read $j$ is $X_j=Z_{(j+2)d}$, $j\ge0$.
Conditional on the path, the labels use these functions with fresh
independent read noise and leave the source unchanged. Thus the
first read is at $2d$ and each later gap is $d$.

Let $\varnothing$ denote the empty word and $u^R$ the reversal of a
finite word. For multiplication operators $M_y=M_{f_y}$ set

$$
F_\varnothing=1,\qquad F_{yu}=M_yPF_u,\qquad
p(u)=\langle Pb,F_u\rangle_m,
\qquad p(\varnothing)=1.
\tag{1.7}
$$

By [R, (8.4)], $p(u)$ is precisely the probability of the original
chronological cylinder $Y_0\cdots Y_{|u|-1}=u$.

**Assumption 1.3 (mathematical access).** The input is the entire
exact function $p:\mathcal L^*\to[0,1]$ of Definition 1.2.
This is an explicit premise about mathematical information. It
does not supply a stationary preparation, a reset, a coordinate
probe, selectable label outcomes, another emission, or another
physical sampling time. A numerical name for $d$, names for the
other parameters, and finite record error bounds are separate inputs.

[R]: RECURSIVE_RELATIONAL_OBSERVATION_DIFFUSION_PHASE_COVER_RIGIDITY.md
[E]: FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX.md
[S]: FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_II.md
[C]: FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_III.md
[O]: FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_IV.md

## 2. One original marked kernel and its actual Hilbert realization

**Definition 2.1 (the marked data).** Put $\mathcal W=\{3,B\}^*$.
On its finite complex word span define the sesquilinear kernel

$$
\mathsf G(u,v)=p(u^Rv3),\qquad u,v\in\mathcal W.
\tag{2.1}
$$

Every entry is one original legal chronological word probability.
In particular, word reversal in this index does not perform path
reversal. Let $\widehat{\mathcal H}$ be its zero-norm quotient and
Hilbert completion once positivity is established, and write $[u]$
for the word vectors. The source observable sector is

$$
\mathcal O=\overline{\operatorname{span}_{\mathbb C}
                  \{F_u:u\in\mathcal L^*\}}^{\,L^2(m)}.
\tag{2.2}
$$

The real kernel supplies a canonical real subspace and conjugation;
complexification does not introduce an additional physical phase
reference.

**Theorem 2.2 (the original marked Gram bridge).** The kernel
$(2.1)$ is positive semidefinite. Its completion has a unitary
realization onto the actual sector $(2.2)$ given by

$$
U[u]=c^{-1/2}P^{1/2}F_{u3}.
\tag{2.3}
$$

For $y\in\{3,B\}$ the prefix maps
$\widehat C_y[u]=[yu]$ descend through all zero-norm relations and
extend boundedly and self-adjointly. They satisfy

$$
U\widehat C_yU^{-1}
 =P^{1/2}M_yP^{1/2}|_{\mathcal O},\qquad
\widehat P:=4\widehat C_B,\qquad
U\widehat P U^{-1}=P|_{\mathcal O}.
\tag{2.4}
$$

In particular
$0\le\widehat P\le I$, $\ker\widehat P=0$, and

$$
\langle[u],\widehat P^{\,n}[v]\rangle
 =4^np(u^RB^nv3)\qquad(n\ge0).
\tag{2.5}
$$

*Proof.* Introduce only as source proof objects

$$
C_y=P^{1/2}M_yP^{1/2},\qquad
C_u=C_{u_1}\cdots C_{u_k},\qquad C_\varnothing=I.
\tag{2.6}
$$

The positive contraction $P=e^{-dK}$ is injective by the spectral
theorem. The square root is its spectral square root, not another
read. Conservation and induction in (1.7) give
$C_u1=P^{1/2}F_u$. The original calibration and the original lead-in
give, including the empty word,

$$
\begin{aligned}
c^{-1}\langle1,C_3C_w1\rangle_m
 &=c^{-1}\langle f_3,PF_w\rangle_m\\
 &=\langle b,PF_w\rangle_m
 =\langle Pb,F_w\rangle_m=p(w).
\end{aligned}
\tag{2.7}
$$

This is the specific marked identity of [R, (8.8)] expressed with
the sandwich operators. It follows that

$$
\begin{aligned}
p(u^Rv3)
 &=c^{-1}\langle1,C_3C_u^*C_vC_31\rangle_m\\
 &=c^{-1}\langle C_uC_31,C_vC_31\rangle_m\\
 &=c^{-1}\langle P^{1/2}F_{u3},P^{1/2}F_{v3}\rangle_m.
\end{aligned}
\tag{2.8}
$$

Thus the kernel is positive and (2.3) is initially isometric.
The positive-kernel quotient and completion used here are the
classical construction; the original cylinder identity (2.8) is
the source correspondence that instantiates it.

We verify the exact range. First $PF_u=4F_{Bu}$, so $\mathcal O$
is invariant under $P$ and hence reduces it. The restriction is
self-adjoint and injective, so its range is dense in $\mathcal O$.
Since $M_yPF_u=F_{yu}$ and $M_y$ is bounded, density shows that
every $M_y$ leaves $\mathcal O$ invariant and therefore reduces it.
It follows that every $C_y$ also reduces $\mathcal O$.
Moreover

$$
f_0=f_1=\frac32f_B-\frac12f_3,
\qquad C_0=C_1=\frac32C_B-\frac12C_3.
\tag{2.9}
$$

Expanding each occurrence of $0$ or $1$ in the recursion shows
that the $F_u$ with $u\in\mathcal W$ already span all the word
functions. Hence

$$
\overline{\operatorname{span}\{C_u1:u\in\mathcal W\}}
 =\overline{P^{1/2}\operatorname{span}\{F_u:u\in\mathcal W\}}
 =\mathcal O.
\tag{2.10}
$$

Let $\mathcal N=\overline{\operatorname{span}
\{C_uC_31:u\in\mathcal W\}}$. This lies in $\mathcal O$ and
reduces $C_3,C_B$, since these operators are bounded self-adjoint
and leave its defining span invariant. The operator $C_3$ is
injective: if $C_3z=0$, then

$$
0=\langle z,C_3z\rangle_m
  =\int f_3|P^{1/2}z|^2\,dm
\tag{2.11}
$$

and $f_3>0$ almost everywhere and injectivity of $P^{1/2}$ force
$z=0$. If $E_{\mathcal N}$ is the orthogonal projection, then
$C_3(I-E_{\mathcal N})1=0$ because $C_31\in\mathcal N$ and the
projection commutes with $C_3$. Thus $1\in\mathcal N$.
Equation (2.10) now gives $\mathcal N=\mathcal O$. This proves
surjectivity in (2.3), including the terminal-marker range issue.

Under (2.3), prefixing by $y$ is exactly the bounded operator
$C_y|_{\mathcal O}$. Consequently it preserves every null
combination before completion and has the claimed bounded extension.
Finally $C_B=P/4$; applying this to (2.8) proves (2.4)–(2.5).
$\square$

**Theorem 2.3 (the constant, the exact normalizer and readout
multiplication).** Set $v_*=[\varnothing]$, let
$E_1=\mathbf1_{\{1\}}(\widehat P)$, and define

$$
\begin{gathered}
c_p=\|E_1v_*\|^2
   =\lim_{n\to\infty}4^np(B^n3)>0,\qquad
\Omega=E_1v_*/\sqrt{c_p},\\
E_\epsilon=\mathbf1_{[\epsilon,1]}(\widehat P),\qquad
R_\epsilon=\widehat P^{-1/2}E_\epsilon
                \quad(0<\epsilon\le1),\\
N_3=\operatorname*{s-lim}_{\epsilon\downarrow0}
       R_\epsilon\widehat C_3R_\epsilon.
\end{gathered}
\tag{2.12}
$$

These limits exist in the stated source class, and

$$
c_p=c,\qquad U\Omega=1,\qquad
UN_3U^{-1}=M_{f_3}|_{\mathcal O}.
\tag{2.13}
$$

The other readout multipliers are
$N_B=I/4$ and $N_0=N_1=3I/8-N_3/2$. In particular the intrinsic
calibration obeys

$$
\langle\Omega,N_3\Omega\rangle=c,\qquad
\|N_3\|=\frac14-c.
\tag{2.14}
$$

*Proof.* Formula (2.3) gives $Uv_*=\sqrt c\,P^{1/2}b$.
Since $\int b\,dm=1$ and $\ker K=\mathbb C1$, the spectral
projection of this vector at the eigenvalue one of $P$ is
$\sqrt c\,1$. This proves the first two claims of (2.13).
Alternatively (2.5) at the empty endpoints gives

$$
4^np(B^n3)=c\langle b,P^{n+1}b\rangle_m\longrightarrow c,
\tag{2.15}
$$

because $P^n$ converges strongly to projection onto constants.
No rate is used. This recovers the original exact $c$; it has not
been supplied or replaced by an estimated upper bound for $\|b\|_\infty$.

The range and reduction proof in Theorem 2.2 is essential for the
next step. In source coordinates the expression in (2.12) is
$E_\epsilon M_{f_3}E_\epsilon|_{\mathcal O}$, where the
projections now refer to $P|_{\mathcal O}$. There is no zero
spectral atom, so $E_\epsilon\to I$ strongly, proving the limit.
Each $R_\epsilon$ is bounded, with norm at most
$\epsilon^{-1/2}$. This uses inverse heat only with spectral
cutoffs; it does not assert a bounded inverse of $P$.

Finally $1\in\mathcal O$ and the sector reduces $M_{f_3}$.
Its powers on $1$ detect the essential supremum of $f_3$:
$\|f_3^n\|_2^{1/n}\to\|f_3\|_\infty$. Thus the restricted
multiplier has the full multiplier norm. Equation (1.6) gives
$\|N_3\|=c\|b\|_\infty=1/4-c$, and integration gives the
remaining equality. $\square$

## 3. Exact observable equivalence, time and conditional continuation

**Theorem 3.1 (a complete invariant at the observable scope).** The
pointed tuple

$$
(\widehat{\mathcal H},\Omega,\widehat P,N_3)
\tag{3.1}
$$

constructed from the original words determines their entire law.
For any two sources satisfying Assumptions 1.1–1.3, equality of
the complete indexed word laws is equivalent to a unitary between
their observable sectors preserving $1$ and intertwining the
restricted $P$ and $M_{f_3}$. Such an intertwiner is unique. No
equivalence of the full spatial $L^2$ spaces is implied by this
assertion alone.

*Proof.* Recover from (3.1)

$$
\begin{gathered}
\widehat C_y=\widehat P^{1/2}N_y\widehat P^{1/2},\qquad
\widehat C_u=\widehat C_{u_1}\cdots\widehat C_{u_k},\\
p(u)=c^{-1}\langle\Omega,
                    \widehat C_3\widehat C_u\Omega\rangle,
\qquad c=\langle\Omega,N_3\Omega\rangle.
\end{gathered}
\tag{3.2}
$$

These are (2.7) and (2.13). Equality of the original laws gives
the same marked kernel, hence its canonical word-vector isometry,
its prefixes, (2.12) and (3.1). Conversely a pointed intertwiner of
$\widehat P,N_3$ preserves (3.2) for every original word. For
uniqueness, the marked vectors
$c^{-1/2}\widehat C_u\widehat C_3\Omega$ are the dense word
vectors $[u]$, so an intertwiner has a fixed action on a dense set.
This is minimality in the marked word-generated Hilbert sense,
rather than a claim about the shortest possible physical encoding.
$\square$

**Theorem 3.2 (the actual unsmoothed inner products and time
domains).** Put

$$
b_o=N_3\Omega/c,\qquad
F^o_\varnothing=\Omega,\qquad
F^o_{yu}=N_y\widehat P F^o_u.
\tag{3.3}
$$

Then $Ub_o=g_d$ and $UF^o_u=F_u$. In particular the law determines
the original $m$-inner products of every two word functions, not
only the smoothed marked Gram. Let $E$ denote the spectral
resolution of $\widehat P$ and
$\sigma_z(A)=\langle z,E(A)z\rangle$. There is a unique
nonnegative self-adjoint operator

$$
\begin{gathered}
\Lambda=-\log\widehat P,\qquad
D(\Lambda)=\left\{z:
 \int_{(0,1]}|\log x|^2\,d\sigma_z(x)<\infty\right\},\\
\widehat{\mathscr V}=D(\Lambda^{1/2})
 =\left\{z:\int_{(0,1]}(-\log x)\,d\sigma_z(x)<\infty\right\}.
\end{gathered}
\tag{3.4}
$$

It corresponds to $dK|_{\mathcal O}$, with

$$
U\widehat P^{\,r}U^{-1}=T_{rd}|_{\mathcal O}\quad(r\ge0),\qquad
U\widehat{\mathscr V}=\mathscr V\cap\mathcal O.
\tag{3.5}
$$

If the original clock $d$ is independently calibrated, the
observable physical generator is $\Lambda/d$, with domain
$U^{-1}(D(K)\cap\mathcal O)$. Without that input, (3.5) supplies
sample-step units.

*Proof.* Equation (3.3) follows by induction from (2.13), so
all its inner products are actual source inner products.
The restriction of $P$ reduces the entire Borel functional calculus
of $K$ because $k\mapsto e^{-dk}$ is injective on $[0,\infty)$
and has a Borel inverse on $(0,1]$. There is no spectral atom at
zero for $P$, though zero may belong to its spectrum. Apply the
unbounded Borel calculus, with exactly the domains in (3.4), to
this inverse. The resulting logarithm is $dK|_{\mathcal O}$.
The exponential is one-to-one on nonnegative real spectral
parameters, giving uniqueness in this self-adjoint class.
Equations (3.5) and the operator-domain statement follow under $U$.
These are the standard spectral results of [T, §3.1]; a bounded
matrix logarithm at spectral zero is not being substituted for them.
Fractional powers in (3.5) are mathematical consequences of the
exact law and the source class, not additional physical reads.
$\square$

**Theorem 3.3 (the original future-law interface).** Every original
finite word $u$ has $p(u)>0$. In the recovered space define

$$
z_u=\frac{\widehat C_u^*\widehat C_3\Omega}{c\,p(u)}.
\tag{3.6}
$$

Then for every future finite word $v$,

$$
\frac{p(uv)}{p(u)}=\langle z_u,\widehat C_v\Omega\rangle.
\tag{3.7}
$$

Two actual histories give the same vector $z_u$ if and only if
all their future conditional word probabilities agree.

*Proof.* At each of the finitely many positive read times the
hidden law is absolutely continuous with respect to $m$, and
every prescribed emission is strictly positive $m$-a.e.
Conditional independence makes the cylinder's conditional
probability the product of these positive factors. Its expectation
is therefore positive, giving $p(u)>0$. Equations (3.2) and
$\widehat C_{uv}=\widehat C_u\widehat C_v$ give (3.7).
By (2.10), $\widehat C_v\Omega$ has dense span; hence equality
of every pairing in (3.7) is equivalent to equality of the two
vectors. This instantiates the existing predictive-state
factorization [PRED]; it does not assert finite rank, finite
retained memory, acquisition of these vectors, or reconstruction
of the hidden path. $\square$

## 4. Entrance, source trace and the full-source capacity consumer

**Theorem 4.1 (the calibrated positive-time entrance and source
trace).** For every $r>0$ the vector

$$
\gamma_r=\widehat P^{\,r-1}b_o
\tag{4.1}
$$

exists on its spectral domain and satisfies $U\gamma_r=g_{rd}$.
For $0<r<1$ its precise domain assertion is

$$
\int_{(0,1]}x^{2r-2}\,d\sigma_{b_o}(x)<\infty.
\tag{4.2}
$$

On the form domain in (3.4) the law therefore determines

$$
\tau(v)=\lim_{r\downarrow0}\langle\gamma_r,v\rangle
       =\operatorname{tr}(Uv).
\tag{4.3}
$$

In the full source form the trace vanishes on
$\mathscr V\cap\mathcal O^\perp$.

*Proof.* For $r\ge1$, (4.1) is forward propagation of $g_d$.
For $0<r<1$, (1.5) gives
$g_d=P^{1-r}g_{rd}$. Let $Q$ project onto $\mathcal O$.
Since $Q$ commutes with the spectral calculus and $g_d\in\mathcal O$,

$$
P^{1-r}(I-Q)g_{rd}=0.
\tag{4.4}
$$

Injectivity proves $g_{rd}\in\mathcal O$. The actual vector
$g_{rd}$ is the inverse image of $g_d$ under $P^{1-r}$, so the
unbounded spectral inverse on this specific vector is defined and
has domain (4.2). No inverse is asserted for arbitrary vectors.

If $Uv\in\mathscr V$, the source identity in (1.5) identifies
the pairing in (4.3) with $\operatorname{tr}(T_{rd}Uv)$.
The heat semigroup tends to the identity in every shifted form
norm on $\mathscr V$, by dominated spectral convergence with
weight $k+q$, $q>0$. Form continuity of the actual trace now gives
(4.3). For $z\in\mathscr V\cap\mathcal O^\perp$, all
$\langle g_t,z\rangle$ vanish. Applying the same form limit
proves $\operatorname{tr}z=0$. Thus the last assertion is about
the full source trace, not an inference from cyclic unitarity alone.
$\square$

**Definition 4.2 (the original defect and the recovered energy).**
Retain the full-space quantities of [S, (115.4), (116.1)–(116.4)]

$$
\begin{gathered}
d_q=\langle h,(I-q(F+q)^{-1})h\rangle_{L^2(\mu)},\qquad
b^{\rm eq}_q=1-qh^{-1}(F+q)^{-1}h,\qquad q>0,\\
\operatorname{Cap}_q(\{e\})=q d_q.
\end{gathered}
\tag{4.5}
$$

There is no factor $1/2$ in the energy. For dimensionless
$\beta>0$ let

$$
\begin{gathered}
Q_\beta[v,u]=\langle\Lambda^{1/2}v,\Lambda^{1/2}u\rangle
                     +\beta\langle v,u\rangle,\\
\mathcal C_\beta
 =\inf\{Q_\beta[v]:v\in\widehat{\mathscr V}\text{ real},
                              \ \tau(v)=1\}.
\end{gathered}
\tag{4.6}
$$

**Theorem 4.3 (full-source capacity from a proper observable
sector).** The exact original law determines

$$
\mathcal C_\beta
 =d\operatorname{Cap}_{\beta/d}(\{e\})
 =\beta d_{\beta/d}>0
\qquad(\beta>0).
\tag{4.7}
$$

Writing $\sigma_b=\sigma_{b_o}$, the following singular integral
is finite and positive and gives the same number:

$$
\begin{gathered}
I_\beta=\int_{(0,1]}
       \frac{x^{-2}}{\beta-\log x}\,d\sigma_b(x),
\qquad 0<I_\beta<\infty,\\
\mathcal C_\beta=I_\beta^{-1},\qquad
d_{\beta/d}=\frac1{\beta I_\beta}.
\end{gathered}
\tag{4.8}
$$

The energy-Riesz vector and original equilibrium vector are

$$
z_\beta=
 \left[x\mapsto\frac{x^{-1}}{\beta-\log x}\right]
                    (\widehat P)b_o
 \in\widehat{\mathscr V},\qquad
U(z_\beta/I_\beta)=b^{\rm eq}_{\beta/d}.
\tag{4.9}
$$

*Proof.* The projection $Q$ of Theorem 4.1 reduces $K$, so
$\mathscr V$ splits across $\mathcal O$ and $\mathcal O^\perp$
with orthogonal shifted energies. The trace vanishes on the
second summand. For every full form vector with trace one,
projecting onto $\mathcal O$ preserves the trace and cannot
increase shifted energy. Conversely observable competitors are
full competitors. The full capacity infimum therefore equals
the observable infimum. By [S, (116.7)], trace one and trace at
least one have the same minimum and unique equilibrium vector.
Since $Q_\beta=d\mathscr E_{\beta/d}$ under $U$, this proves
(4.7), and also puts the full equilibrium vector in $\mathcal O$.

It remains to justify the singular integral, rather than merely
assign a formal inverse. Work first on a bounded spectral window
$\mathbf1_{[0,R]}(\Lambda)$. There (4.1)–(4.3) give

$$
\tau(v)=\langle b_o,e^\Lambda v\rangle.
\tag{4.10}
$$

The squared dual norm of this functional for $Q_\beta$ on that
window is

$$
I_{\beta,R}
 =\int_{[e^{-R},1]}
      \frac{x^{-2}}{\beta-\log x}\,d\sigma_b(x).
\tag{4.11}
$$

This is bounded by the finite squared norm of $\tau$ on the full
observable form domain, supplied by (1.4) and (4.3).
The windows are dense in that form norm. Monotone convergence
and Riesz representation give
$I_\beta=\|\tau\|_{Q_\beta^*}^2<\infty$, and the representing
vector is (4.9), with
$Q_\beta[z_\beta,v]=\tau(v)$. This proves its form-domain
qualification; its squared $L^2$ norm is at most $I_\beta/\beta$.
Since $\tau(\Omega)=1$, the dual norm is positive. The minimum
trace-one energy is its reciprocal, attained at
$z_\beta/I_\beta$. This proves (4.8)–(4.9), with the exact
original normalization $d_q$ from (4.5). $\square$

**Theorem 4.4 (the actual source-killed boundary at observable
scope).** The form $Q_\beta$ restricted to $\ker\tau$ is the
observable part of the original source-killed form. Let
$K^0=J_h^{-1}FJ_h$, the full killed operator of
[S, Theorem 116.3]. The subspace $\mathcal O$ reduces its
resolvent. In the recovered space its dimensionless resolvent is

$$
U^{-1}(dK^0+\beta)^{-1}|_{\mathcal O}U
 =(\Lambda+\beta)^{-1}
        -\frac{|z_\beta\rangle\langle z_\beta|}{I_\beta}.
\tag{4.12}
$$

*Proof.* The full zero-trace form domain splits as

$$
\mathscr V_0
 =\bigl(\mathscr V\cap\mathcal O\cap\ker\operatorname{tr}\bigr)
       \mathbin{\oplus}
   (\mathscr V\cap\mathcal O^\perp),
\tag{4.13}
$$

by Theorem 4.1. This is an orthogonal splitting for every shifted
energy, so it reduces the killed form and its resolvent. The
kernel of the nonzero continuous functional $\tau$ is dense in
$\widehat{\mathcal H}$: the full $\mathscr V_0$ is dense in
$L^2(m)$ by [S, Theorem 115.3], and $Q\mathscr V_0$ lies in
the observable zero-trace domain and is dense in $\mathcal O$.
Thus this restricted form has its usual self-adjoint operator.

For $f\in\widehat{\mathcal H}$ let
$w=(\Lambda+\beta)^{-1}f$. Its $Q_\beta$-orthogonal projection
onto $\ker\tau$ is
$w-z_\beta\tau(w)/I_\beta$. Since
$\tau(w)=Q_\beta[z_\beta,w]=\langle z_\beta,f\rangle$,
this proves (4.12). The source supplier identifies the resulting
part operator with $K^0$ on the full source. In particular this
does not identify $D(K^0)$ with $D(K)\cap\ker\operatorname{tr}$;
the latter would impose both raw coefficient equations, contrary
to [S, (116.11)]. $\square$

**Theorem 4.5 (original words supplying the capacity spectral
data).** The smaller original data family $p(B^n3)$, $n\ge0$,
already determines $\sigma_b$ and hence the scalar curve (4.8).
In particular

$$
\begin{gathered}
\frac{4^np(B^n3)}c
 =\int_{(0,1]}x^{n+1}\,d\sigma_b(x),\\
d_{1/(4d)}=\frac4{I_{1/4}},\qquad
d_{1/(Nd)}=\frac N{I_{1/N}}\quad(N\ge1).
\end{gathered}
\tag{4.14}
$$

*Proof.* The first identity is (2.15) before taking its limit.
Its right side gives all nonnegative moments of the finite measure
$x\,d\sigma_b(x)$ on $[0,1]$. Compact moment uniqueness follows
from density of polynomials in continuous functions and uniqueness
of the representing finite measure. Since the actual heat has
no zero spectral atom, dividing this measure by $x$ on $(0,1]$
uniquely recovers $\sigma_b$; no missing mass at zero is allowed.
Its finite total mass is supplied by $g_d\in L^2(m)$.
Substitute the two discounts into (4.8). The mature compact
moment fact is used only inside this original-word calculation.
$\square$

## 5. Full-domain source calibration and its exact parameter fibres

**Definition 5.1 (one dilation convention).** For $s,\kappa>0$
compare two legitimate members of the original source family by

$$
\begin{gathered}
a'=\frac{\kappa a}{s^2},\qquad
\eta'=\frac{\kappa\eta}{s^4},\qquad d'=\frac d\kappa,\\
\mathcal U_su=s^{5/2}u\circ\delta_s,\qquad
\mathcal W_sv=v\circ\delta_s.
\end{gathered}
\tag{5.1}
$$

Primes refer to that member's own original coefficients, normalized
zero state, full endpoint, clock and prescribed readout. This is a
comparison of models, not a change to a running experiment.

**Theorem 5.2 (the original full-domain scaling correspondence).**
The map $\mathcal U_s$ is unitary on the unchanged raw-Haar
$L^2(\mu)$ and transports the entire original domains. In
particular

$$
\begin{gathered}
S_{a',\eta'}^*\mathcal U_s=\kappa\mathcal U_sS_{a,\eta}^*,
\qquad D(S_{a',\eta'}^*)=\mathcal U_sD(S_{a,\eta}^*),\\
C'(\mathcal U_su)=sC(u),\qquad
A'(\mathcal U_su)=s\bigl(A(u)-(\log s)C(u)\bigr),\\
\rho'=\rho-\log s,\qquad c_h'=s c_h,\qquad
h'=\mathcal U_sh,\\
D(H')=\mathcal U_sD(H),\qquad
H'=\kappa\mathcal U_sH\mathcal U_s^{-1},\qquad
F'=\kappa\mathcal U_sF\mathcal U_s^{-1}.
\end{gathered}
\tag{5.2}
$$

The probability, time, trace and original word correspondences are

$$
\begin{gathered}
m'=(\delta_{1/s})_*m,\qquad
\mathcal W_s:L^2(m)\longrightarrow L^2(m')\text{ unitary},\\
K'=\kappa\mathcal W_sK\mathcal W_s^{-1},\qquad
\mathscr E'[\mathcal W_sv,\mathcal W_su]
       =\kappa\mathscr E[v,u],\qquad
\operatorname{tr}'(\mathcal W_sv)=\operatorname{tr}v,\\
g_t'=\mathcal W_sg_{\kappa t},\qquad
g_{d'}'=\mathcal W_sg_d,\qquad c'=c,\qquad
f_y'=\mathcal W_sf_y\text{ as classes},\qquad p'=p,\\
d_q'=d_{q/\kappa},\qquad
\operatorname{Cap}'_q(\{e\})
       =\kappa\operatorname{Cap}_{q/\kappa}(\{e\})\quad(q>0).
\end{gathered}
\tag{5.3}
$$

*Proof.* The Haar Jacobian of $\delta_s$ is $s^5$.
On the whole punctured smooth core,
$L\mathcal U_s=s^2\mathcal U_sL$,
$\partial_w^2\mathcal U_s=s^4\mathcal U_s\partial_w^2$, and
$\Gamma\mathcal U_s=s^3\mathcal U_s\Gamma$.
Since $16\sqrt{a'\eta'}=\kappa s^{-3}16\sqrt{a\eta}$,

$$
S_{a',\eta'}\mathcal U_s=\kappa\mathcal U_sS_{a,\eta}
\quad\text{on }\mathcal D_0.
\tag{5.4}
$$

The core maps bijectively to itself. Taking graph closures and
adjoints transports their full domains, since $\kappa$ is finite
and positive.

To compute the coefficients use their actual parameter-dependent
chart, rather than a parameter-independent radial convention.
Write $\ell=\sqrt{\eta/a}$, $\zeta=w-xy/2$ and
$Z=(x,y,z,\zeta/\ell)$. The coefficient diagnostic is exactly
[E, (109.1)–(109.3)]

$$
\begin{gathered}
f_u(x,y,z,t)=\ell^{1/2}u(x,y,z,\ell t+xy/2),\\
H_u(\tau,\omega)=e^{-\tau}f_u(e^{-\tau}\omega),\qquad
H_u=(A(u)+\tau C(u))e_0+Z_u,\qquad
e^{\tau/8}Z_u\in H^1\text{ on the positive cylinder end}.
\end{gathered}
\tag{5.5}
$$

The fixed angular vector $e_0$ is the normalized vector of
[E, (109.3)], independent of $a,\eta$ in this chart.
Here $\ell'=\ell/s$, and direct substitution yields

$$
f'_{\mathcal U_su}(Z)=s^2f_u(sZ),\qquad
H'_{\mathcal U_su}(\tau,\omega)
           =sH_u(\tau-\log s,\omega).
\tag{5.6}
$$

Translation by a fixed amount preserves the weighted remainder
condition on a sufficiently far positive end. Uniqueness of the
affine coefficients in (5.5) proves their formulas in (5.2),
including the logarithmic sign.

The unique maximal zero line is transported by (5.4). More
precisely, $w_*'=s^{-1}\mathcal U_sw_*$ has coefficient one.
Its norm is $s^{-1}\|w_*\|_2$, so $h'=\mathcal U_sh$ is
the coefficient-positive unit zero state. The entire selectors
$A=\rho C$ and $C=0$ are now transported by their displayed
coefficient formulas. Equivalently the full endpoint graph core
$\mathcal D_0+\mathbb Ch$ of [E, (112.4)–(112.5)] transports
bijectively. This proves the endpoint and Friedrichs statements
in (5.2), rather than merely an off-source differential identity.

The measure formula in (5.3) follows by change of variables, and
$J_{h'}\mathcal W_s=\mathcal U_sJ_h$. This proves the full
$K$ correspondence. On the punctured form core the derivative
identities give the energy factor $\kappa$. They extend to the
closure; multiplication of energy by a fixed positive constant
preserves equivalence of the form norms. Thus
$\mathscr V_0'=\mathcal W_s\mathscr V_0$ and
$\mathcal W_s1=1$, and the direct-sum trace in (1.4) is preserved.
The entrance identity now gives, for every $v\in L^2(m)$,

$$
\begin{aligned}
\langle g_t',\mathcal W_sv\rangle_{m'}
 &=\operatorname{tr}'(T_t'\mathcal W_sv)\\
 &=\operatorname{tr}(T_{\kappa t}v)
 =\langle\mathcal W_sg_{\kappa t},\mathcal W_sv\rangle_{m'}.
\end{aligned}
\tag{5.7}
$$

This identifies the actual source entrance, not another preparation.
At $d'=d/\kappa$, the essential norm of $g'_{d'}$ equals that
of $g_d$, hence the exact prescribed $c$ and all four readout
classes agree under $\mathcal W_s$. Also
$P'\mathcal W_s=\mathcal W_sP$ and
$g'_{2d'}=\mathcal W_sg_{2d}$. The word recursion gives
$F'_u=\mathcal W_sF_u$ and therefore $p'(u)=p(u)$ for every
chronological word. Borel repairs have no effect because each
positive-time state law is absolutely continuous with respect to
its own $m$. The time change maps the first epoch $2d'$ to
$2d$ and every gap $d'$ to $d$; conditional fresh-noise reading
and nondisturbance are preserved. Finally the full Friedrichs
correspondence gives
$I-q(F'+q)^{-1}=\mathcal U_s[I-(q/\kappa)(F+q/\kappa)^{-1}]
\mathcal U_s^{-1}$. Pairing with $h'=\mathcal U_sh$ proves
the defect transformation, and $\operatorname{Cap}_q=q d_q$
proves the capacity transformation. $\square$

**Theorem 5.3 (complete classification inside this source family).**
For any two finite positive triples in the family of Assumptions
1.1–1.2, including all allowed repaired representatives,

$$
p_{a,\eta,d}=p_{a',\eta',d'}
\quad\Longleftrightarrow\quad
\theta=\frac{a^2d}{\eta}
       =\frac{(a')^2d'}{\eta'}=\theta'.
\tag{5.8}
$$

Equivalently their triples lie in one orbit (5.1). A faithful
strictly separating scalar obtained from the original law is

$$
\mathcal I(p)=\frac{p(3)}{\lim_{n\to\infty}4^np(B^n3)}
             =\Phi(\theta),\qquad
\Phi(t)=\|g^{\rm ref}_{3t/2}\|_{L^2(m_{\rm ref})}^2,
\tag{5.9}
$$

where the reference source has $a=\eta=1$. The function
$\Phi$ is continuous and strictly decreasing on $(0,\infty)$.

*Proof.* The transformation (5.1) preserves $a^2d/\eta$.
Choosing $s^2=\eta/a$ and $\kappa=\eta/a^2$ sends a triple
to $(1,1,\theta)$. Theorem 5.2 proves sufficiency in (5.8).
Equations (1.7), (2.15), and self-adjoint propagation give

$$
\mathcal I(p)=\langle g_d,g_{2d}\rangle_m
             =\|g_{3d/2}\|_2^2.
\tag{5.10}
$$

Unitary source transport to the reference member proves (5.9).
This uses just an original one-letter probability and its
original-law normalizer, avoiding any presumption of same-time
duplicate reads.

For completeness $g_t$ is nonconstant at every $t>0$.
If $g_t=1$, then for $0<s<t$ the propagation law and injectivity
of $T_{t-s}$ force $g_s=1$. Choose a nonnegative continuous
compactly supported function $\varphi$ away from $e$ with
$\int\varphi\,dm>0$, possible by full local support of $m$.
Continuous paths started at $e$ give
$\mathbb E_e\varphi(Z_s)\to\varphi(e)=0$ as $s\downarrow0$,
whereas $g_s=1$ would make every such expectation
$\int\varphi\,dm>0$. This contradiction proves nonconstancy.

If $t_2>t_1>0$, apply the reference spectral theorem to
$g^{\rm ref}_{3t_1/2}$. Its spectral measure has positive mass
on positive energies because $\ker K_{\rm ref}=\mathbb C1$
and this vector is nonconstant. Therefore

$$
\Phi(t_1)-\Phi(t_2)
 =\int_{(0,\infty)}
       (1-e^{-3(t_2-t_1)k})\,
             d\sigma^{K_{\rm ref}}_{g^{\rm ref}_{3t_1/2}}(k)>0.
\tag{5.11}
$$

Positive-time strong continuity gives continuity of $\Phi$.
Equality of laws implies equality of $\mathcal I$, hence of
$\theta$ by strict decrease. Finally, if two triples have the
same $\theta$, solve
$s^2=\eta a'/(a\eta')$ and $\kappa=a's^2/a$; equality of
$\theta$ gives $d'=d/\kappa$. Thus (5.1) exhausts their
parameter ambiguity. No explicit expression or effective inverse
for $\Phi$ has been assumed. $\square$

**Theorem 5.4 (unequal calibrated targets with identical words).**
Even with a common fixed $d$, the complete original law over the
allowed parameter family does not determine the raw-coordinate
probability measure or the numerical coefficient $\rho$.
For $s>1$, compare
$(a,\eta,d)$ and $(a/s^2,\eta/s^4,d)$. Their laws agree, but

$$
\rho'=\rho-\log s,\qquad
m'(B_R)=m(B_{sR})>m(B_R)\quad(R>0),
\tag{5.12}
$$

where $B_R$ is a ball of any fixed proper continuous homogeneous
gauge, for example
$\varrho(p)=(|(x,y,z)|^4+(w-xy/2)^2)^{1/4}$.
If $d$ is not fixed as an external clock calibration,
$(a,\eta,d)$ and $(\kappa a,\kappa\eta,d/\kappa)$ also have
the same indexed law, with $K'=\kappa K$.

*Proof.* Use (5.2)–(5.3) with $\kappa=1$ for the first pair.
Homogeneity gives $\delta_sB_R=B_{sR}$. The intervening annulus
has a nonempty open subset away from $e$ and strictly positive
$m$-measure because $h>0$ there. This proves the strict
inequality and the unequal target, with the same raw coordinates
and measure convention in both models. Use $s=1$ for the clock
comparison. Since $K$ has a nonconstant heat orbit by [R,
Theorem 7.2], multiplication by $\kappa\ne1$ changes its
physical generator. Both comparisons retain the full derived
selector and the original read rule in their respective sources.
$\square$

**Definition 5.5 (the family prior in the stronger recovery).**
Theorem 5.3 identifies the full source tuple modulo the explicitly
transported dilation and clock scaling only under membership in
this precise differential family. With externally fixed $d$, its
remaining orbit has $\kappa=1$. With all $a,\eta,d$ externally
named and fixed, these are not competing parameter values.
Theorem 3.1 instead reconstructs the intrinsic observable tuple
without identifying a spatial representation. The former uses
the family equation, group, Haar convention, coefficient chart
and endpoint construction as prior information; they are not
deduced from a cyclic unitary. In particular neither theorem
claims that this source family exhausts all possible hidden
models of the same label process.

## 6. Spatial factor, invisible angular directions and actual paths

**Theorem 6.1 (the recovered readout factor and the proper
observable sector).** The recovered tuple determines the measure
$(g_d)_*m$ through

$$
\nu_b(E)=\langle\Omega,\mathbf1_E(N_3/c)\Omega\rangle
        =m\{x:g_d(x)\in E\}
\tag{6.1}
$$

for Borel $E\subset\mathbb R$. It determines the corresponding
one-readout commutative spectral algebra on its cyclic subspace.
But $\mathcal O$ is a proper subspace of the full $L^2(m)$,
with an infinite-dimensional orthogonal complement. No equality
of $\mathcal O$ with all rotation-invariant functions follows.

*Proof.* Formula (6.1) follows from $U\Omega=1$ and the actual
multiplier identification. The cyclic spectral theorem gives
exactly the factor generated by this scalar class.
For properness use the published source rotation symmetry of
[S, §120] and [C, §136]. In symmetric central coordinates
$\zeta=w-xy/2$, let $R_\alpha$ rotate $(x,y)$ while fixing
$(z,\zeta)$. It preserves $m$, fixes every $g_t$ and commutes
with $T_t$. Choose the invariant allowed representative supplied
by [C, Proposition 136.2]; all original sampled laws are
unchanged. Induction in (1.7) gives

$$
F_u\circ R_\alpha=F_u,\qquad
\mathcal O\subseteq L^2(m)^{\{R_\alpha\}}.
\tag{6.2}
$$

As in [O, (170.5)], choose disjoint positive-measure sets $A_n$
in a patch disjoint from its half-turn image and put
$v_n=\mathbf1_{A_n}-\mathbf1_{R_\pi A_n}$.
These are bounded, nonzero, linearly independent and odd under
the half-turn. By change of variables they are orthogonal to
every $F_u$, proving the assertion. The infinite dimension of
$\mathcal O$ itself is already supplied by [R, Theorem 7.2]:
it contains $g_d$ and the independent heat orbit of $g_{2d}$.
Neither this reuse nor (6.2) is a new passive-memory rank theorem.
$\square$

**Theorem 6.2 (a precise same-source path target not recovered
by the labels).** In the original experiment there exists a
nonzero bounded real half-turn-odd function $v$ such that
$v(X_0)$ is not almost surely a measurable function of the
entire infinite label sequence $(Y_j)_{j\ge0}$.

*Proof.* Take $v=\mathbf1_A-\mathbf1_{JA}$ with
$J=R_\pi$, $m(A)>0$ and $A\cap JA=\varnothing$, as in the
preceding proof. Since $g_{2d}>0$ a.e.,
$\mathbb P_e(v(X_0)\ne0)>0$. Full source rotation symmetry
preserves the $e$-start path law. Couple $Z$ and $JZ$ using
the same independent reading uniforms at all original epochs.
The invariant emission representative makes their entire label
sequences identical and replaces $v(X_0)$ by $-v(X_0)$.
Allowed noninvariant null repairs do not change this conclusion
in law, because the countable positive read times avoid their
null sets almost surely. Thus the joint law of
$((Y_j),v(X_0))$ equals that of $((Y_j),-v(X_0))$.
If $v(X_0)=F((Y_j))$ almost surely, the same joint-law identity
would give $-v(X_0)=F((Y_j))$ almost surely, a contradiction.
This is a path target within one original source. It is separate
from the unequal-model coefficient example (5.12), and proves
no impossibility of recovering an angularly invariant target.
$\square$

**Definition 6.3 (spatial and endpoint distinctions).** The sector
$\mathcal O$ has its actual Hilbert metric and the restrictions
of the original heat and readout multiplication. A closed linear
span of word functions need not be a multiplication algebra or
a vector lattice. In particular no correspondence has been
proved here from this sector to all raw spatial multiplication,
locality, coordinates, the metric, or a spatial quotient carrying
Markov transitions. Joint cyclicity for the algebra generated by
$\widehat P,N_3$ does not establish cyclicity for the commuting
algebra generated by $N_3$ alone. The latter is the additional
standard-space hypothesis in Jorgensen–Neeb–Ólafsson [J,
Proposition 3.7 and Theorem 3.27].

The operator $\Lambda/d$ is the actual full-endpoint generator
restricted to $\mathcal O$. Its normalized source trace is
recovered, and for its operator-domain vectors

$$
\tau(v)=\frac{C(hUv)}{C(h)},\qquad
A(hUv)=\rho C(hUv).
\tag{6.3}
$$

The raw dictionaries $J_h,A,C$ and $\rho$ are not all recovered
by that assertion; (5.12) shows why the last coefficient cannot
be intrinsic over the family. For general form vectors only
$\tau$ is assigned, without maximal-domain coefficients.
The equilibrium vector (4.9) belongs to the form domain; it is
not declared to belong to $D(K)$ or $D(H)$. No identification of
the two recovered operators with unrelated $\alpha,\beta$
syntaxes is made without another correspondence theorem.

## 7. Exact determination, numerical names and finite records

**Definition 7.1 (three different information premises).** Exact
set-theoretic access to $p$ as in Assumption 1.3, an effective
procedure returning certified rational approximations to each
$p(u)$, and finitely many actual labels with a confidence
guarantee are different premises. Theorems 2–6 concern the first.
Their proof uses a zero-norm quotient, a spectral projection at
one, strong operator limits, unbounded spectral functions on
qualified vectors and possibly singular integrals. No effective
modulus for these operations is included among the premises.

**Theorem 7.2 (the direction of a capacity truncation).** For
$0<\epsilon\le1$ set

$$
I_{\beta,\epsilon}
 =\int_{[\epsilon,1]}
       \frac{x^{-2}}{\beta-\log x}\,d\sigma_b(x).
\tag{7.1}
$$

Then $I_{\beta,\epsilon}\le I_\beta$ and, whenever the truncated
integral is positive,

$$
\mathcal C_\beta\le I_{\beta,\epsilon}^{-1},\qquad
d_{\beta/d}\le(\beta I_{\beta,\epsilon})^{-1}.
\tag{7.2}
$$

A certified upper bound $I_\beta\le U<\infty$, by contrast,
gives the lower bounds
$\mathcal C_\beta\ge1/U$ and
$d_{\beta/d}\ge1/(\beta U)$.

*Proof.* The integrand is nonnegative, so restriction of the
integration domain decreases the integral. Taking reciprocals
of positive numbers reverses the inequality, and (4.8) gives
all assertions. $\square$

**Definition 7.3 (the concrete remaining certificate interface).**
The quantities in (4.14) are exactly the unchanged original
defects required by [R, Proposition 9.6]. A future finite lower
certificate for them must upper-bound the corresponding complete
$I_\beta$, including its low-$x$ tail, or supply another
validated full-source bound. Positive truncated integrals alone
have the opposite direction by Theorem 7.2. Finiteness proved
using the analytic source trace does not itself give a rational
tail modulus, a numerical name for the source, or a finite
confidence packet with construction and validation costs.

Similarly the strict separation in (5.9) supplies a unique
mathematical inverse on the actual range of $\Phi$, without a
proved effective evaluation or inverse modulus. A convergence
rate for (2.15), conditioning and error control for the recovered
multipliers, finite probability acquisition, and a stopping rule
are not supplied by the exact-law equivalence. These statements
identify missing premises; they are not general impossibility
theorems for this parameter family.

**Definition 7.4 (the economical-relation correspondence and its
remaining spatial obligation).** A single original marked
probability kernel and the two existing letter prefixes recover
the useful relational carrier (3.1). In that carrier, inner
products, sample-time action, actual future-law tests and the
normalized source boundary have the explicit mutually faithful
maps of Theorems 2.2, 3.1, 3.3 and 4.1–4.4. Concrete consumers
are comparison of original full endpoints and the exact defect
targets in [R, Proposition 9.6].

To recover a spatial multiplication or locality structure from
this intrinsic carrier requires a distinguished suitable
commutative algebra, its measure and source binding, and a
proof transporting the relevant operations and domains. This
volume proves the scalar readout factor (6.1), the full-family
classification (5.8) under its source prior, and the particular
obstructions (5.12), (6.2) and Theorem 6.2. It does not prove
density in the rotation-fixed sector or supply that stronger
spatial-algebra correspondence. Exact mathematical recovery also
does not discharge the finite acquisition obligations in
Definition 7.3. These are the remaining differences from a
general mutual recovery of space, time, boundary and memory.

## 8. Mathematical suppliers and the new correspondence

**Definition 8.1 (reuse and hypothesis boundaries).** The new
`repo-derived` content is the original-law composition (2.8),
its full marked range and multiplier descent, the calibrated
inverse-heat/source-trace comparison with the unobserved
complement, and the exact parameter/endpoint correspondence
(5.2)–(5.11). The positive-kernel, spectral, compact moment and
minimal-realization principles used inside those proofs are
established results. No external priority assertion is needed
for this source-specific composition.

The source suppliers are [R, §§7–10] for the original heat orbit,
all actual words, the calibrated marker, and the unchanged
numerical defect consumer; [E, §§109–112] for the actual chart,
coefficient-one zero line and entire endpoint; [S, Theorems
115.3, 116.2–116.3, 117.2 and 133.2] for the form, source trace,
capacity, entrance and bounded readout; and [C, §136] and
[O, §§169–170] for the original rotation and invisible odd
classes. These analytic source hypotheses are retained in full.

The general realization suppliers have narrower and distinct
inputs. [RRO, §§125–126 and 137][RRO] treats complete linear
response or exact finite self-adjoint moment data with specified
inner product, positivity and kernel compatibility. The finite
real symmetric theorem
[`minimal_symmetric_realization_uniqueness`][SYM] consumes all
adjoint moments and reachability. The algebraic
[`finite_hankel_realization`][WH], including its residual/shift
and basis construction, consumes finite-dimensional residual
span. [`SequenceHankelRealization`][SH] constructs dynamics on
the span of supplied sequence tails. None supplies (2.8), the
original entrance calibration, or the source trace from passive
words, and no finite-dimensional hypothesis from those results
is imposed here. The source-specific conditional future vectors
in (3.6) instantiate [`predictive_state_universal_minimality`][PRED]
on realized histories and their complete future laws; that
factorization by itself supplies neither their Hilbert metric
nor their acquisition.

For the positive kernel in (2.1), the pinned Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679` provides
[`RKHS.OfKernel`, `kernel_ofKernel`, `RKHS.equiv`][RKHS],
including the seminormed finite-sum completion and its uniqueness
construction. Take the index set $\mathcal W$, scalars
$\mathbb C$ and scalar kernel $\mathsf G$; scalar multiplication
gives its one-dimensional operator-valued kernel. The kernel's
positive-semidefinite premise is proved in (2.8). Its standard
Hilbert quotient is reused, not reproved as a new abstract theorem.

The external `literature-attested` suppliers are [T, §3.1,
Theorems 3.1, 3.2 and 3.7, (3.25)–(3.30), (3.50)–(3.52)]
for bounded strong limits, unbounded Borel domains, forms and
unitary transport; [J, Proposition 3.7, Lemma 3.16 and Theorem
3.27] for the distinction between joint time/readout cyclicity
and cyclicity for a spatial multiplication algebra; and
[Thon–Jaeger, §2, Proposition 7, Corollary 8 and Proposition
12][TJ] for finite sequential-system rank, minimality and
similarity. The latter's finite-dimensional setting cannot
replace the source hypotheses here, and similarity alone cannot
replace the actual Gram identity. These are mature tools within
the proofs, not additional geometry-recovery theorems.

[RRO]: RECURSIVE_RELATIONAL_OBSERVATION.md
[SYM]: ../../../D5/S3/Quantum/Measurements/MinimalSymmetricRealizationUniqueness.lean
[WH]: ../../../D5/S3/Observer/Hankel/WordHankelRealization.lean
[SH]: ../../../D5/S3/Observer/Hankel/SequenceHankelRealization.lean
[PRED]: ../../../D5/S3/ObserverMemory/PredictionFactors/PredictiveStateUniversalMinimality.lean
[RKHS]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/InnerProductSpace/Reproducing.lean
[T]: https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf
[J]: https://arxiv.org/pdf/1510.07445v3
[TJ]: https://www.jmlr.org/papers/volume16/thon15a/thon15a.pdf

## 追加锚（本行以下为增补区）

## 9. Finite original-record geometry with ambient continuation certificates

### 9.1. The original record and its common uncertainty packet

**Definition 9.1 (the finite access contract).** Retain Assumption 1.1
and Definition 1.2, but replace Assumption 1.3 by one finite initial
segment of the actual label record. In particular the source remains
$G=H^1\times\mathbb R$ with raw Haar measure, the full complex endpoint
$A=\rho C$, the normalized $h$ and $m=h^2\mu$, the $e$-start, first
read at $2d$, gaps $d$, and exactly the original four emissions and
fresh conditional read noise. The mathematical constants $c$ and
$\|g_d\|_\infty$ are not numerical inputs.

Fix an integer $\ell\ge0$ and a finite list of distinct words
$S=(u_1,\ldots,u_q)$ in $\{3,B\}^{\le\ell}$, containing the empty
word. Put

$$
T=2\ell+3,\qquad K_T=4^T.
\tag{9.1}
$$

For $N\ge1$, use the original statistic [R, Definition 8.3] at
target length $T$. Thus $A(3v)$ counts the $N$ overlapping windows
with prescribed word $3v$, $v\in\mathcal L^T$, and

$$
Z=\sum_v A(3v),\qquad
\widehat\nu(v)=\frac{A(3v)+1}{Z+K_T}.
\tag{9.2}
$$

Use the full $4^{T+1}$-counter convention of that supplier. There
are exactly $N+T$ acquired labels, namely $Y_0$ through
$Y_{N+T-1}$; the last read is at $(N+T+1)d$. For any word
$w$ with $|w|\le T$, let $\widehat p(w)$ be its prefix marginal
under $\widehat\nu$, with $\widehat p(\varnothing)=1$.

A numerical confidence packet additionally specifies the same original
source and clock, rational $t>0$, and validated rational bounds

$$
0<D_0^-\le d_{1/(4d)},\qquad
0<D_N^-\le d_{1/(Nd)},\qquad D_0^-,D_N^-\le1.
\tag{9.3}
$$

These are precisely the full-source defects of [R, §§9, 11]. They
can be supplied as validated certificates, or constructed using the
additional original coefficient and clock names of [R, Definition
11.1 and Theorem 11.4]. Their encoding and construction or validation
cost belong to the input bill. They are not inferred from labels.
Define the rational variance envelope and the failure bound

$$
\begin{gathered}
\overline V=\frac{2T+1}{4N}
             +2\frac{1-D_N^-}{D_N^-},\qquad
\alpha=\min\left\{1,\frac{4^{T+1}}t
                      \sqrt{\frac{\overline V}{D_0^-}}\right\},\\
e_p=\min\left\{1,\frac{Nt+K_T}{Z+K_T}\right\}.
\end{gathered}
\tag{9.4}
$$

An upward rational enclosure of $\alpha$ may replace it. The packet's
$N,T,t$ and defect certificates are selected without consulting the
record used for this packet. Selection from a predeclared sequence of
packets is treated in Definition 9.8 below.

The supplied results give a single event $\mathcal E$ with

$$
\mathbb P_e(\mathcal E)\ge1-\alpha,\qquad
\mathcal E\ \Longrightarrow\
\operatorname{TV}(\widehat\nu,p|_{\mathcal L^T})\le e_p,
\quad |\widehat p(w)-p(w)|\le e_p\quad(|w|\le T).
\tag{9.5}
$$

Here and below $p|_{\mathcal L^T}$ means the original length-$T$
probability vector, not restriction to a new experiment. To identify
the interface exactly, take
$\Delta=\sum_v|A(3v)/N-\pi_{T+1}(3v)|$. The marked identity of
[R, Theorem 8.2] is $\pi_{T+1}(3v)=cp(v)$. Theorem 9.4 there,
with window length $T+1$, bounds
$\mathbb P_e(\Delta>t)$ by (9.4), since
$\Delta\le2\operatorname{TV}(a_{N,T+1},\pi_{T+1})$.
Proposition 8.5 there gives (9.5) on $\{\Delta\le t\}$.
These existing sampler and dependence estimates are the suppliers;
no independent-window or stationary-preparation hypothesis is added.
In particular $Z=0$ is allowed, giving $e_p=1$ rather than a false
precise certificate. Label-only access provides (9.2) and its fixed
horizon consistency, but not a nontrivial numerical (9.5).

### 9.2. Two original prefixes and a finite positive carrier

**Definition 9.2 (normalized marked vectors and the measured blocks).**
Work on the real part of the source sector $\mathcal O$; all the
following real pairings extend by complexification. Theorem 2.2 gives
the source proof vectors and operators

$$
\begin{gathered}
\beta_i=4^{|u_i|},\qquad v_i=\beta_i U[u_i],\qquad
Va=\sum_{i=1}^q a_i v_i,\\
R_B=P,\qquad R_3=4P^{1/2}M_3P^{1/2},\qquad
0\le R_3\le R_B\le I,\qquad \|v_i\|_m\le1.
\end{gathered}
\tag{9.6}
$$

The factor four normalizes an existing prefix; it changes neither an
emission nor its calibration. The order follows from $0\le4f_3\le1$.
Also $v_i=R_{u_{i,1}}\cdots R_{u_{i,|u_i|}}U[\varnothing]$,
and $\|U[\varnothing]\|^2=p(3)\le1$, proving the last bound.
These are source correspondences used in proofs, not hidden-coordinate
inputs to the finite construction.

For $y\in\{B,3\}$ define real symmetric blocks

$$
\begin{aligned}
G_{ij}&=\langle v_i,v_j\rangle_m
       =\beta_i\beta_jp(u_i^Ru_j3),\\
(B_y)_{ij}&=\langle v_i,R_yv_j\rangle_m
       =4\beta_i\beta_jp(u_i^Ryu_j3),\\
(D_y)_{ij}&=\langle R_yv_i,R_yv_j\rangle_m
       =16\beta_i\beta_jp(u_i^Ryyu_j3).
\end{aligned}
\tag{9.7}
$$

Every probability here is an original legal word of length at most
$T$. In particular $D_y$ measures the whole source norm after a
prefix, including the component orthogonal to $\operatorname{ran}V$.
It is not reconstructed by multiplying fitted $q\times q$ matrices.

Replace $p$ by $\widehat p$ in (9.7), round each entry to a dyadic
with absolute error at most a specified $\zeta=2^{-b}$, $b\ge0$,
and average each matrix with its transpose. Denote the five resulting
rational symmetric matrices by
$\widehat G,\widehat B_B,\widehat B_3,\widehat D_B,\widehat D_3$.
Exact rational entries with $\zeta=0$ are also permitted. Put

$$
\epsilon=4^{2\ell+2}e_p+\zeta,\qquad \delta=q\epsilon.
\tag{9.8}
$$

On $\mathcal E$, each of the five entry errors is at most
$\epsilon$, and each Euclidean operator-norm error is at most
$\delta$. Symmetrization preserves these bounds. This is the only
word-noise amplification used to fit the carrier; no later query
length is inserted into (9.8).

Choose rational $\lambda>0$ and set

$$
\begin{gathered}
S_f=\widehat G+(5\delta+\lambda)I,\qquad
L_3=\widehat B_3+\delta I,\qquad
L_B=\widehat B_B+3\delta I,\\
A_3=S_f^{-1}L_3,\qquad A_B=S_f^{-1}L_B,\qquad
\langle a,b\rangle_f=a^{\mathsf T}S_f b.
\end{gathered}
\tag{9.9}
$$

The rational construction first checks
$S_f\ge\lambda I$, $L_3\ge0$, $L_B-L_3\ge0$ and
$S_f-L_B\ge0$. These are finite rational quadratic-form order
tests. If one fails, the result is inconclusive; a total carrier
value can be assigned as $S_f=(1+\lambda)I$, $A_B=A_3=0$,
without asserting the source comparison below. No exact rank or
zero test of an unknown real number occurs.

**Theorem 9.3 (acquired marked geometry in the original source).**
On the single event $\mathcal E$, the order tests in Definition 9.2
pass. The rational Hilbert carrier
$(\mathbb R^q,\langle\cdot,\cdot\rangle_f)$ has
$S_f$-self-adjoint operators

$$
0\le A_3\le A_B\le I.
\tag{9.10}
$$

The actual-source map $V$ satisfies, simultaneously for all real
coefficient vectors $a$,

$$
\begin{gathered}
G+(4\delta+\lambda)I\le S_f
                  \le G+(6\delta+\lambda)I,\qquad
\|Va\|_m\le\|a\|_f,\\
0\le\|a\|_f^2-\|Va\|_m^2
               \le(6\delta+\lambda)\|a\|_2^2.
\end{gathered}
\tag{9.11}
$$

Consequently (9.11), applied to differences, certifies the squared
distances of all retained marked combinations. The operator
$A_B$ represents one original sample-time step, and $A_3$ the
normalized original marker prefix, with the source-error certificate
in Theorem 9.4. The comparison is valid for singular and arbitrarily
ill-conditioned $G$.

*Proof.* Apply (2.8) to the scaled words in (9.6). Inserting one
or two self-adjoint prefixes gives exactly (9.7), in its displayed
order. Thus
$0\le B_3\le B_B\le G$ and $D_y=V^*R_y^2V$.
Equation (9.5), scaling and rounding give (9.8). A symmetric
$q\times q$ entry error bounded by $\epsilon$ has operator norm
at most $q\epsilon$, by Cauchy--Schwarz in the finite sums.
It follows that

$$
\begin{gathered}
L_3\ge B_3\ge0,\qquad
L_B-L_3\ge B_B-B_3\ge0,\\
L_B\le B_B+4\delta I\le G+4\delta I,\qquad
S_f\ge G+(4\delta+\lambda)I.
\end{gathered}
\tag{9.12}
$$

This proves all rational tests, including strict invertibility of
$S_f$. In its inner product, $A_y$ has quadratic form $L_y$;
(9.12) proves (9.10), self-adjointness and contractivity.
The upper error bound for $\widehat G$ also gives the upper
inequality in (9.11). Taking quadratic forms proves the remaining
claims. This uses ordinary finite positive-form calculus; the new
source input is the three original-word identities (9.7).
$\square$

The retained $q$ is a chosen coordinate count, not a certified Gram
rank. If $Va=0$, (9.11) bounds the artificial squared length by
$(6\delta+\lambda)\|a\|_2^2$. Keeping such directions avoids
deciding which nearly null combinations are exactly null. In
particular the finite carrier is not asserted to be isometric to an
exact $q$-dimensional hidden source.

### 9.3. Ambient leakage, original letters and repeated use

**Theorem 9.4 (a source-space continuation certificate).** On
$\mathcal E$, for every $a\in\mathbb R^q$ and
$y\in\{B,3\}$, define

$$
\begin{aligned}
\widehat Q_y(a)
 &=a^{\mathsf T}\widehat D_y a
   -2(A_ya)^{\mathsf T}\widehat B_y a
   +(A_ya)^{\mathsf T}\widehat G(A_ya),\\
r_y(a)
 &=\min\left\{2\|a\|_f,
  \sqrt{\max(0,\widehat Q_y(a))
           +\epsilon(\|a\|_1+\|A_ya\|_1)^2}\right\}.
\end{aligned}
\tag{9.13}
$$

Then

$$
\|R_yVa-VA_ya\|_m\le r_y(a).
\tag{9.14}
$$

In particular (9.14) bounds
$\|(I-\Pi_S)R_yVa\|_m$, where $\Pi_S$ is the actual
orthogonal projection onto $\operatorname{ran}V$. The projection
and this range are proof objects; no observer access to them is used.

For every original letter define its source sandwich operator
$C_z=P^{1/2}M_zP^{1/2}$ and its finite representative by

$$
\begin{array}{c|c|c|c}
z&C_z&F_z&\kappa_z\\ \hline
B&R_B/4&A_B/4&1/4\\
3&R_3/4&A_3/4&1/4\\
0,1&(3R_B-R_3)/8&(3A_B-A_3)/8&3/8
\end{array}
\tag{9.15}
$$

Both source and finite operators in each row are positive, with norm
at most $\kappa_z$ in their respective Hilbert spaces. Valid local
residual bounds are

$$
s_B(a)=r_B(a)/4,\qquad s_3(a)=r_3(a)/4,\qquad
s_0(a)=s_1(a)=\frac{3r_B(a)+r_3(a)}8.
\tag{9.16}
$$

Consider any finite application sequence $O_1,\ldots,O_H$, where
each $O_j$ is either $R_B,R_3$ or one of the four $C_z$. Use
the corresponding finite map $A_B,A_3$ or $F_z$, denoted by
$\widetilde O_j$. Let $\kappa_j=1$ for $R_B,R_3$, and use
(9.15) for the letters. Starting from an arbitrary rational $a_0$,
put

$$
\begin{gathered}
a_j=\widetilde O_j a_{j-1},\qquad z_0=Va_0,\qquad
z_j=O_jz_{j-1},\\
E_0=0,\qquad
E_j=\kappa_jE_{j-1}+s_{O_j}(a_{j-1}),
\end{gathered}
\tag{9.17}
$$

where $s_{R_y}=r_y$ and $s_{C_z}=s_z$. Then

$$
\|z_j-Va_j\|_m\le E_j\qquad(0\le j\le H).
\tag{9.18}
$$

These inequalities hold on the same $\mathcal E$ for all finite
query lengths, sequences and rational starting coefficients,
including choices made from this packet's acquired matrices.
There is no additional independence assumption or multiplication of
confidence levels.

*Proof.* Expansion of the actual squared norm gives

$$
\|R_yVa-VA_ya\|_m^2
 =a^{\mathsf T}D_ya-2(A_ya)^{\mathsf T}B_ya
                   +(A_ya)^{\mathsf T}G(A_ya).
\tag{9.19}
$$

Its difference from $\widehat Q_y(a)$ has absolute value at most
$\epsilon(\|a\|_1+\|A_ya\|_1)^2$, term by term. Both
$V$ and $A_y$ are contractions in (9.11) and (9.10), so the
norm in (9.19) is also at most $2\|a\|_f$. This proves (9.14).
The orthogonal projection kills $VA_ya$ and is a contraction,
proving the ambient leakage assertion. In particular a small fitted
normal-equation residual is not substituted for the measured
$D_y$ term.

The source identities in (9.15) are exactly (2.9) and $C_B=P/4$.
For $0,1$, positivity follows from $R_3\le R_B$ and
$A_3\le A_B$; the upper bound follows from
$3R_B-R_3\le3I$ and $3A_B-A_3\le3I$.
The other two rows follow immediately. Linear combination of the
two actual residual vectors gives (9.16). Finally

$$
z_j-Va_j=O_j(z_{j-1}-Va_{j-1})
            +(O_jVa_{j-1}-V\widetilde O_ja_{j-1}).
\tag{9.20}
$$

Apply the operator bounds and induct. This is the usual residual
propagation argument, also used in [PRE]; (9.7) and (9.19) pay its
previously missing original-source measurement obligation. All
entrywise inequalities were established on one event before any
coefficient or query was chosen. They hold for every real vector,
so their subsequent data-dependent applications require no union
bound over queries. $\square$

### 9.4. Sample time and specified original future events

**Theorem 9.5 (finite relational outputs and original prediction
tests).** Start (9.17) at $a_0=e_j$. For every retained $i$, put

$$
\mathcal B_i=E_H+\epsilon\|a_H\|_1
                         +(5\delta+\lambda)|(a_H)_i|.
\tag{9.21}
$$

On $\mathcal E$,

$$
\left|\langle v_i,O_H\cdots O_1v_j\rangle_m
                   -e_i^{\mathsf T}S_fa_H\right|
 \le\mathcal B_i.
\tag{9.22}
$$

In particular the following outputs are certified.

For $n\ge0$, apply $A_B$ $n$ times. The clipped estimate
$[e_i^{\mathsf T}S_fA_B^ne_j/(\beta_i\beta_j)]_{[0,1]}$
has error at most $\min(1,\mathcal B_i/(\beta_i\beta_j))$
against the original sample-time pairing

$$
\frac{\langle v_i,P^nv_j\rangle_m}{\beta_i\beta_j}
       =4^np(u_i^RB^nu_j3).
\tag{9.23}
$$

This compares the actual heat evolution for $n$ sample steps on
the retained smoothed word functions. When a numerical clock name
is supplied, these are the times $nd$; without it this action still
has its sample-step meaning. No extra read at an intermediate time
or selected $B$ outcome is performed.

For an arbitrary word $w=w_1\cdots w_H\in\mathcal L^H$,
apply the finite maps in the order
$F_{w_H},F_{w_{H-1}},\ldots,F_{w_1}$. Then

$$
\begin{gathered}
n_{i,w,j}=p(u_i^Rwu_j3)
     =\frac{\langle v_i,C_{w_1}\cdots C_{w_H}v_j\rangle_m}
                  {\beta_i\beta_j},\\
\widehat n_{i,w,j}
 =\left[\frac{e_i^{\mathsf T}S_f
                 F_{w_1}\cdots F_{w_H}e_j}
                    {\beta_i\beta_j}\right]_{[0,1]},\qquad
|\widehat n_{i,w,j}-n_{i,w,j}|
       \le\Delta_{i,w,j}:=\min\left(1,
                                 \frac{\mathcal B_i}{\beta_i\beta_j}\right).
\end{gathered}
\tag{9.24}
$$

Thus a fixed training horizon $T$ supports certificates for inserted
words longer than $T$, at the price of the measured and accumulated
leakage. The bound may be inconclusive. The reversed order of applying
matrices in this assertion is essential: the chronological word is
$u_i^Rw_1\cdots w_Hu_j3$, not $u_i^Rw_H\cdots w_1u_j3$.

For the fixed original history $h=u_i^R$, use its marginal
$\widehat p(h)$ from Definition 9.1. If

$$
\widehat p(h)>e_p,
\tag{9.25}
$$

then the clipped scalar conditional test

$$
\widehat r_{i,w,j}
 =\left[\frac{\widehat n_{i,w,j}}{\widehat p(h)}\right]_{[0,1]}
\tag{9.26}
$$

satisfies, simultaneously with (9.22)--(9.24),

$$
\left|\widehat r_{i,w,j}
   -\mathbb P_e\{Y_{|h|}\cdots
      Y_{|h|+|wu_j3|-1}=wu_j3\mid Y_0\cdots Y_{|h|-1}=h\}\right|
 \le\min\left\{1,
        \frac{\Delta_{i,w,j}+e_p}{\widehat p(h)}\right\}.
\tag{9.27}
$$

For the empty history use its exact probability one and denominator
error zero. If (9.25) fails, the conditional output is inconclusive.
No lower probability bound for a rare history is presumed.

*Proof.* The difference in (9.22) is bounded by
$\|v_i\|_mE_H+|e_i^{\mathsf T}(G-S_f)a_H|$.
Use $\|v_i\|_m\le1$, the entry error for $\widehat G$ and
the explicit diagonal shift in (9.9), obtaining (9.21).
Theorem 2.2 gives (9.23). Inserting $C_{w_1}\cdots C_{w_H}$
between the two marked vectors in (2.8) gives (9.24), including
its chronological order for all four letters. Both true scalars in
(9.23) and (9.24) belong to $[0,1]$: for the former use positive
source word functions, positivity preservation of $P$, and their
norm bound; for the latter use the original word probability.
Clipping a real estimate to this interval cannot increase its error.

For (9.27), let $n=p(hwu_j3)$, $p_h=p(h)$ and
$\widehat p_h=\widehat p(h)$. On $\mathcal E$, (9.25)
gives $p_h\ge\widehat p_h-e_p>0$. The source also gives
$0\le n\le p_h$. Therefore

$$
\left|\frac{\widehat n}{\widehat p_h}-\frac n{p_h}\right|
 \le\frac{|\widehat n-n|}{\widehat p_h}
      +\frac n{p_h}\frac{|p_h-\widehat p_h|}{\widehat p_h}
 \le\frac{\Delta_{i,w,j}+e_p}{\widehat p_h}.
\tag{9.28}
$$

Clip once more and use the original cylinder conditioning identity.
No separately optimized probabilities or independently sampled
histories have been combined. $\square$

Individual tests (9.27) need not form a normalized distribution as
$w,j$ vary. Products of positive sandwich operators need not give
nonnegative finite fitted pairings; this is why scalar clipping is
specified. Nor does $\sum_zF_z=A_B$ supply a finite Markov filter:
no fitted fixed constant vector or normalized all-future law has
been constructed. The retained vectors are marked observable
directions, not the current hidden state or the exact predictive
vectors $z_u$ of (3.6). In particular (9.27) concerns a named
original history; substituting the growing history at the current
record cut requires a new denominator and horizon contract.

### 9.5. Finite arithmetic and the acquisition bill

**Definition 9.6 (precision, retention and cost of these outputs).**
All quantities in (9.2), the rounded matrices, the order tests,
their inverses, and the coefficient iterates are rational. Positive
semidefiniteness of a rational symmetric matrix is decidable by
successive rational Schur complements: pivot on a positive diagonal;
a zero diagonal in a positive semidefinite matrix must have zero
row, which can be tested exactly and removed. A negative diagonal,
or a zero diagonal with a nonzero row, rejects. The dimension
decreases at each step. Strict invertibility in (9.9) is secured
by the checked lower bound $S_f\ge\lambda I$. These are tests of
known rational numbers, never of the unknown source Gram rank.

The radical bounds in (9.4), (9.13) and (9.17) have rational squared
arguments. Bisection with outward rounding returns upper rational
bounds at any requested absolute precision. If each local residual
is rounded upwards by at most $\omega$, (9.17) increases by at
most $H\omega$, since all $\kappa_j\le1$. Thus precision
$\omega\le\tau/(H+1)$ pays a declared total arithmetic allowance
$\tau$ for a query. Exact rational coefficient iterates introduce
no additional roundoff; implementations using rounded iterates would
have to add their own normed recurrence errors to (9.17).

The full-counter acquisition route retains

$$
O\bigl(4^{T+1}\log(N+1)+T\bigr)
\quad\text{bits}
\tag{9.29}
$$

for the counters and a $T+1$-label buffer. Prefix marginalization
and extraction of (9.7) can be bounded by
$O(T4^{T+1}+q^2T)$ rational or integer operations after the
stream has been counted; a direct buffer route costs
$O((N+T)(T+1))$ elementary symbol operations. No claim of optimal
counter retention is needed. After extraction only five symmetric
blocks, the two finite maps, the metric, the packet and the desired
history marginals need be retained; raw past labels can be discarded
for these particular outputs.

More explicitly, let $B_0$ bound the bit lengths of a common
denominator and all integer numerators for the finite matrices in
(9.9), the measured blocks and the rational radii. It can be chosen
of order

$$
b+\ell+\log(q+1)+\log(N+4^T)
 +\text{the total bit length of }(t,\lambda,D_0^-,D_N^-).
\tag{9.30}
$$

The shared denominator $Z+4^T$ in (9.2), a dyadic denominator for
the rounded entries, and the denominators of $t,\lambda$ suffice
to see this. Exact elimination uses $O(q^3)$ arithmetic operations.
Integer determinant/minor bounds give an encoding for each fitted
map with a common denominator and numerators of at most
$F=O(q(B_0+\log(q+1)))$ bits. Fraction-free elimination and
rational order tests therefore have finite polynomial bit cost in
$q,B_0$; their retention is $O(q^2F)$ bits.

A query of $H$ prefixes or letters uses $O(Hq^2)$ rational
operations, including its local quadratic residual evaluations.
With common-denominator arithmetic its coefficient bit lengths are
$O((H+1)(F+\log(q+1)))$, and its workspace beyond the retained
blocks is $O(q(H+1)(F+\log(q+1)))$ bits, plus the chosen radical
precision. The elementary integer operations and bisections have
polynomial bit cost in these displayed quantities. Arbitrarily long
reuse is consequently not a fixed-bit memory assertion, even when
the retained coordinate count $q$ stays fixed.

The complete bill also includes the construction or validation cost
$C_{\rm cap}$ of (9.3) from the specified original numerical names,
and the physical acquisition of $N+T$ labels through time
$(N+T+1)d$. No rate for $C_{\rm cap}$ or for finding an adequate
$N$ is obtained merely from positivity of $d_r$. Known valid
certificates at a given $N$ make (9.4) finite. From the numerical
services of [R, §11], refining absolute error enclosures eventually
produces positive lower certificates because each $d_r>0$.
Searching $N$ with progressively accurate certificates can meet
any fixed positive failure target and fixed $t,T$: the supplied
fact $d_{1/(Nd)}\to1$ makes $\overline V\to0$ when those lower
certificates are chosen to approach one. This is termination for
each fixed original member, without a uniform sample bound over
the coefficient family. A finite observed radius or conditional
guard can still fail to be useful.

### 9.6. What accuracy growth does and does not imply

**Proposition 9.7 (finite task recovery without a rank oracle).**
Fix the original source, a finite dictionary $S$ and finitely many
queries from Theorem 9.5. Write $E=\operatorname{ran}V$. Consider
packets and precision choices along which

$$
\lambda\longrightarrow0,\qquad
\delta/\lambda\longrightarrow0,\qquad \epsilon\longrightarrow0,
\tag{9.31}
$$

on their common good event. Let $G^\dagger$ denote the Moore--Penrose
inverse only for the following mathematical limit, not as an
observer input. Then

$$
A_y\longrightarrow G^\dagger B_y,\qquad
VA_ya\longrightarrow\Pi_SR_yVa
\quad(y=B,3).
\tag{9.32}
$$

For fixed coefficient vectors the unrounded $r_y$ in (9.13)
converges to the actual projection leakage
$\|(I-\Pi_S)R_yVa\|_m$. More generally this statement holds
along convergent coefficient vectors. Thus a fixed frame does not
lose its ambient error by merely increasing the record length.

For finite-task recovery impose the following sufficient condition
on each of the finitely many query trajectories: every intermediate
source vector belongs to $E$, and at a $C_0$ or $C_1$ step with
input $z$, both component images $R_Bz,R_3z$ belong to $E$.
Then the error certificates (9.21)--(9.24) tend to zero under
(9.31) and vanishing arithmetic allowances. Conditional certificates
also tend to zero for each of their fixed histories once $e_p\to0$.
Such histories have strictly positive probability by Theorem 3.3.
This is a condition on the specified finite trajectories, not an
assumed invariant finite hidden model.

For the singleton dictionary $S=(\varnothing)$ the limiting squared
one-step sample-time leakage is strictly positive and equals

$$
16\left(p(BB3)-\frac{p(B3)^2}{p(3)}\right)>0.
\tag{9.34}
$$

Thus even in this actual original source, confidence refinement
alone cannot turn its smallest retained marked line into a closed
sample-time carrier.

*Proof.* If $a\in\ker G$, then $Va=0$ and $B_ya=0$.
Symmetry therefore gives $\operatorname{ran}B_y\subseteq
(\ker G)^\perp$. On this finite-dimensional complement the
positive eigenvalues of $G$ have a positive minimum, unless the
complement is zero, in which case the assertion is immediate.
This minimum is used to prove a limit, not supplied or tested by
the observer.

Compare (9.9) with
$A_y^0=(G+\lambda I)^{-1}B_y$. For the fixed dictionary,
$A_y^0$ stays bounded and tends to $G^\dagger B_y$ by this
orthogonal decomposition. The matrix difference identity gives

$$
A_y-A_y^0
 =S_f^{-1}\bigl[(L_y-B_y)
                    +(G+\lambda I-S_f)A_y^0\bigr].
\tag{9.33}
$$

Here $\|S_f^{-1}\|\le\lambda^{-1}$,
$\|L_y-B_y\|\le4\delta$, and
$\|G+\lambda I-S_f\|\le6\delta$. Equation (9.31)
proves the first limit. The normal equations, or the ordinary
Hilbert projection theorem, identify
$VG^\dagger B_ya=\Pi_SR_yVa$, proving the second.
Equation (9.19), entry convergence and coefficient convergence
show that the square-root expression in (9.13) tends to the
projection leakage. Its other cap tends to $2\|Va\|_m$,
which is at least that leakage. This proves the residual claim,
including exactly degenerate frames.

The same limit holds for the fixed linear combinations (9.15).
If all intermediate source vectors of a query belong to $E$,
successive projected actions equal those original vectors.
Induction in the finite coefficient recurrences gives convergent
coefficients with zero limiting ambient residual on every queried
step. Equations (9.17) and (9.21) then tend to zero. The stated
component condition at a $0$ or $1$ step ensures that both terms
in (9.16) vanish. A dictionary containing the finitely many $3,B$
words in the two-prefix expansions of all query trajectories always
supplies this sufficient condition. Finally the denominators in
(9.27) tend to their fixed positive original probabilities.

For the singleton, the squared projection leakage is
$D_B-B_B^2/G$, yielding (9.34) by (9.7). It is positive because
$v_\varnothing$ and $Pv_\varnothing$ are independent. Indeed
$v_\varnothing=\sqrt c\,P^{1/2}g_d$; applying $P^{1/2}$
to a dependence would give a dependence of $g_{2d}$ and
$Pg_{2d}$, contrary to the original heat-orbit independence
used in [MEM, Theorem 3.1]. Also $p(3)>0$ by Theorem 3.3.
$\square$

Cancellation between two nonzero component leakages alone need not
make the conservative sum (9.16) vanish. For a pure sample-time
query there is only the $R_B$ path, so this distinction disappears.

**Definition 9.8 (joint growth and the remaining infinite task).**
For a predeclared countable family of packets, assign failure
allowances $\alpha_s$ with $\sum_s\alpha_s\le\alpha_*$,
and make (9.4) at most $\alpha_s$ for each packet before using
its record. A union bound gives one event of probability at least
$1-\alpha_*$ on which all their conclusions hold. The records may
be nested initial segments of the same trajectory. Stopping at a
successful displayed error bound or selecting a finite query from
these packets is valid on that event; repeatedly trying unbudgeted
fixed-$N$ certificates is not the same confidence statement.

For each fixed dictionary, the sampler supplies $e_p\to0$ when
$t\to0$, $K_T/N\to0$ and $Z/N\to c>0$. The last fact is
the original one-marker ergodic limit [R, Theorem 8.2], and does
not require knowing $c$ numerically. One can therefore refine
record and rounding precision, and choose $\lambda$, to attain
(9.31) for a fixed task using the additional capacity services.
No exact lower frame eigenvalue is needed to evaluate the finite
certificates. The preceding limit proof supplies no uniform rate
as that eigenvalue approaches zero.

The dictionary, the finite query menu, and the query lengths may grow.
For any such sequence, sufficient checkable accuracy conditions are
that the displayed accumulated residual $E_H$, the metric term in
(9.21), and the chosen arithmetic allowances tend to zero after the
normalizations of the declared output. For conditional tests, their
sum with $e_p$ divided by the guarded observed denominator must
also tend to zero. Shrinking word error alone does not imply these
conditions when $q,\ell,H$ or the rarity of histories grows.
In particular (9.8) carries an explicit $4^{2\ell+2}$
amplification, (9.29) an exponential counter bill, and repeated
sample-time use can accumulate nonvanishing leakage.

Theorem 2.2 ensures that increasing $3,B$ dictionaries have dense
marked span. For any fixed finite trajectory its required prefix
vectors can be included, and Proposition 9.7 then gives finite-task
convergence. For example, if the chosen starting words have length
at most $\ell_0$ and there are at most $H$ applications, retaining
all $3,B$ words through length $L=\ell_0+H$ suffices for those
trajectories. This blanket choice has $q=2^{L+1}-1$ and training
horizon $T=2L+3$, and pays the corresponding bill (9.29); it is
not a free growing-horizon limit. Density by itself gives neither a uniform frame
condition nor uniformly small leakage on a growing menu. Broader
quantitative recovery needs estimates controlling precisely these
task tails, coefficient/regularization costs, horizons and guarded
history probabilities, in addition to the acquisition schedule.

The actual source has infinite algebraic Hankel rank and countably
infinitely many exactly reachable predictive profiles, by
[original passive predictive memory, Theorems 3.1 and 5.1][MEM].
The finite carrier above is consequently an approximation with a
measured ambient residual. Neither (9.10) nor successful finite
tests turn it into a finite exact realization. There is no asserted
uniform all-history or all-future recovery, current-cut filter,
reconstruction of $\Omega$ or the exact $c$, bounded inverse heat,
source trace evaluation, full spatial multiplication algebra, or
parameter calibration. Those stronger interfaces in §§3--7 retain
their separate hypotheses and unpaid stability obligations.

### 9.7. Mathematical suppliers and the source-specific increment

**Definition 9.9 (correspondence and literature scope).** The
`repo-derived` addition is the finite composition (9.7)--(9.28):
actual dependent-record confidence produces a positive marked
carrier, its two source-bound prefixes, an ambient rather than
merely fitted residual, and joint certificates for original sample
time and specified conditional future events. Its finite precision
and access contracts are Definitions 9.1, 9.6 and 9.8. The sampler
of [R, §§8--9], its coefficient/clock capacity service in §11,
and the exact marked geometry of Theorem 2.2 are reused, not
additional results claimed here. The source-resolvent supremum
and separation results in [R, §13] do not replace the unchanged
heat calibration by a resolvent readout. The present bridge does
not need that substitution or a numerical name of the sharp
normalizer.

The mature dictionary/Galerkin shape is `literature-attested` in
Williams--Kevrekidis--Rowley [EDMD, §§2.2--2.3]. Their observation
interface uses state-observable snapshot pairs; no such snapshots
are available here. Equations (9.7) and (9.19) give the original
word substitute for the needed inner products and whole-source
norm, while (9.5) supplies the appropriate dependent-record error.
The finite positive-form, diagonal regularization, projection and
triangle-inequality steps are established tools inside this
source-specific result, with no general-theorem priority claim.

The existing D5 source [PRE], including its private
`stateError_step_bound` and `weightedResidual_succ`, supplies
the residual-recursion and output-bound pattern. Its public
`stateError_le_residual_sum` and `outputError_le_residual_sum`
concern supplied continuous linear dynamics, projection and lift.
Here $V$, $R_y$, $A_y$ instantiate the lift/intertwining role;
the varying-letter recurrence is displayed in (9.20). That library
does not acquire $D_y$ or bind its residual to this original
passive record. [NoisyHoKalmanRecovery, `run_noisy_recovery`][NHK]
and [HoKalmanPredictionBudget][HKB] instead require a true finite
matrix realization of the declared order; their finite-rank
contract is not instantiated by this source. The predictive
factorization [PRED] and positive-conditioning result [PCOND]
likewise preserve their complete-law premises; they do not supply
a normalized finite fitted future law from (9.24).

At the pinned Mathlib revision of §8, the standard positive-form
and Hilbert projection ingredients are in
`Mathlib.LinearAlgebra.Matrix.PosDef` and
`Mathlib.Analysis.InnerProductSpace.Projection.Minimal`, including
`exists_norm_eq_iInf_of_complete_subspace`. These support the
finite algebra and the mathematical projection used in Proposition
9.7, without a rank oracle or a quantitative smallest-eigenvalue
input. The statements in this section are mathematical prose;
no new Lean verification is asserted.

[MEM]: RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_PASSIVE_PREDICTIVE_MEMORY.md
[PRE]: ../../../D5/S3/Observer/Hankel/ProjectedRealizationError.lean
[NHK]: ../../../D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.lean
[HKB]: ../../../D5/S3/Observer/Hankel/HoKalmanPredictionBudget.lean
[PCOND]: ../../../D5/S3/ObserverMemory/PredictionFactors/PositiveConditioningPredictionStability.lean
[EDMD]: https://arxiv.org/pdf/1408.4408v1

## 追加锚（本行以下为增补区）

## 10. Finite constant initialization and unmarked continuation

### 10.1. A confidence enclosure for the original constant

**Definition 10.1 (the same-record marker certificate).** Retain
Definitions 9.1--9.8 and the unchanged source of Assumption 1.1.
Thus $a,\eta,d>0$, the unit-source field, the full conservative
endpoint $H$ with $A=\rho C$, the distinct killed/Friedrichs endpoint
$F$, the normalized positive $h$, the $e$-start, first read at $2d$,
subsequent gaps $d$, the four original emissions, every permitted
Borel representative, and the original clock are all fixed. No new
read, stationary preparation, reset, or capacity experiment is
introduced. Use one of the independently preselected packets of
Definition 9.1 with $N\ge1$ and put

$$
 \widehat c=\frac ZN,\qquad
 c_-=[\widehat c-t]_+,\qquad
 c_+=[\widehat c+t]_{[0,1]},
 \tag{10.1}
$$

where $[x]_+=\max\{0,x\}$ and
$[x]_{[0,1]}=\min\{1,\max\{0,x\}\}$.
The number $\widehat c$ is a statistic of this record, not a new
source constant. If $N=0$, or if $\widehat c\le t$, the packet
returns an inconclusive normalization branch.

Let $\Delta$ be the full-source frequency discrepancy used in the
proof of (9.5), so that

$$
 \Delta=\sum_{v\in\mathcal L^T}
 \left|\frac{A(3v)}N-cp(v)\right|.
 \tag{10.2}
$$

Write $\mathcal E$ for the same $\Delta\le t$ capacity event
underlying (9.5). Since
$\sum_vp(v)=1$ and $\sum_vA(3v)/N=Z/N$, this gives

$$
 \mathcal E\Longrightarrow c\in[c_-,c_+].
 \tag{10.3}
$$

This is a finite confidence enclosure for the original $c$ on the
same event that supplies (9.5); it is not a claim of a sharp or exact
numerical value.

For an integer $n\ge0$ with $2n+1\le T$, define

$$
 \widehat s_n=4^{2n}\widehat p(B^{2n}3),\qquad
 \eta_n=4^{2n}e_p,\qquad
 \rho_n=\sqrt{\max\{0,\widehat s_n+\eta_n-c_-\}}.
 \tag{10.4}
$$

The marked identity (2.5) gives the exact source quantity

$$
 s_n:=\|P^nv_*\|_m^2
      =4^{2n}p(B^{2n}3),\qquad v_*:=v_\varnothing=U[\varnothing].
 \tag{10.5}
$$

Consequently, on $\mathcal E$,
$|\widehat s_n-s_n|\le\eta_n$. Theorem 2.3 gives
$U\Omega=1$, $\|\Omega\|=1$ and
$\langle\Omega,v_*\rangle=\sqrt c$. Since
$P1=1$ (equivalently $\widehat P\Omega=\Omega$), (10.5) therefore
has the exact geometric
identity

$$
 s_n-c=\|P^nv_*-\sqrt c\,\Omega\|^2
       =\|P^nv_*-\sqrt c\,1\|_m^2.
 \tag{10.6}
$$

The quantity $\rho_n$ is thus an observable upper radius for the
heat-averaged distance to the source constant; no spectral gap or
mixing rate is used.

**Theorem 10.2 (a finite carrier vector for the constant).** Use the
finite maps and residuals of Definitions 9.2--9.4. Starting with the
empty-word coordinate $e_*$, set

$$
 a^{(0)}=e_*,\qquad a^{(j+1)}=A_Ba^{(j)},\qquad a_n=a^{(n)},
 \tag{10.7}
$$

and compute $E_n^B$ from (9.17) with $O_j=R_B$ and
$\widetilde O_j=A_B$. If $\widehat c>t$, define

$$
 \bar a_n=\frac{a_n}{\sqrt{\widehat c}},\qquad
 r_{\mathbf1}(n)=
 \frac{E_n^B+\rho_n}{\sqrt{\widehat c}}+\frac{t}{\widehat c}.
 \tag{10.8}
$$

On $\mathcal E$,

$$
 \|V\bar a_n-1\|_m\le r_{\mathbf1}(n).
 \tag{10.9}
$$

The vector $V\bar a_n$ is a finite source-bound carrier vector. It
is not an actual stationary preparation.

*Proof.* Theorem 9.4 and (10.7) give
$\|Va_n-P^nv_*\|_m\le E_n^B$. Equations (10.4)--(10.6) give
$\|P^nv_*-\sqrt c\,1\|_m\le\rho_n$. Divide these two bounds by
$\sqrt{\widehat c}$. Finally, (10.3) implies

$$
 \left|\frac{\sqrt c}{\sqrt{\widehat c}}-1\right|
 =\frac{|c-\widehat c|}
 {\sqrt{\widehat c}(\sqrt c+\sqrt{\widehat c})}
 \le\frac{t}{\widehat c}.
$$

The triangle inequality proves (10.9). The argument uses the same
event as (9.5), so no confidence factor is multiplied for the
normalization. $\square$

### 10.2. A finite unmarked continuation consumer

**Definition 10.3 (unmarked menu and its fixed readout).** Let
$\mathcal M\subset\mathcal L^*$ be a declared finite menu, with the
empty word allowed, and write $w=w_1\cdots w_h$. Let $C_z,F_z$ be
the source and finite letter maps in (9.15), and put

$$
 \Phi_w=C_3C_{w_1}\cdots C_{w_h},\qquad
 \widetilde\Phi_w=F_3F_{w_1}\cdots F_{w_h}.
 \tag{10.10}
$$

The residual $E_w$ is the value of (9.17) for the reverse application
sequence

$$
 C_{w_h},\ldots,C_{w_1},C_3
 \quad\hbox{and}\quad
 F_{w_h},\ldots,F_{w_1},F_3,
 \tag{10.11}
$$

started at $\bar a_n$; its final finite vector is
$b_w=\widetilde\Phi_w\bar a_n$. Put

$$
 \kappa_f=6\delta+\lambda,\qquad
 \nu_w=\|C_3\|\prod_{j=1}^h\|C_{w_j}\|
 \le\frac14\prod_{j=1}^h\kappa_{w_j},
 \tag{10.12}
$$

where $\kappa_z$ is the row bound in (9.15), and define the finite
outward-rounded radius

$$
 \rho_w^{\rm out}=
 \|\bar a_n\|_fE_w
 +\frac{\kappa_f}{2}
   \bigl(\|\bar a_n\|_2^2+\|b_w\|_2^2\bigr)
 +\nu_w\bigl(2r_{\mathbf1}(n)+r_{\mathbf1}(n)^2\bigr)+\tau_w.
 \tag{10.13}
$$

Here $\tau_w\ge0$ is a predeclared allowance for outward rounding
of the displayed radicals and finite arithmetic. All quantities in
(10.13) are obtained from the packet matrices and rational
coefficient vectors; no rank, path, or terminal-marker oracle is
used.

**Theorem 10.4 (finite unmarked word readout).** Assume
$N\ge1$, $\widehat c>t$, and that the order tests of Definition 9.2
pass. For every $w\in\mathcal M$, define

$$
 \widehat q_w=\bar a_n^{\mathsf T}S_f b_w,\qquad
 \widehat p_w=\left[\frac{\widehat q_w}{\widehat c}\right]_{[0,1]},\qquad
 R_w=\min\left\{1,\frac{\rho_w^{\rm out}+t}{\widehat c}\right\}.
 \tag{10.14}
$$

Then, on $\mathcal E$,

$$
 |\widehat p_w-p(w)|\le R_w.
 \tag{10.15}
$$

The word $w$ is unmarked: it may end in any of $0,1,3,B$ and no
terminal $3$ is appended to the menu. The fixed $C_3$ in (10.10) is
the canonical readout in Theorems 3.1 and 3.2, not an additional
chronological emission.

For a finite collection of fixed histories and continuations, use the
same estimate for $h$ and $hw$. If $\widehat p_h>R_h$, then

$$
 \widehat r_{h,w}=\left[\frac{\widehat p_{hw}}{\widehat p_h}\right]_{[0,1]},\qquad
 |\widehat r_{h,w}-p(hw)/p(h)|
 \le\min\left\{1,\frac{R_{hw}+R_h}{\widehat p_h}\right\}.
 \tag{10.16}
$$

If the displayed denominator guard fails, the conditional output is
inconclusive. Theorem 3.3 supplies $p(h)>0$ for every fixed finite
history, but it supplies no uniform lower bound for a growing or rare
history.

*Proof.* Theorem 3.1 and (3.2) identify

$$
 q_w:=\langle1,\Phi_w1\rangle_m=c\,p(w).
 \tag{10.17}
$$

By (9.17), (10.11) and the residual induction,
$\|\Phi_wV\bar a_n-Vb_w\|_m\le E_w$. The metric defect in (9.11),
polarized, gives for any $a,b$

$$
 \left|a^{\mathsf T}S_fb-\langle Va,Vb\rangle_m\right|
 \le\frac{\kappa_f}{2}(\|a\|_2^2+\|b\|_2^2).
 \tag{10.18}
$$

Since $\|V\bar a_n\|_m\le\|\bar a_n\|_f$, (10.13), before its
outward allowance, bounds the difference between $\widehat q_w$ and
$\langle V\bar a_n,\Phi_wV\bar a_n\rangle_m$. Writing
$V\bar a_n=1+\xi$ and using $\|\Phi_w\|\le\nu_w$ bounds the latter
quantity's difference from $q_w$ by
$\nu_w(2\|\xi\|+\|\xi\|^2)$. Equation (10.9) gives (10.13), hence
$|\widehat q_w-q_w|\le\rho_w^{\rm out}$ on $\mathcal E$.
Because $0\le p(w)\le1$ and $|c-\widehat c|\le t$,

$$
 \left|\frac{\widehat q_w}{\widehat c}-p(w)\right|
 \le\frac{\rho_w^{\rm out}+t}{\widehat c}.
$$

Clipping proves (10.15). If $\widehat p_h>R_h$, the same event gives
$p(h)>0$ and $|p(h)-\widehat p_h|\le R_h$; the elementary ratio
inequality used in (9.28) proves (10.16). $\square$

The readout in (10.14) is a finite consumer of the initialized
carrier and of the existing letter/residual transport. It uses the
original chronological word law through (10.17), while its requested
menu contains no marked terminal. It does not make the finite maps a
normalized all-future law: different menu products may be clipped
individually, and no fitted multiplication algebra or current-cut
filter is inferred.

### 10.3. Stopping and the paid finite task

**Proposition 10.5 (predeclared finite stopping).** Fix one original
source, a finite menu $\mathcal M$, finitely many fixed history pairs
$(h,w)$, and positive tolerances $\tau_{\mathbf1},\tau_p$.
Choose a countable predeclared packet schedule with failure allowances
$\alpha_s$ satisfying $\sum_s\alpha_s\le\alpha_*$, nested initial
records, and a dovetailed list of finite choices

$$
 n_s,\ L_s,\ S_s=\{3,B\}^{\le L_s},\quad
 T_s=2L_s+3,\quad N_s,\ t_s,\ D_{0,s}^-,D_{N,s}^-,
 \lambda_s,\ \zeta_s,\ \tau_{w,s}.
 \tag{10.19}
$$

The list is required to contain every finite $n,L$ and every positive
rational refinement of the displayed error and confidence allowances.
Each packet's defect certificates are chosen so that its (9.4) failure
bound is at most $\alpha_s$, as required by Definition 9.8.
At stage $s$, stop at the first packet for which the order tests pass,
$\widehat c_s>t_s$, $r_{\mathbf1}(n_s)\le\tau_{\mathbf1}$,
$R_{w,s}\le\tau_p$ for every requested menu word, and all guards in
(10.16) pass.

For every fixed source and the declared finite task, this stopping
rule terminates on the common event
$\bigcap_s\mathcal E_s$, whose probability is at least
$1-\alpha_*$. The assertion is source- and menu-specific; it gives
no uniform rate over sources, menus, rare histories, or future
normalizations.

*Proof.* Theorem 2.3 and the spectral convergence in Theorem 3.2 give
$P^nv_*\to\sqrt c\,1$ in the source norm. Hence some finite $n$
makes the exact term in (10.6) smaller than any prescribed positive
part of $\tau_{\mathbf1}$. For that finite $n$ and menu, expand
each $C_0$ and $C_1$ into the $C_B,C_3$ words in (2.9). A finite
$L$ therefore contains every intermediate source vector in the
corresponding finite trajectories. Proposition 9.7 then supplies
finite packet precision choices with vanishing metric and residual
allowances; Definition 9.8 supplies the same-record confidence union
and the capacity refinement $e_p\to0$ for this fixed task. The
dovetailed list (10.19) contains such a finite choice. Since $c>0$
and every fixed history has positive probability by Theorem 3.3,
sufficiently refined packets also satisfy the positive denominator and
history guards. At that stage (10.9), (10.15) and (10.16) meet the
declared tolerances, so the first successful stage is finite. $\square$

The stage bill retains the original access costs. It acquires exactly
$N_s+T_s$ labels, ending at time $(N_s+T_s+1)d$, keeps the
$4^{T_s+1}$ full counters and the buffer of Definition 9.1, and pays
the validated capacity construction or certification cost
$C_{\rm cap}$. It also pays the existing fit and query bounds in
(9.29), with $q_s=2^{L_s+1}-1$. The new finite work consists of
$n_s$ applications of $A_B$, the reverse applications in (10.11) for
the declared menu, their quadratic residual evaluations, outward
radical bounds, and retention of the $q_s$-vectors and finite outputs.
Its arithmetic cost is $O((n_s+\sum_{w\in\mathcal M}|w|)q_s^2)$
apart from the already charged matrix fits and counter extraction.
No independent path samples, selected emissions, extra read/preparation
port, or sharp $N d$ oracle is charged or assumed.

## 11. Scope, suppliers and the positive-state boundary

**Definition 11.1 (literature and source status).** The
repo-derived result is the finite composition of (10.1)--(10.18):
the existing dependent-record confidence event supplies a reliable
interval for the original $c$, (2.5) and Theorem 2.3 turn it into a
measurable heat-averaged constant-vector radius, and (9.14)--(9.20)
transport that vector through a finite unmarked menu. Theorem 3.1 and
(3.2) supply the fixed marker readout; Theorem 3.3 supplies the
fixed-history positivity used only by the guards. The source sampler,
capacity defects and full-source chronology are reused from [R,
Definitions 8.1 and 8.3, Theorem 8.2, Proposition 8.5 and
Proposition 8.6], not re-proved or replaced. Strong convergence of the
positive self-adjoint semigroup is the spectral supplier already used
in [T, §3.1]; finite positive-form and residual transport are the
existing tools recorded in §9.7. No general priority claim is made.

The finite vector in (10.9) is a certified mathematical element of
$L^2(G,m)$ relative to the original constant $1$. It is not a
stationary preparation, a positive state for each actual history, or
a physical operation on the source. The supplied DEV C128375--378
direct chronological positive-state binding result states that such a
binding on the same prefix multiplication exists exactly when the
prediction vector is constant and excludes the empty and all-finite-$B$
histories. The present certificate cannot overturn that source
obstruction.

This unit does not claim a physical multiplication algebra, a
current-cut filter, a normalized all-future fitted law, a full C139
backend, old $D$ or Jordan data, an actual $A$, a joint/reference
interface, physical instruments, exact global sharp calibration, a
complete quantum origin, or a uniform source/menu/rare-history rate.
It also does not supply an exact numerical $c$, a sharp $N d$ oracle,
a stationary reset, or growing all-future normalization. All claims
remain conditional on the original full-source endpoint and capacity
contract, with no Lean or executable mathematical verification
asserted.

## 追加锚（本行以下为增补区）

## 12. Actual local-energy multiplication from the exact word tuple

**Definition 12.1 (intrinsic inputs and the local source dictionary).**
Retain Assumptions 1.1–1.3, the full complex endpoint (1.3), the
original clock and the exact tuple (3.1). For local regularity use the
same-source suppliers [S, (120.5)–(120.8), (122.9)]: on
$M=G\setminus\{e\}$ the density $h^2$ is smooth and strictly positive,
and the original divergence expression is

$$
\begin{gathered}
K_{\rm loc}u=-h^{-2}\operatorname{div}
                    (h^2\mathsf A\nabla u),\\
\langle\mathsf A\zeta,\zeta\rangle
 =a\left[\zeta_x^2+(\zeta_y+x\zeta_w)^2+\zeta_z^2\right]
       +\eta\zeta_w^2.
\end{gathered}
\tag{12.1}
$$

These are assertions about the actual $K=J_h^{-1}HJ_h$ and its
local expression, not a choice of another self-adjoint extension.
Positive-time smoothing gives a unique smooth representative of
$b=g_d$ on $M$: indeed $g_d=T_{d/2}g_{d/2}$ and the cited estimates
apply to $g_{d/2}\in L^2(m)$. Essential boundedness and full local
support of $m$ imply that this representative is bounded on $M$.
Put, only in the source dictionary,

$$
\begin{gathered}
\mathcal D=C_c^\infty(M;\mathbb C),\qquad
\mathfrak a(v,u)=a\sum_{j=1}^3(X_jv)(X_ju)
                          +\eta(\partial_wv)(\partial_wu),\\
E=\mathfrak a(b,b),\qquad \gamma=dE,\qquad
r=(1+\gamma)^{-1}.
\end{gathered}
\tag{12.2}
$$

The bilinear notation $\mathfrak a$ has no complex conjugation;
$b$ is real and $E\ge0$. Both $E$ and $\gamma$ are smooth and
finite on $M$, without any asserted global boundedness or
integrability. Values at $e$ may be assigned arbitrarily when
taking $m$-classes. Permitted Borel repairs of the actual emission
do not change $M_b$, its spectral phases, or the unique smooth
representative of its class on $M$.

The recovered inputs for the construction below are just

$$
\mathsf B=N_3/c,\qquad \Lambda=-\log\widehat P,\qquad
U\mathsf B U^{-1}=M_b|_{\mathcal O},\quad
U\Lambda U^{-1}=dK|_{\mathcal O},
\tag{12.3}
$$

with $c$ recovered by Theorem 2.3. Coordinates, $h$, derivatives
and compactly supported functions in (12.1)–(12.2) are proof
objects in the source realization, not additional inputs.

**Theorem 12.2 (source-bound phase limit and the actual energy
domain).** For each integer $n\ge1$ define the nonnegative
self-adjoint operator and its bounded resolvent

$$
\begin{gathered}
V_n=e^{in\mathsf B},\qquad
\mathsf L_n=n^{-2}V_n^*\Lambda V_n,\qquad
D(\mathsf L_n)=V_n^*D(\Lambda),\\
\mathsf R_n=(\mathsf L_n+I)^{-1}
 =V_n^*q_n(\widehat P)V_n,\\
q_n(x)=\frac{n^2}{n^2-\log x}\quad(0<x\le1),\qquad q_n(0)=0.
\end{gathered}
\tag{12.4}
$$

The exact tuple determines the strong limit

$$
\mathsf R=\operatorname*{s-lim}_{n\to\infty}\mathsf R_n,\qquad
U\mathsf R U^{-1}=M_r|_{\mathcal O}.
\tag{12.5}
$$

It is a positive contraction with zero kernel and dense range.
Consequently it determines a unique nonnegative self-adjoint operator

$$
\begin{gathered}
\mathsf G=\mathsf R^{-1}-I,\qquad
D(\mathsf G)=\operatorname{Ran}\mathsf R,\\
UD(\mathsf G)=
 \{u\in\mathcal O:\gamma u\in L^2(m)\},\qquad
U\mathsf G U^{-1}u=\gamma u.
\end{gathered}
\tag{12.6}
$$

In particular $\mathcal O$ reduces the maximal source multiplication
operator $M_\gamma$. This is reduction with its maximal restricted
domain, rather than an unqualified compression of an unbounded
expression. The associated closed nonnegative form is

$$
\begin{gathered}
UD(\mathsf G^{1/2})=
 \{u\in\mathcal O:\sqrt\gamma\,u\in L^2(m)\},\\
\langle\mathsf G^{1/2}v,\mathsf G^{1/2}w\rangle
       =\int_G\gamma\,\overline{Uv}\,Uw\,dm.
\end{gathered}
\tag{12.7}
$$

The operator $\mathsf G$ is in sample-step units: it is multiplication
by $dE$. With an independently calibrated numerical $d$, $\mathsf G/d$
is multiplication by the original physical energy $E$. No new clock
or physical phase control is assumed.

*Proof.* Work first on the full $\mathcal H=L^2(m)$, before making
any restriction to $\mathcal O$. Every $\psi\in\mathcal D$ belongs
to $D(K)$. In fact $h\psi\in\mathcal D_0\subset D(H)$, since
$h$ is smooth off $e$ and the support is compact there. Ground-state
conjugation identifies $K\psi$ with (12.1). The same statement holds
for $e^{inb}\psi\in\mathcal D$ for every finite $n$. Thus the full
operators

$$
\begin{gathered}
L_n=n^{-2}M_{e^{-inb}}(dK)M_{e^{inb}},\\
D(L_n)=M_{e^{-inb}}D(K),\qquad L_n\ge0
\end{gathered}
\tag{12.8}
$$

are self-adjoint, and $\mathcal D\subset D(L_n)$ for all $n$.
This specifies the entire moving domain; no global invariance of
$D(K)$ under $M_b$ or its phases is used.

The local product rule from (12.1), on exactly these compact
punctured vectors, gives

$$
L_n\psi=\gamma\psi+
 \frac{id}{n}\left[(K_{\rm loc}b)\psi
                              -2\mathfrak a(b,\psi)\right]
                  +\frac d{n^2}K\psi.
\tag{12.9}
$$

Indeed $K_{\rm loc}(e^{inb})=e^{inb}(inK_{\rm loc}b+n^2E)$.
This fixes both the sign and the absence of a factor $1/2$ in
(12.2). Every coefficient and derivative in the remainder of
(12.9) is bounded on the fixed support of $\psi$. Therefore

$$
\|L_n\psi-M_\gamma\psi\|_2\longrightarrow0
                  \quad(\psi\in\mathcal D).
\tag{12.10}
$$

Here $K_{\rm loc}b$ is only a local differential expression.
Equation (12.9) asserts neither $b\in D(K)$ nor global integrability
of $K_{\rm loc}b$.

We verify the relevant limit domain. The maximal real multiplier

$$
D(M_\gamma)=\{u\in L^2(m):\gamma u\in L^2(m)\}
\tag{12.11}
$$

is nonnegative and self-adjoint. Its resolvents are the bounded
multipliers $(\gamma-z)^{-1}$ for nonreal $z$, and
$(M_\gamma+I)^{-1}=M_r$. Its graph norm is the $L^2$ norm for
the measure $(1+\gamma^2)m$. On $M$ this measure has smooth
strictly positive locally finite density. Exhaust $M$ by compact
subsets and apply smooth compact cutoffs to a function in (12.11).
Dominated convergence in this weighted norm gives graph convergence.
On each resulting compact neighborhood the weighted norm is
equivalent to ordinary Lebesgue $L^2$, so compactly supported
mollification gives approximation by $\mathcal D$. The missing
point has zero $m$-measure. Hence $\mathcal D$ is an operator core
for $M_\gamma$. These cutoffs prove density in the source space;
they supply no observer cutoff operation.

For completeness, the core-to-resolvent argument in this instance
uses only bounded resolvents. For $\psi\in\mathcal D$,

$$
\begin{aligned}
&(L_n+I)^{-1}(M_\gamma+I)\psi-\psi\\
&\hspace{2em}=(L_n+I)^{-1}(M_\gamma-L_n)\psi
                      \longrightarrow0.
\end{aligned}
\tag{12.12}
$$

Both $(L_n+I)^{-1}$ and $(M_\gamma+I)^{-1}$ have norm at most
one. The set $(M_\gamma+I)\mathcal D$ is dense: approximate
$(M_\gamma+I)^{-1}v$ in the graph norm for any $v\in\mathcal H$.
Equation (12.12) and that uniform bound prove

$$
\operatorname*{s-lim}_{n\to\infty}(L_n+I)^{-1}=M_r
                          \quad\text{on }\mathcal H.
\tag{12.13}
$$

This is the usual core criterion for strong resolvent convergence,
[T, §6.6, Lemma 6.36], here with its shifted-resolvent proof and
actual multiplication core supplied. In particular
$L_n\to M_\gamma$ in strong resolvent topology. No operator-norm
convergence or uniform error bound is asserted. Crucially,
$\mathcal D$ is a core for the *limit multiplier*; it has not
been declared a core for the full, non-Friedrichs $K$.

Let $Q$ be the orthogonal projection onto $\mathcal O$. Theorem 2.2
shows that $Q$ commutes with the bounded $P$ and $M_b$.
The injective spectral inverse in Theorem 3.2 then shows that it
reduces $K$ and preserves its domain. It also commutes with
$M_{e^{inb}}$. Thus it preserves the full domains in (12.8),
commutes with every $(L_n+I)^{-1}$, and by (12.13) commutes with
$M_r$. This proves reduction before any limit is restricted.

Since $0<r\le1$ almost everywhere, $M_r$ has zero kernel. Its
restriction to the reducing subspace $\mathcal O$ is self-adjoint
and injective, and so has dense range there. Moreover

$$
\operatorname{Ran}(M_r|_{\mathcal O})
       =D(M_\gamma)\cap\mathcal O.
\tag{12.14}
$$

For one inclusion, if $u=M_rv$ with $v\in\mathcal O$, then
$\gamma u=(1-r)v\in\mathcal O$. Conversely, if
$u\in D(M_\gamma)\cap\mathcal O$, apply $Q$ to
$u=M_r(M_\gamma+I)u$. Injectivity gives
$Q(M_\gamma+I)u=(M_\gamma+I)u$, proving the other inclusion.
This also shows that $Q$ preserves (12.11) and commutes with
$M_\gamma$ there.

Restrict (12.8) and (12.13) to $\mathcal O$ and transport by $U$.
The unitary and spectral identities in (12.3) give precisely
(12.4)–(12.6). In (12.4), $q_n$ is bounded and continuous on
$[0,1]$, so the displayed resolvent formula uses no unbounded
inverse heat on an arbitrary vector.

More explicitly, if $E_{\mathsf R}$ is the spectral resolution
of $\mathsf R$ and
$\sigma_v^{\mathsf R}(A)=\langle v,E_{\mathsf R}(A)v\rangle$,
the inverse domain is

$$
D(\mathsf G)=
 \left\{v:\int_{(0,1]}(s^{-1}-1)^2
                                 d\sigma_v^{\mathsf R}(s)<\infty\right\}.
\tag{12.15}
$$

There is no zero spectral atom, although zero may lie in the
spectrum. This condition is equivalent to square integrability
of $s^{-1}$, hence to $v\in\operatorname{Ran}\mathsf R$.
It gives the maximal domain in (12.6), with a closed self-adjoint
operator, not merely a closable formal commutator. The square-root
calculus gives (12.7); closedness follows from self-adjointness.
Finally (12.9) identifies the multiplier with $dE$ for the
original $dK$, proving the clock assertion. $\square$

## 13. The generated commutative algebra and a strict measured factor

**Theorem 13.1 (only the actual generated spatial algebra).** Let
$\mathsf R,\mathsf G$ be the operators of Theorem 12.2. The bounded
self-adjoint operators $\mathsf B,\mathsf R$ commute. Their generated
von Neumann algebra and its constant-cyclic subspace are

$$
\mathcal A=W^*(\mathsf B,\mathsf R)
                \subset\mathcal B(\widehat{\mathcal H}),\qquad
\mathcal H_{\rm rel}=\overline{\mathcal A\Omega}.
\tag{13.1}
$$

The exact word law determines a joint probability measure $\nu$ on
$\mathbb R\times[0,\infty)$ by

$$
\nu(A\times D)=
 \langle\Omega,\mathbf1_A(\mathsf B)
                    \mathbf1_D(\mathsf G)\Omega\rangle.
\tag{13.2}
$$

It is exactly the original joint measure

$$
\nu=(b,\gamma)_*m.
\tag{13.3}
$$

For bounded Borel $\varphi$ write
$\Phi_\varphi=\varphi(\mathsf B,\mathsf G)$. Joint Borel calculus
is defined here by the bounded commuting pair
$(\mathsf B,\mathsf R)$ and the inverse $\gamma=r^{-1}-1$ on
$r>0$. Then

$$
\begin{gathered}
U\Phi_\varphi U^{-1}=M_{\varphi(b,\gamma)}|_{\mathcal O},\\
\mathcal A=\{\Phi_\varphi:\varphi\in L^\infty(\nu)\},\qquad
\|\Phi_\varphi\|=\|\varphi\|_{L^\infty(\nu)}.
\end{gathered}
\tag{13.4}
$$

There is a unitary, determined by the exact tuple,

$$
\begin{gathered}
W:L^2(\nu)\longrightarrow\mathcal H_{\rm rel},\qquad
W\varphi=\Phi_\varphi\Omega
                 \quad(\varphi\text{ bounded}),\\
UW\varphi=\varphi(b,\gamma),\qquad
U\mathcal H_{\rm rel}
     =L^2\!\left(\overline{\sigma(b,\gamma)}^{\,m},m\right)
                   \subseteq\mathcal O.
\end{gathered}
\tag{13.5}
$$

Thus $\mathcal A$ has the faithful cyclic measured realization
$L^\infty(\nu)$ on $\mathcal H_{\rm rel}$, with reference measure
the original $m$, pushed forward as in (13.3). There is no assertion
that $\mathcal H_{\rm rel}=\widehat{\mathcal H}$.

*Proof.* In the source realization (12.3) and (12.5) are the
restrictions of the commuting actual multipliers $M_b,M_r$.
They therefore commute, and bounded Borel functional calculus
on the reducing sector gives

$$
U\mathbf1_A(\mathsf B)\mathbf1_D(\mathsf G)U^{-1}
             =M_{\mathbf1_{\{b\in A,\,\gamma\in D\}}}|_{\mathcal O}.
\tag{13.6}
$$

Together with $U\Omega=1$, this proves (13.2)–(13.3), first on
rectangles and then on their generated Borel sigma algebra. The
measure is a probability since $m(G)=1$. The point $r=0$ has zero
spectral projection, so the Borel inverse causes no missing part.

Simple functions of rectangles and bounded monotone limits show
that every bounded Borel $\varphi(b,\gamma)$ acts as in (13.4) and
belongs to the generated algebra. Conversely the bounded joint
spectral calculus of two commuting self-adjoint operators is a
von Neumann algebra and is the one they generate. This is the
classical spectral-algebra intermediate, not an assumed spatial
algebra. Its actual-source identification is (13.6).

No joint null set hidden from $\Omega$ changes that conclusion.
If $\Phi_\varphi\Omega=0$, then $\int|\varphi|^2d\nu=0$, so
$M_{\varphi(b,\gamma)}=0$ on the full source space, hence
$\Phi_\varphi=0$. Thus $\Omega$ is separating for $\mathcal A$.
Also

$$
\|\Phi_\varphi\Omega\|^2=\int|\varphi|^2d\nu,
\tag{13.7}
$$

which extends $W$ isometrically from bounded functions. They are
dense in $L^2(\nu)$, and their images have closure
$\mathcal H_{\rm rel}$ by (13.1), giving surjectivity. On this
cyclic subspace $\Phi_\varphi$ is ordinary multiplication by
$\varphi$, so its norm is at least $\|\varphi\|_\infty$;
the source multiplier bound gives the reverse inequality.
Every completed-measurable bounded class has a Borel version
modulo $\nu$, proving the $L^\infty$ formulation of (13.4).

Finally the pullbacks of bounded Borel functions of $(b,\gamma)$
are dense in the right side of (13.5): simple functions and
completion modulo $m$ suffice, or equivalently the measurable
factorization for the standard Borel map $(b,\gamma)$ does so.
All these pullbacks belong to $\mathcal O$ because their
multipliers reduce it and $1\in\mathcal O$. This proves (13.5).
The spectral and cyclic representation steps are the usual
multiplication representation [T, §§3.1–3.2]; they apply to this
proved algebra and its cyclic subspace, without imposing spatial
multiplier cyclicity on the whole visible sector. $\square$

**Theorem 13.2 (strict original-source gain beyond the readout
algebra).** In addition retain the analytic-source hypotheses of
[original energy fibre geometry, Assumption 1.1 and Definition
2.1][EF]. For every original finite $a,\eta,d>0$, the measured
factor (13.3) has the joint absolute continuity asserted in
[EF, Theorem 4.1], and

$$
\begin{gathered}
W^*(\mathsf B)\subsetneq\mathcal A,\\
\mathcal H_b:=\overline{W^*(\mathsf B)\Omega}
                  \subsetneq\mathcal H_{\rm rel},\\
\overline{\sigma(b)}^{\,m}
                  \subsetneq\overline{\sigma(b,\gamma)}^{\,m}.
\end{gathered}
\tag{13.8}
$$

Let $E_b$ denote the orthogonal projection in
$\widehat{\mathcal H}$ onto $\mathcal H_b$. A strictly positive
intrinsic witness is

$$
\begin{aligned}
\Delta_p&=\|(I-E_b)\mathsf R\Omega\|^2\\
 &=\int_G\left|r-\mathbb E_m[r\mid
                      \overline{\sigma(b)}^{\,m}]\right|^2dm>0.
\end{aligned}
\tag{13.9}
$$

No numerical value or effective lower bound for $\Delta_p$ is
part of this assertion.

*Proof.* First check the source correspondence needed for the
cited fibre theorem. Its $G,e,\mu,X_j$ are (1.1), with the same
unit-source $\Gamma$, positive normalized $h$, full complex
$A=\rho C$ endpoint and $m=h^2\mu$ of (1.2)–(1.4).
Its $b$ is the smooth representative of this same $g_d$; the
positive-time smoothing in Definition 12.1 is exactly its
Definition 2.1. Its Definition 1.2 sets
$E=a\sum_j(X_jb)^2+\eta(\partial_wb)^2$ and $\gamma=dE$,
which agree with (12.2), including the original sampling interval
and no factor $1/2$. Theorem 12.2 has identified the recovered
operator with this very $M_\gamma$ on its maximal observable
domain before any fibre result is invoked. Finally (13.3) uses
the same normalized measure, rather than the source-start law at
one read time or a product replacement. Hence [EF, Theorems 3.1
and 4.1] apply to exactly this pair and give

$$
\nu\ll\operatorname{Leb}_2,\qquad
m\{\gamma=F(b)\}=0
                  \quad\text{for every Borel }F:\mathbb R\to\mathbb R.
\tag{13.10}
$$

In particular $\gamma$ is not measurable for the completed
$\sigma(b)$, by the completed-sigma conclusion of that theorem.
Since $r>0$ and $\gamma=r^{-1}-1$ almost everywhere, $r$ is not
measurable for that completed sigma algebra either. It is bounded,
so its $L^2$ class lies in the right side of (13.5) but outside
$L^2(\overline{\sigma(b)}^{\,m},m)$. Under $U$, the latter space
is exactly $\mathcal H_b$, by the same cyclic calculation with
$\mathsf B$ alone. Thus $\mathsf R\Omega\notin\mathcal H_b$,
proving the strict cyclic inclusion and (13.9). In particular
$\mathsf R\notin W^*(\mathsf B)$, proving the strict algebra
inclusion. The strict sigma inclusion is (13.10)'s cited
completed-measurability consequence. This proof uses actual-source
fibre separation, rather than inferring strictness from $E\ne0$
or nonconstancy of a multiplier. $\square$

[EF]: RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_ENERGY_FIBRE_GEOMETRY.md

## 14. The same source path and the remaining autonomous-factor condition

**Theorem 14.1 (the original positive-time joint factor laws).**
Use the hypotheses of Theorem 12.2, without needing the extra
analytic hypotheses for strictness. In sample-step units let
$0<r_1<\cdots<r_k$ and let $\varphi_1,\ldots,\varphi_k$ be
bounded Borel functions on $\mathbb R\times[0,\infty)$.
Use $\gamma_r$ for the entrance vector already defined in (4.1),
distinguished from the spatial scalar $\gamma$ of (12.2). Then

$$
\begin{aligned}
&\mathbb E_e\!\left[\prod_{j=1}^k
      \varphi_j\bigl(b(Z_{r_jd}),\gamma(Z_{r_jd})\bigr)\right]\\
&\quad=\left\langle\gamma_{r_1},
       \Phi_{\varphi_1}\widehat P^{\,r_2-r_1}
       \Phi_{\varphi_2}\cdots
       \widehat P^{\,r_k-r_{k-1}}
       \Phi_{\varphi_k}\Omega\right\rangle.
\end{aligned}
\tag{14.1}
$$

For $k=1$ the right side means
$\langle\gamma_{r_1},\Phi_{\varphi_1}\Omega\rangle$.
Consequently the exact original word law determines all these
finite-dimensional factor distributions at named sample-step times.
For every $r>0$ their one-time distribution $\nu_r$ is equivalent
to the reference measure $\nu$ of (13.3), with

$$
\nu_r(D)=\langle\gamma_r,\Phi_{\mathbf1_D}\Omega\rangle
      =\int_G g_{rd}\,\mathbf1_{\{(b,\gamma)\in D\}}\,dm.
\tag{14.2}
$$

There is also a joint correspondence with the unchanged noisy
labels. For $y_0,\ldots,y_\ell\in\mathcal L$ and bounded Borel
$\varphi_0,\ldots,\varphi_\ell$, write
$D_j=\Phi_{\varphi_j}N_{y_j}$. Then

$$
\begin{aligned}
&\mathbb E_e\!\left[\prod_{j=0}^{\ell}
   \varphi_j\bigl(b(X_j),\gamma(X_j)\bigr)
                 \mathbf1_{\{Y_j=y_j\}}\right]\\
&\hspace{3em}=\langle\gamma_2,
          D_0\widehat P D_1\cdots\widehat P D_\ell\Omega\rangle,
\qquad X_j=Z_{(j+2)d}.
\end{aligned}
\tag{14.3}
$$

These are laws of functions of the same original source path.
They do not assert that their values on a realized path can be
read from its realized label sequence.

*Proof.* Theorem 4.1 gives $U\gamma_r=g_{rd}$, with its exact
inverse spectral domain even when $0<r<1$. At the first positive
time $r_1d$ the actual source law has density $g_{r_1d}$ with
respect to $m$. Apply the original Markov property forward at
the finitely many times, conditioning from the last one backwards.
This gives the bounded-function expression

$$
\left\langle g_{r_1d},
 M_{\varphi_1(b,\gamma)}T_{(r_2-r_1)d}
 M_{\varphi_2(b,\gamma)}\cdots
 T_{(r_k-r_{k-1})d}M_{\varphi_k(b,\gamma)}1\right\rangle_m.
\tag{14.4}
$$

Every multiplier in (14.4) reduces $\mathcal O$ by (13.4),
and every heat factor reduces it by Theorem 3.2. All products
are bounded; all vectors beginning with $1$ remain in
$\mathcal O$. Transporting by $U$ proves (14.1). Taking
indicators proves (14.2), and $g_{rd}>0$ almost everywhere proves
both directions of absolute continuity with respect to $\nu$.

At the original read times, condition on the one undisturbed
path. Fresh conditional reading noise turns the product of the
label indicators in (14.3) into $\prod_j f_{y_j}(X_j)$.
Each emission is a bounded function of $b$ by (1.6), so the
result is (14.4) with first time $2d$, gaps $d$, and multipliers
$M_{\varphi_j(b,\gamma)f_{y_j}}$. Their transports are exactly
$D_j$, proving (14.3). Null-repaired versions cause no ambiguity:
at each of these finitely many positive deterministic times
the source law is absolutely continuous with respect to $m$.
The same argument handles countably many original read times
by a countable union of null events. No value at time zero or
at $e$ is required for the energy variable. $\square$

**Definition 14.2 (scope of the recovered relation factor).**
The recoverable spatial relation here is the measured map
$x\mapsto(b(x),\gamma(x))$ through its generated completed sigma
algebra, joint law and multiplication on the cyclic subspace
(13.5). It is strictly finer than the one-readout measured factor
under Theorem 13.2's analytic-source premises. It is not an
identification of the full raw coordinates or of all
rotation-invariant functions. Both $b$ and $\gamma$ are invariant
under the original rotations: the rotations preserve the full
source, $b$ and the principal metric in (12.1). They are also
invariant under the original $z$ reflection. Thus the invisible
directions and the same-source path obstruction of §6 remain.

An autonomous heat factor on (13.5) would additionally require
$T_tL^2(\overline{\sigma(b,\gamma)}^{\,m},m)$ to lie in that
same subspace for every $t\ge0$. If $E_{\rm rel}$ denotes the
orthogonal projection onto $\mathcal H_{\rm rel}$, this condition
is equivalent, by self-adjointness and the injective time
calculus, to

$$
E_{\rm rel}\widehat P=\widehat P E_{\rm rel}.
\tag{14.5}
$$

No such commutation is proved by (12.5) or (13.5). Those
statements show that the whole visible sector reduces heat
and the recovered multipliers, not that its smaller multiplier
cyclic subspace reduces heat. Formula (14.1) is valid without
(14.5), because its intermediate vectors are allowed to range
over the whole visible sector. A compression to
$\mathcal H_{\rm rel}$ alone therefore supplies no asserted
Markov semigroup or local generator on the two-variable factor.

The intrinsic construction (12.4)–(12.6) is set-theoretic exact
recovery. It gives no effective modulus for its strong limit,
no finite-record energy evaluator and no new emission or physical
instrument. In particular the finite constant-vector and finite
unmarked-menu conclusions of §§9–11 retain exactly their own
capacity and same-event premises; they do not control the
unbounded-domain or large-$n$ limit in §12. The recovered
nonnegative form (12.7) is a multiplication form, distinct from
the diffusion form (1.4). Membership of its functions in
$D(K^{1/2})$, recursive energy closure, full spatial multiplier
cyclicity and general mutual recovery of space, time,
boundary and memory are not supplied by this two-variable factor.

**Definition 14.3 (mathematical attribution).** The source-specific
deduction in §§12–14 is repo-derived: it is the composition of the original marked
tuple and calibrated $b$ from §§2–4 with the actual full-domain
phase calculation (12.8)–(12.13), the reduction (12.14), and the
same-source measured and path correspondences (13.3), (14.1) and
(14.3). The strictness premise is exactly [EF, Theorems 3.1 and
4.1], consumed with the dictionary in the proof of Theorem 13.2.
It is not re-proved or replaced by a generic nonzero-energy test.
These are conditional mathematical deductions from the cited
analytic-source suppliers.

Maximal real multiplication operators, their graph cores and
spectral representations are literature-attested intermediates [T,
§§2.2, 3.1–3.2]; the common-limit-core resolvent criterion is
[T, §6.6, Lemma 6.36]. Their use here is within the source-specific
proofs. The local commutator mechanism is already present in
[S, §129.D], on actual compact punctured vectors. No global
boundedness of that commutator, no common global multiplication
domain for $K$, and no identification with unrelated FIB
$\alpha,\beta$ syntax is part of this deduction. The asserted
scope is ordinary conditional mathematics, with no additional
formal-verification or general priority assertion.

## 追加锚（本行以下为增补区）

## 15. Original B-conditioned futures, shifted records and coordinate moments

**Definition 15.1 (one source and three future laws).** Retain the
entire source of Assumption 1.1 and Definition 1.2, for every original
finite $a,\eta,d>0$ and every permitted Borel repair. In particular
$b=g_d$ as an $m$-class, $P=T_d$, $f_3=cb$, $f_B=1/4$, all four
labels, the $e$-start, $2d$ first read, $d$ spacing and original
independent conditional read noise are unchanged. Put

$$
\begin{gathered}
\mathsf Y=\mathcal L^{\mathbb N},\qquad
\mathscr Y=\bigotimes_{j\ge0}2^{\mathcal L},\qquad
(\theta y)_j=y_{j+1},\\
Q_0=\operatorname{Law}_{\mathbb P_e}((Y_j)_{j\ge0}),\qquad
H_r=\{Y_0\cdots Y_{r-1}=B^r\},\qquad H_0=\mathsf Y,\\
R_B^r(E)=\mathbb P_e((Y_{r+j})_{j\ge0}\in E\mid H_r),\qquad
Q_r=(\theta^r)_*Q_0,\qquad r\in\mathbb Z_{\ge0},\ E\in\mathscr Y.
\end{gathered}
\tag{15.1}
$$

Let $Q_*$ be the stationary mathematical comparison $Q_m$ of
[R, Definition 8.1], made with initial hidden law $m$, the same
transition kernel $P$ and the same emissions. Thus
$Q_*([w])=\langle1,F_w\rangle_m=\langle1,C_w1\rangle_m$.
This defines a comparison measure, not an additional preparation.
Set $\operatorname{TV}(\mu,\nu)=\sup_{E\in\mathscr Y}|\mu(E)-\nu(E)|$.

Use the actual common future kernel $\mathcal K(x,E)$: starting at
hidden state $x$ at a read epoch, it emits the current label by $f$,
then repeats transition $P$ and the original read noise. The original
standard Borel state space and the iterated kernels give this kernel
on the complete product sigma algebra. Its cylinder values are
$\mathcal K(x,[w])=F_w(x)$ almost everywhere. The construction and
monotone-class extension are the common-kernel machinery of
[R, (8.11)]. Kernel versions on exceptional $m$-null sets do not
change any measure here. For a probability density $v$ relative to
$m$, write $\mathcal Q(v)(E)=\int v(x)\mathcal K(x,E)m(dx)$.

**Theorem 15.2 (the B-wait/shift correspondence with a source moment
bound).** Under Definition 15.1, on the whole $\mathscr Y$,

$$
\begin{gathered}
\mathbb P_e(H_r)=4^{-r},\qquad
R_B^r=Q_r=\mathcal Q(\varrho_r),\qquad
\varrho_r=P^{r+1}b=g_{(r+2)d},\qquad Q_*=\mathcal Q(1),\\
R_B^r([w])=4^rp(B^rw)
 =\sum_{u\in\mathcal L^r}p(uw)
 =\langle P^{r+1}b,F_w\rangle_m.
\end{gathered}
\tag{15.2}
$$

Here $\varrho_r$ is the actual next-read density at time $(r+2)d$.
It is distinct from the half-step representation vector
$z_{B^r}=P^{r+1/2}b$ in [C128, (376.6)][C128S]. Define

$$
 m_j=Q_0\{Y_j=3\},\qquad
 \Delta_r=m_r-m_{r+1},\qquad
 V_r=\operatorname{TV}(Q_r,Q_*).
 \tag{15.3}
$$

Then

$$
\begin{gathered}
m_j=c\langle b,P^{j+1}b\rangle_m,\qquad
m_j\downarrow c,\qquad m_j>c,\qquad \Delta_r>0,\\
\|\varrho_r-1\|_2^2=\frac{m_{2r+1}-c}{c},\\
0<m_r-c\le V_r\le
 \min\left\{1,\frac12\sqrt{\frac{m_{2r+1}-c}{c}}\right\},\qquad
V_{r+1}\le V_r,\qquad V_r\longrightarrow0.
\end{gathered}
\tag{15.4}
$$

In particular this is a bound for all measurable future events,
with no bound on the number of retained future coordinates.

*Proof.* Given the hidden path, the probability of the first $r$
labels all being $B$ is the constant $4^{-r}$. Fresh conditional
read noise makes that past event independent of the later labels
conditional on the path. For a finite cylinder of future hidden
states and future labels, integrating the past read factors therefore
gives $4^{-r}$ times its unconditional probability. Equality of
finite measures extends from these cylinders to the full joint
hidden/read product sigma algebra. Projecting to future labels and
dividing by $4^{-r}$ proves $R_B^r=Q_r$ on $\mathscr Y$. This
uses the constant original B emission and the actual common source;
it is stronger than equality of one-coordinate marginals.

The hidden state at the first reindexed future read is
$X_r=Z_{(r+2)d}$, with density $P^{r+1}b$. The Markov/read
contract gives the same $\mathcal K$ after that read epoch under
both laws. Integration proves the first line of (15.2). On cylinders,
$F_{B^rw}=4^{-r}P^rF_w$ and self-adjointness give its last
pairing. Partitioning by the first $r$ labels gives the sum in
(15.2). These are also the actual density updates of
[MEM, Theorem 2.1]; no fractional physical read is used.

In (15.2) take the first future event to be $\{y_0=3\}$ and
use $f_3=cb$. This proves the formula for $m_j$. For the finite
spectral measure $\sigma_b^K(A)=\langle b,\mathbf1_A(K)b\rangle_m$,
the constant component of $b$ is $1$, so

$$
\begin{aligned}
m_j-c&=c\int_{(0,\infty)}e^{-(j+1)d\lambda}\,d\sigma_b^K(\lambda),\\
\Delta_r&=c\int_{(0,\infty)}e^{-(r+1)d\lambda}
                    (1-e^{-d\lambda})\,d\sigma_b^K(\lambda).
\end{aligned}
\tag{15.5}
$$

The positive-energy mass is nonzero by the original-source
nonconstancy in Theorem 5.3, also used in [C128, (376.7)]. Thus
both integrals are strictly positive at every finite index. Bounded
convergence gives $m_j\to c$. Self-adjointness and conservation give

$$
\|P^{r+1}b-1\|_2^2
 =\langle b,P^{2r+2}b\rangle_m-1
 =(m_{2r+1}-c)/c.
\tag{15.6}
$$

For every $E\in\mathscr Y$, the common-kernel integral is

$$
 Q_r(E)-Q_*(E)
 =\int(\varrho_r-1)\mathcal K(x,E)m(dx).
 \tag{15.7}
$$

Since $0\le\mathcal K(x,E)\le1$ and $\int(\varrho_r-1)dm=0$,
its absolute value is at most $\tfrac12\|\varrho_r-1\|_1$.
Cauchy--Schwarz on the probability space $(G,m)$ and (15.6) give
the upper bound in (15.4). The event $\{y_0=3\}$ gives its lower
bound. Finally $Q_{r+1}=\theta_*Q_r$ and $\theta_*Q_*=Q_*$,
so taking preimages in the definition of TV gives monotonicity.
The upper bound tends to zero. The integral proof uses the original
complete future kernel; one-point marginal equality alone would
not justify any of these complete-future upper bounds. $\square$

[C128S]: AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md

## 16. One original finite packet certifying a square and every future event

**Definition 16.1 (coordinate events of the existing packet).**
Use exactly Definition 9.1 and Definition 10.1, with
$T=2\ell+3$ and the same marked-discrepancy event
$\mathcal E=\{\Delta\le t\}$ of (10.2). For $0\le j<T$ set

$$
 E_j^{(T)}=\{v\in\mathcal L^T:v_j=3\},\qquad
 \widehat m_j=\widehat\nu(E_j^{(T)})
 =\sum_{v:v_j=3}\frac{A(3v)+1}{Z+4^T}.
 \tag{16.1}
$$

These are marginals of the acquired length-$T$ original-law
estimate. They are not the raw label frequency, whose long-record
limit is the stationary marker mass $c$. Retain the same rational
$e_p$, $c_-=[Z/N-t]_+$ and $c_+$ of (9.4) and (10.1).
Choose an integer $r\ge0$ with $\ell\ge r$, so
$r+1<T$ and $2r+1<T$, and declare rational $0<\epsilon<1$.
Define the rational lower gap

$$
 L_r=\widehat m_r-\widehat m_{r+1}-2e_p.
 \tag{16.2}
$$

The declaration can be part of a predeclared packet family as in
Definition 9.8. Within one packet the TV event controls all its
coordinate events simultaneously, including a selection of $r$
from the finite allowed set.

**Theorem 16.2 (the source-specific dual certificate).** On the
same event $\mathcal E$ already used in §§9--10,

$$
 |\widehat m_j-m_j|\le e_p\quad(0\le j<T),\qquad
 c\in[c_-,c_+].
 \tag{16.3}
$$

Use the existing prefix algebra $\mathscr C_0$, functional
$\ell_{B^r}$, $D_0=I-P$ and $S=C_3$ of
[C128, Definitions 375.1 and (376.2)]. If $L_r>0$, the rational
coefficient $\tau=8L_r$ gives the specified self-adjoint square

$$
 A=D_0-\tau S\in\mathscr C_0,\qquad
 \ell_{B^r}(A^*A)\le-4L_r^2<0.
 \tag{16.4}
$$

If the additional rational guards

$$
 c_->0,\qquad
 \widehat m_{2r+1}+e_p\le c_-(1+4\epsilon^2)
 \tag{16.5}
$$

hold, then simultaneously

$$
 \sup_{E\in\mathscr Y}|R_B^r(E)-Q_*(E)|=V_r\le\epsilon.
 \tag{16.6}
$$

The probability, under the original acquisition law, of a packet
passing these guards while either conclusion is false is at most
its original failure allowance $\alpha$. No second confidence
event is introduced.

*Proof.* Equation (9.5) is a whole length-$T$ TV bound. Apply
it directly to each $E_j^{(T)}$, whose true probability is $m_j$.
This proves all coordinate inequalities on that single event;
there is no sum of individual word errors. Equation (10.3) gives
the same-event enclosure of $c$.

By (15.2), the existing gap
$R_r(3)-4R_r(B3)$ of [C128, (376.2)] equals
$m_r-m_{r+1}=\Delta_r$. Thus (16.3) gives $\Delta_r\ge L_r$.
The existing arbitrary-coefficient expansion [C128, (376.8)] is

$$
 \ell_{B^r}((D_0-\tau S)^2)
 =-\tau\Delta_r+\tau^2a_r,\qquad a_r=R_B^r([33]).
 \tag{16.7}
$$

Both original $3$ emissions are bounded by $1/4$, so conditioning
on the source path gives $0<a_r\le1/16$. With $\tau=8L_r>0$,
the right side of (16.7) is at most
$-8L_r^2+64L_r^2/16=-4L_r^2$. This is the old square obstruction
with a certified rational coefficient; its existence and algebraic
expansion are reused, not new positive-state or square theorems.
No estimate of $a_r$ or optimization over squares is required.

For (16.6), (16.3)--(16.5) imply

$$
 m_{2r+1}\le\widehat m_{2r+1}+e_p
 \le c_-(1+4\epsilon^2)\le c(1+4\epsilon^2).
 \tag{16.8}
$$

Apply (15.4). Only rational inequalities are needed for this guard;
no numerical square root is needed. Both conclusions hold on
$\mathcal E$, whose complement has original probability at most
$\alpha$. A failed guard is inconclusive. In particular failure of
$L_r>0$ does not overturn the exact finite-$r$ obstruction of
[C128, Theorem 376.1]. $\square$

**Proposition 16.3 (tail comparison and the retained original past).**
For fixed $r$, confidence in Theorem 16.2 concerns the specified
mathematical conditional law $R_B^r$, whether or not the acquired
record begins with $B^r$. Conditional on the acquired record actually
satisfying $H_r$, its failure probability is bounded by
$\min\{1,4^r\alpha\}$, rather than by $\alpha$ in general.
For a predeclared family with total allowance $\alpha_*$ the same
statement holds with $\alpha_*$ for each fixed $H_r$.

Let $\overline Q_r=Q_0(\,\cdot\mid H_r)$ on the original indexed
record space $\mathsf Y$, retaining the first $r$ coordinates.
Then

$$
 \operatorname{TV}(Q_0,\overline Q_r)=1-4^{-r}.
 \tag{16.9}
$$

Let $J_r(y)=B^ry$ concatenate that fixed past with a future
sequence. Although $\overline Q_r=(J_r)_*R_B^r$ and
$\operatorname{TV}(\overline Q_r,(J_r)_*Q_*)=V_r\to0$,

$$
 \operatorname{TV}(Q_0,(J_r)_*Q_*)\ge1-4^{-r}.
 \tag{16.10}
$$

The same lower obstruction holds on every finite original record
containing its first $r$ coordinates. Hence discarding and
reindexing the past is essential to (16.6).

*Proof.* For any packet-failure event $F$ with
$Q_0(F)\le\alpha$, division by $Q_0(H_r)=4^{-r}$ gives the
conditional failure bound; the union event gives its family version.
The Radon--Nikodym derivative of $\overline Q_r$ relative to
$Q_0$ is $4^r\mathbf1_{H_r}$, whose half $L^1(Q_0)$ distance
from $1$ is $1-4^{-r}$. The finite-record version has the same
derivative for any length at least $r$. The concatenation map
identifies the future space measurably with $H_r$, so it preserves
TV between the two concatenated future laws. Finally $(J_r)_*Q_*$
assigns probability one to $H_r$, while $Q_0(H_r)=4^{-r}$;
this event proves (16.10). None of these conditional mathematical
measures supplies a forced B outcome or a change of preparation.
$\square$

## 17. Fixed-source stopping, paid horizons and mathematical scope

**Assumption 17.1 (predeclared refinement with the original services).**
Fix one original source and a declared rational $0<\epsilon<1$.
Retain the original coefficient/clock and capacity-certificate
services of Definition 9.1 and [R, §11]. Declare a countable
schedule of pairs $(r_s,k_s)$ such that for every fixed integer
$r\ge0$, stages with $r_s=r$ occur at arbitrarily large refinement
levels $k_s$. Set $\ell_s=r_s$, $T_s=2r_s+3$, and declare positive
rational failure allowances $\beta_s$ with
$\sum_s\beta_s\le\alpha_*<1$. Each packet is chosen without
consulting its label record. Its validated defects make its (9.4)
failure bound at most $\beta_s$.

Require, along the stages for every fixed $r$,

$$
 t_s\longrightarrow0,\qquad 4^{T_s}/N_s\longrightarrow0.
 \tag{17.1}
$$

The initial record lengths $L_s^{\rm rec}=N_s+T_s$ are
nondecreasing. They are obtained by retaining and extending the
same original trajectory from $e$. Earlier labels needed for a
new longer-window count remain available through paid retention
and recounting; a later segment is not a fresh $e$-start.

Such numerical schedules are permitted by the original services:
choose the refinement targets for $t_s$ and $4^{T_s}/N_s$ first,
then enlarge $N_s$ and refine the validated defect enclosures until
the positive allowance $\beta_s$ is met. For each fixed finite
$T_s,t_s$, the facts $d_{1/(N_sd)}\to1$ and positivity of the
fixed defect in (9.3) supply finite termination, as in Definition
9.6. Increasing $N_s$ can also enforce the record-length constraint.
This uses the stated numerical services, not label-only access.

**Theorem 17.2 (finite stopping for both certificates).** Under
Assumption 17.1, stop at the first stage for which $L_{r_s}>0$
and both guards (16.5) hold. On the common event
$\mathcal E_*:=\bigcap_s\mathcal E_s$, this stage is finite and
its two conclusions (16.4) and (16.6) are valid. The common event
has original probability at least $1-\alpha_*$. The assertion
has no source-uniform sample or physical-time bound.

*Proof.* On every $\mathcal E_s$, (10.2) gives
$|Z_s/N_s-c|\le t_s$. Along a fixed $r$ subsequence, (17.1)
therefore yields

$$
\begin{gathered}
c_{-,s}\longrightarrow c>0,\qquad
e_{p,s}\le
 \min\left\{1,\frac{t_s+4^{T_s}/N_s}
                         {c-t_s+4^{T_s}/N_s}\right\}
 \longrightarrow0,\\
|\widehat m_{j,s}-m_j|\le e_{p,s}\quad(0\le j<T_s),
\end{gathered}
\tag{17.2}
$$

where the displayed fraction is used once $t_s<c$. By (15.4)
there is a finite fixed $r$ for which

$$
 \kappa:=c(1+4\epsilon^2)-m_{2r+1}>0.
 \tag{17.3}
$$

This strict slack in the sufficient bound is what the stopping
proof needs. At this same fixed $r$, $\Delta_r>0$. On its
refining subsequence, (16.3) gives
$L_r\ge\Delta_r-4e_{p,s}$, so the square guard eventually passes.
Also $c_{-,s}\ge c-2t_s$ and
$\widehat m_{2r+1,s}+e_{p,s}\le m_{2r+1}+2e_{p,s}$.
Thus $t_s<c/2$ and

$$
 2e_{p,s}+2t_s(1+4\epsilon^2)<\kappa
 \tag{17.4}
$$

suffice for both guards (16.5), and hold eventually at that fixed
$r$. Its successful stage has a finite index in the predeclared
schedule. The union bound gives $Q_0(\mathcal E_*)\ge1-\alpha_*$,
and Theorem 16.2 gives both conclusions there. Merely increasing
$r$ would not prove this stopping claim: $\Delta_r\to0$, so a
shrinking absolute gap still requires adequate fixed-$r$
refinement. $\square$

**Definition 17.3 (the full cost of the nested-record route).**
Every tested stage $s$ keeps the original $4^{T_s+1}$ integer
counters, a $T_s+1$ label buffer, and the packet's validated
certificate inputs. It uses the original $N_s+T_s$ initial labels
through read time $(N_s+T_s+1)d$, with counter/buffer storage

$$
 O\bigl(4^{T_s+1}\log_2(N_s+2)+T_s\bigr)
 \quad\text{bits},
 \tag{17.5}
$$

and pays $C_{{\rm cap},s}$ for constructing or validating its
capacity and clock inputs. These are the costs of Definitions 9.1
and 9.6. The coordinate numerators in (16.1) are sums from the
same marked row: a direct extraction of all coordinates costs
$O(T_s4^{T_s})$ integer additions, with a common denominator
$Z_s+4^{T_s}$. Each numerator is at most $Z_s+4^{T_s}$.
The finitely many rational guards and $\tau=8L_r$ have finite
integer-arithmetic cost in their displayed input bit lengths.
No fitted matrix or additional rare-prefix division is required
by this particular consumer; this statement does not remove any
cost incurred for other outputs of §§9--10.

If $s_*$ is the stopping stage, retaining all initial labels permits
recounting each tested horizon correctly and adds
$2L_{s_*}^{\rm rec}$ bits for the four-symbol record. A direct
recount at stage $s$ has
$O((N_s+T_s)(T_s+1))$ elementary symbol work, as in Definition
9.6. Total numerical work includes the sum of these recount,
extraction, guard and $C_{{\rm cap},s}$ expenses over every
$s\le s_*$. Peak workspace includes the retained record, current
full counters and buffer, and certificate/guard arithmetic; a
route retaining several histograms pays for each retained one.
The nested physical acquisition uses $L_{s_*}^{\rm rec}$ actual
labels and ends at $(L_{s_*}^{\rm rec}+1)d$; counts from earlier
stages do not create additional independent trajectories. If old
labels and adequate window information were discarded, these
initial longer-window histograms would require an additional
retention/recount service; shorter-horizon histograms alone do
not supply them. The certificate gives no decrease in total
resources, no Pareto dominance, and no source-uniform stopping
bound. In particular the unchanged full-counter cost is
exponential in the declared horizon.

**Definition 17.4 (source correspondence and limits).** The
source-specific deduction is the combination of (15.2),
(15.4), (16.3)--(16.8) and Theorem 17.2: coordinate events of
one original marked-law packet control the actual B-conditioned
reindexed complete future and certify the existing square
obstruction at the same specified finite history. Sections 9--11
supply the packet, same-event $c$ interval, finite-menu machinery
and costs; their rare B-prefix half-step moments are distinct from
the coordinate moments (16.1). Sections 12--14 recover energy
multiplication and richer factors from exact law; their exact-law
premise does not furnish this finite-record certificate.

The common hidden/read future kernel and its product-sigma
extension are reused from [R, (8.11)]. The actual density update,
fixed-word convergence and exact infinite predictive-memory
boundary are reused from [MEM, Theorems 2.1, 4.1 and 5.1]. The
same-prefix-multiplication boundary, strict finite B gap and
arbitrary-coefficient square expansion are reused from [C128,
§§375--378]. Its §§379--384 concern original label mass and
Jordan units, not the coordinate-event future-law interface.
[O, Definition 175.1 and Proposition 187.1] fixes the same
propagation $q=cb$, $g=Pb$, $Pq=cg$ and already excludes its
in-span exceptional ordered gap; that question remains settled.
[Synthesis, §§25.33--25.36][SYN15] concerns native89 finite-rate
and seam-output contracts, with different operations, states and
history quantifiers, and supplies no identification with this
passive diffusion.

Spectral convergence and bounded multiplier identities are the
mature tools of [T, §3.1], already used in [R, (8.9)]. Common
stochastic-kernel contraction is a mature intermediate here,
proved in the event integral (15.7); a related general treatment
is [Abate--Redig--Tkachev, arXiv:1311.3066v1, Proposition 2 and
Lemma 1][ART15], whose total-variation norm is twice the
probability-distance convention in Definition 15.1. No general
kernel, spectral or interval theorem is asserted as new, and no
global literature priority is claimed for this source application.

All statements retain every original finite history, all four
emissions and their original noise, every allowed Borel repair,
the same full endpoint and original acquisition clock. Conditional
laws and $Q_*$ are mathematical comparison objects. A negative
value in (16.4) is the failure of the specified algebraic positive
state binding, not a negative physical probability. The complete
future comparison is for the specified $B^r$ conditional suffix,
not all histories or the retained original past. It supplies
neither a finite exact all-history predictor, stationary physical
preparation, reset, copy, new port, source-free confidence,
complete quantum origin, nor a formal-verification claim.

[SYN15]: FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_SYNTHESIS.md
[ART15]: https://arxiv.org/abs/1311.3066v1

## 追加锚（本行以下为增补区）

## 18. Four original marker counts in place of a word table

**Definition 18.1 (the sparse chronological statistic).** Retain
Assumption 1.1 and Definition 1.2, for all their finite positive
$a,\eta,d$ and permitted repairs. In particular $H$ is the full
complex endpoint, $b=g_d$, $P=T_d$, and the actual initial hidden
read density is $Pb=g_{2d}$. Put $I_i=\mathbf1\{Y_i=3\}$.
For a fixed integer $r\ge0$, define the three positive lags

$$
 h_1=r+1,\qquad h_2=r+2,\qquad h_3=2r+2,
 \qquad \lambda_r=2r+2.
 \tag{18.1}
$$

For $N\ge1$ use exactly the initial chronological label segment
$Y_0,\ldots,Y_{N+\lambda_r-1}$ of the one original trajectory.
The four integer fields are

$$
 Z=\sum_{i=0}^{N-1}I_i,\qquad
 A_j=\sum_{i=0}^{N-1}I_i I_{i+h_j}\quad(1\le j\le3),
 \qquad z=Z/N,\quad a_j=A_j/N.
 \tag{18.2}
$$

Thus $0\le A_j\le Z\le N$. If $r=0$, $A_2=A_3$ and those two
fields may share one value. All intermediate labels are the original
four-label reads; the statistic subsequently uses their marker bits.
No conditioning, selected marker, restart, new read epoch or
independent trajectory is involved. In particular a marker at
index $i$ is an ordinary observed label, not a new source entrance.

Under the invariant mathematical comparison $Q_*$ of Definition
15.1 set $q=f_3=cb$ and, for positive integer $h$, set

$$
 \mu_h=\langle q,P^h q\rangle_m.
 \tag{18.3}
$$

This comparison is used only to calculate errors of (18.2) under
$Q_0$, the actual $e$-start law. It is not an available preparation.

**Definition 18.2 (the sparse numerical packet and its guards).**
In addition to $r,N$, declare an integer $v\ge1$, rational
$t>0$, $0<\epsilon<1$, and validated rational lower bounds

$$
 0<D_0^-\le d_{1/(4d)},\qquad
 0<D_v^-\le d_{1/(vd)},\qquad D_0^-,D_v^-\le1.
 \tag{18.4}
$$

Here $d_\xi$ is exactly the original full-source capacity divided
by $\xi$ in [R, Definition 9.1], not the killed capacity. These
are the same coefficient/clock and capacity services as Definition
9.1 and [R, §11]. Their construction, validation and encoding are
paid inputs. Neither a numerical supremum of $b$, a hidden
coordinate, a new clock nor a value of $c$ is supplied. The packet
is selected without consulting its label segment. Put

$$
 \begin{gathered}
 \overline V_{N,v}=
 \min\left\{\frac14,\frac{6v-3}{4N}
                   +6\frac{1-D_v^-}{D_v^-}\right\},\qquad
 \alpha_{N,v,t}=
 \min\left\{1,\frac2t\sqrt{\frac{\overline V_{N,v}}{D_0^-}}\right\},\\
 c_-=[z-t]_+,\qquad c_+=\min\{1,z+t\},\\
 (\widetilde m_r,\widetilde m_{r+1},\widetilde m_{2r+1})
 =\begin{cases}(A_1/Z,A_2/Z,A_3/Z),&Z>0,\\(0,0,0),&Z=0,\end{cases}\\
 e=\begin{cases}\min\{1,2Nt/Z\},&Z>0,\\1,&Z=0,\end{cases}
 \qquad
 L=\widetilde m_r-\widetilde m_{r+1}-2e.
 \end{gathered}
 \tag{18.5}
$$

The repeated coordinate at $r=0$ has a single meaning since its
counts agree. There are no pseudocounts and no word histogram.
For a declared rational failure allowance $0<\beta<1$, the wholly
rational input condition

$$
 4\overline V_{N,v}\le\beta^2t^2D_0^-
 \tag{18.6}
$$

suffices for $\alpha_{N,v,t}\le\beta$. The output guards are

$$
 L>0,\qquad c_->0,\qquad
 \widetilde m_{2r+1}+e\le c_-(1+4\epsilon^2).
 \tag{18.7}
$$

## 19. Sparse simultaneous confidence for the original dual consumer

**Theorem 19.1 (lag-uniform original acquisition of the two
certificates).** Under Definitions 18.1–18.2, the exact original
source correspondence is

$$
 \mathbb E_*z=c,\qquad
 \mathbb E_*a_j=\mu_{h_j}=c\,m_{h_j-1}\quad(1\le j\le3).
 \tag{19.1}
$$

There is a simultaneous event, defined directly from the four raw
counts,

$$
 \mathcal F_{N,r,t}=
 \left\{|z-c|\le t,\quad
       |a_j-cm_{h_j-1}|\le t\ (1\le j\le3)\right\},
 \qquad Q_0(\mathcal F_{N,r,t})\ge1-\alpha_{N,v,t}.
 \tag{19.2}
$$

On this event $c\in[c_-,c_+]$ and

$$
 |\widetilde m_j-m_j|\le e
 \quad(j\in\{r,r+1,2r+1\}).
 \tag{19.3}
$$

If (18.7) passes, set $\tau=8L$ and use the same $D_0=I-P$,
$S=C_3$, prefix algebra $\mathscr C_0$ and functional $\ell_{B^r}$
as in Theorem 16.2. On $\mathcal F_{N,r,t}$ the two conclusions are
exactly

$$
 \begin{gathered}
 A=D_0-\tau S\in\mathscr C_0,\qquad
 \ell_{B^r}(A^*A)\le-4L^2<0,\\
 \sup_{E\in\mathscr Y}|R_B^r(E)-Q_*(E)|\le\epsilon.
 \end{gathered}
 \tag{19.4}
$$

Consequently the original probability of passing the guards while
either conclusion is false is at most $\alpha_{N,v,t}$. The bound
(18.5) contains no lag $h_j$, word-span or word-cardinality factor.
The record length and retention still depend on $\lambda_r$.
This is confidence for a new sparse event (19.2), not an assertion
that the full-word event of Definition 9.1 was already sparse.

*Proof.* First, $\int q\,dm=c$ since $\int b\,dm=1$.
Stationarity of the comparison hidden chain and conditional
independence of distinct original read noises give
$\mathbb E_*I_iI_{i+h}=\langle q,P^h q\rangle_m$ for $h\ge1$.
The actual source identity of (15.4), with index $h-1$, gives

$$
 \langle q,P^h q\rangle_m
 =c^2\langle b,P^h b\rangle_m=c\,m_{h-1}.
 \tag{19.5}
$$

This proves (19.1). The extra read after the first marker is why
coordinate $m_j$ uses lag $j+1$, rather than lag $j$. The hidden
initial density in $m_j$ remains $Pb$, not $b$ or $1$.

We next bound the variances of these actual pair counts, including
interlaced pairs. Write

$$
 \theta_n=\Theta(1/(nd)),\qquad u=q-c,\qquad
 \gamma_n=\langle u,P^n u\rangle_m\quad(n\ge1).
 \tag{19.6}
$$

Here $\Theta$ is the source defect of [R, (9.1)]. Its monotonicity
needed below follows from its original killed-resolvent definition:
if $\nu$ is the spectral measure of $F$ at $h$ in raw $L^2(\mu)$,
then

$$
 1-d_\xi=\int_{[0,\infty)}\frac{\xi}{x+\xi}\,d\nu(x).
 \tag{19.7}
$$

The right side is nondecreasing in $\xi$. Since $0<d_\xi<1$,
$\Theta(\xi)=(1-d_\xi)/d_\xi$ is nondecreasing as well.
Thus $\theta_n$ is nonincreasing in $n$, and $\theta_n\to0$.
This uses the killed operator only inside the existing full-source
rank-one defect formula; it does not change the process endpoint.

The positive-form Cauchy–Schwarz argument in [R, (9.3), (9.15)]
implies, for centered real $f,g$ with sup norms at most one,

$$
 |\langle f,P^n g\rangle_m|\le\theta_n.
 \tag{19.8}
$$

Indeed $P^n=e^{-ndK}$ is positive self-adjoint, and each diagonal
positive form is at most $\theta_n$ by [R, (9.3)]. In particular
$0\le\gamma_n\le\theta_n$, and $\gamma_n$ is nonincreasing by
spectral calculus. All functions used below are bounded real
$m$-classes, so permitted null-set repairs do not affect the
pairings or actual positive-time read laws.

Fix any positive lag $h$ and let $J_i=I_iI_{i+h}$.
For $k>h$, reversing the first pair by self-adjointness gives

$$
 \operatorname{Cov}_*(J_0,J_k)=
 \langle qP^h q-\mu_h,
         P^{k-h}(qP^h q-\mu_h)\rangle_m,
 \qquad
 |\operatorname{Cov}_*(J_0,J_k)|\le\theta_{k-h}.
 \tag{19.9}
$$

The centered factor has sup norm at most one since
$0\le qP^h q\le1$. For $0<k<h$, all four read epochs are distinct
and chronological conditioning gives instead

$$
 \mathbb E_*(J_0J_k)
 =\langle qP^k q,P^{h-k}(qP^k q)\rangle_m.
 \tag{19.10}
$$

This identity includes the interlacing $0,k,h,h+k$; treating these
pairs as disjoint windows would not give it. Put
$w_k=qP^k u$ and $v_k=qP^{h-k}q$. Expanding
$qP^kq=cq+w_k$ inside (19.10) yields

$$
 \mathbb E_*(J_0J_k)
 =c^4+c^2\gamma_{h-k}
       +2c\langle v_k,P^k u\rangle_m
       +\langle w_k,P^{h-k}w_k\rangle_m.
 \tag{19.11}
$$

Since $u$ is centered, $v_k$ may be centered in its pairing with
$P^k u$. Both centered sup norms are at most one, so (19.8)
bounds the absolute value of that pairing by $\theta_k$.
Contraction and $0\le q\le1$ also give

$$
 0\le\langle w_k,P^{h-k}w_k\rangle_m
 \le\|w_k\|_2^2\le\|P^k u\|_2^2
 =\gamma_{2k}\le\theta_k.
 \tag{19.12}
$$

Finally $\mu_h=c^2+\gamma_h$, $\mu_h+c^2\le2$, and
$\gamma_h\le\gamma_k$ for $k<h$. Subtracting $\mu_h^2$ from
(19.11), and bounding its four resulting terms, gives

$$
 |\operatorname{Cov}_*(J_0,J_k)|
 \le\theta_{h-k}+5\theta_k\qquad(0<k<h).
 \tag{19.13}
$$

The shared-read case $k=h$ uses $I_h^2=I_h$, not two independent
read noises. For that case, and for any other exceptional lag,
Cauchy–Schwarz and the Bernoulli variance bound give
$|\operatorname{Cov}_*(J_0,J_k)|\le1/4$.

For a chosen separation $v\ge1$, call a covariance index
$1\le k<N$ exceptional when

$$
 k<v\quad\hbox{or}\quad |k-h|<v.
 \tag{19.14}
$$

There are at most $(v-1)+(2v-1)=3v-2$ such indices, independently
of $h$. For every other index, (19.9), (19.13) and monotonicity
of $\theta_n$ bound the absolute covariance by $6\theta_v$.
The usual covariance expansion for the stationary average of the
$J_i$ therefore gives

$$
 \begin{aligned}
 \operatorname{Var}_*\left(\frac1N\sum_{i=0}^{N-1}J_i\right)
 &=\frac{N\operatorname{Var}_*(J_0)
      +2\sum_{k=1}^{N-1}(N-k)\operatorname{Cov}_*(J_0,J_k)}{N^2}\\
 &\le\frac1{4N}+\frac{3v-2}{2N}+6\theta_v
 =\frac{6v-3}{4N}+6\theta_v.
 \end{aligned}
 \tag{19.15}
$$

The good-lag term uses
$2N^{-2}\sum_{k=1}^{N-1}(N-k)\le1$; an empty good or exceptional
set causes no difficulty. An average of Bernoulli variables is
in $[0,1]$, so its variance is also at most $1/4$.
For the marker average $z$ alone,
$\operatorname{Cov}_*(I_0,I_k)=\gamma_k$. Its at most $v-1$
short indices and remaining bound $\theta_v$ give the same
conservative envelope. The lower certificate $D_v^-$ in (18.4)
thus proves simultaneously, without a lag restriction,

$$
 \operatorname{Var}_*(z)\le\overline V_{N,v},\qquad
 \operatorname{Var}_*(a_j)\le\overline V_{N,v}\quad(1\le j\le3).
 \tag{19.16}
$$

The covariance identities and summation here are mature second-moment
methods, used inside this source-specific acquisition proof. No
positive spectral gap, geometric ergodicity or independent-window
assumption was used. The separation parameter $v$ is an integer in
the proof and numerical packet; it does not change any physical gap.
For example, $v=\lfloor\sqrt N\rfloor$ makes the exact envelope in
(19.15) tend to zero for each fixed source, uniformly over the pair
lag. No source-uniform rate for $\theta_v$ follows.

Chebyshev's inequality and a union bound over the four fields give
$Q_*(\mathcal F_{N,r,t}^c)\le4\overline V_{N,v}/t^2$.
On the full hidden-and-read record starting at the first read, the
actual initial-law derivative relative to the invariant comparison
is $g_{2d}(X_0)$. The future kernels, including fresh read noise,
are identical. As in [R, (9.18)], the full-source defect gives
$\|g_{2d}\|_2^2\le d_{1/(4d)}^{-1}\le(D_0^-)^{-1}$.
Cauchy–Schwarz on this common path space consequently yields

$$
 Q_0(\mathcal F_{N,r,t}^c)
 \le(D_0^-)^{-1/2}Q_*(\mathcal F_{N,r,t}^c)^{1/2}
 \le\frac2t\sqrt{\frac{\overline V_{N,v}}{D_0^-}}.
 \tag{19.17}
$$

This is the standard $L^2$ initial-law event transfer; see Daniel
Paulin, *Concentration inequalities for Markov chains by Marton
couplings and spectral methods*, arXiv:1212.2015v3, Proposition
3.14, (3.25) [PS18]. Its hypotheses are a common time-homogeneous
transition, invariant comparison and square-integrable initial
Radon–Nikodym density. Here the displayed direct path-space proof
also incorporates the same conditional read kernel. No burn-in or
stationary preparation is substituted. Paulin's positive-gap
variance bounds are not premises. Clipping (19.17) at one proves
(19.2); (18.6) is precisely its squared sufficient condition.

On $\mathcal F_{N,r,t}$, $c\in[c_-,c_+]$. If $Z>0$, (19.5)
gives, for each of the three coordinates,

$$
 \left|\frac{a_j}{z}-m_{h_j-1}\right|
 =\frac{|(a_j-cm_{h_j-1})-m_{h_j-1}(z-c)|}{z}
 \le\frac{2t}{z}.
 \tag{19.18}
$$

Both the ratio and the true probability are in $[0,1]$, justifying
the cap at one in $e$. If $Z=0$, the declared error $e=1$ is valid
and $L>0$ cannot pass. This proves (19.3) without any division by
a rare $B^r$ frequency. In particular these ratios estimate original
nonstationary coordinates; raw marker frequency $z$ estimates $c$.

The deterministic part of Theorem 16.2 uses only the three
coordinate error bounds and the enclosure of $c$. Equations
(19.3), (18.7) supply exactly those hypotheses, with $e$ in place
of $e_p$. Thus $\Delta_r\ge L>0$, and the already established
expansion (16.7), with $0<a_r\le1/16$, gives the first conclusion
of (19.4) at $\tau=8L$. Also
$m_{2r+1}\le\widetilde m_{2r+1}+e\le c(1+4\epsilon^2)$,
so the existing complete-kernel bound (15.4) gives the second.
The exact square expansion and complete-future theorem are reused;
the additional assertion is that (18.2) actually supplies their
simultaneous finite inputs with the original-start error (19.17).
$\square$

[PS18]: https://arxiv.org/html/1212.2015v3

## 20. Fair sparse refinement on one retained original record

**Assumption 20.1 (a declared summable schedule).** Fix one original
source, rational $0<\epsilon<1$ and $0<\alpha_*<1$, and retain
the numerical services of Definition 18.2. Before inspecting labels,
declare a countable schedule $(r_s,k_s)_{s\ge1}$ with every fixed
$r\ge0$ occurring at arbitrarily large refinement levels $k_s$.
For example, concatenate the blocks $r=0,\ldots,n$, with $k=n$,
for $n=0,1,\ldots$. Declare rational $t_s>0$, $0<\beta_s<1$
such that $\sum_s\beta_s\le\alpha_*$ and $t_s\to0$ along each
fixed-$r$ subsequence. The choices $t_s=2^{-k_s-3}$ and
$\beta_s=\alpha_*2^{-s}$ suffice.

Choose $v_s,N_s$ and validated defects, without label feedback,
so that (18.6) holds with allowance $\beta_s$ and
$R_s=N_s+\lambda_{r_s}$ is nondecreasing. These choices may use
the original numerical source/clock services. All stages use the
initial $R_s$ labels of the same retained and extended trajectory
from $e$. A later segment is never treated as a new $e$-start.
New lags are counted by a paid scan of that retained prefix.

**Theorem 20.2 (sourcewise finite stopping with strict fixed-lag
slack).** The services in Assumption 20.1 permit all of its finite
packet choices. On the event

$$
 \mathcal F_*:=\bigcap_{s\ge1}\mathcal F_{N_s,r_s,t_s},
 \qquad Q_0(\mathcal F_*)\ge1-\alpha_*,
 \tag{20.1}
$$

the first stage passing (18.7) is finite and both conclusions
(19.4) hold at that stage. No source-uniform stopping index,
physical time, resource rate or finite total bill is asserted
off this event.

*Proof.* First fix a validated $D_0^->0$ once. For a given stage
let $\delta_s=\beta_s^2t_s^2D_0^-/4>0$. Since
$d_{1/(vd)}\to1$ as $v\to\infty$, the numerical services permit
finite selection of $v_s$ and a sufficiently refined $D_{v_s}^-$
with

$$
 6\frac{1-D_{v_s}^-}{D_{v_s}^-}<\delta_s/2.
 \tag{20.2}
$$

A search over increasing integers and improving validated lower
enclosures terminates by this strict inequality and convergence.
For example one may also enforce $v_s\ge2^{k_s}$. At this fixed
$v_s$, choose $N_s$ large enough that
$(6v_s-3)/(4N_s)\le\delta_s/2$ and $R_s\ge R_{s-1}$.
One may also enforce $N_s\ge2^{k_s}v_s$. These are finite integer
inequalities. Then $\overline V_{N_s,v_s}\le\delta_s$, proving
(18.6). The construction needs no rate for the convergence of the
capacity defect. Refining its enclosures is essential: fixed
coarse lower bounds need not permit (20.2).

Theorem 19.1 and countable subadditivity give (20.1), despite the
shared and nested data. On this event, for every fixed $r$ and its
refining subsequence, once $t_s<c$,

$$
 z_s\ge c-t_s>0,\qquad
 c_{-,s}\ge c-2t_s,\qquad
 e_s\le\frac{2t_s}{c-t_s}\longrightarrow0.
 \tag{20.3}
$$

By (15.4) choose a finite fixed $r$ with
$\kappa=c(1+4\epsilon^2)-m_{2r+1}>0$. At this very same $r$,
$\Delta_r>0$. Along its refining subsequence,

$$
 L_s\ge\Delta_r-4e_s,\qquad
 \widetilde m_{2r+1,s}+e_s\le m_{2r+1}+2e_s.
 \tag{20.4}
$$

Eventually $4e_s<\Delta_r$, $t_s<c/2$, and
$2e_s+2t_s(1+4\epsilon^2)<\kappa$. These inequalities imply all
of (18.7). Their stage index is finite in the declared schedule,
and Theorem 19.1 applies there on $\mathcal F_*$. Merely letting
$r$ increase is not the argument: $\Delta_r$ shrinks, while the
proof refines at a fixed $r$ having both positive margins.
$\square$

**Proposition 20.3 (selection, conditioning and the retained past).**
The first successful stage in Theorem 20.2 is a stopping rule for
the successively available original label prefixes and declared
numerical packets. The probability of issuing a false certificate
at any stage is at most $\alpha_*$. For any fixed $r$, conditional
on the actual acquired record beginning with $B^r$, that probability
is at most $\min\{1,4^r\alpha_*\}$. The result certifies the
specified mathematical conditional law $R_B^r$ on its complete
renumbered future, and does not force that conditioning event.
It makes no comparison including the retained original past beyond
the distinctions of Proposition 16.3.

*Proof.* Every guard is a finite rational function or comparison of
an available prefix and its declared packet; the event of first
success by stage $s$ is measurable from that prefix. A false
certificate belongs to $\mathcal F_*^c$, proving the unconditional
claim. The original probability of the fixed event $H_r$ is
$4^{-r}$ by (15.2), so division gives the conditional bound.
This does not give the same bound for a random selected $r$
conditioned on its own selected event. Proposition 16.3 continues
to give the full-past obstruction, in particular
$\operatorname{TV}(Q_0,(J_r)_*Q_*)\ge1-4^{-r}$.
$\square$

## 21. Paid representation, chronological work and the scope of reuse

**Definition 21.1 (a finite bit and arithmetic model).** Encode each
original label by two bits. A marker bit is obtained by comparing
that label with $3$. For one packet write

$$
 R=N+\lambda_r,\qquad b_N=\lceil\log_2(N+1)\rceil,
 \qquad w=\lceil\log_2(R+2)\rceil.
 \tag{21.1}
$$

Use unsigned bounded integers, explicit bit arrays and exact rational
arithmetic. A word operation acts on at most $w$ bits and may read
or write a bit, compare, add, subtract, or take an integer remainder.
A word operation is not a constant-cost real operation: the
schoolbook bit cost is at most $O(w^2)$, including remainder.
Numerical-service bit work and its own peak space are separate
charges $C_{\rm cap}$ and $M_{\rm cap}$. Names have the total
query-function meaning of [R, Definition 11.1]; a finite packet
uses only finitely many precision queries. Their answer costs,
as well as construction and validation, belong to $C_{\rm cap}$.
Let $B_{\rm cap}$ count the finite retained name representations,
query replies, validated capacity certificates and rational packet.
An infinite name is not treated as a finite string; oracle access
and its costs remain the stated conditional service. No bound for
these three quantities is implicit in a count of labels.

**Proposition 21.2 (an explicit realization and its bill).** The
statistic (18.2) has a chronological realization with exactly four
count fields of $b_N$ bits, a circular array of $\lambda_r$ marker
bits, a two-bit current label, one current marker bit, and sixteen
$w$-bit control registers. Hence this allocated counting workspace
has exactly

$$
 4b_N+\lambda_r+3+16w
 \tag{21.2}
$$

bits, apart from the separately encoded numerical packet. A
shared field can reduce it when $r=0$; no minimality is asserted.
The exact observation bill is $R$ labels, with final original read
at $(R+1)d$ from the $e$-start. The count fields each lie in
$\{0,\ldots,N\}$. At most $4N$ count increments and
$64(R+\lambda_r+1)$ word operations suffice, including initial
array writes, index work and marker extraction. Thus schoolbook
bit work is $O((R+\lambda_r+1)w^2+Nb_N)$ in addition to the
numerical-service and rational-guard work.

If $U$ is the total bit length of the rational inputs and the
integers appearing in (18.1)–(18.7), straight-line evaluation of
those displayed rational expressions and cross-multiplied guards
has $O(U^2)$ schoolbook bit cost, denoted $C_{\rm rat}$, and
$O(U)$ additional working bits. This charge includes producing
$\tau=8L$ and checking (18.6); square roots need not be computed.
Without retaining the full label prefix, the four counts, their
integer parameters and numerical packet suffice for these guards.
If the original label segment is retained as well, its additional
payload is exactly $2R$ bits, with its index and length already
covered by the stated control registers.

For the nested-record route through a finite successful stage $S$,
retaining all original labels pays exactly $2R_S$ payload bits and
$R_S$ physical reads in total. Recounting all prefixes pays

$$
 \begin{gathered}
 \sum_{s=1}^S64(R_s+\lambda_{r_s}+1)
       \quad\hbox{word operations at their respective widths }w_s,\\
 \sum_{s=1}^S4N_s\quad\hbox{as an upper bound on count increments},
 \qquad
 \sum_{s=1}^S(C_{{\rm cap},s}+C_{{\rm rat},s})
       \quad\hbox{additional bit work}.
 \end{gathered}
 \tag{21.3}
$$

The physical final time is $(R_S+1)d$, not a sum of restarted
clocks. With service scratch released between stages, peak space
is bounded by $2R_S$ plus the maximum, over $s\le S$, of (21.2),
$B_{{\rm cap},s}$, the guard working space and $M_{{\rm cap},s}$
added together. Source names retained for reuse are included in
$B_{{\rm cap},s}$. Every term is finite on the stopping event;
no expectation or source-uniform bound for their sum is inferred.

*Proof.* Initialize the circular array and count fields to zero.
At label index $k=0,\ldots,R-1$, extract $I_k$. If $k<N$, add it
to $Z$. For each of the three ordered lags $h_j$, if $k\ge h_j$
and $i_j=k-h_j<N$, retrieve $I_{i_j}$ from its circular position
and add $I_{i_j}I_k$ to $A_j$. Perform these reads before writing
$I_k$ in position $k\bmod\lambda_r$. A required old bit is still
in the array since $1\le h_j\le\lambda_r$; the equality case is
why the write comes last. Only initialized past positions are
read. Each pair origin $i=0,\ldots,N-1$ is counted exactly once,
at index $i+h_j\le R-1$. This proves (18.2) as an actual consumer
of the chronological original segment, including its endpoint.

One allocation of the control registers is
$N,r,\lambda_r,h_1,h_2,h_3,R,k,p,p_1,p_2,p_3,i_1,i_2,i_3$
and one temporary register, where $p=k\bmod\lambda_r$ and
$p_j=i_j\bmod\lambda_r$ are used only when their origins are
eligible. All register values fit in $w$ bits; negative origins
are avoided by the first test. Range tests, subtractions,
remainders, bit accesses, products of two bits and increments
require fewer than sixty-four of the declared word operations
per label. Initialization and final extraction fit the remaining
$64(\lambda_r+1)$ allowance. Each count has $N$ possible unit
increments, proving the separate $4N$ bound. The loop index and
ring positions are included in (21.2), rather than hidden in a
unit-memory convention.

The rational formulas have a fixed finite number of operations
and bounded algebraic degree in their encoded inputs. They may
be evaluated with unreduced fractions and positive denominators,
using cross products for comparisons. Their intermediate bit
lengths are $O(U)$; schoolbook multiplication gives $O(U^2)$ bit
work and $O(U)$ space. The $Z=0$ branch is tested before division.
This accounts for deterministic arithmetic without assuming
constant-cost access to exact real source parameters.

For the nested route, store the two-bit labels once as the source
continues. At each stage scan its complete retained prefix using
the same counter construction, then release its counting scratch
after deciding the guards. Original physical reads are not repeated;
record accesses and computations are repeated and charged in
(21.3). Numerical packets are constructed or validated at their
stated costs. Summing the finite scans and taking the maximum of
simultaneously held workspaces gives the asserted bill. $\square$

**Definition 21.3 (source correspondence and mathematical scope).**
The additional result of Theorem 19.1 is the following
`repo-derived` acquisition/interface deduction: the original marker
and three homogeneous lag pairs (18.2) produce the same square and
specified complete conditional-future certificates as §16, with
the new original-start event (19.2), capacity confidence independent
of the pair lag, and the actual representation and costs (21.2)–(21.3).
The exact marked-source relation is (19.5), not an identification
based solely on a shared model-family name. The original full-source
suppliers are [R, §8] for the marked identity, [R, §9] for the
capacity resolvent, bounded centered covariance and initial-density
estimate, and [R, §11] for the numerical defects. Equations
(15.4), (16.7) and the deterministic part of Theorem 16.2 supply
the two consumers. Theorem 20.2 adds only sourcewise stopping under
its explicitly stated fair refinement and numerical services.

The standard covariance expansion, positive-form Cauchy–Schwarz,
Chebyshev and union bounds, initial-law transfer [PS18, Proposition
3.14, (3.25)] and rational interval propagation are
`literature-attested` intermediates inside this deduction. They
are not new general concentration or spectral theorems. Paulin's
spectral-gap bounds require an additional positive-gap hypothesis;
none is supplied or inferred here. The comparison is conditional
ordinary mathematics under the analytic suppliers of Assumption
1.1, without a claim of formal verification or worldwide priority.

At matched $r,N$, the four bounded count values replace the
$4^{2r+4}$ fields of the full length-$2r+4$ word table in Definition
9.1; the sparse final lag is $2r+2$, so its endpoint uses
$N+2r+2$ labels. Its confidence is derived directly, rather than
by summing the old word errors. The old full table has additional
consumers that these four counts do not serve. Defect refinement,
record retention, arithmetic, final time and all numerical services
remain on the bill. There is no claim of optimal counters,
source-uniform convergence, or dominance of every total-resource
coordinate. Exact laws, finite-confidence certificates, actual
reachability, full-past prediction and uniform rates are distinct:
the B-conditioned suffix theorem does not prepare stationarity,
force $B^r$, discard its paid past for free, or compare the retained
full record with a stationary one. The negative square remains
failure of the specified algebraic positive-state binding, not a
negative physical probability.

## 追加锚（本行以下为增补区）
