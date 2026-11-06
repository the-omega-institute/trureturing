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
