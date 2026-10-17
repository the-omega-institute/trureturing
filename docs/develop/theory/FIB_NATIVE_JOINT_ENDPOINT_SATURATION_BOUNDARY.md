# Joint endpoint records: the evaluated finite-activity saturation boundary

## 1. Conditional experiment, activity class and notation

**Convention 1.1 (source and unchanged problem).** The isolated CG root,
its isolation/Jacobian certificate, exact ranks, TP normalization and
original minimax identification are named `ASSUMED-UNVERIFIED`
antecedents. Operator equalities below apply at that root. Supplied
coefficient enclosures are conditional inequalities of the displayed
expressions, not off-root normalization or fresh numerical
certification. All results are ordinary conditional mathematics.

Use the original five modes indexed by $(0,1,2,3,13)$ and

$$
\begin{gathered}
E=((e_0+e_{13})/\sqrt2,(e_1+e_3)/\sqrt2,e_2),\quad P=EE^\dagger,\\
p_y=(y/128,(64-y)/128,1/2),\quad a_y=(\sqrt{p_{yi}})_i,\\
\rho_{y,e,n}=U_{e,n}a_ya_y^TU_{e,n}^\dagger,\quad
U_{e,n}=\operatorname{diag}(e,n,1),\quad
y\in\{5,16,27\},\quad e,n\in\{\pm1\}.
\end{gathered}
\tag{JS.1}
$$

The sole unknown normalized specimen is $E\rho_{y,e,n}E^\dagger$.
Its original height is $y/256$ and winding parity is $en=(-1)^m$.
The instrument receives neither history. The ideal live block remains
the entire coherent matrix $EU_{e,n}B_y^{\rm ideal}U_{e,n}^\dagger E^\dagger$
of CG.111. The five separate ideal failure measures are

$$
w_\ell f_y(u)du\,P_f,\qquad
w=(0,1/4,1/2,1/4,0),\qquad f_y(u)=\frac{6y}{(y+6u)^2},
\quad 0\le u\le1.
\tag{JS.2}
$$

Absolute time is $6+u$. Error is HALF the full stopped-cq trace norm,
maximized over all twelve histories, including every live coherence,
singular-time component, wrong support, abort and zero-target sector.
The actual output density used in recovery is $g(u)=2/(1+u)^2$;
it never replaces the ideal $f_y$ in this comparison.

An actual acquisition has CP encoders of total effect $I_5$, actually
generated dephased classical labels, and full-output TP conditional
decoders. Each fibre counts jointly every future-accessible
input-bearing specimen, memory, quantum controller, environment,
return system and entanglement share. Other dilation systems are
permanently inaccessible before this same cut. Discarded Kraus
multiplicity is not readable. No prior, helper, copy, postselection,
acceptance division, reset, retry, readable old history, bypass or free
time is supplied.

For the plus effect $F$ of an actually acquired binary report retain
exactly the original inequality and cost:

$$
\mathsf V(F)=\frac{2|\operatorname{Re}F_{01}|}{\kappa}\ge s,
\qquad \mathsf W=\mathsf C(s).
\tag{JS.3}
$$

Here $\mathsf W$ is the maximum over the twelve histories of the
ACQUIRED probability of a joint fibre of dimension at least three,
including its later-failure mass. Other effect coordinates and the
forgotten full channel remain free in the comparison class.

**Definition 1.2 (full activity class).** Use exactly FA Definition
67.2. On each whole joint decoder fibre a measurable PSD first-event
rate $R_j(u)$ has integrable operator norm. Survivor controls preserve
trace apart from that rate and may be arbitrary admitted TP controls,
including noncommuting and unobserved controls. Their survivor maps obey

$$
-\frac d{du}\operatorname{tr}\mathcal S_{j,u}(X)
=\operatorname{tr}(R_j(u)\mathcal S_{j,u}(X)),\qquad
\mathcal S_{j,0}=\mathrm{id}.
\tag{JS.4}
$$

Terminal survivor processing is TP on the whole fibre. No singular
first-event part, forced deadline absorption or positive-carrier
operation after first absorption is permitted. Activity is

$$
\mathsf A=\sup_j\int_0^1\|R_j(u)\|\,du.
\tag{JS.5}
$$

For finite labels use a maximum; use the stipulated essential supremum
for an integral instrument. This is a supremum of integrated norms,
not an expectation or an integral of a labelwise maximum. Write
$\mathfrak F_{s,A}$ for the class with original error $E_*$, (JS.3),
and $\mathsf A\le A$, and $\mathcal T_A(s)$ for its supremal
full-acquisition-label height TV between $(5,+,+)$ and $(27,+,+)$
when nonempty. Necessity covers finite and convergent countable
instruments and only the expressly stipulated measurable/integrable
finite-fibre extension of CG Convention 21.3. No further disintegration
or infinite-dimensional coding theorem is assumed. Write $\mathcal T(s)$
for the same original optimization without an activity budget, and
$t_{\min}(s)=\inf\{t\ge0:\mathfrak F_{s,\log(1+t)}\ne\varnothing\}$.
FA73 supplies its positive finite attained value for $0\le s<s_0$.

**Definition 1.3 (source dictionary).** Set

$$
\begin{gathered}
D=\operatorname{diag}(h_0,h_1,h_2),\quad
T=ae_0e_1^T+be_1e_0^T,\quad S=ce_0e_2^T+de_2e_0^T,\\
M=\operatorname{diag}(0,m_1,m_2),\quad
D^\dagger D+T^\dagger T+S^\dagger S+M=I_3,\\
\theta=ab/(h_0h_1),\quad\omega=cd/(h_0h_2),\quad
\delta=\theta+\omega,\quad s_0=\sqrt\delta,\quad\kappa=h_0a+h_1b,\\
\alpha=\theta/\delta,\quad\beta=\omega/\delta,\quad U=1/\alpha,\\
V=m_2h_1^2/b^2,\quad W=m_1h_2^2/d^2,\quad
\mu=\alpha V+\beta W,\quad r=V/\mu.
\end{gathered}
\tag{JS.6}
$$

The seven amplitudes and $m_1,m_2$ are positive, $0<\delta<1$ and
$\alpha+\beta=1$. FA71/74 supplies $V/W\in(1/5,3/10)$, so
$0<r<1<U$. For $0\le x\le U$ define

$$
\begin{aligned}
Y(x)&=(1-\alpha x)/\beta,\qquad H(x)=(\sqrt x-1)^2/2,\\
D_c(x)&=\delta h_0^2+b^2x+d^2Y(x),\\
N_c(x)&=\delta h_1^2h_2^2+a^2h_2^2x+c^2h_1^2Y(x),\\
c_*(x)&=N_c(x)/D_c(x),\qquad F_c(x)=H(x)/c_*(x),\\
C_{\rm end}&=\mu F_c(r)=\frac{(\sqrt\mu-\sqrt V)^2}{2c_*(r)}.
\end{aligned}
\tag{JS.7}
$$

Both affine denominators are strictly positive on the entire closed
interval. The variable $x$ here is not a history height. On the compact
ellipse define

$$
\begin{gathered}
\mathcal E=\{(z,w):\alpha z^2+\beta w^2=1\},\quad
h(z,w)=(1,z,w)^T,\quad K(z,w)=s_0D+zT+wS,\\
n(z,w)=(0,dw/h_2,-bz/h_1)^T,\quad
\Delta=\rho_{27,+,+}-\rho_{5,+,+},\\
N_{ij}=\operatorname{tr}(K_i\Delta K_j^\dagger),\quad
(K_0,K_1,K_2)=(D,T,S),\quad L=\operatorname{diag}(s_0,1,1),\\
G=LNL,\quad f(z,w)=h(z,w)^TGh(z,w),\quad
k(z,w)=n(z,w)^T\Delta n(z,w),\\
H_{\rm live}=(1-\delta)\Delta A,\quad
A_y=\sum_i h_i^2p_{yi},\quad \Delta A=A_{27}-A_5>0,\\
d_f=11m_1/64,\quad
z_f=\sqrt{m_1m_2}(\sqrt{37}-\sqrt{59})/16<0,\\
\Xi=\begin{pmatrix}-d_f&z_f\\z_f&0\end{pmatrix},\quad
L_f=\sqrt{d_f^2+4z_f^2},\quad\gamma_f=(L_f-d_f)/2>0,\\
S_{\rm corner}=\frac14\sum_{\sigma,\eta=\pm1}|f(\sigma,\eta)|,\quad
T_0=\mathcal T(s_0)=\frac{H_{\rm live}+S_{\rm corner}+L_f}{2},\quad
B_0=T_0-\gamma_f.
\end{gathered}
\tag{JS.8}
$$

The expression for $T_0$ is the credited static endpoint. These are
unnormalized height differences, not conditional-on-failure distances.

## 2. Existing actual labels and the whole-class necessary constraints

**Lemma 2.1 (actual-label reduction).** Put $t=e^A-1$ and
$q=1-s/s_0$ for $0\le s<s_0$. For every finite-budget competitor,
each actual low label nonzero on supported inputs has whole fibre
dimension two and can be written

$$
K_j=\sqrt{\pi_j}K(z_j,w_j),\quad
N_j=\pi_jv_j n_jn_j^T,\quad
\pi_j>0,\quad(z_j,w_j)\in\mathcal E,\quad
0\le v_j\le t c_*(z_j^2).
\tag{JS.9}
$$

Here $N_j$ is its pulled-back total later-failure effect. Its supported
acquisition effect is exactly $K_j^\dagger K_j+N_j$. On the existing
label space let $P$ have masses $\pi_j$ and let $d\nu=v\,dP$; their
ellipse pushforwards satisfy

$$
\int hh^T\,dP=I_3,\qquad \int nn^T\,d\nu=M,\qquad
\nu(\mathcal E)=\mu,\qquad\int z^2\,d\nu=V,\quad
\int w^2\,d\nu=W,\quad\int zw\,d\nu=0,
\tag{JS.10}
$$

and

$$
0\le e:=\int H(z^2)dP=1-\int|z|dP\le q,
\qquad\int F_c(z^2)d\nu\le te\le tq.
\tag{JS.11}
$$

The TV of the full actual acquisition label is exactly

$$
T_{\rm instr}=\frac12\left[H_{\rm live}
 +\int|f(z,w)+v k(z,w)|\,dP\right].
\tag{JS.12}
$$

In this last integral each label retains its own $v$, including when
several labels have the same ellipse point. Coarsening gives only an
upper bound by (JS.12).

Proof. JR42 gives supported live map $\Lambda_*$, total failure effect
$M$, zero other effect, zero high failure, low coefficient Gram
$\operatorname{diag}(\delta,1,1)$, and high products proportional to
$D$. Complex equality forces each nonzero low product onto the real
null face after removal of one phase; no real-processor restriction is
imposed on competitors.

The trace differential inequality from (JS.4) gives whole-fibre
survival at least $e^{-A}I$, even with arbitrary admitted TP survivor
controls. Hence a nonzero supported encoder cannot have zero live
composition. A nonzero null product has rank two: its determinant is
zero and its $1,2$ principal minor is nonzero. On a low fibre this
forces dimension exactly two. For arbitrary encoder and live-decoder
Kraus families fix a nonzero product $B_0C_0$; $C_0$ is onto and
$B_0$ injective. For a null product $xD+zT+wS$, its kernel and
adjoint kernel are respectively

$$
\mathbb C(1,-bz/(h_1x),-dw/(h_2x))^T,\qquad
\mathbb C(1,-az/(h_1x),-cw/(h_2x))^T.
\tag{JS.13}
$$

A common image or kernel fixes both ratios. Fixing $B_0$ therefore
makes every nonzero $B_0C_j$ proportional; its injectivity makes all
$C_j$ proportional. Fixing the onto $C_0$ similarly makes all live
$B_i$ proportional. Zero products with these fixed matrices force
zero factors. Absorbing the squared proportionality constants gives
one supported encoder matrix and one live-decoder matrix on this
actual label. This is FA69's double rigidity, not an observable Kraus
refinement.

Normalize its first coefficient to obtain $K_j$ in (JS.9). The failure
effect kills both $e_0$, since it is dominated by $M$, and the kernel
in (JS.13), since the encoder has that kernel. The remaining line is
$n(z,w)$, nonzero even on either axis. FA69's explicit Schur complement,
with $G_K=K(z,w)^\dagger K(z,w)$, is

$$
G_K-\frac{G_Ke_0e_0^TG_K}{(G_K)_{00}}=c_*(z^2)nn^T.
\tag{JS.14}
$$

Indeed $(G_K)_{00}=D_c(z^2)$, and elimination of this pivot gives
$N_c(z^2)nn^T/D_c(z^2)$ using
$\delta=\theta z^2+\omega w^2$. The necessary survival bound pulls
back to $N_j\preceq tK_j^\dagger K_j$; its Schur complement gives
exactly $v_j\le tc_*(z_j^2)$. This bound is independent of the
competitor's time law. Full decoder TP and zero other supported
output give the stated acquisition effect.

The low Gram gives the first matrix identity in (JS.10). The diagonal
and off-diagonal failure entries give the $V,W,zw$ constraints;
the ellipse equation gives mass $\mu$. Absorb the actual report coin
into each label. Failure effects have zero $01$ entry, while high
products proportional to $D$ also give zero $01$ contribution.
The winding identity is therefore
$\mathsf V=s_0|\int r_jz_jdP|\le s_0\int|z|dP$.
Together with $\int1=\int z^2=1$ this proves the first part of
(JS.11). Capacity gives $d\nu\le tc_*(z^2)dP$; multiplication by
$F_c\ge0$ proves the second part.

On an existing low label the exact height difference of its acquisition
probability is $\pi_j(f+v_jk)$. High labels have no supported failure
and positive differences totaling $H_{\rm live}$. Supported-zero labels
contribute zero. Taking HALF the absolute sum proves (JS.12), without
separating its live and failure contributions. The stipulated integral
case uses the same almost-everywhere rigidity and integrable moments;
no new disintegration is needed. $\square$

## 3. The credited critical cost and its strict equality structure

**Lemma 3.1 (strict capacity tangent).** On $[0,U]$ the tangent to
$F_c$ at $r$ is a global supporting line, with equality only at $r$.
Consequently every measure satisfying (JS.10)'s failure constraints has

$$
\int F_c(z^2)d\nu\ge C_{\rm end},
\quad\text{with equality exactly when }z^2=r\quad\nu\text{-a.e.}
\tag{JS.15}
$$

All such equality directions have $k(z,w)<0$. A covariance-admissible
equality measure exists.

Proof. The supplied JR.52 bounds imply $J=adh_2-bch_1>0$: the lower
product $65\cdot98\cdot809=5153330$ exceeds the upper product
$147\cdot16\cdot707=1662864$, with the common denominator $10^9$.
These are symbolic uses of inherited enclosures. Writing
$D_c=D_0+D_1x$ and $N_c=N_0+N_1x$ gives

$$
\begin{gathered}
D_0=\delta h_0^2+d^2/\beta>0,\quad
N_0=\delta h_1^2h_2^2+c^2h_1^2/\beta>0,\\
D_1=-bJ/(ch_1)<0,\qquad N_1=(ah_2/d)J>0.
\end{gathered}
\tag{JS.16}
$$

For $\rho=1/c_*=D_c/N_c$, its first derivative is strictly negative
and its second strictly positive, since

$$
\rho'=\frac{D_1N_0-D_0N_1}{(N_0+N_1x)^2},\qquad
\rho''=\frac{-2N_1(D_1N_0-D_0N_1)}{(N_0+N_1x)^3}.
\tag{JS.17}
$$

On $0<x<1$, $H'<0$, $H''>0$, so
$F_c''=H''\rho+2H'\rho'+H\rho''>0$. Continuity at zero extends
strict convexity to $[0,1]$. Thus the tangent at $r$ lies strictly
below every other point of this interval, including zero. Its slope
is negative and its value at $1$ is strictly below $F_c(1)=0$.
For $x>1$ it decreases further, whereas $F_c(x)\ge0$. This proves
the strict support assertion through both axes. Integrating it with
mass $\mu$ and first moment $V=\mu r$ proves (JS.15).

Let $\nu_0$ assign mass $\mu/2$ to each of
$(\sqrt r,\sqrt{W/\mu})$ and $(\sqrt r,-\sqrt{W/\mu})$.
Its covariance is $M$, since the off-diagonal cancels and the two
diagonal integrals are $m_1,m_2$. Its cost is $C_{\rm end}$.
For any equality direction, writing $\epsilon=\operatorname{sign}(zw)$,

$$
n=(0,\eta\sqrt{m_1/\mu},-\sigma\sqrt{m_2/\mu})^T,\qquad
k=-\frac{d_f+2\epsilon z_f}{\mu}<0.
\tag{JS.18}
$$

For the strict sign use the inherited $m_1>496/1000$, $m_2<345/1000$:

$$
\frac{d_f}{2|z_f|}
=\frac{\sqrt{59}+\sqrt{37}}{16}\sqrt{\frac{m_1}{m_2}}
>\frac{27}{32}\sqrt{\frac{496}{345}}>1.
\tag{JS.19}
$$

The last squared comparison is $361584>353280$; the preceding one
uses $\sqrt{59}>15/2$ and $\sqrt{37}>6$. $\square$

**Corollary 3.2 (strict finite feasibility bound).** Every feasible
finite weak budget satisfies $tq>C_{\rm end}$.

Proof. Equations (JS.11) and (JS.15) give $tq\ge te\ge C_{\rm end}$.
Equality would force the scalar pushforward of $\nu$ to
$\mu\delta_r$. The positive measure $tP-\nu/c_*$ would then have
zero $H$ integral and be supported on $z^2=1$. The scalar law of $P$
would be
$(\mu/(tc_*(r)))\delta_r+(1-\mu/(tc_*(r)))\delta_1$.
Its first moment is strictly below one since $r<1$, contradicting
(JS.10). Thus equality is impossible. $\square$

## 4. Compact limiting failure problem and universal upper bound

**Definition 4.1 (limiting correspondence problem).** For finite
$\lambda\ge C_{\rm end}$ put

$$
\Phi(\lambda)=\max\left\{
\int k(z,w)_+d\nu:\ \nu\ge0,\quad
\int nn^T d\nu=M,\quad\int F_c(z^2)d\nu\le\lambda
\right\}.
\tag{JS.20}
$$

The measure is on the whole compact ellipse, including its axes.
This definition is an intermediate optimization, not an evaluated
scalar crossover.

**Lemma 4.2 (compactness and finite representation).** The maximum in
(JS.20) exists. Every feasible measure can be replaced by at most five
atoms preserving covariance, cost and objective. Feasibility holds
exactly for $\lambda\ge C_{\rm end}$, and $\Phi(C_{\rm end})=0$.

Proof. Covariance is equivalent to mass $\mu$, $z^2$ moment $V$ and
$zw$ moment zero; the $w^2$ moment follows from the ellipse. All
relevant functions are continuous on a fixed compact set. Measures
of this fixed mass have weakly convergent subsequences, preserving
all these integrals. One elementary compactness justification takes
a countable uniformly dense family in the continuous functions,
selects a diagonal subsequence of their bounded integrals, and extends
the limit by the uniform norm; the resulting positive functional of
mass $\mu$ is integration against a measure on the compact ellipse.
Thus the closed cost slice is compact and its continuous objective
attains a maximum.

There is also a finite-dimensional representation proof. Apply the
continuous map $(z,w)\mapsto(z^2,zw,F_c(z^2),k_+)$ into $\mathbb R^4$.
An affine dependence among more than five image points permits changing
weights, keeping the barycentre fixed, until a weight vanishes.
Repeating reduces any finite convex combination to five points.
Such five-point combinations form a compact set, as the continuous
image of the compact five-weight simplex and five copies of the image.
Approximation of the four continuous integrals by finite simple laws
therefore puts their barycentre in this same closed hull. Multiplying
by $\mu$ gives the asserted exact representation, including zero
weights and axes. Lemma 3.1 and $\nu_0$ prove the feasibility domain;
its equality directions have $k_+=0$, proving the endpoint value.
$\square$

**Theorem 4.3 (full-class limiting necessity).** If $q_n\to0$ through
positive values, $t_n=e^{A_n}-1$, $q_nt_n\to\lambda<\infty$, and
original competitors are feasible, then $\lambda\ge C_{\rm end}$ and

$$
\limsup_n T_{{\rm instr},n}\le B_0+\Phi(\lambda).
\tag{JS.21}
$$

Proof. The coefficient probability laws $P_n$ have
$\int(|z|-1)^2dP_n=2e_n\le2q_n$. Every weak limit is therefore
supported on $|z|=1$, and the ellipse then gives $|w|=1$.
The exact zero moments of $z,w,zw$ force the four corner weights to
be $1/4$ by the four sign equations. Hence
$P_n\Rightarrow\frac14\sum_{\sigma,\eta}\delta_{(\sigma,\eta)}$
and $\int|f|dP_n\to S_{\rm corner}$.

The failure-weighted measures $\nu_n$ have fixed mass $\mu$ on this
same compact ellipse. Along any subsequence they have a further weak
limit retaining covariance, including possible axis mass. Its continuous
cost integral is at most $\lambda$ by (JS.11). No compactness is
asserted for $t_nP_n$, whose mass diverges, or for the unbounded
label multipliers $v_j$. Fixed weighted failure mass is the compact
quantity. Corollary 3.2 gives $\lambda\ge C_{\rm end}$.

For every covariance-admissible $\nu$,
$\int k d\nu=\operatorname{tr}(M\Delta)=-d_f$, so
$\int|k|d\nu=d_f+2\int k_+d\nu$. The actual-label triangle inequality
in (JS.12) gives

$$
T_{{\rm instr},n}\le\frac{H_{\rm live}+\int|f|dP_n+
\int|k|d\nu_n}{2}.
\tag{JS.22}
$$

Take a subsequence realizing the upper limit and then a compact
failure subsequence. The resulting bound is
$(H_{\rm live}+S_{\rm corner}+d_f)/2+\int k_+d\nu
\le B_0+\Phi(\lambda)$. This necessity covers every admitted
survivor control, time law and free completion. $\square$

## 5. Exact finite moment repair and common recovery

**Theorem 5.1 (recovery of a strict-cost failure measure).** Let
$\nu=\sum_{i=1}^m a_i\delta_{(z_i,w_i)}$, $a_i>0$, have covariance
$M$ and cost $C_\nu<\lambda$. Along every prescribed sequence
$q_n\to0$, $q_nt_n\to\lambda>C_{\rm end}$, one common finite
original instrument for each sufficiently large $n$ has activity at
most $\log(1+t_n)$, contrast at least $s_0(1-q_n)$, exact original
sharp cost and errors, and TV tending to $B_0+\int k_+d\nu$.

Proof. Put $c_i=c_*(z_i^2)$ and, using a matrix symbol distinct from
the radial endpoint $U$, define

$$
\mathsf U=\sum_i\frac{a_i}{c_i}h_ih_i^T
=\begin{pmatrix}b_0&b_1&b_2\\b_1&b_{11}&b_{12}\\b_2&b_{12}&b_{22}\end{pmatrix},
\quad d_0=\sum_i\frac{a_i|z_i|}{c_i}.
\tag{JS.23}
$$

The ellipse gives $b_0=\alpha b_{11}+\beta b_{22}$ and
$C_\nu=(b_0+b_{11})/2-d_0$.
For a sufficiently large finite $t$ generate one rare low label per
atom, with live coefficient weight $\pi_i=a_i/(tc_i)$ and attached
failure effect $a_in_in_i^T$. Its multiplier is $tc_i$, exactly its
capacity. All these attached effects sum to $M$ at each finite $t$.
Their nonvanishing later-failure acquisition mass is fully counted;
small live coefficient weight is not small acquired mass.

Set

$$
\begin{gathered}
m_t=1-b_0/t,\quad X_t=(1-b_{11}/t)/m_t,\quad
Y_t=(1-b_{22}/t)/m_t,\\
p_{\sigma\eta}=\frac{m_t}{4}
-\frac{\sigma b_1}{4t\sqrt{X_t}}
-\frac{\eta b_2}{4t\sqrt{Y_t}}
-\frac{\sigma\eta b_{12}}{4t\sqrt{X_tY_t}},\qquad
(z,w)=(\sigma\sqrt{X_t},\eta\sqrt{Y_t}).
\end{gathered}
\tag{JS.24}
$$

These are four additional pure-live labels. For large $t$, $X_t,Y_t>0$,
$\alpha X_t+\beta Y_t=1$ exactly, and every $p_{\sigma\eta}>0$
since it tends to $1/4$. Their mass, two squared moments and three
cross moments are exactly

$$
m_t,\quad 1-b_{11}/t,\quad1-b_{22}/t,\quad
-b_1/t,\quad-b_2/t,\quad-b_{12}/t.
\tag{JS.25}
$$

Adding the rare moments $\mathsf U/t$ gives $\int hh^TdP=I_3$
exactly. No asymptotic moment equation is substituted for a finite
normalization.

Report $\operatorname{sign}z$ on each low label, choosing either sign
at zero, and fair reports on the high and complement labels specified
below. The normalized raw contrast is

$$
1-e_t=\frac{d_0}{t}+\sqrt{(1-b_0/t)(1-b_{11}/t)}.
\tag{JS.26}
$$

For $Z_t=1-(b_0+b_{11})/(2t)$ its exact deficit is

$$
e_t=\frac{C_\nu}{t}+
\frac{(b_0-b_{11})^2}
{4t^2[Z_t+\sqrt{(1-b_0/t)(1-b_{11}/t)}]}.
\tag{JS.27}
$$

This follows by multiplying $Z_t-\sqrt{(1-b_0/t)(1-b_{11}/t)}$
by its conjugate sum. If $t\ge2(b_0+b_{11})$, the bracket is at
least one. Thus $te_t=C_\nu+O(t^{-1})$ with a nonnegative remainder.
Since $C_\nu<\lambda$ and $qt\to\lambda$, eventually $e_t\le q$.
Moment Cauchy--Schwarz also gives $0\le e_t\le1$, so the original
contrast inequality is met. If exact contrast is desired, append and
retain an independent binary kernel of factor $(1-q)/(1-e_t)$.
This lies in $[0,1]$ eventually and preserves full-record TV, costs
and activities.

The whole-fibre realization in Theorem 6.1 applies to this exact list.
On a rare actual label the signed height difference is
$a_if(z_i,w_i)/(tc_i)+a_ik(z_i,w_i)$; its absolute value tends to
$a_i|k(z_i,w_i)|$, including $k=0$. Bulk weights and directions tend
to the four corners. The high sum is $H_{\rm live}$. Therefore this
same common acquisition has limiting TV

$$
\frac{H_{\rm live}+S_{\rm corner}+\int|k|d\nu}{2}
=B_0+\int k_+d\nu.
\tag{JS.28}
$$

This proves recovery with the actual live/failure grouping, rather
than combining separately attainable marginal optima. $\square$

## 6. Whole-fibre chronological realization and original outputs

**Theorem 6.1 (simultaneous full-output realization).** Every finite
list in Theorem 5.1, and the lists with varying weights below, has
whole-fibre TP chronological decoders in Definition 1.2, total encoder
effect $I_5$, original error $E_*$, sharp acquired cost and the specified
contrast, simultaneously on all twelve histories. Its full-complex,
passive-reference and separately labelled Borel maps are (JS.33)--(JS.34).

Proof. For a low label let $K$ be its scaled live matrix and $N_f$
its attached failure effect. The null determinant identity is

$$
\det(xD+zT+wS)=h_0h_1h_2x(x^2-\theta z^2-\omega w^2).
\tag{JS.29}
$$

It vanishes, while the lower-right minor $\pi\delta h_1h_2$ is
nonzero. Thus $K$ has rank two, including both ellipse axes. The
vector $n$ is orthogonal to its kernel in (JS.13), so $N_f$ is
supported on its row space. Fix an isometry $J$ from $\mathbb C^2$
onto that space and put

$$
\begin{gathered}
Q_K=J^\dagger(K^\dagger K+N_f)J\succ0,\quad
C_K=Q_K^{1/2}J^\dagger,\quad B_K=KJQ_K^{-1/2},\\
F_K=Q_K^{-1/2}J^\dagger N_fJQ_K^{-1/2}.
\end{gathered}
\tag{JS.30}
$$

Multiplication using the row-space projection gives
$B_KC_K=K$, $C_K^\dagger F_KC_K=N_f$ and
$B_K^\dagger B_K+F_K=I_2$, with $B_K^\dagger B_K\succ0$.
Thus $0\preceq F_K\prec I_2$ on the entire fibre. Use encoder
$C_KE^\dagger$ and, on its whole fibre, the no-event matrix and rate

$$
Z_K(u)=\sqrt{I_2-G_t(u)F_K},\quad
R_K(u)=g(u)F_K(I_2-G_t(u)F_K)^{-1},\quad G_t(u)=2u/(1+u).
\tag{JS.31}
$$

In each original label $\ell$ the current-survivor jump is

$$
\mathcal J_{K,\ell}(u)(Y)
=w_\ell g(u)\operatorname{tr}
(F_KZ_K(u)^{-1}YZ_K(u)^{-1})P_f.
\tag{JS.32}
$$

Its total effect is $R_K(u)$. Since $F_K$ commutes with this chosen
path, $\dot Z_K=-R_KZ_K/2$. Its pulled-back density from the initial
decoder input is exactly $w_\ell g(u)\operatorname{tr}(F_KY)P_f$.
At time one apply only to survivors the isometry
$EB_K(I_2-F_K)^{-1/2}$; its composite live matrix is $EB_K$.
All inverses here are fixed linear operators with positive denominators,
not state-dependent normalization.

The integrated jump effect is $F_K$ and the terminal effect is $I_2-F_K$.
For any intermediate $a\le b$, the no-event propagator is
$Z_K(b)Z_K(a)^{-1}$; the integrated jump pullback is
$Z_K(a)^{-1}(Z_K(a)^2-Z_K(b)^2)Z_K(a)^{-1}$, complementary to its
no-event effect. This proves whole-fibre chronological CP/TP consistency
at every cut. First absorption is actual in this mathematical process;
no later positive-carrier operation follows it. Only survivors receive
the terminal map. There is no singular part or deadline atom.
If $F_K$ has nonzero eigenvalue $f_K$, the integrated rate norm is
$-\log(1-f_K)$. By (JS.14),
$f_K/(1-f_K)=v/c_*(z^2)$. Thus rare saturated labels have activity
$\log(1+t)$ and pure-live labels have activity zero. All rates have
integrable norm for each finite $t$. Necessity in Lemma 2.1 did not
impose this chosen $g$-law or its commutativity.

Add two fair-report high encoders
$\sqrt{(1-\delta)/2}\,DE^\dagger$ into whole dimension-three fibres,
with zero rate and live TP decoder $X\mapsto EXE^\dagger$.
Fix isometries $W_\perp:\mathbb C^2\to V^\perp$ and
$J_0:\mathbb C^2\to\mathbb C^3$. Add two fair-report complement
encoders $W_\perp^\dagger/\sqrt2$ into counted dimension-two fibres,
with zero rate and whole-fibre decoder
$X\mapsto EJ_0XJ_0^\dagger E^\dagger$.
This is FA75's freely chosen coherent completion, distinct from the
fixed certain-failure completion CG.142/CA.10.

The exact moment repair gives low coefficient Gram
$\operatorname{diag}(\delta,1,1)$; adding the high Gram gives $I_3$.
Consequently total supported live effect is $I_3-M$ at the source
root. The attached failures sum exactly to $M$, and the complement
adds $I_5-P$. Hence total encoder effect is $I_5$, with every positive
branch bounded by it and therefore TNI. All conditional decoders are
TP on their entire declared fibres. Generate and dephase each actual
label, permanently discarding every other dilation system before the
joint cut. Retaining any correlated share would change the fibre count.

For every complex $A\in M_5$, with $A_V=E^\dagger AE$, the forgotten
maps are exactly

$$
\begin{aligned}
\Phi^L(A)&=E[DA_VD^\dagger+TA_VT^\dagger+SA_VS^\dagger
 +J_0W_\perp^\dagger AW_\perp J_0^\dagger]E^\dagger,\\
\Phi_\ell^f(\mathcal B)(A)&=w_\ell\left(\int_{\mathcal B}g(u)du\right)
 \operatorname{tr}(EME^\dagger A)P_f,
\qquad\ell\in\{0,1,2,3,13\}.
\end{aligned}
\tag{JS.33}
$$

The second identity holds for every Borel $\mathcal B\subseteq[0,1]$.
These follow by bilinearity of the exact live Gram and the sum of
pulled failure effects. They are identities on all complex matrix
units. Cross-support terms vanish; every within-complement qubit
coherence is retained. Labels $0$ and $13$ remain separately zero,
the other three remain separate, and no extra sector is introduced.

Tensor every encoder, jump, survivor and terminal map by $I_R$ for
any passive reference. The live map is the sum of conjugations by
$EK E^\dagger\otimes I_R$, $K=D,T,S$, and
$EJ_0W_\perp^\dagger\otimes I_R$. The failure map is

$$
w_\ell\left(\int_{\mathcal B}g(u)du\right)P_f\otimes
\operatorname{Tr}_5[(EME^\dagger\otimes I_R)X].
\tag{JS.34}
$$

This is the exact conditional reference operator, not an unconditional
marginal. Thus the full complex/reference/five-Borel identity holds,
with fixed common metadata preserved. On each supported original
history (JS.33) is the credited CG.135 simulator. Its original HALF
full-cq error, with the ideal coherent block and $f_y$, is unchanged:
$e_5=e_{27}=E_*$ and $e_{16}<71/484<37/250<E_*$ under the supplied
certificate. A TV deficit is not added to this error.

An actual low-label probability is
$\operatorname{tr}[(K^\dagger K+N_f)\rho_{y,e,n}]$, including later
failure. Only the high pair has dimension at least three. Its acquired
probability on each history is $(1-\delta)A_y$, independent of signs,
with maximum $(1-\delta)A_{27}=\mathsf C(s)$ on the weak plateau
by JR34--40. The coherent complement is counted as two and has zero
probability on the twelve histories. Failures contribute no $01$
report coordinate, so the reported contrast is precisely (JS.26).
Appending a report coin while retaining its parent label multiplies
both height laws by the same kernel and preserves their full TV.
Everything is fixed before receiving the sole specimen. $\square$

## 7. A limit theorem for every prescribed finite product sequence

**Theorem 7.1 (exact limiting correspondence and common recovery).**
For every finite $\lambda>C_{\rm end}$ and every prescribed sequence
$q_n>0$, $q_n\to0$, $t_n=e^{A_n}-1$, $q_nt_n\to\lambda$,
the original classes are eventually nonempty and

$$
\lim_n\mathcal T_{A_n}(s_0(1-q_n))=B_0+\Phi(\lambda).
\tag{JS.35}
$$

There is one sequence of common finite instruments attaining this
limit, with all properties of Theorem 6.1. No fixed-$s$ estimate is
transferred uniformly to obtain it.

Proof. Choose a maximizing failure measure $\nu_*$ at $\lambda$,
with at most five atoms, by Lemma 4.2. If its cost is strictly below
$\lambda$, Theorems 5.1 and 6.1 already supply recovery. The following
selection also handles equality of cost, including the saturation
boundary.

Let $c_{\min}=\min_{[0,U]}c_*>0$, and put

$$
B=\frac{\mu(1+U+1/\beta)}{c_{\min}},\quad K_B=B^2/4,\quad
D_\lambda=\lambda-C_{\rm end}>0,\quad\lambda_n=q_nt_n,\\
\epsilon_n=\frac{2(|\lambda_n-\lambda|+K_B/t_n)}{D_\lambda},\qquad
\nu_n=(1-\epsilon_n)\nu_*+\epsilon_n\nu_0.
\tag{JS.36}
$$

For sufficiently large $n$, $0<\epsilon_n<1$ and $t_n\to\infty$.
The covariance is still $M$, and
$C_{\nu_n}\le\lambda-\epsilon_nD_\lambda$.
For every covariance-admissible measure, (JS.23)'s PSD matrix has
trace at most $B$, since $z^2\le U$, $w^2\le1/\beta$ and mass is
$\mu$. Thus all entries are uniformly bounded. For $t_n\ge16B$,
(JS.24)'s radicals are positive and its four weights are positive:
$m_t\ge15/16$, $X_t,Y_t\ge15/16$, and the sum of the three absolute
corrections to $m_t/4$ is at most $B/t_n\le1/16$.
Equation (JS.27) also gives uniformly

$$
t_ne_{t_n}\le C_{\nu_n}+K_B/t_n
\le\lambda-2|\lambda_n-\lambda|-K_B/t_n\le\lambda_n.
\tag{JS.37}
$$

This is the required finite contrast margin for the prescribed
sequence; a cost equality in the limiting problem is never used as a
finite strict margin. The rare support can be the fixed union of
$\nu_*$ and $\nu_0$, at most seven points, with varying weights.
Their exact failure covariance and moment repair hold at every finite
$n$. Their actual height differences and bulk limits in the proof of
Theorem 5.1 converge to those of $\nu_*$. Hence their common
full-label TV tends to $B_0+\Phi(\lambda)$.

There are at most seven rare, four bulk, two high and two fair
complement labels in this construction. These fifteen labels are an
upper construction count, not a minimum alphabet assertion. Zero
weights may be omitted. An exact-contrast attenuation can double the
count without changing the limit or other properties; the original
inequality needs no attenuation.

For the reverse bound use Theorem 4.3 on maximizing or asymptotically
maximizing original instruments. FA72 supplies finite attainment when
feasible. Alternatively choose full-label values within $1/n$ of the
supremum; compactness then gives the same upper bound. This matches
the explicit recovery and proves (JS.35). $\square$

## 8. The evaluated saturation constant and its sharp equality cases

**Definition 8.1 (explicit source radicals).** Put

$$
\begin{gathered}
u_f=\frac{-2z_f}{d_f+L_f},\qquad 0<u_f<1,\\
a_+=\frac{\alpha V+\beta Wu_f^2}{1+u_f^2},\qquad
a_-=\frac{\alpha Vu_f^2+\beta W}{1+u_f^2},\\
x_+=\frac{V}{\alpha V+\beta Wu_f^2},\qquad
x_-=\frac{Vu_f^2}{\alpha Vu_f^2+\beta W},\\
\boxed{C_{\rm sat}=a_+F_c(x_+)+a_-F_c(x_-).}
\end{gathered}
\tag{JS.38}
$$

All denominators are strictly positive, and $0<x_-<r<x_+<U$. In particular (JS.38) is a rational/radical
evaluation, with no remaining root selection, minimization or SDP.

**Theorem 8.2 (sharp final saturation boundary).** One has

$$
C_{\rm sat}>C_{\rm end},\qquad
\Phi(\lambda)=\gamma_f\quad\Longleftrightarrow\quad
\lambda\ge C_{\rm sat}.
\tag{JS.39}
$$

Every covariance-admissible failure measure with objective $\gamma_f$
has exactly cost $C_{\rm sat}$. Its whitened effects are the two
spectral projections of $\Xi$, up to proportional splitting and
simultaneous reversal of the ellipse coordinates.

Proof. On coordinates $1,2$ put $M_2=\operatorname{diag}(m_1,m_2)$
and whiten each rank-one failure effect as
$E(z,w)=M_2^{-1/2}nn^TM_2^{-1/2}$. The covariance constraint is
$\int E d\nu=I_2$, and $k=\operatorname{tr}(E\Xi)$.
The eigenvalues of $\Xi$ are $\gamma_f>0$ and
$-b_f=-(L_f+d_f)/2<0$, both simple. Thus

$$
k_+\le\operatorname{tr}(E\Xi_+),\qquad
\int k_+d\nu\le\operatorname{tr}\Xi_+=\gamma_f.
\tag{JS.40}
$$

In the spectral basis write the two nonnegative overlaps of a nonzero
rank-one $E$ as $a,b$. The pointwise inequality is
$\max(\gamma_f a-b_fb,0)\le\gamma_f a$.
It is an equality exactly when $a=0$ or $b=0$. A nonzero direction
with both overlaps positive gives strict inequality, including a
zero-$k$ direction. Equality of the integral forces equality almost
everywhere, since the gap is nonnegative. Therefore every nonzero
failure outcome lies on one of the two spectral lines, and their
integrated whitened effects are exactly the two projections.

Choose real unit eigenvectors

$$
e_+=(u_f,-1)^T/\sqrt{1+u_f^2},\qquad
e_-=(1,u_f)^T/\sqrt{1+u_f^2}.
\tag{JS.41}
$$

They have the stated signs since $z_f<0$; $0<u_f<1$ follows from
$L_f>2|z_f|$ and $d_f>0$. For either spectral vector $e=(e_1,e_2)$
define

$$
a_e=\alpha Ve_2^2+\beta We_1^2,\qquad
z_e=-\sqrt V e_2/\sqrt{a_e},\qquad
w_e=\sqrt W e_1/\sqrt{a_e}.
\tag{JS.42}
$$

These points are on the ellipse and satisfy
$n(z_e,w_e)=M_2^{1/2}e/\sqrt{a_e}$.
The two-atom measure of masses $a_{e_+}=a_+$ and $a_{e_-}=a_-$
therefore has covariance $M$, objective $\gamma_f$, squared $z$
coordinates $x_+,x_-$, and exactly cost (JS.38).

Conversely a whitened spectral line fixes the ratio $z:w$.
Ellipse normalization fixes its two possible points, differing only
by simultaneous reversal, and fixes $z^2=x_+$ or $x_-$.
The integrated whitened projection has coefficient one, which forces
total mass $a_+$ or $a_-$ on that line. Splitting or simultaneous
reversal cannot change its cost. Thus every failure-optimal measure
has cost precisely $C_{\rm sat}$. Compact attainment in Lemma 4.2
makes $\Phi(\lambda)<\gamma_f$ for every smaller admissible budget,
not merely nonattainment by a selected family.

Finally $a_++a_-=\mu$ and $a_+x_++a_-x_-=V$.
The strict inequalities $x_-<r<x_+$ follow directly from $0<u_f<1$
and $\beta W>0$; both coordinates are strictly below $U$.
Integrating Lemma 3.1's strictly supporting tangent over these two
positive masses yields $C_{\rm sat}>\mu F_c(r)=C_{\rm end}$.
The spectral measure gives the remaining implication in (JS.39).
$\square$

**Corollary 8.3 (evaluated original limiting regime).** Under the
sequences of Theorem 7.1,

$$
\lim_n\mathcal T_{A_n}(s_0(1-q_n))=T_0
\quad\Longleftrightarrow\quad\lambda\ge C_{\rm sat}.
\tag{JS.43}
$$

In particular equality at $\lambda=C_{\rm sat}$ has genuine common
finite-rate recovery along every prescribed product sequence.

Proof. Combine (JS.35), (JS.39) and $B_0+\gamma_f=T_0$.
For $\lambda=C_{\rm sat}$ the spectral failure measure has no strict
cost margin. Equations (JS.36)--(JS.37) supply that margin at each
finite budget while converging to its value. The output, error,
contrast and acquired-cost identities are all those of the same
instrument in Theorem 6.1. $\square$

## 9. The critical endpoint and the unevaluated strict interior

**Theorem 9.1 (critical full-record limit).** Along any feasible
sequence $q_n\to0$, $q_nt_n\to C_{\rm end}$, every full actual-label
instrument has TV tending to $B_0$. Also
$q\,t_{\min}(s_0(1-q))\to C_{\rm end}$.

Proof. The strict tangent gap
$F_c(x)-F_c(r)-F_c'(r)(x-r)$ is continuous, positive away from $r$,
and has $\nu_n$ integral at most $q_nt_n-C_{\rm end}$.
Hence $\nu_n$ concentrates at $z^2=r$. Lemma 3.1 makes all its
limiting failure differences negative, so
$\int|k|d\nu_n\to d_f$. The live laws still converge to uniform
corners by Theorem 4.3.

The actual grouping loss is bounded by

$$
0\le\int|f|dP_n+\int|k|d\nu_n-
\int|f+vk|dP_n
\le2\int\min(|f|,v|k|)dP_n.
\tag{JS.44}
$$

Choose an open radial neighborhood $O$ of $r$ whose closure misses
$1$. The last bound is at most
$2(\|f\|_\infty P_n\{z^2\in O\}
+\|k\|_\infty\nu_n\{z^2\notin O\})$, which tends to zero.
This estimate retains each actual label's own multiplier.
Equation (JS.12) now gives the limit
$(H_{\rm live}+S_{\rm corner}+d_f)/2=B_0$ for every full-label
instrument. Coarsenings have only the corresponding upper-limit bound.

Corollary 3.2 gives the strict lower threshold bound.
For every fixed $\lambda>C_{\rm end}$, apply Theorem 5.1 with
$\nu_0$ and $t=\lambda/q$ for all sufficiently small $q$.
This gives $\limsup q t_{\min}\le\lambda$; let
$\lambda\downarrow C_{\rm end}$ to match the lower bound.
FA73 supplies threshold attainment, so its optimizing classes also
have the critical TV limit. These are the credited WE critical
conclusions, here established in the notation of the joint theorem.
$\square$

**Theorem 9.2 (continuous strict transition and attained chord).**
On $[C_{\rm end},C_{\rm sat}]$ the function $\Phi$ is continuous,
concave and strictly increasing, with endpoint values $0,\gamma_f$.
For every $\lambda$ in this interval,

$$
\Phi(\lambda)\ge
\gamma_f\frac{\lambda-C_{\rm end}}{C_{\rm sat}-C_{\rm end}}.
\tag{JS.45}
$$

Thus for $C_{\rm end}<\lambda<C_{\rm sat}$ the original joint limit
is strictly between $B_0$ and $T_0$. Its interior scalar value is not
evaluated by (JS.20) or (JS.45).

Proof. Budget inclusion makes $\Phi$ nondecreasing. Mixing two
covariance-admissible failure measures preserves covariance and mixes
both cost and objective, proving concavity. The mixture of $\nu_0$
and the spectral measure, with spectral weight
$(\lambda-C_{\rm end})/(C_{\rm sat}-C_{\rm end})$, proves (JS.45).
For every interior product this mixture has a common original recovery
by Theorem 7.1, including strict-cost perturbations when necessary.
It is an attainable limiting lower bound, not a combination of
incompatible records.

Compactness proves right continuity at $C_{\rm end}$: any optimizing
sequence with costs decreasing to it has subsequential limits on
$z^2=r$, where $k_+=0$. Concavity of the finite function gives
continuity at every larger interior budget. At $C_{\rm sat}$ the
chord tends to $\gamma_f$ and (JS.40) bounds it above, also proving
continuity there. The chord is positive above $C_{\rm end}$ and
Theorem 8.2 gives a strict gap below $\gamma_f$ until $C_{\rm sat}$.
If two distinct budgets below $C_{\rm sat}$ had equal values,
concavity would force all later secant slopes to be nonpositive;
monotonicity would force them to be zero. This contradicts the larger
value at $C_{\rm sat}$. The same endpoint inequalities handle a pair
containing either endpoint. Therefore increase is strict throughout
the stated interval, and $\Phi=\gamma_f$ thereafter. No chord
equality, strict concavity, differentiability, interior contact pattern
or optimizer count follows. $\square$

## 10. Existing credit and remaining original obligations

**Convention 10.1 (attribution and increment).** CG supplies the source
root, ranks, normalization and original minimax/support premises.
JR34--40 supplies the sharp worst-history acquired curve and plateau;
JR42--45 supplies supported equality, strong TV and weak real-PSD
reduction/finite realization. JR50--57 supplies the spectral plateau,
four-slack dual, endpoint asymptotics and pre-cap results. RC58--66
already supplies the complete static residual/contact curve, its
three-to-four real-null transition and gluing. Those static questions
retain their resolved conditional status; their support pattern is
not transferred to finite activity.

FA68--75 supplies the prescribed-path minimum for arbitrary TP survivor
controls, double rigidity and exact capacity, chronological constructors,
isolated strong threshold and complete strong value, weak Toeplitz
SDP/finite attainment, weak threshold/logarithmic order, strict finite
TV deficit, fixed-$s$ exponential deficit order and full-output/B14
slack. CA's no-rank-one/real-face and IR's image/null mechanisms enter
through these sources. Their existing literature and library
attributions retain their stated conditional scopes; no additional
external or kernel authentication is asserted.

WE denotes the supplied companion titled *Weak finite-activity
endpoint: an evaluated feasibility constant and the full-record limit*.
Its evaluated $C_{\rm end}$, strict tangent, uniform bounded additive
threshold strip, $O(q)$ logarithmic refinement and universal critical
TV limit are existing credit. Lemma 3.1 and Theorem 9.1 provide the
supporting deductions used here; they are not counted as new relative
to WE. The additional source-specific results are the full-class
limiting correspondence with exact finite moment repair, common
recovery along every prescribed finite product sequence, evaluated
strict boundary $C_{\rm sat}$ and its failure-optimal cost uniqueness,
exact final saturated regime, and qualitative strict interior
transition with an attainable chord. These are conditional repository
derivations, with no worldwide priority or absence claim.

**Definition 10.2 (remaining mathematics and native bridge).** The
scalar values of $\Phi$ on $(C_{\rm end},C_{\rm sat})$, their contacts,
weights, possible interior transitions and quantitative approach to
saturation remain unresolved. The compact formula is a correspondence
theorem, not an evaluation of this entire crossover. The full finite-$s$
weak scalar $(s,A)$ frontier, exact finite threshold and additive
correction, finite-budget optimizer/contact structure and optimal
TV-deficit coefficients also remain unresolved beyond supplied credit.
No $\lambda=\infty$ theorem or uniform fixed-$s$ transfer is asserted.

FA74's strict deficit remains at every finite feasible activity.
Equality to $T_0$ above is a joint limiting result, not finite-$A$
attainment of the unbudgeted endpoint TV. At $q=0$ no finite budget
is feasible. Rare-label survival stays positive at every finite
parameter; no singular limiting failure is enacted at a finite budget.
Construction counts do not bound minimum physical alphabets or imply
whole-instrument/five-mode uniqueness.

All native services remain `ASSUMED-UNVERIFIED`: lawful access to the
sole unknown specimen, calibrated D/T/S operations and actual label
generation, joint coherent storage of every accessible share, controlled
whole-fibre decoding, acquisition duration and placement on the same
aligned clock, native first absorption at $6+u$, no later positive-carrier
action, terminal live output, and original stopped archives,
source/epoch, controller and permission semantics. Mathematical CP maps
and chronological instruments grant none of these services or extra
time. OriginalControl is geometric, not an actuator; the admitted
probability-changing noncommuting controls preclude an exhaustive
Schur or diagonal menu. No spectral-energy/acquired-mass/ML-error
identification, physical dimension/SO3 assertion, general NN or empirical
ML theorem, native permission, Lean/kernel/frozen certification or
programme completion is claimed. The full original native/joint-height/
clock and broader quantum-first programme remains active.

[JR]: FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD.md
[RC]: FIB_NATIVE_COMPLETE_CONTINUATION_RESIDUAL_CONTACT_CURVE.md
[FA]: FIB_NATIVE_COMPLETE_CONTINUATION_FINITE_ACTIVITY_FRONTIER.md

## 追加锚（本行以下为增补区）

## 11. Global interpolation by a strictly convex scalar selection

**Convention 11.1 (conditional scope and exact dictionary).** Sections
11–18 retain every assumption and comparison-class clause of §§1–2.
In particular the CG root, its isolation/Jacobian certificate, exact
ranks, root TP identity and original minimax/support identification
remain `ASSUMED-UNVERIFIED`. The results are ordinary conditional
mathematics. The amplitude enclosures used by the suppliers remain
conditional inequalities; no rational centre certifies these premises.

Let [TC] denote *Joint failure records: three-line structure and the
exact initial law*, and [SC] denote *Joint interior records: support
obstruction and saturation curvature*. Their global cost convexity,
unique optimizing line measure, at-most-three-line structure, strict
concavity, projective certificate, scalar three-line family, selected
initial/final branches and initial/saturation coefficients are suppliers,
not additional results here. WE retains ownership of the universal
critical full-record limit. Sections 7–9 retain ownership of limiting
correspondence, prescribed-sequence recovery, evaluated saturation and
spectral equality. The additional assertions below are scalar selection
across the intervening limiting budgets, quantitative uniform estimates
and a simultaneous finite-activity spectral layer.

To distinguish the off-diagonal magnitude from both the source amplitude
$b$ and §8's negative spectral eigenvalue magnitude, put

$$
b_{\rm off}=-z_f>0,\qquad
p_z=d_f^2/L_f^2,\qquad p_s=(1+d_f/L_f)/2=1/(1+u_f^2).
\tag{JS.46}
$$

Here $u_f$ has exactly Definition 8.1's spectral meaning. The endpoint
radial constant is $r=V/\mu$, not this $u_f$. In notation in which the
live quadratic is $\ell$, the failure quadratic is $f$, the radial
constant is $u_f$ and the off-diagonal magnitude is $b_f$, the exact
translation to this volume is respectively $f(z,w)$, $k(z,w)$,
$r$ and $b_{\rm off}$. The constant denoted $\nu$ in that notation
is $\mu/c_*(r)$; it is distinct from this volume's failure measure
$d\nu=v\,dP$. Its $(\mu_f,V_f,W_f)$ are $(\mu,V,W)$.
The normalization matrix remains $L=\operatorname{diag}(s_0,1,1)$;
a terminal decoder effect is a different operator $B^\dagger B$.

For $0\le p\le1$ define the same scalars as TC.2 by

$$
\begin{aligned}
a(p)&=\beta W+(\alpha V-\beta W)p,& x(p)&=Vp/a(p),\\
J(p)&=a(p)F_c(x(p)),&
g_+(p)&=2b_{\rm off}\sqrt{p(1-p)}-d_f(1-p),\\
C(p)&=J(p)+J(1-p),&
D_J(p,q)&=J(p)-J(q)-(p-q)J'(q).
\end{aligned}
\tag{JS.47}
$$

All denominators are positive through the axes. SC Theorem 2.1 and
TC Lemma 2.1 give strict convexity of $F_c$ on $[0,U]$, with positive
second derivative in the interior. Consequently
$J''(p)=V^2(\beta W)^2F_c''(x(p))/a(p)^3>0$ for $0<p<1$.
The source inequality $d_f>2b_{\rm off}$ is (JS.19); hence
$1/2<p_z<p_s<1$, $g_+>0$ on $(p_z,1)$, and its unique maximum
is $g_+(p_s)=\gamma_f$. Also
$2J(1/2)=C_{\rm end}$ and $C(p_s)=C_{\rm sat}$.

The physical change of coordinates is essential. For a real unit
vector $e=(e_1,e_2)^T$ and whitened mass $\omega$, its actual failure
effect, ellipse point and failure-measure mass are

$$
\begin{gathered}
B_e=\omega M_2^{1/2}ee^TM_2^{1/2},\quad M_2=\operatorname{diag}(m_1,m_2),\\
z_e=-\sqrt V e_2/\sqrt{a(e_2^2)},\quad
w_e=\sqrt W e_1/\sqrt{a(e_2^2)},\quad
\nu_e=\omega a(e_2^2),\quad
n(z_e,w_e)=M_2^{1/2}e/\sqrt{a(e_2^2)}.
\end{gathered}
\tag{JS.48}
$$

Thus covariance is $\sum\omega ee^T=I_2$, the cost is
$\sum\omega J(e_2^2)$, and the objective is
$\sum\omega(e^T\Xi e)_+$. The unwhitened effects are never
replaced by $\omega ee^T$. Antipodes or proportional splittings do
not change these quantities. This is precisely TC.3–4/SC.15–16.

**Definition 11.2 (selected scalar cost).** For $0<\varpi<\gamma_f$
put

$$
\begin{gathered}
y_\varpi(x)=\frac{(\varpi+d_fx)^2}{4b_{\rm off}^2x},\qquad
x_-(\varpi)=\varpi/L_f,\\
x_+(\varpi)=\frac{2b_{\rm off}^2-d_f\varpi+
2b_{\rm off}\sqrt{b_{\rm off}^2-d_f\varpi-\varpi^2}}{L_f^2},\\
\mathcal K(x,y)=(x+y)J\!\left(\frac y{x+y}\right)
 +(2-x-y)J\!\left(\frac{1-y}{2-x-y}\right),\qquad
\phi_\varpi(x)=\mathcal K(x,y_\varpi(x)).
\end{gathered}
\tag{JS.49}
$$

The interval is $[x_-(\varpi),x_+(\varpi)]$. Its right endpoint is
the larger intersection with $x+y=1$; its left endpoint is the
restriction to positive-line coordinate $p\le p_s$, rather than
the other triangular intersection. For derivative evaluation put
$m=x+y$, $p=y/m$, $q=(1-y)/(2-m)$ and $\Delta_J=J'(p)-J'(q)$.
Then

$$
\phi_\varpi'(x)=D_J(p,q)-p\Delta_J+
[D_J(p,q)+(1-p)\Delta_J]
\frac{d_f^2-\varpi^2/x^2}{4b_{\rm off}^2}.
\tag{JS.50}
$$

**Theorem 11.3 (unique clamped root and global limiting value).**
$\phi_\varpi'$ is strictly increasing on its interval and is negative
at its left endpoint. Define $x_*(\varpi)$ as $x_+(\varpi)$ when
$\phi_\varpi'(x_+)\le0$, and otherwise as the unique zero of
(JS.50) in $(x_-,x_+)$. Set

$$
\lambda_*(\varpi)=\mathcal K(x_*(\varpi),y_\varpi(x_*(\varpi))).
\tag{JS.51}
$$

This function is continuous and strictly increasing, with continuous
endpoint values $\lambda_*(0)=C_{\rm end}$ and
$\lambda_*(\gamma_f)=C_{\rm sat}$. Throughout the interval,

$$
\Phi(\lambda_*(\varpi))=\varpi,\qquad
\mathcal R(\lambda_*(\varpi))=B_0+\varpi,
\tag{JS.52}
$$

where $\mathcal R$ is the original prescribed-product limit in
Theorem 7.1, with the critical endpoint supplied by Theorem 9.1.
Thus every strict-interior limiting budget has a unique
$\lambda_*(\varpi)=\lambda$ selection, followed by one strictly
monotone clamped root. There is no remaining measure, instrument or
SDP optimization in this specification.

Proof. TC Theorem 3.1 supplies one positive line in every interior
optimizer. Write its whitened effect as

$$
X=\begin{pmatrix}x&-\sqrt{xy}\\-\sqrt{xy}&y\end{pmatrix},
\quad m=x+y\le1,\quad p=y/m>p_z.
\tag{JS.53}
$$

Its positive contribution is
$P_+(x,y)=-d_fx+2b_{\rm off}\sqrt{xy}=mg_+(p)$.
The complement has trace $2-m$ and second diagonal proportion $q$.
Strict Jensen for $J$ bounds its cost below by $(2-m)J(q)$.
The flat two-sign complement of §12 realizes this bound; because
$q<1/2$ both its expectations are strictly negative. Thus
$\mathcal K$ is the exact cost for this positive effect.

Coordinates $p>p_s$ can be excluded at fixed positive contribution.
At fixed $m$, decreasing $p$ to $p_s$ raises $g_+$ and lowers cost,
since $\partial_p\mathcal K=m[J'(p)-J'(q)]>0$.
Then decrease $m$ to restore $mg_+=\varpi$. This lowers cost too,
since $\partial_m\mathcal K=D_J(p,q)>0$. Hence an optimum may
be sought with $p_z<p\le p_s$. The equation $P_+=\varpi$ gives
$y=y_\varpi(x)$; $m\le1$ and $p\le p_s$ give exactly (JS.49)'s
interval. In particular $0<x<y<1$ there.

Each perspective term in $\mathcal K$ has PSD Hessian. Their null
directions are $(x,y)$ and $(1-x,1-y)$, which differ when $x<y$.
Therefore $\nabla^2\mathcal K\succ0$ on this region. Direct
differentiation gives
$\mathcal K_y=D_J+(1-p)\Delta_J>0$ and
$y_\varpi''=\varpi^2/(2b_{\rm off}^2x^3)>0$. Hence

$$
\phi_\varpi''=(1,y_\varpi')\nabla^2\mathcal K(1,y_\varpi')^T
 +\mathcal K_y y_\varpi''>0.
\tag{JS.54}
$$

At $x_-$, $p=p_s$ and $y_\varpi'=-1$, so
$\phi_\varpi'=-\Delta_J<0$. This proves the selected-root rule.

It also supplies a global certificate, rather than only stationarity.
At an interior root take $\eta=P_{+,y}/\mathcal K_y>0$;
the constrained derivative gives $\nabla P_+=\eta\nabla\mathcal K$.
At the triangular edge take

$$
\eta=g_+'(p)/C'(p)>0,\qquad
\chi=g_+(p)-\eta D_J(p,1-p)\ge0.
\tag{JS.55}
$$

The last sign is the selected edge derivative sign, as proved in §12.
Here $\nabla P_+-\eta\nabla\mathcal K=\chi(1,1)$.
Concavity of $P_+$ and convexity of $\mathcal K$ therefore give,
over the whole nonnegative triangle $x+y\le1$,

$$
P_+-\eta\mathcal K
\le P_{+,*}-\eta\mathcal K_*+\chi(x+y-1)
\le P_{+,*}-\eta\mathcal K_*.
\tag{JS.56}
$$

For an interior root use $\chi=0$. In particular no positive effect
of cost at most $\mathcal K_*$ improves $\varpi$. The exact complement
attains this bound. Together with TC's whole-class structure this
proves (JS.52), not merely optimality within a proposed family.

To see strict increase, scale the positive effect at $\varpi_2$ by
$\varpi_1/\varpi_2$ for $0<\varpi_1<\varpi_2$. Its coordinate
$p$ stays fixed, its contribution becomes $\varpi_1$, and its cost
strictly decreases by $\partial_m\mathcal K=D_J>0$. The minimum
cost at $\varpi_1$ is no larger than that strictly smaller cost.
Continuous dependence of a unique minimum on its compact interval
gives continuity in the open range. As $\varpi\downarrow0$, scaling
the spectral line to vanishing mass gives cost tending to
$2J(1/2)=C_{\rm end}$; the opposite bound is Lemma 3.1. As
$\varpi\uparrow\gamma_f$, the spectral bound forces $m\to1$ and
$p\to p_s$, giving $C_{\rm sat}$. These prove both endpoint
extensions and coverage. The spectral and critical values themselves
are the credited §§8–9 values. $\square$

## 12. Physical two/three-ray criterion and reconciliation with TC

**Theorem 12.1 (pointwise minimum and all possible edge contacts).**
For $0<\varpi<\gamma_f$, the minimum number of nonzero physical
failure rays in an optimizing limiting measure at
$\lambda=\lambda_*(\varpi)$ is two if
$\phi_\varpi'(x_+)\le0$ and three if this derivative is positive.
At $C_{\rm end}$ and at/above $C_{\rm sat}$ it is two.

For explicit effects use $x=x_*$, $y=y_\varpi(x)$, $m=x+y$,
$p=y/m$, $q=(1-y)/(2-m)$ and

$$
\begin{gathered}
e_P=(\sqrt{1-p},-\sqrt p)^T,\qquad
e_\pm=(\sqrt{1-q},\pm\sqrt q)^T,\\
\omega_\pm=\frac12\left[2-m\pm
 \frac{\sqrt{xy}}{\sqrt{q(1-q)}}\right],\\
B_P=mM_2^{1/2}e_Pe_P^TM_2^{1/2},\qquad
B_\pm=\omega_\pm M_2^{1/2}e_\pm e_\pm^TM_2^{1/2}.
\end{gathered}
\tag{JS.57}
$$

Zero weights are omitted. These effects sum to $M_2$. Every possible
edge/interior change lies among the zeros on $(p_z,p_s)$ of

$$
E_{\rm edge}(p)=g_+(p)C'(p)-g_+'(p)D_J(p,1-p).
\tag{JS.58}
$$

This zero set is finite and nonempty. No singleton, simple-zero,
ordered-root or actual finite-acquisition-alphabet assertion is made.

Proof. The complement of (JS.53) has diagonals $1-x,1-y$ and
cross entry $\sqrt{xy}$. Formula (JS.57) matches all these entries.
Its determinant is $1-m$. For $m<1$ both $\omega_\pm$ are positive;
for $m=1$ the minus weight vanishes. Both negative-line expectations
are strictly negative because $q<1/2$ and $d_f>2b_{\rm off}$.
Strict Jensen forces this same $q$ in every cost-minimal complement.
Two positive rank-one whitened effects summing to $I_2$ must be
orthogonal projections with masses one. Thus $m<1$ cannot have an
alternative two-ray optimum. Equivalently use TC's unique optimizing
line measure. For $m=1$ (JS.57) is exactly that orthogonal pair.
Rank-two covariance excludes one ray. At critical cost strict Jensen
forces $p=1/2$ and opposite cross signs; at spectral cost the equality
classification of Theorem 8.2 applies. These give the endpoint counts.

At an edge point $x=1-p,y=p$ the contour derivative is
$y_\varpi'=-P_{+,x}/P_{+,y}$, so direct substitution yields

$$
\phi_\varpi'(x_+)=-E_{\rm edge}(p)/P_{+,y},\qquad
c_p=-\frac{\sqrt{p(1-p)}}{C'(p)}E_{\rm edge}(p).
\tag{JS.59}
$$

Here $c_p$ is exactly TC.8's dual cross entry, and $P_{+,y}>0$,
$C'(p)>0$. Thus the clamped edge rule, $E_{\rm edge}\ge0$ and
TC's necessary-and-sufficient $c_p\le0$ are the same test.
Equation (JS.55)'s $\chi\ge0$ is the same sign once more.

The functions are real analytic on a neighborhood of $[p_z,p_s]$:
all radial arguments remain strictly between their axes there.
At $p_z$, $E_{\rm edge}=-g_+'D_J<0$; at $p_s$ it is
$\gamma_f C'>0$. Continuity gives at least one zero. An infinite
zero set in this compact interval would have an accumulation point
in its analytic neighborhood and force the function to vanish
identically, contradicting these endpoint signs. Hence the set is
finite, including possible multiple roots or roots without a sign
change. $\square$

**Proposition 12.2 (the selected root closes a selection gap, not a
zero inventory).** At an interior root of Theorem 11.3 the exact
parameters $m,p,q$ satisfy TC.7 and TC.12–13, namely

$$
m=\frac{1-2q}{p-q},\qquad
g_+'(p)D_J(p,q)-g_+(p)[J'(p)-J'(q)]=0,
\quad \lambda_*(\varpi)=mJ(p)+(2-m)J(q),\quad
\varpi=mg_+(p).
\tag{JS.60}
$$

Proof. The diagonal identity is $mp+(2-m)q=1$. In coordinates
$(m,p)$ the derivatives of the cost are $D_J(p,q)$ and
$m[J'(p)-J'(q)]$; those of the contribution are $g_+(p)$ and
$mg_+'(p)$. Their parallel gradients give (JS.60). Cross cancellation
gives exactly TC.7's two negative masses. Conversely TC's feasible
three-line stationary family has these moments and contribution,
so its cost-minimizing representative is the unique root already
selected here. At $m=1$, (JS.59) gives TC's projective test.

TC Definition 10.2 separately leaves arbitrary-budget branch selection
and the full inventory/sign intervals of the $c_p$ zeros unresolved.
Equations (JS.49)–(JS.52) supply the first by a globally justified
monotone scalar inversion. They do not supply the second: the finite
zero set (JS.58) has not been isolated or sorted in the conditional
source field. TC's algebraically selected initial branch, its global
three-line equations and its selected final inverse are reused exactly;
none is counted again as new. This distinguishes a unique optimizer
at each budget from uniqueness of a support transition. $\square$

## 13. Same-label capacity separation and quantitative corner control

**Lemma 13.1 (capacity and remaining live measures).** On the actual
label space of any original finite-budget competitor put
$\zeta=tq$, $z_\nu=\int F_c(z^2)d\nu$ and

$$
dP_{\rm cap}=\frac{d\nu}{tc_*(z^2)},\qquad
dP_{\rm rem}=dP-dP_{\rm cap}\ge0,\qquad
E_{\rm rem}=\int H(z^2)dP_{\rm rem}.
\tag{JS.61}
$$

Then, uniformly over that whole class,

$$
C_{\rm end}\le z_\nu\le\zeta,\qquad
E_{\rm rem}\le(\zeta-z_\nu)/t,\qquad
P_{\rm cap}(\mathcal E)\le\mu/(tc_{\min}),\quad c_{\min}=\min c_*>0,
\tag{JS.62}
$$

and for a source constant $K$,

$$
\left|\int|f|dP-S_{\rm corner}\right|
\le K\left[t^{-1}+\sqrt{(\zeta-z_\nu)/t}\right].
\tag{JS.63}
$$

This is an analytic decomposition on existing labels. It generates no
new record, report, readable Kraus index or free physical refinement.

Proof. Capacity (JS.9) gives positivity in (JS.61), and
$\int H\,dP_{\rm cap}=z_\nu/t$. Subtract this from (JS.11);
Lemma 3.1 gives the other cost bound. Fixed failure mass gives the
last inequality in (JS.62).

Push a remaining point to its nearest signed corner. With
$u=|z|-1$, the ellipse gives

$$
\bigl||w|-1\bigr|
\le\frac{\alpha}{\beta}(1+\alpha^{-1/2})|u|,
\qquad \int u^2dP_{\rm rem}=2E_{\rm rem}.
\tag{JS.64}
$$

The lost capacity mass has every moment $O(t^{-1})$. Thus the
remaining total and three cross moments differ from those of $I_3$
by $O(t^{-1})$. After the push their errors are
$O(t^{-1}+\sqrt{E_{\rm rem}})$ by Cauchy–Schwarz. Four-sign Fourier
inversion fixes each pushed mass to
$1/4+O(t^{-1}+\sqrt{E_{\rm rem}})$. The function $|f|$ is Lipschitz
on the compact ellipse, giving (JS.63). At an axis choose either sign;
there $|u|$ is bounded away from zero unless already at a corner,
so the same estimate includes that mass. $\square$

## 14. Critical every-instrument strip and sub-spectral uniform rate

**Theorem 14.1 (critical strip for every complete actual record).**
There are source constants $K,\epsilon_0,t_*>0$ such that every
feasible original instrument with $t\ge t_*$ and
$0\le\epsilon=tq-C_{\rm end}\le\epsilon_0$ has

$$
|T_{\rm instr}-B_0|\le K(\epsilon+t^{-1}).
\tag{JS.65}
$$

This strengthens the WE/§9 universal critical limit quantitatively.
The double-sided statement concerns its entire generated acquisition
record; a subsequent coarsening has only the corresponding upper bound.

Proof. Let $\epsilon_\nu=z_\nu-C_{\rm end}$ and
$\Delta_\nu=\epsilon-\epsilon_\nu\ge0$. The strict tangent gap
$F_c(x)-F_c(r)-F_c'(r)(x-r)$ has integral $\epsilon_\nu$ against
$\nu$. Choose a fixed open radial neighborhood $O$ of $r$, whose
closure misses $1$, in which every sign of $k(z,w)$ is strictly
negative. Such a choice exists by (JS.18)–(JS.19). Its complementary
tangent gap has a positive minimum. Therefore

$$
\nu\{z^2\notin O\}\le K\epsilon_\nu,
\qquad 0\le\int|k|d\nu-d_f\le K\epsilon_\nu.
\tag{JS.66}
$$

The latter uses $\int k\,d\nu=-d_f$ and bounds $k_+$ outside $O$.
Since $H$ has a positive minimum on $\overline O$, (JS.61)–(JS.62)
also give $P\{z^2\in O\}\le K(1+\Delta_\nu)/t$.
The exact actual-label triangle loss (JS.44) is at most
$2[\|f\|_\infty P(O)+\|k\|_\infty\nu(O^c)]$.
Using (JS.63), (JS.66) and (JS.12) on this same record yields

$$
|T_{\rm instr}-B_0|
\le K\left[\epsilon_\nu+
\sqrt{\Delta_\nu/t}+t^{-1}\right].
\tag{JS.67}
$$

The bounded $\Delta_\nu/t$ term was absorbed into $K/t$.
Now $\sqrt{x/t}\le(x+t^{-1})/2$ proves (JS.65). No optimizing
assumption, chosen time law or hidden record refinement entered.
$\square$

**Theorem 14.2 (uniform value error below the spectral threshold).**
Fix $C_{\rm end}<\bar\zeta<C_{\rm sat}$. Uniformly over all actually
feasible weak points with $C_{\rm end}\le\zeta=t(1-s/s_0)\le\bar\zeta$,

$$
\mathcal T_{\log(1+t)}(s)=B_0+\Phi(\zeta)+O_{\bar\zeta}(t^{-1}).
\tag{JS.68}
$$

Proof. The triangle inequality and Lemma 13.1 imply for each competitor

$$
T_{\rm instr}-[B_0+\Phi(\zeta)]
\le-[\Phi(\zeta)-\Phi(z_\nu)]
 +K/t+K\sqrt{(\zeta-z_\nu)/t}.
\tag{JS.69}
$$

Choose $\zeta'\in(\bar\zeta,C_{\rm sat})$. Concavity and strict
increase give the positive lower secant
$\Phi(\zeta)-\Phi(z_\nu)\ge m_{\bar\zeta}(\zeta-z_\nu)$,
where $m_{\bar\zeta}=[\Phi(\zeta')-\Phi(\bar\zeta)]/
(\zeta'-\bar\zeta)>0$. Completing the square in
$\sqrt{\zeta-z_\nu}$ bounds (JS.69) by $K'/t$.

For the lower bound, TC Theorem 8.1 supplies the finite right slope
$S_0=\Phi'_+(C_{\rm end})$; concavity gives the global Lipschitz bound
$0\le\Phi(b)-\Phi(a)\le S_0(b-a)$ on this interval.
All covariance measures have the uniform repair bound $B,K_B$ in
(JS.36). Choose a fixed $D>K_B$. If
$\zeta-C_{\rm end}\ge D/t$, select the optimizing failure measure
at $\zeta-D/t$ (including the critical measure at equality) and
apply the exact four-label repair (JS.23)–(JS.27).
Its normalized contrast deficit obeys
$te_t\le\zeta-D/t+K_B/t\le\zeta$. The rare weights, all moment
entries and grouping loss are uniformly bounded by source constants;
there are at most three failure lines by TC. Its full actual-label
TV is at least $B_0+\Phi(\zeta-D/t)-K/t$, hence at least
$B_0+\Phi(\zeta)-K'/t$.

If $\zeta-C_{\rm end}<D/t$, the point was assumed feasible; choose
any feasible instrument and apply (JS.65). Its TV is $B_0+O(t^{-1})$,
while $\Phi(\zeta)=O(t^{-1})$ by the same finite initial slope.
This gives the lower bound even in the narrow finite feasibility strip.
In particular feasibility is never inferred from the leading product
alone. FA Theorem 78.3/FA.41 already evaluates the exact threshold,
and FA.55 excludes $q=C_{\rm end}/t$ for large $t$.
All recovery lists have the explicit reports and simultaneous original
outputs of §17. $\square$

## 15. Corner coefficients stable under the same Gram consumption

**Definition 15.1 (evaluated live coefficient, including zero corners).**
For $a=(\sigma,\eta)\in\{\pm1\}^2$ put

$$
h_a=(1,\sigma,\eta)^T,\quad L_a=|h_a^TGh_a|,\quad
v_a=(0,\sigma,-(\alpha/\beta)\eta)^T,\quad e_a=2h_a^TGv_a.
\tag{JS.70}
$$

Let $B(z,w)=B_0^{\rm cor}+B_z z+B_w w+B_{zw}zw$ interpolate the
four $L_a$ by four-sign Fourier inversion, and set

$$
b_a'=\sigma B_z-(\alpha/\beta)\eta B_w
 +(1-\alpha/\beta)\sigma\eta B_{zw}.
\tag{JS.71}
$$

If $h_a^TGh_a\ne0$ let both endpoints $a_a^-,a_a^+$ equal
$\operatorname{sign}(h_a^TGh_a)e_a-b_a'$. Otherwise let
$a_a^-=-|e_a|-b_a'$ and $a_a^+=|e_a|-b_a'$. Define

$$
M(c)=\frac14\sum_a\max\{(a_a^--c)^2,(a_a^+-c)^2\},\qquad
\Gamma=\sqrt{2M(c_*)},\qquad \mathsf a=\Gamma/2.
\tag{JS.72}
$$

Here $c_*$ is evaluated finitely as follows. Sort the distinct midpoints
$(a_a^-+a_a^+)/2$. On each of the resulting at-most-five intervals,
choose at each corner an endpoint farthest from $c$ on that interval.
Clamp the average of these four endpoints to the interval closure,
and compare $M$ at the resulting candidates. The minimum candidate
is $c_*$. Unbounded extreme intervals cause no difficulty, and ties
are included. Each summand is a quadratic $c^2$ plus a convex
piecewise affine function, so $M$ is strongly convex and $c_*$ is
unique. No optimization remains in this finite definition.

When all corner heights are nonzero this reduces to

$$
\Gamma^2=\tfrac12\sum_a(a_a-\bar a)^2,\qquad
\bar a=\tfrac14\sum_a a_a.
\tag{JS.73}
$$

The coefficient $\mathsf a$, rather than $\Gamma$, uses JR55's
HALF-TV convention. The static endpoint square-root mechanism and
its coefficient are credited there; the perturbation statement below
is the additional assertion. The zero-corner formula covers the
degenerate conditional extension without dividing by $\Gamma$.

**Lemma 15.2 (uniform upper bound and admissible Gram repair).**
For (JS.61)'s remaining law, uniformly with bounded $\zeta$,

$$
\int|f|dP\le S_{\rm corner}+\Gamma\sqrt{E_{\rm rem}}
 +O(E_{\rm rem}+t^{-1}).
\tag{JS.74}
$$

If $\Gamma>0$, this coefficient can be attained by finitely many
pure-live atoms near the four corners while repairing exactly the
same residual Gram $I_3-\int hh^TdP_{\rm cap}$. With a small amplitude
$\varepsilon$ and $\delta_t=t^{-1}$ their energy and total live value
obey uniformly

$$
\begin{aligned}
E_{\rm rem}&=\varepsilon^2+
O(\varepsilon^3+\varepsilon\delta_t+\delta_t^2),\\
\int|f|dP&=S_{\rm corner}+\Gamma\varepsilon+
O(\varepsilon^2+\delta_t).
\end{aligned}
\tag{JS.75}
$$

Every target Gram here lies in
$\{S:\operatorname{tr}(QS)=0\}$, $Q=\operatorname{diag}(1,-\alpha,-\beta)$.
No six-dimensional unrestricted symmetric-matrix repair is asserted.
For $\Gamma=0$ one may take no tangent motion and obtain residual
energy $O(t^{-2})$ and live value $S_{\rm corner}+O(t^{-1})$.

Proof. Put $u=|z|-1$ in each sign sector. Near its corner,

$$
|f(z,w)|-B(z,w)=\max\{a_a^-u,a_a^+u\}+O(u^2).
\tag{JS.76}
$$

The ellipse parametrization is
$z=\sigma(1+u)$,
$w=\eta\sqrt{1-2(\alpha/\beta)u-(\alpha/\beta)u^2}$.
Taylor expansion proves (JS.76) locally, also when $f$ vanishes,
since $|e_au|$ has exactly the two slopes specified above. Away from
the corners $u^2$ is bounded below and every numerator is continuous
and bounded. Thus a single $K u^2$ remainder works on the entire
ellipse, including both axes and every sign assignment there.

The exact total Gram gives $\int B\,dP=S_{\rm corner}$.
Capacity mass is $O(\delta_t)$, and
$\int u\,dP_{\rm rem}=-E_{\rm rem}+O(\delta_t)$.
Subtract $c_*u$ from (JS.76) and use Cauchy–Schwarz. Lemma 13.1's
sector masses are $1/4+O(\sqrt{E_{\rm rem}}+\delta_t)$, so the
weighted squared farthest slope is
$M(c_*)+O(\sqrt{E_{\rm rem}}+\delta_t)$.
When $M(c_*)>0$, multiplying its square root by
$\sqrt{2E_{\rm rem}}$ gives
$\Gamma\sqrt{E_{\rm rem}}+O(E_{\rm rem}+\delta_t)$.
When $M(c_*)=0$ all slope endpoints equal $c_*$; their centered
linear term vanishes exactly and the same bound follows directly.
Adding back the capacity mass proves (JS.74).

For attainment the zero-subgradient condition for $M$ permits, at
each corner, a distribution $\theta_{a,i}$ on its farthest endpoints
$s_{a,i}$, with at most two entries, such that

$$
\tfrac14\sum_{a,i}\theta_{a,i}(s_{a,i}-c_*)=0,\qquad
\tfrac14\sum_{a,i}\theta_{a,i}(s_{a,i}-c_*)^2=M(c_*).
\tag{JS.77}
$$

Omit zero $\theta$'s. Set
$v_{a,i}=\sqrt{2/M(c_*)}(s_{a,i}-c_*)$ and initially
$u_{a,i}=\varepsilon v_{a,i}$. Their uniform-corner mean velocity
is zero and mean squared velocity is two. A farthest upper endpoint
has nonnegative centered velocity; a farthest lower endpoint has
nonpositive centered velocity. Thus the selected endpoint is the
actual directional slope of the absolute value at a zero corner,
not a fictitious branch. The linear gain is $\Gamma\varepsilon$.

For exact repair allow four total corner weights $w_a$, distributing
each as $w_a\theta_{a,i}$, and one common shift $c$ in
$u_{a,i}=\varepsilon v_{a,i}+c$. At $\varepsilon=c=0$, $w_a=1/4$,
the derivative of the moment map
$(\int1,\int z,\int w,\int zw,\int z^2)$ has rank five.
The four weight columns are the Hadamard columns in the first four
coordinates; the common shift changes the last coordinate by two
and the first four by zero. The ellipse identity supplies the sixth
moment. A fixed right inverse and the implicit-function theorem
therefore repair every sufficiently small admissible target Gram.
Weights stay positive. The zero mean velocity makes the common
shift $O(\varepsilon^2+\delta_t)$; weight changes are
$O(\varepsilon+\delta_t)$. Expanding $u^2/2$ and (JS.76) gives
exactly (JS.75). These charts are uniform for a bounded family of
$O(\delta_t)$ Gram consumptions. There are at most two atoms per
corner, hence eight pure-live labels. With $\Gamma=0$ the same
rank-five map at zero motion gives the stated $O(\delta_t^2)$
energy; no normalization by $\Gamma$ is used. $\square$

## 16. The compact-uniform spectral product and value layer

**Definition 16.1 (credited curvature and the cubic profile).** SC.21–22
and TC's exact final branch give

$$
\gamma_f-\Phi(C_{\rm sat}-h)=\mathsf b h^2+O(h^3),\qquad
\mathsf b=K_{\rm sat}=
\frac{L_f^3}{4b_{\rm off}^2 C'(p_s)^2}>0.
\tag{JS.78}
$$

Indeed $D_{\rm sat}=2u_fC'(p_s)/(1+u_f^2)
=2b_{\rm off}C'(p_s)/L_f$, so this is exactly the supplied
$L_f/D_{\rm sat}^2$, with its uniform cubic remainder.
For $\mathsf a>0$ and real $\xi$ let $r_\xi$ be the unique root

$$
r_\xi^3-\xi r_\xi=\mathsf a/(4\mathsf b),\qquad
r_\xi>\sqrt{\max\{\xi,0\}},\qquad
\mathcal V_{\rm sp}(\xi)=\mathsf a r_\xi-
\mathsf b(r_\xi^2-\xi)^2.
\tag{JS.79}
$$

For $\mathsf a=0$ define instead
$\mathcal V_{\rm sp}(\xi)=-\mathsf b\max\{-\xi,0\}^2$.

**Theorem 16.2 (full-class upper bound and one common attaining family).**
Put

$$
s_t(\xi)=s_0\left(1-\frac{C_{\rm sat}}t-
\frac{\xi}{t^{4/3}}\right).
\tag{JS.80}
$$

For every finite $R$, these points are feasible for all sufficiently
large $t$, uniformly for $|\xi|\le R$, and

$$
\lim_{t\to\infty}\sup_{|\xi|\le R}
\left|t^{2/3}[\mathcal T_{\log(1+t)}(s_t(\xi))-T_0]
-\mathcal V_{\rm sp}(\xi)\right|=0.
\tag{JS.81}
$$

Thus the product width is $t^{-1/3}$, the strength displacement beyond
$s_0(1-C_{\rm sat}/t)$ is $t^{-4/3}$, and the value correction is
$t^{-2/3}$. At $\xi=0$ and $\mathsf a>0$ it equals

$$
\mathcal T_{\log(1+t)}(s_0(1-C_{\rm sat}/t))
=T_0+3\mathsf b\left(\frac{\mathsf a}{4\mathsf b}\right)^{4/3}
t^{-2/3}+o(t^{-2/3}).
\tag{JS.82}
$$

Proof. The same-label split, (JS.74), and the exact failure upper
bound yield for every competitor, with $z_\nu\le\zeta=tq$,

$$
T_{\rm instr}-T_0\le
\mathsf a\sqrt{(\zeta-z_\nu)/t}
-[\gamma_f-\Phi(z_\nu)]
+O((\zeta-z_\nu)/t+t^{-1}).
\tag{JS.83}
$$

Here $\zeta=C_{\rm sat}+\xi t^{-1/3}$ stays in a fixed compact
interval. For $z_\nu\ge C_{\rm sat}$ the scaled gain is at most
$\mathsf a\sqrt{\xi_+}+o(1)$. For smaller cost write
$z_\nu=C_{\rm sat}-y t^{-1/3}$; budget requires
$y\ge\max\{0,-\xi\}$. Costs a fixed distance below saturation
lose a fixed positive amount while their live gain tends to zero.
For costs close to saturation, (JS.78) bounds the loss below by
$\mathsf b h^2/2$ after shrinking its fixed neighborhood.
Consequently unbounded $y$ cannot be near maximal: its quadratic loss
dominates its $\sqrt{\xi+y}$ gain, uniformly for $|\xi|\le R$.
On bounded $y$ the cubic remainder is uniform. The limiting upper
bound is therefore

$$
\sup_{y\ge\max\{0,-\xi\}}
\{\mathsf a\sqrt{\xi+y}-\mathsf b y^2\}.
\tag{JS.84}
$$

The discarded $z_\nu\ge C_{\rm sat}$ bound is included by $y=0$
when $\xi\ge0$. For $\mathsf a>0$, substitute
$r=\sqrt{\xi+y}$. The derivative is
$\mathsf a-4\mathsf b r(r^2-\xi)$; it is positive at the left
endpoint and changes sign exactly once because $r^3-\xi r$ is
strictly increasing for $r>\sqrt{\max\{\xi,0\}}$.
This evaluates (JS.84) as (JS.79). With $\mathsf a=0$ it is
maximized by $y=\max\{0,-\xi\}$, giving the stated degeneration.
The compact restriction of $y$ and the uniform remainders prove
a compact-uniform upper bound, including arbitrary original time laws.

For the matching construction suppose first $\mathsf a>0$ and put
$y_\xi=r_\xi^2-\xi>0$ and
$\lambda_t=C_{\rm sat}-y_\xi t^{-1/3}$. On each compact $\xi$
interval $r_\xi$ is positive, continuous and bounded; the same holds
for $y_\xi$. For large $t$, TC Corollary 4.2's selected final branch
contains $\lambda_t$. Choose its unique $p_t<p_s$ with
$C(p_t)=\lambda_t$. Use the two orthogonal unit vectors

$$
e_P(t)=(\sqrt{1-p_t},-\sqrt{p_t})^T,\qquad
e_N(t)=(\sqrt{p_t},\sqrt{1-p_t})^T.
\tag{JS.85}
$$

For each vector use (JS.48) and generate one actual saturated low
label with coefficient weight

$$
\pi_e=\frac{a(e_2^2)}{tc_*(z_e^2)},\qquad
N_e=M_2^{1/2}ee^TM_2^{1/2},\qquad v_e=tc_*(z_e^2).
\tag{JS.86}
$$

The physical effects sum exactly to $M_2$. Their live Gram consumption
is $O(t^{-1})$, and their exact $H$ cost is $\lambda_t/t$.
Repair that very Gram with Lemma 15.2's pure-live atoms. For example
choose their amplitude
$\varepsilon_t=(r_\xi-t^{-1/6})t^{-2/3}$, positive for large $t$.
The unused energy margin is of order $t^{-3/2}$, whereas the errors
in (JS.75) are $O(t^{-5/3})+O(t^{-2})$, uniformly on the compact
interval. Hence

$$
E_{\rm rem}\le r_\xi^2t^{-4/3},\qquad
\lambda_t/t+E_{\rm rem}\le
C_{\rm sat}/t+\xi t^{-4/3}=q.
\tag{JS.87}
$$

This proves the original contrast inequality at each sufficiently
large finite parameter. The live HALF-TV gain is
$\mathsf a r_\xi t^{-2/3}+o(t^{-2/3})$, and the failure loss is
$\mathsf b y_\xi^2t^{-2/3}+o(t^{-2/3})$ by (JS.78).
The actual live/failure grouping loss on the two saturated labels
is at most $2\|f\|_\infty\sum\pi_e=O(t^{-1})$, below this scale.
Thus this one common instrument attains (JS.79), with §17's actual
reports, original errors, sharp joint cost and FIRST process.

If $\Gamma=0$, take the final-branch cost
$\lambda_t=\min\{\zeta,C_{\rm sat}\}-D/t$ with a fixed sufficiently
large $D$. Lemma 15.2 at zero motion repairs the consumed Gram with
energy at most $D/t^2$ and live change $O(t^{-1})$. Its finite contrast
is therefore admissible; (JS.78) gives scaled value
$-\mathsf b\max\{-\xi,0\}^2+o(1)$. All charts, cost inverses and
remainders are uniform on $|\xi|\le R$. These constructions prove
both feasibility and the lower bound in (JS.81). Substitution of
$r_0^3=\mathsf a/(4\mathsf b)$ proves (JS.82). $\square$

The correction is relative to $T_0=\mathcal T(s_0)$, not to the
unbudgeted value at the varying strength $s_t(\xi)$. The static
square-root gain at that strength has order $t^{-1/2}$ when its
coefficient is positive. Thus (JS.82) preserves FA's strict finite
deficit below $\mathcal T(s_t(\xi))$.

## 17. Actual labels, permitted reports and simultaneous original outputs

**Proposition 17.1 (one original realization for every recovery list).**
For each finite list above keep every nonzero low atom as an actually
generated, dephased label $j$. Write its live matrix and attached
failure effect as

$$
K_j=\sqrt{\pi_j}K(z_j,w_j),\quad
N_j=\pi_jv_jn_jn_j^T,\quad
\sum\pi_jh_jh_j^T=I_3,\quad \sum N_j=M,\quad
0\le v_j\le tc_*(z_j^2).
\tag{JS.88}
$$

Extend the effects on coordinates $1,2$ by zero on coordinate zero.
For the limiting optimizer lists, first use (JS.48) and the exact
finite repair of §5 or §15; a limiting failure measure by itself is
not an acquisition. Assign deterministic binary report
$r_j=\operatorname{sign}z_j$, choosing either report at $z_j=0$.
Add two actual high labels $H_+,H_-$ with encoders
$\sqrt{(1-\delta)/2}\,DE^\dagger$, whole fibre dimension three,
zero rate, decoder $Y\mapsto EYE^\dagger$ and reports $+,-$.
Fix isometries $W_\perp:\mathbb C^2\to\operatorname{ran}(I_5-P)$
and $J_0:\mathbb C^2\to\mathbb C^3$. Add two actual complement
labels $C_+,C_-$ with encoders $W_\perp^\dagger/\sqrt2$, whole
counted fibre dimension two, zero rate, decoder
$Y\mapsto EJ_0YJ_0^\dagger E^\dagger$ and reports $+,-$.
All these labels and maps are fixed before the sole specimen arrives.

The permitted optional report attenuation is the actual kernel

$$
\Pr(F=f\mid j)=\tfrac12(1+f\eta r_j),\qquad
\eta=\frac{1-q}{\sum_j\pi_j|z_j|}\in[0,1],\quad f\in\{\pm1\},
\tag{JS.89}
$$

where high/complement reports are included in the label. Retain the
parent label and generate/dephase the coin output; this preserves
full-record TV and changes contrast to exactly $s$. The original
inequality uses the deterministic reports and needs no extra coin.
The denominator is positive in these endpoint constructions; if a
separate zero-contrast construction has zero denominator, use a fair
kernel rather than this ratio.

Proof. The physical encoders and chronological low decoders are exactly
Theorem 6.1's row-space construction: $C_j=Q_j^{1/2}J_j^\dagger$,
$B_j=K_jJ_jQ_j^{-1/2}$ and
$F_j=Q_j^{-1/2}J_j^\dagger N_jJ_jQ_j^{-1/2}$, where
$Q_j=J_j^\dagger(K_j^\dagger K_j+N_j)J_j\succ0$ and $J_j$ is
onto $\operatorname{ran}K_j^\dagger$. Use encoder $C_jE^\dagger$.
Null rank is exactly two, also at axes, and
$B_j^\dagger B_j+F_j=I_2$ with $B_j^\dagger B_j\succ0$.
The terminal CP map $\operatorname{Ad}_{B_j}$ has prescribed effect
$B_j^\dagger B_j$; coercivity alone is not asserted sufficient for
arbitrary different noncommuting time laws.

For the chosen attainer use $g(u)=2/(1+u)^2$,
$G_t(u)=2u/(1+u)$, $Z_j(u)=\sqrt{I_2-G_t(u)F_j}$ and
$R_j(u)=g(u)F_j[I_2-G_t(u)F_j]^{-1}$ on the whole fibre.
Its current-survivor jumps are (JS.32), individually for all five
original labels. Its survivor terminal map is the isometry
$EB_j(I_2-F_j)^{-1/2}$. The intermediate no-event/jump effects in
§6 sum to identity at every cut. Activity is exactly
$\log(1+v_j/c_*(z_j^2))\le\log(1+t)$; pure-live labels have zero
rate. Every finite carrier has positive terminal survival. First
failure is at actual absolute time $6+u$ in this mathematical process;
only survivors receive terminal processing, with no deadline atom,
singular failure or later positive-carrier action. Necessity throughout
§§13–16 allowed every admitted original CP/time law, including
noncommuting TP controls; $g$ was used only for these attainments.

The exact Gram and $\sum N_j=M$ give total supported encoder effect
$I_3$ by root TP. The complement contributes $I_5-P$, so the total
effect is $I_5$ and each encoder is TNI. Decoders are TP on their
entire declared fibres. Every future-accessible input-bearing quantum
share belongs to those joint fibres; all other dilation systems,
including Kraus multiplicity, are permanently discarded before the
cut. Splitting an actual fair report produces the two labels explicitly
listed above, not a hidden record.

For every complex $X\in M_5$ the same list has exactly (JS.33), and
for every passive reference its live matrices tensor with $I_R$ and
its failure component on each Borel $\mathcal B$ is exactly

$$
w_\ell\left(\int_{\mathcal B}\frac{2\,du}{(1+u)^2}\right)P_f\otimes
\operatorname{Tr}_5[(EME^\dagger\otimes I_R)X],
\quad \ell\in\{0,1,2,3,13\}.
\tag{JS.90}
$$

This follows by Kraus bilinearity of the exact Gram and by summing
the pulled-back failures. It is the conditional reference operator.
Both zero labels $0,13$ are individually zero; the three positive
Borel maps remain separate. Within-complement coherences are retained,
cross-support operators vanish, and no unlisted sector is added.
This is the allowed JR completion freedom, distinct from fixed
CA10's certain-failure complement. The complete outputs on the twelve
supported histories are the same CG.135 outputs, compared against
the original coherent ideal blocks and $f_y$, never against $g$.
Thus the four errors at each height obey
$e_5=e_{27}=E_*$ and $e_{16}<71/484<37/250<E_*$ simultaneously.

Each low-label acquisition law is
$\operatorname{tr}[(K_j^\dagger K_j+N_j)\rho_{y,e,n}]$.
Each high law is $(1-\delta)A_y/2$, and complement laws vanish on
these histories. Hence the generated-record TV and contrast are exactly

$$
T_{\rm instr}=\tfrac12[H_{\rm live}+\sum_j\pi_j|f_j+v_jk_j|],
\qquad \mathsf V=s_0\sum_j\pi_j|z_j|\ge s.
\tag{JS.91}
$$

Only $H_\pm$ have dimension at least three, so their worst-history
ACQUIRED mass is $(1-\delta)A_{27}=\mathsf C(s)$, including every
later-failure mass in the acquired probabilities. A retained report
coin multiplies both height laws by the same conditional kernel;
summing its outputs preserves the absolute difference at each parent
label. It therefore preserves full TV, activity and sharp cost.
This proves all required properties for the same instrument.
$\square$

For the spectral construction there are two saturated low labels,
at most eight pure-live labels, two high and two complement labels
before optional attenuation. These are upper construction counts.
The limiting physical failure-ray count, actual low-label count,
total acquired alphabet, hidden Kraus multiplicity and joint quantum
dimension are different quantities. No minimum finite optimizer
alphabet follows from these counts.

The fixed-$s$ auxiliary constant $\nu_*$ retains FA.31's separate
meaning. With $L_0=L^2$, the spectral $e_\pm$ of (JS.41),
$r_\pm=(dh_1/(bh_2))\sqrt{m_2/m_1}(e_\pm)_2/(e_\pm)_1$,
$\mathbf c_\pm=(\sqrt{\theta r_\pm^2+\omega},-r_\pm,1)^T$ and
$a_0=[4\sum_\pm\mathbf c_\pm^TL_0^{-1}\mathbf c_\pm]^{-1}$,
it is
$\nu_*=\max_\pm m_1h_2^2(e_\pm)_1^2/
[a_0d^2\mathfrak c(\mathbf c_\pm)]$.
That auxiliary family consists of $\sqrt{a_0}\mathbf c_\pm$ and
the support-restricted IR null decomposition of its residual Gram.
It is not $\mu/c_*(r)$, a failure measure, or (JS.86)'s rare mass.
The current constructions use (JS.86) and the corner repair directly;
they do not borrow a uniform fixed-$s$ bound from this auxiliary family.

## 18. Attribution, remaining finite mathematics and native boundaries

**Convention 18.1 (scope of the additional deductions).** Theorems
11.3 and 12.1–12.2 add globally selected limiting interpolation and
the pointwise physical two/three-ray test with its exact TC crosswalk.
They do not rederive TC's global unique at-most-three-line structure,
strict concavity, projective certificate, initial polynomial selection,
initial slope/quadratic law or selected final interval. SC's global
convexity and sharp full-measure saturation curvature are used with
their exact hypotheses. WE/§9 supplies the critical limit; §14 adds
the every-instrument strip and sub-spectral uniform $t^{-1}$ rate.
JR55 supplies the static endpoint square-root mechanism; §15 gives
its finite Gram stability and explicit zero-corner handling. Section
16 combines that stability and SC's curvature at the simultaneous
spectral scale with a whole-class upper bound and a common attainer.
Sections 5–8 and FA68–75 supply finite repair, spectral equality,
capacity and chronological/full-output realization. RC23–30's static
dual and RC58–66's static contact/gluing remain credited results.

FA78–79 already evaluates the entire scalar feasibility threshold and
the height on its minimum-budget boundary; FA84 supplies the strong
actual-low-label count: four at its normalized budgets $r=1,2$ and
five at every other feasible strong budget, with no reachable
six-label strong region. FA82's weak three/four/five feasibility counts
and TA's total unbudgeted alphabets retain their own scopes. None is
a count of arbitrary finite-$A$ height optimizers. These credits
supersede the corresponding unresolved-item descriptions in §10.2
only to their stated extent. The new deductions are conditional
repository mathematics using the suppliers' classical convex,
spectral, CP and first-event mechanisms. No new external theorem,
worldwide priority, exhaustive literature or certification claim is
needed for them.

**Definition 18.2 (unresolved original target).** The full inventory,
isolation, multiplicities and sign intervals of (JS.58)'s source-specific
zeros remain unresolved. A finite nonempty set is not a proof of one
transition. The scalar interpolation above resolves limiting budget
selection, not the finite weak height frontier $\mathcal T_A(s)$ for
every feasible interior $(s,A)$.

That finite frontier still requires one simultaneously supporting dual
for pure-live and saturated atoms on the entire ellipse, exact common
live Gram and physical failure covariance, positive contact weights,
the original contrast inequality, and all optimizer/contact/rank
changes. An implicit moment SDP or scalar failure cost does not evaluate
it. The fixed-strength deficit coefficient $K(s)$ still needs its
precontact/contact evaluation and all gluing, zero-weight, degenerate
orientation and sign cases beyond its credited postcontact/local
results. Exact finite-$A$ height-optimizer acquisition alphabets,
critical five-label and static-contact joint layers, and the other
required next terms remain unresolved. The estimates (JS.68) and
(JS.81) are uniform asymptotics, not finite-frontier equalities.
At $q=0$ finite activity remains infeasible; finite positive survival
is never replaced by limiting certain failure.

Every original native obligation also persists: lawful access to the
sole unknown specimen, calibration and actual acquisition-label
generation, coherent storage and joint counting of every accessible
share, whole-fibre decoder actuation, acquisition duration and placement
on the same absolute clock, native FIRST absorption at $6+u$, no
later positive-carrier action, positive terminal survivors, stopped
archives, source/epoch, controller and permissions. They remain
`ASSUMED-UNVERIFIED`. The mathematical TP process supplies no actuator
or extra interval; OriginalControl remains geometric. No original
twelve-history error, passive reference, separately labelled Borel map,
sharp worst-history joint cost or full-complex competitor is dropped.
These finite conditional results neither complete nor narrow the
unchanged quantum-first AURIC FIB ATOM programme through 2027.

[TC]: FIB_NATIVE_JOINT_THREE_LINE_STRUCTURE_AND_INITIAL_LAW.md
[SC]: FIB_NATIVE_JOINT_INTERIOR_SUPPORT_AND_SATURATION_CURVATURE.md

## 追加锚（本行以下为增补区）
