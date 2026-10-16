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
