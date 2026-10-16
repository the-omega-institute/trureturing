# Weak finite-activity endpoint: an evaluated feasibility constant and the full-record limit

## 1. Conditional source and the unchanged original experiment

**Convention 1.1 (mathematical antecedents).** This companion uses the
ordinary conditional results of [JR], [RC] and [FA]. The isolated CG
source root, its isolation/Jacobian certificate, exact ranks,
normalization and original minimax identification remain named
`ASSUMED-UNVERIFIED` antecedents here. Equalities of source operators and
trace preservation apply at that root. Supplied enclosures establish
inequalities of derived expressions; they do not establish off-root
normalization. No fresh numerical, external, Lean/kernel or frozen
certification is asserted.

There is one unknown normalized reached-cut specimen, in the original
five modes indexed by $(0,1,2,3,13)$. Put

$$
\begin{gathered}
E=((e_0+e_{13})/\sqrt2,(e_1+e_3)/\sqrt2,e_2),\qquad P=EE^\dagger,\\
p_y=(y/128,(64-y)/128,1/2),\quad a_y=(\sqrt{p_{yi}})_i,\\
\rho_{y,e,n}=U_{e,n}a_ya_y^TU_{e,n}^\dagger,\quad
U_{e,n}=\operatorname{diag}(e,n,1),\quad
y\in\{5,16,27\},\quad e,n\in\{\pm1\}.
\end{gathered}
\tag{WE.1}
$$

The received state is $E\rho_{y,e,n}E^\dagger$. Original height is
$y/256$ and winding parity is $en=(-1)^m$; neither is given to the
instrument. The ideal live matrices remain the entire coherent matrices
$EU_{e,n}B_y^{\rm ideal}U_{e,n}^\dagger E^\dagger$ prescribed by CG.111.
The five ideal failure measures, separately in their original labels,
are $w_\ell f_y(u)du\,P_f$, where

$$
w=(0,1/4,1/2,1/4,0),\qquad f_y(u)=\frac{6y}{(y+6u)^2},\qquad 0\le u\le1.
\tag{WE.2}
$$

Here $P_f$ is the fixed normalized stopped failure output. Original
absolute time is $6+u$. Error is HALF the entire stopped-cq trace norm,
maximized over all twelve histories. It includes every live coherence,
singular-time component, abort, wrong-support and zero-target sector.
The ideal matrices and original minimax certificate are inherited data;
no replacement ideal target is introduced.

An actual acquisition consists of CP encoders of total effect $I_5$,
actually generated dephased classical labels, and full-output TP
conditional decoders. Its quantum fibre counts jointly every
future-accessible input-bearing specimen, memory, quantum controller,
environment, return system and entanglement share. Any other dilation
system is permanently inaccessible before this same acquisition cut.
An inaccessible Kraus multiplicity is not a record. There is no prior,
postselection, acceptance division, helper specimen, copy, reset, retry,
readable old history, bypass or free clock interval.

For a designated binary record with supported plus effect $F$, retain
exactly the original inequality and sharp cost:

$$
\mathsf V(F)=\frac{2|\operatorname{Re}F_{01}|}{\kappa}\ge s,
\qquad \mathsf W=\mathsf C(s),
\tag{WE.3}
$$

where $\mathsf W$ is the maximum over the twelve histories of the
ACQUIRED probability of a joint fibre of dimension at least three.
It includes any acquired branch that later fails. Other entries of $F$
and the forgotten complete channel are free.

**Definition 1.2 (the full finite-activity comparison class).** Use
exactly FA Definition 67.2. A positive-semidefinite first-event rate
$R_\lambda(u)$ acts on each whole joint decoder fibre. Survivor controls
are TP apart from this loss and may be noncommuting or unobserved TP
controls. For its survivor map $\mathcal S_{\lambda,u}$,

$$
-\frac d{du}\operatorname{tr}\mathcal S_{\lambda,u}(X)
=\operatorname{tr}(R_\lambda(u)\mathcal S_{\lambda,u}(X)),
\qquad \mathcal S_{\lambda,0}=\mathrm{id}.
\tag{WE.4}
$$

Rates are measurable with integrable operator norm; terminal survivor
processing is TP. There is no singular first-event part, forced deadline
failure, or later positive-carrier action after absorption. Activity is

$$
\mathsf A=\sup_\lambda\int_0^1\|R_\lambda(u)\|\,du.
\tag{WE.5}
$$

Use a maximum for finite labels and essential supremum in the stipulated
integral case. This is neither an expected cost nor an integral of a
maximum over labels. Let $\mathfrak F_{s,A}$ have the original error
$E_*$, (WE.3), and $\mathsf A\le A$. For nonempty classes let
$\mathcal T_A(s)$ be the supremum of the TV distance between the full
acquisition-label laws at $(5,+,+)$ and $(27,+,+)$. The principal class
is finite; necessity also covers the convergent countable and expressly
measurable/integrable finite-fibre extensions supplied in CG Convention
21.3. No arbitrary disintegration or infinite-dimensional coding
extension is presumed. Put

$$
t=e^A-1,\qquad q=1-s/s_0,\qquad
A_{\min}(s)=\log(1+t_{\min}(s)).
\tag{WE.6}
$$

FA Theorem 73.1 already proves a positive finite attained threshold
$t_{\min}(s)$ for $0\le s<s_0$. The endpoint $s=s_0$ is infeasible
at every finite activity. Empty classes have no claimed TV maximum.

**Definition 1.3 (source dictionary).** With the source amplitudes of
JR.2, write

$$
\begin{gathered}
D=\operatorname{diag}(h_0,h_1,h_2),\quad
T=a e_0e_1^T+b e_1e_0^T,\quad S=c e_0e_2^T+d e_2e_0^T,\\
M=\operatorname{diag}(0,m_1,m_2),\quad
D^\dagger D+T^\dagger T+S^\dagger S+M=I_3,\\
\theta=\frac{ab}{h_0h_1},\quad \omega=\frac{cd}{h_0h_2},\quad
\delta=\theta+\omega,\quad s_0=\sqrt\delta,\quad
\kappa=h_0a+h_1b,\\
\alpha=\theta/\delta,\quad\beta=\omega/\delta,\quad U=1/\alpha,\\
V=\frac{m_2h_1^2}{b^2},\quad W=\frac{m_1h_2^2}{d^2},\quad
\mu=\alpha V+\beta W,\quad r=V/\mu,\quad k=\sqrt r.
\end{gathered}
\tag{WE.7}
$$

All displayed amplitudes and $m_i$ are positive; $0<\delta<1$ and
$\alpha+\beta=1$. The supplied FA.74 comparison $V/W=v^\dagger<1$
gives $0<V<\mu$, hence $0<r<1<U$. The symbols $a,b,c,d$ denote source
amplitudes, and $W$ in (WE.7) is a failure moment, distinct from
$\mathsf W$.

For the radial variable $x\in[0,U]$, unrelated to original height, put

$$
\begin{aligned}
w_2(x)&=(1-\alpha x)/\beta,\\
D_c(x)&=h_0^2\delta+b^2x+d^2w_2(x),\\
N_c(x)&=h_1^2h_2^2\delta+a^2h_2^2x+c^2h_1^2w_2(x),\\
c_*(x)&=N_c(x)/D_c(x),\qquad H(x)=(\sqrt x-1)^2/2,\\
\mathcal F(x)&=H(x)/c_*(x),\qquad
B_* =\mu/c_*(r),\qquad C_{\rm end}=B_*(1-k)^2/2.
\end{aligned}
\tag{WE.8}
$$

Both affine expressions $D_c,N_c$ are strictly positive on this entire
closed interval, including its axes. The capacity $c_*$ is precisely
FA.6 for the normalized real null vector $(s_0,z,w)$ with $z^2=x$,
$w^2=w_2(x)$.

## 2. Actual-label reduction over the whole class

**Lemma 2.1 (the imported rigidity and capacity in normalized form).**
For every finite-activity competitor at a weak sharp cost, each actual
low label nonzero on supported inputs has whole fibre dimension two.
After removing a common phase its supported composite live matrix and
pulled-back failure effect have the form

$$
\begin{gathered}
K_j=\sqrt{\pi_j}(s_0D+z_jT+w_jS),\qquad \pi_j>0,\\
\alpha z_j^2+\beta w_j^2=1,\qquad
n(z,w)=(0,dw/h_2,-bz/h_1)^T,\\
N_j=\pi_j\upsilon_j n(z_j,w_j)n(z_j,w_j)^T,\qquad
0\le\upsilon_j\le t c_*(z_j^2).
\end{gathered}
\tag{WE.9}
$$

This describes existing actual labels, with no readable Kraus refinement.
Their exact coefficient and failure moments are

$$
\begin{gathered}
\sum_j\pi_j=\sum_j\pi_jz_j^2=\sum_j\pi_jw_j^2=1,\qquad
\sum_j\pi_jz_j=\sum_j\pi_jw_j=\sum_j\pi_jz_jw_j=0,\\
\sum_j\pi_j\upsilon_j=\mu,\quad
\sum_j\pi_j\upsilon_jz_j^2=V,\quad
\sum_j\pi_j\upsilon_jw_j^2=W,\quad \sum_jN_j=M.
\end{gathered}
\tag{WE.10}
$$

High labels have zero supported failure and only $D$ live products.
Their aggregate effect is $(1-\delta)D^\dagger D$. With actual binary
reports $r_j\in\{\pm1\}$, absorbing their coins into the labels,

$$
\mathsf V(F)=s_0\left|\sum_j\pi_j r_jz_j\right|
\le s_0\sum_j\pi_j|z_j|.
\tag{WE.11}
$$

Proof. JR Theorem 42.1 gives the supported live map, failure effect $M$,
zero other effect, zero high failure, low Gram
$\operatorname{diag}(\delta,1,1)$ and high products proportional to $D$.
Its complex equality conditions give the real null face
$x_0^2=\theta z_0^2+\omega w_0^2$; this is not an imposed real or
static-support competitor class.

Here the use of FA Theorem 69.1 is essential: trace balance implies
whole-fibre survival at least $e^{-A}I$, so a supported nonzero label
cannot have zero live map. A nonzero live product has rank two. On a
low fibre this forces an onto encoder Kraus matrix and an injective
live-decoder Kraus matrix. The real null products have kernels
$(1,-bz_0/(h_1x_0),-dw_0/(h_2x_0))$ and adjoint kernels
$(1,-az_0/(h_1x_0),-cw_0/(h_2x_0))$. A common image or kernel fixes
both ratios. Injectivity and surjectivity therefore make all encoder
Kraus matrices proportional, and all live-decoder Kraus matrices
proportional, on each actual label. This is FA69's double rigidity,
valid for arbitrary admitted TP survivor paths and terminal processing.
Normalize the nonzero first coefficient to obtain (WE.9)'s $K_j$.

FA Theorem 69.2 then applies on this very label. Its failure effect
kills both $e_0$ and $\ker K_j$, so it is a nonnegative multiple of
$n n^T$, also when $z=0$ or $w=0$. For
$G_K=K(s_0,z,w)^\dagger K(s_0,z,w)$ its explicit Schur complement is

$$
G_K-\frac{G_Ke_0e_0^TG_K}{(G_K)_{00}}=c_*(z^2)nn^T.
\tag{WE.12}
$$

The necessary whole-fibre bound $L_{\rm dec}\succeq e^{-A}I$ pulls
back to $N_j\preceq tK_j^\dagger K_j$; (WE.12) gives exactly the
capacity in (WE.9). FA69 also identifies the admitted prescribed-law
minimum as $\log(1+\upsilon_j/c_*(z_j^2))$. These are whole-class
necessities; no time law $g$ or commutativity is assumed here.

The low Gram gives the first six moments. The diagonal entries of
$\sum N_j=M$ give the $V,W$ moments; multiply the null equation by
$\pi_j\upsilon_j$ and sum to obtain $\mu$. Full TP decoders make each
supported encoder effect exactly $K_j^\dagger K_j+N_j$. Failure effects
kill coordinate zero, so they have no $01$ record contribution. Only
the $DT$ live term contributes, giving (WE.11), with high contribution
zero. Labels zero on the supported algebra contribute zero throughout.
The same sums become integrals under exactly the supplied measurable
extension. $\square$

**Theorem 2.2 (scalar feasibility equivalence).** For $t>0$ and
$0\le s<s_0$, $\mathfrak F_{s,\log(1+t)}$ is nonempty if and only if
there is a probability measure $\lambda$ on the compact set

$$
\mathcal K_t=\{(x,v):0\le x\le U,\ 0\le v\le tc_*(x)\}
\tag{WE.13}
$$

such that

$$
\int x\,d\lambda=1,\qquad\int v\,d\lambda=\mu,\qquad
\int xv\,d\lambda=V,\qquad
\int\sqrt x\,d\lambda\ge s/s_0.
\tag{WE.14}
$$

At most five scalar atoms suffice for feasibility. This is a
feasibility reduction, with no TV-preserving symmetrization assertion.

Proof. Push the coefficient probability in Lemma 2.1 to
$(x,v)=(z^2,\upsilon)$. Its support and moments are (WE.13)–(WE.14),
by (WE.10)–(WE.11).

Conversely first consider a finite law with atoms $(x_i,v_i)$ of
weights $p_i>0$. For each atom actually generate four sign labels
$(i,\sigma,\eta)$, setting

$$
\pi=p_i/4,\quad z=\sigma\sqrt{x_i},\quad
w=\eta\sqrt{w_2(x_i)},\quad
K=\sqrt\pi(s_0D+zT+wS),\quad N=\pi v_i nn^T,
\quad r_{\rm report}=\sigma.
\tag{WE.15}
$$

The independent signs kill all three live cross moments and the failure
$12$ moment. The live Gram is $\operatorname{diag}(\delta,1,1)$.
The failure diagonal sums are

$$
\frac{d^2}{h_2^2}\frac{\mu-\alpha V}{\beta}=m_1,\qquad
\frac{b^2}{h_1^2}V=m_2.
\tag{WE.16}
$$

Thus $\sum N=M$, capacity holds, and reports give contrast
$s_0\int\sqrt x\,d\lambda\ge s$. Section 5 constructs the whole-fibre
chronological decoders, common high pair and coherent counted
complement for any such finite list, with all original errors and
output identities. Axes cause no difficulty: a zero signed coordinate
may simply keep its duplicate generated coin labels.

For any general $\lambda$, the continuous map
$(x,v)\mapsto(x,\sqrt x,v,xv)$ has compact image in $\mathbb R^4$.
Every finite convex combination can be reduced to five points: an
affine dependence among more points permits moving the weights along
a nonzero dependence with sum zero until a weight vanishes, preserving
the barycentre. Repeat. The set of combinations of at most five image
points is compact, as the image of the product of the compact image
with the closed five-weight simplex. Hence the convex hull is closed.
Uniform approximation of the four continuous functions by simple laws
places their integral vector in this hull. It therefore has an exact
five-point representation, preserving also the contrast integral.
Construction (WE.15) uses at most twenty low labels, plus two high and
two fair complement labels. No general disintegration is used. At
$t=0$, $\int v=\mu>0$ is impossible, consistently with the original
class. $\square$

## 3. The evaluated capacity cost and strict lower bound

**Lemma 3.1 (global strict supporting tangent, including both axes).**
For the supplied source, the tangent to $\mathcal F$ at $r$ is a strict
global supporting line on $[0,U]$:

$$
\mathcal F(x)\ge\mathcal F(r)+\mathcal F'(r)(x-r),
\qquad\text{equality if and only if }x=r.
\tag{WE.17}
$$

Consequently a nonnegative measure $\nu$ of mass $\mu$ and first moment
$V$ has

$$
\int\mathcal F\,d\nu\ge\mu\mathcal F(r)=C_{\rm end}>0,
\qquad\text{equality if and only if }\nu=\mu\delta_r.
\tag{WE.18}
$$

Proof. The required source-specific sign follows symbolically from the
supplied JR.52 bounds. Put $J=adh_2-bch_1$. They imply
$a>65/1000$, $d>98/1000$, $h_2>809/1000$, $b<147/1000$,
$c<16/1000$, $h_1<707/1000$. Thus

$$
65\cdot98\cdot809=5153330>1662864=147\cdot16\cdot707,
\qquad J>0.
\tag{WE.19}
$$

These comparisons use inherited conditional enclosures, with no new
numerical authentication. Write $D_c=D_0+D_1x$, $N_c=N_0+N_1x$.
Direct substitution of $\alpha/\beta=ab h_2/(cd h_1)$ gives

$$
\begin{gathered}
D_0=h_0^2\delta+d^2/\beta>0,\quad
N_0=h_1^2h_2^2\delta+c^2h_1^2/\beta>0,\\
D_1=-bJ/(ch_1)<0,\qquad N_1=(ah_2/d)J>0.
\end{gathered}
\tag{WE.20}
$$

For $\varrho=1/c_*=D_c/N_c$, all denominators stay positive, and

$$
\varrho'=\frac{D_1N_0-D_0N_1}{(N_0+N_1x)^2}<0,\qquad
\varrho''=\frac{-2N_1(D_1N_0-D_0N_1)}{(N_0+N_1x)^3}>0.
\tag{WE.21}
$$

On $0<x<1$, $H'=(1-1/\sqrt x)/2<0$ and
$H''=1/(4x^{3/2})>0$. Therefore
$\mathcal F''=H''\varrho+2H'\varrho'+H\varrho''>0$ there.
Continuity at zero gives strict convexity on $[0,1]$; in particular
the tangent at the interior point $r$ is strictly below $\mathcal F$
at every other point, including zero. Also $\mathcal F'(r)<0$ and
the tangent value at $1$ is strictly less than $\mathcal F(1)=0$.
For $x>1$ that line decreases further, while $\mathcal F(x)\ge0$.
This proves (WE.17) on the whole interval, including $x=U$.
Integrate it and use $V=\mu r$ to prove (WE.18). Its continuous
nonnegative gap vanishes only at $r$, proving the equality condition.
$\square$

**Theorem 3.2 (strict whole-class lower bound and concentration).**
Every feasible finite weak budget satisfies

$$
tq>C_{\rm end}.
\tag{WE.22}
$$

For any feasible sequence $q_n\downarrow0$,
$t_nq_n\to C_{\rm end}$, its failure-weighted squared $T$ coefficient
measures converge to $\mu\delta_r$.

Proof. For an arbitrary actual competitor define its scalar coefficient
law $P_x=\sum\pi_j\delta_{z_j^2}$ and its failure-weighted law
$\nu_x=\sum\pi_j\upsilon_j\delta_{z_j^2}$, with the same definitions
by integration when stipulated. They obey

$$
\int x\,dP_x=1,\quad \nu_x([0,U])=\mu,\quad
\int x\,d\nu_x=V,\quad
\nu_x\le tc_*P_x.
\tag{WE.23}
$$

These are coefficient measures, never source priors or Born
acquisition probabilities. By the first identity,

$$
e:=\int H\,dP_x=1-\int\sqrt x\,dP_x,\qquad 0\le e\le q.
\tag{WE.24}
$$

Capacity and Lemma 3.1 yield

$$
tq\ge te\ge\int\mathcal F\,d\nu_x\ge C_{\rm end}.
\tag{WE.25}
$$

If equality held throughout, $\nu_x=\mu\delta_r$, and the positive
measure $tP_x-\nu_x/c_*$ would have zero $H$ integral, hence be supported
at $1$. Normalization would force
$P_x=(B_*/t)\delta_r+(1-B_*/t)\delta_1$. Its first moment would be
$1-(B_*/t)(1-r)<1$, a contradiction. This proves strictness. The
attained threshold of FA73 consequently also satisfies (WE.22).

For completeness the limiting constraints are compact, including the
axes. From (WE.24), for every $\epsilon>0$,

$$
P_x\{|\sqrt x-1|\ge\epsilon\}\le 2q/\epsilon^2.
\tag{WE.26}
$$

Thus $P_{x,n}\Rightarrow\delta_1$. The $\nu_{x,n}$ have fixed mass
on the fixed compact interval; their subsequential limits retain mass
$\mu$ and moment $V$. The function $\mathcal F$ is continuous even at
zero, so its integral passes to these limits. This supplies the actual
lower-limit compactness, rather than only a formally rescaled SDP.
The multipliers $\upsilon_j$ need not remain bounded as $n$ varies;
the weighted measures do. No finite-mass compactness is asserted for
$t_nP_{x,n}$, whose total mass diverges.

Let $g_r(x)=\mathcal F(x)-\mathcal F(r)-\mathcal F'(r)(x-r)$.
It is continuous and positive except at $r$. Equations (WE.23)–(WE.25)
give the quantitative estimate

$$
\nu_x\{|x-r|\ge\epsilon\}
\le\frac{tq-C_{\rm end}}
{\min_{x\in[0,U],\ |x-r|\ge\epsilon}g_r(x)}
\tag{WE.27}
$$

whenever the indicated set is nonempty. Thus sharp scaling forces
$\nu_{x,n}\Rightarrow\mu\delta_r$, including all possible singular
limit measures and axis mass. This necessity has used FA69 over the
whole class, never a chosen $g$-law, static support family or
TV symmetrization. $\square$

**Corollary 3.3 (closed source formula and strict improvement).** The
constant is the evaluated expression

$$
\boxed{C_{\rm end}=\frac{(\sqrt\mu-\sqrt V)^2}{2}
\frac{\mu\delta h_0^2+b^2V+d^2W}
{\mu\delta h_1^2h_2^2+a^2h_2^2V+c^2h_1^2W}.}
\tag{WE.28}
$$

It is a positive rational/radical expression in the conditional source
coefficients, not a restated limiting infimum. It strictly improves the
FA.25 leading lower coefficient $d_{\rm mom}/\mathfrak c_{\max}$.

Proof. Substitute $r=V/\mu$ and $w_2(r)=W/\mu$ into (WE.8).
By (WE.21), $c_*$ is strictly increasing. Hence
$c_*(r)<c_*(U)=h_2^2ah_1/(h_0b)=\mathfrak c_{\max}$, where the last
equality uses FA73's two axial capacities and monotonicity. Since
$d_{\rm mom}=(\sqrt\mu-\sqrt V)^2/2>0$, (WE.28) gives the strict
comparison. $\square$

## 4. Exact finite recovery and the threshold strip

**Theorem 4.1 (two radial families and an explicit recovery budget).**
Put

$$
\begin{gathered}
p_{\rm cap}=\frac{\beta}{2(1-\alpha r)},\qquad
R(p)=\frac{1-pr}{1-p},\\
Q(p)=1-pk-\sqrt{(1-p)(1-pr)},\qquad
q_0=Q(p_{\rm cap}).
\end{gathered}
\tag{WE.29}
$$

Then $0<p_{\rm cap}<1/2$ and $0<q_0<1$. For $0<q\le q_0$, define

$$
\begin{gathered}
p(q)=\frac{q(2-q)}{(1-k)^2+2qk},\qquad
t_{\rm rec}(q)=B_*/p(q)\\
=\frac{C_{\rm end}}q+\frac{B_*(1+k)^2}{2(2-q)}.
\end{gathered}
\tag{WE.30}
$$

One common twelve-label original instrument has exact contrast
$s=s_0(1-q)$, sharp acquired cost, original error and uniform activity
$\log(1+t_{\rm rec})$. Consequently

$$
\boxed{\frac{C_{\rm end}}q<t_{\min}(s)
\le\frac{C_{\rm end}}q+\frac{B_*(1+k)^2}{2(2-q)},\quad 0<q\le q_0,}
\tag{WE.31}
$$

and

$$
\lim_{s\uparrow s_0}q t_{\min}(s)=C_{\rm end},\qquad
A_{\min}(s)=\log(1/q)+\log C_{\rm end}+O(q).
\tag{WE.32}
$$

Proof. Since $1-\alpha r>\beta$, $p_{\rm cap}<1/2$. On its entire
interval $R(p)\ge1$ and $R(p)<U$: the latter inequality is exactly
$p<\beta/(1-\alpha r)$. For $p>0$, $R(p)>1$. The radicals in (WE.29)
are positive. Differentiation gives

$$
Q'(p)=-k+\frac{1+r-2pr}{2\sqrt{(1-p)(1-pr)}}>0,
\tag{WE.33}
$$

because its numerator is positive and
$(1+r-2pr)^2-4r(1-p)(1-pr)=(1-r)^2>0$.
Thus $Q$ is a continuous increasing bijection from $[0,p_{\rm cap}]$
onto $[0,q_0]$, with $q_0>0$. Its defining positive mean square-root
term gives $q_0<1$. Squaring $1-q-pk=\sqrt{(1-p)(1-pr)}$ gives
$p((1-k)^2+2qk)=q(2-q)$. Existence on this bijective branch proves
that (WE.30) selects the unsquared positive root, with no extraneous
solution.

Consider the two-atom scalar law

$$
\lambda_q=p\delta_{(r,t_{\rm rec}c_*(r))}
 +(1-p)\delta_{(R(p),0)}.
\tag{WE.34}
$$

Its first $x$ moment is one, its $v$ moment is $\mu$, and its $xv$
moment is $V$. Its mean square root is
$pk+(1-p)\sqrt{R(p)}=1-q$. Apply the four-sign construction (WE.15)
to each atom. This gives eight actually generated low labels. The four
failure-carrying labels have

$$
\pi=p/4,\quad z=\sigma\sqrt r,\quad w=\eta\sqrt{W/\mu},\quad
N=\frac\mu4 nn^T,
\tag{WE.35}
$$

whereas the four pure-live labels have $\pi=(1-p)/4$, $z^2=R(p)$,
$w^2=w_2(R(p))$, and $N=0$. Both radial families have strictly
positive squared coordinates. All live cross moments vanish; their
Gram is exactly $\operatorname{diag}(\delta,1,1)$. The four effects
in (WE.35) sum exactly to $M$: their diagonal sums are
$d^2W/h_2^2=m_1$ and $b^2V/h_1^2=m_2$, and the off-diagonal cancels.
Reports $\sigma$ give exact contrast $s_0(1-q)$.

Use Section 5's whole-fibre construction, adding two fair high and two
fair coherent-complement labels. Each carrying label saturates its
capacity at $t_{\rm rec}$, so its activity is $\log(1+t_{\rm rec})$;
all other rates vanish. Small $p$ is small live coefficient mass,
not small acquisition mass: the nonzero effects (WE.35), and hence all
later-failure acquisition, remain included. Every matrix and report
choice is fixed before receiving the sole specimen.

Finally divide $B_*$ by the displayed $p(q)$ to obtain the exact second
line of (WE.30). Theorem 3.2 gives the strict lower bound. The additive
upper term is uniformly bounded by
$B_*(1+k)^2/[2(2-q_0)]$. Factoring $C_{\rm end}/q$ out of
$1+t_{\min}$ and using $\log(1+O(q))=O(q)$ proves (WE.32).
$\square$

**Corollary 4.2 (joint feasibility away from the critical boundary).**
For $q_n\downarrow0$, if $\limsup q_n(e^{A_n}-1)<C_{\rm end}$,
the classes are eventually empty. If
$\liminf q_n(e^{A_n}-1)>C_{\rm end}$, they are eventually nonempty.
At the critical product, (WE.31) is a uniform bounded additive strip
for $t_{\min}$, not an evaluation of its additive correction.

Proof. The first assertion is (WE.22). For the second, (WE.30) gives
$q_nt_{\rm rec}(q_n)=C_{\rm end}+O(q_n)$; the strict limiting margin
puts this recovery below the proposed budgets eventually. At $q=0$
no finite budget is feasible, as already supplied by FA71. $\square$

## 5. Whole-fibre chronological instruments and exact outputs

**Proposition 5.1 (finite-label recovery inside the same class).**
Every finite list supplied by (WE.15), in particular the eight low
labels of Theorem 4.1, has a common chronological realization in
Definition 1.2, with the following full-complex and passive-reference
identities. This is the FA70/75 constructor applied with the present
exact live Gram and failure effects, rather than a new native service.

Proof. For one low label let $K,N$ be its actual matrices. The null
determinant identity is

$$
\det(x_0D+z_0T+w_0S)
=h_0h_1h_2x_0(x_0^2-\theta z_0^2-\omega w_0^2).
\tag{WE.36}
$$

Here $x_0=\sqrt\pi s_0\ne0$, and the lower-right minor is
$\pi\delta h_1h_2>0$. Hence $K$ has rank exactly two, also on the
axes of the general scalar construction. The effect $N$ is supported
on $\operatorname{ran}K^\dagger$. Fix a row-space isometry
$J:\mathbb C^2\to\operatorname{ran}K^\dagger$ and put

$$
\begin{gathered}
Q_K=J^\dagger(K^\dagger K+N)J\succ0,\quad
C_K=Q_K^{1/2}J^\dagger,\quad B_K=KJQ_K^{-1/2},\\
F_K=Q_K^{-1/2}J^\dagger NJQ_K^{-1/2}.
\end{gathered}
\tag{WE.37}
$$

Direct multiplication, using the row-space projection $JJ^\dagger$,
gives

$$
B_KC_K=K,\quad C_K^\dagger F_KC_K=N,\quad
B_K^\dagger B_K+F_K=I_2,\quad B_K^\dagger B_K\succ0.
\tag{WE.38}
$$

Thus $0\preceq F_K\prec I_2$ on the entire fibre, not only a selected
encoded state. Use encoder $C_KE^\dagger$ into that whole fibre.
This is exactly the row-space factorization FA.11–.12.

Here is its actual first-event decoder. For elapsed time $u\in[0,1]$
put

$$
\begin{gathered}
g(u)=2/(1+u)^2,\quad G_t(u)=2u/(1+u),\\
Z_K(u)=\sqrt{I_2-G_t(u)F_K},\qquad
R_K(u)=g(u)F_K(I_2-G_t(u)F_K)^{-1}.
\end{gathered}
\tag{WE.39}
$$

The current-survivor jump density in each original label is

$$
\mathcal J_{K,\ell}(u)(Y)=w_\ell g(u)
\operatorname{tr}(F_KZ_K(u)^{-1}YZ_K(u)^{-1})P_f.
\tag{WE.40}
$$

Its total effect is $R_K(u)$. Commutativity of this chosen path gives
$\dot Z_K=-R_KZ_K/2$. Pulling (WE.40) back by $\operatorname{Ad}_{Z_K(u)}$
gives $w_\ell g(u)\operatorname{tr}(F_KY)P_f$ exactly. On survivors
at time one apply the live isometry
$EB_K(I_2-F_K)^{-1/2}$, whose adjoint-times-itself is $I_2$ by
(WE.38). Its composite live matrix on the decoder input is $EB_K$.
The fixed inverse is a linear operator; no input-dependent or
acceptance normalization occurs.

For an intermediate time $a$, the no-event propagator is
$Z_K(u)Z_K(a)^{-1}$. Its squared norm has negative derivative and
is contractive. The pullback of jumps from $a$ to $b$ integrates to

$$
Z_K(a)^{-1}\bigl(Z_K(a)^2-Z_K(b)^2\bigr)Z_K(a)^{-1},
\tag{WE.41}
$$

complementary to the no-event effect at $b$. This proves whole-fibre
CP/TP chronological consistency at every cut; splitting its integral
at any intermediate time gives the same stopped instrument. Only the
surviving carrier evolves. After its first jump the label/time and
stopped output are retained, with no further positive-carrier action.
There is no deadline atom or singular failure. The terminal survivor
effect is positive definite for every finite parameter.

If $F_K$ has nonzero eigenvalue $f$, the maximal rate eigenvalue is
$g(u)f/(1-G_t(u)f)$. Its integral is $-\log(1-f)$. By (WE.12) and
(WE.38), $f/(1-f)=v/c_*(z^2)$ for the failure multiplier $v$ of this
label. Its activity is therefore $\log(1+v/c_*(z^2))\le\log(1+t)$.
If $N=0$, its rate is zero. In Theorem 4.1, $f=t_{\rm rec}/(1+t_{\rm rec})$
on each carrying label, attaining the stated uniform budget.
These are FA.13's chronological operations; competitors in the
necessity proof were never required to use them.

Add the two high encoders
$\sqrt{(1-\delta)/2}\,DE^\dagger$, one for each fair report, into
whole three-dimensional fibres, with zero rate and TP live decoder
$X\mapsto EXE^\dagger$. Fix isometries
$W_\perp:\mathbb C^2\to V^\perp$ and
$J_0:\mathbb C^2\to\mathbb C^3$. The two fair complement encoders
are $W_\perp^\dagger/\sqrt2$ into counted two-dimensional fibres,
with zero rate and TP live decoder
$X\mapsto EJ_0XJ_0^\dagger E^\dagger$. This coherently transmits the
whole complementary qubit. It has probability zero on all original
histories but is still counted. It is FA75's free completion, distinct
from the fixed certain-failure completion CG.142/CA.10.

The total live coefficient Gram is
$\operatorname{diag}(\delta,1,1)+(1-\delta)e_0e_0^T=I_3$.
Thus supported live effect is $I_3-M$ by the exact root identity
(WE.7). The low encoder effects are $K^\dagger K+N$; their attached
$N$ sum to $M$. Adding the complement gives total encoder effect
$P+(I_5-P)=I_5$. Each positive effect is bounded by this sum, proving
individual CP/TNI. All decoders above are TP on their entire fibres.
A dilation may generate these actual labels by copying the branch and
Kraus multiplicity to a permanently discarded orthogonal environment;
only the dephased label and its declared full fibre remain accessible.
Any retained correlated share would change the stated dimension.

For every complex $A\in M_5$, write $A_V=E^\dagger AE$. Forgetting
acquisition labels gives exactly

$$
\begin{aligned}
\Phi^L(A)&=E[DA_VD^\dagger+TA_VT^\dagger+SA_VS^\dagger
 +J_0W_\perp^\dagger AW_\perp J_0^\dagger]E^\dagger,\\
\Phi^f_\ell(\mathcal B)(A)&=w_\ell\left(\int_{\mathcal B}g(u)du\right)
 \operatorname{tr}(EME^\dagger A)P_f,
\quad \ell\in\{0,1,2,3,13\}.
\end{aligned}
\tag{WE.42}
$$

The second formula holds on every Borel set $\mathcal B\subseteq[0,1]$.
The live identity follows by expanding the coefficient Gram, and the
failure identity by summing the actual pulled-back $N$ in (WE.40).
They are identities on all complex matrix units. Cross-support
operators have zero image because the acquisition separates these
branches; all within-complement complex coherences are retained.
Labels $0$ and $13$ are separately zero; the other three remain
separate. There are no extra sectors or singular measures.

For every passive reference $R$ and joint complex operator $X$, the
live amplification is the sum of conjugations by
$EK E^\dagger\otimes I_R$, $K=D,T,S$, and by
$EJ_0W_\perp^\dagger\otimes I_R$. The failure amplification is

$$
w_\ell\left(\int_{\mathcal B}g(u)du\right)P_f\otimes
\operatorname{Tr}_5[(EME^\dagger\otimes I_R)X].
\tag{WE.43}
$$

This is the conditional reference operator. It is not replaced by an
unconditional marginal. Finite Kraus bilinearity and the displayed
jump identities prove these formulas at every amplification, time and
label; no sampling or selected-state agreement is used. Fixed common
metadata remain in their original state.

On each of the twelve supported histories the complement term vanishes.
Hence the complete output is the credited CG.135 output, compared
with the unchanged ideal live block and $f_y$, not $g$. All original
HALF full-cq errors are preserved. The supplied values are
$e_5=e_{27}=E_*$ and $e_{16}<71/484<37/250<E_*$. No failure or TV
deficit is added to these errors.

For an actual low label the acquisition probability is
$\operatorname{tr}[(K^\dagger K+N)\rho_{y,e,n}]$, expressly including
later-failure mass. High probabilities are $(1-\delta)A_y/2$ each,
where $A_y=\sum h_i^2p_{yi}$. Only the high pair has dimension at
least three, so every history has high mass $(1-\delta)A_y$, with
maximum $(1-\delta)A_{27}=\mathsf C(s)$ by JR34–40. The complement
is coherently counted as two. No $N$ has a $01$ entry, and reports
$\sigma$ therefore give (WE.11)'s exact contrast for the radial
recovery. Its twelve labels comprise eight low, two high and two
complement labels, all generated before decoding. This establishes
simultaneous output, cost, contrast and finite-activity attainment.
It grants no native acquisition-duration or actuator permission.
$\square$

## 6. Full generated-record TV at asymptotically minimal activity

**Definition 6.1 (unnormalized differences).** Put
$\Delta=\rho_{27,+,+}-\rho_{5,+,+}$ and

$$
\begin{gathered}
N_{ij}=\operatorname{tr}(K_i\Delta K_j^\dagger),\quad
(K_0,K_1,K_2)=(D,T,S),\quad L=\operatorname{diag}(s_0,1,1),\quad G=LNL,\\
f(z,w)=(1,z,w)G(1,z,w)^T,\qquad h(z,w)=n(z,w)^T\Delta n(z,w),\\
d_f=11m_1/64,\quad
z_f=\sqrt{m_1m_2}(\sqrt{37}-\sqrt{59})/16,\\
L_f=\sqrt{d_f^2+4z_f^2},\quad\gamma_f=(L_f-d_f)/2>0,\quad
H_\Delta=(1-\delta)\Delta A,
\quad\Delta A=\operatorname{tr}(D^\dagger D\Delta)>0,\\
T_0=\mathcal T(s_0)
=\frac12\left[H_\Delta+\frac14\sum_{\sigma,\eta=\pm1}|f(\sigma,\eta)|+L_f\right].
\end{gathered}
\tag{WE.44}
$$

The endpoint identity is the credited JR43/51 endpoint. These are
unnormalized differences, not distances conditioned on failure.

**Theorem 6.2 (universal full-record critical limit).** Let $s_n<s_0$,
$q_n=1-s_n/s_0\downarrow0$, and suppose the original classes are
feasible at finite $A_n$, with

$$
q_n(e^{A_n}-1)\longrightarrow C_{\rm end}.
\tag{WE.45}
$$

Every sequence of instruments in these classes, retaining their full
actually generated acquisition labels, has height-record TV tending to
$T_0-\gamma_f$. Consequently

$$
\boxed{\lim_n\mathcal T_{A_n}(s_n)=T_0-\gamma_f,\qquad
\lim_{s\uparrow s_0}\mathcal T_{A_{\min}(s)}(s)=T_0-\gamma_f.}
\tag{WE.46}
$$

The twelve-label recovery in Theorem 4.1 has the same limit. A
coarsened record has only the corresponding upper limit bound.

Proof. On the full compact ellipse
$\mathcal E=\{(z,w):\alpha z^2+\beta w^2=1\}$, use Lemma 2.1 on
each actual low label to define

$$
P_n=\sum_j\pi_j\delta_{(z_j,w_j)},\qquad
\nu_n=\sum_j\pi_j\upsilon_j\delta_{(z_j,w_j)}.
\tag{WE.47}
$$

Their radial pushforwards are those in Theorem 3.2. Every subsequential
limit of $P_n$ is supported on $|z|=1$ by (WE.26), hence on
$|w|=1$ by the ellipse equation. The exact moments
$\int z=\int w=\int zw=0$, $\int1=1$ then force all four corner
weights to be $1/4$ by the four-sign Fourier equations. Thus

$$
P_n\Rightarrow\frac14\sum_{\sigma,\eta=\pm1}\delta_{(\sigma,\eta)}.
\tag{WE.48}
$$

The measures $\nu_n$ have fixed mass $\mu$ on the same compact ellipse.
By (WE.27), every limit is supported on the four points

$$
z=\sigma\sqrt r,\qquad w=\eta\sqrt{W/\mu}.
\tag{WE.49}
$$

No claim about their individual sign weights is needed. At these points

$$
n=(0,\eta\sqrt{m_1/\mu},-\sigma\sqrt{m_2/\mu})^T,
\qquad h=-\frac{d_f+2\sigma\eta z_f}{\mu}<0.
\tag{WE.50}
$$

Here strict negativity follows directly from the supplied bounds
$m_1>496/1000$, $m_2<345/1000$ (FA74). Indeed

$$
\frac{d_f}{2|z_f|}=\frac{\sqrt{59}+\sqrt{37}}{16}\sqrt{\frac{m_1}{m_2}}
>\frac{27}{32}\sqrt{\frac{496}{345}}>1,
\tag{WE.51}
$$

using $\sqrt{59}>15/2$, $\sqrt{37}>6$, and
$729\cdot496=361584>353280=1024\cdot345$. This uses no new
numerical enclosure. Since $\sum N_j=M$,
$\int h\,d\nu_n=\operatorname{tr}(M\Delta)=-d_f$ exactly. By compactness,
continuity and negative limit support,

$$
\int|h|\,d\nu_n\longrightarrow d_f,\qquad
\int|f|\,dP_n\longrightarrow\frac14\sum_{\sigma,\eta}|f(\sigma,\eta)|.
\tag{WE.52}
$$

The first conclusion can equivalently be seen by writing
$\int|h|=-\int h+2\int h_+$; all limiting measures give $h_+$
integral zero. This controls every subsequence without assuming
convergence of the sign weights.

It remains to check the actual grouping loss. FA69's double rigidity,
used on the existing labels, and full decoder TP give each low
acquisition effect exactly $K_j^\dagger K_j+N_j$. Its actual signed
height difference is therefore
$\pi_j[f(z_j,w_j)+\upsilon_jh(z_j,w_j)]$. Each high label has only
$D$ products, no supported failure, and nonnegative height difference;
their sum is $H_\Delta$. Supported-zero labels contribute nothing.
Consequently the TV of the full actual acquisition label, without any
hidden refinement, is exactly

$$
T_n=\frac12\left[H_\Delta+
\int|f+\upsilon h|\,dP_n\right].
\tag{WE.53}
$$

This integral notation retains each label's own multiplier even if
several labels have the same ellipse point. It may equivalently be
an integral on the full label space. Its separated comparison has
nonnegative triangle loss bounded by

$$
0\le\int|f|\,dP_n+\int|h|\,d\nu_n
-\int|f+\upsilon h|\,dP_n
\le2\int\min\{|f|,\upsilon|h|\}\,dP_n.
\tag{WE.54}
$$

Choose a fixed open radial neighborhood $O$ of $r$ whose closure misses
$1$. The right side is at most

$$
2\left[\|f\|_\infty P_n\{z^2\in O\}
+\|h\|_\infty\nu_n\{z^2\notin O\}\right]\longrightarrow0.
\tag{WE.55}
$$

The first term vanishes by corner concentration (or (WE.26)); the
second by (WE.27). Both functions are bounded on the compact ellipse.
Thus this argument controls all actual-label live/failure grouping
losses even when multipliers diverge. It does not combine independently
optimized records, and it does not make an analytic Kraus index
observable.

Combining (WE.52)–(WE.55) proves

$$
T_n\longrightarrow\frac12\left[H_\Delta+
\frac14\sum_{\sigma,\eta}|f(\sigma,\eta)|+d_f\right]=T_0-\gamma_f.
\tag{WE.56}
$$

All concentrations and grouping estimates applied to arbitrary
instruments in the stated classes, hence prove the universal
quantifier. FA72 already supplies finite TV attainment whenever the
class is nonempty. Applying the conclusion to maximizing instruments
proves the first limit of (WE.46). Alternatively use full-label
instruments within $1/n$ of the supremum; retaining the whole label
can only increase TV. A contradiction subsequence gives the same
limit. FA73 supplies attained thresholds and (WE.31) proves their
critical scaling, yielding the second limit. The explicit recovery
also has that scaling and the entire common instrument of Section 5,
so attains the same limiting value. Classical postprocessing contracts
TV; equality is not asserted for coarsened records. $\square$

## 7. Attribution and the remaining original obligations

**Convention 7.1 (existing credit and the present increment).** CG
supplies the isolated source root, exact ranks, normalization, minimax
value and all-complex support premises, conditionally throughout.
JR34–40 supplies the sharp worst-history acquired cost and complete
record/resource curve, not CG alone. JR42–45 supplies sharp-cost
rigidity, the strong TV value, weak four-PSD reduction and finite
instrument mechanism. JR50–57 supplies the spectral plateau,
normalized four-slack dual, endpoint square-root TV law, every-multiplier
asymptotics and pre-cap obstruction. RC58–66 supplies the complete
static residual/contact curve, its genuine three-to-four real-null
transition, weights and gluing. Those static residual questions in
the historical original goal retain their supplied resolved status.
No static support pattern is transferred to finite-budget optimizers.

FA68 supplies the prescribed-path activity minimum, including arbitrary
TP survivor controls and noncommuting effect paths, and its
endpoint-equivalent different-path example. FA69 supplies the
whole-class double rigidity and exact rank-one capacity used in
Lemma 2.1 and Theorem 6.2. FA70 and FA75 supply the row-space,
chronological and full-output constructor reused with the present
finite families in Section 5. FA71 supplies the isolated attained
strong threshold, complete strong value and persistent gap. FA72
supplies the exact eight-Toeplitz-block weak SDP and finite attainment;
FA73 supplies attained weak thresholds and logarithmic divergence;
FA74 supplies the positive finite-budget deficit and fixed-$s$
$\Theta(e^{-A})$ law. FA75.2 supplies the B14 inequality with its
nonnegative actual-information slack. None is claimed anew here.
In particular certain-failure spectral rows of the unbudgeted class
are not asserted to have finite activity.

CA's no-rank-one and real exposed-face facts and IR's image/null
mechanisms enter through these supplied sources. Their classical
linear algebra, CP compatibility, no-jump/first-jump calculus, Toeplitz
and literature/library attributions keep their supplied hypotheses;
no fresh authentication or expanded theorem scope is claimed. The
additional source-specific deductions here are the feasibility-only
scalar equivalence, strict global capacity tangent, evaluated leading
constant (WE.28), uniform bounded additive recovery strip and $O(q)$
logarithmic refinement, failure-weighted concentration, and universal
full-record critical TV limit. These are ordinary conditional
repository derivations, with no worldwide novelty or absence claim.

**Definition 7.2 (remaining original mathematics and native bridge).**
The exact finite-$q$ threshold $t_{\min}(s)$ and its bounded additive
correction, the entire scalar $(s,A)$ TV frontier, its finite-budget
optimizer/contact structure, optimal TV deficit coefficients, and the
general joint or uniform crossover for limiting product larger than
$C_{\rm end}$ remain unresolved. A feasibility construction is not
asserted TV-optimal at any nonzero $q$. The critical-product limit is
not a uniform rate or a complete crossover theorem. Construction label
counts are not minimum physical alphabets, and no whole-instrument or
whole-five-mode optimizer uniqueness is inferred.

All native services remain `ASSUMED-UNVERIFIED`: lawful access to the
sole unknown reached-cut specimen, calibrated D/T/S operations, actual
label generation, coherent joint storage of every later-accessible
share, controlled whole-fibre TP decoding, acquisition duration and
placement on the same aligned original clock, actual native first
absorption at $6+u$, no later positive-carrier action, terminal live
output, and original archive/source/epoch/controller/permission
semantics. The construction gives mathematical chronological first
events, not a supplied native actuator or time interval. Geometric
OriginalControl predicates do not enact these operations. The admitted
probability-changing noncommuting controls prevent an exhaustive Schur
or diagonal menu; they also provide no missing implementation theorem.
No physical dimension/energy/acquired-mass identification, ML-error
interpretation, general NN or empirical ML result, native clock
permission, kernel certification or wider programme completion is
asserted. The unchanged original native/joint-height/clock and broader
quantum-first programme remains active.

[JR]: FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD.md
[RC]: FIB_NATIVE_COMPLETE_CONTINUATION_RESIDUAL_CONTACT_CURVE.md
[FA]: FIB_NATIVE_COMPLETE_CONTINUATION_FINITE_ACTIVITY_FRONTIER.md

## 追加锚（本行以下为增补区）
