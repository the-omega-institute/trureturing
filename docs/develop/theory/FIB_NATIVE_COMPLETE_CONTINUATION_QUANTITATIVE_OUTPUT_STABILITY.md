# Quantitative output stability and original acquisition-count deficits

## 1. Conditional premises and the unchanged experiment

**Assumption 1.1 (owning mathematical inputs).** Fix one consistent isolated
original source, with the dictionary, positivity, ranks and root TP identity
of [CG, §§13–16][CG] and [GC, Definition 3.1][GC]. The complete stopped-output
minimax certificate is the separate CG premise. The sharp worst-history cost
of jointly acquired dimension at least three and the **unaveraged** equality
face of [JR, Theorem 42.1][JR] are additional premises. In particular, for
every original instrument satisfying exact minimax error and sharp cost,
assume on the supported qutrit:

$$
\begin{gathered}
\Lambda^L=\Lambda_*:=D(\cdot)D^\dagger+T(\cdot)T^\dagger+S(\cdot)S^\dagger,
\qquad G_f=M,\qquad G_o=0,\\
Q_L^{\rm coeff}=\operatorname{diag}(\delta,1,1),\qquad
Q_H^{\rm coeff}=\operatorname{diag}(1-\delta,0,0).
\end{gathered}
\tag{QS.1}
$$

Every supported high label has zero failure effect. Every nonzero supported
low live Kraus product is, up to a common complex phase, a real product
$xD+zT+wS$ with $x\ne0$ and $x^2=\theta z^2+\omega w^2$.
These assertions apply before height optimization. The sign-averaged
conclusions of CG Theorem 17.2 alone do not provide (QS.1).

The original full-class setting, whole-fibre survival, actual-label
rigidity and physical capacity are those of [FA, Conventions 67.1–67.3,
Theorems 69.1–69.2 and 87.2][FA] and [RC, §67][RC]. Finite common laws
have the simultaneous constructor of [GC, Proposition 10.1][GC] and
[RC, Proposition 75.1][RC]. The equivalence between the common law and
the physical joint moments is [GC, Proposition 12.2][GC]. The arguments
below make their parameter correspondence explicit. They do not establish
the original source, minimax or sharp-cost premises anew. All conclusions
are ordinary conditional mathematics.

**Definition 1.2 (input and complete target).** In the five ordered modes
$0,1,2,3,13$ let

$$
\begin{gathered}
E=((e_0+e_{13})/\sqrt2,(e_1+e_3)/\sqrt2,e_2),\qquad P=EE^\dagger,\\
p_y=(y/128,(64-y)/128,1/2),\quad a_y=(\sqrt{p_{yi}})_i,\quad
U_{\epsilon,\chi}=\operatorname{diag}(\epsilon,\chi,1),\\
\rho_{y,\epsilon,\chi}=U_{\epsilon,\chi}a_ya_y^TU_{\epsilon,\chi}^\dagger,
\qquad y\in\{5,16,27\},\quad\epsilon,\chi\in\{\pm1\}.
\end{gathered}
\tag{QS.2}
$$

There is one normalized unknown specimen $E\rho_{y,\epsilon,\chi}E^\dagger$
and no prior on the twelve histories. Let $\xi_y$ be the positive vector
whose squared entries are

$$
\left(y/128,\ y(58-y)/(128(y+6)),\ y/(2(y+6))\right).
$$

The ideal stopped-cq target $\Omega_{y,\epsilon,\chi}$ is the direct sum of
the coherent live block
$EU_{\epsilon,\chi}\xi_y\xi_y^TU_{\epsilon,\chi}^\dagger E^\dagger$
and the five separately labelled Borel measures

$$
w_\ell\frac{6y}{(y+6a)^2}\,da\,P_f,\qquad
(w_0,w_1,w_2,w_3,w_{13})=(0,1/4,1/2,1/4,0),\quad0\le a\le1.
\tag{QS.3}
$$

Here $P_f$ is the fixed one-dimensional failure output and FIRST is the
absolute time $6+a$. Both zero-weight components remain separate.
The complete error is

$$
\mathsf E(\Phi)=\max_{y,\epsilon,\chi}\frac12
 \|\Phi(E\rho_{y,\epsilon,\chi}E^\dagger)-\Omega_{y,\epsilon,\chi}
                      \|_{1,\mathrm{stopped\text{-}cq}}.
\tag{QS.4}
$$

It includes live coherence, every failure measure, singular-time, abort,
wrong-support and zero-target sectors. Passive references retain their
conditional operators. This is the original twelve-input HALF objective.

**Definition 1.3 (competitors, actual record and resources).** An acquisition
is one common full complex CP instrument, followed by conditional full-output
TP decoders. All hidden Kraus multiplicities and all time laws admitted by
[FA, Definition 67.2][FA] are allowed. Its retained acquisition label is the
actual record. Its binary report is obtained by an existing common classical
kernel; a discarded Kraus index is not an extra acquired label. For a plus
report effect $F$ on the supported qutrit, the contrast requirement is
$\mathsf V(F)=2|\operatorname{Re}F_{01}|/\kappa\ge s$, where
$\kappa=h_0a+h_1b$.

Fix a finite feasible weak request, with $t=e^A-1\ge t_0>0$ and
$0\le s<s_0$. The class under consideration satisfies exactly

$$
\mathsf E(\Phi)=E_*,\qquad \mathsf V(F)\ge s,\qquad
\mathsf W=\mathsf C(s),\qquad
\sup_{j\ {\rm generated}}\int_0^1\|R_j(a)\|\,da\le A.
\tag{QS.5}
$$

The cost $\mathsf W$ is the maximum over the twelve histories of the
probability of a **joint**, future-accessible, input-dependent acquisition
fibre of dimension at least three. Specimen, memory, controller, accessible
environments and entangled shares are counted together. Activity is the
integrated operator norm on each **entire** fibre, with essential supremum
in the stipulated measurable class. Survivor controls and terminal survivor
processing are TP; loss is only through the positive integrable rate.
There is no terminal forced absorption or later positive-carrier action on
a failed carrier. No helper, copy, history oracle, reset, retry, bypass,
postselection, acceptance division or survival division is available.

Necessity concerns finite instruments, convergent countable instruments,
and only the measurable finite-dimensional-fibre, encoder/live-Kraus-field,
integrable-effect and live-Choi extension stipulated in [CG, Convention
21.3][CG] and [JR, Definition 41.1][JR]. Integral CP densities need not be
individually TNI; their integrated effect is the identity. No unrestricted
physical disintegration or infinite-dimensional coding statement is used.
Every attainer used below is finite. Write $T_{\rm actual}$ for HALF the
variation of the actual acquisition distributions between histories
$(5,+,+)$ and $(27,+,+)$, and $\mathcal T(s,t)$ for its optimum in (QS.5).
An error/cost optimizer means a member of (QS.5), without a height-optimality
assumption.

## 2. Fixed source and one joint fractional law

**Definition 2.1 (source dictionary).** In the qutrit coordinates put

$$
\begin{gathered}
D=\operatorname{diag}(h_0,h_1,h_2),\quad
T=ae_0e_1^T+be_1e_0^T,\quad
S=c_{\rm src}e_0e_2^T+de_2e_0^T,\quad M=\operatorname{diag}(0,m_1,m_2),\\
D^\dagger D+T^\dagger T+S^\dagger S+M=I_3,\\
\theta=ab/(h_0h_1),\quad\omega=c_{\rm src}d/(h_0h_2),\quad
\delta=\theta+\omega\in(0,1),\quad s_0=\sqrt\delta,\quad
\alpha=\theta/\delta>0,\quad\beta=\omega/\delta>0,\quad\alpha+\beta=1,\\
\Delta=\rho_{27,+,+}-\rho_{5,+,+},\quad
(K_0,K_1,K_2)=(D,T,S),\quad
N_{ij}=\operatorname{tr}(K_i\Delta K_j^\dagger),\\
L_{\rm coeff}=\operatorname{diag}(s_0,1,1),\quad
G=L_{\rm coeff}NL_{\rm coeff},\quad H_{\rm high}=(1-\delta)N_{00}>0,\\
V=m_2h_1^2/b^2,\quad W=m_1h_2^2/d^2,\quad \mu=\alpha V+\beta W.
\end{gathered}
\tag{QS.6}
$$

All nine source amplitudes $h_0,h_1,h_2,a,b,c_{\rm src},d,m_1,m_2$ are
positive. These are the same quantities as [GC, (GC.6)–(GC.12)][GC];
$c_{\rm src}$ distinguishes the source amplitude from capacity. If
$u_F=V/\mu$, $v_F=W/\mu$ and
$c_f=c(1,\sqrt{u_F},\sqrt{v_F})$, the inherited feasibility floor is
$t_0=W/c_f$. Feasibility of the fixed request is assumed, rather than
inferred from $t\ge t_0$ and $s<s_0$ alone. All identities refer to the
same isolated root, not independently variable points in its enclosure.

**Definition 2.2 (physical cylinder and moments).** For $\phi\in\mathbb T=
\mathbb R/(2\pi\mathbb Z)$ and $0\le\xi\le1$, define

$$
\begin{gathered}
u=\cos\phi,\quad v=\sin\phi,\quad z=u/\sqrt\alpha,\quad
w=v/\sqrt\beta,\quad h=(1,z,w)^T,\quad K_h=s_0D+zT+wS,\\
n_h=(0,dw/h_2,-bz/h_1)^T,\quad
\ell(h)=h^TGh,\quad f(h)=n_h^T\Delta n_h,\\
c(h)=\frac{h_1^2h_2^2\delta+a^2h_2^2z^2+
                         c_{\rm src}^2h_1^2w^2}
                  {h_0^2\delta+b^2z^2+d^2w^2}>0,\\
b_x=t c(h)\xi,\quad H_\xi(\phi)=\ell(h)+t c(h)\xi f(h),\quad
 g_\xi(\phi)=|H_\xi(\phi)|,\quad k(\phi,\xi)=|u|,\\
\Gamma_\xi(\phi)=(1,u,v,u^2,uv,\xi c,\xi c u^2,\xi c uv),\quad
B=(1,0,0,\alpha,0,\mu/t,\alpha V/t,0),\quad
r=\sqrt\alpha\,s/s_0.
\end{gathered}
\tag{QS.7}
$$

The denominator and numerator of $c$ are strictly positive on the whole
circle, including $z=0$ and $w=0$. The fractional space is
$X=\mathbb T\times[0,1]$; its endpoint sheets are $\xi=\eta\in\{0,1\}$.
A common law is a coefficient probability law $\pi$ on $X$ satisfying

$$
\int\Gamma\,d\pi=B,\qquad \bar k:=\int k\,d\pi\ge r,\qquad
J(\pi)=\int g\,d\pi.
\tag{QS.8}
$$

The scalar roof is $R_t(r)=\sup J(\pi)$ over these laws. For finite laws
$\pi=\sum_jp_j\delta_{(\phi_j,\xi_j)}$, positive $p_j$ count supported
atoms; they are coefficient weights, not acquisition probabilities.

**Proposition 2.3 (complete joint moment correspondence).** The eight
moment equations in (QS.8) are equivalent to the full physical equations

$$
\int hh^T\,d\pi=I_3,\qquad
\int b_x n_hn_h^T\,d\pi=M.
\tag{QS.9}
$$

Proof. This is the correspondence of [GC, Proposition 12.2][GC], with
$b_x=t c\xi$. To spell out every entry, the first five coordinates give
$\int1=1$, $\int u=\int v=\int uv=0$ and $\int u^2=\alpha$.
Since $v^2=1-u^2$, $\int v^2=\beta$. Rescaling by
$z=u/\sqrt\alpha$, $w=v/\sqrt\beta$ gives all six independent entries
of the first matrix in (QS.9). Multiplying the last three coordinates by
$t$ gives

$$
\int b_x=\mu,\quad \int b_xu^2=\alpha V,\quad\int b_xuv=0.
$$

Thus $\int b_xz^2=V$, $\int b_xzw=0$, and the pointwise ellipse identity
$\alpha z^2+\beta w^2=1$ gives $\int b_xw^2=W$. The lower diagonal
entries of the second matrix in (QS.9) are $d^2W/h_2^2=m_1$ and
$b^2V/h_1^2=m_2$, its cross entry is zero, and its first row and column
vanish. Conversely the complete live Gram gives the first five moments;
the two failure diagonals and cross entry give $V,W,0$, and the ellipse
gives $\mu$. They recover the last three moments. All constraints belong
to this one law. $\square$

## 3. Existing complex instruments reduce before height optimization

**Theorem 3.1 (one atom per supported actual low label).** Under Assumption
1.1, every member of (QS.5), with arbitrary complex encoder and decoder
Kraus multiplicities, gives one fractional atom of (QS.7) for each existing
supported nonzero low acquisition label. It obeys (QS.8), and its unchanged
actual record satisfies

$$
T_{\rm actual}=\frac{H_{\rm high}+J(\pi)}2.
\tag{QS.10}
$$

A supported-zero full encoder gives no atom, no contrast and no supported
height, while remaining counted if generated. This reduction assumes no
height optimality and introduces no readable Kraus index, endpoint
splitting, new report, or replacement acquisition effect.

Proof. The argument applies [FA, Theorems 69.1–69.2 and 87.2][FA] to the
exact error/cost face of JR42. The following details identify its use for
the present competitors.

For any positive input $Y$ to an entire decoder fibre let
$p(a)=\operatorname{tr}\mathcal S_a(Y)$. Trace balance and positivity give
$p'(a)\ge-\|R(a)\|p(a)$ almost everywhere. Multiplication by
$\exp(\int_0^a\|R(b)\|\,db)$ and integration show
$p(1)\ge e^{-A}\operatorname{tr}Y$. Terminal TP preserves this mass, so

$$
L_{\rm dec}\succeq e^{-A}I
\tag{QS.11}
$$

on the entire fibre. In particular a supported nonzero encoder has a
nonzero live composite. No assertion about a supported-zero encoder has
been used here.

Apply the separately assumed unaveraged JR42 face to this very instrument.
Every nonzero supported low product is a phase multiple of
$K(x,z,w)=xD+zT+wS$ with real coefficients and
$x^2=\theta z^2+\omega w^2$, $x\ne0$. Its determinant is
$h_0h_1h_2x(x^2-\theta z^2-\omega w^2)=0$, while its lower diagonal
$2\times2$ minor is $h_1h_2x^2\ne0$. Thus its rank is exactly two,
including both axes. A supported nonzero low fibre, whose dimension is
below three, must have dimension two.

Write its arbitrary supported encoder and live-decoder Kraus matrices as
$C_j:\mathbb C^3\to\mathbb C^2$ and
$B_i:\mathbb C^2\to\mathbb C^3$. Choose a nonzero product
$B_{i_0}C_{j_0}$. Rank two makes $C_{j_0}$ onto and $B_{i_0}$ injective.
For every real-null product,

$$
\begin{aligned}
\ker K(x,z,w)&=\mathbb C(1,-bz/(h_1x),-dw/(h_2x))^T,\\
\ker K(x,z,w)^\dagger&=
 \mathbb C(1,-az/(h_1x),-c_{\rm src}w/(h_2x))^T.
\end{aligned}
\tag{QS.12}
$$

Positive source amplitudes make either the kernel or image determine
$z/x,w/x$ uniquely. For fixed $B_{i_0}$, every nonzero $B_{i_0}C_j$
has rank two and the image of $B_{i_0}$, hence is proportional to the
chosen product. Injectivity makes the corresponding $C_j$ proportional
to $C_{j_0}$. For fixed onto $C_{j_0}$, every nonzero $B_iC_{j_0}$ has
its kernel, hence is proportional, and surjectivity makes $B_i$
proportional to $B_{i_0}$. A zero product with either fixed full-rank
factor forces its other factor to be zero. Absorbing the sums of squared
proportionality constants gives one effective encoder and live decoder
for this same acquired label. This is double rigidity within an existing
label, not an operational refinement.

Remove its common phase and normalize its coefficient vector to
$\sqrt{p_j}(s_0,z_j,w_j)$, $p_j>0$. The null identity becomes
$\alpha z_j^2+\beta w_j^2=1$ and its live product is
$K_j=\sqrt{p_j}K_{h_j}$. Let $N_j$ be its total pulled-back supported
failure effect. It is positive, dominated by $M$, and kills
$\ker K_j=\ker C_j$. Positivity and $M e_0=0$ also give $N_je_0=0$.
These independent null vectors leave exactly the line
$n_{h_j}=(0,dw_j/h_2,-bz_j/h_1)^T$, which is nonzero at either axis.
Consequently

$$
N_j=p_jb_j n_{h_j}n_{h_j}^T,\qquad b_j\ge0.
\tag{QS.13}
$$

Summing failure times, components or hidden failure Kraus operators changes
$b_j$, not the number of actual labels.

The zero-other-effect part of JR42 lifts through the onto encoder to zero
on the entire low fibre: every positive fibre input is $C_jXC_j^\dagger$
for some positive supported $X$. Full-output TP therefore yields
$L_{\rm dec}+F_{\rm dec}=I$. From (QS.11),
$F_{\rm dec}\preceq t L_{\rm dec}$; pullback gives
$N_j\preceq t p_jK_{h_j}^\dagger K_{h_j}$. For
$G_h=K_h^\dagger K_h$, the physical Schur identity of
[FA, (FA.10)][FA] is

$$
(G_h)_{00}=h_0^2\delta+b^2z^2+d^2w^2>0,\qquad
G_h-\frac{G_he_0e_0^TG_h}{(G_h)_{00}}=c(h)n_hn_h^T.
\tag{QS.14}
$$

The Schur complement of the positive $00$ pivot in $tG_h-b_jn_hn_h^T$
is $(tc(h)-b_j)n_hn_h^T$. Thus (QS.13) obeys exactly
$0\le b_j\le tc(h_j)$, without choosing a time density for the competitor.

The complete low coefficient Gram in (QS.1) gives
$\sum_jp_jh_jh_j^T=I_3$. The full failure effect gives
$\sum_jp_jb_jn_{h_j}n_{h_j}^T=M$. Hence
$\xi_j=b_j/[tc(h_j)]\in[0,1]$ defines exactly one original fractional
atom per supported nonzero low label, with $\int\Gamma=B$ by Proposition
2.3. If $m_j\in[-1,1]$ are the existing report coefficients, then

$$
\mathsf V(F)=s_0\left|\sum_jp_jm_jz_j\right|
 \le s_0\sum_jp_j|z_j|=\frac{s_0}{\sqrt\alpha}\bar k.
\tag{QS.15}
$$

The report used by this competitor is retained. Its original contrast
inequality implies $\bar k\ge r$; it need not be an equality.

Full decoder TP identifies the actual supported acquisition effect of
label $j$ as $p_jK_{h_j}^\dagger K_{h_j}+N_j$. Its signed height mass is
therefore $p_j[\ell(h_j)+b_jf(h_j)]$. Live and eventual failure signed
masses are added inside the label before taking an absolute value.
Every supported high live product is proportional to $D$, with no supported
failure. All high signed masses are nonnegative, and their complete Gram
makes their sum $H_{\rm high}$. This proves (QS.10) for the same actual
record and all its original effects.

Finally, if a full encoder vanishes on the support, positivity makes each
supported encoder Kraus matrix zero: for every supported vector the sum
of their squared norms is zero. Its supported live and failure maps,
contrast and height all vanish. Such full labels remain admitted and
counted, but supply no atom. Thus fewer than $m$ actual low labels implies
fewer than $m$ supported nonzero low atoms. The arguments apply termwise
in convergent countable classes and almost everywhere in the stipulated
measurable extension; no larger disintegration class is inferred.
$\square$

## 4. Finite realization and the physical optimum correspondence

**Proposition 4.1 (application of the common original constructor).** Every
finite law in (QS.8) has the finite original realization of [GC, Proposition
10.1][GC], with exactly its occupied low atoms and one coherent high label.
It satisfies (QS.5), (QS.10), all five separate failure Borel maps, and the
original passive-reference conditional identities. Consequently

$$
\mathcal T(s,t)=\frac{H_{\rm high}+R_t(r)}2
\tag{QS.16}
$$

whenever the law supremum is attained by a finite law, in particular for
the contact law in §5.

Proof. Proposition 2.3 and $0\le b_j\le tc(h_j)$ give exactly the complete
same-law premises of the cited constructor. The following specialization
records which outputs and resources that existing result supplies; it is
not a new source or minimax proof. Omit zero weights and set
$K_j=\sqrt{p_j}K_{h_j}$, $N_j=p_jb_jn_{h_j}n_{h_j}^T$. For an isometry
$J_j:\mathbb C^2\to\operatorname{ran}K_j^\dagger$, use

$$
\begin{gathered}
Q_j=J_j^\dagger(K_j^\dagger K_j+N_j)J_j\succ0,\quad
C_j=Q_j^{1/2}J_j^\dagger E^\dagger,\\
B_j=K_jJ_jQ_j^{-1/2},\qquad
F_j=Q_j^{-1/2}J_j^\dagger N_jJ_jQ_j^{-1/2},\qquad
B_j^\dagger B_j+F_j=I_2.
\end{gathered}
\tag{QS.17}
$$

The sole possible nonzero failure eigenvalue has odds $b_j/c(h_j)$;
rank two and these expressions remain valid on both axes. The common
relative-time functions supplied by that constructor are

$$
\begin{gathered}
g(a)=2/(1+a)^2,\quad G_{\rm time}(a)=2a/(1+a),\\
Z_j(a)=\sqrt{I-G_{\rm time}(a)F_j},\quad
R_j(a)=g(a)F_j[I-G_{\rm time}(a)F_j]^{-1},\\
\int_0^1\|R_j(a)\|\,da=\log(1+b_j/c(h_j))\le A.
\end{gathered}
\tag{QS.18}
$$

Their cumulative jump effect plus survivor effect is $I$ at every cut;
$I-F_j\succeq e^{-A}I$ on the entire qubit. Only terminal survivors
receive the isometry $EB_j(I-F_j)^{-1/2}$. FIRST is $6+a$ and failed
carriers receive no later action. This choice of $g$ realizes the laws;
it does not restrict the time laws in Theorem 3.1.

The single high encoder stacks $\sqrt{1-\delta}DE^\dagger$ with an
isometry from the complementary input subspace into a second summand.
Its counted joint fibre has dimension five, rate zero and two discarded
terminal Kraus indices. Root TP makes its effect plus all low effects
$I_5$. On every complex supported matrix the complete live Gram gives
exactly $\Lambda_*$, and the complete failure covariance gives, for every
Borel $\mathcal B\subseteq[0,1]$, the separate maps

$$
\Phi^f_\ell(\mathcal B)(X)=w_\ell\left(\int_{\mathcal B}g(a)\,da\right)
                    \operatorname{tr}(EME^\dagger X)P_f.
\tag{QS.19}
$$

For a passive reference $R$ the corresponding conditional output is

$$
w_\ell\left(\int_{\mathcal B}g(a)\,da\right)P_f\otimes
 \operatorname{Tr}_5[(EME^\dagger\otimes I_R)X],
\tag{QS.20}
$$

and every live Kraus matrix is tensored with $I_R$. Thus coherences and
conditional operators, including both zero failure components, are
preserved. The credited complete stopped-cq HALF errors are

$$
e_y=\frac12\left[\|\Lambda_*(a_ya_y^T)-\xi_y\xi_y^T\|_1+
 \sum_\ell w_\ell\int_0^1
 \left|\operatorname{tr}(Ma_ya_y^T)g(a)-\frac{6y}{(y+6a)^2}\right|da
 \right].
\tag{QS.21}
$$

The inherited CG minimax premise gives $e_5=e_{27}=E_*$ and
$e_{16}<71/484<37/250<E_*$, with the same error for all four sign pairs.
This reuses all twelve errors; it does not assert that all twelve are
equal. The inherited JR cost premise gives the sharp worst-history high
probability $\mathsf C(s)$, with the complementary input having zero
probability on the histories. Deterministic low reports $\operatorname{sgn}z_j$
give $\mathsf V=s_0\bar k/\sqrt\alpha\ge s$, with either fixed report at
$z_j=0$. The actual height is (QS.10). Thus a finite law is a genuine
conditional original attainer at its own request. Conversely Theorem 3.1
bounds every original competitor by the common-law supremum. If a finite
law attains that supremum the two bounds give (QS.16). $\square$

## 5. A complete endpoint certificate and the exact slack

**Assumption 5.1 (regular nonmerging contact certificate).** At the fixed
source and feasible request of §§1–2 choose $\lambda>0$ and
$Y=(Y_0,\ldots,Y_7)\in\mathbb R^8$ such that

$$
D_\eta(\phi):=Y\cdot\Gamma_\eta(\phi)-|H_\eta(\phi)|-
                         \lambda|\cos\phi|\ge0
\quad(\phi\in\mathbb T,\ \eta=0,1).
\tag{QS.22}
$$

These are inequalities on both **entire** endpoint circles. Their complete
equality set is exactly $m\ge1$ distinct endpoint pairs
$z_i=(\phi_i,\eta_i)$, with angles taken modulo $2\pi$ and sheets
$\eta_i\in\{0,1\}$. At every contact,

$$
u_i\ne0,\qquad H_{\eta_i}(\phi_i)\ne0,\qquad
\gamma_i=D_{\eta_i}''(\phi_i)>0.
\tag{QS.23}
$$

There is one strictly positive common contact law
$\pi^*=\sum_{i=1}^mp_i^*\delta_{z_i}$ with

$$
p_i^*>0,\qquad\sum_i p_i^*\Gamma(z_i)=B,\qquad
\sum_i p_i^*k(z_i)=r.
\tag{QS.24}
$$

No contact has a contact on the other sheet at the same angle with
$H_0H_1\ge0$. Same-angle contacts of strictly opposite nonzero height
are permitted as distinct pairs. These are hypotheses on this certificate;
they do not remove degenerate strata from the original programme.

**Theorem 5.2 (fractional gap and strictly positive inward slope).** Define
$D_\xi=Y\cdot\Gamma_\xi-|H_\xi|-\lambda k$ on $X$. Then

$$
\begin{gathered}
D_\xi=(1-\xi)D_0+\xi D_1+\tau_\xi,\\
\tau_\xi=(1-\xi)|H_0|+\xi|H_1|-
                  |(1-\xi)H_0+\xi H_1|\ge0.
\end{gathered}
\tag{QS.25}
$$

At contact $i$ set $\varepsilon_i=\operatorname{sgn}H_{\eta_i}(\phi_i)$,
$c_i=c(h_i)$, $f_i=f(h_i)$ and
$Q_i=Y_5+Y_6u_i^2+Y_7u_iv_i$. The derivative into the fractional
interval, with $\zeta=|\xi-\eta_i|$, is

$$
\begin{aligned}
\chi_i&=(1-2\eta_i)c_i(Q_i-\varepsilon_i t f_i)\\
 &=D_{1-\eta_i}(\phi_i)+|H_{1-\eta_i}(\phi_i)|
                          -\varepsilon_i H_{1-\eta_i}(\phi_i)>0.
\end{aligned}
\tag{QS.26}
$$

Without the nonmerging hypothesis, $\chi_i=0$ is equivalent to a
same-angle opposite-sheet contact with $H_{\eta_i}H_{1-\eta_i}\ge0$;
then every fraction at that angle has zero gap. For opposite nonzero
endpoint heights that are both contacts, $\chi_i=2|H_{1-\eta_i}|>0$.

Proof. Both $\Gamma_\xi$ and $H_\xi$ are affine in $\xi$. Subtracting
the chord of the endpoint absolute values gives (QS.25), with
nonnegativity from the triangle inequality, including at zero heights.
For an inward displacement write
$\xi=\eta_i+(1-2\eta_i)\zeta$. The nonzero contact height keeps sign
$\varepsilon_i$ for small $\zeta$. Differentiating the original gap gives
the first expression in (QS.26); the last three moment coordinates
contribute $(1-2\eta_i)c_iQ_i$ and the height contributes
$(1-2\eta_i)\varepsilon_i t c_i f_i$. No factor of $t$ is absorbed into
$Y$ or $c$.

The contact equality is
$Y\cdot\Gamma_{\eta_i}-\lambda k_i-
\varepsilon_iH_{\eta_i}=0$. Affineness therefore also gives

$$
\chi_i=Y\cdot\Gamma_{1-\eta_i}(\phi_i)-\lambda k_i-
                                \varepsilon_iH_{1-\eta_i}(\phi_i).
$$

Adding and subtracting $|H_{1-\eta_i}|$ proves the second expression
in (QS.26). Both its summands are nonnegative. It vanishes exactly if
the other endpoint is a contact and
$\varepsilon_i H_{1-\eta_i}\ge0$, equivalently
$H_{\eta_i}H_{1-\eta_i}\ge0$. In that case the two heights have the
same weak sign, so their absolute-value chord is exact at every fraction;
both endpoint gaps vanish, and (QS.25) gives $D_\xi(\phi_i)=0$ for
all $\xi$. Conversely a compatible endpoint pair has these properties
and forces $\chi_i=0$. Assumption 5.1 excludes exactly that case.
If the other height is nonzero and of opposite sign, the endpoint gap
is zero and $|H_o|-\varepsilon_iH_o=2|H_o|$. $\square$

**Theorem 5.3 (slack, contrast overshoot and actual HALF deficit).** Under
Assumption 5.1 the contact law attains

$$
R_t(r)=J(\pi^*)=Y\cdot B-\lambda r=:J^*.
\tag{QS.27}
$$

For every common feasible law, set $\mathcal E=J^*-J(\pi)$. Then exactly

$$
\mathcal E=\lambda(\bar k-r)+\int_XD_\xi(\phi)\,d\pi\ge0,
\qquad 0\le\bar k-r\le\mathcal E/\lambda.
\tag{QS.28}
$$

For every original competitor in (QS.5), including one that is not height
optimal, its law from Theorem 3.1 satisfies

$$
\mathcal T(s,t)-T_{\rm actual}=\mathcal E/2.
\tag{QS.29}
$$

Proof. Integrating the definition of $D$ and using the same moment target
$B$ gives
$\int D=Y\cdot B-J-\lambda\bar k$. Rearranging proves (QS.28)
with $J^*=Y\cdot B-\lambda r$, and (QS.25) makes both terms
nonnegative. The contact law has $D=0$ on its support and $\bar k=r$,
so it attains $J^*$. This proves (QS.27) over all coefficient probability
laws, without a compactness substitute for optimality. This finite law
has the original realization of Proposition 4.1, whereas Theorem 3.1
bounds every original competitor by it. Formula (QS.16) therefore holds,
and subtraction of (QS.10) gives (QS.29). The scalar $\mathcal E$ is
lost low height. It is distinct from the minimax error $\mathsf E(\Phi)$,
from diamond distance, from code leakage and from separately optimized
sheet deficits. The original contrast remains an inequality; the overshoot
term in (QS.28) is retained. $\square$

## 6. Coercivity on the entire fractional cylinder

**Theorem 6.1 (global angular-quadratic and fractional-linear control).** Let
$d_{\mathbb T}$ be shortest angular distance and define

$$
\rho(\phi,\xi)^2=\min_{1\le i\le m}
             \{d_{\mathbb T}(\phi,\phi_i)^2+|\xi-\eta_i|\}.
\tag{QS.30}
$$

Under Assumption 5.1 there is $c_0>0$ such that

$$
D_\xi(\phi)\ge c_0\rho(\phi,\xi)^2\quad((\phi,\xi)\in X),\qquad
\int_X\rho^2\,d\pi\le\mathcal E/c_0
\tag{QS.31}
$$

for every common feasible law. The assertion concerns the entire cylinder,
not just endpoint support.

Proof. At contact $i$, $u_i\ne0$ and $H_{\eta_i}(\phi_i)\ne0$ make
the endpoint gap smooth on an angular arc. Its nonnegativity and zero
value force first derivative zero. Continuity of its second derivative
and $\gamma_i>0$ allow an arc, in a local angular coordinate
$q=\phi-\phi_i$ with $|q|=d_{\mathbb T}(\phi,\phi_i)$, on which
$D_{\eta_i}''\ge\gamma_i/2$. Taylor's integral formula gives

$$
D_{\eta_i}(\phi)\ge\gamma_i q^2/4.
\tag{QS.32}
$$

Define the continuous function

$$
A_i(\phi)=Y\cdot\Gamma_{1-\eta_i}(\phi)-\lambda k(\phi)
                                  -\varepsilon_iH_{1-\eta_i}(\phi).
$$

By (QS.26), $A_i(\phi_i)=\chi_i>0$. Shrink the arc so that
$A_i\ge\chi_i/2$. Since the contact height is nonzero, further shrink
it and choose a fractional width $\zeta_i>0$ so that both
$H_\xi(\phi)$ and $H_{\eta_i}(\phi)$ have sign $\varepsilon_i$
whenever $\zeta=|\xi-\eta_i|<\zeta_i$ on this arc. Also require
$\zeta_i\le1/2$. In the opposite-height case the sign width may need
to be smaller than $1/2$; no uniform half-cylinder sign assertion is used.
On this relative neighbourhood $U_i\subset X$ the exact affine formula is

$$
D_\xi(\phi)=(1-\zeta)D_{\eta_i}(\phi)+\zeta A_i(\phi).
\tag{QS.33}
$$

Indeed the two height terms here are taken with their actual common sign,
while $A_i$ uses the signed other endpoint. Using (QS.32) and
$1-\zeta\ge1/2$ gives

$$
\begin{aligned}
D_\xi(\phi)&\ge(\gamma_i/8)q^2+(\chi_i/2)\zeta\\
&\ge\min\{\gamma_i/8,\chi_i/2\}
                  (d_{\mathbb T}(\phi,\phi_i)^2+|\xi-\eta_i|)\\
&\ge\min\{\gamma_i/8,\chi_i/2\}\rho(\phi,\xi)^2.
\end{aligned}
\tag{QS.34}
$$

There are no other zeros of $D$. At an endpoint the complete equality
set is specified by Assumption 5.1. If $0<\xi<1$, the nonnegative
identity (QS.25) can vanish only when $D_0=D_1=0$ and $\tau_\xi=0$.
For real heights and an interior fraction, equality in that triangle
inequality is precisely $H_0H_1\ge0$, including a zero height. This
would be a compatible same-angle endpoint pair, which is excluded.
Thus the listed endpoint pairs are the complete zero set on $X$.

Let $U=\bigcup_iU_i$. Its complement is closed in the compact cylinder
and contains no zero. If nonempty it has a strictly positive minimum
$d_{\rm off}=\min_{X\setminus U}D$. Also
$\rho^2\le\pi^2+1$ everywhere, since angular distance is at most $\pi$
and fractional distance at most one. Choose any positive $c_0$ no larger
than every $\min\{\gamma_i/8,\chi_i/2\}$ and, when the complement is
nonempty, than $d_{\rm off}/(\pi^2+1)$. On $U$ equation (QS.34) applies;
on its complement the latter bound applies. This proves the pointwise
inequality on the whole cylinder. Integrate and use
$\int D\le\mathcal E$ from (QS.28) to obtain (QS.31).
The complete zero set and exact full-circle feasibility are essential;
finite-grid positivity or a small stationary residual gives neither.
$\square$

## 7. Moment rounding without splitting actual atoms

**Theorem 7.1 (finite Lipschitz constant and measurable rounding).** For
$F=\Gamma$ or $F=(\Gamma,k)$ there is a finite $L>0$ such that, for
every $x=(\phi,\xi)$ and every contact $z_i$,

$$
\|F(x)-F(z_i)\|_2\le L
        \sqrt{d_{\mathbb T}(\phi,\phi_i)^2+|\xi-\eta_i|}.
\tag{QS.35}
$$

Assign each $x$ to one nearest contact in (QS.30), breaking ties by a
fixed index, and let $q_i$ be the coefficient mass assigned to $i$.
Then $q_i\ge0$, $\sum_iq_i=1$, and

$$
\left\|\sum_iq_iF(z_i)-\int_XF\,d\pi\right\|_2
                 \le L\sqrt{\mathcal E/c_0}.
\tag{QS.36}
$$

A finite law with $N$ supported original atoms has at most $N$ nonempty
rounding cells, including when different contacts have the same angle
and opposite endpoint heights. No original atom is split.

Proof. The original capacity is smooth on the compact circle with positive
denominator; its angular derivatives and all fractional coefficients are
bounded. For $F=\Gamma$, let $M_\phi$ bound the angular derivative norm
on $X$ and let $M_\xi$ bound its fractional derivative norm. For
$F=(\Gamma,k)$ choose an angular Lipschitz bound instead: $|\cos\phi|$
is globally $1$-Lipschitz along angular paths, and it is independent of
$\xi$. Thus finite $M_\phi,M_\xi$ exist for both choices. Moving along
a shortest angular path at fixed fraction and then along a fractional
segment gives, with $d=d_{\mathbb T}(\phi,\phi_i)$ and
$\zeta=|\xi-\eta_i|$,

$$
\|F(x)-F(z_i)\|_2\le M_\phi d+M_\xi\zeta
 \le\sqrt{M_\phi^2+M_\xi^2}\sqrt{d^2+\zeta^2}
 \le\sqrt{M_\phi^2+M_\xi^2}\sqrt{d^2+\zeta}.
$$

Take this constant, enlarged to a positive value if needed, as $L$.
No differentiability of $|\cos|$ at its axes is required.

The squared distances to contacts are continuous. Finite comparisons,
with the fixed-index tie rule, define Borel cells $V_i$. Their masses
$q_i=\pi(V_i)$ are nonnegative and sum to one. With $a(x)$ the assigned
index, (QS.35), the triangle inequality for the vector integral and
Cauchy–Schwarz for the probability law give

$$
\begin{aligned}
\left\|\sum_iq_iF(z_i)-\int F\,d\pi\right\|_2
&\le\int\|F(z_{a(x)})-F(x)\|_2\,d\pi\\
&\le L\int\rho\,d\pi
 \le L\sqrt{\int\rho^2\,d\pi}
 \le L\sqrt{\mathcal E/c_0}.
\end{aligned}
$$

For a finite law each original atom has a single assigned index, so it
can occupy only one cell. The argument uses the original fractions;
it never replaces them by two endpoint labels. $\square$

## 8. Quantitative deficits and minimum actual counts

**Theorem 8.1 (independent moment columns, $m\le8$).** Retain Assumptions
1.1 and 5.1, and suppose $1\le m\le8$ and
$A_\Gamma=[\Gamma(z_1)\ \cdots\ \Gamma(z_m)]$ has independent columns.
Choose any left inverse $J_{\rm left}A_\Gamma=I_m$, and set

$$
K=\max_i\|\operatorname{row}_i(J_{\rm left})\|_2>0,\qquad
p_{\min}=\min_i p_i^*>0,\qquad
\Delta_m=c_0\left(\frac{p_{\min}}{KL}\right)^2>0,
\tag{QS.37}
$$

using $F=\Gamma$ in Theorem 7.1. Every feasible law with fewer than $m$
supported original atoms has low-height deficit $\mathcal E\ge\Delta_m$.
Every original competitor in (QS.5) with fewer than $m$ supported nonzero
low labels, and hence every one with fewer than $m$ actual low labels,
has the actual HALF-TV deficit

$$
\mathcal T(s,t)-T_{\rm actual}\ge\frac{\Delta_m}{2}
       =\frac{c_0}{2}\left(\frac{p_{\min}}{KL}\right)^2.
\tag{QS.38}
$$

Proof. Rounding gives
$\|A_\Gamma q-B\|_2\le L\sqrt{\mathcal E/c_0}$, while
$A_\Gamma p^*=B$. Applying the chosen left inverse gives exactly
$q-p^*=J_{\rm left}(A_\Gamma q-B)$ and hence

$$
\|q-p^*\|_\infty\le KL\sqrt{\mathcal E/c_0}.
\tag{QS.39}
$$

A law with fewer than $m$ original atoms has fewer than $m$ occupied
rounding cells, so some $q_i=0$. For that index
$p_{\min}\le p_i^*=|q_i-p_i^*|$. Inserting (QS.39) and squaring
proves (QS.37)'s low-height bound. Theorem 3.1 maps every stated original
competitor to such a law without height optimality, and (QS.29) divides
the deficit by two. $\square$

**Theorem 8.2 (nine augmented columns and contrast overshoot).** Retain
Assumptions 1.1 and 5.1 with $m=9$, and suppose the square matrix

$$
C=\begin{pmatrix}\Gamma(z_1)&\cdots&\Gamma(z_9)\\
                         k(z_1)&\cdots&k(z_9)\end{pmatrix}
\tag{QS.40}
$$

is invertible. Use $F=(\Gamma,k)$ in Theorem 7.1 and put

$$
\begin{gathered}
K=\max_i\|\operatorname{row}_i(C^{-1})\|_2>0,\quad
p_{\min}=\min_i p_i^*>0,\quad
a_0=KL/\sqrt{c_0}>0,\quad b_0=K/\lambda>0,\\
\Delta_9=\left[
 \frac{2p_{\min}}{a_0+\sqrt{a_0^2+4b_0p_{\min}}}\right]^2>0.
\end{gathered}
\tag{QS.41}
$$

Every feasible law with fewer than nine supported original atoms has
$\mathcal E\ge\Delta_9$. Every original competitor in (QS.5) with fewer
than nine supported nonzero low labels, including every one with fewer
than nine actual low labels, has the actual HALF-TV deficit

$$
\mathcal T(s,t)-T_{\rm actual}\ge\frac{\Delta_9}{2}
 =\frac12\left[
 \frac{2p_{\min}}{a_0+\sqrt{a_0^2+4b_0p_{\min}}}\right]^2.
\tag{QS.42}
$$

Proof. Here $Cp^*=(B,r)$. The rounded vector differs from $(B,\bar k)$
by norm at most $L\sqrt{\mathcal E/c_0}$. Thus

$$
C(q-p^*)=[Cq-(B,\bar k)]+(0,\ldots,0,\bar k-r).
$$

The exact overshoot estimate (QS.28) and the row norm bound give

$$
\|q-p^*\|_\infty
 \le K\left[L\sqrt{\mathcal E/c_0}+\mathcal E/\lambda\right].
\tag{QS.43}
$$

Fewer than nine original atoms leave a missing cell. Therefore
$p_{\min}\le a_0\sqrt{\mathcal E}+b_0\mathcal E$. For
$y=\sqrt{\mathcal E}\ge0$, the polynomial
$b_0y^2+a_0y-p_{\min}$ is strictly increasing, with its unique positive
zero

$$
y_*=\frac{-a_0+\sqrt{a_0^2+4b_0p_{\min}}}{2b_0}
   =\frac{2p_{\min}}{a_0+\sqrt{a_0^2+4b_0p_{\min}}}.
$$

Hence $y\ge y_*$ and $\mathcal E\ge\Delta_9$. Theorem 3.1 and
(QS.29) give (QS.42) for unchanged original acquisitions. Omitting the
$\mathcal E/\lambda$ term would omit the achieved-contrast error in
the ninth row and would not prove this bound. $\square$

**Corollary 8.3 (conditional minimum supported and total counts).** Under
either Theorem 8.1 or Theorem 8.2, the minimum supported-low count of a
height-optimal original instrument is exactly $m$, and its minimum total
actual count is exactly $m+1$. More generally every competitor with at
most $m$ total actual labels has actual TV deficit at least
$\Delta_m/2$, using $\Delta_9$ in the nine-contact case. This is an
equality of minima, not a count identity for every instrument.

Proof. The strictly positive contact law has $m$ atoms and the constructor
of Proposition 4.1 realizes it with exactly those low labels and one high
label. Equations (QS.38) or (QS.42) prohibit fewer than $m$ supported
nonzero low labels at the optimum. Positive $H_{\rm high}$ forces at
least one supported high actual label. Supported-zero labels remain
counted, and extra high labels have the same fixed total high height;
neither reduces this lower bound. Thus the contact realization attains
both minima. If a competitor has at most $m$ total labels, at least one
is high, so it has at most $m-1$ low labels and the quantitative bound
applies. A competitor with fewer than $m$ relevant labels is already
finite, so this exclusion requires no unrestricted measurable physical
representation. $\square$

## 9. Compatible merging and degenerate boundaries

**Proposition 9.1 (compatible coincident contacts defeat endpoint counting).**
Suppose the nonmerging condition is omitted, and both endpoints at one angle
are contacts with $H_0H_1\ge0$. Then the positive full-cylinder coercivity
of Theorem 6.1 relative to only the finite endpoint contact set fails.
If the contact law gives this pair positive masses $a_p,a_s$, merging them
gives an original $(m-1)$-label low law with zero actual TV deficit.
For arbitrary nonnegative pair masses, the complete merge losses are

$$
\begin{gathered}
D_{\rm low}=a_p|H_0|+a_s|H_1|-|a_pH_0+a_sH_1|,
\qquad D_{\rm TV}=D_{\rm low}/2,\\
H_0H_1<0,\ a_p,a_s>0
\quad\Longrightarrow\quad
D_{\rm low}=2\min\{a_p|H_0|,a_s|H_1|\},\qquad
D_{\rm TV}=\min\{a_p|H_0|,a_s|H_1|\}.
\end{gathered}
\tag{QS.44}
$$

For $H_0H_1\ge0$, either height zero, or either mass zero, the appropriate
loss is zero; if both masses vanish there is no supported label.

Proof. Theorem 5.2 gives $D_\xi=0$ throughout that angular fibre. At any
interior fraction the squared distance (QS.30) from a finite set of endpoint
pairs is strictly positive. Hence no $c_0>0$ can give (QS.31).
For $a_p+a_s>0$ use exactly the original fractional merge of
[GC, Theorem 15.1][GC]: replace the pair by mass $a_p+a_s$ at fraction
$a_s/(a_p+a_s)$. Its complete live and failure moments and contrast are
unchanged, and its signed height is $a_pH_0+a_sH_1$. This gives (QS.44),
including the factor HALF for actual TV. With compatible heights and both
masses positive, it removes one supported label with no height loss. The
same original constructor realizes the merged law. With strictly opposite
nonzero heights and positive masses the actual loss in (QS.44) is strictly
positive, so this merge cannot preserve optimality. These are exact
conditional mechanisms, not an assertion that such a higher-contact source
seed exists. $\square$

**Proposition 9.2 (zero curvature prevents the stated quadratic estimate).**
At a smooth isolated endpoint contact with $D''=0$, no positive estimate
$D\ge c_0\rho^2$ of Theorem 6.1 can hold near that contact if its first
derivative vanishes. In particular nonnegative isolated quartic contact is
a genuine local obstruction to omitting the curvature assumption.

Proof. Taylor's formula gives $D(\phi_i+q)=o(q^2)$ when value, first
derivative and second derivative vanish. For a finite isolated endpoint
contact set, along that sheet and for sufficiently small $q$ the nearest
contact is this one and $\rho^2=q^2$. The ratio $D/\rho^2$ tends to zero,
contradicting every positive $c_0$. The explicit profile
$(1-\cos q)^2=q^4/4+o(q^4)$ is nonnegative and has an isolated quartic
zero modulo $2\pi$. It is a local analytic example, without an asserted
original-source realization. Other growth orders require a different
estimate. $\square$

**Convention 9.3 (regularity and exactness boundaries).** Height-zero
contacts make $\varepsilon_i$ undefined and may create absolute-value
corners. Contacts with $u_i=0$ have a contrast corner. The Lipschitz
rounding step remains valid at axes, but its regular-contact coercivity
premise does not automatically extend through such contacts. The physical
rank-two label reduction and capacity in §§2–4 include both axes without
an exception.

Zero weights must be omitted and give no count necessity:
$p_{\min}=0$ makes the stated positive deficit unavailable. Collisions,
rank loss, infinite equality sets, zero arcs, and height/report sign
changes require their own analysis. When $\lambda=0$ the nine-contact
argument loses overshoot control; the $m\le8$ argument can still apply
under its own remaining certificate and rank conditions, because it does
not use a contrast row in its left inverse. None of these cases is deleted
from the original domain by the regular theorem.

Endpoint feasibility on a grid, an incomplete zero inventory, positivity
inferred from small stationarity residuals, or a rank test for auxiliary
moments, PPT matrices or unrelated marginals does not satisfy Assumption
5.1 or the stated original column-rank hypotheses. Without the unaveraged
JR42 equality face or whole-fibre survival, Theorem 3.1's actual-label
transfer is unavailable. The abstract common-law estimate alone then gives
no theorem for general original instruments. Approximate minimax,
approximate sharp cost and approximate common moments require additional
rigidity and error estimates; they are outside this theorem.

The constants are for this fixed source, request and certificate. No
numerical value or parameter-uniform bound is asserted. Uniform constants
on a parameter patch would require uniform positive curvature, inward
slopes, weights, rank singular values and off-contact margins, bounded
Lipschitz constants and a complete compatible contact cover; for the
nine-contact estimate the multiplier must also be bounded away from zero.
Pointwise positivity supplies none of those uniform hypotheses by itself.

## 10. Mathematical interfaces and the remaining original target

**Convention 10.1 (method and literature scope).** The quantitative
cylinder, rounding and deficit arguments in §§5–8 are repo-derived
conditional deductions at the original GC/FA/RC interface. The original
joint moment and HALF normalizations, double rigidity, capacity and common
constructor are reused with their owning premises. The new analytic
estimates use elementary real absolute-value identities, Taylor's formula,
compactness, Lipschitz bounds and finite-dimensional left inverses.

Strict dual separation, curvature and full rank also occur in the
nondegenerate certificate methods of Duval–Peyré, *Exact Support Recovery
for Sparse Spikes Deconvolution*, [§3.1–§3.2, served
arXiv:1306.6909v1](https://arxiv.org/pdf/1306.6909v1). Their support-recovery
theorem requires a convolution setting, a minimal-norm nondegenerate dual
certificate, the stated value/derivative sampling rank, and a specified
noise-to-regularization regime. Those hypotheses are not a theorem about
this constrained positive common law and fractional capacity cylinder.
Likewise the dual-interpolant criterion and homogeneous M-system theorem
of de Castro–Gamboa, *Exact Reconstruction Using Support Pursuit*,
[Lemma 1.1 and Theorem 2.1, served
arXiv:1103.4951v1](https://arxiv.org/pdf/1103.4951v1), require their own
full-rank interpolation, strict off-support and moment-system conditions.
No such M-system for the present two-sheet functions is assumed. These
references supply methodological context at their stated served-text
scopes, without a version-exact historical-byte premise. Neither result
is invoked to obtain (QS.31), (QS.38), (QS.42), an original higher-contact
seed or a universal compression theorem. No priority, exhaustive literature
search or nonexistence assertion is made.

**Open problem 10.2 (first missing higher-count certificate).** For an
actual higher-count consequence, supply one eight-contact or nine-contact
law at the same isolated original source together with its complete
full-circle dual. Required data include exact source/root membership,
all endpoint zeros and strict exclusion off that complete set, positive
same-law weights solving every common moment and active contrast,
nonzero height and report signs, positive angular curvatures and inward
slopes, and independent $\Gamma$ columns for eight contacts or invertible
$(\Gamma,k)$ columns for nine. To obtain a numerical actual TV deficit,
one must additionally evaluate or rigorously bound $c_0,L,K,p_{\min}$
and, in the nine-contact case, $\lambda$.

Such an eight-contact seed would give the positive actual HALF-TV deficit
(QS.38) for every competitor with at most seven supported low labels;
such a nine-contact seed would give (QS.42) for every one with at most
eight. No such actual seed or evaluated deficit constant is specified
here. The conditional transfer from instruments to laws has been given
before height optimization; another abstract compactness assertion is
not the missing higher-count certificate. The original maximum minimum
**total** alphabet remains, at [GC, Theorem 9.2][GC]'s conditional scope,

$$
M_{\max}\in\{8,9,10\}.
\tag{QS.45}
$$

Neither a universal seven/eight-low theorem, a dense-seven-low theorem
on the actual target lift, nor exclusion of strictly decreasing affine
open rectangles follows. The necessary affine/coexistence implications
of [GC, §§16–18][GC] retain their scope; an unverified sufficient criterion
is not a realized seed. Corollary 8.3 gives no value of $M_{\max}$ in the
absence of the additional contact data.

**Open problem 10.3 (complete finite parameters, order and gluing).** The
unchanged target is the evaluated finite-$(s,A)$ roof for **all** budgets
and feasible contrasts, every common oriented failure allocation and all
live-height decompositions, including those below maximum contrast at a
fixed allocation. It still needs selected roots, positive common weights,
evaluated contact ranges, universal necessity, global ordering, certified
connected coverage and one simultaneous original attainer at every point.
Exact strong optimal minimum counts remain separate from the inherited
strong existence upper bound of eight total labels.

The [connected-interval volume][CI]'s conditional range $t=1000$,
$\lambda\in[1/4,23/5]$, and the [two-parameter strip and rectangle][TP]
retain only their own source, signed-root and whole-circle scopes. An
additional numerical target supplies no continuation or coverage. The
connections below $1/4$, intervening and later events, transverse-budget
coverage and maximal ranges remain unresolved; no event is designated
chronologically next.

All occupied and unused roots, multiplicities, report and height signs,
axes, height-zero contacts, zero arcs, collisions, zero weights, moment
ranks, capacities, and count transitions remain in the original domain.
Floor, rising-boundary, strong and degenerate endpoint, threshold, budget
and orientation gluing remain required. Regularity in Assumption 5.1
does not settle those strata. The remaining precontact/contact $K(s)$,
evaluated source parameters, physical orientations and coefficient gluing,
limiting transition-root isolation, multiplicities, sign intervals and
next terms, critical five-label/static-contact interpolation and uniform
joint-limit rates retain the supplier boundaries recorded in [GC, §§11
and 20][GC]. Limiting structure is not a finite-activity support theorem.

**Convention 10.4 (unchanged original outputs, resources and native boundary).**
The sole unknown $M_5$ specimen, all twelve signed histories $y=5,16,27$,
the complete stopped-cq HALF minimax, live complex coherence, arbitrary
passive-reference conditional operators, and five separate Borel failure
components including two zero targets remain as in §1. Contrast stays an
inequality except where a positive dual multiplier forces activity. No
acceptance or survival division, helper, copy, history oracle, reset,
retry or bypass is introduced.

Sharp cost remains the worst-history probability of a joint future-accessible
input-dependent fibre of dimension at least three, counting storage,
controller, specimen, environments and accessible entangled shares together.
Activity remains the integrated operator norm on each entire fibre, with
positive finite survivors, TP survivor controls and TP terminal processing.
FIRST remains absolute $6+a$, and failed carriers receive no later
positive-carrier action. No arbitrary-channel, product-input, LOSR, PPT,
MC, code-leakage or diamond-for-HALF-TV substitution is made. Necessity
stays finite, convergent countable and only the stipulated measurable
finite-dimensional-fibre/Kraus/integrable-effect/live-Choi class; all
attainers used here are finite.

Source existence, isolation, dictionary, ranks and root TP, complete
stopped-output minimax, the separate sharp JOINT cost and unaveraged
equality face, full-complex actual-label rigidity/capacity and one-high
constructor remain conditional original premises. Native access and
calibration, jointly counted coherent storage and shares, acquisition
duration, entire-fibre actuation, absolute FIRST alignment,
archive/source/epoch/controller/permissions, and quantum/native-count
bridges remain unresolved. A finite mathematical CP/TP realization
provides none of those physical permissions or operations. No source-final,
kernel, native, publication or through-2027 programme-completion conclusion
follows from this conditional quantitative theorem.

[CG]: FIB_NATIVE_COMPLETE_CONTINUATION_DISTINGUISHABILITY_GAP.md
[JR]: FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD.md
[FA]: FIB_NATIVE_COMPLETE_CONTINUATION_FINITE_ACTIVITY_FRONTIER.md
[RC]: FIB_NATIVE_COMPLETE_CONTINUATION_RESIDUAL_CONTACT_CURVE.md
[GC]: FIB_NATIVE_COMPLETE_CONTINUATION_GLOBAL_ACTUAL_COUNTS.md
[CI]: FIB_NATIVE_COMPLETE_CONTINUATION_CONNECTED_INTERVAL.md
[TP]: FIB_NATIVE_COMPLETE_CONTINUATION_TWO_PARAMETER_STRIP.md

## 追加锚（本行以下为增补区）
