# FIB-ATOM recursive holographic boundary geometry · Continuation III Appendix V: an original hard residual neighborhood and the H51 slice

## 211. The exact antisymmetric contrast and its twelve-dimensional slice

**Definition 211.1 (the original telescope and the additional contrast).** Retain exactly [Appendix III Definitions 134.1, 154.1 and 155.1](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_III.md), with all their inherited endpoint, source and analytic suppliers, and [Appendix IV Definition 210.1](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_IV.md#210-one-actual-common-partition-with-both-cubic-contrast-channels-zero). Thus $\theta=(a,\eta,d,b)$ ranges over every original finite $a,\eta,d>0$ and every permitted everywhere Borel representative $0<b\le M$ of $g_d$. The group $G=H^1\times\mathbb R$, original product, raw Haar measure $\mu$, source $e$, unit-source field $L\Gamma=\delta_e$, coefficient-one $w_*$, positive normalized $h$, selector $A_{\rm src}=\rho C_{\rm src}$ and full conservative source-inclusive operator $K$ are unchanged. In particular,

$$
\begin{gathered}
m=h^2\mu,\quad T_s=e^{-sK},\quad P=T_d,\quad
 g=g_{2d},\quad g_j=P^jg=g_{(2+j)d},\\
M=1+\|g_d\|_\infty,\quad c=(4M)^{-1},\quad p=\tfrac14,\qquad
 f_3=cb,\quad f_B=p,\quad f_0=f_1=(\tfrac34-cb)/2,\\
\mathcal C(v,w,z)=\int_GgvP(wPz)\,dm,\quad
\Delta(u)_{yzw}=\mathcal C(u_y,u_z,u_w)-\mathcal C(f_y,f_z,f_w).
\end{gathered}
\tag{211.1}
$$

The diffusion starts at $e$ at time zero, in the original units and clock; the epochs remain $2d,3d,4d$. The target uses the same $f$ and its original conditionally independent fresh read noises at those epochs. Write $I=\{0,1,3\}$, $\mathcal L=I\cup\{B\}$, and let $\mathcal T_6$ be the six permutations of $013$. For a bounded pointwise Borel simplex tuple $u$ on the whole $G$, retain $\mathcal H_{36}$, $\mathcal H_{50}$ and $\eta_1(u)=u_0-u_1$, $\eta_2(u)=u_B-p$ from Definition 210.1 (the first thirty-six coordinates of (154.2), followed by its six distinct-label and eight contrast coordinates), and put

$$
\begin{aligned}
\mathcal K(u)&=\mathcal C(\eta_1(u),\eta_2(u),u_3)
                -\mathcal C(\eta_2(u),\eta_1(u),u_3),\\
\mathcal H_{51}(u)&=(\mathcal H_{50}(u),\mathcal K(u)),\\
L(S)&=-S_{033}+S_{133}+S_{303}-S_{313}.
\end{aligned}
\tag{211.2}
$$

The symbol $\mathcal K$ is a scalar readout, distinct from the generator $K$. Use $H=\{v\in\mathbb R^{\mathcal L}:\sum_yv_y=0\}$, $q=(-c/2,-c/2,c,0)$ and the spaces $\mathcal W$, $\mathcal W_{13}$ of (157.6). The norm of a residual tensor is $\|S\|_\infty=\max_{y,z,w\in\mathcal L}|S_{yzw}|$. Every triple coefficient of a partition uses that partition in all three slots, including its own propagated terminal.

**Proposition 211.2 (the K-to-L identity and an independent residual equation).** Under Definition 211.1, on the exact $\mathcal H_{36}$ fiber one has

$$
\mathcal K(u)=-2\Delta(u)_{013}+2\Delta(u)_{103}+L(\Delta(u)).
\tag{211.3}
$$

Consequently on the exact $\mathcal H_{50}$ fiber, $\mathcal K(u)=L(\Delta(u))$ and

$$
\mathcal H_{51}(u)=\mathcal H_{51}(f)
\quad\Longleftrightarrow\quad L(\Delta(u))=0.
\tag{211.4}
$$

The functional $L$ is nonzero on $\mathcal W_{13}$, and

$$
\dim(\mathcal W_{13}\cap\ker L)=12.
\tag{211.5}
$$

*Proof.* On the $\mathcal H_{36}$ fiber, complement expansion gives every ordered pair law, and hence $\Delta(u)\in H^{\otimes3}$, as in (157.7). Expanding the two contrasts in (211.2), every term with a constant slot is a fixed pair coefficient. Its signed sum is zero because $f_0=f_1$. In the remaining terms substitute $u_B=1-u_0-u_1-u_3$. The terms with equal first two labels cancel, the $013,103$ terms have coefficients $-2,2$, and the other terms are $-033+133+303-313$. Their target combination is zero, again because $f_0=f_1$. This proves (211.3). The six distinct-label equations on the $\mathcal H_{50}$ fiber prove (211.4), since $\mathcal K(f)=0$.

For explicit independence, set $h_i=e_i-e_B$ for $i\in I$ and take

$$
S^\dagger=2q\otimes h_1\otimes h_3+h_0\otimes h_1\otimes q.
\tag{211.6}
$$

It belongs to $\mathcal W$. Among the six distinct-label coordinates only $013$ can contribute, and its two contributions are $-c,c$. Thus $S^\dagger\in\mathcal W_{13}$. Its coordinates $033,133,303$ vanish and $S^\dagger_{313}=2c$, so $L(S^\dagger)=-2c\ne0$. Since $\dim\mathcal W_{13}=13$ by (157.6), rank-nullity proves (211.5). These are repo-derived identities in the retained source readouts; no new source premise is introduced. $\square$

## 212. A common actual hard target neighborhood at every positive small amplitude

**Theorem 212.1 (original hard residual neighborhoods and H51 coattainment).** Under exactly Definition 211.1, for every original $\theta$ there exist bounded real Borel functions $X=(X_y)_{y\in\mathcal L}$ on the original $G$, a number $t_0>0$ and one fixed tensor $R$ such that, using the invariant representative $f^0$ of (153.6), for every $0<t<t_0$,

$$
\begin{gathered}
\sum_yX_y=0,\qquad u^{(t)}=f^0+tX
 \text{ is a pointwise simplex tuple on }G,\\
\mathcal H_{51}(u^{(t)})=\mathcal H_{51}(f),\qquad
\Delta(u^{(t)})=t^2R,\\
R\in\mathcal W_{13}\cap\ker L,\qquad
R_{BB3}=\kappa>0.
\end{gathered}
\tag{212.1}
$$

For each such $t$ there is $0<\epsilon(\theta,t)<t^2\kappa/2$ with the following actual hard-image property:

$$
\begin{split}
&S\in\mathcal W_{13},\quad
 \|S-t^2R\|_\infty<\epsilon(\theta,t)\\
&\qquad\Longrightarrow\quad
 \exists D\text{ one deterministic pointwise Borel partition of the whole }G:\quad
 \mathcal H_{50}(\mathbf1_D)=\mathcal H_{50}(f),\quad \Delta(D)=S.
\end{split}
\tag{212.2}
$$

If also $L(S)=0$, this same $D$ satisfies $\mathcal H_{51}(\mathbf1_D)=\mathcal H_{51}(f)$. Thus an entire relative neighborhood of $t^2R$ in the twelve-dimensional space $\mathcal W_{13}\cap\ker L$ is realized by actual $\mathcal H_{51}$ partitions. Every partition in (212.2) has $\Delta(D)_{BB3}>t^2\kappa/2>0$. In particular an actual H51 witness with positive BB3 exists. All constants may depend on $\theta$, and the radius may also depend on $t$; no extra restriction on $\theta$ or on its permitted representative $b$ is imposed.

*Proof.* Fix arbitrary original $\theta$. Use the quotient $\mathcal Q$, angular coordinate, measure $\nu$, orbit $q_\circ$, neighborhood $U$, invariant slack set $E$ and invariant representatives $b^0,f^0$ of (153.5)–(153.6). In particular $f_3^0\ge c\tau$ on $E$, $f_0^0,f_1^0,f_B^0\ge1/4$ on $G$, and the open orbit neighborhoods over $U$ lie in $E$. All target integrals of $f^0$ equal those of the prescribed $f$.

### 212.A. Three independently protected self-frequency pairs

Let $a_j$ be the actual orbit coefficients (153.7)–(153.10). They satisfy $a_j=a_{-j}>0$ and $a_j\to0$. Choose $n_0,n_1,m_*$ as in (154.5), and put $L_0=m_*$. For each fixed positive odd $p$, arbitrarily large odd $q$ satisfy

$$
a_{q+p}\ne a_{q-p}.
\tag{212.3}
$$

Otherwise the positive even tail would satisfy $a_{k+2p}=a_k$ for all sufficiently large even $k$. Iteration would contradict its convergence to zero. Choose successively positive odd pairs $(p_i,q_i)$, in the order $i=0,1,3$, with

$$
p_0>10L_0,\quad q_0>10p_0,\quad
p_1>10q_0,\quad q_1>10p_1,\quad
p_3>10q_1,\quad q_3>10p_3,\quad
 a_{q_i+p_i}\ne a_{q_i-p_i}.
\tag{212.4}
$$

Write $k_i^\pm=q_i\pm p_i$ and $L=q_3$. In the finite set
$\mathcal M=\{1,n_0,n_1,m_*,p_0,q_0,p_1,q_1,p_3,q_3\}$, the frequency $k_i^\pm$ has a unique unordered representation as an absolute signed sum of two members, namely $q_i,p_i$ with that sign. Indeed a pair using a frequency later than $q_i$ has difference greater than $9q_i>k_i^+$ unless it uses that same frequency twice; the equal-frequency difference is zero and the double is too large. A pair not using $q_i$ among the remaining frequencies has sum at most $2p_i<k_i^-$. Finally a pair using $q_i$ gives $k_i^\pm$ only with $p_i$, by the same separation bounds.

Use $\mathcal K_j$, $\kappa_j$ and $\mathfrak c_j^q$ of (154.6). Their continuity and $\kappa_j(q_\circ)=a_j>0$, together with the nonconstancy and analytic uniqueness of $g$ in 154.A, give one $q_\diamond\in U$ such that

$$
\begin{gathered}
g_1:=g(q_\diamond)\ne g_0:=g(q_\circ)>0,\\
\kappa_{n_1+1}(q_\diamond),\quad
\kappa_{n_1+m_*}(q_\diamond),\quad
\kappa_{n_0+1}(q_\diamond),\quad
\kappa_{k_i^+}(q_\diamond)>0\quad(i=0,1,3).
\end{gathered}
\tag{212.5}
$$

For the nonnegative normalized bumps $\phi_\delta$ of (154.8), write $V_j=\phi_\delta(q)\cos(j\vartheta)$, and set

$$
z_i=V_{p_i}+V_{q_i},\qquad
v_0=V_{n_0}+z_0,\quad v_1=V_{n_1}+z_1,\quad
v_3=V_1+V_{m_*}+z_3.
\tag{212.6}
$$

They are bounded, $E$-supported, odd, and have disjoint positive spectra. The bump parameter $\delta$ will be fixed once for all amplitudes $t$.

Use the actual quadratic densities
$\mathsf A(v,w)=gP(vPw)$, $\mathsf B(v,w)=P(gv)Pw$, $\mathsf T(v,w)=P(vP(gw))$ of (154.9). For each $i\in I$ evaluate the three columns $\mathsf A(z_i,z_i),\mathsf B(z_i,z_i),\mathsf T(z_i,z_i)$ at the rows $\mathfrak c_{k_i^+}^{q_\circ}$, $\mathfrak c_{k_i^-}^{q_\circ}$ and $\mathfrak c_{k_i^+}^{q_\diamond}$. Put $H_i=(a_{p_i}+a_{q_i})/2$, $a_i^\pm=a_{k_i^\pm}$ and $\kappa_i=\kappa_{k_i^+}(q_\diamond)$. The uniform localization formula (154.12) gives the limiting matrix

$$
M_i=\begin{pmatrix}
g_0H_i a_i^+&g_0a_{p_i}a_{q_i}&g_0H_i a_i^+\\
g_0H_i a_i^-&g_0a_{p_i}a_{q_i}&g_0H_i a_i^-\\
g_1H_i\kappa_i&b_i&g_0H_i\kappa_i
\end{pmatrix},
\qquad
b_i=\mathfrak c_{k_i^+}^{q_\diamond}
       [g_0(\mathcal K_{p_i}+\mathcal K_{q_i})^2].
\tag{212.7}
$$

The product column at $q_\circ$ has mixed coefficient $g_0a_{p_i}a_{q_i}$ at both frequencies; its self products have frequencies $0,2p_i,2q_i$. In each nested column the two mixed orders contribute $H_i$ times the corresponding heat character. At $q_\diamond$ their difference is $(g_1-g_0)H_i\kappa_i$. Subtracting the third column from the first therefore gives

$$
\det M_i=(g_1-g_0)g_0^2a_{p_i}a_{q_i}H_i^2\kappa_i(a_i^- -a_i^+)\ne0.
\tag{212.8}
$$

Uniformity on both output orbits in (154.12) preserves all three nonzero determinants for sufficiently small fixed $\delta>0$. The six distinct-label density rows (154.10) retain their seven-evaluation rank-six certificate (154.13)–(154.16): every new mixed frequency in the relevant component is greater than $2L_0$, whereas every old evaluation is at most $2L_0$. The hierarchy (212.4) gives this separation also for products involving the newly added modes in $v_3$. Fix one $\delta$ for these three determinants and the old rank-six certificate.

### 212.B. Exact lower-law corrections and all twenty-seven triple densities

Choose odd $N>10L$ and the three disjoint infinite sector sets $S_0,S_1,S_3$ of (154.18). Apply the exact original-space results 152.A–C to (212.6). Explicitly, in each $X_{E,S_i}$ choose $y_i$ and six tests $h_{i,k}$ with $\ell_j(y_i)(h_{i,k})=\delta_{jk}$, where $\ell_j$ lists the six ordered pair functionals. The finite-constraint surjectivity (152.29) supplies $w_i\in X_{E,S_i}$ with

$$
\ell_j(w_i)(h_{i,k})=0,\quad B_r(y_i,w_i)=0,\quad
q(w_i)=-q(v_i)-q(y_i),\qquad x_i=v_i+y_i+w_i.
\tag{212.9}
$$

Thus, with precisely the original $Q_r,q_r,B_r$ convention,

$$
q_r(x_i)=0,\quad Q_r(x_i,x_j)=0\ (i\ne j),\quad
\ell_j(x_i)(h_{i,k})=\delta_{jk}.
\tag{212.10}
$$

These are actual bounded, $E$-supported odd functions with finite disjoint spectra. Every protected frequency in 212.A is positive and at most $2L$. A low/high product has frequency at least $N-L>2L$; a high/high product has frequency a multiple of $N$, either zero or at least $N$. Since the actual $P$ and multiplication by $g$ preserve angular characters, all protected evaluations, on both orbits, are unchanged by (212.9).

Let $\mathsf Z$ remove the angular mean. For $abc\in I^3$ and $j\in I$ define the three-component densities

$$
R_{abc}^{(j)}=\mathbf1_E\mathsf Z\left[
 \mathbf1_{j=a}\mathsf A(x_b,x_c)
 +\mathbf1_{j=b}\mathsf B(x_a,x_c)
 +\mathbf1_{j=c}\mathsf T(x_b,x_a)\right].
\tag{212.11}
$$

They are bounded real Borel functions, even and of zero angular mean. Before multiplication by $\mathbf1_E$ they have continuous representatives on $\Omega$ by the original local smoothing used in 154.B. The original source density $g$ is bounded. Consequently these representatives are bounded by the Markov bounds and full support, and (212.11) gives legal supported directions even when $f_3^0$ has no global positive lower bound.

The twenty-seven vector densities $\mathbf R_{abc}=(R_{abc}^{(j)})_{j\in I}$ are independent in $L^2(m;\mathbb R^3)$. To prove this, suppose a linear combination with coefficients $\lambda_{abc}$ is zero. The continuous, mean-removed combination is then zero throughout the open neighborhood over $U\subset E$, by full support. Regard $\lambda$ as a trilinear functional on the basis $\{e_0,e_1,e_3\}$ of $\mathbb R^I$. For each fixed $i,j\in I$, the three protected evaluations at $k_i^\pm$ of component $j$ isolate exactly

$$
\lambda(e_j,e_i,e_i)\mathsf A(z_i,z_i)
 +\lambda(e_i,e_j,e_i)\mathsf B(z_i,z_i)
 +\lambda(e_i,e_i,e_j)\mathsf T(z_i,z_i).
\tag{212.12}
$$

The uniqueness of the signed sums in 212.A excludes every other low product; (212.9) excludes every correction product. The actual matrices whose limits are (212.7) are invertible. Hence all three coefficients in (212.12) vanish, for every $i,j$. This kills all twenty-one words with a repeated label. The remaining six coefficients multiply exactly the six distinct-label rows (154.10) in components $0,1$. Their protected low-frequency evaluations still have rank six by 212.A–B. All six coefficients therefore vanish as well.

It follows that the actual matrix

$$
\mathsf G_{abc,def}=\sum_{j\in I}\int_G R_{abc}^{(j)}R_{def}^{(j)}\,dm
\tag{212.13}
$$

is positive definite. This conclusion uses finitely many actual source evaluations and their continuity, not an added rank premise.

### 212.C. One fixed quadratic ray and sixty-three legal directions

Set $s=x_0+x_1+x_3$, $X_i=x_i$ for $i\in I$ and $X_B=-s$. Choose $t_0>0$ so that for $0<t<t_0$ the tuple $u^{(t)}=f^0+tX$ has uniform positive slack in every component on $E$. This is possible by boundedness and the lower bounds $c\tau,1/4$; outside $E$ the tuple is $f^0$. Oddness kills every marginal perturbation and every first-order pair perturbation, while (212.10) kills every quadratic pair perturbation. Thus $\mathcal H_{36}(u^{(t)})=\mathcal H_{36}(f)$.

For each triple, its linear perturbation vanishes by parity and its cubic perturbation vanishes because three odd factors change sign under the simultaneous half-turn. Multilinearity therefore gives a single fixed tensor

$$
R_{abc}=\mathcal C(X_a,X_b,f_c^0)
       +\mathcal C(X_a,f_b^0,X_c)
       +\mathcal C(f_a^0,X_b,X_c)
\quad(a,b,c\in\mathcal L),
\qquad \Delta(u^{(t)})=t^2R.
\tag{212.14}
$$

Here the terminal in each term is exactly the terminal specified by that expansion. For distinct $a,b,c\in I$, each quadratic term is zero by disjoint spectra and invariance of $f^0,g,P$; thus the six distinct-label residuals vanish. The contrasts are $\eta_1(u^{(t)})=t(x_0-x_1)$ and $\eta_2(u^{(t)})=-ts$, so all eight contrast cubics vanish by oddness. Hence $\mathcal H_{50}(u^{(t)})=\mathcal H_{50}(f)$. The exact contraction identity (157.8) puts $R$ in $\ker(\pi^{\otimes3})=\mathcal W$, and the distinct-label zeros put $R$ in $\mathcal W_{13}$.

The source propagation identity $Pf_3^0=cg$ gives, for bounded real $v,w$,

$$
\mathcal C(v,w,f_3^0)=c\langle gv,P(gw)\rangle_m
                   =\mathcal C(w,v,f_3^0).
\tag{212.15}
$$

In $\mathcal K(u^{(t)})$ the $t^2$ coefficient is zero by (212.15); the $t^3$ coefficient is zero by oddness. Proposition 211.2 gives $L(R)=0$. Finally the BB3 computation (155.11), now with (212.10), yields

$$
R_{BB3}=\kappa=c\langle gs,P(gs)\rangle_m
              =c\|T_{d/2}(gs)\|_2^2>0.
\tag{212.16}
$$

Indeed the other two quadratic BB3 terms are $-pQ_{13}(s,x_3)$ and $-pQ_{23}(s,x_3)$ and vanish by (212.10). The low mode $n_0$ occurs nontrivially in $s$ and nowhere else, so $s\ne0$. The strict inequality uses the original $g>0$ almost everywhere and injectivity of the full self-adjoint heat semigroup, as in Proposition 134.2.

Fix any $0<t<t_0$. Consider the sixty-three-coordinate map

$$
\mathcal J(u)=\left(\mathcal H_{36}(u),
                 (\mathcal C(u_a,u_b,u_c))_{abc\in I^3}\right).
\tag{212.17}
$$

For its first thirty-six rows use the nine invariant and twenty-seven odd supported directions from 154.D, with (212.10) in place of (154.20), compensating every variation in $B$. Their lower-row matrix is invertible: the marginal block is three copies of the Gram matrix of $\mathbf1_Eg_0,\mathbf1_Eg_1,\mathbf1_Eg_2$, positive definite by Lemma 147.2 and analytic uniqueness. The odd pair directions are dual to the six ordered functionals in each designated sector. Disjoint spectra make their pair block invertible by the same computation (152.34)–(152.36), with its nonzero factor $t$. Every component-$3$ variation is supported in $E$.

For each $abc\in I^3$ add the direction $e_{abc}$ with components $e_{abc,j}=R_{abc}^{(j)}$ for $j\in I$ and $e_{abc,B}=-\sum_{j\in I}R_{abc}^{(j)}$. For any even, zero-angular-mean direction of this form, the lower thirty-six differentials vanish: invariant factors pair to zero by zero angular mean and odd factors pair to zero by parity. In every triple differential, the constant-in-$t$ density is invariant and the linear-in-$t$ density is odd. Self-adjointness gives the remaining density exactly as in (212.11), since
$\mathcal C(x_a,x_b,h)=\langle h,P(x_bP(gx_a))\rangle_m$. The twenty-seven-row restriction on these directions is consequently $t^2\mathsf G$, invertible by (212.13). Thus $D\mathcal J(u^{(t)})$ on these sixty-three directions is block triangular and invertible.

Choose bounded Borel representatives, with one common null repair as in 154.D. All variations are supported in $E$ and sum to zero including their $B$ component. Uniform slack there gives a positive-radius closed Euclidean ball of parameters $z\in\mathbb R^{63}$ on which

$$
u(z)=u^{(t)}+\sum_{k=1}^{63}z_ke_k
\tag{212.18}
$$

is a pointwise simplex tuple on all of $G$.

### 212.D. One finite hard carrier uniformly covering the target neighborhood

Set $F(z)=\mathcal J(u(z))-\mathcal J(u^{(t)})$ and $A=DF(0)$. The map is polynomial, $F(0)=0$, and $A$ is invertible. Shrink the legal ball to a radius $r>0$ such that

$$
\sup_{\|z\|_2\le r}\|z-A^{-1}F(z)\|_2<r/3.
\tag{212.19}
$$

Use the common finite coordinate-quantile construction of 154.E on this entire ball. Namely choose increasing finite Borel partitions $\mathcal P_n$ generating the original Borel sigma algebra. Within each positive-mass cell $A_0$, consecutive nested first-coordinate quantile slices of masses $\int_{A_0}u_y(z)\,dm$, in order $0,1,3,B$, define $D_n(z)$. Coordinate hyperplanes have zero $m$-mass, so those slices exist with the stated masses; their endpoints are assigned consistently. Assign every zero-mass cell to $B$. This gives one deterministic pointwise Borel partition of the whole original $G$ for every parameter, with

$$
\sum_y m(D_{n,y}(z)\mathbin\triangle D_{n,y}(z'))
 \le6\sum_y\|u_y(z)-u_y(z')\|_1.
\tag{212.20}
$$

Keep precisely the original source-start path density

$$
W(x_1,x_2,x_3)=g(x_1)p_d(x_1,x_2)p_d(x_2,x_3),\qquad
W_n=\mathbb E[W\mid\mathcal P_n^{\otimes3}],\qquad
\|W-W_n\|_1\longrightarrow0.
\tag{212.21}
$$

Every coordinate of $\mathcal J$ is an integral against $W$ of three factors in $[0,1]$, using constants for absent slots. With $W_n$ those products factor cellwise. The quantile slice masses therefore make the integrals for $u(z)$ and $\mathbf1_{D_n(z)}$ equal exactly. Consequently

$$
F_n(z)=\mathcal J(\mathbf1_{D_n(z)})-\mathcal J(u^{(t)}),\qquad
\sup_{\|z\|_2\le r}\|F_n(z)-F(z)\|_2
 \le2\sqrt{63}\,\|W-W_n\|_1.
\tag{212.22}
$$

This estimate is uniform over the whole parameter ball. Every $F_n$ is continuous: telescope its slot products, integrate each changed indicator against the corresponding bounded original marginal $g,Pg,P^2g$, and apply (212.20). In particular no regularity of the moving slice boundaries is assumed.

Choose one finite $n$, independent of the target $S$, such that

$$
2\sqrt{63}\|A^{-1}\|\|W-W_n\|_1<r/3,
\qquad
0<\epsilon(\theta,t)<\min\left\{
 \frac{t^2\kappa}{2},\frac{r}{3\sqrt{27}\|A^{-1}\|}\right\}.
\tag{212.23}
$$

For every $S$ as in (212.2), define the target displacement
$v(S)=(0_{36},(S_{abc}-t^2R_{abc})_{abc\in I^3})$.
Then $\|A^{-1}v(S)\|_2<r/3$. Equations (212.19), (212.22) and (212.23) show that the continuous map

$$
z\longmapsto z-A^{-1}(F_n(z)-v(S))
\tag{212.24}
$$

maps the closed radius-$r$ ball into itself. Brouwer's finite-dimensional closed-ball theorem gives a fixed point $z_S$. For $D=D_n(z_S)$ one obtains exactly

$$
\mathcal H_{36}(\mathbf1_D)=\mathcal H_{36}(f),\qquad
\Delta(D)_{abc}=S_{abc}\quad(abc\in I^3).
\tag{212.25}
$$

Both $\Delta(D)$ and $S$ belong to $H^{\otimes3}$. Restriction to $I^3$ is injective on that tensor space: use the basis $h_i=e_i-e_B$ in each slot, or recover every $B$ index by zero contractions. Hence $\Delta(D)=S$ in all sixty-four coordinates.

Since $S\in\mathcal W_{13}$, its six distinct-label coordinates vanish and $\pi^{\otimes3}S=0$. The exact identity (157.8), valid on this same lower-law fiber, now gives all eight contrast equations. Thus $\mathcal H_{50}(\mathbf1_D)=\mathcal H_{50}(f)$. Proposition 211.2 gives the H51 conclusion whenever $L(S)=0$. The BB3 inequality follows from (212.23). This proves all the quantified statements, using one fixed finite $n$ for the entire target neighborhood at each $\theta,t$, though the root $z_S$ and partition can depend on $S$. Every evaluation against (212.21) uses this partition's own propagated terminal. Replacing $b^0$ by the originally prescribed $b$ changes no target integral, since all three original positive-time laws are absolutely continuous with respect to $m$.

The actual three-pair separation (212.3)–(212.13), its sixty-three-direction consumer (212.17)–(212.25), and the H51 slice are repo-derived relative to the retained original suppliers. The exact sector corrections consume 152.A–C, whose classical intermediates are R. Meshulam and P. Šemrl, *Locally linearly dependent operators*, [doi:10.2140/pjm.2002.203.441](https://doi.org/10.2140/pjm.2002.203.441), Theorem 2.2, and B. S. Mityagin, *The zero set of a real analytic function*, [arXiv:1512.07276v1](https://arxiv.org/abs/1512.07276v1), Proposition 0, under their stated hypotheses. The fixed-point intermediate in (212.24) is L. E. J. Brouwer, *Über Abbildung von Mannigfaltigkeiten*, [doi:10.1007/BF01456931](https://doi.org/10.1007/BF01456931), in the same closed-ball form as 154.E. These classical results are used inside the source-specific deduction and are not new standalone theorems.

The radius restriction in (212.23) excludes the origin from the asserted residual neighborhood. Thus this theorem supplies actual local residual freedom and a positive H51 witness, while leaving universal $F_{64}$ attainment or exclusion, origin enclosure, compatible choices across amplitudes, fixed-start summable label motion and physical succession unresolved. The full original source and analytic suppliers remain inherited premises, rather than new certifications of those premises. $\square$

## 追加锚（本行以下为增补区）
## 213. A finite hard carrier with anchored label-motion control

**Theorem 213.1 (an actual H51 section at a selected positive-ray partition).** Under exactly Definition 211.1, use the functions $X$, number $t_0$ and tensor $R$ of Theorem 212.1. For every original $\theta$ and every $0<t<t_0$, there exist one deterministic pointwise Borel partition $D_0$ of the whole original $G$, numbers $\rho>0$ and $0<C<\infty$, and a family of deterministic pointwise whole-$G$ Borel partitions $(D_S)_{S\in\mathcal U}$, where

$$
S_0=t^2R,\qquad
\mathcal U=\{S\in\mathcal W_{13}\cap\ker L:
                      \|S-S_0\|_\infty<\rho\},
\qquad 0<\rho<t^2\kappa/2,
\tag{213.1}
$$

such that

$$
\begin{gathered}
D_{S_0}=D_0\quad\text{pointwise on }G,\\
\mathcal H_{51}(\mathbf1_{D_S})=\mathcal H_{51}(f),\qquad
\Delta(D_S)_{yzw}=S_{yzw}
       \quad(S\in\mathcal U,\ (y,z,w)\in\mathcal L^3),\\
m(A(D_S,D_T))\le C\|S-T\|_\infty
       \quad(S,T\in\mathcal U).
\end{gathered}
\tag{213.2}
$$

Here $A(D,D')$ is the Borel set where the two partition labels differ. In particular, $\Delta(D_0)=t^2R$ and
$m(A(D_0,D_S))\le C\|S-t^2R\|_\infty$. The center partition, all finite carrier choices and both constants are fixed before the target quantifier. Each coefficient uses its displayed partition in all three slots, including its own propagated terminal. The constants may depend on $\theta,t$; no additional condition on the original parameters or the admitted representative $b$ is imposed.

*Proof.* Fix arbitrary original $\theta$ and $0<t<t_0$. Put $u^*=u^{(t)}$ and retain $\mathcal J$ from (212.17). Its sixty-three bounded, $E$-supported directions in 212.C have invertible differential at $u^*$. All four components of $u^*$ have a common strictly positive lower bound on $E$.

### 213.A. Compact localization of the actual legal directions

Let $e_1,\ldots,e_{63}$ be those directions, including their compensating $B$ components. Every coordinate of $\mathcal J$ is an integral against the original nonnegative path density $W$ of (212.21), with one factor in each used slot and a constant $1$ in each unused slot. The three slot marginals are $g,Pg,P^2g$, bounded by $\|g\|_\infty$. Thus each differential at a simplex tuple, applied to a direction $h$, is bounded in absolute value by
$3\|g\|_\infty\sum_y\|h_y\|_1$.

The measure $m$ is a finite Radon measure in the original coordinates, and $\Omega=\{r>0\}$ has full $m$-measure. Inner regularity therefore supplies compact subsets $K\subset E\cap\Omega$ for which all the finitely many quantities
$\sum_y\|\mathbf1_{G\setminus K}e_{k,y}\|_1$ are arbitrarily small. The differential matrices on the directions $\mathbf1_Ke_k$ consequently approach the original invertible matrix. Fix one such compact $K$ for which the matrix is invertible, and write

$$
\begin{gathered}
v_k=\mathbf1_Ke_k,\qquad
u(z)=u^*+\sum_{k=1}^{63}z_kv_k,\qquad
F(z)=\mathcal J(u(z))-\mathcal J(u^*),\qquad A=DF(0),\\
B=\left(\sum_{k=1}^{63}
             \left(\sum_y\|v_{k,y}\|_1\right)^2\right)^{1/2}.
\end{gathered}
\tag{213.3}
$$

Here $A$ is invertible and $0<B<\infty$. Choose bounded Borel representatives with the pointwise sum-zero convention. The inherited slack on $E$ gives a closed ball $\overline B_r\subset\mathbb R^{63}$, with $r>0$, on which $u(z)$ is a pointwise whole-$G$ simplex tuple. The map $F$ is polynomial, $F(0)=0$, and, by shrinking $r$,

$$
\sup_{z\in\overline B_r}\|I-A^{-1}DF(z)\|_{2\to2}\le\tfrac14,
\qquad
\sum_y\|u_y(z)-u_y(z')\|_1\le B\|z-z'\|_2.
\tag{213.4}
$$

This localization only restricts the correction directions; it does not restrict the original operator, source law, state space or target readout.

### 213.B. Uniform control of the original path density with one slot fixed

For $x\in\Omega$, let $p_x=p_d(x,\cdot)$. The evaluation representation (120.8)–(120.10) of Appendix II gives $p_x\in L^2(m)$ and local norm continuity of $x\mapsto p_x$. Applying that representation to $1$ and using the continuous representative of $T_d1=1$ gives $\int p_x\,dm=1$ for every $x\in\Omega$. Positivity and symmetry hold for these representatives. Since $m(G)=1$, the same row map is continuous in $L^1(m)$. These are properties of the full source-inclusive semigroup, obtained off its null exceptional set, rather than a change to a punctured semigroup.

Write $W^{(j)}_x$ for $W$ with its $j$th argument fixed at $x$, as an $L^1(m^{\otimes2})$ function of the remaining arguments. The actual density and symmetry give

$$
\begin{aligned}
W^{(1)}_x(y,z)&=g(x)p_x(y)p_d(y,z),\\
W^{(2)}_x(y,z)&=g(y)p_x(y)p_x(z),\\
W^{(3)}_x(y,z)&=g(y)p_d(y,z)p_x(z).
\end{aligned}
\tag{213.5}
$$

The representative of $g$ is continuous on $\Omega$ by (122.11) and bounded there by its essential bound, using full support. Markov conservation and symmetry show, for $x,x'\in K$,

$$
\begin{aligned}
\|W^{(1)}_x-W^{(1)}_{x'}\|_1
 &\le |g(x)-g(x')|+\|g\|_\infty\|p_x-p_{x'}\|_1,\\
\|W^{(2)}_x-W^{(2)}_{x'}\|_1
 &\le 2\|g\|_\infty\|p_x-p_{x'}\|_1,\\
\|W^{(3)}_x-W^{(3)}_{x'}\|_1
 &\le \|Pg\|_\infty\|p_x-p_{x'}\|_1.
\end{aligned}
\tag{213.6}
$$

Consequently each family $\{W^{(j)}_x:x\in K\}$ is compact in $L^1(m^{\otimes2})$ and uniformly continuous in $x$.

Choose increasing finite Borel partitions $\mathcal P_n$ generating the original Borel sigma algebra, such that $K$ is a union of cells and the maximum diameter of its positive-mass cells tends to zero. One construction joins $\{K,G\setminus K\}$ with successively finer finite coordinate grids on expanding bounded boxes. Let

$$
W_n=\mathbb E[W\mid\mathcal P_n^{\otimes3}],\qquad
\alpha_n=\max_{1\le j\le3}\mathop{\rm ess\,sup}_{x\in K}
                  \|(W-W_n)^{(j)}_x\|_{L^1(m^{\otimes2})}.
\tag{213.7}
$$

Then $\alpha_n\to0$. To verify the stronger convergence here, let $Q_n$ be conditional expectation on $\mathcal P_n$. The contractions $Q_n^{\otimes2}$ converge strongly to the identity in $L^1(m^{\otimes2})$. This convergence is uniform on each of the three compact families above: cover a family by a finite $\varepsilon$-net, use strong convergence at its centers, and use the contraction bound for the net errors. For almost every $x$ in a positive-mass cell $J\subset K$, the fixed-slot section of $W_n$ is

$$
(W_n)^{(j)}_x
 =\frac1{m(J)}\int_J Q_n^{\otimes2}W^{(j)}_{x'}\,dm(x').
\tag{213.8}
$$

Its difference from $W^{(j)}_x$ is bounded by the uniform conditional-expectation error on the compact family plus its modulus of continuity at the diameter of $J$. Both bounds tend to zero. Zero-mass cells are irrelevant to the essential supremum. Also $\|W-W_n\|_1\to0$ on the entire $G^3$, by the generating property. No global uniform kernel estimate is required.

### 213.C. Lipschitz approximation on one finite quantile carrier

For these same partitions $\mathcal P_n$, construct $D_n(z)$ by the fixed coordinate-quantile rule of 212.D, in order $0,1,3,B$, with the same endpoint assignments for all parameters. Thus every $D_n(z)$ is a deterministic pointwise Borel partition of the whole $G$. Since $u(z)=u^*$ outside $K$ and $K$ is a union of cells, these partitions agree pointwise outside $K$ for every $z$. Write $d_n(z)=\mathbf1_{D_n(z)}$ and set

$$
F_n(z)=\mathcal J(d_n(z))-\mathcal J(u^*),\qquad
E_n(z)=F_n(z)-F(z).
\tag{213.9}
$$

The slice estimate (212.20) and (213.4) give

$$
\sum_y\|d_{n,y}(z)-d_{n,y}(z')\|_1
 \le6B\|z-z'\|_2,\qquad
m(A(D_n(z),D_n(z')))\le3B\|z-z'\|_2.
\tag{213.10}
$$

To control $E_n$ quantitatively, let $\mathcal J_V$ denote the coordinate integrals defining $\mathcal J$, with density $V$ in place of $W$. The exact masses in each cell imply
$\mathcal J_{W_n}(d_n(z))=\mathcal J_{W_n}(u(z))$.
Consequently

$$
E_n(z)=\mathcal J_{W-W_n}(d_n(z))
                         -\mathcal J_{W-W_n}(u(z)).
\tag{213.11}
$$

For either tuple in this identity, telescope the difference between parameters $z,z'$ in its at most three used slots. All other slot factors have absolute value at most $1$, and every changed factor is supported in $K$. Equation (213.7) bounds each resulting integral by $\alpha_n$ times the $L^1$ norm of the changed factor. For each coordinate this gives at most three times the sum over labels. Combining the hard and soft differences with (213.4) and (213.10) proves

$$
\operatorname{Lip}_{\overline B_r}(E_n)
 \le21\sqrt{63}\,\alpha_n B\longrightarrow0,
\qquad
\|E_n(0)\|_2\le2\sqrt{63}\,\|W-W_n\|_1\longrightarrow0.
\tag{213.12}
$$

This estimate concerns the actual nonlinear common-partition integrals. In particular, a terminal change is included among the telescoped slots; no terminal is frozen at $u^*$ or at a different partition.

### 213.D. A contraction and a fixed central partition

Choose one finite $n$ such that

$$
\|A^{-1}\|\operatorname{Lip}(E_n)\le\tfrac14,
\qquad
\|A^{-1}E_n(0)\|_2<r/8,
\tag{213.13}
$$

and then fix

$$
0<\rho<\min\left\{\frac{t^2\kappa}{2},
                  \frac{r}{8\sqrt{27}\|A^{-1}\|}\right\}.
\tag{213.14}
$$

All these choices precede $S$. Put $v(S)=(0_{36},(S_{abc}-(S_0)_{abc})_{abc\in I^3})$. For $S\in\mathcal U$, consider on the closed ball $\overline B_r$ the map

$$
\Psi_S(z)=z-A^{-1}(F_n(z)-v(S)).
\tag{213.15}
$$

By (213.4) and (213.13), its Lipschitz constant is at most $1/2$. Also
$\|\Psi_S(0)\|_2\le\|A^{-1}E_n(0)\|_2+\|A^{-1}v(S)\|_2<r/4$,
so $\Psi_S(\overline B_r)\subset B_{3r/4}$. The closed Euclidean ball is complete. Iterating $\Psi_S$ from zero has successive differences bounded by a geometric sequence of ratio $1/2$; hence it converges to a fixed point $z_S$. The same contraction bound makes that fixed point unique in $\overline B_r$. For any $S,T\in\mathcal U$, subtraction of their fixed-point equations gives

$$
\|z_S-z_T\|_2
 \le\tfrac12\|z_S-z_T\|_2+\|A^{-1}\|\|v(S)-v(T)\|_2,
\qquad
\|z_S-z_T\|_2\le2\sqrt{27}\|A^{-1}\|\|S-T\|_\infty.
\tag{213.16}
$$

First set $z_0=z_{S_0}$ and $D_0=D_n(z_0)$, then define $D_S=D_n(z_S)$ on the whole target neighborhood. The unique root at $S_0$ is precisely $z_0$. Applying the identical deterministic slice rule to that identical parameter gives $D_{S_0}=D_0$ pointwise, including all endpoint and null-cell assignments. This equality is supplied by the construction itself. Combining (213.10) and (213.16) gives (213.2) with the finite positive constant

$$
C=6\sqrt{27}\,B\|A^{-1}\|.
\tag{213.17}
$$

### 213.E. All residual coordinates and the exact H51 fiber

The root equation $F_n(z_S)=v(S)$ says
$\mathcal H_{36}(\mathbf1_{D_S})=\mathcal H_{36}(f)$ and
$\Delta(D_S)_{abc}=S_{abc}$ for $abc\in I^3$.
As in (212.25), the lower laws put $\Delta(D_S)$ in $H^{\otimes3}$. Since $S\in\mathcal W_{13}\subset H^{\otimes3}$ and restriction to $I^3$ is injective there, the equality holds in all sixty-four coordinates. The six distinct-label zeros and $\pi^{\otimes3}S=0$ give the H50 equations by (157.8); $L(S)=0$ gives the remaining H51 equation by Proposition 211.2. The center is included. Every coordinate is an integral of the same partition tuple against the original $W$, and therefore uses that partition's own propagated terminal.

The original representative $b$ has not been restricted: $u^*$ uses the inherited $f^0$, whose target integrals equal those of every admitted $f$. All three slot laws are absolutely continuous with respect to $m$. Thus the common null repairs and that representative substitution preserve all target equations, with the whole-$G$ partitions still specified pointwise.

The new deduction is the compact localization of the source-specific rank-sixty-three directions, the fixed-slot estimate (213.7)–(213.12), and its quantitative inverse on a single finite actual carrier. It consumes the original source and analytic suppliers of Definition 211.1 and the proved rank in 212.C; it assumes no rank or inverse property of a hard partition. The contraction step is the classical principle of S. Banach, *Sur les opérations dans les ensembles abstraits et leur application aux équations intégrales*, Fund. Math. 3, 133–181, [doi:10.4064/fm-3-1-133-181](https://doi.org/10.4064/fm-3-1-133-181), in the complete closed-ball form whose geometric-iteration proof is given above. Conditional-expectation convergence and compactness are used only as intermediate facts in the displayed source-specific estimates. $\square$

**Corollary 213.2 (exact radial whole-residual decrease from the selected partition).** With exactly the $D_0,\rho,C$ selected in Theorem 213.1, put $N_0=\|\Delta(D_0)\|_\infty=t^2\|R\|_\infty>0$. For every requested decrease

$$
0<\delta<\min\{\rho,N_0/2\},\qquad
S_\delta=(1-\delta/N_0)t^2R,
\tag{213.18}
$$

there is an actual deterministic pointwise whole-$G$ Borel partition $D_\delta$ such that

$$
\begin{gathered}
\mathcal H_{51}(\mathbf1_{D_\delta})=\mathcal H_{51}(f),\qquad
\Delta(D_\delta)=S_\delta\quad\text{in all sixty-four coordinates},\\
\|\Delta(D_\delta)\|_\infty=N_0-\delta<N_0,\qquad
\Delta(D_\delta)_{BB3}=(1-\delta/N_0)t^2\kappa>0,\\
m(A(D_0,D_\delta))\le C\delta.
\end{gathered}
\tag{213.19}
$$

*Proof.* The target $S_\delta$ lies in $\mathcal W_{13}\cap\ker L$ and
$\|S_\delta-S_0\|_\infty=\delta<\rho$. Take precisely $D_\delta=D_{S_\delta}$ from the selected family (213.2). Homogeneity of the residual norm and the strict positivity of $1-\delta/N_0$ give every equality and inequality in (213.19). In the amplitude notation $S_\varepsilon=(1-\varepsilon)^2t^2R$, the same family gives

$$
m(A(D_0,D_{S_\varepsilon}))
 \le C(2\varepsilon-\varepsilon^2)t^2\|R\|_\infty
\quad\text{whenever }0<\varepsilon<1
\text{ and }(2\varepsilon-\varepsilon^2)N_0<\rho.
\tag{213.20}
$$

All coefficients use their own actual partition terminals, as in Theorem 213.1. The full-neighborhood section proves these radial estimates; no converse from radial estimates to transverse selection is needed or asserted.

The radius in (213.14) keeps every target in this family at positive BB3. The result concerns a selected starting partition and its nearby targets. It does not establish control from an arbitrary prescribed hard partition, extension to zero residual, uniform carrier capacity across amplitudes or along an iteration, a summable-to-zero chain, universal $F_{64}$ attainment or exclusion, or physical succession. The original source and analytic suppliers remain inherited premises. $\square$

## 追加锚（本行以下为增补区）

## 214. Refined exact H51 sections and the cost of returning to the soft target

**Theorem 214.1 (prescribed refinements of the actual nonlinear sections).** Retain exactly Definition 211.1, with every original $\theta$, every admitted representative $b$ and all inherited source and analytic suppliers. Use precisely $X,t_0,R,\kappa$ of Theorem 212.1, and write

$$
\|v\|_{\oplus1}=\sum_{y\in\mathcal L}\|v_y\|_{L^1(m)},
\qquad \Lambda=\|X\|_{\oplus1},\qquad u^{(t)}=f^0+tX.
\tag{214.1}
$$

Let $(\mathcal P_j)$ be any increasing sequence of finite Borel partitions generating the original Borel sigma algebra modulo $m$-null sets, and let $Q_j$ denote conditional expectation on $\mathcal P_j$. Prescribe any $0<t_j<t_0$ and any $\varepsilon_j>0$ tending to zero. There exist increasing finite Borel carriers $\mathcal R_j$, each refining $\mathcal P_j$, and, for each $j$, numbers $\rho_j,C_j>0$, soft tuples $u_{j,S}$ and deterministic pointwise whole-$G$ Borel partitions $D_{j,S}$, indexed by

$$
S_j^0=t_j^2R,\qquad
\mathcal U_j=\{S\in\mathcal W_{13}\cap\ker L:
                    \|S-S_j^0\|_\infty<\rho_j\},\qquad
0<\rho_j<\min\{t_j^2\kappa/2,\varepsilon_j\},
\tag{214.2}
$$

with the following simultaneous properties:

$$
\begin{gathered}
\mathcal H_{51}(\mathbf1_{D_{j,S}})=\mathcal H_{51}(f),\qquad
\Delta(D_{j,S})=S\quad\hbox{in all sixty-four coordinates},\\
m(A(D_{j,S},D_{j,T}))\le C_j\|S-T\|_\infty
       \quad(S,T\in\mathcal U_j),\\
\int_A\mathbf1_{D_{j,S,y}}\,dm=\int_Au_{j,S,y}\,dm
       \quad(A\in\mathcal R_j,\ y\in\mathcal L),\\
Q_j(\mathbf1_{D_{j,S,y}})=Q_j u_{j,S,y},\\
\sup_{S\in\mathcal U_j}\|u_{j,S}-u^{(t_j)}\|_{\oplus1}
 \le\varepsilon_j,\qquad
\sup_{S\in\mathcal U_j}\|u_{j,S}-f\|_{\oplus1}
 \le t_j\Lambda+\varepsilon_j.
\end{gathered}
\tag{214.3}
$$

The carrier and constants precede the target quantifier, and $D_{j,S_j^0}$ is the actual central partition of its own section, pointwise. The soft tuples are preimages for finite cell masses; their exact nonlinear coefficients need not equal those of their hard images. Cell-mass matching here is to $u_{j,S}$, not an added requirement of exact cell-mass matching to $f$. All residual equalities use the same original operator, source, measure, units, clock and each displayed partition's own propagated terminals. No compatibility between the central partitions for different $j$ is assumed.

*Proof.* Fix the original $\theta$. For each $t_j$, use the actual compact localization of the sixty-three directions in 213.A. Denote its compact subset of $E\cap\Omega$ by $K_j$, its directions by $v_{j,k}$, its invertible differential by $A_j$, and the positive constant in (213.3) by $B_j$. These are supplied by 212.C and 213.A, not rank or inverse hypotheses on a hard partition. Choose the legal ball radius $r_j>0$ small enough that (213.4) holds and

$$
u_j(z)=u^{(t_j)}+\sum_{k=1}^{63}z_kv_{j,k},\qquad
B_jr_j\le\varepsilon_j\quad(\|z\|_2\le r_j).
\tag{214.4}
$$

Shrinking a legal ball preserves its pointwise simplex property and the differential estimate. The product-$L^1$ bound follows from Cauchy--Schwarz exactly as in (213.4).

At index $j$, join $\mathcal P_j$, the preceding carrier $\mathcal R_{j-1}$ when $j>1$, and $\{K_j,G\setminus K_j\}$ with increasing finite coordinate grids on expanding boxes. This produces, for this fixed $j$, a generating sequence of finite Borel refinements. Its cells inside $K_j$ have maximum diameter tending to zero, even when the prescribed cells have irregular boundaries. Consequently the proof of (213.7)--(213.8) applies unchanged: conditional expectation in the two free slots converges uniformly on the three compact families of fixed-slot densities, and averaging inside a cell of $K_j$ adds only their modulus of continuity at its diameter. Both the fixed-slot error and the global $L^1$ error of $W$ tend to zero. Finite joins impose no additional regularity assumption on $\mathcal P_j$.

Apply the same coordinate-quantile rule as in 212.D and 213.C, with order $0,1,3,B$ and fixed endpoint and null-cell assignments. For every parameter in the legal ball it matches all four soft masses on every carrier cell. The first coordinate has no atoms on any such cell, because $m\ll\mu$ and coordinate hyperplanes have zero Haar measure. The slice estimate (213.10) and both errors in (213.12) therefore hold along this refined sequence. Choose one finite carrier $\mathcal R_j$ far enough that

$$
\|A_j^{-1}\|\operatorname{Lip}(E_{j,n})\le\tfrac14,
\qquad \|A_j^{-1}E_{j,n}(0)\|_2<r_j/8,
\tag{214.5}
$$

where $E_{j,n}$ is the hard-minus-soft error map (213.9) on this ball. Then choose

$$
0<\rho_j<\min\left\{t_j^2\kappa/2,\varepsilon_j,
             \frac{r_j}{8\sqrt{27}\|A_j^{-1}\|}\right\}.
\tag{214.6}
$$

The contraction (213.15) now has, for every $S\in\mathcal U_j$, a unique root $z_{j,S}$ in that ball. Set $u_{j,S}=u_j(z_{j,S})$ and use exactly its quantile partition for $D_{j,S}$. All choices of roots inside the designated balls obey (214.4); uniqueness in particular fixes the center pointwise. Equations (213.16)--(213.17) give the finite constant $C_j=6\sqrt{27}B_j\|A_j^{-1}\|$. Equation (213.11) gives the exact cell masses, and summing over the refinement of each $\mathcal P_j$ cell proves the $Q_j$ identity. Since $f^0=f$ almost everywhere, (214.4) proves both norm bounds in (214.3).

The root equations give the original thirty-six lower laws and the twenty-seven coordinates on $I^3$. Zero contractions and injectivity of restriction from $H^{\otimes3}$ recover all sixty-four coordinates, as in 213.E. Membership in $\mathcal W_{13}\cap\ker L$ gives exactly H51 by (157.8) and Proposition 211.2. In particular every target still has $S_{BB3}>t_j^2\kappa/2>0$. The common null repairs affect no original positive-time law and do not restrict the admitted $b$.

The finite cell-mass step is a linear intermediate, consistent with the classical finite atomless-measure purification of A. Dvoretzky, A. Wald and J. Wolfowitz, *Relations among certain ranges of vector measures*, Pacific J. Math. 1 (1951), 59--74, [doi:10.2140/pjm.1951.1.59](https://msp.org/pjm/1951/1-1/pjm-v1-n1-p06-s.pdf), Theorem 4 and Lemma 2, pp. 66--67. That theorem alone supplies no common-partition cubic equation or continuous section. Here exact nonlinear equality is supplied by the source-specific rank and fixed-slot contraction of 212.C and 213.A--E. The refinement with uniformly small soft preimages is a repo-derived consequence of those original suppliers, not a new linear purification theorem. $\square$

**Corollary 214.2 (quantitative cell defect and the obstruction to summable soft resets).** In Theorem 214.1 suppose $t_j\to0$. For any whole-$G$ Borel partition $D$ and any fixed whole-$G$ Borel partition $E$, put

$$
\begin{gathered}
\beta_j(D)=\sum_y\|Q_j(\mathbf1_{D_y}-f_y)\|_1,\qquad
\alpha_f(E)=1-\sum_y\int_{E_y}f_y\,dm,\\
\xi_j(E)=\sum_y\|\mathbf1_{E_y}-Q_j\mathbf1_{E_y}\|_1,
\qquad a_\theta=\tfrac58+\tfrac c2.
\end{gathered}
\tag{214.7}
$$

The following quantitative estimates and uniform limits hold:

$$
\begin{gathered}
|m(A(D,E))-\alpha_f(E)|\le\xi_j(E)+\tfrac12\beta_j(D),\\
\tfrac58+\tfrac c2\le\alpha_f(E)\le1-c,\qquad
\xi_j(E)\longrightarrow0,\\
\sup_{S\in\mathcal U_j}\beta_j(D_{j,S})
 \le t_j\Lambda+\varepsilon_j\longrightarrow0,\\
\sup_{S\in\mathcal U_j}
 |m(A(D_{j,S},E))-\alpha_f(E)|\longrightarrow0.
\end{gathered}
\tag{214.8}
$$

Thus every diagonal choice $S_j\in\mathcal U_j$ and every legal-root realization of these sections has exactly H51, exactly the requested full residual $S_j\to0$, and componentwise weak-star limit $f$, while remaining positively separated from every fixed hard anchor. No such sequence, or subsequence with indices tending to infinity, can have summable total label motion.

More precisely, for every sequence of actual whole-$G$ Borel partitions $E_j$ satisfying $\sum_jm(A(E_j,E_{j+1}))<\infty$, there is an eventual-label partition $E_\infty$. With

$$
\tau_j=\sum_{k=j}^\infty m(A(E_k,E_{k+1})),\qquad
\zeta_j(E_\infty)=\sum_y
 \|(I-Q_j)(\mathbf1_{E_{\infty,y}}-f_y)\|_1,
\tag{214.9}
$$

one necessarily has

$$
\begin{gathered}
|\beta_j(E_j)-2\alpha_f(E_\infty)|
 \le2\tau_j+\zeta_j(E_\infty),\qquad
\zeta_j(E_\infty)\longrightarrow0,\\
\lim_{j\to\infty}\beta_j(E_j)
 =2\alpha_f(E_\infty)\ge\tfrac54+c>0.
\end{gathered}
\tag{214.10}
$$

These necessary nonzero defects do not exclude a different compatible continuation. If such a summable chain also has full residual tending to zero, its endpoint still attains the original law by (155.31)--(155.33).

*Proof.* The mass-one density in (134.4) and $[b]=g_d$ give $\int b\,dm=1$ and $0<c\le1/8$. From the pointwise source normalization in (211.1),

$$
0<f_3=cb\le\tfrac14=f_B\le f_0=f_1\le\tfrac38,
\qquad
\int f_3\,dm=c,\quad \int f_0\,dm=\tfrac38-\tfrac c2.
\tag{214.11}
$$

For each point the selected $f_y$ lies between $f_3$ and $f_0$. Integration proves the two bounds for $\alpha_f$, including the source-dependent $c/2$ term. For unrestricted hard anchors they are attained by assigning all of $G$ to $0$ or to $3$, respectively; sharpness here asserts no calibration of those anchors.

Write $e_y=\mathbf1_{E_y}$, $d_y=\mathbf1_{D_y}$, $a_y=Q_je_y$ and $h_y=Q_j(d_y-f_y)$. Conditional expectation gives

$$
\sum_y\int e_y(d_y-f_y)\,dm
 =\sum_y\int(e_y-a_y)(d_y-f_y)\,dm
                  +\int\sum_y a_yh_y\,dm.
\tag{214.12}
$$

The first term has absolute value at most $\xi_j(E)$. Pointwise, $0\le a_y\le1$ and $\sum_yh_y=0$, so $|\sum_ya_yh_y|\le\frac12\sum_y|h_y|$. Also $m(A(D,E))=1-\sum_y\int e_yd_y\,dm$. This proves the first estimate in (214.8) with its factor $1/2$.

On a generating increasing finite algebra, $Q_jv\to v$ in $L^1$ for every $v\in L^1(m)$: approximate $v$ in $L^1$ by a simple function measurable on some finite algebra, and use the contraction of $Q_j$ for the two approximation errors. Such simple functions are dense because these algebras generate modulo null sets. This proves $\xi_j(E)\to0$ and later $\zeta_j(E_\infty)\to0$. The exact cell identity in (214.3) and the same contraction give $\beta_j(D_{j,S})\le\|u_{j,S}-f\|_{\oplus1}$. The remaining bounds and the uniform fixed-anchor limit follow. They hold for all allowed targets and roots, with no relation between choices at different indices.

For completeness, for a bounded Borel test $h$ and a single label, the cell identity gives uniformly in $S$

$$
\left|\int h(\mathbf1_{D_{j,S,y}}-f_y)\,dm\right|
 \le\|h-Q_jh\|_1+\|h\|_\infty\beta_j(D_{j,S}).
\tag{214.13}
$$

The right side tends to zero. Truncation extends this to every $L^1$ test, using $|\mathbf1_{D_{j,S,y}}-f_y|\le1$. Thus the weak-star limit is $f$. Equation (214.2) also gives $\|S_j\|_\infty\le t_j^2(\|R\|_\infty+\kappa/2)\to0$, with exact H51 and full-coordinate equality at each finite index.

For a summable chain, the union of change sets from index $j$ onward has measure at most $\tau_j$. Outside their null limsup the labels are eventually constant. Assign $B$ on that Borel exceptional set; the resulting $E_\infty$ satisfies $m(A(E_j,E_\infty))\le\tau_j$, as in (155.32). Contractivity and $\|\mathbf1_E-\mathbf1_F\|_{\oplus1}=2m(A(E,F))$ give

$$
|\beta_j(E_j)-\beta_j(E_\infty)|\le2\tau_j,\qquad
\left|\beta_j(E_\infty)
 -\|\mathbf1_{E_\infty}-f\|_{\oplus1}\right|
 \le\zeta_j(E_\infty).
\tag{214.14}
$$

For a hard partition and a simplex tuple, the last unconditioned norm is exactly $2\alpha_f(E_\infty)$. This proves (214.10), contradicting the vanishing-defect limit for every diagonal sequence above. Applying the same argument to any subsequence uses the corresponding generating subsequence of $\mathcal P_j$, and gives the same contradiction.

The consumer is the summable endpoint criterion (155.31): repeated independent selections from these increasingly refined, near-$f$ soft families cannot meet it, even with exact H51 and arbitrarily small prescribed full residuals. The assertion does not give a positive lower bound on consecutive step sizes; the anchor is fixed before its limit is taken. It does not restrict sections or chains with nonvanishing cell defect, solve a finite-carrier origin equation, settle universal $F_{64}$ attainment or exclusion, or provide physical succession. $\square$

**Corollary 214.3 (separation inside one exact positive full-residual H51 fiber).** For every original $\theta$ and every fixed $0<t<t_0$, the exact fiber

$$
\mathscr F_t=\{D:\ D\text{ is a deterministic pointwise whole-}G
 \text{ Borel partition},\quad
 \mathcal H_{51}(\mathbf1_D)=\mathcal H_{51}(f),\quad
 \Delta(D)=t^2R\text{ in all sixty-four coordinates}\}
\tag{214.15}
$$

contains a sequence $D_j$ obtained from Theorem 214.1 with $t_j=t$ and $S=S_j^0=t^2R$, such that $\mathbf1_{D_{j,y}}\overset{*}{\rightharpoonup}u_y^{(t)}$ for every label. Put

$$
a_t=1-\mathop{\rm ess\,sup}_{x\in G}\max_yu_y^{(t)}(x).
\tag{214.16}
$$

Then $a_t>0$, and for every fixed whole-$G$ hard partition $E$,

$$
m(A(D_j,E))\longrightarrow
 \alpha_{u^{(t)}}(E):=1-\sum_y\int_{E_y}u_y^{(t)}\,dm
 \ge a_t>0.
\tag{214.17}
$$

The fiber $\mathscr F_t$, modulo null changes and with label-motion distance $m(A(\cdot,\cdot))$, contains an infinite $a_t/2$-separated subset. Its indicator tuples are not relatively compact in product $L^1$. The full residual in this conclusion is fixed, equal for every member, and has BB3 exactly $t^2\kappa>0$.

*Proof.* Use any prescribed generating refinements and $\varepsilon_j\downarrow0$ in Theorem 214.1, keeping this one $t$. At the centers, (214.3) gives $\Delta(D_j)=t^2R$ and exact H51, and

$$
\sum_y\|Q_j(\mathbf1_{D_{j,y}}-u_y^{(t)})\|_1
 \le\varepsilon_j\longrightarrow0.
\tag{214.18}
$$

The test argument (214.13), now with $u^{(t)}$ in place of $f$, proves the claimed weak-star limit. Pairing it with the fixed indicators of $E$ proves the limit (214.17). Equivalently, (214.12) gives its quantitative error at most $\xi_j(E)+\varepsilon_j/2$.

Denote the invariant slack set $E$ of 212.A--C by $E_{\rm sl}$ in this paragraph, to distinguish it from the fixed hard anchor. The supplier 212.C gives a uniform $\sigma_t>0$ such that all four components of $u^{(t)}$ are at least $\sigma_t$ on $E_{\rm sl}$. Consequently their maximum there is at most $1-3\sigma_t$. Outside $E_{\rm sl}$ one has $X=0$ and $f^0=f$ almost everywhere, so (214.11) bounds the maximum by $3/8$. Thus

$$
a_t\ge\min\{3\sigma_t,5/8\}>0.
\tag{214.19}
$$

For each fixed $D_i$, (214.17) makes $m(A(D_j,D_i))>a_t/2$ for every sufficiently large $j$. Recursively choose an increasing subsequence whose next index is beyond the finitely many thresholds for all preceding choices. This gives the infinite separated subset, and hence failure of relative compactness in product $L^1$, whose distance is twice the label-motion distance. In fact the displayed $D_j$ has no product-$L^1$ convergent subsequence: a product-$L^1$ limit of finite-label indicator tuples is again a hard tuple modulo null sets, by passage to an almost-everywhere convergent subsequence; such a limit would contradict (214.17) for that fixed hard anchor.

This is separation within one exact nonlinear full-residual fiber, obtained by retaining the section roots through arbitrary finite refinements. It does not infer nonattainment at residual zero. The approximate-zero noncompactness of Appendix III Proposition 144.1 and the weak-star construction of Appendix IV Theorem 209.5 concern different, varying residuals; neither supplies the equalities defining (214.15). Here those equalities and H51 persist at every refinement by Theorem 214.1. The universal zero-residual and physical succession questions retain exactly their original scope. $\square$

## 追加锚（本行以下为增补区）

## 215. Source-start relaxation excludes a fixed chronological hard continuation

**Definition 215.1 (the fixed hard partition and its future centered pair law).** Retain exactly Definition 211.1, including every original $\theta=(a,\eta,d,b)$, the source-start diffusion $Z$ at $e$ in the original clock, the full conservative source-inclusive operator $K$, the probability measure $m$, and $P=T_d$. Let $D=(D_0,D_1,D_3,D_B)$ be any one deterministic pointwise Borel partition of the whole original $G$, fixed for all future reads, and put

$$
 p=\tfrac14,\qquad v_D=\mathbf1_{D_B}-p,\qquad s_n=(n+2)d\quad(n\ge0).
$$

At the two epochs $s_n$ and $s_n+d$, use the same partition $D$ and independent fresh read noises conditional on the path. Define the centered $B$-pair statistic

$$
 J_D(n)=\mathbb E_e\!\left[v_D(Z_{s_n})v_D(Z_{s_n+d})\right]
       =\int_G g_{s_n}\,v_D\,P v_D\,dm,\qquad
 E_D=\|T_{d/2}v_D\|_{L^2(m)}^2.
 \tag{215.1}
$$

The second factor in (215.1) is the terminal propagated from this same $D$ by the original $P$; no terminal, source law, or clock is restarted or held fixed from another partition.

**Theorem 215.2 (source-start heat relaxation and fixed-partition chronological obstruction).** Under Definition 215.1, for every original $\theta$ and every fixed whole-$G$ partition $D$,

$$
 \begin{gathered}
 E_D>0,\qquad \|g_{s_n}-1\|_{L^1(m)}\longrightarrow0,\\[2mm]
 \left|J_D(n)-E_D\right|\le(1-p)^2\|g_{s_n}-1\|_{L^1(m)}
       \longrightarrow0,\\[2mm]
 J_D(n)\longrightarrow E_D,\qquad
 J_D(n)\ge\tfrac12E_D\quad\text{for all sufficiently large }n.
 \end{gathered}
 \tag{215.2}
$$

For the prescribed original soft readout $f$ of Definition 211.1, the centered $B$ read is $f_B-p=0$ pointwise. Hence its corresponding fresh-noise centered $B$-pair statistic is identically zero at every pair of epochs $(s_n,s_n+d)$. Consequently no fixed deterministic partition $D$ can agree with this stronger complete chronological target at all future epochs. This conclusion applies in particular to any fixed $D$ that also satisfies the original current three-epoch $F_{64}$ equations, if such a $D$ is supplied; it does not assert or deny universal $F_{64}$ attainment.

*Proof.* The full form in Appendix II Theorem 115.3 is conservative and has energy

$$
 \mathscr E[u]=\int_{G\setminus\{e\}}
 \left(a\sum_{r=1}^3|X_ru|^2+\eta|\partial_\zeta u|^2\right)dm
 \tag{215.3}
$$

on $\mathscr V=\mathscr V_0\dotplus\mathbb C1$. If $u\in\ker K$, then $u\in\mathscr V$ and $\mathscr E[u]=0$. The weak derivatives in (215.3) therefore vanish on the connected punctured group $G\setminus\{e\}$, so the $\mathscr V_0$ component is constant almost everywhere there. Appendix II Theorem 116.2 identifies $\mathscr V_0$ with the zero source-trace subspace; that constant must consequently be zero. Thus

$$
 \ker K=\mathbb C1.
 \tag{215.4}
$$

This is a statement about the full source-inclusive form, not the killed or punctured operator.

By Appendix II Theorem 117.2 and its propagation identity, $g_{s_n}=T_{nd}g_{2d}$. Since $\int g_{2d}\,dm=1$, the vector $h=g_{2d}-1$ is orthogonal to $\ker K$. Let $E_K$ be the spectral resolution of $K$. Equation (215.4) gives $E_K(\{0\})h=0$, and therefore

$$
 \|g_{s_n}-1\|_2^2
 =\|T_{nd}h\|_2^2
 =\int_{(0,\infty)}e^{-2nd\lambda}\,d\langle h,E_K(\lambda)h\rangle_m
 \longrightarrow0.
 \tag{215.5}
$$

Dominated convergence is enough here; no positive spectral gap is used. Because $m(G)=1$, $\|g_{s_n}-1\|_1\le\|g_{s_n}-1\|_2$, proving the first limit in (215.2). The source density in this argument is the actual density from the original source at time zero, as supplied by Appendix II Theorem 117.2.

The Markov property and conditional independence of the two fresh reads give the middle expression in (215.1), with the actual propagated terminal $P\mathbf1_{D_B}$ in the second slot. Self-adjointness of $P=T_d$ gives

$$
 E_D=\langle v_D,Pv_D\rangle_m.
 \tag{215.6}
$$

Since $v_D$ takes only the values $-p$ and $1-p$, $\|v_D\|_\infty\le1-p$. Positivity and the Markov contraction from Appendix II Theorem 115.3 imply $|Pv_D|\le P|v_D|\le1-p$. Hence

$$
 \begin{aligned}
 |J_D(n)-E_D|
 &=\left|\int_G(g_{s_n}-1)v_DPv_D\,dm\right|\\
 &\le (1-p)^2\|g_{s_n}-1\|_1,
 \end{aligned}
 \tag{215.7}
$$

which proves the convergence assertion.

The class $v_D$ is nonzero: an indicator cannot equal the strict intermediate constant $p$ almost everywhere on a probability space. Spectral calculus for the nonnegative self-adjoint $K$ therefore gives

$$
 E_D=\int_{[0,\infty)}e^{-d\lambda}\,d\langle v_D,E_K(\lambda)v_D\rangle_m>0,
 \tag{215.8}
$$

because the multiplier is strictly positive at every finite spectral value. This is the same injectivity mechanism recorded for $T_s$ in Appendix II Proposition 124.1. The eventual lower bound in (215.2) follows from convergence to the positive number $E_D$.

Finally, for the original soft readout, $f_B=p$ in Definition 211.1, so the centered emission variable $f_B(Z_s)-p$ is zero on every path at every positive epoch. Independent fresh read noise does not change this identity, and its pair statistic is exactly zero. Equation (215.2) makes the fixed hard statistic strictly positive from some future index onward, which proves the chronological exclusion. The argument uses only the fixed partition's own propagated terminal at each hard read and leaves the three-epoch $F_{64}$ question, origin enclosure, compatible summable continuations and physical succession open. The source-specific composition is the relaxation (215.5), the exact heat-norm identity (215.6) and the comparison with the unchanged readout; the spectral-calculus and Markov-semigroup facts cited above are intermediate suppliers rather than standalone claims. $\square$



## 追加锚（本行以下为增补区）
