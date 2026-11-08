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

## 216. An original later marginal varies inside one exact positive hard fiber

**Definition 216.1 (the original later one-time coordinate).** Retain exactly Definition 211.1 and the functions $X$, number $t_0$ and tensor $R$ of Theorem 212.1. For an integer $j\ge3$ and a pointwise whole-$G$ Borel simplex tuple $u$, put

$$
 M_j(u)=\int_G g_j u_0\,dm,
 \qquad g_j=P^jg=g_{(2+j)d}.
 \tag{216.1}
$$

For a deterministic whole-$G$ Borel partition $D$, write $M_j(D)=M_j(\mathbf1_D)$. By Appendix II Theorem 117.2, this is the probability of label $0$ at the original epoch $(2+j)d$ for the diffusion started at the original source $e$ at time zero. The partition is held fixed at every read; neither the source nor the clock is restarted.

**Theorem 216.2 (actual hard future separation at fixed current law).** For every original $\theta=(a,\eta,d,b)$ and every fixed $0<t<t_0(\theta)$, there exist an integer $j\ge3$, a number $\delta>0$, and deterministic pointwise whole-$G$ Borel partitions $D^\lambda$, one for every $|\lambda|<\delta$, such that, with $u^*=u^{(t)}$,

$$
 \begin{gathered}
 D^\lambda\in\mathscr F_t,\qquad
 M_j(D^\lambda)=M_j(u^*)+\lambda
       \quad(|\lambda|<\delta),\\
 \mathcal H_{51}(\mathbf1_{D^\lambda})=\mathcal H_{51}(f),\qquad
 \Delta(D^\lambda)_{yzw}=t^2R_{yzw}
       \quad((y,z,w)\in\mathcal L^3).
 \end{gathered}
 \tag{216.2}
$$

Here $\mathscr F_t$ is exactly (214.15), and every triple uses its displayed hard partition in all three slots, including its own propagated terminal. In particular, the two actual hard partitions

$$
 D=D^{\delta/2},\qquad E=D^{-\delta/2}
 \quad\hbox{satisfy}\quad
 M_j(D)-M_j(E)=\delta>0.
 \tag{216.3}
$$

They have identical H51 and identical complete current three-read law, with BB3 residual exactly $t^2\kappa>0$. Thus even the complete current law together with H51 does not determine all later original one-time marginals on this fixed positive-residual hard fiber. The epoch and the interval may depend on $\theta,t$; the assertion requires neither a prescribed epoch nor a common pair for all future epochs.

*Proof.* Fix arbitrary original $\theta$ and $0<t<t_0$. Retain the original invariant slack set $E_{\rm sl}=E$ of (153.6), writing $E_{\rm sl}$ to distinguish it from the second partition in (216.3). It contains the open rotation lift of the nonempty quotient neighborhood $U\Subset\mathcal Q$. By 212.C, all components of $u^*$ have a common lower bound $\sigma_t>0$ on $E_{\rm sl}$. Retain the sixty-three bounded supported sum-zero directions $e_1,\ldots,e_{63}$ of 212.C and the current map

$$
 \mathcal J(u)=\left(\mathcal H_{36}(u),
       (\mathcal C(u_a,u_b,u_c))_{abc\in I^3}\right)\in\mathbb R^{63}.
 \tag{216.4}
$$

The actual matrix $A_{\ell k}=D\mathcal J_\ell(u^*)[e_k]$ is invertible by (212.11)--(212.18). This is the rank proved for the original current map, not a new rank hypothesis.

### 216.A. A bounded supported future direction outside the current rows

Every $g_j$ is bounded by $\|g\|_\infty$, by the Markov contraction. It has a real analytic representative on the connected full-measure set $\Omega=\{r>0\}$, by the source propagation identity and Appendix II (122.8)--(122.11). The restricted family

$$
 (\mathbf1_{E_{\rm sl}}g_j)_{j\ge3}
 \quad\hbox{is linearly independent in }L^2(E_{\rm sl},m).
 \tag{216.5}
$$

Indeed, a finite relation zero almost everywhere on $E_{\rm sl}$ is an analytic function zero almost everywhere on its open subset over $U$. Full support and continuity make it zero throughout that open subset. Analytic uniqueness on connected $\Omega$ makes it zero on $\Omega$, hence in $L^2(G,m)$. The resulting nonzero polynomial relation $q(P)g=0$ contradicts Appendix IV Lemma 169.1 with source time $2d$. This uses orbit independence only, with no claim of source cyclicity or density.

Let $\mathscr V=L^2(E_{\rm sl},m;\mathbb R^I)$ with its real inner product. For a bounded supported triple $h_I=(h_i)_{i\in I}$, always use the compensating component $h_B=-\sum_{i\in I}h_i$. At $u^*$ each current differential has a bounded real Borel density $\rho_\ell\in\mathscr V$:

$$
 D\mathcal J_\ell(u^*)[h]
       =\sum_{i\in I}\int_{E_{\rm sl}}\rho_{\ell,i}h_i\,dm,
 \qquad 1\le\ell\le63.
 \tag{216.6}
$$

To see boundedness directly, the marginal rows have densities $g_0,g_1,g_2$. The ordered pair rows have the densities obtained from $g_a vP^k w$ by moving $P^k$ to the other factor, with $(a,k)=(0,1),(0,2),(1,1)$. For the triple row $abc\in I^3$, the density in component $i$ is the restriction to $E_{\rm sl}$ of

$$
 \mathbf1_{i=a}\,gP(u_b^*Pu_c^*)
 +\mathbf1_{i=b}\,P(gu_a^*)Pu_c^*
 +\mathbf1_{i=c}\,P(u_b^*P(gu_a^*)).
 \tag{216.7}
$$

Self-adjointness gives the terminal term in (216.7). The Markov bound and $0\le u_y^*\le1$ bound each summand by $\|g\|_\infty$. These expressions also show that (216.6) concerns the full actual operator and the common current tuple in every slot.

Put $V=\operatorname{span}_{\mathbb R}\{\rho_1,\ldots,\rho_{63}\}\subset\mathscr V$. For each $j\ge3$ let $k_j=(g_j,0,0)|_{E_{\rm sl}}$, in the component order $0,1,3$. By (216.5) these vectors are linearly independent. Since $V$ is finite dimensional, choose one integer $j\ge3$ with $k_j\notin V$. Let $\Pi_V$ be the orthogonal projection in $\mathscr V$, and set

$$
 w=k_j-\Pi_Vk_j,\qquad
 h_i=\mathbf1_{E_{\rm sl}}w_i\ (i\in I),\qquad
 h_B=-\sum_{i\in I}h_i,\qquad
 \gamma=\|w\|_{\mathscr V}^2>0.
 \tag{216.8}
$$

The vector $w$ is bounded: $k_j$ is bounded and $\Pi_Vk_j$ is a finite linear combination of the bounded $\rho_\ell$. It has real Borel representatives. Orthogonality gives the exact identities

$$
 D\mathcal J(u^*)[h]=0,\qquad
 DM_j(u^*)[h]=\langle k_j,w\rangle_{\mathscr V}
              =\gamma>0.
 \tag{216.9}
$$

Thus this is an actual legal bounded direction with a nonzero future differential, rather than a transversality assumption about arbitrary hard partitions.

### 216.B. A legal sixty-four-dimensional simplex family

Define $\widetilde e_k=e_k$ for $k\le63$ and $\widetilde e_{64}=h$, and put

$$
 \begin{gathered}
 u(z)=u^*+\sum_{k=1}^{64}z_k\widetilde e_k,
 \qquad \mathcal J^+(u)=(\mathcal J(u),M_j(u)),\\
 F(z)=\mathcal J^+(u(z))-\mathcal J^+(u^*),\qquad
 \widetilde A=DF(0)
       =\begin{pmatrix}A&0\\ *&\gamma\end{pmatrix}.
 \end{gathered}
 \tag{216.10}
$$

The matrix $\widetilde A$ is invertible. Choose bounded Borel representatives and a common Borel null set covering the exceptional bounds and sum-zero identities of these finitely many directions. Set the directions equal to zero there, and use the original pointwise simplex representative of $u^*$ there. Outside $E_{\rm sl}$ every direction is zero. On $E_{\rm sl}$, a sufficiently small radius $r>0$ gives
$\sup_y|\sum_kz_k\widetilde e_{k,y}|<\sigma_t/2$ for $\|z\|_2\le r$ outside the repaired set. Thus $u(z)$ is a pointwise simplex tuple on the whole original $G$ throughout this closed parameter ball. The repairs change no integral. They restrict neither the state space nor the form domain of $K$.

The map $F$ is polynomial, $F(0)=0$, and its derivative at zero is $\widetilde A$. Shrink the legal radius so that

$$
 \sup_{\|z\|_2\le r}
       \|z-\widetilde A^{-1}F(z)\|_2<r/3.
 \tag{216.11}
$$

### 216.C. Simultaneous exact hard realization of the current and future coordinates

Take increasing finite Borel partitions $\mathcal P_n$ generating the original Borel sigma algebra, and use exactly the common coordinate-quantile construction of 212.D on the entire ball in (216.10). Within each positive-mass cell, nested consecutive coordinate slices have masses $\int_Cu_y(z)\,dm$ in the order $0,1,3,B$. Coordinate hyperplanes are $m$-null because the original $m=h^2\mu$ is absolutely continuous in these coordinates. Thus the slices exist for every parameter, including zero prescribed masses. Assign endpoints consistently and assign zero-mass cells to $B$. This defines deterministic pointwise whole-$G$ Borel partitions $D_n(z)$ with

$$
 \begin{gathered}
 \int_C\mathbf1_{D_{n,y}(z)}\,dm=\int_Cu_y(z)\,dm
       \quad(C\in\mathcal P_n),\\
 \sum_y m(D_{n,y}(z)\mathbin\triangle D_{n,y}(z'))
       \le6\sum_y\|u_y(z)-u_y(z')\|_1.
 \end{gathered}
 \tag{216.12}
$$

Retain the original path density $W$ of (212.21), and set

$$
 W_n=\mathbb E[W\mid\mathcal P_n^{\otimes3}],\qquad
 g_{j,n}=\mathbb E[g_j\mid\mathcal P_n],\qquad
 F_n(z)=\mathcal J^+(\mathbf1_{D_n(z)})-\mathcal J^+(u^*).
 \tag{216.13}
$$

Both conditional expectations converge in $L^1$ to their respective densities. The cell identities (216.12) make the soft and hard integrals against $W_n$ equal for every current row, and make their label-$0$ integrals against $g_{j,n}$ equal. Consequently

$$
 \sup_{\|z\|_2\le r}\|F_n(z)-F(z)\|_2
 \le2\sqrt{63}\,\|W-W_n\|_1
              +2\|g_j-g_{j,n}\|_1
 \longrightarrow0.
 \tag{216.14}
$$

This is simultaneous approximation of the original current path law and the original later source density, uniformly on the whole legal ball. Each $F_n$ is continuous: (216.12) gives continuity of indicators in $L^1$, telescoping current slot products bounds their changes by the bounded marginals $g_0,g_1,g_2$, and the future integral is bounded by $\|g_j\|_\infty$ times the change in its indicator. No differentiability of a hard partition or of its boundaries is used.

Choose one finite $n$ so that the right side of (216.14), multiplied by $\|\widetilde A^{-1}\|$, is less than $r/3$. Then choose $\delta>0$ so that

$$
 \|\widetilde A^{-1}(0_{63},\lambda)\|_2<r/3
       \quad(|\lambda|<\delta).
 \tag{216.15}
$$

For every such $\lambda$, the continuous map

$$
 z\longmapsto z-\widetilde A^{-1}
                      (F_n(z)-(0_{63},\lambda))
 \tag{216.16}
$$

maps the closed radius-$r$ ball into itself, by (216.11), (216.14) and (216.15). Brouwer's closed-ball fixed-point theorem supplies a root $z_\lambda$ with $F_n(z_\lambda)=(0_{63},\lambda)$. Put $D^\lambda=D_n(z_\lambda)$. These are actual deterministic hard partitions, and they satisfy exactly

$$
 \mathcal J(\mathbf1_{D^\lambda})=\mathcal J(u^*),\qquad
 M_j(D^\lambda)=M_j(u^*)+\lambda.
 \tag{216.17}
$$

The finite $n$ is chosen before the target $\lambda$; no continuity or compatibility of the roots is needed.

### 216.D. Recovery of the complete fixed current law and its chronological consumer

The first thirty-six equations in (216.17) give $\mathcal H_{36}(\mathbf1_{D^\lambda})=\mathcal H_{36}(f)$. Thus both $\Delta(D^\lambda)$ and $\Delta(u^*)=t^2R$ have zero contractions and belong to $H^{\otimes3}$. Their coordinates on $I^3$ agree by the other twenty-seven current equations. Restriction to $I^3$ is injective on $H^{\otimes3}$, as in (212.25), so all sixty-four coordinates agree. Since $R\in\mathcal W_{13}\cap\ker L$, (157.8) and Proposition 211.2 give exact H51. Therefore every $D^\lambda$ lies in exactly $\mathscr F_t$, proving (216.2). Taking the two target values in (216.3) proves their strictly positive marginal difference. By (216.1) it occurs at an actual original integer epoch, in the same source-start process.

The consumer is chronological sufficiency of the exact current-law fiber: equality of every current three-read coefficient, even with H51 fixed, cannot determine this later label probability. The source-orbit escape in 216.A and its simultaneous hard realization in 216.C supply an actual pair; the partition-distance separation in Corollary 214.3 alone and the fixed-hard-versus-soft pair obstruction in Theorem 215.2 do not supply that pair.

This is a repo-derived composition of the original source orbit, the actual current rank in 212.C, and the common hard carrier. The analytic uniqueness intermediary is the identity principle for real analytic functions, also used in Appendix III 153.D; the supplied local analyticity is Appendix II (122.8)--(122.11), with its cited Kotake--Narasimhan regularity theorem. The fixed-point intermediary is L. E. J. Brouwer, *Über Abbildung von Mannigfaltigkeiten*, [doi:10.1007/BF01456931](https://doi.org/10.1007/BF01456931), in the same closed-ball form as 212.D. Finite cell-mass matching is only the linear step; the exact common-partition nonlinear equations follow from (216.10)--(216.17), rather than from a general linear purification theorem. These classical intermediaries are not standalone new theory.

All original source and analytic suppliers retain their inherited scope. This positive-residual result imposes no extra hypothesis on $\theta$ or the admitted representative $b$: replacing $f^0$ by $f$ in target integrals changes no original positive-time law, and every repaired null set is null for all those laws. It leaves universal residual-zero $F_{64}$ attainment or exclusion, origin enclosure, actual compatible summable continuation, physical succession and general instrument or full-history contracts unresolved. $\square$

## 追加锚（本行以下为增补区）

## 217. Every baseline relation pays source heat energy through the actual full law

**Definition 217.1 (relation space, actual residual and relation matrix).** Retain exactly Definition 211.1 and all its original endpoint, source and analytic suppliers. In particular, $\theta=(a,\eta,d,b)$ ranges over every original permitted value, $m=h^2\mu$, $g=g_{2d}$, $P=T_d$, $Pf_3=cg$ and $p=1/4$. All tuples below are pointwise Borel simplex tuples on the whole original $G$, and every coefficient uses that tuple in all three slots, with its own propagated terminal. Equalities of functions and norm analyticity refer to $m$-classes; bounded Borel representatives and null repairs retain the pointwise interface because every original positive-time slot law is absolutely continuous with respect to $m$. Put

$$
\begin{gathered}
 K_{\rm rel}=\left\{a\in\mathbb R^{\mathcal L}:\sum_y a_yf_y=0\right\},\qquad
 h_a(u)=\sum_y a_yu_y,\\
 \delta(u)=\|\Delta(u)\|_\infty,\qquad
 \varepsilon_3(u)=\|u_3-f_3\|_\infty,\\
 a^{(1)}=(1,-1,0,0),\qquad
 a^{(B)}=(-p,-p,-p,1-p)
 \quad\text{in the order }(0,1,3,B).
\end{gathered}
\tag{217.1}
$$

These two vectors form a basis of $K_{\rm rel}$. Indeed $f$ has the affine form (157.1), and $[b]$ is nonconstant by the source-start argument in Proposition 135.2. Thus $a\cdot f=0$ imposes two independent scalar conditions on four coefficients; the displayed independent vectors satisfy them. For this basis write

$$
\begin{gathered}
 h_1=u_0-u_1,\qquad h_B=u_B-p,\\
 Q_{rs}(u)=\mathcal C(h_r,h_s,f_3),\qquad
 R_{rs}(u)=\sum_{y,z}a_y^{(r)}a_z^{(s)}\Delta(u)_{yz3},
 \quad r,s\in\{1,B\}.
\end{gathered}
\tag{217.2}
$$

**Theorem 217.2 (all relations, cross terms and terminal-defect bound).** For any finite list $a^{(r)}\in K_{\rm rel}$ and any legal $u$, define $h_r,Q_{rs},R_{rs}$ by the same formulas. Then

$$
\begin{aligned}
 R_{rs}(u)&=\mathcal C(h_r,h_s,u_3),\\
 Q_{rs}(u)-R_{rs}(u)&=-\mathcal C(h_r,h_s,u_3-f_3),\\
 Q_{rs}(u)&=c\left\langle T_{d/2}(gh_r),T_{d/2}(gh_s)\right\rangle_m.
\end{aligned}
\tag{217.3}
$$

In particular $Q$ is a symmetric positive-semidefinite Gram matrix. With $A_r=\|a^{(r)}\|_1$,

$$
\begin{gathered}
 |R_{rs}(u)|\le A_rA_s\delta(u),\qquad
 |Q_{rs}(u)-R_{rs}(u)|
 \le\|h_r\|_\infty\|h_s\|_\infty\varepsilon_3(u),\\
 0\le c\|T_{d/2}(gh_a(u))\|_2^2
 \le\|a\|_1^2\delta(u)+\|h_a(u)\|_\infty^2\varepsilon_3(u)
 \quad(a\in K_{\rm rel}).
\end{gathered}
\tag{217.4}
$$

For the displayed basis the residual constants are $A_1^2=4$, $A_B^2=9/4$ and $A_1A_B=3$. For every $v=(\alpha,\beta)$ the same bound applies to $a=\alpha a^{(1)}+\beta a^{(B)}$, so it controls the joint cross terms and every relation direction, rather than only two separate diagonal tests. At an exact full-law zero it leaves precisely the terminal-defect cost; it imposes no terminal-preservation, parity or first-order-kernel hypothesis.

*Proof.* Contracting the actual residual in the first two slots gives

$$
 R_{rs}(u)=\mathcal C(h_r,h_s,u_3)
  -\mathcal C(a^{(r)}\cdot f,a^{(s)}\cdot f,f_3)
 =\mathcal C(h_r,h_s,u_3).
$$

Subtract the same expression with terminal $f_3$. The original propagation $Pf_3=cg$ and self-adjointness give

$$
 \mathcal C(h_r,h_s,f_3)
 =c\langle gh_r,P(gh_s)\rangle_m
 =c\langle T_{d/2}(gh_r),T_{d/2}(gh_s)\rangle_m.
$$

All terms are finite since $g\in L^2(m)$ and the $h_r$ are bounded. This consumes the original positive source form (134.15)--(134.19), not a substituted initial law. The Markov contraction and $\int g\,dm=1$ give $|\mathcal C(v,w,z)|\le\|v\|_\infty\|w\|_\infty\|z\|_\infty$; the finite coefficient sum gives the other estimate in (217.4). These prove every assertion, including arbitrary linear combinations. The strictness used below is the existing fact that $T_{d/2}$ is injective and $g>0$ almost everywhere: $Q_{aa}=0$ implies $h_a=0$. $\square$

## 218. Unrestricted finite-parameter analytic zeros and ordinary rank deficiency

**Definition 218.1 (a norm-analytic chart through the original readout).** Let $U\subset\mathbb R^n$ be an open neighborhood of $0$. A chart here is any real norm-analytic map

$$
 \Phi:U\longrightarrow L^\infty(G,m;\mathbb R)^{\mathcal L},
 \qquad \Phi(0)=f,
\tag{218.1}
$$

whose values admit legal whole-$G$ Borel simplex representatives. Its range need not lie in a fixed finite-dimensional function space, and $\Phi_3$ is unrestricted. Use the actual sixty-three-coordinate current map $\mathcal J$ of (212.17) and put

$$
 \mathscr R=\{u:h_1(u)=h_B(u)=0\},\qquad
 E(u)=Q_{11}(u)+Q_{BB}(u).
\tag{218.2}
$$

A regular zero means ordinary surjectivity onto $\mathbb R^{63}$ of the derivative of the current map, with no transversality qualifier.

**Theorem 218.2 (analytic full-zero obstruction without a terminal ansatz).** For every original $\theta$ and every chart (218.1), there is a neighborhood $U_0$ of $0$ such that

$$
 z\in U_0,\quad\Delta(\Phi(z))=0
 \quad\Longrightarrow\quad h_1(\Phi(z))=h_B(\Phi(z))=0.
\tag{218.3}
$$

At every such zero the ambient derivative $D\mathcal J(\Phi(z))$, on bounded sum-zero direction tuples, has rank at most $62$. Thus the chart derivative also has rank at most $62$: these are not ordinary $63$-coordinate regular zeros.

More generally, a norm-analytic curve of legal exact full-law zeros on a connected real interval, taking the value $f$ at an interior point, remains in $\mathscr R$ throughout that interval. It cannot reach a hard tuple, including at any endpoint to which it extends continuously in $L^\infty$. Smooth flat departures, nonanalytic paths, arbitrary infinite-parameter zero sets, finite-amplitude zeros outside this neighborhood and direct hard constructions are not excluded by this assertion.

*Proof.* First consider a norm-analytic curve $u(s)$ through $f$, with $\Delta(u(s))=0$ for $s>0$ sufficiently small. If $h_r(u(s))$ is not identically zero as an analytic germ, let $k\ge1$ be its first nonzero Taylor order. Then, for one nonzero bounded $m$-class $H$,

$$
 h_r(u(s))=s^kH+O_{L^\infty}(s^{k+1}),\qquad
 Q_{rr}(u(s))
 =s^{2k}c\|T_{d/2}(gH)\|_2^2+O(s^{2k+1}).
\tag{218.4}
$$

The leading energy is strictly positive by the last sentence of Theorem 217.2. But $\varepsilon_3(u(s))=O(s)$, without any restriction on its first-order coefficient. Equation (217.4) at the exact zero gives

$$
 0\le Q_{rr}(u(s))
 \le\|h_r(u(s))\|_\infty^2\varepsilon_3(u(s))
 =O(s^{2k+1}),
\tag{218.5}
$$

contradicting (218.4). Hence both relation functions vanish as analytic germs. The identity principle, applied to every continuous linear functional on $L^\infty$, extends their vanishing along a connected analytic interval. Norm continuity preserves these equalities at an included limit endpoint. A hard $B$ indicator cannot equal $p=1/4$ almost everywhere on the probability space, proving the hard-tuple assertion.

For finite parameter dimension, all sixty-four functions $\Delta(\Phi(z))_{yzw}$ and the scalar $E(\Phi(z))$ are real analytic: $\mathcal C$ is bounded trilinear, and $E$ is a continuous quadratic form in the analytic relation functions. Moreover $E(u)>0$ exactly when $u\notin\mathscr R$. If (218.3) failed arbitrarily near $0$, the semianalytic, hence subanalytic, set

$$
 X=\{x\in U:\Delta(\Phi(x))_{yzw}=0\text{ for all }y,z,w,
                         \ E(\Phi(x))>0\}
\tag{218.6}
$$

would have $0$ in its closure.
Use Bierstone--Milman, [*Semianalytic and subanalytic sets*, IHES 67, pp.5--42](https://www.numdam.org/item/PMIHES_1988__67__5_0.pdf), Theorem 0.2, with the pure $n$-dimensional analytic manifold $U$ and compact set $\{0\}$. It supplies finitely many analytic $\varphi_i:\mathbb R^n\to U$ and compact $L_i$ whose images cover a neighborhood of $0$, with each $\varphi_i^{-1}(X)$ a union of quadrants. This supplies the required arbitrary-dimensional curve passage as follows. Lift a sequence in $X$ tending to $0$ into the $L_i$. Finiteness and compactness give one $i$, one quadrant $Q\subset\varphi_i^{-1}(X)$, and a convergent subsequence of lifts with limit $y_0\in\overline Q$ and $\varphi_i(y_0)=0$. Choose $y_1\in Q$. By their Definition 5.4 each coordinate of $Q$ is either zero, strictly positive or strictly negative; consequently

$$
 y(s)=y_0+s(y_1-y_0)\in Q\quad(0<s<1).
\tag{218.7}
$$

The analytic curve $s\mapsto\Phi(\varphi_i(y(s)))$ passes through $f$, is an exact zero for small positive $s$, and has $E>0$ there. This contradicts (218.4)--(218.5). It proves (218.3). This use of rectilinearization includes the compact lifting and quadrant-segment argument; it does not promote the one-dimensional Lemma 6.3 to higher dimensions.

Finally, at any $u\in\mathscr R$ the actual scalar contraction

$$
 R_{11}(u)=\Delta(u)_{003}-\Delta(u)_{013}
                    -\Delta(u)_{103}+\Delta(u)_{113}
          =\mathcal C(h_1(u),h_1(u),u_3)
\tag{218.8}
$$

has zero derivative in every bounded direction, since each differentiated term retains a zero $h_1$ factor. The expression on the left is a nonzero linear functional of the last twenty-seven coordinates of $\mathcal J(u)-\mathcal J(f)$, indexed by $I^3$. It annihilates the entire derivative range, giving rank at most $62$ without a transverse-branch assumption. This also excludes a regular zero in a smooth parameterization at any of these points, though it makes no assertion about zeros reached by an unrelated smooth flat departure. $\square$

The source-specific conclusion uses the terminal-defect inequality for every analytic relation order, then finite-dimensional real analytic geometry. The latter is a consumed classical tool; its semianalytic description, pure-dimensional manifold, compact set and inverse-image quadrant hypotheses are all as above. No global spectral gap, source-orbit density or common fixed reservoir is assumed.

## 219. The actual joint quadratic cone and soft origin-enclosure restriction in H51

**Definition 219.1 (actual matrices and bounded proximity).** Use the ordered relation basis of (217.1), with $R(u),Q(u)$ as in (217.2). For $C>0$ and $t>0$, bounded proximity means

$$
 \max_y\|u_y-f_y\|_\infty\le Ct.
\tag{219.1}
$$

It implies $\|h_1\|_\infty\le2Ct$, $\|h_B\|_\infty\le Ct$ and $\varepsilon_3(u)\le Ct$. Write $b_1=2$, $b_B=1$ for these constants, and define the injective real linear map

$$
 A_\theta v=\sqrt c\,T_{d/2}(gv):L^\infty(m;\mathbb R)\longrightarrow L^2(m;\mathbb R).
\tag{219.2}
$$

**Theorem 219.2 (exactly the full positive-semidefinite two-contrast cone).** For every original $\theta$, the matrices that occur as finite limits

$$
 t_n^{-2}R(u_n)\longrightarrow Z,\qquad t_n\downarrow0,
 \qquad \sup_n t_n^{-1}\max_y\|u_{n,y}-f_y\|_\infty<\infty
\tag{219.3}
$$

for actual legal whole-$G$ soft tuples are precisely

$$
 \operatorname{Sym}_2^+
 =\left\{\begin{pmatrix}x&z\\z&y\end{pmatrix}:
                   x\ge0,\ y\ge0,\ z^2\le xy\right\}.
\tag{219.4}
$$

The same limit set is obtained with $Q(u_n)$ in (219.3). No convergence or compactness of the scaled function tangents is assumed for necessity. Every matrix in (219.4), including ranks zero and one, is attained by a bounded affine soft path whose variations are supported on original legal slack, with $u_3=f_3$ and $\Delta(u_t)=O(t^2)$ in all sixty-four coordinates. These last choices are properties of the sufficiency construction, not restrictions on (219.3).

Quantitatively, every tuple satisfying (219.1) obeys

$$
 |R_{rs}(u)-Q_{rs}(u)|\le b_rb_sC^3t^3.
\tag{219.5}
$$

If also $\delta(u_t)=o(t^2)$, then $t^{-2}Q(u_t)\to0$. This asserts collapse of the weighted heat energies, not compactness or $L^2$ convergence of the scaled contrasts. If a scaled contrast does converge in $L^2$, its limit is zero, by boundedness of $g$, continuity of the heat map and injectivity.

*Proof.* Equation (219.5) is (217.4). At every amplitude $Q(u)$ is a positive-semidefinite Gram matrix, and (219.5) makes $t_n^{-2}(R-Q)\to0$ under a single finite proximity constant. The positive-semidefinite cone is closed in this finite-dimensional matrix space, so every limit is in (219.4), whether or not the functions have convergent subsequences.

For sufficiency choose an original Borel slack set $E$ of positive $m$-measure as in (153.6); only positivity of its measure is needed here. Define the sum-zero label lifts

$$
 n_1=(1/2,-1/2,0,0),\qquad
 n_B=(-1/2,-1/2,0,1).
\tag{219.6}
$$

They satisfy $a^{(r)}\cdot n_s=\mathbf1_{r=s}$ and $(n_s)_3=0$. On the infinite-dimensional space of bounded real Borel classes supported in $E$, impose the at most $128$ linear equations

$$
 D\Delta(f)[n_1v]=0,\qquad D\Delta(f)[n_Bv]=0.
\tag{219.7}
$$

These are bounded linear functionals by the trilinear estimate of Theorem 217.2. Nonatomicity, disjoint positive-measure subsets of $E$, and rank-nullity give two independent classes in their common kernel, by the finite-codimension argument of (134.21). Since $A_\theta$ is injective, Gram--Schmidt for the inner product $\langle A_\theta v,A_\theta w\rangle_m$ gives bounded supported Borel functions $v_1,v_2$ in the same kernel with

$$
 \langle A_\theta v_i,A_\theta v_j\rangle_m=\mathbf1_{i=j}.
\tag{219.8}
$$

For any $Z\in\operatorname{Sym}_2^+$ choose a real $2$-by-$2$ matrix $B$ with $BB^{\mathsf T}=Z$, including singular $B$ when necessary. Set $\xi_r=\sum_jB_{rj}v_j$ and

$$
 \begin{aligned}
 u_{t,0}&=f_0+t(\xi_1-\xi_B)/2,&
 u_{t,1}&=f_1-t(\xi_1+\xi_B)/2,\\
 u_{t,3}&=f_3,& u_{t,B}&=p+t\xi_B.
 \end{aligned}
\tag{219.9}
$$

The components sum to one. The unchanged $f_3$ is positive everywhere, and $f_0,f_1,p\ge1/4$ globally. Bounded supported representatives therefore make (219.9) a pointwise simplex tuple for all sufficiently small $|t|$, equal to $f$ outside $E$. Its contrasts are exactly $t\xi_1,t\xi_B$, so (219.8) and its own terminal $u_{t,3}=f_3$ give

$$
 R(u_t)=Q(u_t)=t^2Z.
\tag{219.10}
$$

The direction in (219.9) is a sum of $n_1\xi_1,n_B\xi_B$, so (219.7) kills every first-order full-law coefficient. Trilinearity then gives the asserted full $O(t^2)$ residual with a finite quadratic limit. This does not claim exact H51 calibration of the constructed paths or realization of every tensor in that slice. Necessity on that exact slice, and the ball consumer, are supplied next.

For the subquadratic-residual statement, (217.4) gives

$$
 0\le t^{-2}Q_{rr}(u_t)
 \le A_r^2\delta(u_t)/t^2+b_r^2C^3t.
\tag{219.11}
$$

Both diagonals tend to zero, and the Gram Cauchy--Schwarz inequality controls the cross term. The final strong-tangent conclusion follows from (219.2), $g\in L^\infty$, and injectivity; no subsequence with this stronger property is presumed. The Gram factorization and finite-codimension argument are consumed linear-algebra tools; the actual source, legal tuple and first-order full-law interface are (219.7)--(219.10). $\square$

**Definition 219.3 (the exact twelve-dimensional residual space and soft image).** Use precisely the H51 space of Theorem 212.1,

$$
 \mathscr V_{51}=\mathcal W_{13}\cap\ker L
 \subset H^{\otimes3},\qquad \dim\mathscr V_{51}=12,
\tag{219.12}
$$

with the tensor maximum norm, not a quotient norm or a larger ambient residual space. Let

$$
 \mathscr S_C(t)=\{\Delta(u):u\text{ legal on }G,
       \ \mathcal H_{51}(u)=\mathcal H_{51}(f),
       \ \max_y\|u_y-f_y\|_\infty\le Ct\}.
\tag{219.13}
$$

The exact pair contractions, the eight contrast equations (157.8), the six distinct-label equations and (211.3) put this image in $\mathscr V_{51}$ exactly. For $S\in\mathscr V_{51}$ define

$$
 \mathsf M(S)_{rs}=\sum_{y,z}a_y^{(r)}a_z^{(s)}S_{yz3},\qquad
 \ell_v(S)=v^{\mathsf T}\mathsf M(S)v,\qquad
 d_v=\sup_{\|S\|_\infty\le1,\ S\in\mathscr V_{51}}|\ell_v(S)|.
\tag{219.14}
$$

On this exact space $\mathsf M(S)$ is symmetric: its off-diagonal difference is $L(S)$, using the zero pair contractions and $S_{013}=S_{103}=0$. Also $\mathsf M(S)_{BB}=S_{BB3}$. For $v\ne0$, $d_v$ is a finite positive constant determined by this explicit finite-dimensional interface.

**Theorem 219.4 (quantitative joint-cone restriction on origin enclosure).** For every original $\theta$, $C,t>0$ and $S\in\mathscr S_C(t)$,

$$
 \begin{gathered}
 v^{\mathsf T}\mathsf M(S)v
 \ge-C^3t^3(2|\alpha|+|\beta|)^2
 \quad(v=(\alpha,\beta)\in\mathbb R^2),\\
 \mathsf M(S)+5C^3t^3I_2\ \text{is positive semidefinite}.
 \end{gathered}
\tag{219.15}
$$

Consequently every finite $t^{-2}$ limit of such exact-slice matrices is in (219.4). If an entire relative residual ball is in this actual soft image,

$$
 B_{\mathscr V_{51},\infty}(S_*,r)
 =\{S\in\mathscr V_{51}:\|S-S_*\|_\infty<r\}
 \subseteq\mathscr S_C(t),\qquad r>0,
\tag{219.16}
$$

then the joint family of necessary inequalities is

$$
 r d_v\le\ell_v(S_*)+C^3t^3(2|\alpha|+|\beta|)^2
 \quad(v=(\alpha,\beta)\ne0).
\tag{219.17}
$$

In the $B$ direction the exact dual constant is $d_{(0,1)}=1$, giving

$$
 r\le (S_*)_{BB3}+C^3t^3\le\|S_*\|_\infty+C^3t^3.
\tag{219.18}
$$

In particular an origin-centered ball contained in this soft image has radius at most $C^3t^3$. More generally, an origin-enclosing ball, meaning $r>\|S_*\|_\infty$, has origin margin at most $C^3t^3$. For the actual center $S_*=t^2R$ of Theorem 212.1 this becomes

$$
 r\le t^2\kappa+C^3t^3,\qquad
 r-t^2\|R\|_\infty\le C^3t^3.
\tag{219.19}
$$

Thus for fixed $C$ no such uniformly $O(t)$ soft-image balls can enclose the origin with a positive margin of order $t^2$. If $\|R\|_\infty>\kappa$, an origin-enclosing ball at that center additionally requires $C^3t>\|R\|_\infty-\kappa$. These are restrictions on actual soft-image coverage, with their proximity hypothesis; they do not assert nonattainment of the point $0$, which is itself attained softly by $f$.

*Proof.* For the actual tuple representing $S$, apply (217.3) to $h_v=\alpha h_1+\beta h_B$. Its positive energy differs from $\ell_v(S)$ by at most

$$
 \|h_v\|_\infty^2\varepsilon_3(u)
 \le C^3t^3(2|\alpha|+|\beta|)^2.
\tag{219.20}
$$

This proves (219.15), including the cross terms. The matrix assertion follows from $(2|\alpha|+|\beta|)^2\le5(\alpha^2+\beta^2)$. For a ball (219.16), the infimum of $\ell_v$ over that ball is $\ell_v(S_*)-rd_v$. Apply (219.15) to every point and approach that infimum to obtain (219.17).

For completeness, the claimed dual constants are computed in the actual slice. Put $k=q/c=(-1/2,-1/2,1,0)$ and use $n_1,n_B$ of (219.6). For a symmetric matrix $Z$, form the explicit tensor

$$
 \begin{aligned}
 \mathsf D(Z)={}&\sum_{r,s\in\{1,B\}}Z_{rs}
 (n_r\otimes n_s\otimes k+n_r\otimes k\otimes n_s
                                  +k\otimes n_r\otimes n_s)\\
 &+(Z_{11}-Z_{BB})k\otimes k\otimes k.
 \end{aligned}
\tag{219.21}
$$

All factors are in $H$, and each summand has a $k$ slot, so $\mathsf D(Z)\in\mathcal W$. This tensor is fully symmetric. Its $013$ coordinate is $(-Z_{11}+Z_{BB})/4+(Z_{11}-Z_{BB})/4=0$; symmetry kills all six distinct-label coordinates and gives $L(\mathsf D(Z))=0$. Thus it is in the exact $\mathscr V_{51}$. Since $a^{(r)}\cdot k=0$, $k_3=1$ and $a^{(r)}\cdot n_s=\mathbf1_{r=s}$, contraction of (219.21) gives

$$
 \mathsf M(\mathsf D(Z))=Z.
\tag{219.22}
$$

Hence $d_v>0$ for every nonzero $v$, by choosing $Z=vv^{\mathsf T}$. In particular, for $Z=\operatorname{diag}(0,1)$ the entries of $\mathsf D(Z)$, up to permutation of slots, are as follows, with $i,j,l\in\{0,1\}$:

$$
 \begin{array}{c|rrrrrrrrrr}
 \text{labels}&BBB&BBi&BB3&Bij&Bi3&B33&ijl&ij3&i33&333\\ \hline
 \mathsf D(Z)&0&-1/2&1&1/2&-1/2&0&-1/4&0&1/2&-1
 \end{array}
\tag{219.23}
$$

Repeated indices are allowed. These values follow directly by using $n_{B,i}=k_i=-1/2$, $n_{B,B}=k_3=1$ and $n_{B,3}=k_B=0$ in (219.21). They show $\|\mathsf D(Z)\|_\infty=1$ and $\mathsf D(Z)_{BB3}=1$. The reverse bound $|S_{BB3}|\le\|S\|_\infty$ is immediate, proving $d_{(0,1)}=1$. Equations (219.18)--(219.19) now follow from (219.17) and $R_{BB3}=\kappa$. The tensor (219.21) is a dual-norm witness in the residual vector space, not an assertion that this tensor is attained by a soft or hard tuple. $\square$

The joint-cone consumer above is distinct from the existing positive-BB3 hard neighborhood in (212.2). That hard neighborhood keeps its original existence and positive-residual conclusions. Its quantile carriers are not asserted to satisfy (219.1), so (219.15)--(219.19) are not transferred to them. The results leave universal original hard $F_{64}$ attainment or exclusion, unrestricted origin enclosure, compatible summable continuation, changing reservoirs, nonanalytic or smooth flat zero paths, finite-amplitude zero constructions and physical succession unresolved. The source-specific deductions consume the original heat form, affine relation space and exact H51 interface; they carry no global novelty or Lean/kernel assertion.

## 追加锚（本行以下为增补区）

## 220. The actual mixed first-last polar pencil on a fixed coarse partition

**Definition 220.1 (the original source and the six polar rows).** Retain the complete original endpoint, source, measure, clock and analytic suppliers of Appendix III Definitions 134.1, 135.1 and 136.1, including Appendix II §§115–117, 120, 122–126 and 133. The quantifier is every original $\theta=(a,\eta,d,b)\in\Theta$: $a,\eta,d>0$ are arbitrary finite original parameters, and $b$ is any of the permitted whole-$G$ Borel representatives of $g_d$ with $0<b\le M$. In particular, retain

$$
\begin{gathered}
G=H^1\times\mathbb R,\quad
(x,y,z,\zeta)(x',y',z',\zeta')
 =(x+x',y+y',z+z',\zeta+\zeta'+xy'),\quad
d\mu=dx\,dy\,dz\,d\zeta,\quad e=(0,0,0,0),\\
X_1=\partial_x,\quad X_2=\partial_y+x\partial_\zeta,\quad
X_3=\partial_z,\quad L=-\sum_{i=1}^3X_i^2,\quad
D_\zeta=-i\partial_\zeta,\quad L\Gamma=\delta_e,\\
\mathsf S=(aL+\eta D_\zeta^2-16\sqrt{a\eta}\,\Gamma)
       |_{C_c^\infty(G\setminus\{e\};\mathbb C)},\quad
C_{\rm src}(w_*)=1,\quad h=w_*/\|w_*\|_{L^2(\mu)},\quad C_{\rm src}(h)>0,\\
\rho=A_{\rm src}(h)/C_{\rm src}(h),\quad
D(H_{\rm end})=\{u\in D(\mathsf S^*):A_{\rm src}(u)=\rho C_{\rm src}(u)\},\quad
H_{\rm end}u=\mathsf S^*u,\\
m=h^2\mu,\quad m(G)=1,\quad U_hu=hu,\quad
K=U_h^{-1}H_{\rm end}U_h\ge0,\quad T_s=e^{-sK},\quad
\mathscr V=\mathscr V_0\dotplus\mathbb C1.
\end{gathered}
\tag{220.1}
$$

Here $\Gamma$, the source coefficients, $w_*$, the central units, the closure defining $\mathscr V_0$ and the full energy are exactly the ones in (134.1)–(134.3). The conservative diffusion starts at $e$ at original time zero; its densities are $g_s>0$ almost everywhere, of mass one, with $g_{s+t}=T_tg_s$ and $g_s\in L^2(m)$. Use the original epochs $2d,3d,4d$ and

$$
\begin{gathered}
P=T_d,\quad g=g_{2d},\quad M=1+\|g_d\|_\infty<\infty,\quad
c=(4M)^{-1},\\
f_3=cb,\quad f_B=1/4,\quad f_0=f_1=(3/4-cb)/2,\qquad
\mathcal C(u,v,w)=\int_GguP(vPw)\,dm.
\end{gathered}
\tag{220.2}
$$

The source summand in (220.1) is retained. Each occurrence of $\mathcal C$ has its displayed inputs and its own terminal heat factor. The original stochastic readout uses the same $f$ at the three epochs with conditionally independent fresh reads given the original path.

Fix any actual rotation-invariant coarse partition $E=(E_S,E_C,E_B)=(S,C,B)\in\mathscr E_\theta$ of (136.1); this class is nonempty by Proposition 136.2. Put $e_j=\mathbf1_{E_j}$, $\mathscr R=R_\pi$ and

$$
\begin{gathered}
V=\{u\in L^\infty(G,m;\mathbb R):u=0\text{ a.e. off }S,
                   \ u\circ\mathscr R=-u\text{ a.e.}\},\\
V^\Psi=\{u\in V:\int_G\psi u\,dm=0\ (\psi\in\Psi)\},
\qquad \Psi\subset L^1(G,m;\mathbb R)\text{ finite},\\
q_j=Pe_j,\qquad r_j=P(ge_j),\\
A_j(u)=\mathcal C(u,u,e_j)=\langle gu,P(q_ju)\rangle_m,\qquad
D_j(u)=\mathcal C(e_j,u,u)=\langle r_ju,Pu\rangle_m,\\
Q=(A_S,A_C,A_B,D_S,D_C,D_B),\qquad
B_l(u,v)=\tfrac12\{Q_l(u+v)-Q_l(u)-Q_l(v)\}.
\end{gathered}
\tag{220.3}
$$

All six rows are symmetric polars of the actual displayed ordered coefficients. They are different from the six values in (146.12). The $q_j,r_j$ have bounded invariant analytic representatives on $\Omega=\{r>0\}$, by the retained heat-image supplier (122.11) and the finite bound (133.2). Rotation invariance is a condition on this construction and its coarse consumer, not on the universal original $F_{64}$ target.

**Proposition 220.2 (no nonzero finite-rank member of the mixed pencil).** For every $E$ and $\Psi$ in Definition 220.1, every nonzero coefficient vector $(\lambda,\mu)\in\mathbb R^3\times\mathbb R^3$ gives an infinite-rank map

$$
u\longmapsto\left[v\longmapsto
       \sum_j\lambda_jB_j(u,v)+\sum_j\mu_jB_{3+j}(u,v)\right]
       \quad\text{from }V^\Psi\text{ to }(V^\Psi)^*.
\tag{220.4}
$$

The dual in this assertion is algebraic, with $j=1,2,3$ denoting $S,C,B$ in that order.

*Proof.* First work on $V$ without the moment constraints. Write

$$
q=P\Bigl(\sum_j\lambda_je_j\Bigr),\qquad
r=P\Bigl(g\sum_j\mu_je_j\Bigr),\qquad
R=\tfrac12(M_gPM_q+M_qPM_g+M_rP+PM_r).
\tag{220.5}
$$

This is a bounded self-adjoint real operator on $L^2(m)$, commuting with every rotation. Its bilinear pairing is precisely (220.4). Suppose that this pairing on $V$ has finite rank. Bounded supported odd vectors are dense in the $S$-supported odd Hilbert space, by truncation. All evaluation determinants of order greater than the alleged rank vanish on $V$; continuity extends them to that completion. Thus the compression $\chi R\chi$, $\chi=\mathbf1_S$, has finite rank on the odd Hilbert space.

Decompose that space into real angular sectors with frequencies $\pm\ell$, $\ell$ positive odd. Both $\chi$ and $R$ preserve these sectors. Only finitely many blocks of a finite-rank block diagonal operator can be nonzero. Choose a positive odd $\ell$ with zero compressed block, and complexify to the character space $H_\ell$. For any $S$-supported $u\in H_\ell$, the output $Ru$ is analytic on $\Omega$: every term in (220.5) contains positive-time heat, with analytic outside multipliers. Its quotient amplitude is analytic on the connected $X=(0,\infty)\times\mathbb R^2$. The zero compression makes it vanish on the positive-measure quotient of $S$. Analytic uniqueness gives $Ru=0$ globally. The uniqueness input is B. S. Mityagin, [*The zero set of a real analytic function*, Proposition 0](https://arxiv.org/abs/1512.07276v1), applied to real and imaginary parts; (136.5) supplies equivalence to a positive smooth quotient density.

For arbitrary $w\in H_\ell$, self-adjointness now gives $\chi Rw=0$ by testing against all $S$-supported inputs. The same analytic uniqueness gives $Rw=0$. Consequently

$$
R|_{H_\ell}=0.
\tag{220.6}
$$

We extract its coefficient relation using the actual heat kernel, rather than a different pencil. In the quotient coordinates write $dm=d\bar m(x)\,d\alpha/(2\pi)$ as in (136.5), and define

$$
\begin{aligned}
p_\ell(x,y)&=\int_0^{2\pi}
 p_d((x,0),(y,\alpha))e^{i\ell\alpha}\,\frac{d\alpha}{2\pi},\\
F(x,y)&=g(x)q(y)+q(x)g(y)+r(x)+r(y).
\end{aligned}
\tag{220.7}
$$

The continuous kernel of (220.5) in this character is $F(x,y)p_\ell(x,y)/2$. Equation (220.6), tested on compactly supported quotient inputs, makes this kernel zero; continuity and full support of $\bar m$ make it zero pointwise. There is a point $x_0$ with $p_\ell(x_0,x_0)>0$. Indeed $H_\ell$ contains nonzero compact punctured smooth tests, heat is injective, and evaluation of its nonzero continuous image is nonzero somewhere. The evaluation-vector identity (120.8)–(120.10), projected onto this character, gives

$$
p_\ell(x,x)=\|\Pi_\ell k_{d/2,(x,0)}\|_2^2.
\tag{220.8}
$$

This is the same evaluation identity as (153.8); no prescribed angular witness is assumed. Continuity gives a quotient neighborhood $U$ of $x_0$ on which $p_\ell$ is nonzero on $U\times U$. Thus $F=0$ there. The function $F$ is real analytic on connected $X\times X$, so

$$
F(x,y)=0\quad(x,y\in X),\qquad
r=-gq,\qquad (g(x)-g(y))(q(x)-q(y))=0.
\tag{220.9}
$$

The last identity follows by substituting the diagonal identity $r=-gq$ back into $F=0$. The actual $g$ is nonconstant: a constant $g$ would satisfy $(P-I)g=0$, contrary to Appendix IV Lemma 169.1. Choose a point $x$ for which $\{y:g(y)\ne g(x)\}$ is nonempty. That set is open, and (220.9) makes $q(y)=q(x)$ on it. Analytic continuation makes $q=\kappa$ constant on all $X$, and then $r=-\kappa g$.

It remains to exclude the constant cancellation case. Let $\beta$ be an invariant representative of $g_d$ from Proposition 136.2; its analytic representative on $\Omega$ satisfies $P\beta=g$. Injectivity and $P1=1$ give

$$
\sum_j\lambda_je_j=\kappa1,\qquad
g\sum_j\mu_je_j=-\kappa\beta.
\tag{220.10}
$$

Each coarse cell has positive measure by (136.1), so the first identity makes all $\lambda_j=\kappa$. If $\kappa\ne0$, the second identity on $S$ makes the analytic function $\mu_Sg+\kappa\beta$ zero on a positive-measure set. It is therefore zero on all $\Omega$. Integrating and using the unit masses of $g$ and $\beta$ gives $\mu_S=-\kappa$, hence $\beta=g$. Propagation then gives $Pg=g$, again contradicting Lemma 169.1 for the original source-start density. If $\kappa=0$, (220.10), $g>0$ almost everywhere and positive cell masses give $\lambda=\mu=0$. Thus every possible cancellation has forced the zero coefficient vector. This proves infinite rank for every nonzero mixed pencil on $V$.

Finally $V^\Psi$ has finite codimension in $V$, even when some tests are only in $L^1$. If a bilinear form has finite rank on $V^\Psi\times V^\Psi$, choose a finite-dimensional complement of $V^\Psi$. The two off-diagonal blocks and the block on that complement have finite rank, so the form has finite rank on $V\times V$. This contradicts the result just proved. The mixed assertion (220.4) follows. Its source-specific content is (220.5)–(220.10), including the constant cancellation case; the spectral, evaluation and analytic-uniqueness steps are consumed intermediates. $\square$

## 221. A hard odd split retaining six independent actual polars

**Theorem 221.1 (fixed-coarse hard sign with a six-row certificate).** Under exactly Definition 220.1, for every fixed $E\in\mathscr E_\theta$ and finite $\Psi\subset L^1(m;\mathbb R)$ there exist a whole-$G$ bounded real Borel $v$ and bounded real Borel $h_1,\ldots,h_6$ with

$$
\begin{gathered}
v^2=\mathbf1_S\quad\text{pointwise},\qquad
v\circ\mathscr R=-v\quad m\text{-a.e.},\qquad
\int_G\psi v\,dm=0\quad(\psi\in\Psi),\\
h_k=0\quad\text{on }G\setminus S,\qquad
h_k\circ\mathscr R=-h_k\quad\text{pointwise},\qquad
\int_G\psi h_k\,dm=0\quad(\psi\in\Psi),\\
A_j(v)=0\quad(j=S,C,B),\qquad
B_l(v,h_k)=\delta_{lk}\quad(1\le l,k\le6).
\end{gathered}
\tag{221.1}
$$

In particular $DQ(v)[h_k]=2\mathbf e_k$. On the subspace of $V^\Psi$ annihilating the first three derivatives, the last three derivatives map onto $\mathbb R^3$. The deterministic whole-$G$ Borel partition

$$
D_0=\{v=1\},\quad D_1=\{v=-1\},\quad D_3=C,\quad D_B=B
\tag{221.2}
$$

belongs to $\mathscr D_{12}(\theta)$ and satisfies all four exact actual-terminal contrasts

$$
\mathcal C(v,v,\mathbf1_{D_w})=0\qquad(w=0,1,3,B).
\tag{221.3}
$$

*Proof.* Proposition 220.2 says that the six maps $u\mapsto B_l(u,\cdot)$ from $V^\Psi$ to its algebraic dual span a six-dimensional space with no nonzero finite-rank member. The contrapositive of R. Meshulam and P. Šemrl, [*Locally linearly dependent operators*, Theorem 2.2, pp. 444–445](https://msp.org/pjm/2002/203-2/pjm-v203-n2-p10-s.pdf), with real field, $n=6$ and $c=1$, supplies $x\in V^\Psi$ whose six functionals are independent: local dependence would supply a nonzero combination of rank at most five. Choose $h_k^0\in V^\Psi$ dual to them, so that $B_l(x,h_k^0)=\delta_{lk}$.

We first impose the three old cancellations while preserving these evaluations. By Proposition 145.2, every nonzero pencil of $(A_S,A_C,A_B)$ has infinite negative index after any finite family of homogeneous linear constraints in $V$. On every such constrained subspace $W$, these three forms map onto $\mathbb R^3$. Here is the required consequence of the finite-sphere argument (147.6)–(147.8), applied to these actual forms. For each unit coefficient vector choose five negative directions in $W$. A finite cover of the coefficient sphere supplies their finite-dimensional span $F$ and $\delta>0$ such that every unit pencil has a five-dimensional spectral subspace with quadratic value at most $-\delta\|z\|_F^2$. For a prescribed $a\in\mathbb R^3$, minimize $\|A(y)-a\|^2$ on $\|y\|_F=R$, where $R^2>\|a\|/\delta$. If $\lambda=A(y)-a\ne0$, its five-dimensional negative subspace contains $z\ne0$ satisfying the four linear equations

$$
B_j(y,z)=0\quad(j=1,2,3),\qquad (y,z)_F=0.
$$

Along $y(s)=R(y+sz)/\|y+sz\|_F$, the second derivative of the squared residual is

$$
4\left(A_\lambda(z)-\frac{\lambda\cdot A(y)}{R^2}\|z\|_F^2\right)
\le4\|\lambda\|\|z\|_F^2
       \left(-\delta+\frac{\|a\|}{R^2}\right)<0,
\tag{221.4}
$$

since $\lambda\cdot A(y)=\|\lambda\|^2+\lambda\cdot a\ge-\|\lambda\|\|a\|$. This contradicts minimality and proves $A(W)=\mathbb R^3$. All directions found this way are actual bounded vectors in a finite-dimensional subspace; no limiting solution is substituted.

Apply this fact on

$$
W=\{z\in V^\Psi:B_l(z,h_k^0)=0\ (1\le l,k\le6),\quad
                           B_j(x,z)=0\ (1\le j\le3)\}
\tag{221.5}
$$

to find $z$ with $A(z)=-A(x)$. Every displayed constraint is a bounded real linear functional on $V$, by the integral kernels in (220.3). Thus $u=x+z$ has $A(u)=0$ and $B_l(u,h_k^0)=\delta_{lk}$. Choose $\varepsilon>0$ so that $\|\varepsilon u\|_\infty<1$. Consider the set

$$
\mathcal K=\{w\in V^\Psi:\|w\|_\infty\le1,\quad A(w)=0,\quad
                B_l(w,h_k^0)=\varepsilon\delta_{lk}\ (1\le l,k\le6)\}.
\tag{221.6}
$$

It contains $\varepsilon u$ and is weak-star compact. The linear constraints are weak-star closed. For the three quadratic constraints the ordered kernels are

$$
a_j(x,y)=g(x)p_d(x,y)q_j(y)\in L^1(m^2),\qquad
\|a_j\|_1=\int_GgPq_j\,dm\le1.
\tag{221.7}
$$

Finite rectangular-tensor approximation makes their quadratics continuous on the bounded weak-star ball, as in (145.10). The remaining fixed-input polar functionals also have $L^1$ representers; for the last three rows this follows from the bounded $r_j$ and the kernel $r_j(x)p_d(x,y)$. These observations verify all closures in (221.6).

Take a countable separating family $(\varphi_t)$ in the real unit ball of $L^1(m)$ and maximize

$$
J(w)=\sum_{t\ge1}2^{-t}\left(\int_G\varphi_tw\,dm\right)^2
\tag{221.8}
$$

on $\mathcal K$. The sum converges uniformly on the unit ball, is weak-star continuous and is strictly convex because the pairings separate classes. Let $w$ be a maximizer. If $|w|<1$ on a positive-measure subset of $S$, choose a positive-measure half-turn-invariant slack set

$$
A=S\cap\Omega\cap\{|w|\le1-1/n\}
\tag{221.9}
$$

for some $n$, using an exactly odd Borel representative on $\Omega$. Impose on bounded odd $\zeta$ supported in $A$ the moments in $\Psi$, all equations $B_l(\zeta,h_k^0)=0$ and the three equations $B_j(w,\zeta)=0$, $1\le j\le3$. Proposition 145.2 applies on this very slack set after all these finite constraints. Lemma 125.3 consequently supplies a nonzero such $\zeta$ with $A_j(\zeta)=0$ for all three $j$. For a sufficiently small $s>0$, both $w+s\zeta$ and $w-s\zeta$ belong to $\mathcal K$, since the quadratic cross terms and squared terms vanish exactly. Strict convexity of $J$ contradicts maximality. Therefore $|w|=1$ almost everywhere on $S$.

Represent each $h_k^0$ on the half-circle section, extend by negative reflection on $\Omega$, and set it to zero on the axis and off $S$. These are pointwise odd bounded Borel representatives of the same classes. Choose a bounded Borel representative $v$ of $w$ equal to a sign on all of $S$, repairing its null exceptional subset there, and put $v=0$ off $S$. This gives the pointwise square and almost-everywhere oddness required in (221.1). Set $h_k=h_k^0/\varepsilon$. All supports and moments survive these choices, and (221.6) gives the exact dual identities. Differentiation of the quadratics gives $DQ_l(v)[h_k]=2B_l(v,h_k)$; in particular $h_4,h_5,h_6$ give the last-three-row assertion with zero first-three-row derivatives.

The cells in (221.2) form one pointwise whole-$G$ partition. The three source densities $g_{jd}$, $j=2,3,4$, are half-turn invariant, so their integrals against $v$ vanish. Combining this with (136.1) and $\mathbf1_{D_{0,1}}=(e_S\pm v)/2$ gives all twelve original source marginals. Oddness and heat commutation give $\mathcal C(v,v,v)=0$: $vPv$ and $P(vPv)$ are even, while $gv$ is odd. Thus

$$
\mathcal C(v,v,\mathbf1_{D_0})
 =\tfrac12A_S(v)+\tfrac12\mathcal C(v,v,v)=0,\qquad
\mathcal C(v,v,\mathbf1_{D_1})
 =\tfrac12A_S(v)-\tfrac12\mathcal C(v,v,v)=0.
\tag{221.10}
$$

The other two equalities are $A_C(v)=A_B(v)=0$. Each heat image is therefore that of the same actual cell, including the two split terminals. All null repairs are invisible to the original positive-time source laws. The source-specific composition is the mixed pencil of Proposition 220.2, the actual signed-pencil property of Proposition 145.2, the constrained correction (221.4) and saturation retaining (221.6). Meshulam–Šemrl is a classical intermediate, not a new standalone result. $\square$

## 222. Co-selection on the original dense-test sequence and its limits

**Theorem 222.1 (the full III146 consumer with six polar rows).** For every original $\theta$, retain the very same invariant coarse cells $E_n=(S_n,C_n,B_n)$ in (146.3), including their rank-two coarse matrices, componentwise weak-star limits and matrix limits. Let $(\psi_t)$ be dense in the real unit ball of $L^1(m)$ and $\Psi_n=\{\psi_1,\ldots,\psi_n\}$. There is a new choice of hard splits over these $E_n$ and associated directions $h_{n,k}\in V_{S_n,-}^{\Psi_n}$ such that every property in (146.2) holds and, for the six actual forms $Q_n$ of (220.3) on $E_n$,

$$
B_{n,l}(v_n,h_{n,k})=\delta_{lk}\qquad(1\le l,k\le6).
\tag{222.1}
$$

The directions have bounded Borel representatives, pointwise supported in $S_n$ and pointwise odd, and annihilate every test in $\Psi_n$. This is an existential co-selection of new splits; it is not an assertion about arbitrarily preselected signs from Theorem 146.1.

*Proof.* Apply Theorem 221.1 to each $E_n$ and $\Psi_n$, and define its partition by (221.2). This gives (222.1), all twelve source marginals and all four exact actual-terminal contrasts. It also gives the exact cubic contrast. The bilinear form with actual terminal $P\mathbf1_{C_n}$ pairs an invariant vector with $v_n$ to zero in either order by parity, and its value on $(v_n,v_n)$ is $A_C(v_n)=0$. The invertible change of components from the four indicators to $(\mathbf1_{S_n},\mathbf1_{C_n},\mathbf1_{B_n},v_n)$ therefore transforms the actual matrix $A^{D_n}$ by ordered congruence into

$$
\begin{pmatrix}A_{E_n}&0\\0&0\end{pmatrix}.
\tag{222.2}
$$

Its rank is exactly two. This calculation uses the same actual terminal $P\mathbf1_{C_n}$ throughout.

The increasing dense moment lists and $\|v_n\|_\infty\le1$ imply $v_n\overset{*}{\rightharpoonup}0$. The unchanged coarse limits (146.3) and the identities $\mathbf1_{D_{n,0,1}}=(\mathbf1_{S_n}\pm v_n)/2$ give all four componentwise weak-star limits to the original $f_y$. Finally the original common path density is

$$
W(x_1,x_2,x_3)=g(x_1)p_d(x_1,x_2)p_d(x_2,x_3),\qquad
W\ge0,\qquad \|W\|_{L^1(m^3)}=1.
\tag{222.3}
$$

Approximate it in $L^1$ by finite sums of rectangular tensors. On each such tensor the three componentwise weak-star pairings converge, and the bounded indicators control the approximation error uniformly. This proves convergence of every one of the 64 original triple-law coefficients, hence total-variation convergence. The coarse matrix limits persist because the coarse cells were unchanged. This establishes all the original-source equalities, rank and limits in (146.2)–(146.3), together with the additional certificate. $\square$

**Proposition 222.2 (diverging normalized duals and the hard-motion boundary).** For every co-selection in Theorem 222.1, any choices of bounded duals satisfying (222.1) obey

$$
\|h_{n,k}\|_\infty\longrightarrow\infty\qquad(k=1,\ldots,6).
\tag{222.4}
$$

No one of these nonzero directions supplies a feasible two-sided affine change of its hard split, even in the relaxed interval $[-1,1]$ with the coarse cells fixed. A curve of hard signs on fixed $S_n$ that is continuous in $L^\infty$ at its initial sign is constant near that sign as an $m$-class.

*Proof.* Since $\sum_jq_{n,j}=1$ and $\sum_jr_{n,j}=Pg$, the exact row-sum representers are

$$
\begin{aligned}
\sum_{j=1}^3B_{n,j}(v_n,h)&=\int_Ga_nh\,dm,
&a_n&=\tfrac12\{gPv_n+P(gv_n)\},\\
\sum_{j=1}^3B_{n,3+j}(v_n,h)&=\int_Gd_nh\,dm,
&d_n&=\tfrac12\{(Pg)Pv_n+P((Pg)v_n)\}.
\end{aligned}
\tag{222.5}
$$

The kernel $p_d$ belongs to $L^1(m^2)$ with mass one. Finite rectangular-tensor approximation therefore shows that $P$ sends any bounded weak-star-null sequence in $L^\infty$ to a norm-null sequence in $L^1$: for a rectangular kernel only finitely many scalar pairings occur, and the error is bounded by its $L^1$ kernel error times the uniform input bound. Apply this to $v_n$, $gv_n$ and $(Pg)v_n$, which are bounded and weak-star null because $g$ and $Pg$ are bounded. Hence

$$
\alpha_n=\|a_n\|_1\longrightarrow0,\qquad
\delta_n=\|d_n\|_1\longrightarrow0.
\tag{222.6}
$$

The normalization (222.1) makes the first row sum in (222.5) equal to one for $h=h_{n,k}$, $k=1,2,3$, and the second sum equal to one for $k=4,5,6$. In particular both norms in (222.6) are positive, and

$$
\|h_{n,k}\|_\infty\ge\alpha_n^{-1}\quad(k\le3),\qquad
\|h_{n,k}\|_\infty\ge\delta_n^{-1}\quad(k\ge4).
\tag{222.7}
$$

This proves divergence for every normalized dual, without any uniform inverse or quantitative cancellation claim.

At a hard sign $v^2=\mathbf1_S$, the two inequalities $|v+th|\le1$ and $|v-th|\le1$ for some $t>0$, with $h$ supported in $S$, force $h=0$ almost everywhere: on each of $\{v=1\}$ and $\{v=-1\}$ the two signs of the inequality force opposite signs for $h$. Each dual in (222.1) is nonzero, so none has this two-sided feasibility. Two distinct hard-sign classes on the same $S$ have $L^\infty$ distance two. This proves the continuity assertion and excludes these ambient derivatives as hard $L^\infty$ tangents. It makes no assertion excluding weaker-topology motions of sets or a different nonlinear hard construction.

For the unchanged completion criterion, put $M_j(v)=\mathcal C(v,e_j,v)$. The certificate is for the six derivatives of $A+D$, at a point where only the three $A$ values have been set to zero. It sets none of the six $M_j(v),D_j(v)$ values in (146.12) to zero. Together with the 27 exact coarse-law equations (146.11), all six of those additional zero values remain requirements for this restricted route to the original full law. The co-selection supplies neither those values nor a compatible legal correction paying them.

In particular this finite-amplitude hard split does not supply an origin-enclosing actual-law family for the finite completion route (156.6)–(156.9), or the fixed-start summable label-motion chain of Corollary 155.4. The first route still needs its legal calibrated family and zero-containing boundary estimate; the second still needs compatible summable choices from one hard start with full residual tending to zero. The ambient rank in (222.1) supplies neither condition, and (222.4) precludes a uniform bound on these normalized duals along the displayed dense-test sequence. The local positive-residual sections of §§212–214 and the analytic and bounded-proximity restrictions of §§218–219 retain their own hypotheses; none is added to the universal target here. Direct hard, changing oscillatory and other nonanalytic constructions remain outside those restricted arguments.

The statements in §§220–222 are source-specific deductions, `repo-derived` relative to their explicit inherited suppliers. They assert no global novelty, new verification of those suppliers, or Lean/kernel result. They neither attain nor exclude original $F_{64}(\theta)$ for any original $\theta$. Native physical realization would additionally require a correspondence preserving the actual source-inclusive endpoint, source law, measure, readout, successor, histories and clock; none is identified by the mathematical hard partitions and ambient polars above. $\square$

## 追加锚（本行以下为增补区）

## 223. Positive-factor hard attenuation from a prescribed certified split

**Theorem 223.1 (fixed-start attenuation with finite moments and a renewed certificate).** Under exactly Definition 220.1, fix any original $\theta$, any particular $E=(S,C,B)\in\mathscr E_\theta$, any finite real $L^1(m)$ list $\Psi$, and any particular $v,h_1,\ldots,h_6$ satisfying all of (221.1). These data are fixed before the following quantifiers. Put

$$
M_j(u)=\mathcal C(u,e_j,u),\qquad
D(u)=(D_S(u),D_C(u),D_B(u)),\qquad j\in\{S,C,B\}.
$$

For every $0<s<1$ and every $\varepsilon,\delta>0$, there is one bounded real whole-$G$ Borel $w$, zero off the same $S$, such that

$$
\begin{gathered}
w^2=\mathbf1_S\quad\text{pointwise},\qquad
w\circ\mathscr R=-w\quad m\text{-a.e.},\qquad
\int_G\psi w\,dm=0\quad(\psi\in\Psi),\\
A_j(w)=0\quad(j=S,C,B),\qquad D(w)=s^2D(v),\\
\max_j|M_j(w)-s^2M_j(v)|<\varepsilon,\\
\left|m\{w\ne v\}-\frac{1-s}{2}m(S)\right|<\varepsilon,\\
\max_{1\le l,k\le6}|B_l(w,h_k)-s\delta_{lk}|
       <\min\{\delta,s/12\}.
\end{gathered}
\tag{223.1}
$$

In particular, writing $J_{lk}=B_l(w,h_k)$, the matrix $J$ is invertible and

$$
\widetilde h_k=\sum_{a=1}^6h_a(J^{-1})_{ak}\in V^\Psi,
\qquad B_l(w,\widetilde h_k)=\delta_{lk}.
\tag{223.2}
$$

The directions in (223.2) have bounded whole-$G$ Borel representatives supported in $S$ and pointwise odd, so $w,\widetilde h_1,\ldots,\widetilde h_6$ again satisfy all of (221.1), for the same finite $\Psi$. The actual four-cell partition has indicators

$$
\bigl(\mathbf1_{D^w_0},\mathbf1_{D^w_1},
      \mathbf1_{D^w_3},\mathbf1_{D^w_B}\bigr)
 =\bigl((e_S+w)/2,(e_S-w)/2,e_C,e_B\bigr).
\tag{223.3}
$$

It belongs to $\mathscr D_{12}(\theta)$ and retains all four own-terminal equalities
$\mathcal C(w,w,\mathbf1_{D^w_y})=0$, $y=0,1,3,B$. If the unchanged coarse matrix $A_E$ has rank two, its actual four-cell matrix $A^{D^w}$ also has rank two. Every operator, source summand, source-start law, measure, clock and propagated terminal is the one in Definition 220.1.

*Proof.* Work first with real $m$-classes and write $Hz=\sum_{k=1}^6z_kh_k$ and $u(z)=sv+Hz$. The prescribed certificate gives the exact expansion

$$
Q(u(z))=s^2Q(v)+2sz+Q(Hz),\qquad A(v)=0.
\tag{223.4}
$$

Here $Q$ is the six-vector in (220.3); its last three rows are $D$, not $M$. Since $s<1$ and the directions are bounded, a closed nondegenerate six-simplex $T$ containing zero in its interior can be chosen so that $\|u(z)\|_\infty<1$ on $T$. Since $s>0$, a sufficiently small $r>0$ makes the cube $C_r=[-r,r]^6$ lie inside $T$ and gives, for every $z\in C_r$,

$$
\begin{gathered}
\|Q(Hz)\|_\infty\le sr/2,\qquad
\max_j|M_j(u(z))-s^2M_j(v)|<\varepsilon/2,\\
\frac12\left|\int_GvHz\,dm\right|<\varepsilon,\qquad
\max_{l,k}|B_l(Hz,h_k)|<\min\{\delta,s/12\}.
\end{gathered}
\tag{223.5}
$$

The first bound follows from the quadratic $O(r^2)$ remainder in (223.4); the other expressions are continuous at zero and vanish there. All of $u(z)$ lies in $V^\Psi$.

The nine ordered quadratic forms $A_j,D_j,M_j$ have, respectively, the actual kernels

$$
\begin{aligned}
k^A_j(x,y)&=g(x)p_d(x,y)q_j(y),\\
k^D_j(x,y)&=r_j(x)p_d(x,y),\\
k^M_j(x,y)&=g(x)\int_Gp_d(x,t)e_j(t)p_d(t,y)\,dm(t).
\end{aligned}
\tag{223.6}
$$

These kernels are nonnegative and in $L^1(m^2)$. Their masses are $\int gPq_j\,dm$, $\int ge_j\,dm$ and $\int gPe_j\,dm$, respectively, all at most one, by the same conservation and self-adjointness used in (145.10). Thus the bounded-ball rectangular-tensor argument of (145.10) applies to all nine forms, including the middle-slot form with both heat steps retained. Each fixed-input functional $B_l(\,\cdot\,,h_k)$ also has an $L^1(m)$ representer: symmetrize its kernel in (223.6), integrate one variable against bounded $h_k$, and use Fubini.

Approximate each of these nine kernels by a finite linear combination of indicator rectangles with $L^1$ error less than $\tfrac14\min\{sr,\varepsilon\}$. Let $\Phi$ be the finite real $L^1$ list consisting of their one-variable indicator factors, $\Psi$, $v$, and representers for all thirty-six $B_l(\,\cdot\,,h_k)$. If two real functions $a,b$ of absolute value at most one have identical pairings with every member of $\Phi$, then all rectangular approximants have identical quadratic values on $a,b$. Consequently

$$
\|Q(a)-Q(b)\|_\infty<sr/2,\qquad
\max_j|M_j(a)-M_j(b)|<\varepsilon/2.
\tag{223.7}
$$

We next construct a continuous hard family on $T$ that matches precisely these finitely many linear pairings, using only the original atomless measure. Let $H_+$ be the Borel half-circle section of $S\cap\Omega$ for the half-turn $\mathscr R$. Its reflection is the complementary half up to the null axis, and $\mathscr R$ preserves $m$. For $\phi\in\Phi$ put

$$
\widehat\phi(x)=\phi(x)-\phi(\mathscr R x),\qquad x\in H_+.
\tag{223.8}
$$

Integration of an odd supported function against $\phi$ is integration of its restriction to $H_+$ against $\widehat\phi$. Denote the seven vertices of $T$ by $t^0,\ldots,t^6$ and its barycentric coordinates by $\lambda_0(z),\ldots,\lambda_6(z)$. Choose Borel representatives, repairing a common null set so that all seven vertex functions have absolute value less than one everywhere on $H_+$. For each vertex, apply A. Dvoretzky, A. Wald and J. Wolfowitz, [*Relations among certain ranges of vector measures*, Theorem 4, printed p. 66](https://msp.org/pjm/1951/1-1/pjm-v1-n1-p06-s.pdf), to the two probabilities $(1+u(t^a))/2,(1-u(t^a))/2$ on $H_+$. The measures are $m|_{H_+}$ and the positive and negative parts of the finitely many densities $\widehat\phi$. They are finite and atomless, being absolutely continuous with respect to the original nonatomic $m$. The theorem supplies Borel signs $\zeta^a$ on $H_+$ such that

$$
\int_{H_+}\widehat\phi\,\zeta^a\,dm
 =\int_{H_+}\widehat\phi\,u(t^a)\,dm
 \qquad(\phi\in\Phi,\ 0\le a\le6).
\tag{223.9}
$$

Partition $H_+$ into the finitely many joint sign-pattern cells of the $\zeta^a$. On each positive-mass cell $A$, use the proportional subdivision (13) and Lemma 2 of the same paper, printed pp. 66–67, recursively to bisect simultaneously $m|_A$ and all the positive and negative measures just listed. The nested binary subdivisions define a Borel function $\tau_A:A\to[0,1]$ with

$$
\nu\bigl(A\cap\{\tau_A<t\}\bigr)=t\nu(A)
\qquad(0\le t\le1)
\tag{223.10}
$$

for every listed measure $\nu$, and hence for each signed measure $\widehat\phi\,m$. Indeed each binary word of length $n$ has $2^{-n}$ of every measure of $A$. The resulting identity for dyadic intervals extends to all thresholds by continuity of finite measures; the included measure $m$ makes each threshold fiber null. Null pattern cells can be assigned any fixed signs.

On $A$, cut the $\tau_A$ interval consecutively into lengths $\lambda_0(z),\ldots,\lambda_6(z)$, and use the constant sign $\zeta^a|_A$ on its $a$th interval. Assign endpoints consistently, including $\tau_A=1$ to the last interval. Reflect by negative sign to $\mathscr R H_+$, put zero off $S$, and use the given $v$ on the remaining null subset of $S$. This defines a whole-$G$ Borel hard sign $W(z)$, pointwise of square $e_S$ and odd almost everywhere. Equation (223.10) and the constant signs on each pattern cell give

$$
\begin{aligned}
\int_G\phi W(z)\,dm
 &=\sum_{a=0}^6\lambda_a(z)
                \int_{H_+}\widehat\phi\,\zeta^a\,dm\\
 &=\sum_{a=0}^6\lambda_a(z)\int_G\phi u(t^a)\,dm
  =\int_G\phi u(z)\,dm\qquad(\phi\in\Phi).
\end{aligned}
\tag{223.11}
$$

In particular all the $\Psi$ moments are exactly zero for every parameter. This family is continuous in $L^1(m)$: every cumulative barycentric threshold varies continuously, and (223.10) for $m$ bounds the measure changed by a threshold displacement by $m(A)$ times that displacement. There are finitely many cells and thresholds; reflection preserves this continuity. The $L^1$ kernels in (223.6), or their rectangular approximants followed by an arbitrarily small $L^1$ remainder, make $Q(W(z))$ continuous. This supplies actual continuous parameter dependence for the fixed-point step, rather than inferring it from pointwise purification choices.

On $C_r$ set $F(z)=Q(W(z))-s^2Q(v)$. By (223.7) and (223.11), the error $E(z)=Q(W(z))-Q(u(z))$ obeys $\|E(z)\|_\infty<sr/2$. Equations (223.4)–(223.5) show that the continuous map

$$
z\longmapsto z-\frac{F(z)}{2s}
       =-\frac{Q(Hz)+E(z)}{2s}
\tag{223.12}
$$

maps $C_r$ into the cube of radius $r/2$. Brouwer's fixed-point theorem, in the form of *Über Abbildung von Mannigfaltigkeiten*, [doi:10.1007/BF01456931](https://doi.org/10.1007/BF01456931), Satz 4, printed p. 115, applies to this continuous self-map of the finite-dimensional cube. A fixed point $z_*$ gives $Q(W(z_*))=s^2Q(v)$. Put $w=W(z_*)$. These are the exact $A$ and $D$ assertions. Equations (223.5) and (223.7) give the strict $M$ estimate. The tests in $\Phi$ also give

$$
\begin{aligned}
B_l(w,h_k)&=B_l(u(z_*),h_k)
              =s\delta_{lk}+B_l(Hz_*,h_k),\\
m\{w\ne v\}
 &=\frac12\left(m(S)-\int_Gvw\,dm\right)
  =\frac{1-s}{2}m(S)-\frac12\int_GvHz_*\,dm.
\end{aligned}
\tag{223.13}
$$

The second identity uses the two pointwise hard signs on exactly the same $S$. The remaining estimates follow from (223.5). Since every entry of $J-sI$ has absolute value less than $s/12$, its row-sum norm is less than $s/2$. Hence $J$ is invertible, proving (223.2); finite linear combinations retain all the stated support, oddness, Borel and moment properties.

Finally the invariant source densities $g_{2d},g_{3d},g_{4d}$ pair to zero with $w$, giving all twelve source marginals of (223.3). Half-turn parity gives $\mathcal C(w,w,w)=0$; $A(w)=0$ then gives all four own-terminal contrasts exactly as in (221.10). The ordered congruence (222.2) gives the rank assertion with the same actual terminal $Pe_C$. These arguments propagate the displayed partition itself; no heat factor is borrowed from a different endpoint.

The source-conditioned deduction is the finite hard realization of the radial target (223.4) from the prescribed certificate, with its simultaneous moments, middle-slot control and label cost. Rectangular approximation reuses (145.10); finite atomless linear purification and the finite-dimensional fixed-point theorem are classical intermediates consumed above, not standalone new results. This is repo-derived relative to the retained original suppliers and asserts no global novelty or Lean/kernel verification. The proof requires no selection of a new starting sign and no stronger hypothesis on the original $\theta$. Its constants and finite choices depend on the given certificate, the finite tests, $s$ and the tolerances. It asserts neither a uniform inverse as these data vary nor a continuous selection of the fixed points. In particular $s=0$ is excluded, and the invertible differential $2sI$ used in (223.12) supplies no zero-endpoint assertion. $\square$

**Corollary 223.2 (finite descent of the six remaining ordered defects).** For the prescribed certified start of Theorem 223.1, define

$$
R(v)=\max_{j\in\{S,C,B\}}\{|D_j(v)|,|M_j(v)|\}.
$$

If $R(v)>0$, $0<s<1$ and $0<\varepsilon<(1-s^2)R(v)/2$, any output in (223.1) satisfies

$$
R(w)<s^2R(v)+\varepsilon
       <\frac{1+s^2}{2}R(v)<R(v).
\tag{223.14}
$$

For every prescribed label budget $\ell>0$, one can choose $s<1$ sufficiently close to one and then $\varepsilon>0$ so that this strict descent and $m\{w\ne v\}<\ell$ hold together. The renewed certificate permits another finite application on the same $E$ and with the same finite $\Psi$ whenever the new $R$ is positive.

*Proof.* The exact $D$ scaling bounds its three absolute values by $s^2R(v)$; the $M$ estimate bounds the other three strictly by $s^2R(v)+\varepsilon$. This proves (223.14). Choose $(1-s)m(S)/2<\ell/2$, then take $\varepsilon<\min\{\ell/2,(1-s^2)R(v)/2\}$. The label estimate in (223.1) gives the budget. Equation (223.2) gives precisely the eligibility needed for finite reuse; no control of the new dual norms across unboundedly many steps is asserted.

These are the six ordered defects in Appendix III (146.12). The twenty-seven coarse equations (146.11) depend only on the unchanged $E$ and are not established by this descent. A nonzero $D_j(v)$ remains nonzero for every allowed $s$; an old zero of $M_j(v)$ need not be preserved by its approximate control. The corollary gives no decrease of the full $64$-coordinate residual norm, no H43 or H51 calibration, origin enclosure, global continuous section or physical successor.

The label cost also restricts repeated use of this particular attenuation. At a fixed $s<1$, every step with error $\varepsilon\le(1-s)m(S)/4$ has label cost greater than $(1-s)m(S)/4$, so sufficiently accurate fixed-factor repetition has nonvanishing cost. More generally, for a hypothetical iteration of these outputs on this same $S$ with factors $s_n$, label costs $c_n$ and errors $\varepsilon_n$, (223.1) gives $(1-s_n)m(S)/2<c_n+\varepsilon_n$. If both $\sum_n c_n$ and $\sum_n\varepsilon_n$ are finite, then $\sum_n(1-s_n)<\infty$, and $\prod_n s_n^2>0$ because every factor is positive and $-\log s_n\le2(1-s_n)$ eventually. The exact $D$ identity then prevents a nonzero initial $D$ from tending to zero along that specific budgeted iteration. This conditional cost consequence concerns only the outputs of Theorem 223.1, not all hard paths. Neither finite descent nor this cost calculation supplies the compatible full-residual-zero endpoint required by (155.31), or resolves universal original hard $F_{64}$ attainment or exclusion. $\square$

## 追加锚（本行以下为增补区）

## 224. Signed index of the actual aggregate-adjacent and three-middle pencil

**Definition 224.1 (the four actual forms).** Retain exactly the complete telescope of Definition 220.1, including (220.1)–(220.3) and all their inherited endpoint, source, regularity and analytic suppliers. Thus the quantifiers are every original $\theta=(a,\eta,d,b)\in\Theta$, with arbitrary finite $a,\eta,d>0$ and every permitted whole-$G$ Borel representative $b$; then every fixed actual rotation-invariant $E=(S,C,B)\in\mathscr E_\theta$. The full source-inclusive $K$, its form, $m=h^2\mu$, the source start at $e$, the original epochs $2d,3d,4d$, $P=T_d$, $g=g_{2d}$, $\mathscr R=R_\pi$ and the prescribed $M,c,f$ are unchanged. For real bounded $u$ put

$$
\begin{aligned}
A_{\rm sum}(u)&=\sum_{j\in\{S,C,B\}}A_j(u)
 =\mathcal C(u,u,1)=\langle gu,Pu\rangle_m,\\
M_j(u)&=\mathcal C(u,e_j,u)
 =\langle gu,P(e_jPu)\rangle_m,\\
\mathcal Q(u)&=(A_{\rm sum}(u),M_S(u),M_C(u),M_B(u)).
\end{aligned}
\tag{224.1}
$$

The first identity uses $\sum_jPe_j=P1=1$. Every $M_j$ retains its actual middle indicator between the two heat factors. For a half-turn-invariant Borel $A\subset S$ write

$$
V_{A,-}=\{u\in L^\infty(m;\mathbb R):u=0\text{ a.e. off }A,
                      \ u\circ\mathscr R=-u\text{ a.e.}\}.
\tag{224.2}
$$

For pencil coefficients use $\kappa\in\mathbb R$ and $\nu=(\nu_S,\nu_C,\nu_B)\in\mathbb R^3$; $\kappa$ is unrelated to the prescribed readout constant $c$. Define

$$
\begin{gathered}
\tau=\sum_j\nu_je_j,\qquad \mathsf T=M_\tau,\qquad \mathsf G=M_g,\\
\mathsf R=\kappa P+P\mathsf T P,\qquad
\mathsf B=\tfrac12(\mathsf G\mathsf R+\mathsf R\mathsf G),\\
\mathfrak q_{\kappa,\nu}(u)=\kappa A_{\rm sum}(u)+\sum_j\nu_jM_j(u)
                         =\langle u,\mathsf Bu\rangle_m.
\end{gathered}
\tag{224.3}
$$

Here $M_\phi$ denotes multiplication by $\phi$. The operators in (224.3) act boundedly on $L^2(m)$; no sign condition on $\kappa$ or $\nu$ is imposed.

**Theorem 224.2 (all coefficient faces on every odd slack space).** For every $\theta,E$ in Definition 224.1, every half-turn-invariant Borel $A\subset S$ with $m(A)>0$, and every $(\kappa,\nu)\ne0$, the form $\mathfrak q_{\kappa,\nu}$ has infinite negative index on $V_{A,-}$. Explicitly, for every integer $n\ge1$ and every finite collection of homogeneous real linear equations $L_i(u)=0$ on $V_{A,-}$, there is an $n$-dimensional real subspace of their common kernel on which $\mathfrak q_{\kappa,\nu}$ is negative definite. The $L_i$ need not be continuous. In particular the assertion applies to every finite real $L^1(m)$ moment list and every finite list of fixed-input polars of the four forms.

*Proof.* We first establish negative directions on actual global odd inputs, then localize those directions. All operators and energies below are restrictions or applications of the original source-inclusive operator.

### 224.A. The density and nonvanishing in each angular sector

Proposition III136.2 and Theorem II133.2 give

$$
0<g\quad m\text{-a.e.},\qquad
\|g\|_\infty\le\|g_d\|_\infty<M,\qquad \int_Gg\,dm=1.
\tag{224.4}
$$

The analytic representative of $g$ on connected $\Omega=\{r>0\}$ is supplied by (II122.11). It is invariant and nonnegative everywhere on $\Omega$: a negative value would, by continuity and the positive smooth local density of $m$, contradict (224.4). This representative is nonconstant. Indeed, if $g$ were constant, its mass would make it $1$; writing $g=Pb$ and using injectivity of $P$ and $P1=1$ would give $b=1$ as an $m$-class. Proposition III135.2 excludes this: propagation and heat injectivity would then make every $g_s=1$ for $0<s<d$, contradicting the continuous source start when tested against a nonzero nonnegative continuous function compactly supported away from $e$. Thus

$$
\gamma=\frac{g-1}{g+1}
\tag{224.5}
$$

is a bounded real invariant nonconstant analytic function on $\Omega$. It defines an $L^\infty(m)$ multiplier globally, with $|\gamma|\le1$; no positive lower bound on $g$ is used.

Fix any positive odd integer $\ell$. In the symmetric cylindrical coordinates of III136.1 let $H_\ell$ be the complex character space consisting of $e^{i\ell\alpha}a(r,z,\xi)$ with quotient amplitude in $L^2(\bar m)$. It is nonzero. Invariance makes $P,\mathsf G,\mathsf T,\mathsf R,\mathsf B$ preserve it. Write $K_\ell$ for the restriction of $K$; thus $P|_{H_\ell}=e^{-dK_\ell}$ is a positive injective contraction with dense range. Density follows from self-adjointness and zero kernel.

We need $\mathsf R|_{H_\ell}\ne0$ for this particular $\ell$. Suppose instead it were zero. The factorization $\mathsf R=P(\kappa I+\mathsf T P)$ and injectivity of $P$ give

$$
(\kappa I+\mathsf T P)|_{H_\ell}=0.
\tag{224.6}
$$

Choose a nonzero compact punctured quotient amplitude $\chi\in C_c^\infty(X)$, $X=(0,\infty)\times\mathbb R^2$, and a nonzero $\omega\in\mathbb R^3$. The actual tests of (II129.11)–(II129.12), in this fixed sector, are

$$
u_N=e^{i\ell\alpha}\chi(r,z,\xi)e^{iN\omega\cdot(r,z,\xi)},\qquad
\|u_N\|_2=\|\chi\|_{L^2(\bar m)}>0,\qquad \|Pu_N\|_2\longrightarrow0.
\tag{224.7}
$$

The smoothing assertion here uses the original heat: pairing $u_N$ against $Pz$ for $\|z\|_2\le1$, the punctured interior estimates and spectral smoothing uniformly bound every local derivative of $Pz$ on the compact amplitude support. Integration by parts in the $\omega$ direction gives decay of the pairing, uniformly in $z$, hence decay of the displayed global norm. The compact support and smooth positive density justify these integrations without crossing the source. Applying (224.6) gives $|\kappa|\|u_N\|_2\le\|\tau\|_\infty\|Pu_N\|_2$, so $\kappa=0$. Density of $\operatorname{Ran}(P|_{H_\ell})$ now implies $\mathsf T|_{H_\ell}=0$. Arbitrary quotient amplitudes in $H_\ell$ force $\tau=0$ almost everywhere on $X$, hence on $G$. All three cells have positive $m$-measure by (III136.1), the strictly positive source densities and $0<t_j\le1/4$. Thus $\nu_S=\nu_C=\nu_B=0$, contrary to the chosen coefficient vector. This proves sectorwise nonvanishing for every positive odd $\ell$, including $\kappa=0$ and every face where some $\nu_j=0$.

### 224.B. Assumed positivity and a one-sided heat range

Suppose $\mathsf B\ge0$ on this $H_\ell$. For $u\in H_\ell$ put $u_s=e^{-s\mathsf G}u$, $s\ge0$. Boundedness of the multipliers and operators gives

$$
\frac{d}{ds}\langle u_s,\mathsf R u_s\rangle_m
 =-2\langle u_s,\mathsf B u_s\rangle_m\le0.
\tag{224.8}
$$

Since $g>0$ almost everywhere, dominated convergence gives $u_s\to0$ in $L^2(m)$ as $s\to\infty$. The left quadratic value therefore tends to zero. Its monotonicity implies $\langle u,\mathsf Ru\rangle_m\ge0$ for every $u$, so $\mathsf R\ge0$. Moreover, as unweighted operator inequalities on $H_\ell$,

$$
0\le\mathsf R\le C_0P,\qquad
C_0=|\kappa|+\|\tau\|_\infty>0.
\tag{224.9}
$$

Indeed $\mathsf T\le\|\tau\|_\infty I$, $P^2\le P$ and $\kappa P\le|\kappa|P$. These inequalities are used only after (224.8) has established $\mathsf R\ge0$; no ordering is inferred by putting $g$ outside them.

Here is the needed Hilbert range factorization, with a possible kernel retained. Put $N=(\ker\mathsf R)^\perp$ and equip $\mathcal H_{\mathsf R}=\operatorname{Ran}\mathsf R^{1/2}$ with

$$
\|\mathsf R^{1/2}u\|_{\mathcal H_{\mathsf R}}=\|u\|_2
\quad(u\in N).
\tag{224.10}
$$

This is a complete nonzero Hilbert space, continuously embedded in $H_\ell$, since $\mathsf R|_{H_\ell}\ne0$. On the dense range of $P^{1/2}$ define $D(P^{1/2}u)=\mathsf R^{1/2}u$. Inequality (224.9) bounds $D$ by $\sqrt{C_0}$, so it extends boundedly to $H_\ell$. Taking adjoints in $DP^{1/2}=\mathsf R^{1/2}$ gives $\mathsf R^{1/2}=P^{1/2}D^*$. Consequently

$$
\mathcal H_{\mathsf R}\subset\operatorname{Ran}P^{1/2}
 =D(e^{dK_\ell/2}),\qquad
\|e^{dK_\ell/2}f\|_2\le\sqrt{C_0}\|f\|_{\mathcal H_{\mathsf R}}.
\tag{224.11}
$$

For $f=\mathsf R^{1/2}u$, $u\in N$, its heat preimage is $D^*u$, uniquely because heat is injective. The equality of the range and exponential domain follows directly from the spectral calculus for $K_\ell\ge0$. This is the elementary adjoint proof of the range-factorization principle of R. G. Douglas, *On majorization, factorization, and range inclusion of operators on Hilbert space*, [doi:10.1090/S0002-9939-1966-0203464-1](https://doi.org/10.1090/S0002-9939-1966-0203464-1); the proof above supplies the specific inclusion used here. Neither a lower heat comparison nor equality with the heat-range norm has been assumed.

### 224.C. Cayley contraction and an actual phase orbit

The exact algebraic identity

$$
(\mathsf G+I)\mathsf R(\mathsf G+I)
 -(\mathsf G-I)\mathsf R(\mathsf G-I)=4\mathsf B
\tag{224.12}
$$

and the bounded inverse of $\mathsf G+I$ imply
$\mathsf R-M_\gamma\mathsf R M_\gamma\ge0$. Define on $\operatorname{Ran}\mathsf R^{1/2}$ the map

$$
L_0(\mathsf R^{1/2}u)=\mathsf R^{1/2}M_\gamma u.
\tag{224.13}
$$

The inequality gives $\|\mathsf R^{1/2}M_\gamma u\|_2\le\|\mathsf R^{1/2}u\|_2$. Thus (224.13) is well-defined even for zero classes and extends to a contraction on $N$, then by zero on $\ker\mathsf R$. Taking adjoints in $L_0\mathsf R^{1/2}=\mathsf R^{1/2}M_\gamma$ gives $M_\gamma\mathsf R^{1/2}=\mathsf R^{1/2}L_0^*$. For $u\in N$, $L_0^*u\in N$ and $\|L_0^*u\|_2\le\|u\|_2$. Hence multiplication by $\gamma$ preserves $\mathcal H_{\mathsf R}$ and is a contraction in (224.10). These are precisely the kernel-sensitive adjoint steps, rather than an assumed inverse for $\mathsf R$.

Choose $u_0\in H_\ell$ with $\mathsf R u_0\ne0$, which exists by 224.A, and put $f=\mathsf R u_0$. Then $0\ne f\in\operatorname{Ran}\mathsf R\subset\mathcal H_{\mathsf R}$, so (224.11) makes $f$ an actual positive-time heat image. The bounded-operator exponential on this Hilbert space defines, for every real $s$,

$$
f_s=e^{is\gamma}f\in\mathcal H_{\mathsf R},\qquad
\|f_s\|_{\mathcal H_{\mathsf R}}\le e^{|s|}\|f\|_{\mathcal H_{\mathsf R}},\qquad
\|f_s\|_2=\|f\|_2.
\tag{224.14}
$$

Indeed the exponential series converges in the range norm; the continuous embedding into $L^2$ identifies its sum with the usual multiplier exponential, since multiplication by $\gamma$ is also bounded on $L^2$. Thus this is an actual pointwise phase orbit, with every member in the original heat range (224.11). In particular $f$ and all $f_s$ have analytic representatives on $\Omega$ by (II122.11). No assertion about arbitrary products in an exponential domain is required.

### 224.D. Linear spectral energy versus quadratic local phase energy

Let $a_0=\|f\|_2^2>0$. Normalize the spectral measure of $f_s$ for $K_\ell$ by $a_0$. Applying scalar Jensen to $e^{d\lambda}$ gives

$$
\begin{aligned}
\mathscr E[f_s]
 &=\|K_\ell^{1/2}f_s\|_2^2\\
 &\le\frac{a_0}{d}\log\frac{\|e^{dK_\ell/2}f_s\|_2^2}{a_0}\\
 &\le\frac{a_0}{d}
       \left[\log\frac{C_0\|f\|_{\mathcal H_{\mathsf R}}^2}{a_0}
                        +2|s|\right].
\end{aligned}
\tag{224.15}
$$

The exponential moment is finite by (224.11)–(224.14). It also makes the first spectral moment finite, since $d\lambda\le e^{d\lambda}$. Jensen can therefore be applied directly, or first with bounded spectral cutoffs and then by monotone convergence. The logarithmic constant is finite and nonnegative because $\|e^{dK_\ell/2}f\|_2\ge\|f\|_2$. This proves only a bound linear in $|s|$, which is sufficient.

Nonconstant analytic $\gamma$ on connected $\Omega$ has a nonempty open set where $\nabla\gamma\ne0$. The nonzero analytic $f$ cannot vanish on that whole set. Choose a relatively compact open patch $U\Subset\Omega$ on which $|f|$ and $|\nabla\gamma|$ are bounded below by positive constants. This follows from continuity after choosing a point where both are nonzero. For complex $f$, analytic uniqueness applies to its real and imaginary parts. The actual matrix $\mathsf A$ of (II122.8) is uniformly positive on this patch, and $dm=h^2d\mu$ has a positive smooth density there. The full original form (II120.1), which is the integral of this nonnegative local energy off the source, now gives

$$
\begin{aligned}
\mathscr E[f_s]
 &\ge\int_U(\nabla f+isf\nabla\gamma)^*
                 \mathsf A(\nabla f+isf\nabla\gamma)\,dm\\
 &=a_U s^2+b_U s+c_U,\\
a_U&=\int_U|f|^2(\nabla\gamma)^{\mathsf T}
                              \mathsf A\nabla\gamma\,dm>0.
\end{aligned}
\tag{224.16}
$$

All three coefficients are finite and real, with $c_U\ge0$, since the functions are smooth on the compact closure and $\mathsf A$ is real symmetric. Formula (224.16) is a local calculation on actual full-form vectors: membership in the form domain already follows from (224.11). It does not differentiate through the source or drop a source-domain condition. The lower bound $a_Us^2-|b_U||s|$ contradicts (224.15) as $|s|\to\infty$. Therefore $\mathsf B\ge0$ is impossible on every positive odd $H_\ell$.

### 224.E. Actual bounded real negative subspaces

For each positive odd $\ell$, failure of nonnegativity supplies $u\in H_\ell$ with $\langle u,\mathsf Bu\rangle_m<0$. Truncate its quotient amplitude in modulus to obtain bounded Borel character vectors converging to $u$ in $L^2$. Boundedness of $\mathsf B$ preserves strict negativity for a sufficiently large truncation, denoted again by $u$. Since $\mathsf B$ is real,

$$
\langle u,\mathsf Bu\rangle_m
 =\mathfrak q_{\kappa,\nu}(\Re u)+\mathfrak q_{\kappa,\nu}(\Im u).
$$

Rotation through $\pi/(2\ell)$ carries $\Re u$ to $\Im u$ up to sign; invariance makes their quadratic values equal. Each is therefore half the strictly negative complex value. Their real representatives are bounded and half-turn odd. Different positive angular frequencies have zero mixed polar pairing, by angular orthogonality and commutation with rotations. Selecting one such real vector from each of any $n$ distinct positive odd sectors gives an $n$-dimensional negative-definite subspace of the actual bounded global odd inputs. This proves infinite index there, before imposing support in $A$.

### 224.F. Localization in the coupled feature image and finite constraints

Let $H_-=\{u\in L^2(m;\mathbb R):u\circ\mathscr R=-u\}$ and let $V_{G,-}$ be its bounded real subspace. Use all four coupled features

$$
Z(u)=\bigl(P^{1/2}(gu),P^{1/2}u,P(gu),Pu\bigr)\in H_-^4.
\tag{224.17}
$$

For real feature vectors the bounded quadratic form

$$
\mathfrak b(z)=\kappa\langle z_1,z_2\rangle_m
                         +\langle z_3,\mathsf Tz_4\rangle_m
\tag{224.18}
$$

has $\mathfrak b(Z(u))=\mathfrak q_{\kappa,\nu}(u)$. In particular the last two features remain coupled through the actual $M_\tau$, rather than being treated as independent heat coordinates.

For $z\in H_-^4$, the adjoint pairing is

$$
\langle z,Z(u)\rangle=\int_GuF_z\,dm,\qquad
F_z=gP^{1/2}z_1+P^{1/2}z_2+gPz_3+Pz_4.
\tag{224.19}
$$

Boundedness of $g$, heat contraction and $m(G)=1$ give $F_z\in L^2(m)\subset L^1(m)$. It is half-turn odd and has an analytic representative on connected $\Omega$, by (II122.11). If $z$ annihilates $Z(V_{A,-})$, test (224.19) with $\mathbf1_A\operatorname{sgn}F_z$, using an odd Borel representative of $F_z$ on $\Omega$ and putting zero on the null axis. Half-turn invariance of $A$ makes this an allowed test. It follows that $F_z=0$ almost everywhere on $A$. The set $A\cap\Omega$ has positive measure and the smooth local density of $m$ is positive. B. S. Mityagin, [*The zero set of a real analytic function*, Proposition 0](https://arxiv.org/abs/1512.07276v1), therefore makes $F_z$ identically zero on $\Omega$. Conversely, annihilating all global odd inputs certainly annihilates those supported in $A$. Thus

$$
\overline{Z(V_{A,-})}=\overline{Z(V_{G,-})}\quad\text{in }H_-^4.
\tag{224.20}
$$

This is the feature-image localization argument of Proposition II127.2, here with the four features (224.17) and their actual adjoint density, so it does not require full rotation invariance of $A$. To transfer a finite-dimensional negative subspace from 224.E, apply $Z$ to a basis. Its image is independent because a zero feature image has quadratic value zero. Approximate these finitely many image vectors in (224.20) by images of members of $V_{A,-}$. Continuity of (224.18) makes the corresponding symmetric Gram matrices converge. Strict negative definiteness is open for finite real symmetric matrices, so close enough approximants are independent and remain negative definite. Lifting them gives actual bounded supported odd vectors of the required dimension. This transfers the proved actual-input index, not an index of an unconstrained ambient feature space.

Finally, for $r$ homogeneous real linear constraints and requested dimension $n$, first take a negative-definite subspace of dimension $n+r$ in $V_{A,-}$. Its intersection with the $r$ kernels has dimension at least $n$, by rank–nullity, and remains negative definite. This does not need continuity of the constraints. The theorem follows on every coefficient face. The source-specific composition is (224.3), sectorwise nonvanishing, the one-sided range/phase-energy contradiction and localization of these same heat features. Range factorization, Jensen and analytic uniqueness are classical intermediates used inside that composition. $\square$

## 225. One hard split with the three individual actual middle zeros

**Theorem 225.1 (the common hard zero fiber with finite moments).** Under exactly Definition 224.1, for every original $\theta$, every fixed $E=(S,C,B)\in\mathscr E_\theta$ and every finite $\Psi\subset L^1(m;\mathbb R)$, there is one bounded real whole-$G$ Borel $v$ such that

$$
\begin{gathered}
v^2=e_S\quad\text{pointwise},\qquad v=0\quad\text{pointwise off }S,\qquad
v\circ\mathscr R=-v\quad m\text{-a.e.},\\
\int_G\psi v\,dm=0\quad(\psi\in\Psi),\\
A_{\rm sum}(v)=M_S(v)=M_C(v)=M_B(v)=0.
\end{gathered}
\tag{225.1}
$$

All four quadratic equations hold on this same $v$ and this same $E$.

*Proof.* Work first with real $m$-classes. Write $\mathcal Q_k$, $1\le k\le4$, for the four forms in (224.1), and let

$$
\beta_k(u,z)=\tfrac12\{\mathcal Q_k(u+z)-\mathcal Q_k(u)-\mathcal Q_k(z)\}
\tag{225.2}
$$

be their symmetric polars. The four forms are linearly independent on each positive-measure $V_{A,-}$: a nonzero coefficient relation would give the zero form, contradicting Theorem 224.2. That theorem supplies the all-pencil hypothesis of Lemma II125.3 on every such space after every finite family of homogeneous linear constraints. In particular it supplies actual nonzero common quadratic-zero vectors there. We use this inside the compact-fiber saturation argument of Theorem III145.3, verifying the actual four kernels.

Let

$$
\mathcal K=\{w\in V_{S,-}:\|w\|_\infty\le1,\quad
      \int_G\psi w\,dm=0\ (\psi\in\Psi),\quad
      \mathcal Q_k(w)=0\ (1\le k\le4)\}.
\tag{225.3}
$$

It is nonempty, since $0\in\mathcal K$. It is weak-star compact in the unit ball of $L^\infty(m;\mathbb R)$. The support, oddness and moment conditions are weak-star closed: multiplication by $e_S$, the measure-preserving half-turn pullback and every $L^1$ pairing have their corresponding preadjoints on $L^1$. For the quadratic conditions, their actual ordered kernels are

$$
\begin{aligned}
k^{\rm sum}(x,y)&=g(x)p_d(x,y),\\
k^M_j(x,y)&=g(x)\int_Gp_d(x,t)e_j(t)p_d(t,y)\,dm(t).
\end{aligned}
\tag{225.4}
$$

The middle kernels are exactly (223.6), retaining both heat steps. They are nonnegative, and Tonelli and conservation give

$$
\|k^{\rm sum}\|_{L^1(m^2)}=1,\qquad
\|k^M_j\|_{L^1(m^2)}=\int_GgPe_j\,dm\le1.
\tag{225.5}
$$

Finite sums of indicator rectangles approximate each kernel in $L^1(m^2)$. On such a sum the quadratic is a finite sum of products of weak-star pairings. The error is uniformly bounded by the kernel's $L^1$ error on the unit ball. Thus all four quadratics are weak-star continuous there, proving the compactness assertion. Likewise, for bounded fixed $w$, each $\beta_k(w,\cdot)$ has an $L^1(m)$ representer: symmetrize (225.4) and integrate one variable against $w$, using Fubini and (225.5).

Choose a countable separating sequence $(\varphi_t)$ in the real unit ball of $L^1(m)$ and maximize on $\mathcal K$ the function

$$
J(w)=\sum_{t\ge1}2^{-t}\left(\int_G\varphi_tw\,dm\right)^2.
\tag{225.6}
$$

Such a sequence exists because the finite Borel measure on $G\cong\mathbb R^4$ has separable $L^1$. The series converges uniformly on the unit ball and is weak-star continuous. It is strictly convex on distinct $m$-classes, since the pairings separate them. Compactness therefore supplies a maximizer $w$; convexity of the fiber itself is not needed.

Take an exactly odd bounded Borel representative on $S\cap\Omega$ by restriction to a half-circle section and negative reflection, and put zero off $S$ and on the null axis. This represents the same class and can be chosen bounded in absolute value by one everywhere. If $|w|<1$ on a positive-measure subset of $S$, some

$$
A_n=S\cap\Omega\cap\{|w|\le1-1/n\}
\tag{225.7}
$$

has positive measure. It is a half-turn-invariant Borel subset of $S$. On $V_{A_n,-}$ impose the finitely many moment equations in $\Psi$ and all four linear equations $\beta_k(w,z)=0$. Theorem 224.2 applies after these constraints. Lemma II125.3 supplies a nonzero bounded $z$ in this constrained space with $\mathcal Q_k(z)=0$ for all four $k$. Equivalently, that lemma can be applied to a basis of the restricted span; a nonzero relation is again excluded by the constrained index theorem. For $0<\varepsilon\le1/(n\|z\|_\infty)$, both $w+\varepsilon z$ and $w-\varepsilon z$ remain in the unit ball and satisfy every linear constraint. The exact expansion

$$
\mathcal Q_k(w\pm\varepsilon z)
 =\mathcal Q_k(w)\pm2\varepsilon\beta_k(w,z)
                       +\varepsilon^2\mathcal Q_k(z)=0
\tag{225.8}
$$

keeps both in $\mathcal K$. They are distinct classes. Strict convexity yields $J(w)<[J(w+\varepsilon z)+J(w-\varepsilon z)]/2$, contradicting maximality. Hence $|w|=1$ almost everywhere on $S$.

On its full-measure sign subset choose the same Borel values, assign either sign on the remaining Borel null subset of $S$, and put $v=0$ everywhere off $S$. Then $v^2=e_S$ pointwise and $v$ is a bounded real whole-$G$ Borel representative of $w$. Its half-turn oddness is retained almost everywhere; pointwise oddness on the fixed axis is neither needed nor asserted. All moments and quadratic values are unchanged by the null repair. This proves (225.1). The consumed common-zero and extremal-hardening results are II125.3 and III145.3; the new input is their all-pencil hypothesis for the four actual forms, proved in Theorem 224.2. $\square$

**Corollary 225.2 (the same four indicators and their individual middle equations).** For the single sign in Theorem 225.1 define

$$
(d_0,d_1,d_3,d_B)=((e_S+v)/2,(e_S-v)/2,e_C,e_B),\qquad
D_y=\{d_y=1\}.
\tag{225.9}
$$

These are the indicators of one pointwise whole-$G$ Borel partition $D$, and

$$
\begin{gathered}
D\in\mathscr D_{12}(\theta),\qquad
\mathcal C(v,d_y,v)=0\quad(y=0,1,3,B),\\
\mathcal C(v,v,1)=0,\qquad \mathcal C(v,v,v)=0.
\end{gathered}
\tag{225.10}
$$

In particular the three individual equations $\mathcal C(v,e_j,v)=0$, $j=S,C,B$, in (III146.12) hold on this same object. For every original $\theta$ one may first select any fixed rank-two coarse $E$ supplied by (III146.3) and then construct this $v$ with any prescribed finite $\Psi$.

*Proof.* The pointwise square and support in (225.1) make $d_0,d_1$ take only the values zero and one, disjointly split $S$, and sum to $e_S$. The other indicators are those of the unchanged $C,B$. Thus they form exactly one Borel partition of all $G$. Each invariant density $g_{rd}$, $r=2,3,4$, pairs to zero with the odd $v$. The coarse marginals (III136.1) give

$$
\begin{aligned}
\int_Gg_{rd}d_0\,dm=\int_Gg_{rd}d_1\,dm
 &=\tfrac12(3/4-t_r)=\int_Gg_{rd}f_0\,dm
                         =\int_Gg_{rd}f_1\,dm,\\
\int_Gg_{rd}d_3\,dm&=t_r=\int_Gg_{rd}f_3\,dm,\\
\int_Gg_{rd}d_B\,dm&=1/4=\int_Gg_{rd}f_B\,dm.
\end{aligned}
\tag{225.11}
$$

These are all twelve original marginal equations. They use the original targets for every allowed representative $b$, since the representative replacements in III136.2 preserve its class and every displayed integral.

Heat commutes with the half-turn, so $Pv$ is odd, $vPv$ is even, and $P(vPv)$ is even. The integrand $gvP(vPv)$ is odd and integrable, hence $\mathcal C(v,v,v)=0$. Multilinearity with the actual indicators (225.9) gives

$$
\begin{aligned}
\mathcal C(v,d_0,v)&=\tfrac12M_S(v)+\tfrac12\mathcal C(v,v,v)=0,\\
\mathcal C(v,d_1,v)&=\tfrac12M_S(v)-\tfrac12\mathcal C(v,v,v)=0,\\
\mathcal C(v,d_3,v)&=M_C(v)=0,\qquad
\mathcal C(v,d_B,v)=M_B(v)=0.
\end{aligned}
\tag{225.12}
$$

All are individual actual middle-slot equalities. Every trilinear value remains $\int guP(wPz)\,dm$ with its displayed arguments. In particular the actual four-label coefficients are $\mathcal C(d_x,d_y,d_z)$ and their own propagated terminals are

$$
Pd_0=(Pe_S+Pv)/2,\quad Pd_1=(Pe_S-Pv)/2,\quad
Pd_3=Pe_C,\quad Pd_B=Pe_B.
\tag{225.13}
$$

No terminal is borrowed from another sign. The remaining equality in (225.10) is the simultaneous $A_{\rm sum}(v)=0$ in (225.1). Since Theorems 224.2 and 225.1 hold for every fixed admissible invariant coarse $E$, selecting a fixed rank-two member of (III146.3) before their application proves the last assertion.

The exact slice (225.1) has only $\sum_jA_j(v)=0$ among the adjacent-terminal forms. For this sign its individual own-terminal contrasts are exactly

$$
\begin{aligned}
\mathcal C(v,v,d_0)=\mathcal C(v,v,d_1)&=A_S(v)/2,\\
\mathcal C(v,v,d_3)&=A_C(v),\qquad
\mathcal C(v,v,d_B)=A_B(v).
\end{aligned}
\tag{225.14}
$$

Their individual zeros have not been established, and no individual $D_j(v)=\mathcal C(e_j,v,v)$ zero is established. This $v$ is a new choice in the four-form zero fiber, with no assertion that it is the sign of III145.3 or V221.1, and with no inherited six-row certificate. Rank two of the fixed coarse $A_E$ therefore gives no asserted rank for the final four-label matrix: the ordered congruence with terminal $Pe_C$ has its odd diagonal entry $A_C(v)$, which has not been set to zero. Neither the nine simultaneous quadratic zeros nor the 27 coarse equations (III146.11) are supplied by (225.1). Universal original hard $F_{64}$ attainment or exclusion and the physical-successor correspondence remain unresolved.

The source-specific four-form signed-index deduction and its common-object composition here are `repo-derived` relative to the explicit original suppliers. The literature credit within Theorem 224.2 concerns classical Hilbert range factorization, spectral Jensen and analytic zero-set uniqueness; the common-zero and compact-fiber mechanisms are the cited repository results. Constants and vector choices depend on the fixed original data and coefficients; no parameter-uniform estimate, globally positive density lower bound, continuous sign selection or compatible hard endpoint path is asserted. $\square$

## 追加锚（本行以下为增补区）
## 226. Constant categorical products inside the full actual hard-law image

**Definition 226.1 (the unchanged process and full hierarchical coordinates).** Retain exactly the complete original endpoint, source and analytic supplier telescope of Definition 211.1, hence of III152.1 and III135.1. In particular every original $\theta=(a,\eta,d,b)$ is permitted: $a,\eta,d>0$ are arbitrary finite original parameters and $b$ is any prescribed everywhere Borel representative of $g_d$ with $0<b\le M$. Keep the original group and product, raw Haar measure $\mu$, source $e$, unit-source field, coefficient-one zero state and positive normalized $h$, actual selector $A_{\rm src}=\rho C_{\rm src}$, full source-inclusive conservative operator $K$, measure $m=h^2\mu$, clock and source start. Write $P=T_d$, $g=g_{2d}$, $g_j=P^jg$ for $j=0,1,2$, $\mathcal L=\{0,1,3,B\}$ and $I=\{0,1,3\}$ as before. The epochs are still $2d,3d,4d$. The forms $L_j,Q_r,\mathcal C$ are precisely (III152.7), with $r\in\{12,13,23\}$.

For a pointwise Borel simplex tuple $u$ on all of $G$, let

$$
\begin{aligned}
\mathscr L_\theta(u)_{abc}&=\mathcal C(u_a,u_b,u_c),\\
\mathscr A_\theta&=\{\mathscr L_\theta(\mathbf1_D):
 D\text{ is one pointwise Borel partition of all }G\},\\
\mathscr M&=\left\{T\in\mathbb R^{\mathcal L^3}:
                    \sum_{a,b,c}T_{abc}=1\right\}.
\end{aligned}
\tag{226.1}
$$

All three factors in $\mathscr L_\theta(\mathbf1_D)$ use that same partition, and its last factor is its own $P\mathbf1_{D_c}$. For $T\in\mathscr M$, denote by $T_A$ its marginal on a set $A\subset\{1,2,3\}$ of slots, and set $T_\varnothing=1$. Define the hierarchical coordinate map

$$
\Xi(T)=\left(
 (T_{\{j+1\}}(a))_{j=0,1,2;\ a\in I},
 (T_{\{k,\ell\}}(a,b))_{k\ell=12,13,23;\ a,b\in I},
 (T_{abc})_{abc\in I^3}\right)\in\mathbb R^{63}.
\tag{226.2}
$$

Thus $\Xi(\mathscr L_\theta(u))=\mathcal J(u)$ for the actual map (212.17). The norm used on these coordinates is Euclidean. A finite common quantile carrier means a fixed finite Borel partition $\mathcal P$ of $G$, with each positive-mass cell subdivided into consecutive first-coordinate quantile slices in the fixed label order $0,1,3,B$. The slice masses may vary with the target; the cells, coordinate and order do not. Every null cell is assigned to $B$.

**Theorem 226.2 (the full constant-product interior).** Under exactly Definition 226.1, for every original $\theta$ and every constant categorical vector $\pi=(\pi_y)_{y\in\mathcal L}$ with $\pi_y>0$ and $\sum_y\pi_y=1$, there are $\delta_{\theta,\pi}>0$ and one finite common quantile carrier such that every $T\in\mathscr M$ satisfying

$$
\|\Xi(T)-\Xi(\pi^{\otimes3})\|_2<\delta_{\theta,\pi}
\tag{226.3}
$$

has strictly positive entries and equals $\mathscr L_\theta(\mathbf1_D)$ for a partition on that carrier. In particular $\pi^{\otimes3}$ is in the ordinary interior of $\mathscr A_\theta$ relative to $\mathscr M$, in all sixty-three hierarchical directions. The carrier and radius precede the target quantifier. No rank or zero-attainment hypothesis is added to the original supplier telescope.

*Proof.* Fix arbitrary original $\theta$ and strictly positive $\pi$.

### 226.A. An exact product center from the actual supported odd data

Use the invariant slack set $E$, bounded supported odd functions $x_i$ for $i\in I$, their finite disjoint spectra and ordered functional independence constructed in 212.A–B. They are the actual functions of (212.9)–(212.10). In particular

$$
L_j(x_i)=0,\qquad
Q_r(x_i,x_k)=0
\quad(j=0,1,2;\ i,k\in I;\ r=12,13,23).
\tag{226.4}
$$

The first equalities follow from invariance of $g_j$ and oddness, and the second include the self-pair equalities in (212.10). Set

$$
X_i=x_i\quad(i\in I),\qquad X_B=-x_0-x_1-x_3,
\qquad u_y^*=\pi_y+tX_y.
\tag{226.5}
$$

Choose one $t>0$ so small that $t\max_y\|X_y\|_\infty<\frac12\min_y\pi_y$. Bounded Borel representatives and one common Borel null repair make $\sum_yX_y=0$, support in $E$, and the resulting positive slack hold pointwise on all of $G$. Thus $u^*$ is a legal whole-$G$ simplex tuple, with uniform positive slack in all four components. Equation (226.4) extends to $X_a,X_b$ for all $a,b\in\mathcal L$ by bilinearity. Also

$$
\mathcal C(X_a,X_b,X_c)=0
\quad(a,b,c\in\mathcal L),
\tag{226.6}
$$

because simultaneous half-turn changes the sign of its three odd inputs, while $g,m,P$ are invariant. All integrals are finite by boundedness and the original probability path law. Conservation and self-adjointness give the exact expansion

$$
\begin{aligned}
\mathcal C(u_a^*,u_b^*,u_c^*)
={}&\pi_a\pi_b\pi_c
+t\bigl(\pi_b\pi_cL_0(X_a)+\pi_a\pi_cL_1(X_b)
                    +\pi_a\pi_bL_2(X_c)\bigr)\\
&+t^2\bigl(\pi_cQ_{12}(X_a,X_b)
          +\pi_bQ_{13}(X_a,X_c)
          +\pi_aQ_{23}(X_b,X_c)\bigr)
+t^3\mathcal C(X_a,X_b,X_c)\\
={}&\pi_a\pi_b\pi_c.
\end{aligned}
\tag{226.7}
$$

For example $\mathcal C(1,v,w)=Q_{23}(v,w)$ and $\mathcal C(v,1,w)=Q_{13}(v,w)$. Therefore the same actual nonconstant soft tuple $u^*$ has the exact product law in all sixty-four entries. The nonconstant original $f^0$ has been replaced only as the center of this construction; none of the process data has changed.

### 226.B. All sixty-three directions at this constant base

The change of center requires its own differential calculation. Use independent variations of components in $I$, compensating their sum in $B$. For the nine invariant directions $\mathbf1_Eg_j$ in these components, the marginal differential is three copies of

$$
G_E=(\langle g_i,\mathbf1_Eg_j\rangle_m)_{0\le i,j\le2}>0.
\tag{226.8}
$$

This is the original positive definite matrix (III152.34), using Lemma III147.2 and analytic uniqueness on the open quotient neighborhood in $E$. For an odd direction $h$ varying component $a\in I$, the actual pair derivative at (226.5) is

$$
D Q_r(u_i,u_j)[\delta u_a=h]\big|_{u=u^*}
=t\left(\mathbf1_{i=a}Q_r(h,x_j)
       +\mathbf1_{j=a}Q_r(x_i,h)\right).
\tag{226.9}
$$

Every constant-$\pi$ term pairs an odd function with an invariant density and is zero. In the high sector belonging to each $x_a$, the six ordered functionals remain independent by (212.10). For the diagonal pair $(a,a)$ their three sums are independent, so choose three dual odd directions there varying component $a$. For each unordered distinct pair $\{a,b\}$ choose six dual odd directions in the high sector of $x_b$, varying component $a$, for the six rows $Q_r(h,x_b),Q_r(x_b,h)$. Disjoint spectra kill all the undesignated pair rows. These are the twenty-seven directions of (III152.35)–(III152.36), now with the derivative (226.9). Their marginal derivatives vanish and their pair block is invertible, with its nonzero factor $t$. Together with (226.8) they give an invertible lower thirty-six-row block at the new center.

For the remaining twenty-seven directions reuse the actual vector densities $\mathbf R_{abc}$ of (212.11), whose Gram matrix $\mathsf G$ is positive definite by (212.13). Define

$$
e_{abc,j}=R_{abc}^{(j)}\quad(j\in I),\qquad
 e_{abc,B}=-\sum_{j\in I}R_{abc}^{(j)}
 \quad(abc\in I^3).
\tag{226.10}
$$

They are bounded, supported in $E$, even and of zero angular mean. Their lower thirty-six derivatives at $u^*$ are zero. In the marginal rows this follows from zero angular mean; in pair rows the constant part is invariant and the linear-in-$t$ part is odd. For any direction $h$ of the form (226.10), self-adjointness gives

$$
D\mathcal C(u_a,u_b,u_c)[h]\big|_{u=u^*}
=t^2\sum_{j\in I}\int_G h_jR_{abc}^{(j)}\,dm
\quad(abc\in I^3).
\tag{226.11}
$$

Indeed its first-, middle- and last-slot quadratic densities are respectively $gP(x_bPx_c)$, $P(gx_a)Px_c$ and $P(x_bP(gx_a))$, exactly those defining (212.11). At this constant base the constant-in-$t$ density is still invariant and the linear-in-$t$ density is odd, so both pair to zero with $h$. Its support and zero angular mean permit the supported mean-removal in (212.11). Thus the last block is precisely $t^2\mathsf G$, with no new rank premise.

Number these sixty-three directions $e_1,\ldots,e_{63}$. The actual derivative of $\mathcal J$ on them is block triangular with invertible diagonal blocks. Consequently

$$
u(z)=u^*+\sum_{k=1}^{63}z_ke_k,\qquad
F(z)=\mathcal J(u(z))-\Xi(\pi^{\otimes3}),\qquad
A=DF(0)
\tag{226.12}
$$

satisfies $F(0)=0$ and $A$ is invertible. All directions are bounded and sum to zero including their $B$ component. The pointwise slack in (226.5) gives a legal closed parameter ball. Since $F$ is polynomial, shrink its radius to $r>0$ so that

$$
\sup_{\|z\|_2\le r}\|z-A^{-1}F(z)\|_2<r/4.
\tag{226.13}
$$

Equations (226.7)–(226.13) establish an exact product-law center with a nonsingular full sixty-three-dimensional differential under the original source.

### 226.C. A fixed finite hard carrier covers a full coordinate ball

Apply the common finite quantile construction of 212.D to the whole family $u(z)$ in (226.12). With the same increasing finite Borel partitions $\mathcal P_n$, form $D_n(z)$ by consecutive slices of masses $\int_{A_0}u_y(z)\,dm$ inside every positive-mass cell $A_0$. The original measure has no mass on coordinate hyperplanes. Hence all slices exist, their endpoints can be assigned consistently, and the resulting $D_n(z)$ is a deterministic Borel partition of the whole original $G$. The slice estimate remains

$$
\sum_y m(D_{n,y}(z)\mathbin\triangle D_{n,y}(z'))
\le6\sum_y\|u_y(z)-u_y(z')\|_1.
\tag{226.14}
$$

Keep the exact original path density $W$ and its conditional expectations $W_n$ from (212.21). The argument of (212.22), using the same tuple or partition in every slot, yields

$$
\begin{aligned}
F_n(z)&=\mathcal J(\mathbf1_{D_n(z)})-\Xi(\pi^{\otimes3}),\\
\sup_{\|z\|_2\le r}\|F_n(z)-F(z)\|_2
 &\le2\sqrt{63}\,\|W-W_n\|_1\longrightarrow0.
\end{aligned}
\tag{226.15}
$$

For $W_n$ each coordinate integral factors cellwise, so equality of the slice masses gives exact equality with $u(z)$. The two errors against $W-W_n$ give the displayed bound, uniformly for the whole parameter ball. Continuity of $F_n$ follows by telescoping each changed slot, using the bounded original marginals $g,Pg,P^2g$ and (226.14). This argument imposes no regularity on moving quantile boundaries.

Choose one finite $n$ with $\sup\|A^{-1}(F_n-F)\|_2<r/4$. For every coordinate displacement $v$ satisfying $\|A^{-1}v\|_2<r/4$, the map

$$
z\longmapsto z-A^{-1}(F_n(z)-v)
\tag{226.16}
$$

sends the closed radius-$r$ ball into itself by (226.13)–(226.15). Brouwer's finite-dimensional closed-ball theorem gives a root $z_v$ with $F_n(z_v)=v$. In particular the exact center $v=0$ and a full open neighborhood of it are attained on this single finite $\mathcal P_n$ carrier. A continuous choice of the roots is not required or asserted.

Finally $\Xi:\mathscr M\to\mathbb R^{63}$ is an affine isomorphism. To see this without restricting to a fixed lower-law fiber, fix the labels in $I$ on slots $F$ and put $B$ in the other slots $B_0=\{1,2,3\}\setminus F$. Complement expansion gives

$$
T_{(a_F,B_{B_0})}
=\sum_{A_0\subset B_0}(-1)^{|A_0|}
  \sum_{i_{A_0}\in I^{A_0}}
      T_{F\cup A_0}(a_F,i_{A_0}).
\tag{226.17}
$$

Every marginal on the right is among (226.2), or is $T_\varnothing=1$. Conversely these formulas reconstruct a tensor of total mass one with the prescribed hierarchical marginals: summing a reconstructed $B$ slot cancels the corresponding negative terms and returns the specified lower marginal. Thus all sixty-three coordinate displacements, including changing lower laws, have unique tensors in $\mathscr M$.

The entries of $\pi^{\otimes3}$ are strictly positive and the inverse affine map is continuous. Choose $\delta_{\theta,\pi}>0$ small enough that (226.3) ensures positivity and $\|A^{-1}(\Xi(T)-\Xi(\pi^{\otimes3}))\|_2<r/4$. The root just constructed has the same $\Xi$ coordinates as $T$; (226.17) proves equality of all sixty-four actual coefficients. This proves the theorem.

The source-specific inputs (212.9)–(212.13) retain their exact hypotheses and consume the classical intermediate results of R. Meshulam and P. Šemrl, *Locally linearly dependent operators*, [Theorem 2.2](https://doi.org/10.2140/pjm.2002.203.441), and B. S. Mityagin, *The zero set of a real analytic function*, [Proposition 0](https://arxiv.org/abs/1512.07276v1). The fixed-point step is the closed-ball form of L. E. J. Brouwer, *Über Abbildung von Mannigfaltigkeiten*, [doi:10.1007/BF01456931](https://doi.org/10.1007/BF01456931), as used in 212.D. Finite linear vector-measure purification, including Dvoretzky–Wald–Wolfowitz's [§3 Theorem 4 and Lemma 2](https://msp.org/pjm/1951/1-1/pjm-v1-n1-p06-s.pdf), preserves fixed linear integrals; it is not being applied to the partition-dependent nonlinear law. Here the exact nonlinear attainment follows from the actual center, all sixty-three derivatives and the uniform hard approximation followed by (226.16). The constant-base full-law interior is repo-derived from these original source data, rather than a separate assertion of a general purification theorem. $\square$

## 227. Actual complete laws for a nonconstant weak-contrast comparison

**Definition 227.1 (only the comparison readout changes).** Under Definition 226.1 retain the original $M,c,b,f$. Since $\int_Gb\,dm=1$, put

$$
\begin{gathered}
\pi=\int_G f\,dm
 =\left(\frac{3/4-c}{2},\frac{3/4-c}{2},c,\frac14\right),\\
f^\lambda=\pi+\lambda(f-\pi),\qquad 0\le\lambda\le1,\\
f_3^\lambda=c[1+\lambda(b-1)],\quad f_B^\lambda=\tfrac14,\quad
 f_0^\lambda=f_1^\lambda=\frac{3/4-c[1+\lambda(b-1)]}{2}.
\end{gathered}
\tag{227.1}
$$

Every $f^\lambda$ is a pointwise Borel simplex tuple on the whole $G$. Its comparison law uses that same readout at the three original epochs, with conditionally independent fresh read noises given the original path, namely $T^\lambda=\mathscr L_\theta(f^\lambda)$. The source, operator, measure and epochs are exactly those of Definition 226.1, without stationary replacement or a change of clock.

**Corollary 227.2 (nonconstant actual complete64 laws and own-terminal rank two).** Under exactly Definition 227.1, for every original $\theta$ there exist $\epsilon_\theta\in(0,1)$ and one finite common quantile carrier such that for every $0\le\lambda\le\epsilon_\theta$ a pointwise whole-$G$ Borel partition $D^\lambda$ on that carrier satisfies

$$
\mathcal C(\mathbf1_{D_a^\lambda},\mathbf1_{D_b^\lambda},
                          \mathbf1_{D_c^\lambda})
 =\mathcal C(f_a^\lambda,f_b^\lambda,f_c^\lambda)
\quad(a,b,c\in\mathcal L).
\tag{227.2}
$$

For every $0<\lambda\le\epsilon_\theta$, the readout $f^\lambda$ is nonconstant, its three label-$3$ source marginal masses are strictly decreasing in chronological order, and the displayed partition's actual own-label-$3$ terminal matrix satisfies

$$
A^{D^\lambda}_{ab}
 =\int_Gg\mathbf1_{D_a^\lambda}
       P\!\left(\mathbf1_{D_b^\lambda}P\mathbf1_{D_3^\lambda}\right)dm,
\qquad \operatorname{rank}A^{D^\lambda}=2.
\tag{227.3}
$$

At $\lambda=0$ the same matrix has rank one. At $\lambda=1$ the comparison law is exactly the original $F_{64}$ target, but (227.2) is asserted only on the stated small interval.

*Proof.* All four entries of $\pi$ are strictly positive, since $0<c<1/4$. Apply Theorem 226.2 at this $\pi$, obtaining a full coordinate neighborhood and one finite carrier. Each coefficient of $T^\lambda$ is a polynomial in $\lambda$ of degree at most three, and $T^0=\pi^{\otimes3}$. Continuity therefore supplies $\epsilon_0\in(0,1)$ with

$$
\|\Xi(T^\lambda)-\Xi(\pi^{\otimes3})\|_2
 <\delta_{\theta,\pi}
\quad(0\le\lambda\le\epsilon_0).
\tag{227.4}
$$

The theorem gives all sixty-four equalities (227.2) on its one common carrier, without changing any process input. In particular it gives equality of the actual matrix (227.3) with $A^\lambda_{ab}=\mathcal C(f_a^\lambda,f_b^\lambda,f_3^\lambda)$. The partition's terminal in this equality is still its own $P\mathbf1_{D_3^\lambda}$; it is not identified with $Pf_3^\lambda$.

The class $b$ is nonconstant by Proposition III135.2. Thus $f^\lambda$ is nonconstant whenever $\lambda>0$. If $t_r=\int g_{rd}f_3\,dm$ are the original masses, that proposition gives $t_2>t_3>t_4>0$. Hence the changed target, and the same hard partition by marginalization of (227.2), have

$$
\int_Gg_{rd}f_3^\lambda\,dm
 =(1-\lambda)c+\lambda t_r
\quad(r=2,3,4),
\tag{227.5}
$$

strictly decreasing for every positive $\lambda$. These laws therefore differ from the constant categorical product even at the marginal level.

For rank, set $\xi_0=1$, $\xi_1=b-1$. The four functions $f_a^\lambda$ have coefficient matrix

$$
R_\lambda=
\begin{pmatrix}
(3/4-c)/2&-\lambda c/2\\
(3/4-c)/2&-\lambda c/2\\
c&\lambda c\\
1/4&0
\end{pmatrix}
\tag{227.6}
$$

in this two-function basis. Conservation and $Pb=g$ give

$$
\begin{aligned}
q_\lambda&=Pf_3^\lambda=c[(1-\lambda)+\lambda g],\\
(H_\lambda)_{ij}&=\langle g\xi_i,P(q_\lambda\xi_j)\rangle_m
\quad(i,j=0,1),\\
A^\lambda&=R_\lambda H_\lambda R_\lambda^{\mathsf T}.
\end{aligned}
\tag{227.7}
$$

All entries are finite since $b,g$ are bounded and $P$ is the original $L^2$ contraction. The matrix $H_\lambda$ is affine in $\lambda$; it need not be symmetric for $\lambda<1$. At $\lambda=1$, however,

$$
(H_1)_{ij}=c\langle g\xi_i,P(g\xi_j)\rangle_m,\qquad
v^{\mathsf T}H_1v
 =c\|T_{d/2}(g(v_0+v_1(b-1)))\|_2^2>0
 \quad(v\ne0).
\tag{227.8}
$$

Strict positivity of $g$, nonconstancy of $b$ and injectivity of the original heat semigroup give the strict inequality, exactly the weighted heat argument of III135.2. Thus the real polynomial $p(\lambda)=\det H_\lambda$, of degree at most two, has $p(1)>0$ and is not identically zero. Its positive roots are finite. Choose $\epsilon_1\in(0,1)$ so that $p(\lambda)\ne0$ throughout $0<\lambda\le\epsilon_1$; a root at zero is harmless.

The principal submatrix of $A^\lambda$ in the ordered rows and columns $(3,B)$ has determinant

$$
\det A^\lambda_{\{3,B\},\{3,B\}}
 =\left(\frac{\lambda c}{4}\right)^2p(\lambda)\ne0
\quad(0<\lambda\le\epsilon_1).
\tag{227.9}
$$

This determinant identity holds for nonsymmetric $H_\lambda$ as well. Equation (227.7) gives rank at most two, while (227.9) gives rank at least two. Taking $\epsilon_\theta=\min\{\epsilon_0,\epsilon_1\}$ proves (227.3) for every partition attaining the displayed complete law. At zero, $A^0_{ab}=\pi_a\pi_b\pi_3$ has rank one. No symmetry or positive definiteness of the changed target matrix was assumed.

For $\lambda<1$ it is the comparison readout, and hence its target marginal, pair and triple laws, that changes. It is not the original $\mathscr D_{12}(\theta)$ constraint with $f$ retained: (227.5) gives the changed right-hand sides. The original law at $\lambda=1$ and its rank-two slice remain exactly those of III135.1–III135.2. The local radius (227.4) provides neither continuation to $1$ nor compatible choices or summable label motion across $\lambda$. It supplies no simultaneous original nine-form zero, no original twenty-seven coarse equations, and no physical-successor correspondence. The complete original $F_{64}$ attainment or exclusion problem at $\lambda=1$, and the physical-successor problem, therefore remain unresolved by these local changed-comparison results. $\square$

## 追加锚（本行以下为增补区）
## 228. Slow original chronological schedules and the sharp motion budget

**Definition 228.1 (moving readouts on the original source process).** Retain exactly Definition 211.1, including every original $\theta=(a,\eta,d,b)$, its endpoint and analytic suppliers, source $e$, coefficient-one state, positive normalized $h$, full conservative source-inclusive nonnegative self-adjoint $K$, $m=h^2\mu$, original clock and source-start diffusion. Put

$$
P=T_d,\qquad s_n=(n+2)d,\qquad g_n=g_{s_n},\qquad p=\tfrac14,\qquad C=1-p=\tfrac34.
$$

Let $(D_n)_{n\ge0}$ be any deterministic pointwise whole-$G$ Borel four-label partition, fixed independently of the realized path. Write $B_n=D_{n,B}$, $u_n=\mathbf1_{B_n}$, $v_n=u_n-p$, and

$$
\begin{aligned}
\rho_n&=\|g_n-1\|_{L^1(m)},&
\delta_n&=m(B_n\mathbin\triangle B_{n+1}),\\
\ell_n&=m\{x:\operatorname{label}_{D_n}(x)\ne\operatorname{label}_{D_{n+1}}(x)\},\\
M_n&=\int_Gg_nv_n\,dm,&
J_n&=\int_Gg_nv_nP(v_{n+1})\,dm,\\
Q_n&=\int_Gg_nu_nP(u_{n+1})\,dm.&
\end{aligned}
\tag{228.1}
$$

Thus $\delta_n\le\ell_n$. Using $P1=1$, self-adjointness, $g_{n+1}=Pg_n$ and $\int_Gg_n\,dm=1$, expansion gives

$$
J_n=Q_n-p(M_n+p)-p(M_{n+1}+p)+p^2
=Q_n-pM_n-pM_{n+1}-p^2.
$$

The original soft readout $f_B=p$ has marginal target $p$, raw adjacent-pair target $p^2$ and centered adjacent-pair target $0$. Thus $M_n$ and $Q_n-p^2$ are the actual marginal and raw-pair discrepancies, and $M_n\to0$, $Q_n\to p^2$ is equivalent to $M_n\to0$, $J_n\to0$. The second factor in $Q_n$ is the actual propagated terminal $P\mathbf1_{B_{n+1}}$ from the next partition; in $J_n$ it is the centered terminal $P(v_{n+1})=P\mathbf1_{B_{n+1}}-p$. More generally, let $k_d(x,y)$ be the symmetric original transition kernel supplied by Appendix II Definition 123.1. For $r\ge0$ and $\mathbf y=(y_0,\ldots,y_r)\in\mathcal L^{r+1}$ define the actual source-start hard and unchanged-soft window coefficients

$$
\begin{aligned}
\mathsf H_{n,r}(\mathbf y)&=\int g_n(x_0)\prod_{j<r}k_d(x_j,x_{j+1})\prod_{j=0}^r\mathbf1_{D_{n+j,y_j}}(x_j)\,dm^{r+1},\\
\mathsf S_{n,r}(\mathbf y)&=\int g_n(x_0)\prod_{j<r}k_d(x_j,x_{j+1})\prod_{j=0}^rf_{y_j}(x_j)\,dm^{r+1}.
\end{aligned}
\tag{228.2}
$$

The product is empty when $r=0$. It uses the actual different partition at every slot and, in particular, every actual own terminal.

**Theorem 228.2 (forced escape and the exact divergent-budget boundary).** For every original $\theta$ and every schedule of Definition 228.1, set

$$
E_n=\|T_{d/2}v_n\|_2^2,\qquad
H_n=|J_n|+\tfrac9{16}\rho_n+\tfrac34\delta_n.
\tag{228.3}
$$

Then $\rho_n\to0$ and

$$
|J_n-E_n|\le\tfrac9{16}\rho_n+\tfrac34\delta_n,\qquad
0\le E_n\le H_n,\qquad
|M_n|\le\sqrt{H_n}+\tfrac34\rho_n.
\tag{228.4}
$$

For every $L<\infty$,

$$
\|E_K([0,L])v_n\|_2^2\le e^{dL}H_n.
\tag{228.5}
$$

If $\delta_n\to0$, then

$$
J_n\to0\quad\Longleftrightarrow\quad u_n\longrightarrow p\ \text{weak-star in }L^\infty(m).
\tag{228.6}
$$

Under these equivalent conditions, $M_n\to0$ automatically, and

$$
\|v_n\|_2^2\to\tfrac3{16},\qquad
\|E_K([0,L])v_n\|_2^2\to0,\qquad
\|E_K((L,\infty))v_n\|_2^2\to\tfrac3{16}.
\tag{228.7}
$$

For every fixed Borel $A\subseteq G$,

$$
m(B_n\mathbin\triangle A)\longrightarrow\tfrac14+\tfrac12m(A).
\tag{228.8}
$$

Consequently $(u_n)$ has no $L^1$-convergent subsequence and $\sum_n\delta_n=\infty$; hence finite total full-label motion $\sum_n\ell_n<\infty$ cannot match even the original centered $B$ marginal and adjacent-pair targets.

There is a sharp converse. For every prescribed sequence of finite numbers $\beta_n\ge0$, a deterministic whole-$G$ Borel schedule exists with

$$
\ell_n\le\beta_n,\qquad \ell_n\to0,\qquad
\mathsf H_{n,r}(\mathbf y)-\mathsf S_{n,r}(\mathbf y)\to0
\tag{228.9}
$$

for every fixed $r$ and every $\mathbf y\in\mathcal L^{r+1}$, if and only if $\sum_n\beta_n=\infty$. The constructed schedule has $m(B_n)=p$ at every epoch. Thus (228.9) is finite-window asymptotic agreement with the unchanged original soft law, including all four labels; it asserts neither exact finite-epoch equality nor an infinite-record total-variation identity.

*Proof.* The source relaxation $\rho_n\to0$ is (215.5), with the source still starting at $e$ and $g_n=T_{nd}g_{2d}$. Put $C_n=\langle v_n,Pv_{n+1}\rangle_m$. Since $\|v_n\|_\infty\le C$, the Markov contraction gives

$$
|J_n-C_n|\le C^2\rho_n=\tfrac9{16}\rho_n.
$$

Self-adjointness gives

$$
|C_n-E_n|=|\langle Pv_n,v_{n+1}-v_n\rangle_m|
\le C\|v_{n+1}-v_n\|_1=C\delta_n.
$$

This proves the first two bounds in (228.4). Since $T_{d/2}1=1$ and $\|1\|_2=1$,

$$
|m(B_n)-p|=|\langle1,v_n\rangle_m|\le\sqrt{E_n},\qquad
|M_n-\langle1,v_n\rangle_m|\le C\rho_n,
$$

which proves the last bound. Spectral calculus for $K$ gives (228.5).

Assume first $\delta_n\to0$ and $J_n\to0$. Then $H_n\to0$. For $\phi\in L^2(m)$ and finite $L$,

$$
|\langle v_n,\phi\rangle|\le e^{dL/2}\sqrt{H_n}\|\phi\|_2+
C\|(I-E_K([0,L]))\phi\|_2.
$$

First let $n\to\infty$, then $L\to\infty$, to obtain weak $L^2$ convergence $v_n\to0$. Truncating an arbitrary $L^1$ test and using $\|v_n\|_\infty\le C$ gives weak-star convergence, proving the forward implication in (228.6). Conversely, if $v_n\to0$ weak-star, the kernel sections $k_d(x,\cdot)$ belong to $L^1(m)$ almost everywhere, so $Pv_{n+1}(x)\to0$ almost everywhere. They are bounded by $C$, hence converge to zero in $L^1(m)$. Therefore

$$
|J_n|\le C\|Pv_{n+1}\|_1+C^2\rho_n\longrightarrow0,
$$

which proves the reverse implication without any common-partition assumption.

Writing $q_n=m(B_n)$ gives

$$
\|v_n\|_2^2=p^2+(1-2p)q_n,\qquad |q_n-p|\le\sqrt{H_n},
$$

so the first limit in (228.7) follows; the second is (228.5), and the third follows by subtracting it from the total norm. Weak-star convergence in (228.6) gives

$$
m(B_n\mathbin\triangle A)=q_n+m(A)-2\int_Au_n\,dm,
$$

which proves (228.8). An $L^1$-convergent subsequence of indicators has an almost-everywhere subsequence converging to an indicator, contradicting its weak-star limit $p\in(0,1)$. If $\sum\delta_n<\infty$, then $(u_n)$ is $L^1$-Cauchy, the same contradiction. Since $\delta_n\le\ell_n$, finite full-label motion is also impossible.

It remains to prove the sharp construction. Choose increasing finite Borel partitions $(\mathcal P_k)_{k\ge1}$ generating the Borel sigma algebra modulo $m$-null sets. In each positive-mass cell $C\in\mathcal P_k$, use a fixed coordinate quantile and the order $0,1,3,B$ to construct a Borel partition $F^k$ satisfying

$$
m(F^k_y\cap C)=\int_Cf_y\,dm\qquad(y\in\mathcal L).
\tag{228.10}
$$

The quantiles exist because $m$ is nonatomic and absolutely continuous in the original coordinates; null cells receive one fixed label. This is the deterministic common-partition construction of Appendix II Proposition 123.2.

For a cell $C\in\mathcal P_k$ and $y\ne z$, put $S_{C,yz}=C\cap F^k_y\cap F^{k+1}_z$. The equality of the $y$-masses of $F^k$ and $F^{k+1}$ on $C$ says that total mass entering and leaving each label agrees. Choose nested coordinate-quantile subsets $S_{C,yz}(t)\subseteq S_{C,yz}$ of mass $t\,m(S_{C,yz})$. Relabel $S_{C,yz}(t)$ from $y$ to $z$ and leave the other points unchanged; call the resulting partition $F^k(t)$, $0\le t\le1$. It has the cell masses (228.10), joins $F^k$ to $F^{k+1}$, and, with $L_k=\sum_{C,y\ne z}m(S_{C,yz})$,

$$
m\{\operatorname{label}_{F^k(t)}\ne\operatorname{label}_{F^k(t')}\}
=L_k|t-t'|.
\tag{228.11}
$$

If $\sum\beta_n=\infty$, then $\sum_n\min(\beta_n,c)=\infty$ for every $c>0$. Traverse the $k$th curve at the original consecutive epochs using increments

$$
\gamma_{n,k}=\min(\beta_n,1/k),\qquad
t_{n+1}=\min(1,t_n+\gamma_{n,k}/L_k)
$$

when $L_k>0$, and pass directly to the next endpoint when $L_k=0$. Every stage finishes in finitely many epochs, so the stage index tends to infinity. Equations (228.11) give $\ell_n\le\beta_n$ and $\ell_n\le1/k$ while in stage $k$, hence $\ell_n\to0$. All choices depend only on $\theta$, the fixed partitions and $\beta$, never on the realized path.

Every current and future partition from an epoch in stage $k$ has the cell masses (228.10) on $\mathcal P_k$, because later grids refine $\mathcal P_k$. Define

$$
W_r(x_0,\ldots,x_r)=\prod_{j<r}k_d(x_j,x_{j+1}),\qquad
W_{r,k}=\mathbb E[W_r\mid\mathcal P_k^{\otimes(r+1)}].
$$

The finite-algebra martingale approximation gives $\|W_r-W_{r,k}\|_1\to0$. Against $W_{r,k(n)}$, cellwise factorization and (228.10) make the hard and soft reference integrals exactly equal. Replacing $W_r$ by $W_{r,k(n)}$ costs at most $\|W_r-W_{r,k(n)}\|_1$ for each integral; replacing the reference initial density $1$ by the actual $g_n$ costs at most $\rho_n$. Therefore

$$
|\mathsf H_{n,r}(\mathbf y)-\mathsf S_{n,r}(\mathbf y)|
\le2\rho_n+2\|W_r-W_{r,k(n)}\|_1\longrightarrow0.
\tag{228.12}
$$

For each fixed $r$, summing (228.12) over the finitely many words gives total-variation convergence of the whole window. In particular the $B$ marginal and $BB$ pair converge to the unchanged soft values, so $J_n\to0$; the schedule also has $m(B_n)=\int f_B\,dm=p$ at every epoch.

If $\sum\beta_n<\infty$ and a schedule satisfying (228.9) existed, then $\sum\delta_n\le\sum\ell_n\le\sum\beta_n<\infty$. The $r=0$ and $r=1$ windows would give $J_n\to0$, while $\ell_n\to0$ gives $\delta_n\to0$, contradicting the already proved infinite-motion conclusion. This proves the iff statement. The spectral projection estimate uses the bounded Borel functional calculus for a nonnegative self-adjoint operator, as in Gerald Teschl, *Mathematical Methods in Quantum Mechanics*, §3.1, Theorem 3.1 and (3.17)–(3.18), https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf. The kernel, quantile and conditional-expectation intermediates are the original suppliers just cited; no extra regularity, selection, stationary restart, random state or changed clock is used. $\square$

This theorem is a paper-level, source-relative composition. It does not prove or exclude the original fixed-three-epoch $F_{64}$ predicate, exact coarse27 equations, simultaneous odd $A/D/M$ equations, the fixed-epoch cross-neighborhood summable-to-zero correction, exact all-epoch matching of every label, native physical identification or physical succession. It also makes no Lean/kernel or global novelty claim. Mathematical heat energy and label motion are the quantities in (228.3) and (228.1), not physical energy or physical cost.

## 追加锚（本行以下为增补区）
## 229. Prescribed accuracy at every original start with arbitrary finite windows

**Definition 229.1 (preassigned windows and accuracy).** Retain all original data and suppliers of Definitions 211.1 and 228.1, including every permitted $\theta=(a,\eta,d,b)$, coefficient-one state, source $e$, full source-inclusive conservative $K$, $m=h^2\mu$, $P=T_d$, $s_n=(n+2)d$, actual $g_n=g_{s_n}$ and unchanged four-label $f$ with $f_B=p=1/4$. Prescribe arrays

$$
0\le\beta_n<\infty,\qquad \epsilon_n>0,\quad \epsilon_n\longrightarrow0,
\qquad r_n\in\{1,2,\ldots\}\quad(n\ge0).
\tag{229.1}
$$

Each $r_n$ is finite; no common bound is imposed. For one deterministic whole-$G$ Borel schedule $D=(D_n)_{n\ge0}$, use exactly the laws $\mathsf H_{n,r_n}$ and $\mathsf S_{n,r_n}$ in (228.2), and set

$$
\operatorname{TV}_n(D,f)
 =\frac12\sum_{\mathbf y\in\mathcal L^{r_n+1}}
 |\mathsf H_{n,r_n}(\mathbf y)-\mathsf S_{n,r_n}(\mathbf y)|.
\tag{229.2}
$$

Every hard slot uses the actual $D_{n+j}$ and its own propagated terminal. All starts refer to the same original $e$-start process; the comparison retains the original conditionally independent soft reads.

**Theorem 229.2 (the prescribed finite-window motion-budget classification).** For every original $\theta$ and every arrays (229.1), there exists one deterministic pointwise whole-$G$ Borel four-label schedule, depending only on $\theta$ and the preassigned arrays and independently of realized paths, such that

$$
\ell_n\le\beta_n\quad(n\ge0),\qquad \ell_n\longrightarrow0,
\qquad \operatorname{TV}_n(D,f)\le\epsilon_n\quad(n\ge0),
\tag{229.3}
$$

if and only if $\sum_{n\ge0}\beta_n=\infty$. In the affirmative case the schedule can also satisfy

$$
m(D_{n,y})=\int_G f_y\,dm\qquad(n\ge0,\ y\in\mathcal L).
\tag{229.4}
$$

These are $m$-marginals; the actual source-start label marginals are controlled by (229.3). The initial hard partition is freely chosen using the full arrays. No spatial preparation, description or computation bound is imposed.

*Proof.* For necessity, projection of (229.3) onto the first two slots, which exist since $r_n\ge1$, gives $M_n\to0$ and $Q_n\to p^2$. The identity following (228.1) gives $J_n\to0$, while $\delta_n\le\ell_n\to0$. Theorem 228.2 already proves $\sum_n\delta_n=\infty$ under precisely these conditions. Since $\delta_n\le\ell_n\le\beta_n$, the caps must have divergent total.

Assume henceforth $\sum_n\beta_n=\infty$. For each fixed $k\ge1$, the clipped tail $\sum_{n\ge N}\min(\beta_n,1/k)$ diverges for every finite $N$: either infinitely many terms reach $1/k$, or its tail equals the original divergent tail. Choose consecutive finite time blocks by

$$
\begin{aligned}
N_1&=0,\\
N_{k+1}&=\min\left\{N>N_k:
 A_k:=\sum_{n=N_k}^{N-1}\min(\beta_n,1/k)\ge1\right\},\\
a_{n,k}&=\min(\beta_n,1/k)\quad(N_k\le n<N_{k+1}).
\end{aligned}
\tag{229.5}
$$

Here $A_k$ denotes the sum at the chosen endpoint. Every endpoint is finite, $N_k\to\infty$, and the blocks depend only on the caps. In particular they are chosen before the spatial refinements below.

Take increasing finite Borel partitions $(\mathcal R_j)_{j\ge1}$ generating the original coordinate Borel sigma algebra modulo null sets. For each start define its actual finite-dimensional density

$$
W_n(x_0,\ldots,x_{r_n})
 =g_n(x_0)\prod_{j<r_n}k_d(x_j,x_{j+1}).
\tag{229.6}
$$

Appendix II Definition 123.1 supplies the original transition kernel and entrance densities. Iterated conservation gives $W_n\ge0$, $W_n\in L^1(m^{\otimes(r_n+1)})$ and $\int W_n\,dm^{\otimes(r_n+1)}=1$. For each fixed $n$, the product algebras generated by $\mathcal R_j^{\otimes(r_n+1)}$ increase to the product Borel sigma algebra modulo null sets. Consequently

$$
\left\|W_n-
 \mathbb E_{m^{\otimes(r_n+1)}}[W_n\mid\mathcal R_j^{\otimes(r_n+1)}]
 \right\|_1\longrightarrow0\quad(j\to\infty).
\tag{229.7}
$$

This is the classical increasing-sigma-field $L^1$ convergence theorem, Rick Durrett, *Probability: Theory and Examples*, fifth-edition manuscript, Theorem 4.6.8, printed p. 247/PDF p. 255, https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf, applied with $X=W_n$ on the indicated product probability space. It is used only as an intermediate in this original-source argument, as is the actual-density approximation in 212.D.

Each block contains finitely many starts, each with a finite $r_n$. Thus choose strictly increasing indices $j_k$ and put $\mathcal P_k=\mathcal R_{j_k}$ so that simultaneously

$$
\widehat W_{n,k}:=\mathbb E[W_n\mid\mathcal P_k^{\otimes(r_n+1)}],
\qquad \|W_n-\widehat W_{n,k}\|_1<\epsilon_n
\quad(N_k\le n<N_{k+1}).
\tag{229.8}
$$

Only finitely many convergences (229.7) are required at each step. This choice imposes no relation between $r_n$, $\epsilon_n$ and the length of a time block.

For every $k$, use the balanced coordinate-quantile construction (228.10), from Appendix II Proposition 123.2, to obtain a whole-$G$ Borel partition $F^k$ with

$$
m(F^k_y\cap C)=\int_C f_y\,dm
\qquad(C\in\mathcal P_k,\ y\in\mathcal L).
\tag{229.9}
$$

For completeness, on each positive-mass cell cut consecutive first-coordinate quantile slices in order $0,1,3,B$ with these four masses. Their sum is $m(C)$. The distribution of that coordinate under the restriction of $m$ to any Borel remainder is continuous, because $m\ll\mu$ and coordinate hyperplanes are null. Hence every prescribed slice mass exists. Assign null cells one fixed label and endpoints consistently. This proves (229.9) for every label with pointwise Borel pieces.

Use the interpolation (228.11) between $F^k$ and $F^{k+1}$; its full-label balance can be checked directly. On $C\in\mathcal P_k$ put $S_{C,yz}=C\cap F^k_y\cap F^{k+1}_z$, for $y\ne z$. Since $\mathcal P_{k+1}$ refines $\mathcal P_k$, both endpoints have the masses (229.9), so

$$
\sum_{z\ne y}m(S_{C,yz})=\sum_{z\ne y}m(S_{C,zy}).
\tag{229.10}
$$

In every $S_{C,yz}$ choose nested Borel coordinate-quantile subsets $S_{C,yz}(t)$ of mass $t\,m(S_{C,yz})$, with empty and full endpoints. Relabel these subsets from $y$ to $z$. The sets $S_{C,yz}$ are disjoint, so this defines a pointwise partition $F^k(t)$, with $F^k(0)=F^k$ and $F^k(1)=F^{k+1}$. For every label its mass in $C$ changes by $t$ times the incoming mass minus $t$ times the outgoing mass; (229.10) makes that change zero. Also, putting $L_k=\sum_{C,y\ne z}m(S_{C,yz})\le1$, nestedness gives

$$
m\{\operatorname{label}_{F^k(t)}\ne\operatorname{label}_{F^k(t')}\}
 =L_k|t-t'|.
\tag{229.11}
$$

Zero-mass transition sets may be included only at the full endpoint; they affect neither balance nor motion. Thus this construction also covers $L_k=0$ without division by $L_k$.

Now define the single schedule on each block, including its common endpoint, by

$$
t_{n,k}=\frac1{A_k}\sum_{i=N_k}^{n-1}a_{i,k},\qquad
D_n=F^k(t_{n,k})\quad(N_k\le n\le N_{k+1}).
\tag{229.12}
$$

The definitions agree at $N_{k+1}$ because both give $F^{k+1}$. For every edge in block $k$, (229.11) gives

$$
\ell_n=L_k\frac{a_{n,k}}{A_k}
 \le\min(\beta_n,1/k)\quad(N_k\le n<N_{k+1}).
\tag{229.13}
$$

This proves the cap bounds and vanishing motion, including zero caps and arbitrarily large finite caps. The label-balance calculation and (229.9) give (229.4). More strongly, if $n$ belongs to block $k$, every partition $D_i$ with $i\ge n$ has (229.9) on $\mathcal P_k$: its own block has index at least $k$, and summing the finer-cell balances gives the asserted coarser-cell balances.

Fix any such $n$. For each word $\mathbf y\in\mathcal L^{r_n+1}$ write

$$
U_{n,\mathbf y}(x)=\prod_{j=0}^{r_n}\mathbf1_{D_{n+j,y_j}}(x_j),
\qquad V_{n,\mathbf y}(x)=\prod_{j=0}^{r_n}f_{y_j}(x_j).
\tag{229.14}
$$

On each product cell of $\mathcal P_k^{\otimes(r_n+1)}$, Fubini and the just-proved balances give equal integrals of these two products. Since $\widehat W_{n,k}$ is constant on each positive-mass product cell,

$$
\int\widehat W_{n,k}U_{n,\mathbf y}\,dm^{\otimes(r_n+1)}
 =\int\widehat W_{n,k}V_{n,\mathbf y}\,dm^{\otimes(r_n+1)}.
\tag{229.15}
$$

Both product families are nonnegative and sum to $1$ over all words, pointwise. Subtract (229.15) from the original hard and soft coefficients, sum absolute values, and use this normalization to obtain the dimension-independent estimate

$$
\begin{aligned}
\operatorname{TV}_n(D,f)
&\le\frac12\int|W_n-\widehat W_{n,k}|
 \sum_{\mathbf y}(U_{n,\mathbf y}+V_{n,\mathbf y})\,dm^{\otimes(r_n+1)}\\
&=\|W_n-\widehat W_{n,k}\|_1<\epsilon_n.
\end{aligned}
\tag{229.16}
$$

Every start is in one finite block. The same schedule therefore meets all inequalities simultaneously, even when its windows overlap or cross arbitrarily many block boundaries. The argument applies (229.7) separately before choosing each grid; it never substitutes a changing $r_n$ into a fixed-$r$ limit. All choices use only the original data and the full prescribed arrays, with no additional random state or path adaptation.

Equation (229.16) approximates the actual density $g_n\prod k_d$ directly, so it has no $\rho_n$ term. In particular arbitrary positive $\epsilon_n$ smaller than $\rho_n$ are allowed. The source-relaxation term in (228.12) is a limitation of that comparison with initial density $1$, not a lower bound on attainable finite-window accuracy here. The additional freedom used here is the preassigned-array-dependent spatial refinement and freely prepared initial partition; no mixing rate is required for sufficiency.

This repo-derived quantified composition serves the original moving-readout laws (228.2). The kernel and nonatomic-coordinate suppliers, balanced realizations and interpolation are reused; the additional conclusion is prescribed accuracy at every original start for one compatible schedule and arbitrary individually finite windows. It is not a new general purification theorem or a global novelty claim. The construction gives no prescribed initial partition, online generation, effective algorithm, source-uniform computation, exact finite-epoch equality or infinite-record total-variation assertion. It preserves the narrower scopes of §§211–228 and supplies no original fixed-common-partition $F_{64}$ or exact coarse27 solution, joint odd $A/D/M$ equations, fixed-epoch cross-neighborhood summable-to-zero correction, native physical source/successor/clock identification or physical installation. These are ordinary paper conclusions, with no Lean/kernel claim and no identification of label motion with physical energy or cost. $\square$

## 追加锚（本行以下为增补区）
