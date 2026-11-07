# FIB-ATOM recursive holographic boundary geometry · Continuation III Appendix V: an original hard residual neighborhood and the H51 slice

## 211. The exact antisymmetric contrast and its twelve-dimensional slice

**Definition 211.1 (the original telescope and the additional contrast).** Retain exactly [Appendix III Definitions 134.1, 154.1 and 155.1](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_III.md), with all their inherited endpoint, source and analytic suppliers, and [Appendix IV Definition 210.1](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_IV.md#210-one-original-common-partition-paying-the-seven-cubic-contrast-obligations). Thus $\theta=(a,\eta,d,b)$ ranges over every original finite $a,\eta,d>0$ and every permitted everywhere Borel representative $0<b\le M$ of $g_d$. The group $G=H^1\times\mathbb R$, original product, raw Haar measure $\mu$, source $e$, unit-source field $L\Gamma=\delta_e$, coefficient-one $w_*$, positive normalized $h$, selector $A_{\rm src}=\rho C_{\rm src}$ and full conservative source-inclusive operator $K$ are unchanged. In particular,

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

The diffusion starts at $e$ at time zero, in the original units and clock; the epochs remain $2d,3d,4d$. The target uses the same $f$ and its original conditionally independent fresh read noises at those epochs. Write $I=\{0,1,3\}$, $\mathcal L=I\cup\{B\}$, and let $\mathcal T_6$ be the six permutations of $013$. For a bounded pointwise Borel simplex tuple $u$ on the whole $G$, retain $\mathcal H_{36}$, $\mathcal H_{50}$ and $\eta_1(u)=u_0-u_1$, $\eta_2(u)=u_B-p$ from §§152 and 210, and put

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
