# FIB-ATOM recursive holographic boundary geometry · Continuation III Appendix II

## 114. Joint zero-energy correction and heat convergence on the full time half-line

**Definition 114.1 (the original critical family and its relative response).** Retain the original group, product, raw Lebesgue Haar measure, unit-source degree-$-3$ field $\Gamma$, horizontal generator $L$, free clock and central spectral units of [§§82--87](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md#82-rank-three-transport-carrier-point-source-stability-and-target-fibre-defect). Fix the same $a,\eta>0$. On $\mathcal H=L^2(G,d\mu;\mathbb C)$, let $H_\sigma$ be the nonnegative operator of [(111.2)](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX.md#111-actual-source-tightness-and-convergence-to-the-original-maximal-zero-line), at the actual critical coupling $g_\sigma$ on the entire complex $\mathcal E_\sigma$, for every $\sigma>2$. Let $H_{\rm end}$ be exactly the actual selector (112.5). Use the free operators and resolvents of (113.1), and put

$$
\begin{gathered}
A_\sigma=aL+\eta|D_w|^\sigma,\qquad
Q_{\sigma,r}=(A_\sigma+r)^{-1},\qquad
R_{\sigma,r}=(H_\sigma+r)^{-1},\qquad r>0,\\
R_{{\rm end},r}=(H_{\rm end}+r)^{-1},\qquad
P_\sigma=\mathbf1_{\{0\}}(H_\sigma),\qquad
P=\mathbf1_{\{0\}}(H_{\rm end})=|w\rangle\langle w|,\\
C_{\sigma,r}=r(R_{\sigma,r}-Q_{\sigma,r}),\qquad
C_{{\rm end},r}=r(R_{{\rm end},r}-Q_{2,r}).
\end{gathered}
\tag{114.1}
$$

Here $w$ is the original unit vector of Theorem 110.2; $\ker S^*=\mathbb Cw$ and $P_\sigma\to P$ in norm are the supplies (112.1) and (111.29). All operator norms below are on the whole original complex $\mathcal H$. A joint limit in $\sigma\downarrow2$ and $r\downarrow0$ permits arbitrary independent sequences of these two parameters.

**Theorem 114.2 (joint threshold correction for the actual original family).** For the family of Definition 114.1,

$$
\lim_{\substack{\sigma\downarrow2\\r\downarrow0}}
 \|C_{\sigma,r}-P_\sigma\|=0,
\qquad
\lim_{r\downarrow0}\|C_{{\rm end},r}-P\|=0.
\tag{114.2}
$$

Thus for every $\varepsilon>0$ there is $\delta>0$ such that the first norm is less than $\varepsilon$ whenever $2<\sigma<2+\delta$ and $0<r<\delta$, with no relation between the two parameters.

**Proof.** First record the zero-shift free estimates to be consumed below. For a bounded compactly supported multiplication function $m$, (105.6), (105.10) and (105.12) give

$$
\begin{gathered}
\|Q_{\sigma,r}F\|_2\le\frac{h_2}{a}\|\rho^2F\|_2
 \quad(F,\rho^2F\in L^2),\\
A_\sigma^{-1}m\longrightarrow A_2^{-1}m,\qquad
T_\sigma m\longrightarrow T_2m\quad\hbox{in norm},\qquad
T_\sigma=D_w/A_\sigma,
\end{gathered}
\tag{114.3}
$$

and the two limiting operators are compact. The first bound holds uniformly in $r>0$ and in orders sufficiently close to $2$: it is exactly the dual of (105.5), before taking its zero-shift limit. Its Hardy--Rellich input is Ciatti--Cowling--Ricci, [*Hardy and uncertainty inequalities on stratified Lie groups*, arXiv:1308.2373v1, Theorem A and Corollary 3.2](https://arxiv.org/html/1308.2373v1), with $p=2$, order $2<Q/p=5/2$, original $L$ and homogeneous norm $\rho$; extension to $D(L)$ is (102.6). The localized compactness is the delivered (105.8)--(105.12). Its free kernel input is Krötz--Thangavelu--Xu, [*The heat kernel transform for the Heisenberg group*, arXiv:math/0401243v2, (4.1.2)](https://arxiv.org/html/math/0401243v2), at $n=1$, after the Jacobian-one shear and multiplication by the independent original $z$ Gaussian. This gives the original $t^{-5/2}$ diagonal. The summable zero-frequency inverse bound (105.9) uses homogeneous dimension $5>4$.

The joint spectral support (105.4) gives $A_\sigma\ge aL$ in the commuting calculus and $\ker L=\{0\}$. Hence for every fixed $z\in\mathcal H$,

$$
\|rQ_{\sigma,r}z\|_2
 \le\|r(aL+r)^{-1}z\|_2\longrightarrow0
 \quad(r\downarrow0),
\tag{114.4}
$$

uniformly in $\sigma$. Put $J_{\sigma,r}=I-rQ_{\sigma,r}$, a contraction. The exact bounded compositions

$$
Q_{\sigma,r}m=J_{\sigma,r}(A_\sigma^{-1}m),\qquad
D_wQ_{\sigma,r}m=J_{\sigma,r}(T_\sigma m)
\tag{114.5}
$$

therefore converge in norm, jointly as $\sigma\downarrow2$, $r\downarrow0$, to $A_2^{-1}m$ and $T_2m$, respectively. Indeed (114.3) handles the varying compact factor, while (114.4) and a finite net in the image of its limiting compact unit ball handle the other factor. All these compositions have their actual domains by (105.6)--(105.7); no everywhere bounded unweighted $A_\sigma^{-1}$ is used.

Now choose arbitrary $\sigma_n>2$ tending to $2$, $r_n>0$ tending to zero and $\|f_n\|_2\le1$. Write $\epsilon_n=\sigma_n-2$ and

$$
\begin{gathered}
u_n=r_nR_{\sigma_n,r_n}f_n,\qquad
h_n=H_{\sigma_n}u_n=r_n(f_n-u_n),\\
\|u_n\|_2\le1,\qquad \|h_n\|_2\le r_n,\qquad
q_{\sigma_n}[u_n]\le r_n/4,\qquad
u_n=(H_{\sigma_n}+1)^{-1}(u_n+h_n).
\end{gathered}
\tag{114.6}
$$

These are nonnegative spectral-calculus identities and bounds; the energy bound uses $\sup_{x\ge0}r_n^2x/(x+r_n)^2=r_n/4$. We may assume $r_n\le1$. The last identity makes $u_n$ a unit-shift response with inputs bounded by $2$. Lemma 113.3, applied at that fixed shift and with amplitude scaling, thus makes $mu_n$ relatively compact in $L^2$ for every bounded compactly supported $m$. Its forced local bound also bounds $X_iu_n$ in $L^2$ on every fixed compact punctured set. Lemma 113.2, with $N=B_0=1$, supplies

$$
\|\langle D_w\rangle^{\epsilon_n}u_n\|_2=O(1).
\tag{114.7}
$$

In particular this use of source tightness requires neither a variable-shift version of Lemma 113.3 nor a uniform global bound for the separate kinetic terms.

Fix a real $\chi\in C_c^\infty(G)$ equal to one near $e$, and set $\psi=1-\chi$. Apply precisely the central commutator construction (105.14)--(105.17) to $u_n$, using (114.7). It gives

$$
\begin{gathered}
[|D_w|^{\sigma_n},\chi]u_n=D_wp_n+k_n,\qquad
p_n=-i\sigma_n(\partial_w\chi)|D_w|^{\epsilon_n}u_n,\\
b_n=-a(L\chi)u_n+2a\sum_i(X_i\chi)(X_iu_n),\qquad
F_n=g_{\sigma_n}\Gamma\psi u_n+b_n-\eta k_n.
\end{gathered}
\tag{114.8}
$$

Here $p_n,b_n$ are bounded $L^2$ sequences supported in fixed compact sets. The entire central-line remainder satisfies the weighted bound (105.17). Consequently

$$
\sup_n\bigl(\|F_n\|_2+\|\rho^2F_n\|_2\bigr)<\infty,
\qquad
\lim_{R\to\infty}\sup_n
 \|\mathbf1_{\{\rho>R\}}\rho^2F_n\|_2=0.
\tag{114.9}
$$

For the potential term this follows directly from $\|u_n\|_2\le1$, boundedness of $\Gamma\psi$, $g_{\sigma_n}\to g_c$, and
$\|\mathbf1_{\{\rho>R\}}\rho^2\Gamma\psi u_n\|_2\le B_\Gamma/R$ for large $R$. For $b_n$ use its compact support and the punctured derivative bound following (114.6). For $k_n$, its horizontal support is fixed; if $\operatorname{supp}\chi\subset K_\xi\times[-J,J]$, then off $|w|\le2J$ the bound is
$|k_n(\xi,w)|\le C|w|^{-1-\sigma_n}\int_{-J}^J|\chi u_n(\xi,s)|ds$.
The original relation $\rho^4\le C(1+|w|^2)$ on that horizontal support and Cauchy--Schwarz give the uniform weighted tail of (105.17). Thus (114.9) retains the whole central line, including the nonlocal commutator tail.

The same legal free-form tests as in (113.19), now with forcing $r_nf_n$, yield the actual $L^2$ identity

$$
\begin{aligned}
y_n:=C_{\sigma_n,r_n}f_n
 &=u_n-r_nQ_{\sigma_n,r_n}f_n\\
 &=\chi u_n-r_nQ_{\sigma_n,r_n}\chi f_n
       +Q_{\sigma_n,r_n}F_n
       -\eta D_wQ_{\sigma_n,r_n}p_n.
\end{aligned}
\tag{114.10}
$$

Indeed localization gives $(A_{\sigma_n}+r_n)\psi u_n=r_n\psi f_n+F_n-\eta D_wp_n$ as a free-form identity. The horizontal product rule and central multiplier bounds preserve $\mathcal E_{\sigma_n}$ under $\psi$. The displayed right side is continuous on that domain, since $\|D_wv\|_2^2\le\|v\|_2^2+D_{\sigma_n}[v]$. Testing against $Q_{\sigma_n,r_n}z$ for arbitrary $z\in\mathcal H$ proves (114.10). This applies no zero inverse to an unspecified distribution and assumes no separate $L^2$ integrability of $\Gamma u_n$ at $e$.

Every term on the last line of (114.10) is relatively compact. The first is covered by (114.6). The second tends to zero in norm by (114.3), since $\rho^2\chi$ is bounded and $r_n\to0$. The last is covered by (114.5) and the fixed compact support of $p_n$. For the third put $m_R=\mathbf1_{\{\rho\le R\}}$. The sequence $Q_{\sigma_n,r_n}m_RF_n$ is relatively compact by (114.5), whereas

$$
\|Q_{\sigma_n,r_n}(1-m_R)F_n\|_2
 \le\frac{h_2}{a}\|\rho^2(1-m_R)F_n\|_2
\tag{114.11}
$$

vanishes uniformly as $R\to\infty$. Finite compact approximations therefore make $\{y_n\}$ relatively compact. This is compactness of the relative correction on bounded inputs; the free normalized responses themselves need not be relatively compact.

Extract $f_n\rightharpoonup f$ and a subsequence $y_n\to y$ strongly. By self-adjointness of $Q_{\sigma_n,r_n}$ and (114.4), $r_nQ_{\sigma_n,r_n}f_n\rightharpoonup0$, so $u_n\rightharpoonup y$. For every $\phi\in\mathcal D_0$, (112.19) gives $\phi\in D(H_{\sigma_n})$ and $H_{\sigma_n}\phi\to S\phi$. Thus

$$
\langle S\phi,y\rangle
 =\lim_n\langle H_{\sigma_n}\phi,u_n\rangle
 =\lim_n\langle\phi,h_n\rangle=0.
\tag{114.12}
$$

By the definition of the adjoint, $y\in\ker S^*=\mathbb Cw$. The actual zero projections fix its coefficient: $P_{\sigma_n}u_n=P_{\sigma_n}f_n$, while $P_{\sigma_n}\to P$ in norm, $P$ is finite rank, and $r_nQ_{\sigma_n,r_n}f_n\rightharpoonup0$. Hence

$$
Py=\lim_nP_{\sigma_n}y_n
   =\lim_nP_{\sigma_n}f_n=Pf,
\qquad y=Pf.
\tag{114.13}
$$

It follows that $y_n-P_{\sigma_n}f_n\to0$ along this subsequence. If the first limit in (114.2) failed, choose independent sequences $\sigma_n\downarrow2$, $r_n\downarrow0$ and unit-ball inputs on which its norm stays bounded below. The compactness and identification just proved give a contradictory subsequence. This proves the joint operator-norm statement for the entire input ball.

For the endpoint take any $r_j\downarrow0$. For each fixed $r_j$, Theorem 113.4, (113.16) and (111.29) allow a choice $2<\sigma_j<2+1/j$ so close to $2$ that

$$
\|(C_{\sigma_j,r_j}-P_{\sigma_j})
       -(C_{{\rm end},r_j}-P)\|<1/j.
\tag{114.14}
$$

The joint limit already proved applies to these independent parameters. The second limit in (114.2) follows. This argument uses the actual selector (112.5), including its zero eigenspace, throughout. $\square$

**Theorem 114.3 (full-unit-input heat convergence for every unbounded time interval).** For each fixed original $a,\eta>0$ and each $t_0>0$,

$$
\lim_{\sigma\downarrow2}\ \sup_{t\ge t_0}
 \|e^{-tH_\sigma}-e^{-tH_{\rm end}}\|_{\mathcal H\to\mathcal H}=0.
\tag{114.15}
$$

The inputs may be arbitrary complex unit vectors depending on both $\sigma$ and $t$. No positive interacting spectral gap, spectral restriction on the inputs, modified coupling or change of clock is assumed.

**Proof.** We first pass from the relative threshold limit to the large-time relative heat response. This is a spectral-calculus consequence of (114.2). For an integer $m\ge1$ set

$$
\alpha_m=\sup_{x\ge0}|(1+x/m)^{-m}-e^{-x}|\longrightarrow0.
\tag{114.16}
$$

Uniform convergence on each compact $x$ interval follows from the logarithm expansion. On $x\ge M$, monotonicity bounds the difference by $(1+M/m)^{-m}+e^{-M}$; first let $m\to\infty$ and then $M\to\infty$. This proves the displayed uniform scalar limit.

For either pair $(H,A,P_H)=(H_\sigma,A_\sigma,P_\sigma)$ or $(H_{\rm end},A_2,P)$, put $r=m/t$, $B_H=r(H+r)^{-1}$ and $B_A=r(A+r)^{-1}$. Nonnegativity makes $B_H-P_H$ and $B_A$ contractions; $B_HP_H=P_H$ gives $(B_H-P_H)^m=B_H^m-P_H$. Telescoping the difference of the two $m$th powers, without assuming that they commute, yields

$$
\|e^{-tH}-e^{-tA}-P_H\|
 \le2\alpha_m+m\|r((H+r)^{-1}-(A+r)^{-1})-P_H\|.
\tag{114.17}
$$

For fixed $m$, Theorem 114.2 controls every $0<r\le m/T$ once $T$ is large. After letting $m\to\infty$ this proves

$$
\begin{gathered}
\lim_{T\to\infty}\limsup_{\sigma\downarrow2}
 \sup_{t\ge T}\|e^{-tH_\sigma}-e^{-tA_\sigma}-P_\sigma\|=0,\\
\lim_{T\to\infty}\sup_{t\ge T}
 \|e^{-tH_{\rm end}}-e^{-tA_2}-P\|=0.
\end{gathered}
\tag{114.18}
$$

The independent joint quantifiers in (114.2) are used before this last scalar approximation limit.

The original free operators can be compared on the same entire time tail. Their actual joint variables obey $\ell\ge|\lambda|$ by (105.4). If $|\lambda|<1$ and $\sigma>2$, then $\big||\lambda|^\sigma-|\lambda|^2\big|\le|\lambda|^2$. The scalar mean value bound therefore gives

$$
|e^{-t(a\ell+\eta|\lambda|^\sigma)}
       -e^{-t(a\ell+\eta|\lambda|^2)}|
 \le\eta t\ell^2e^{-at\ell}
 \le\frac{4\eta}{e^2a^2t}.
\tag{114.19}
$$

If $|\lambda|\ge1$, each exponential is at most $e^{-at}$ on this same joint support. The spectral theorem gives the bound, uniform in all $\sigma>2$,

$$
\|e^{-tA_\sigma}-e^{-tA_2}\|
 \le\frac{4\eta}{e^2a^2t}+2e^{-at}.
\tag{114.20}
$$

The split at $|\lambda|=1$ uses the fixed original central units. Combining (114.18), (114.20) and $\|P_\sigma-P\|\to0$ proves

$$
\lim_{T\to\infty}\limsup_{\sigma\downarrow2}
 \sup_{t\ge T}\|e^{-tH_\sigma}-e^{-tH_{\rm end}}\|=0.
\tag{114.21}
$$

For completeness the bounded-time portion is supplied by the existing norm resolvents, rather than a new threshold estimate. Theorem 113.4 and the norm case of Teschl, [*Mathematical Methods in Quantum Mechanics*, authorized online edition, Theorem 6.31](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf), give norm convergence at each fixed $t>0$. The operators are self-adjoint on the same $\mathcal H$, have spectra in $[0,\infty)$, and the continuous extension $x\mapsto e^{-t|x|}$ has equal limits zero at both infinities, exactly as required there. Equivalently apply continuous calculus on $[0,1]$ to the norm-convergent $(H_\sigma+1)^{-1}$, with the function $b_t(y)=e^{-t(y^{-1}-1)}$ for $y>0$ and $b_t(0)=0$. For any nonnegative self-adjoint $K$ and $s,t\ge t_0$,

$$
\|e^{-tK}-e^{-sK}\|
 \le |t-s|\sup_{x\ge0}xe^{-t_0x}
 =\frac{|t-s|}{e t_0}.
\tag{114.22}
$$

A finite time net therefore makes the convergence uniform on every $[t_0,T]$. Together with (114.21) this proves (114.15) on the full original half-line. $\square$

## 追加锚（本行以下为增补区）


## 115. Positivity and the full ground-state form of the actual endpoint

**Definition 115.1 (the unchanged endpoint and its positive cone).** Retain exactly the group, product, source, Haar measure, clock and units of Definition 114.1. Thus

$$
\begin{gathered}
G=H^1\times\mathbb R,\qquad
p p'=(x+x',y+y',z+z',w+w'+xy'),\qquad
d\mu=dx\,dy\,dz\,dw,\\
X_1=\partial_x,\qquad X_2=\partial_y+x\partial_w,\qquad
X_3=\partial_z,\qquad L=-\sum_{i=1}^3X_i^2,\\
L\Gamma=\delta_e,\qquad
S=(aL+\eta D_w^2-g_c\Gamma)|_{\mathcal D_0},\qquad
g_c=16\sqrt{a\eta},\qquad a,\eta>0,\\
M=G\setminus\{e\},\qquad
\mathcal D_0=C_c^\infty(M;\mathbb C),\qquad
\mathcal H_+=\{f\in L^2(G,d\mu;\mathbb R):f\ge0\text{ a.e.}\}.
\end{gathered}
\tag{115.1}
$$

Here $\Gamma$ remains the original positive homogeneous degree-$-3$ unit-source Green field of $L$. Write $F$ for the Friedrichs operator of Theorem 87.4, with form $(\overline q_c,\mathcal Q_c)$, and let

$$
\begin{gathered}
h=\frac{w_*}{\|w_*\|_2},\qquad
c_h=C(h)=\|w_*\|_2^{-1}>0,\qquad
\rho=\frac{A(h)}{C(h)},\\
H=H_{\rm end},\qquad
D(H)=\{u\in D(S^*):A(u)=\rho C(u)\},\qquad Hu=S^*u.
\end{gathered}
\tag{115.2}
$$

The vector $w_*$ is exactly (110.2); $A,C$, their source expansion and their boundary pairing are exactly (112.2)--(112.3). In particular $\ker F=\{0\}$, $h\notin\mathcal Q_c$, $\ker H=\mathbb Ch$, and $\mathcal D_0+\mathbb Ch$ is the supplied graph core of this actual $H$. The normalization in (115.2) chooses the coefficient-positive representative of the actual zero line, without imposing a condition on any finite-$\sigma$ state. Denote the closed form of $H$ by $q_H$, and set

$$
\mathcal C[v]=a\sum_{i=1}^3|X_iv|^2+\eta|\partial_wv|^2.
\tag{115.3}
$$

**Theorem 115.2 (the actual zero line is positive, and the actual heat preserves the original cone).** For every fixed original $a,\eta>0$, the vector $h$ of (115.2) has a real representative smooth and strictly positive on $M$, hence strictly positive $\mu$-a.e. For every $r>0$ put

$$
G_r=(F+r)^{-1},\qquad n_r=h-rG_rh,\qquad d_r=\langle h,n_r\rangle.
\tag{115.4}
$$

Then $n_r\in\mathcal H_+\setminus\{0\}$, $d_r>0$, and the full original-space resolvent is

$$
(H+r)^{-1}
 =G_r+\frac{|n_r\rangle\langle n_r|}{r d_r}.
\tag{115.5}
$$

Consequently

$$
e^{-tH}\mathcal H_+\subset\mathcal H_+
\qquad\text{for every }t\ge0.
\tag{115.6}
$$

These are statements about selector (112.5), on the entire original $L^2$, including its singular zero state.

**Proof.** The differential expression and the punctured core are invariant under complex conjugation. Uniqueness of the coefficient-one vector in Theorems 109.2 and 110.2 therefore gives $\overline{w_*}=w_*$: its conjugate is another maximal zero vector with source coefficient one. Thus $h$ is real and $C(h)=c_h>0$. Local elliptic regularity gives its smooth representative on $M$; no sign has yet been inferred.

First the Friedrichs resolvent preserves $\mathcal H_+$. On a punctured compact support, the weak modulus inequality for the first derivatives gives
$\overline q_c[|u|]\le\overline q_c[u]$ for $u\in\mathcal D_0$. The absolute value belongs to $\mathcal E_2\subset\mathcal Q_c$; smooth local approximation is legitimate because $\Gamma$ and the kinetic coefficients are bounded on that support. For $u\in\mathcal Q_c$, approximate by $u_j\in\mathcal D_0$. The vectors $|u_j|$ converge to $|u|$ in $L^2$ and have bounded closed-form norm. Weak compactness in $\mathcal Q_c$ and lower semicontinuity extend the same inequality to all of $\mathcal Q_c$. For real $f\ge0$, replacing a vector by its absolute value cannot increase

$$
\overline q_c[v]+r\|v\|_2^2-2\operatorname{Re}\langle f,v\rangle.
\tag{115.7}
$$

The unique minimizer is $y=G_rf$, so $y\ge0$. This uses the closed critical form, without subtracting possibly infinite separate kinetic and potential integrals.

For this $y\in D(F)$, (112.2)--(112.3) give $C(y)=0$ and
$H_y=A(y)e_0+Z_y$, where $e^{\tau/8}Z_y\in H^1$ on the positive cylinder end. The coordinate multiplier defining $H_y$ is positive, and $e_0$ in (109.3) is real and strictly positive. Thus
$\langle e_0,H_y(\tau)\rangle\ge0$ for almost every sufficiently large $\tau$. Along a sequence of such slices the remainder tends to zero in angular $L^2$, so

$$
A(G_rf)\ge0\qquad(f\in\mathcal H_+).
\tag{115.8}
$$

Only the supplied weighted remainder is used; no pointwise source estimate is required.

The exact original boundary pairing, with first slot $h$ and second slot $y$, now fixes the sign:

$$
\begin{aligned}
\langle n_r,f\rangle
 &=\langle h,(I-rG_r)f\rangle
  =\langle h,Fy\rangle\\
 &=a c_h A(y)\ge0\qquad(f\in\mathcal H_+).
\end{aligned}
\tag{115.9}
$$

Here $S^*h=0$ and $C(y)=0$ have been used in (112.3), with its stated antilinear-first-slot convention. Since the real positive cone is self-dual, (115.9) proves $n_r\ge0$. The spectral theorem for the supplied nonnegative $F$ with zero kernel gives $rG_rh\to0$ as $r\downarrow0$. Hence $n_r\to h$ in $L^2$, and the cone is closed, so $h\ge0$ and $h\ne0$.

On every relatively compact coordinate region in $M$, the principal matrix of the original equation is smooth and uniformly positive: its quadratic symbol is

$$
a\bigl(p_x^2+(p_y+xp_w)^2+p_z^2\bigr)+\eta p_w^2.
\tag{115.10}
$$

The potential $-g_c\Gamma$ is smooth there. The local elliptic Harnack principle applies to the nonnegative solution $S^*h=0$. Its local-to-global chain on connected $M$ makes a nonzero such solution strictly positive everywhere on $M$. These are precisely the local divergence-form ellipticity and locally bounded-potential hypotheses used for positive solutions in Pinchover--Tintarev, [*A ground state alternative for singular Schrödinger operators*, arXiv:math/0411658v1, §1, (1.1)--(1.4) and §2](https://arxiv.org/html/math/0411658v1), and the Harnack implication discussed by Lenz--Stollmann--Veselić, [*The Allegretto--Piepenbrink theorem for strongly local Dirichlet forms*, arXiv:0811.2135v1, §3](https://arxiv.org/html/0811.2135v1). They are used on $M$ only. Neither a global potential-form bound at $e$ nor a Harnack estimate across $e$ is asserted.

To verify (115.5) on its full domain, note first that
$(S^*+r)n_r=0$. Conversely the supplied decomposition $D(S^*)=D(F)\dotplus\mathbb Ch$ shows that every vector in $\ker(S^*+r)$ equals a multiple of $n_r$: for $u=y+ch$, its equation is $(F+r)y=-rc h$. Moreover, if $E_F$ is the spectral resolution of $F$, then

$$
d_r=\int_{[0,\infty)}\frac{\lambda}{\lambda+r}
                  \,d\langle h,E_F(\lambda)h\rangle>0.
\tag{115.11}
$$

The strict inequality follows from $\|h\|_2=1$ and $\ker F=\{0\}$. Thus $n_r\ne0$. For any complex $f\in\mathcal H$, every maximal-domain solution of $(S^*+r)u=f$ is $u=G_rf+c n_r$. The actual selector in the first line of (112.5) requires

$$
0=\langle h,S^*u\rangle
  =\langle n_r,f\rangle-r c d_r,
\tag{115.12}
$$

which gives exactly (115.5). In particular this computation does not apply a zero inverse to a general forcing or substitute a Friedrichs source condition. Both terms on its right preserve the real positive cone, by (115.9) and $d_r>0$. Positivity of $e^{-tH}$ follows from the usual strong resolvent-power approximation to the nonnegative self-adjoint heat semigroup, including the identity at $t=0$. This final semigroup step is standard functional calculus; the source-specific content is (115.8)--(115.12) for the actual original boundary pairing. $\square$

**Theorem 115.3 (full-domain correspondence and conservative strongly local dynamics).** Use the positive representative $h$ from Theorem 115.2 and set

$$
\begin{gathered}
dm_h=h^2d\mu,\qquad m_h(G)=1,\qquad
U_h:L^2(G,dm_h;\mathbb C)\longrightarrow\mathcal H,
\quad U_hv=hv,\\
K=U_h^{-1}HU_h,\qquad T_t=U_h^{-1}e^{-tH}U_h.
\end{gathered}
\tag{115.13}
$$

Define $\mathscr V_0$ as the closure of $C_c^\infty(M;\mathbb C)$ in the norm

$$
\|v\|_{h,1}^2=\int_G|v|^2dm_h+\int_M\mathcal C[v]dm_h.
\tag{115.14}
$$

Then the entire closed form of $K$ has exactly the domain and values

$$
\begin{gathered}
\mathscr V=\mathscr V_0\dotplus\mathbb C1,
\qquad U_h\mathscr V_0=\mathcal Q_c,
\qquad D(H^{1/2})=\mathcal Q_c\dotplus\mathbb Ch,\\
\mathscr E[v,z]=\int_M\left(
 a\sum_{i=1}^3\overline{X_iv}X_iz
 +\eta\overline{\partial_wv}\partial_wz\right)dm_h,
\qquad v,z\in\mathscr V,\\
q_H[y+ch]=\overline q_c[y]
\quad(y\in\mathcal Q_c,\ c\in\mathbb C).
\end{gathered}
\tag{115.15}
$$

The derivatives in the integral are the local weak derivatives on $M$, with their global weighted $L^2$ limits. The form $(\mathscr E,\mathscr V)$ is a regular strongly local Dirichlet form on the original space $G$ with measure $m_h$. Its semigroup is conservative:

$$
T_t1=1\qquad(t\ge0).
\tag{115.16}
$$

In particular it is a Markov contraction on real bounded functions, and $m_h$ is an invariant probability measure. The full operator domain is

$$
D(K)=\{v\in\mathscr V:hv\in D(S^*),\ A(hv)=\rho C(hv)\},
\qquad Kv=h^{-1}S^*(hv).
\tag{115.17}
$$

**Proof.** Because $h>0$ a.e., (115.13) is a unitary map, and multiplication or division by $h$ maps $C_c^\infty(M)$ bijectively to itself. On a compact punctured support the usual ground-state identity gives

$$
q_c[h\psi]=\int_Mh^2\mathcal C[\psi]d\mu,
\qquad \psi\in C_c^\infty(M;\mathbb C).
\tag{115.18}
$$

For its direct verification expand the derivatives of $h\psi$ and test the original weak equation for $h$ against $h|\psi|^2$. The derivatives of the real $h$ and the real potential cancel; the remaining terms are those on the right. All integrals are finite on this support. For real factors this is exactly Pinchover--Tintarev, Lemma 2.4, (2.6), with their solution $\psi$ equal to the present $h$, their multiplier $v$ equal to the present test, their $A$ given by (115.10), and their $V=-g_c\Gamma$ on a bounded punctured region. Real and imaginary parts and polarization give the complex identity. Equivalently it is Lenz--Stollmann--Veselić, Theorem 2.3 with $E=0$, $\Phi=h$, and $\nu=-g_c\Gamma\,d\mu$, again only locally on $M$, where $h,h^{-1}$ are smooth and locally bounded. This established identity is an intermediate step, not an identification of endpoint domains by itself.

The domain identification instead uses the actual graph core in (112.4)--(112.5). On it $Hh=0$, and hence

$$
q_H[\phi+ch]=q_c[\phi]
\qquad(\phi\in\mathcal D_0,\ c\in\mathbb C).
\tag{115.19}
$$

A graph core of a nonnegative self-adjoint operator is a form core: spectral truncation first approximates every form-domain vector by operator-domain vectors, and graph approximation then implies form approximation. Consequently the closed form of $K$ is exactly the completion of
$C_c^\infty(M)+\mathbb C1$ with the integral energy in (115.18), and not merely a form agreeing with it on punctured tests. Its completion of the smaller core $C_c^\infty(M)$ is isometrically $U_h^{-1}\mathcal Q_c$, by (115.18) and the definition of the Friedrichs form. This is a closed subspace of the complete form space of $K$. Adding the finite-dimensional subspace $\mathbb C1$ gives another closed subspace; density of the larger core makes it the whole space. The sum is direct because $h\notin\mathcal Q_c$. This proves the domain equalities in (115.15).

For any Cauchy sequence in this form core, its derivatives are Cauchy in $L^2(m_h)$. On each compact subset of $M$, positivity and smoothness of $h$ make the weighted norm equivalent to the ordinary local $H^1$ norm. The limits are therefore the distributional derivatives of the actual $L^2(m_h)$ limit. Exhausting $M$ proves exactly the integral formula in (115.15), with no additional source energy. In particular the constant has zero energy, and polarization gives $q_H[y+ch]=\overline q_c[y]$. Formula (115.17) now follows from unitary conjugation of the actual operator selector, rather than from a condition imposed on smooth tests.

This also records the singular source component at form level. Every $v\in\mathscr V$ has a unique decomposition $v=v_0+c$, with $v_0\in\mathscr V_0$, and the coefficient $c$ is a continuous linear functional in the full form norm. It vanishes on the closed punctured form core and takes value one at the constant. If $hv\in D(H)$, the maximal-domain decomposition and $\mathcal Q_c\cap D(S^*)=D(F)$ give

$$
c=\frac{C(hv)}{C(h)}.
\tag{115.20}
$$

Thus deleting $\mathbb C1$ would give the Friedrichs form, not the actual endpoint. No pointwise limit of an arbitrary form-domain vector at $e$ is needed for this source coordinate, and no separate kinetic or potential integral of $hv$ is asserted finite.

For the Markov property, let $N:\mathbb R\to\mathbb R$ satisfy $N(0)=0$ and $|N(s)-N(t)|\le|s-t|$. If $v=c+\psi$ is in the real form core, then $N(v)-N(c)$ is a compactly supported $H^1$ function on $M$. On its compact support, local smooth approximation and the equivalence of weighted and unweighted $H^1$ norms put it in $\mathscr V_0$. The weak chain rule gives

$$
N(v)\in\mathscr V,\qquad
\mathscr E[N(v)]\le\mathscr E[v].
\tag{115.21}
$$

For general real $v\in\mathscr V$, choose core approximants. Their contractions converge in $L^2(m_h)$ by the Lipschitz bound, and have bounded form norms by (115.21). Weak compactness in the closed form and lower semicontinuity extend (115.21) to $v$. This is the normal-contraction criterion for a Dirichlet form, used on the real form and then complexified, as in Lenz--Stollmann--Veselić, §1. All source coefficients $c$ are retained in this argument; contractions have not been tested only on a vanishing-source subdomain.

We verify regularity on $G$, including the point $e$. The measure $m_h$ is a finite Radon measure with full support and no atom at $e$. Use the original smooth Carnot cutoffs $\chi_R$ of (108.7), equal to one on growing balls and satisfying

$$
|X_i\chi_R|\le C/R,\qquad
|\partial_w\chi_R|\le C/R^2.
\tag{115.22}
$$

Fix any $\chi\in C_c^\infty(G;\mathbb R)$ equal to one near $e$. The vectors $\chi_R(1-\chi)$ are punctured compact tests and converge to $1-\chi$ in (115.14): the $L^2(m_h)$ tail vanishes since $m_h(G)=1$, the derivative of $\chi$ lies in a fixed compact set where $\chi_R=1$ for large $R$, and the remaining derivative cost is bounded by $C(R^{-2}+R^{-4})m_h(G)$. Thus $1-\chi\in\mathscr V_0$ and $\chi\in\mathscr V$. Applying this to $\chi_R$ itself gives

$$
\|1-\chi_R\|_{L^2(m_h)}\longrightarrow0,
\qquad
\mathscr E[1-\chi_R]=\mathscr E[\chi_R]
 \le C(R^{-2}+R^{-4})\longrightarrow0.
\tag{115.23}
$$

It follows that $\mathbb C\chi+C_c^\infty(M)$, whose members are continuous and compactly supported on $G$, is form dense: approximate the constant by $\chi_R$, and observe that $\chi_R-\chi$ is a punctured compact test. It is also uniformly dense in $C_c(G)$, by ordinary smooth approximation followed by making a smooth approximant constant in a sufficiently small source neighborhood. Uniform continuity controls that last change, and every such function has the form $c\chi+\psi$ with $\psi\in C_c^\infty(M)$. This proves regularity without treating $e$ as a discarded boundary.

Strong locality follows from the full integral formula (115.15). If $v$ is constant on a neighborhood of the compact support of $z$, its local weak gradient vanishes there, and that of $z$ vanishes off its support. The energy pairing is zero. The point $e$ contributes no extra term: the gradient completion already proved the entire energy to be the displayed integral, with $m_h(\{e\})=0$. Finally $1\in\mathscr V$ has zero energy, so it lies in $D(K)$ with $K1=0$. Therefore $T_t1=1$. The standard Dirichlet-form semigroup correspondence gives positivity and the Markov contractions; symmetry and $T_t1=1$ give invariance of $m_h$. These standard consequences consume the full-domain source identification above. $\square$

**Definition 115.4 (supplier correspondence and the remaining native bridge).** The source-specific deductions in this section are the sign of the original boundary functional in (115.9), its actual resolvent (115.5), and the closure (115.15) retaining the source coefficient (115.20). Their suppliers are the unchanged actual field of §§82--87, the Friedrichs completion and zero kernel of Theorem 87.4, the full source expansion of Theorems 109.2 and 112.2, the coefficient-one global vector of Theorem 110.2, and the actual graph core and selector of (112.4)--(112.5). The actual zero projections and convergence of §§111--114 are retained; no convergence theorem or spectral gap is inferred anew from positivity. The ground-state identity and Dirichlet-form consequences retain the precise primary-source correspondences in the proofs. They are established methods, while their application to this particular source coefficient and non-Friedrichs endpoint is a repository deduction, without a worldwide-priority assertion. The positive-lower-bound domain formulas in Ashbaugh et al., [*A Survey on the Krein--von Neumann Extension*, arXiv:1203.5713v1, Theorem 2.1, (2.9)--(2.11)](https://arxiv.org/html/1203.5713v1), require $S\ge\varepsilon I$, $\varepsilon>0$; that hypothesis is absent here and those formulas are not used.

The resulting dynamics has, away from $e$, Markov generator

$$
-Kv=a\sum_{i=1}^3X_i^2v+\eta\partial_w^2v
 +2a\sum_{i=1}^3(X_i\log h)X_iv
 +2\eta(\partial_w\log h)\partial_wv.
\tag{115.24}
$$

Its source behavior is determined by (115.15) and (115.17), not by extending this displayed differential formula across $e$. Its principal matrix (115.10) has rank four for $\eta>0$; conjugation changes the drift, not that rank. The original horizontal distribution still has rank three, the carrier still has four coordinates and homogeneous dimension five, and none of these numbers is a derived physical spatial dimension.

A native legal transport realization of this endpoint would additionally require an actual admissible source and native evolution, a specified representation and observation map, and proofs that this same source, raw units, clock, full generator including its source domain, and observation law intertwine with that native evolution. In particular the conservative probability dynamics $T_t$ on $L^2(h^2d\mu)$, the original positive Schrödinger heat on $L^2(d\mu)$, signed or complex amplitudes, and any proposed finite positive network have different state and observation contracts until those maps are supplied. Theorems 115.2--115.3 settle the three endpoint questions for the exact original selector; they do not supply that native realization or assert positivity of any finite-$\sigma>2$ regulator. The native source/operator/readout correspondence remains unproved.

## 追加锚（本行以下为增补区）

## 116. The original source capacity, contact law and conservative continuation

**Definition 116.1 (the same source and the original clock).** Use exactly the original $G=H^1\times\mathbb R$, product, raw Haar measure, unit-source $\Gamma$, $a,\eta>0$, $g_c=16\sqrt{a\eta}$, $H=H_{\rm end}$ and selector (112.5) of Definition 115.1. Retain the coefficient-positive normalized $h$, $c_h=C(h)>0$, $\rho=A(h)/C(h)$, $F$, $G_r=(F+r)^{-1}$, $n_r=h-rG_rh$, $d_r=\langle h,n_r\rangle$, $U_h$ and $K$ of §115. Write $m=m_h=h^2\mu$, $M=G\setminus\{e\}$ and

$$
\begin{gathered}
\operatorname{tr}(v_0+c)=c
 \quad(v_0\in\mathscr V_0,\ c\in\mathbb C),\qquad
\mathscr E_r[v,z]=\mathscr E[v,z]+r\langle v,z\rangle_{L^2(m)},\\
b_r=U_h^{-1}n_r=1-rh^{-1}G_rh,\qquad r>0.
\end{gathered}
\tag{116.1}
$$

All pairings are antilinear in the first slot. Forms and operators are on the entire original complex spaces; probability statements use their real Dirichlet forms. A tilde denotes a quasi-continuous representative for $(\mathscr E,\mathscr V)$. For the compact singleton use the usual shifted capacity

$$
\operatorname{Cap}_r(\{e\})
 =\inf\{\mathscr E_r[v]:v\in\mathscr V\text{ real},
                              \ \widetilde v\ge1
                                  \text{ quasi-everywhere on }\{e\}\}.
\tag{116.2}
$$

This is the outer Dirichlet-form capacity, expressed by its quasi-continuous constraint on a compact set. Its null sets are independent of $r>0$, since the shifted form norms are equivalent. The form in (115.15) fixes its normalization; no factor $1/2$ or change of time is inserted.

**Theorem 116.2 (the source trace and its exact capacity).** The original point $e$ is nonpolar, and every $v\in\mathscr V$ satisfies

$$
\widetilde v(e)=\operatorname{tr}v,\qquad
\mathscr V_0=\{v\in\mathscr V:\widetilde v(e)=0\}.
\tag{116.3}
$$

In particular $\mathscr V_0$ is exactly the part-form domain on $M$. For every $r>0$, $b_r\in\mathscr V$ is the equilibrium potential of $\{e\}$, $0\le\widetilde b_r\le1$ quasi-everywhere, and

$$
\begin{gathered}
\operatorname{tr}b_r=1,\qquad
\mathscr E_r[b_r,v]=r d_r\,\operatorname{tr}v
                              \quad(v\in\mathscr V),\\
\operatorname{Cap}_r(\{e\})=\mathscr E_r[b_r]=r d_r,\qquad
|\widetilde v(e)|^2\le\frac{\mathscr E_r[v]}{r d_r}
                              \quad(v\in\mathscr V).
\end{gathered}
\tag{116.4}
$$

Equality in the last inequality holds exactly for complex multiples of $b_r$. The corresponding equilibrium measure is $r d_r\delta_e$, with $\delta_e$ the unit point mass at the original identity. The original boundary coefficients give the additional exact normalization

$$
\begin{gathered}
C(n_r)=c_h,\qquad
A(n_r)=\rho c_h-rA(G_rh),\qquad
d_r=a c_h A(G_rh),\\
r d_r=a c_h\bigl(\rho C(n_r)-A(n_r)\bigr).
\end{gathered}
\tag{116.5}
$$

Here $A,C$ are evaluated only on the displayed maximal-domain vectors. For $v\in D(K)$ the source value also equals $C(hv)/c_h$, as in (115.20); no such maximal-domain coefficient is assigned to a general form vector.

**Proof.** We first identify the point without assuming that a measure-zero set is polar. Theorem 115.3 supplies regularity on all of $G$, the continuous functional $\operatorname{tr}$, and the form core
$\mathcal A=\mathbb C\chi+C_c^\infty(M;\mathbb C)$, where $\chi\in C_c^\infty(G)$ equals one near $e$ and $\chi-1\in\mathscr V_0$. On this core, $\operatorname{tr}v=v(e)$.

The standard part-form theorem identifies its domain on the open set $M$ with the form-norm closure of $\mathscr V\cap C_c(M)$, and also with the vectors vanishing quasi-everywhere on $G\setminus M$. This is the part-process correspondence stated in Chen--Fukushima--Ying, [*Traces of symmetric Markov processes and their characterizations*, arXiv:math/0606784v1, §2, (2.2)--(2.3)](https://arxiv.org/pdf/math/0606784v1). The open-set part theorem itself requires regularity, not transience or a spectral gap. In the present form, every member of $\mathscr V\cap C_c(M)$ can be approximated by $C_c^\infty(M)$ in form norm: on a compact punctured neighborhood of its support, $h$ is smooth and bounded above and below by positive constants, and the principal matrix (115.10) is uniformly positive. The integral norm (115.15) is therefore equivalent there to the ordinary $H^1$ norm. A punctured smooth cutoff and local mollification give the approximation. Thus this closure is exactly $\mathscr V_0$. If $\{e\}$ were polar, the part theorem would make the same closure all of $\mathscr V$. This contradicts the closed direct sum in (115.15), since $\operatorname{tr}1=1$. Hence $\{e\}$ has positive capacity.

For $v\in\mathscr V$, take a form-convergent sequence $v_j\in\mathcal A$. The usual capacity estimate for a form-convergent sequence gives a subsequence converging quasi-everywhere to $\widetilde v$: choose a subsequence with $\|v_{j+1}-v_j\|_{\mathscr E_1}\le2^{-2j}$, where $\|u\|_{\mathscr E_1}^2=\mathscr E_1[u]$. The capacity estimate gives $\operatorname{Cap}_1(\{|\widetilde v_{j+1}-\widetilde v_j|>2^{-j}\})\le2^{-2j}$. Outside the capacity-zero limsup set the differences are eventually summable; outside the unions of the tails the convergence is uniform. This yields the quasi-continuous version of the form limit. No polar exceptional set can contain $e$. Consequently
$\widetilde v(e)=\lim_jv_j(e)=\lim_j\operatorname{tr}v_j=\operatorname{tr}v$.
This proves (116.3). It asserts a quasi-continuous value, not an ordinary limit along arbitrary points approaching $e$.

Since $G_rh\in D(F)\subset\mathcal Q_c$, (115.15) gives $b_r\in1+\mathscr V_0$. Put $y=G_rh$. The spectral resolvent equation gives $Fy=n_r$. For any $z\in\mathscr V_0$, write $w=hz\in\mathcal Q_c$. The form identity and closed-form representation for $F$ give

$$
\begin{aligned}
\mathscr E_r[b_r,z]
 &=-r\,\overline q_c[y,w]+r\langle n_r,w\rangle_{\mathcal H}\\
 &=-r\langle Fy,w\rangle_{\mathcal H}
                       +r\langle n_r,w\rangle_{\mathcal H}=0,\\
\mathscr E_r[b_r,1]&=r\langle n_r,h\rangle_{\mathcal H}=r d_r.
\end{aligned}
\tag{116.6}
$$

The identity with the constant uses $\mathscr E[b_r,1]=0$ and the reality of $d_r$. Decomposing $v$ first in $\mathscr V_0+\mathbb C1$ proves the pairing in (116.4). Decomposing instead as
$v=(\operatorname{tr}v)b_r+z$, $z\in\mathscr V_0$, proves the orthogonal identity

$$
\mathscr E_r[v]=r d_r|\operatorname{tr}v|^2+\mathscr E_r[z].
\tag{116.7}
$$

The supplied $d_r>0$ makes $b_r$ the unique minimizer among real vectors with trace one, and (116.7) makes it the unique minimizer with trace at least one. This proves the capacity, sharp inequality and equality condition. Truncation to $[0,1]$ preserves the value one at $e$ and cannot increase either energy or squared norm; uniqueness of the minimizer proves $0\le\widetilde b_r\le1$. The pairing in (116.4) identifies its equilibrium measure as $r d_r\delta_e$, and proves directly that evaluation at $e$ has finite shifted energy. These variational and equilibrium-measure identifications are the standard equilibrium construction applied to this particular form.

Finally $C(y)=0$, $C(h)=c_h$, $A(h)=\rho c_h$ and $S^*h=0$. Applying exactly (112.3) to $h,y$ gives
$\langle h,Fy\rangle=a c_h A(y)$.
Its left side is $d_r$, and the coefficients of $n_r=h-ry$ give all of (116.5). In particular $n_r$ has boundary defect
$A(n_r)-\rho C(n_r)=-r d_r/(a c_h)$; it is not a vector in the actual operator domain $D(H)$. The form argument has not imposed the selector on an equilibrium potential. $\square$

**Theorem 116.3 (contact in the original clock and the exact killed operator).** Let $Z=(Z_t,\mathbb P_x)$ be the conservative $m$-symmetric diffusion properly associated with the full form of §115. There is a properly exceptional set $N$ with $e\notin N$ on whose complement the following process statements are understood. In particular they hold for quasi-every starting point in $M$, with the source start retained. Define

$$
\tau_e=\inf\{t\ge0:Z_t=e\},\qquad
\sigma_e=\inf\{t>0:Z_t=e\},\qquad \inf\varnothing=\infty.
\tag{116.8}
$$

Then $e$ is regular for itself: $\mathbb P_e(\sigma_e=0)=1$. For every $r>0$ and $t\ge0$,

$$
\begin{gathered}
\mathbb E_x[e^{-r\tau_e};\tau_e<\infty]=\widetilde b_r(x),\\
\mathbb P_x(\tau_e>t)=P_t^0 1(x)
       =\bigl[h^{-1}e^{-tF}h\bigr](x)\quad(x\in M\setminus N),\\
P_t^0=U_h^{-1}e^{-tF}U_h,\qquad
R_r^0=U_h^{-1}G_rU_h,\qquad
\int_0^\infty e^{-rt}P_t^0 1\,dt
        =h^{-1}G_rh=\frac{1-b_r}{r}.
\end{gathered}
\tag{116.9}
$$

The first line includes $x=e$, where $\tau_e=0$ and $\widetilde b_r(e)=1$. For the killed process the source-start convention is immediate killing, so its survival is zero for $x=e$, including $t=0$; on $M$ it is one at $t=0$. The functions in the second line are taken in the part-process versions, not by assigning an ordinary value to $h(e)$. The same choice of process versions gives the formulas for all the indicated parameters. Moreover,

$$
\mathbb P_x(\tau_e<\infty)=1\qquad(x\in G\setminus N).
\tag{116.10}
$$

The entire killed form is $(\mathscr E|_{\mathscr V_0},\mathscr V_0)$ on $L^2(M,m)$, which is the same Hilbert space as $L^2(G,m)$. Its nonnegative self-adjoint operator is exactly

$$
\begin{gathered}
K^0=U_h^{-1}FU_h,\qquad
D(K^0)=\{v:hv\in D(F)\}
      =\{v:hv\in D(S^*),\ C(hv)=0\},\\
D(K)\cap\mathscr V_0
 =\{v:hv\in D(S^*),\ A(hv)=C(hv)=0\}
 =U_h^{-1}D(\overline S)
 \ \subsetneq\ D(K^0).
\end{gathered}
\tag{116.11}
$$

Thus the source-killed operator is not obtained merely by restricting $D(K)$ to its zero-source vectors while keeping both boundary equations.

**Proof.** The space $G$ is locally compact, separable and metrizable, and $m$ is a full-support Radon probability measure. Theorem 115.3 gives a regular, symmetric, strongly local Dirichlet form, hence a properly associated diffusion outside a properly exceptional set. Its lifetime is infinite quasi-everywhere: $T_t1=1$ gives the resolvent $R_r1=1/r$, whose quasi-continuous version is the constant. The process resolvent therefore gives
$\mathbb E_x\int_0^\zeta e^{-rt}dt=1/r$ quasi-everywhere, forcing $\zeta=\infty$. Since $e$ is nonpolar, it cannot be removed in the exceptional set.

For completeness the irreducibility used in the cited symmetric hitting theory holds here. A zero-energy vector has all its local weak derivatives zero on connected $M$, by $a,\eta>0$ and (115.15), so is constant $m$-a.e. An invariant measurable set for a conservative symmetric semigroup on this finite measure space has its indicator fixed by the semigroup, hence in the zero-energy kernel. Its indicator must therefore be constant almost everywhere. This excludes nontrivial invariant sets. No positive spectral gap follows.

The closed singleton is finely closed. The standard symmetric-process fact that the irregular points of a finely closed set form a polar subset is used in Chen--Fukushima--Ying, §4 preceding (4.1). Applied to $\{e\}$, its nonpolarity forces its only point to be regular for itself. Equivalently, this is the positive-capacity-singleton regularity argument in the proof of Chen's [RIMS lectures, Theorem 1.2.2](https://sites.math.washington.edu/~zchen/RIMS_lecture.pdf); only that general symmetric-form fact is used, not the Brownian model there.

The part-process theorem cited in Theorem 116.2 now says that killing $Z$ at $\tau_e$ on $M$ has form domain exactly $\mathscr V_0$. Its full energy is already (115.15), so unitary multiplication by $h$ identifies it with $(\overline q_c,\mathcal Q_c)$ and its operator with $F$. This proves the survival and resolvent assertions in (116.9), including all $t\ge0$ by the killed transition function.

The standard hitting projection theorem identifies the $r$-equilibrium potential of a closed set with its discounted hitting probability. Its projection characterization is recalled in Chen's RIMS lectures, §1.2, in the paragraph before Theorem 1.2.1 and in the proof of Theorem 1.2.3; the general hitting kernels are specified in Chen--Fukushima--Ying, §2 immediately before (2.14). Here the ambient form is $(\mathscr E,\mathscr V)$, the closed set is $\{e\}$, the part domain is $\mathscr V_0$, and the projection is in the inner product $\mathscr E_r$. The input function is $1\in\mathscr V$. Its projected remainder is exactly $b_r$, since $1-b_r\in\mathscr V_0$ and (116.6) is the required orthogonality. This verifies the full parameter correspondence and proves the first line of (116.9). Alternatively, integrating the killed survival gives
$\mathbb E_x\int_0^{\tau_e}e^{-rt}dt=R_r^0 1(x)$ and the same identity follows from $1-rR_r^0 1=b_r$. Quasi-continuous versions give these statements quasi-everywhere, including the regular source. One may fix common versions using the diffusion transition functions and its hitting time; rational parameters followed by their right-continuity in time and continuity of Laplace transforms retain all $t$ and $r$, rather than asserting identities only for separately chosen almost-everywhere representatives.

An $L^2$ limit alone would not establish (116.10) for the legitimate starting points. Here there is a stronger limit. Let $\nu(B)=\langle h,E_F(B)h\rangle$, a probability measure with $\nu(\{0\})=0$. The exact form correspondence gives

$$
\begin{aligned}
\|1-b_r\|_{L^2(m)}^2
 &=\int_{[0,\infty)}
          \frac{r^2}{(\lambda+r)^2}\,d\nu(\lambda)\longrightarrow0,\\
\mathscr E[1-b_r]
 &=\int_{[0,\infty)}
          \frac{r^2\lambda}{(\lambda+r)^2}\,d\nu(\lambda)
       \le\frac r4\longrightarrow0.
\end{aligned}
\tag{116.12}
$$

Dominated convergence proves the first limit using $\ker F=\{0\}$; the second uses the maximum of the displayed multiplier. Thus $b_r\to1$ in the full form norm as $r\downarrow0$. Choose a decreasing sequence $r_j\downarrow0$ and a subsequence converging quasi-everywhere. The hitting representation and monotone convergence give
$\widetilde b_{r_j}(x)\uparrow\mathbb P_x(\tau_e<\infty)$; the form-norm subsequence forces this limit to be one quasi-everywhere. Absorb the resulting polar set into a properly exceptional $N$, which still cannot contain $e$. This proves (116.10).

The operator-domain formulas in (116.11) follow from $U_h\mathscr V_0=\mathcal Q_c$, (112.3) and the actual selector (115.17). The strict inclusion is witnessed by
$v=h^{-1}G_rh$: its product by $h$ lies in $D(F)$, while
$A(G_rh)=d_r/(a c_h)>0$ and $C(G_rh)=0$.
It is therefore in $D(K^0)$ and outside $D(K)$. Restricting the actual operator to the two zero coefficients gives the transformed closed minimal operator, rather than the self-adjoint part operator. $\square$

**Theorem 116.4 (the source-start response and zero residence).** On the entire complex $L^2(G,m)$, let $R_r=(K+r)^{-1}$. For every $r>0$,

$$
\begin{gathered}
R_r=R_r^0+\frac{|b_r\rangle\langle b_r|}{r d_r},\qquad
\widetilde{R_rf}(e)=\frac{\langle b_r,f\rangle_{L^2(m)}}{r d_r}
                                  \quad(f\in L^2(G,m;\mathbb C)),\\
\frac{C((H+r)^{-1}\phi)}{c_h}
   =\frac{\langle n_r,\phi\rangle_{\mathcal H}}{r d_r}
                                  \quad(\phi\in\mathcal H).
\end{gathered}
\tag{116.13}
$$

For bounded complex Borel $f$, the exact source-start occupation response is

$$
\mathbb E_e\int_0^\infty e^{-rt}f(Z_t)\,dt
 =\frac1{r d_r}\int_G b_r f\,dm,\qquad
R_r(e,dy)=\frac{b_r(y)}{r d_r}\,m(dy).
\tag{116.14}
$$

The full process continues conservatively after source contact. For every legitimate starting point, including $e$, it has zero ordinary residence time there:

$$
\mathbb P_x\left(
  \int_0^T\mathbf1_{\{e\}}(Z_s)\,ds=0
                   \text{ for every finite }T\ge0\right)=1
                 \quad(x\in G\setminus N).
\tag{116.15}
$$

In contrast with positive shifted capacity, the zero-order variational infimum is zero, even with compactly supported admissible vectors:

$$
\begin{gathered}
\inf\{\mathscr E[v]:v\in\mathscr V\text{ real},
                                      \widetilde v(e)\ge1\}=0,\\
\inf\{\mathscr E[v]:v\in\mathscr V\cap C_c(G;\mathbb R),
                                      v(e)\ge1\}=0,\\
0<\operatorname{Cap}_r(\{e\})=r d_r<r,\qquad
\lim_{r\downarrow0}
          \frac{\operatorname{Cap}_r(\{e\})}{r}=1.
\end{gathered}
\tag{116.16}
$$

These zero-order infima do not make the source polar.

**Proof.** Conjugating exactly the supplied rank-one formula (115.5) by $U_h$ gives the first identity in (116.13). The first summand maps into $\mathscr V_0$ and $b_r$ has trace one. Applying (116.3) gives the source-start trace on every complex $L^2$ input. On the original space $(H+r)^{-1}\phi\in D(H)$, so (115.20) applies legitimately and gives the last identity. There is no division by a pointwise value of $h$ at $e$, and no claim that a general input has boundary coefficients.

The properly associated resolvent identifies $\widetilde{R_rf}$ with the expected discounted occupation for bounded Borel inputs, outside a properly exceptional set. Its trace value at the nonpolar source is therefore precisely (116.14). The density is positive and integrable, with
$\int b_r\,dm=\langle h,n_r\rangle=d_r$; its total mass is $1/r$, as required by conservation. This also checks the normalization against the original clock. For an $L^2$ input the formula for the trace in (116.13) remains finite by Cauchy--Schwarz; the bounded-Borel formula extends to Borel $L^2$ representatives by truncation, applied first to $|f|$, and then to real and imaginary parts. In particular it is insensitive to modifications on $m$-null sets.

Since $m(\{e\})=0$, the bounded Borel function $\mathbf1_{\{e\}}$ is zero as an $L^2(m)$ element. Its resolvent has quasi-continuous representative zero, so for quasi-every $x$,
$\mathbb E_x\int_0^\infty e^{-rs}\mathbf1_{\{e\}}(Z_s)\,ds=0$.
The integrand is nonnegative. Outside a properly exceptional set the integral is consequently zero almost surely; it bounds $e^{-rT}$ times the unweighted integral up to each finite $T$. Taking integer $T$ proves (116.15) simultaneously for all finite $T$. Nonpolarity again prevents exclusion of $e$. This argument uses occupation potentials, rather than inferring polarity or path avoidance from zero measure.

Conservation gives infinite lifetime, and (116.10) gives finite contact. Continuity of the diffusion paths puts the contact at the same original point $e$. The strong Markov property at $\tau_e$ makes the subsequent law the source-start law $\mathbb P_e$, for which infinite lifetime and (116.15) hold. Thus contact is followed by conservative continuation, with no interval of ordinary holding at the source. Its self-regularity concerns immediate returns and is compatible with zero time spent there.

Finally the constant $1$ is admissible with zero energy. It also supplies the usual recurrence criterion, $1\in\mathscr V\subset\mathscr V_e$ with $\mathscr E[1]=0$, for the full form. For the compactly supported infimum use the $\chi_R$ of (115.23), equal to one near $e$, whose energies tend to zero. For the shifted statements use (115.11):

$$
d_r=\int_{(0,\infty)}\frac{\lambda}{\lambda+r}\,d\nu(\lambda),
\qquad 0<d_r<1,\qquad d_r\longrightarrow1
                                  \quad(r\downarrow0).
\tag{116.17}
$$

The probability normalization of $\nu$ and its zero mass at zero justify all three assertions. The zero-order infimum is therefore distinct from the positive shifted capacity which detects polarity in this recurrent conservative setting. $\square$

**Definition 116.5 (source-specific correspondence and the unpaid native realization).** The equilibrium projection, part process, quasi-continuity, regularity of a nonpolar singleton and hitting-potential correspondence used above are established symmetric Dirichlet-form theory, with the cited Chen--Fukushima--Ying §2/§4 and Chen RIMS §1.2 supplying their meanings. Their ambient hypotheses hold here by Theorem 115.3 and the irreducibility argument in Theorem 116.3; their set is the original $\{e\}$, their measure is $h^2d\mu$, their discount is the original $r$, and their energy is exactly (115.15). The Brownian $1/2$ normalization in examples in those sources is not imported. The full form is conservative and recurrent; no transient zero-order theorem is applied to it. The proofs use only shifted projections and the original $F$ with $\ker F=\{0\}$, not a positive lower spectral bound.

The [native spatial-cap volume, Proposition 5.2](FIB_NATIVE_SPATIAL_CAP_RETAINED_AND_RESONANT_LIMITS.md#5-the-natural-logarithmic-source-form-and-positive-point-capacity) already identifies a continuous source trace and positive logarithmic point capacity on its different inherited-wall carrier. Its weight $H_\eta$, its interpolation, its inherited outer killing and its native boundary coefficients are not the normalized global $h$, full conservative form and original $A,C$ here; its parameter $\eta$ is not identified with the fixed central coefficient of (115.1). No capacity value or contact law is transferred from that model. The source-specific additions here are (116.3)--(116.5), the original-clock formulas (116.9)--(116.14), and the full-versus-killed domain distinction (116.11), deduced from the actual endpoint suppliers of §§112--115. They are ordinary mathematical deductions for this endpoint, not a new general potential theory or a worldwide-priority assertion.

A faithful native source/evolution/representation/readout correspondence for this endpoint must preserve the source functional $\operatorname{tr}$ and the actual selector, the shifted energies and capacities $r d_r$ in the same clock, the contact transforms $b_r$ and all-time killed survival, conservative continuation and zero ordinary residence, and the source-start response (116.14). More precisely, any proposed identification of native states with this process that preserves its source, time and transition laws must carry the native first-source-contact stopping time to $\tau_e$, its stopped transitions to $P_t^0$, and its discounted source-start observation laws to (116.14); a form-preserving identification must also carry source evaluation and the shifted minimization (116.2) to (116.4). These requirements follow by applying the identification to the displayed stopping times, expectations and variational constraints. Agreement only with the off-source differential expression (115.24), or with the two-zero-coefficient restriction of the actual operator, does not supply these identities. No such native maps are constructed here. The complete native legal-source/evolution/representation/readout correspondence remains unpaid, and no conclusion about physical spatial dimension follows.

## 追加锚（本行以下为增补区）

## 117. Deterministic-time entrance from the original source and a forbidden passive record

**Definition 117.1 (the retained endpoint and the source evaluation).** Fix arbitrary original $a,\eta>0$. Retain exactly $G$, $e$, $\mu$, the unit source $\Gamma$, the actual selector $A(u)=\rho C(u)$, $H$, the coefficient-positive normalized $h$, $m=h^2\mu$, $U_h$, $K=U_h^{-1}HU_h$ and $T_t=e^{-tK}$ of §§115–116. In particular $m(G)=1$, $m(\{e\})=0$ and $K\ge0$. Use the entire complex $L^2(G,m)$ with

$$
\langle u,v\rangle_m=\int_G\overline u v\,dm.
\tag{117.1}
$$

The source trace, form domain and shifted energy are precisely $\operatorname{tr}$, $\mathscr V$ and $\mathscr E_r$ of (116.1). The parameter $r>0$ below is a resolvent discount, with $b_r,d_r$ unchanged from (116.1) and (116.4); it is not a native transition probability. Let $Z$ be the conservative diffusion properly associated with this full form as in Theorem 116.3, and use its actual source-start law $\mathbb P_e$. All positive times refer to the original clock. No killed process, invariant initial distribution, pointwise value of $h$ at $e$, or change of selector is substituted.

**Theorem 117.2 (the actual source has a strictly positive deterministic-time entrance density).** For every $t>0$ there is a unique real nonnegative $g_t\in L^2(G,m)$ such that, for every bounded complex Borel function $f$ on $G$,

$$
\begin{gathered}
\mathbb E_e[f(Z_t)]
 =\operatorname{tr}(T_t[f])
 =\langle g_t,[f]\rangle_m
 =\int_G g_t f\,dm,\\
\mathbb P_e(Z_t\in dy)=g_t(y)m(dy),\qquad
\int_Gg_t\,dm=1,\qquad g_t>0\quad m\text{-a.e.}
\end{gathered}
\tag{117.2}
$$

Here $[f]$ is the $L^2(m)$ class of the given Borel function. The density is unique as an $L^2$ class; strict positivity is asserted almost everywhere for each fixed $t>0$. For every $r>0$ the complex-linear functional $\ell_t(v)=\operatorname{tr}(T_tv)$ on the full complex space satisfies

$$
\begin{gathered}
|\ell_t(v)|^2
 \le \frac{\sup_{\lambda\ge0}(\lambda+r)e^{-2t\lambda}}
              {r d_r}\,\|v\|_{L^2(m)}^2,\qquad
\|g_t\|_{L^2(m)}^2
 \le \frac{\sup_{\lambda\ge0}(\lambda+r)e^{-2t\lambda}}
              {r d_r},\\
g_{t+s}=T_sg_t\quad(t>0,\ s\ge0).
\end{gathered}
\tag{117.3}
$$

The expectation identity extends to every Borel representative of a complex $L^2(m)$ vector, with absolute integrability at each positive time. In particular it is insensitive to all Borel $m$-null modifications at such a time, including modifications at the nonpolar source itself. No density is asserted at time zero, when the actual law is $\delta_e$.

**Proof.** Spectral smoothing gives $T_tv\in D(K^{1/2})=\mathscr V$ for $t>0$ and every complex $v\in L^2(m)$. If $E_K$ is the spectral resolution of $K$, then the original trace bound (116.4) gives

$$
\begin{aligned}
|\operatorname{tr}(T_tv)|^2
 &\le\frac{\mathscr E_r[T_tv]}{r d_r}\\
 &=\frac1{r d_r}\int_{[0,\infty)}
       (\lambda+r)e^{-2t\lambda}\,d\langle v,E_K(\lambda)v\rangle_m\\
 &\le\frac{\sup_{\lambda\ge0}(\lambda+r)e^{-2t\lambda}}
              {r d_r}\,\|v\|_2^2.
\end{aligned}
\tag{117.4}
$$

The supremum is finite, for example it is at most $r+(2\mathrm e t)^{-1}$, and $r d_r>0$ by (116.4). The complex Hilbert-space Riesz theorem therefore supplies a unique vector $g_t$ with $\ell_t(v)=\langle g_t,v\rangle_m$. The order of the pairing follows from its antilinear first slot and the linearity of $\ell_t$; no restriction to a real subspace is made in this construction. The operator-norm bound for the functional is exactly the bound for $\|g_t\|_2$ in (117.3).

For real $v\ge0$ almost everywhere, the Markov property gives $T_tv\ge0$ almost everywhere. Its quasi-continuous form representative is nonnegative quasi-everywhere: its negative part is the zero form vector and thus has quasi-continuous version zero. Since $e$ is nonpolar, (116.3) implies $\operatorname{tr}(T_tv)\ge0$. Real inputs also have real trace. Testing the Riesz identity on all real vectors first makes $g_t$ real, and testing on its negative part gives
$0\le\ell_t((g_t)_-)=-\|(g_t)_-\|_2^2$. Hence $g_t\ge0$. Conservation and the unchanged source trace give
$\int g_t\,dm=\ell_t(1)=\operatorname{tr}1=1$. This proves positivity and mass without assigning a value to an arbitrary $L^2$ representative at $e$.

We next identify the functional with the actual deterministic-time process law. Proper association is used in its semigroup sense: for each $t>0$ and each bounded real Borel $f$, the function
$x\mapsto\mathbb E_x[f(Z_t)]$, on the complement of the properly exceptional set of the process, is a quasi-continuous version of $T_t[f]$. Two quasi-continuous versions of this form vector agree quasi-everywhere. Both that exceptional set and the set on which the versions could differ have zero capacity; neither can contain the positive-capacity singleton $\{e\}$. Consequently, for this very $t$ and this given Borel representative,

$$
\mathbb E_e[f(Z_t)]
 =\widetilde{T_t[f]}(e)
 =\operatorname{tr}(T_t[f])
 =\langle g_t,[f]\rangle_m.
\tag{117.5}
$$

This is an evaluation of the properly associated transition function, rather than an inference from equality of Laplace transforms or equality for almost every time. The argument applies separately to every fixed $t>0$ and every bounded Borel $f$, and never requires an uncountable union of exceptional sets to avoid $e$: no individual polar set can contain $e$. Real and imaginary parts prove the bounded complex identity. In particular, applying it to $f=\mathbf1_A$ for an arbitrary Borel $m$-null set $A$ proves $\mathbb P_e(Z_t\in A)=0$. Thus even null sets of positive capacity cause no representative ambiguity in the positive-time law. Applying bounded truncations to the absolute value of a Borel $L^2$ representative and using
$\int g_t|v|\,dm\le\|g_t\|_2\|v\|_2$ proves absolute integrability and extends (117.5) to that representative. Uniqueness of the density also follows from these bounded Borel tests.

For every complex $v\in L^2(m)$, the semigroup identity and self-adjointness give

$$
\langle g_{t+s},v\rangle_m
 =\operatorname{tr}(T_tT_sv)
 =\langle g_t,T_sv\rangle_m
 =\langle T_sg_t,v\rangle_m.
\tag{117.6}
$$

Riesz uniqueness proves the last line of (117.3). To obtain strict positivity, use precisely the irreducibility argument of Theorem 116.3: a semigroup-invariant indicator is a zero-energy vector, and the full integral energy forces such a vector to be constant on connected $M$. Hence there is no invariant set with both it and its complement of positive $m$-measure. The standard equivalence between this irreducibility and positivity improvement is [Lenz–Stollmann–Veselić, *The Allegretto–Piepenbrink Theorem for Strongly local forms*, arXiv:0811.2135v1, §1, Theorem 1.1](https://arxiv.org/html/0811.2135v1#S1.Thmtheorem1). Its form $\mathfrak h$ is here the densely defined closed nonnegative $\mathscr E$ on $L^2(G,m)$, its operator is $K$, and its positivity-preserving semigroup is the actual $T_t$. These are the hypotheses of that equivalence; no Harnack principle, pointwise heat-kernel regularity or spectral gap is required. It gives $T_su>0$ almost everywhere whenever $s>0$ and $u\ge0$ is nonzero. Since $g_{t/2}$ has mass one,

$$
g_t=T_{t/2}g_{t/2}>0\quad m\text{-a.e.}
\tag{117.7}
$$

This proves (117.2) for the source-start process itself.

There is also an exact consistency check with the original source resolvent. For bounded complex Borel $f$, (117.2) and (116.14) imply

$$
\int_0^\infty e^{-rt}\left(\int_Gg_t f\,dm\right)dt
 =\mathbb E_e\int_0^\infty e^{-rt}f(Z_t)\,dt
 =\frac1{r d_r}\int_Gb_r f\,dm.
\tag{117.8}
$$

Both iterated expectation integrals are justified by the absolute bound $\|f\|_\infty/r$ and conservation. The left integrand is measurable by its equality with the actual transition expectation; no jointly pointwise choice of the $L^2$ densities is needed. Thus (116.14) is the Laplace-time average of the deterministic-time laws already identified in (117.5), with the same discount and clock. It is not substituted for those laws. $\square$

**Definition 117.3 (fixed-gap, time-homogeneous nondisturbing emission).** A candidate in this class uses exactly the process $Z$ of Definition 117.1 started at $e$, a fixed deterministic $\Delta>0$ in its original time units, and Borel functions

$$
f_y:G\longrightarrow[0,1],\qquad
\sum_{y\in\mathcal A}f_y(x)=1\quad(x\in G),\qquad
\mathcal A=\{0,1,3,B\}.
\tag{117.9}
$$

Conditional on the entire source path, the read at time $n\Delta$, $n=0,1,\ldots$, produces $\widehat Y_n=y$ with probability $f_y(Z_{n\Delta})$, and the read noises at distinct epochs are independent and fresh. The functions are the same at every epoch. A read leaves the actual source state and all its subsequent transition rules unchanged: after the read the source still evolves by $Z$ with transition semigroup $T_t$. There is no additional retained controller, shared read-noise memory, or emission depending on past records. The emitted labels are outcomes, not selectable operations. All four outcomes and their unconditional probabilities count; no failure branch or unwanted record is discarded.

This specifies a complete candidate passive record law, not just one-time emission marginals. A Borel partition $G=\bigsqcup_{y\in\mathcal A}A_y$, with $f_y=\mathbf1_{A_y}$, is its deterministic coarse-graining special case. The value $f_y(e)$ matters for the time-zero read; at positive sampled epochs Theorem 117.2 determines the law for every Borel choice, including changes on $m$-null sets. One may instead declare a fixed lead-in $t_*>0$ and read at $t_*+n\Delta$, retaining the same source start at original time zero and the same evolution throughout the lead-in. This variant adds no preparation at $t_*$.

**Definition 117.4 (the complete original passive target).** The target is exactly [Self Generated Predictive Memory, Assumption 1.1](RECURSIVE_RELATIONAL_OBSERVATION_SELF_GENERATED_PREDICTIVE_MEMORY.md#1-the-source-and-the-continuing-decoder-contract). To separate its parameters from the source coefficients and the resolvent discount, write

$$
\begin{gathered}
p_{\rm N},q_{\rm N},r_{\rm N}>0,\qquad
p_{\rm N}+q_{\rm N}+r_{\rm N}<1,\\
s_{\rm N}=p_{\rm N}+q_{\rm N},\qquad
a_{\rm N}=1-s_{\rm N},\qquad b_{\rm N}=1-r_{\rm N},\qquad
c_{\rm N}=1-s_{\rm N}-r_{\rm N},\\
P_{\rm N}=\begin{pmatrix}
c_{\rm N}&p_{\rm N}&0&q_{\rm N}&r_{\rm N}\\
q_{\rm N}&a_{\rm N}&p_{\rm N}&0&0\\
0&q_{\rm N}&a_{\rm N}&p_{\rm N}&0\\
p_{\rm N}&0&q_{\rm N}&a_{\rm N}&0\\
r_{\rm N}&0&0&0&b_{\rm N}
\end{pmatrix},\qquad
\pi=\tfrac15(1,1,1,1,1).
\end{gathered}
\tag{117.10}
$$

Its rows and columns are indexed by $0,1,2,3,4$, with rows denoting departure states. The hidden chain has $X_0\sim\pi$ and this exact transition matrix, and its only records are

$$
Y_n=\chi(X_n),\qquad
\chi(0)=0,\quad\chi(1)=1,\quad\chi(3)=3,\quad
\chi(2)=\chi(4)=B.
\tag{117.11}
$$

The parameters in (117.10) have no presumed identification with $a,\eta,r$ of the endpoint. Equalities $p_{\rm N}=q_{\rm N}$ or $r_{\rm N}=s_{\rm N}$ remain allowed. Exact realization requires equality of the complete unconditional finite-record laws of $(\widehat Y_n)$ and $(Y_n)$ at their corresponding indices, with the same subsequent reads and their chronological successors. It does not give the observer access to $X_n$, source resets, selected output labels, or a supplied past. In the endpoint candidate the actual initial state is $e$, not a sample from $m$; only its emitted records are required to have the stationary target law.

**Theorem 117.5 (the actual endpoint cannot realize this passive law by the declared emissions).** For every original $a,\eta>0$, every fixed $\Delta>0$, every choice of the native parameters in (117.10), and every emission kernel of Definition 117.3, the candidate complete record law differs from the target of Definition 117.4. This holds also for every fixed positive lead-in and for every deterministic coarse graining in that class. If the positive one-letter target marginals for symbols $1$ and $3$ are matched at a positive sampled epoch, then for every corresponding adjacent pair whose first time $t$ is positive,

$$
\begin{aligned}
\mathbb P_e(\widehat Y_n=1,\widehat Y_{n+1}=3)
 &=\int_Gg_t f_1\,T_\Delta f_3\,dm>0,\\
\mathbb P(Y_n=1,Y_{n+1}=3)
 &=\tfrac15(P_{\rm N})_{13}=0,
\end{aligned}
\qquad
\begin{cases}
t=n\Delta>0,&\text{without lead-in},\\
t=t_*+n\Delta>0,&\text{with lead-in}.
\end{cases}
\tag{117.12}
$$

Thus matching the complete law fails already at this two-record marginal once those one-letter marginals are matched.

**Proof.** Each column sum of $P_{\rm N}$ is one: the first is $c_{\rm N}+q_{\rm N}+p_{\rm N}+r_{\rm N}$, the next three are $a_{\rm N}+p_{\rm N}+q_{\rm N}$, and the last is $r_{\rm N}+b_{\rm N}$. Hence $\pi P_{\rm N}=\pi$. At every native epoch the four one-letter probabilities in order $(0,1,3,B)$ are therefore $(1/5,1/5,1/5,2/5)$. Because $\chi^{-1}(1)=\{1\}$ and $\chi^{-1}(3)=\{3\}$, the target adjacent event in (117.12) is exactly $\{X_n=1,X_{n+1}=3\}$, of probability $(P_{\rm N})_{13}/5=0$. This calculation uses the actual indexed matrix, including its forbidden entry, rather than a different five-state or quantum instrument.

For any positive sampled time $u$, Theorem 117.2 and the emission rule give

$$
\mathbb P_e(\widehat Y_j=y)=\int_G g_u f_y\,dm.
\tag{117.13}
$$

If the $1$ and $3$ marginals are matched there, both integrals are $1/5$. Since $0\le f_y\le1$ and $m$ is a probability, $f_1,f_3\in L^2(m)$; neither is the zero $L^2$ vector. In particular the Borel set $\{f_1>0\}$ has positive $m$-measure. This conclusion would already follow from any positive values for those two marginals, and does not depend on how small their supports are.

Conditional independence of the read noises given the path first gives

$$
\begin{aligned}
\mathbb P_e(\widehat Y_n=1,\widehat Y_{n+1}=3)
 &=\mathbb E_e[f_1(Z_t)f_3(Z_{t+\Delta})]\\
 &=\int_Gg_t(x)f_1(x)\,(T_\Delta f_3)(x)\,m(dx).
\end{aligned}
\tag{117.14}
$$

The second line is the ordinary Markov conditional-expectation formula in the same source process and original clock. Proper association identifies its transition expectation with $T_\Delta[f_3]$ $m$-a.e.; the law $g_t m$ from (117.2) makes that representative equality sufficient in this integral. The read has not intervened in the transition to $t+\Delta$. Since $\Delta>0$ and $f_3$ is nonnegative and nonzero, the positivity improvement used in (117.7) gives $T_\Delta f_3>0$ $m$-a.e. Also $g_t>0$ $m$-a.e. The integrand is therefore strictly positive almost everywhere on $\{f_1>0\}$, a set of positive measure, so its integral is strictly positive. It is finite because $0\le T_\Delta f_3\le1$ and $\int g_t\,dm=1$.

If either positive one-letter marginal is not matched, the complete record law already differs on one record. If both are matched, (117.12) proves a difference on two records. With sampling from time zero, take $n=1$, so $t=\Delta>0$; no assertion about a density at $e$ at time zero is used. With a positive lead-in, $n=0$ already suffices. Indicator emissions satisfy every hypothesis, proving the coarse-graining case. No stationarity of the endpoint source-start distribution has been imposed. $\square$

**Definition 117.6 (attribution and the exact correspondence excluded).** Spectral smoothing, the complex Riesz representation theorem, quasi-continuity and proper association, the irreducibility/positivity-improvement equivalence, and the Markov multiplication formula in (117.14) are established suppliers. Theorem 117.2 applies them to the specific trace with capacity $r d_r$, the actual non-Friedrichs selector and the nonpolar original source of §§115–116. Theorem 117.5 consumes that deterministic-time source law against the exact forbidden entry in Self Generated Predictive Memory, Assumption 1.1. These are source-specific deductions, not new general positivity or reconstruction theorems and not claims of worldwide priority. The capacity/contact result on the different inherited-wall carrier cited in Definition 116.5 does not replace this source-start construction.

The excluded correspondence is one complete common-source, clock and readout proposal: start the actual endpoint at $e$, preserve its full transition law and genuine successors, associate one native step with the fixed positive elapsed time $\Delta$, and use only the nondisturbing memoryless emission kernel (117.9), including every record without conditioning away failures. Positivity of $K$ or existence of a positive spectral representation alone does not identify a native record law. It is proper association at the nonpolar source, followed by positivity improvement and the shared-path joint formula, that makes the contradiction with (117.10) follow.

This class excludes contact/event sampling, interventions that change the source successor, instruments with retained state, past-dependent emissions, arbitrary shared memory, and real-time unitary dynamics. The theorem places no obstruction on those other proposals, on all classical extensions, or on the original C5/qutrit instrument. The distinctions between a positive kernel, an operational coherent comparison and purification in [Coherent Reconstruction, §§12–13, 25–34](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md) and [Self Generated Predictive Memory, §§12–16](RECURSIVE_RELATIONAL_OBSERVATION_SELF_GENERATED_PREDICTIVE_MEMORY.md) retain their separate hypotheses. No coherent comparison service is supplied here, and classical joint records are not asserted to exhaust coherent retained memory. Conservative contact continuation in Theorem 116.4 is a source-start Markov law, not by itself a coherent-record return interface.

The strict inequality in (117.12) is an exact obstruction for each declared candidate. Its positive value depends on the source, sampling gap, epoch and emissions; the argument supplies no parameter-uniform separation, quantitative noise tolerance or sample bound. No pointwise heat kernel at $e$, spectral gap, physical Hilbert/Born/composition acquisition, or completion of quantum origin follows. The construction or exclusion of faithful native coherent operations remains a separate mathematical obligation. The conclusions here are ordinary mathematical consequences of the stated source and readout premises.

## 追加锚（本行以下为增补区）
