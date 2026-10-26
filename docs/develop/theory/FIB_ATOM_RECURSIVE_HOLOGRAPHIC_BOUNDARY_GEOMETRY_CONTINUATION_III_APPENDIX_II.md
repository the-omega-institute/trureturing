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
