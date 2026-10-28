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

## 118. Uniform passive-pair separation for the original source-start diffusion

**Definition 118.1 (the original pair laws and their uniform separation problem).**
Fix arbitrary original $a,\eta>0$ and arbitrary original times $t,\Delta>0$.
Retain exactly Definition 117.1: the four-coordinate group $G=H^1\times\mathbb R$,
identity $e$, raw Haar measure $\mu$, unit-source field $\Gamma$, actual selector
$A(u)=\rho C(u)$, operator $H$, coefficient-positive normalized $h$, measure
$m=h^2\mu$, unitary $U_hv=hv$, operator $K=U_h^{-1}HU_h$ and semigroup
$T_s=e^{-sK}$. The entire complex form domain and energy are (115.15), including
the source summand $\mathbb C1$; the actual operator domain is (115.17).
The conservative diffusion $Z$ starts at $e$ at original time zero and runs
through the lead-in $t$ without preparation or change of clock.

Fix every permitted native tuple $p_{\rm N},q_{\rm N},r_{\rm N}>0$ with
$p_{\rm N}+q_{\rm N}+r_{\rm N}<1$, retaining exactly $s_{\rm N},a_{\rm N},b_{\rm N},
c_{\rm N},P_{\rm N},\pi$ and $\chi$ of (117.10)–(117.11).
In particular $p_{\rm N}=q_{\rm N}$ and $r_{\rm N}=s_{\rm N}$ are allowed.
On $\mathcal A=\{0,1,3,B\}$ define the exact adjacent target law

$$
\Pi_{\rm N}(y,z)
 =\mathbb P(\chi(X_0)=y,\chi(X_1)=z)
 =\frac15\sum_{\substack{i:\chi(i)=y\\j:\chi(j)=z}}(P_{\rm N})_{ij}.
\tag{118.1}
$$

Let $\mathcal F$ be the class of all Borel tuples $f=(f_y)_{y\in\mathcal A}$ of (117.9):
$0\le f_y\le1$ and $\sum_y f_y(x)=1$ for every $x\in G$.
Read the same tuple at $t$ and $t+\Delta$, using fresh noises independent
conditional on the entire $Z$ path, leaving $Z$ and its successors unchanged
and retaining all four outcomes. Define, by the same Markov formula as (117.14),

$$
\begin{aligned}
\nu_f(y,z)
 &=\mathbb E_e[f_y(Z_t)f_z(Z_{t+\Delta})]
   =\int_G g_t f_y\,T_\Delta f_z\,dm,\\
d_f&=\operatorname{TV}(\nu_f,\Pi_{\rm N})
   =\frac12\sum_{y,z\in\mathcal A}|\nu_f(y,z)-\Pi_{\rm N}(y,z)|.
\end{aligned}
\tag{118.2}
$$

Here $g_t$ is the actual source-start density (117.2), not a stationary
initial law. The uniform separation in Theorem 118.3 is a repo-derived
source-specific deduction for these laws. Bounded-domain elliptic kernels,
part-process survival domination, tightness and Cauchy–Schwarz are classical
intermediate tools, credited in its proof; no new general kernel theorem or
worldwide-priority assertion is part of this attribution.

**Definition 118.2 (fixed source-dependent localization and constants).**
Use the actual probability densities $g_t,g_{t+\Delta}\in L^2(G,m)$ of (117.2).
They are strictly positive $m$-a.e., and their laws assign no mass to $e$.
Fix any auxiliary resolvent discount $\alpha>0$ and use the original
$d_\alpha$ of (116.4). Its role is separate from the native probability
$r_{\rm N}$; no numerical inequality between them is imposed. Set

$$
B=\frac{\sup_{\lambda\ge0}(\lambda+\alpha)e^{-2(t+\Delta)\lambda}}
         {\alpha d_\alpha},\qquad
0<\|g_{t+\Delta}\|_2^2\le B<\infty.
\tag{118.3}
$$

The inequality is (117.3); $\alpha$ is not a new source parameter.
Identify $G$ with its original $\mathbb R^4$ coordinates, with Euclidean norm
$|x|$. Choose $R>1$ large enough that, for

$$
C=\{x:1/R\le|x|\le R\},\qquad
D=\{x:1/(2R)<|x|<2R\},
\tag{118.4}
$$

$$
\int_{G\setminus C}g_t\,dm\le\frac1{20},\qquad
\int_{G\setminus C}g_{t+\Delta}\,dm\le\frac1{20}.
\tag{118.5}
$$

Such a common $R$ exists by monotone convergence along the compact annuli
exhausting $M=G\setminus\{e\}$. The domain $D$ is bounded, connected and smooth,
$C\subset D$, and $\overline D\subset M$. These choices precede every choice of $f$.
For the same full diffusion put $\tau_D=\inf\{s\ge0:Z_s\notin D\}$, and denote
its part semigroup on $D$ by

$$
Q_s^D v(x)=\mathbb E_x[v(Z_s);\ s<\tau_D],\qquad x\in D,
\tag{118.6}
$$

with the properly associated versions. Write $H_D$ for the Dirichlet
realization on $D$ of the original expression $S$ in (115.1), and $k_D$ for
the continuous interior kernel of $e^{-sH_D}$ relative to the original $\mu$.
Its existence and correspondence to (118.6) are proved below. Define

$$
p_D(s,x,y)=\frac{k_D(s,x,y)}{h(x)h(y)},\qquad
\kappa=\min_{x,y\in C}p_D(\Delta,x,y),\qquad
\delta=\min\left\{\frac1{20},\frac{\kappa}{1000B}\right\}.
\tag{118.7}
$$

This density belongs only to the bounded off-source part. No global
pointwise heat kernel, or kernel evaluation at $e$, is included in the definition.

**Theorem 118.3 (uniform separation from the exact original passive pair).**
For every fixed original $a,\eta,t,\Delta>0$ and every native parameter tuple
of Definition 118.1, the constants in Definition 118.2 satisfy
$0<\kappa<\infty$, $\delta>0$, and

$$
\operatorname{TV}(\nu_f,\Pi_{\rm N})\ge\delta
\quad\text{for every }f\in\mathcal F,\qquad
\inf_{f\in\mathcal F}\operatorname{TV}(\nu_f,\Pi_{\rm N})\ge\delta>0.
\tag{118.8}
$$

This is a source- and time-dependent existence bound, independent of every
Borel emission tuple. It supplies no cross-source or cross-time uniform
constant, numerical value for $\kappa$ or $d_\alpha$, computed rate or sample bound.
The passive contract remains Definition 117.3: there is no source reset,
postselection, event sampling, read intervention, retained controller or shared
noise memory. No stationary initial source, global heat-kernel premise,
logarithmic Sobolev constant, spectral gap, compactness of the full semigroup,
extra emission regularity or stronger approximation premise is required.
The conclusion concerns these unconditional classical records; it supplies no
coherent operations, physical realization or native-origin correspondence and
places no obstruction on the different operational classes in Definition 117.6.

**Proof.** First identify the local part of the full form, retaining its
original source domain. On a neighborhood of $\overline D$, Theorem 115.2
makes $h$ smooth and strictly positive; $h,h^{-1}$ and their required derivatives
are bounded there. The original principal matrix $A_0$ has quadratic symbol

$$
p^{\mathsf T}A_0(x)p
 =a\bigl(p_x^2+(p_y+xp_w)^2+p_z^2\bigr)+\eta p_w^2.
\tag{118.9}
$$

This is exactly (115.10). It is positive definite for every original
$a,\eta>0$, and uniformly so on that compact neighborhood. Together with
the upper and lower bounds on $h^2$, it makes the local full form norm
equivalent to the ordinary $H^1$ norm. Consequently the part domain
$\{v\in\mathscr V:\widetilde v=0\text{ quasi-everywhere on }G\setminus D\}$,
identified by zero extension, is precisely the complex $H_0^1(D)$.
Indeed, a part-domain vector is locally $H^1$ on a neighborhood of
$\overline D$ and is zero outside $D$. Across the smooth boundary its zero
extension has zero trace, so its restriction belongs to $H_0^1(D)$.
Conversely, the defining $C_c^\infty(D)$ approximants to any $H_0^1(D)$ vector
converge in the equivalent local form norm. Their zero extensions lie in
$\mathscr V_0$ and converge in the full form norm, giving that vector in the
part domain. These vectors vanish on a neighborhood of $e$, with source
trace zero. Polarization of (115.15) thus gives the exact part energy

$$
\mathscr E^D[v,z]
 =\int_D\left(a\sum_{i=1}^3\overline{X_iv}X_iz
       +\eta\overline{\partial_wv}\partial_wz\right)dm,
\qquad v,z\in H_0^1(D).
\tag{118.10}
$$

This is also the $D$-part of the source-killed form in (116.9)–(116.11).
It is obtained by taking a part of the form, not by restricting the operator
to $D(K)\cap\mathscr V_0$, which (116.11) distinguishes from the part operator.

Multiplication by the actual $h$ maps $H_0^1(D)$ bijectively onto itself
and is unitary from $L^2(D,m)$ to $L^2(D,\mu)$.
Apply the original ground-state identity (115.18) on $C_c^\infty(D)$ and
then close it on this domain. It identifies the conjugated part with $H_D$,
whose form is

$$
q_D[\phi]
 =\int_D\left(a\sum_{i=1}^3|X_i\phi|^2
       +\eta|\partial_w\phi|^2-g_c\Gamma|\phi|^2\right)d\mu,
\qquad \phi\in H_0^1(D),\qquad g_c=16\sqrt{a\eta}.
\tag{118.11}
$$

In particular the real potential is $-g_c\Gamma$, with its original sign.
All coefficients are bounded and smooth on $\overline D$, and the principal
matrix is uniformly elliptic there. The raw Haar measure is exactly
Lebesgue measure in these coordinates, so no measure or time normalization
enters this identification.

For the local kernel use Arendt–ter Elst–Glück,
[*Strict positivity for the principal eigenfunction of elliptic operators with
various boundary conditions*, arXiv:1909.12194v3, §4.1 and Remark 4.2,
Corollary 3.5](https://arxiv.org/pdf/1909.12194v3).
The coefficient hypotheses are those of §4, with $\Omega=D$, principal
coefficients $A_0$, divergence and first-order lower coefficients $b_k=c_k=0$,
and zeroth coefficient $c_0=-g_c\Gamma$. The bounded connected smooth annulus
is Wiener regular, as required in §4.1. Its Dirichlet form is exactly
(118.11). Section 4.1 supplies the positive irreducible holomorphic
strongly continuous semigroup $S_s=e^{-sH_D}$ on $L^2(D,\mu)$ and
$S_sL^2(D,\mu)\subset C_0(D)$ for every $s>0$.
Here $H_D$ is self-adjoint, so its adjoint has the identical smoothing property.
The restriction of $S$ to $C_0(D)$ is a strongly continuous semigroup by the
same section. For each $x\in D$, choose $\psi\in C_c(D)$ with $\psi(x)\ne0$;
uniform convergence $S_s\psi\to\psi$ as $s\downarrow0$ gives a nonzero
evaluation at $x$ for some $s>0$. Self-adjointness gives the adjoint evaluation
condition as well. Thus all three hypotheses of Corollary 3.5 hold with
its exponent $p=2$. That corollary gives, for every $s>0$, a jointly continuous
spatial kernel $k_D(s,\cdot,\cdot)$, strictly positive at every pair in
$D\times D$. Remark 4.2 also records the classical Dirichlet kernel positivity.

Conjugating back by the original $h$ gives the semigroup identity below,
and hence the identity $m$-a.e. for the properly associated process versions:

$$
\begin{aligned}
Q_s^Dv(x)
 &=h(x)^{-1}\int_D k_D(s,x,y)h(y)v(y)\,d\mu(y)\\
 &=\int_D p_D(s,x,y)v(y)\,dm(y).
\end{aligned}
\tag{118.12}
$$

Thus $p_D(s,\cdot,\cdot)$ is continuous and strictly positive on $D\times D$.
Compactness of $C\times C\subset D\times D$ proves $0<\kappa<\infty$.
This application imports only the bounded-domain kernel, with no assertion
of a global pointwise kernel for the singular-source endpoint.

For the relation to the full process use Lenz–Stollmann,
[*On the decomposition principle and a Persson type theorem for general regular
Dirichlet forms*, arXiv:1705.10398v2, §1, equation (1)](https://arxiv.org/pdf/1705.10398v2).
Their space, measure, regular form, operator and open set are respectively
$G,m,\mathscr E,K,D$. Regularity and proper association are supplied by
Theorems 115.3 and 116.3; the part form is (118.10).
Their equation (1) identifies its semigroup with the survival expression
(118.6) almost everywhere. Since the survival indicator is at most one,
for every nonnegative Borel $v\in L^2(G,m)$,

$$
T_\Delta v(x)\ge Q_\Delta^D(v|_D)(x)
\quad\text{for }m\text{-a.e. }x\in D.
\tag{118.13}
$$

This uses only that equation's regular-form part correspondence, not the
additional spectral hypotheses of the cited paper's later results.
Proper association identifies the transition expectations up to null sets;
the actual source-at-$t$ law $g_t m$ makes those null sets immaterial.
For $v=f_3$, (118.12)–(118.13) imply
$T_\Delta f_3(x)\ge\kappa\int_C f_3\,dm$ for $m$-a.e. $x\in C$.
The unchanged shared-path formula (118.2) now yields

$$
\nu_f(1,3)
 \ge\kappa\left(\int_Cg_t f_1\,dm\right)
              \left(\int_C f_3\,dm\right).
\tag{118.14}
$$

Only a surviving component of the full transition was bounded below.
The process observed in $\nu_f$ remains the original conservative diffusion,
with no killing, conditioning, reset or intervention in its law.

It remains to make (118.14) uniform over every Borel $f$.
For the exact matrix (117.10), the column sums are
$c_{\rm N}+q_{\rm N}+p_{\rm N}+r_{\rm N}=1$,
$a_{\rm N}+p_{\rm N}+q_{\rm N}=1$ for the next three columns, and
$r_{\rm N}+b_{\rm N}=1$ for the last. Thus $\pi P_{\rm N}=\pi$.
The singleton preimages $\chi^{-1}(1)=\{1\}$ and $\chi^{-1}(3)=\{3\}$ give

$$
\Pi_{\rm N}(\{1\}\times\mathcal A)=\frac15,\qquad
\Pi_{\rm N}(\mathcal A\times\{3\})=\frac15,\qquad
\Pi_{\rm N}(1,3)=\frac15(P_{\rm N})_{13}=0.
\tag{118.15}
$$

These identities hold also when $p_{\rm N}=q_{\rm N}$ or
$r_{\rm N}=s_{\rm N}$, with no native parameter exclusion.
Write $d=d_f$. If $d\ge1/20$, then $d\ge\delta$ immediately.
Suppose $d<1/20$. Total variation bounds the difference on every marginal
event. Summing (118.2) over the other label, conservation and (117.2) give

$$
\int_Gg_t f_1\,dm\ge\frac15-d,\qquad
\int_Gg_{t+\Delta}f_3\,dm\ge\frac15-d.
\tag{118.16}
$$

Subtract the two tails in (118.5), using $0\le f_y\le1$, to obtain

$$
A_1:=\int_Cg_t f_1\,dm>\frac1{10},\qquad
A_3:=\int_Cg_{t+\Delta}f_3\,dm>\frac1{10}.
\tag{118.17}
$$

Cauchy–Schwarz on $(g_{t+\Delta}\sqrt{f_3})\sqrt{f_3}$ over $C$ gives

$$
A_3^2
 \le\left(\int_Cg_{t+\Delta}^2f_3\,dm\right)
      \left(\int_Cf_3\,dm\right)
 \le B\int_Cf_3\,dm,
\qquad \int_Cf_3\,dm>\frac1{100B}.
\tag{118.18}
$$

Combining (118.14), (118.17) and (118.18), and testing total variation on
the forbidden singleton of (118.15), proves

$$
d\ge\nu_f(1,3)>\frac{\kappa}{1000B}\ge\delta.
\tag{118.19}
$$

Both cases establish (118.8). Positivity and finiteness of $B$ follow from
(117.3) and $\alpha d_\alpha>0$, so $\delta>0$.
All localization constants were fixed from the original source and times
before $f$ was chosen. Neither a stationary replacement for $g_t m$ nor any
regularity approximation to the Borel emissions entered the argument. $\square$

## 追加锚（本行以下为增补区）

## 119. Stochastic attainment and deterministic approximation for the original passive pair

**Definition 119.1 (attainable laws for the unchanged source and target).**
Fix every original $a,\eta,t,\Delta>0$ and every native tuple of Definition 118.1,
including $p_{\rm N}=q_{\rm N}$ and $r_{\rm N}=s_{\rm N}$ when they occur.
Retain exactly Definitions 117.1, 117.3, 117.4 and 118.1 and their suppliers
in §§115–116: the four-coordinate $G$, original $e,\mu,\Gamma$, actual selector
$A(u)=\rho C(u)$, coefficient-positive normalized $h$, $m=h^2\mu$, entire
complex form (115.15), $K=U_h^{-1}HU_h$, original-clock $T_s=e^{-sK}$ and
actual conservative diffusion started at $e$ at time zero. The same Borel
$f\in\mathcal F$ is read at $t,t+\Delta$ with the independent fresh noises
conditional on the entire path and unchanged successors of Definition 117.3.
Let $\mathcal F_{\rm det}$ consist of the indicator tuples of all Borel
partitions $G=\bigsqcup_{y\in\mathcal A}A_y$, where $\mathcal A=\{0,1,3,B\}$.
Using precisely $\nu_f,d_f,\Pi_{\rm N}$ of (118.1)–(118.2), define

$$
\begin{gathered}
\mathcal L_{\rm stoch}=\{\nu_f:f\in\mathcal F\},\qquad
\mathcal L_{\rm det}=\{\nu_f:f\in\mathcal F_{\rm det}\},\\
D_{\rm stoch}=\inf_{f\in\mathcal F}d_f,\qquad
D_{\rm det}=\inf_{f\in\mathcal F_{\rm det}}d_f.
\end{gathered}
\tag{119.1}
$$

The law sets lie in the finite-dimensional probability simplex on
$\mathcal A^2$; closures below use its ordinary Euclidean topology.
For clarity, summing the actual indexed matrix (117.10) over the fibers of
$\chi$ gives, in label order $(0,1,3,B)$,

$$
5\Pi_{\rm N}=\begin{pmatrix}
c_{\rm N}&p_{\rm N}&q_{\rm N}&r_{\rm N}\\
q_{\rm N}&a_{\rm N}&0&p_{\rm N}\\
p_{\rm N}&0&a_{\rm N}&q_{\rm N}\\
r_{\rm N}&q_{\rm N}&p_{\rm N}&a_{\rm N}+b_{\rm N}
\end{pmatrix}.
\tag{119.2}
$$

Its row and column marginals are $(1,1,1,2)/5$ and its $(1,3)$ and $(3,1)$
entries vanish. This is the original target, with no stationary replacement
for the source law $g_t m$.

**Theorem 119.2 (attained stochastic minimum and equal deterministic infimum).**
For each fixed parameter tuple of Definition 119.1,
$\mathcal L_{\rm stoch}$ is compact and

$$
\mathcal L_{\rm stoch}=\overline{\mathcal L_{\rm det}},\qquad
\min_{f\in\mathcal F}d_f=D_{\rm stoch}=D_{\rm det}\ge\delta>0,
\tag{119.3}
$$

where $\delta$ is any fixed choice supplied by Definition 118.2 and
Theorem 118.3 for these source parameters and times. Every stochastic pair
law is a limit of pair laws obtained by using one deterministic Borel
partition at both epochs. The conclusion asserts neither an attaining
partition nor a computed optimum value. Whether such a partition exists
for every permitted tuple, and hence whether stochastic attainment,
equality of infima and deterministic attainment all hold together,
remains unresolved.

**Proof.** Write $\mathscr E[v]=\mathscr E[v,v]$ for the full form (115.15).
We first prove the continuity needed for the actual nonstationary law.
Suppose $0\le u_n\le1$ and $u_n\to u$ weak-star in $L^\infty(m)$.
The limit lies in the same order interval. Since $m(G)=1$, every $L^2(m)$
test lies in $L^1(m)$, so this convergence also holds weakly in $L^2(m)$.
Put $v_n=T_\Delta u_n$. The Markov contraction of Theorem 115.3 and
spectral calculus for the actual nonnegative self-adjoint $K$ give

$$
0\le v_n\le1,\qquad v_n\in\mathscr V,\qquad
\mathscr E[v_n]
 \le\sup_{\lambda\ge0}\lambda e^{-2\Delta\lambda}\|u_n\|_2^2
 \le\frac1{2\mathrm e\Delta}.
\tag{119.4}
$$

Here $\mathrm e$ is the exponential constant. This bound uses the entire
form, including its source summand, rather than a killed or punctured-core
substitute. On any bounded smooth annulus $D$ with $\overline D\subset M$,
Theorem 115.2 bounds $h$ and $h^{-1}$. Formula (115.15) bounds the weak
derivatives $X_1v_n,X_2v_n,X_3v_n,\partial_wv_n$ there. In the original
coordinates, $\partial_x=X_1$, $\partial_z=X_3$ and
$\partial_y=X_2-x\partial_w$; boundedness of $x$ on $D$ and $a,\eta>0$
therefore give a uniform ordinary $H^1(D)$ bound, exactly the local
ellipticity of (115.10) and (118.9)–(118.10).

Classical local Rellich compactness gives precompactness in $L^2(D)$,
hence locally in $L^2(m)$ by the bounds on $h$. Exhaust $M$ by compact
annuli $C_R=\{1/R\le|x|\le R\}$, each contained in a slightly larger
smooth punctured annulus. A diagonal subsequence has a local $L^2(m)$
limit $v$, with $0\le v\le1$ by a further almost-everywhere subsequence.
Because $m$ is finite and $m(\{e\})=0$,

$$
m(G\setminus C_R)\longrightarrow0,\qquad
\int_{G\setminus C_R}|v_n-v|^2\,dm\le m(G\setminus C_R).
\tag{119.5}
$$

The tails here include both the shrinking source neighborhood and the
large-radius region. Local convergence and (119.5) give global strong
$L^2(m)$ convergence along this subsequence. Bounded linearity of
$T_\Delta$ already gives $v_n\rightharpoonup T_\Delta u$ in $L^2(m)$,
so the strong limit is $T_\Delta u$. Every subsequence admits such a
strongly convergent further subsequence, and every strong cluster limit
has this same value. If the whole sequence failed to converge strongly,
a subsequence at a fixed positive distance from that value would
contradict this property. Thus

$$
u_n\overset{w^*}{\longrightarrow}u,\quad 0\le u_n\le1
\quad\Longrightarrow\quad
T_\Delta u_n\longrightarrow T_\Delta u\quad\hbox{in }L^2(m).
\tag{119.6}
$$

This is compactness on the bounded emission order interval. It asserts
no compactness of $T_\Delta$ on the full $L^2$ unit ball and uses no global
heat-kernel premise.

For coordinatewise weak-star convergence $f_n\to f$ in the emission
simplex, split the actual pair-coordinate difference as

$$
\begin{aligned}
\nu_{f_n}(y,z)-\nu_f(y,z)
 &=\int_G g_t f_{n,y}\,T_\Delta(f_{n,z}-f_z)\,dm\\
 &\quad+\int_G g_t(f_{n,y}-f_y)\,T_\Delta f_z\,dm.
\end{aligned}
\tag{119.7}
$$

The first term is bounded in absolute value by
$\|g_t\|_2\|T_\Delta(f_{n,z}-f_z)\|_2$, which tends to zero by (119.6).
Here $g_t\in L^2(m)$ is precisely the actual source density of (117.2).
The second term tends to zero against the fixed $L^1(m)$ test
$g_tT_\Delta f_z$, since $0\le T_\Delta f_z\le1$.
Thus the pair map and the finite sum $d_f$ are continuous for this
convergence; two merely weak-star limits have not been multiplied.

Consider now the simplex $\mathcal S$ of four $L^\infty(m)$ classes with
$0\le f_y\le1$ and $\sum_y f_y=1$ almost everywhere. Positivity and the
sum constraint are weak-star closed, as seen by testing against $L^1(m)$
functions. Classical Banach–Alaoglu makes $\mathcal S$ compact in the
finite product weak-star topology. The finite Borel measure $m$ on
$\mathbb R^4$ has separable $L^1(m)$, so this compact space is metrizable.
Consequently the sequential continuity just proved is continuity on
$\mathcal S$, and its pair-law image is compact.

Every class tuple in $\mathcal S$ has Borel representatives. Combine
their exceptional Borel $m$-null sets, including the failures of the
bounds and sum constraint, into one set and assign a fixed label there.
The resulting tuple belongs to the exact pointwise class $\mathcal F$.
Both positive-time marginals are absolutely continuous with respect to
$m$, with densities $g_t,g_{t+\Delta}$ by Theorem 117.2. The probability
that either sampled state lies in this null set is zero, so this repair
preserves the pair law. It asserts nothing about repairing the time-zero
law $\delta_e$. Hence the image is exactly $\mathcal L_{\rm stoch}$.
Its compactness and continuity of total variation give a minimum in
$\mathcal F$ (equivalently, apply (119.7) to a convergent subsequence of
a minimizing sequence).

It remains to approximate every $f\in\mathcal F$ by partitions with the
same law limit. Choose increasing finite Borel partitions $\mathcal P_n$
generating the Borel sigma algebra, for example those generated by the
first $n$ members of a countable Borel generator of $\mathbb R^4$.
On each cell $C$, split it into four Borel pieces $C_y$ with
$m(C_y)=\int_C f_y\,dm$. To justify the splitting directly, every Borel
remainder $E$ has continuous cumulative mass
$s\mapsto m(E\cap\{x_1\le s\})$, since $m=h^2\mu$ is absolutely
continuous with respect to Lebesgue measure and coordinate hyperplanes
have zero mass. Its endpoint limits are zero and $m(E)$, so it attains
each intermediate mass. Remove the required pieces successively, using
an empty or full remainder at the endpoints. The sum constraint supplies
exactly the remaining mass for the last piece.

Let $A_{n,y}$ be the union of the $y$-pieces over the finitely many cells.
These form a Borel partition of all $G$. For every $\mathcal P_n$-simple
test $\psi$, the prescribed cell integrals give
$\int\psi(\mathbf1_{A_{n,y}}-f_y)\,dm=0$. For any $\phi\in L^1(m)$,
choose $\mathcal P_n$-simple $\psi_n$ with $\|\phi-\psi_n\|_1\to0$.
Such approximants exist because the partitions refine and generate the
sigma algebra: their simple functions are $L^1$ dense. Then

$$
\left|\int_G\phi(\mathbf1_{A_{n,y}}-f_y)\,dm\right|
 \le\|\phi-\psi_n\|_1\longrightarrow0.
\tag{119.8}
$$

Thus the indicator tuples converge coordinatewise weak-star to $f$.
Use this same partition at both epochs. Formula (119.7) gives entrywise
$\nu_{\mathbf1_{A_n}}\to\nu_f$ and $d_{\mathbf1_{A_n}}\to d_f$.
It follows that $\mathcal L_{\rm stoch}\subset\overline{\mathcal L_{\rm det}}$;
the reverse inclusion follows from inclusion of deterministic tuples and
the compactness, hence closedness, of $\mathcal L_{\rm stoch}$.
Equivalently, $D_{\rm det}\le d_f$ for every $f\in\mathcal F$, while
$D_{\rm stoch}\le D_{\rm det}$ follows from inclusion. This proves the
equality in (119.3). The lower bound is exactly Theorem 118.3, unchanged.

The splitting used here is classical atomless splitting; finite-linear
background is [Dvoretzky–Wald–Wolfowitz, §3, Theorem 4 and Lemma 2](https://msp.org/pjm/1951/1-1/pjm-v1-n1-p06-s.pdf).
It preserves the displayed cell integrals, not the quadratic pair law
exactly. Fractional-partition antecedents are
[Borgs–Chayes–Lovász–Sós–Vesztergombi, §4.1.2, Lemmas 4.2–4.3 and Example 4.4](https://annals.math.princeton.edu/wp-content/uploads/annals-v176-n1-p02-p.pdf)
and [Borgs–Chayes–Cohn–Zhao, §5.3, Proposition 5.5 and Lemmas 5.7–5.8](https://arxiv.org/pdf/1408.0744v1).
Their fractional labels, ordinary partitions and two-point integrals
correspond to $f$, $\mathbf1_A$ and $\nu_f$ here, but their symmetric
graphon settings do not replace the nonstationary weighting by the
actual $g_t$ or the full-form smoothing bridge (119.4)–(119.7).
Banach–Alaoglu, local Rellich and splitting are credited intermediate
methods in this source-specific deduction, not new general compactness
or exact quadratic purification theorems.

Finally the indicator tuples are not weak-star closed: applying the
same splitting construction to $f_0=f_1=1/2$, $f_3=f_B=0$ gives partitions
converging to a non-indicator tuple. Compactness of the stochastic image
and the approximation above therefore do not establish that a minimizing
law has an indicator representative. Nonclosedness alone also does not
exclude such a representative for the exact target (119.2). Deterministic
attainment, and the universal conjunction containing it, remain unresolved.
$\square$

## 追加锚（本行以下为增补区）

## 120. A positive quadratic direction on every original emission overlap

**Definition 120.1 (the unchanged source and the constrained quadratic direction).**
Fix arbitrary original $a,\eta,t,\Delta>0$. Retain the entire source model
of Definitions 115.1, 116.1, 117.1, 117.3, 118.1 and 119.1. In particular,

$$
\begin{gathered}
G=H^1\times\mathbb R,\qquad
(x,y,z,w)(x',y',z',w')
 =(x+x',y+y',z+z',w+w'+xy'),\\
e=(0,0,0,0),\qquad d\mu=dx\,dy\,dz\,dw,\qquad
M=G\setminus\{e\},\\
X_1=\partial_x,\quad X_2=\partial_y+x\partial_w,\quad
X_3=\partial_z,\quad L=-\sum_{i=1}^3X_i^2,\quad
L\Gamma=\delta_e,\\
S=(aL+\eta D_w^2-16\sqrt{a\eta}\,\Gamma)|_{C_c^\infty(M;\mathbb C)},\\
H=H_{\rm end},\qquad
D(H)=\{u\in D(S^*):A(u)=\rho C(u)\},\qquad Hu=S^*u.
\end{gathered}
$$

Here $\Gamma$ is the original unit-source field, and $h$ is the same
coefficient-positive normalized zero vector of (115.2), smooth and strictly
positive on $M$. Keep $F$, its form $(\overline q_c,\mathcal Q_c)$ and the
full complex form and source summand of (115.15):

$$
\begin{gathered}
D(H^{1/2})=\mathcal Q_c\dotplus\mathbb Ch,\qquad
q_H[y+ch]=\overline q_c[y]
 \quad(y\in\mathcal Q_c,\ c\in\mathbb C),\\
m=h^2\mu,\qquad U_hv=hv,\qquad
K=U_h^{-1}HU_h,\qquad T_s=e^{-sK},\\
\mathscr V=\mathscr V_0\dotplus\mathbb C1,\qquad
\mathscr E[u,v]=\int_M\left(
 a\sum_{i=1}^3\overline{X_i u}X_i v
 +\eta\overline{\partial_wu}\partial_wv\right)dm.
\end{gathered}
$$

The operator domain is exactly (115.17). The conservative diffusion $Z$
starts at $e$ at original time zero, and $T_s$ uses its original clock.
Use its actual density $g_t$ from (117.2), so
$\mathbb P_e(Z_t\in dp)=g_t(p)m(dp)$, $g_t\in L^2(m)$,
$g_t>0$ $m$-almost everywhere and $\int g_t\,dm=1$.
For real bounded Borel $u,w$ put

$$
Q(u,w)=\int_G g_t u\,T_\Delta w\,dm.
$$

For every pointwise Borel emission tuple $f\in\mathcal F$ of (117.9),
with $f_y:G\to[0,1]$ and $\sum_{y\in\mathcal A}f_y(p)=1$ for every
$p\in G$, where $\mathcal A=\{0,1,3,B\}$, and every $\kappa>0$, write

$$
E=\{p\in G:f_1(p)\ge\kappa,\ f_3(p)\ge\kappa\}.
$$

Thus $Q(f_y,f_z)=\nu_f(y,z)$ is exactly (118.2), with the same tuple at
both epochs, fresh read noises conditional on the entire source path,
and unchanged source evolution. In general $Q$ need not be symmetric.
Its values are finite, since the Markov contraction and the unit mass of
$g_t$ give $|Q(u,w)|\le\|u\|_\infty\|w\|_\infty$.

**Theorem 120.2 (a positive direction satisfying all eight pair-law constraints).**
For every original $a,\eta,t,\Delta>0$, every pointwise Borel tuple
$f\in\mathcal F$ of Definition 117.3, and every $\kappa>0$ with $m(E)>0$,
there is a bounded real Borel function $v:G\to\mathbb R$ such that

$$
\begin{gathered}
v(p)=0\quad\text{for every }p\in G\setminus E,\\
Q(v,f_z)=Q(f_z,v)=0\quad\text{for every }z\in\{0,1,3,B\},\qquad
Q(v,v)>0.
\tag{120.3}
\end{gathered}
$$

All eight equalities hold for this one function, the actual source-start
$g_t$ and the original-clock $T_\Delta$.

**Proof.** We first identify a symmetry of the full endpoint. Use the
Jacobian-one coordinates $(x,y,z,\xi)$ with $\xi=w-xy/2$. Then

$$
X_1=\partial_x-\frac y2\partial_\xi,\qquad
X_2=\partial_y+\frac x2\partial_\xi,\qquad
X_3=\partial_z,\qquad \partial_w=\partial_\xi.
\tag{120.4}
$$

Let $R_\theta$ rotate $(x,y)$ through $\theta$, leaving $z,\xi$ fixed,
and let its action on functions be pullback. It preserves $\mu$, $e$,
$L$ and $\partial_w^2$. The original representation
$\Gamma(p)=\int_0^\infty h_s(p)\,ds$ in
[(82.8)](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md#82-rank-three-transport-carrier-point-source-stability-and-target-fibre-defect)
uses the free heat densities of $L$. Its classical supplier, as in
Proposition 82.4, is Folland, [*Subelliptic estimates and function spaces
on nilpotent Lie groups*, Theorem 3.1 and Proposition 3.17 at $\alpha=2$](https://doi.org/10.1007/BF02386204).
That free semigroup commutes with
these rotations and its source $e$ is fixed, so its densities, and hence
$\Gamma$, are invariant. Thus rotations preserve the punctured symmetric
operator $S$, its adjoint and its Friedrichs operator $F$, including
$\mathcal Q_c$ and $\overline q_c$.

The supplied identity $\ker S^*=\mathbb Ch$, recalled in Definition 114.1
from (112.1), implies $R_\theta h\in\mathbb Ch$. Rotation preserves
reality, positivity and unit norm. The positive unit vector in this
one-dimensional line is unique, so $R_\theta h=h$. The entire domain
$\mathcal Q_c\dotplus\mathbb Ch$ and the full form
$q_H[y+ch]=\overline q_c[y]$ are therefore rotation invariant. The
closed-form representation of the operator shows that the actual $H$
commutes with rotations. Since $h$ is invariant, so do $K$ and $T_s$ on
$L^2(m)$. This uses the source summand and fixes the actual extension.

Rotations also preserve $\mathscr V_0$, fix $1$ and preserve
$\operatorname{tr}(v_0+c)=c$ in (116.1). Applying (117.2) to a rotated
input and using Riesz uniqueness proves $R_\theta g_t=g_t$ in $L^2(m)$.
The initial law in this argument is still the source law at $e$.

We next obtain the local regularity needed to evaluate the full
semigroup off the source. On each relatively compact neighborhood in
$M$, $h$ and $\Gamma$ are smooth, $h$ is bounded above and below by
positive constants, and the principal matrix $\mathsf A$ has symbol

$$
\langle\mathsf A(p)\zeta,\zeta\rangle
 =a\bigl[\zeta_x^2+(\zeta_y+x\zeta_w)^2+\zeta_z^2\bigr]
   +\eta\zeta_w^2.
\tag{120.5}
$$

It is strictly positive for nonzero $\zeta$ and uniformly positive on
compact subsets. The full form puts $D(K)$ in $H^1_{\rm loc}(M)$.
Testing its operator identity against punctured smooth functions gives,
in the original coordinates, the weak equation

$$
-\operatorname{div}(h^2\mathsf A\nabla u)=h^2Ku
\quad\text{on }M,\qquad u\in D(K).
\tag{120.6}
$$

The interior divergence-form estimates used here are John K. Hunter,
[*Chapter 4: Elliptic PDEs*, Theorems 4.27 and 4.28, printed pp. 112 and 114](https://www.math.ucdavis.edu/~hunter/pdes/ch4.pdf).
Their coefficient matrix is $h^2\mathsf A$ and their right-hand side is
$h^2Ku$ on nested punctured neighborhoods. Both the smooth coefficient
hypotheses and uniform ellipticity hold there. For $u\in D(K^2)$,
apply the interior $H^2$ estimate first to $Ku$, whose right-hand side
is $h^2K^2u$, and then the $H^4$ estimate to $u$, whose right-hand side
$h^2Ku$ is now locally $H^2$. Local weighted and unweighted norms are
equivalent. The local $H^1$ terms are controlled by the full energy
$\mathscr E[w,w]=\langle w,Kw\rangle_m$ for $w=u,Ku$.
Consequently, for each compact $C\Subset M$, nested relatively compact
neighborhoods give a finite constant $C_C$ with

$$
\|u\|_{H^4(C)}
 \le C_C\sum_{j=0}^2\|K^ju\|_{L^2(m)},\qquad u\in D(K^2).
\tag{120.7}
$$

Here the norm on $C$ means restriction from such a neighborhood.
The same interior estimates at higher orders give arbitrary local
Sobolev regularity for vectors in all the domains $D(K^N)$.
There is no assertion about extending (120.6) through $e$.

Classical Sobolev embedding in four dimensions sends local $H^4$ into
local $C^1$. The spectral theorem for the nonnegative self-adjoint $K$
gives bounded maps $T_s:L^2(m)\to D(K^N)$ for every $s>0$ and integer
$N\ge0$, since $\lambda^Ne^{-s\lambda}$ is bounded on $[0,\infty)$.
Thus $T_su$ has a smooth representative on $M$. On the real Hilbert
space, (120.7) and the Riesz representation theorem give vectors
$k_{s,p}\in L^2(m;\mathbb R)$ such that

$$
(T_su)(p)=\langle k_{s,p},u\rangle_m
\quad(p\in M,\ u\in L^2(m;\mathbb R)).
\tag{120.8}
$$

The local $C^1$ bound is uniform for $\|u\|_2\le1$, so
$p\mapsto k_{s,p}$ is locally norm-continuous. Also
$g_t=T_{t/2}g_{t/2}$ by (117.3), hence $g_t$ has a smooth representative
on $M$. Its rotation invariance is pointwise there: for any fixed
rotation the continuous difference vanishes almost everywhere, and
$m$ has full support on $M$.

Define on $M\times M$

$$
p_\Delta(p,q)=\langle k_{\Delta/2,p},k_{\Delta/2,q}\rangle_m.
\tag{120.9}
$$

This is continuous and symmetric. Self-adjointness and the semigroup
identity give $T_{\Delta/2}k_{\Delta/2,p}=k_{\Delta,p}$ in $L^2(m)$.
Evaluating the left side at $q$ by (120.8) shows that its continuous
representative is $p_\Delta(p,q)$. Thus (120.8) also yields

$$
(T_\Delta u)(p)=\int_M p_\Delta(p,q)u(q)\,dm(q),
\qquad p\in M,\quad u\in L^2(m;\mathbb R).
\tag{120.10}
$$

In particular the formula applies to the bounded compactly supported
functions below. It requires no value of this kernel at $e$, which has
zero $m$-measure.

For distinct $p_1,\ldots,p_n\in M$, the matrix
$(p_\Delta(p_i,p_j))_{i,j=1}^n$ is strictly positive definite. To see
strictness, a zero Gram quadratic form for real coefficients $c_i$
would give $\sum_i c_i k_{\Delta/2,p_i}=0$. The functional
$\ell(u)=\sum_i c_i u(p_i)$ is continuous on $D(K^2)$ in its graph
norm by (120.7), and would vanish on $T_{\Delta/2}(L^2(m;\mathbb R))$.
This range is graph-norm dense in $D(K^2)$: for any real $u\in D(K^2)$,
its spectral truncations satisfy

$$
u_N=\mathbf1_{[0,N]}(K)u\longrightarrow u\quad\text{in }D(K^2),
\qquad
u_N=T_{\Delta/2}\bigl(e^{(\Delta/2)K}u_N\bigr),
\tag{120.11}
$$

where the parenthesized vector is in $L^2(m)$ by the spectral cutoff.
Thus $\ell$ vanishes on $D(K^2)$. Every punctured smooth compactly
supported function belongs to $D(K^N)$ for all $N$: multiplication by
$h$ sends it into the original punctured core, and the smooth local
expression for $K$ preserves smooth compact support in $M$. Induction
gives the asserted domain membership. Disjoint smooth bump functions
with value one at their respective $p_i$ force $c_i=0$ for every $i$.
This proves the finite Gram strictness for the actual full semigroup.

We now choose points inside the given Borel overlap. Let $E^*$ be the
Lebesgue density points belonging to $E\cap M$, using the coordinates
$(x,y,z,\xi)$. Local equivalence of $m$ and Lebesgue measure and the
Lebesgue density theorem give $m(E\setminus E^*)=0$. Remove also the
axis $x=y=0$, a null set. In cylindrical coordinates
$x=r\cos\theta$, $y=r\sin\theta$ with $r>0$, the measure is

$$
dm=h(r,z,\xi)^2r\,dr\,d\theta\,dz\,d\xi.
\tag{120.12}
$$

Fubini's theorem gives a positive-measure set of bases $(r,z,\xi)$
whose angular slice of $E^*$ has positive one-dimensional measure.
The smooth rotation-invariant representative of $g_t$ depends only on
this base. Since $g_t>0$ $m$-almost everywhere, one can choose such a
base with $g_t=c>0$. Its slice contains nine distinct angles. The
corresponding distinct points $p_1,\ldots,p_9$ of $E^*$ have the exact
same actual density value $g_t(p_i)=c$. This uses no regularity of the
emissions or of the boundary of $E$.

Take small pairwise disjoint coordinate balls $B_i(\varepsilon)$ about
these points, with closures in $M$, and put

$$
A_i(\varepsilon)=E\cap B_i(\varepsilon),\qquad
\phi_i=\frac{\mathbf1_{A_i(\varepsilon)}}{m(A_i(\varepsilon))}
\quad(1\le i\le9).
\tag{120.13}
$$

The density-point property makes every denominator positive for all
sufficiently small $\varepsilon>0$. Each $\phi_i$ is a pointwise
defined bounded real Borel function zero outside $E$. Write
$B_{ij}(\varepsilon)=\tfrac12[Q(\phi_i,\phi_j)+Q(\phi_j,\phi_i)]$.
By (120.10), kernel symmetry and Fubini on these compact neighborhoods,

$$
\begin{aligned}
B_{ij}(\varepsilon)
 &=\frac{1}{m(A_i(\varepsilon))m(A_j(\varepsilon))}
   \int_{A_i(\varepsilon)\times A_j(\varepsilon)}
   \frac{g_t(p)+g_t(q)}2\,p_\Delta(p,q)\,dm(p)dm(q)\\
 &\longrightarrow c\,p_\Delta(p_i,p_j)
 \qquad(\varepsilon\downarrow0).
\end{aligned}
\tag{120.14}
$$

Indeed the integrand is continuous on the fixed compact punctured
neighborhoods, and these are normalized averages over sets shrinking
to $(p_i,p_j)$. Local boundedness justifies the integrals, while the
original definition of $Q$ is finite on all bounded inputs. The limit
matrix is strictly positive definite by the preceding Gram argument
and $c>0$. Positive definiteness is open for real symmetric finite
matrices, so fix one sufficiently small $\varepsilon$ for which
$B(\varepsilon)$ is strictly positive definite. For every nonzero
$b\in\mathbb R^9$ this gives

$$
Q\left(\sum_{i=1}^9b_i\phi_i,\sum_{i=1}^9b_i\phi_i\right)
 =b^{\mathsf T}B(\varepsilon)b>0.
\tag{120.15}
$$

Finally consider the single real linear map

$$
\mathbb R^9\longrightarrow\mathbb R^8,\qquad
b\longmapsto
\left(Q\left(\sum_i b_i\phi_i,f_z\right),
      Q\left(f_z,\sum_i b_i\phi_i\right)\right)_{z\in\mathcal A}.
\tag{120.16}
$$

Its entries are finite by the bound in Definition 120.1. Rank-nullity
gives a nonzero vector $b$ in its kernel, even if some rows are
dependent. Set $v=\sum_i b_i\phi_i$. This is one bounded real Borel
function vanishing at every point outside $E$. All eight required
constraints hold simultaneously by (120.16), and (120.15) gives
$Q(v,v)>0$. The parameters, emission tuple and $\kappa$ were arbitrary,
which proves exactly (120.3). $\square$

**Definition 120.17 (supplier correspondence and scope).** Theorem 120.2
is a repo-derived source-specific synthesis using established methods.
Its source suppliers are the original heat-integral field (82.8), the
one-dimensional maximal zero line recalled in Definition 114.1, the
positive normalized $h$ and full complex form and selector of
Theorems 115.2–115.3, the trace of (116.1), and the actual source-start
density and semigroup identity of Theorem 117.2. Hunter's interior
estimates supply (120.7) with coefficient $h^2\mathsf A$ and
right-hand side $h^2Ku$; classical Sobolev embedding, the spectral
and Riesz representation theorems, Lebesgue differentiation, Fubini,
finite-matrix continuity and rank-nullity supply the indicated
intermediate steps within this proof. These methods are not asserted
as new standalone general theorems, and no worldwide-priority claim
is made for their source-specific combination.

The conclusion is the existence of the direction (120.3) on the
specified $1/3$ overlap, with no openness assumption on that Borel
set. It supplies the positive-direction hypothesis for a conditional
$1/3$ second-variation argument; no additional hypotheses or
conclusions of such an argument are established here. In particular,
deterministic attainment in Theorem 119.2 remains unresolved, as do
the both-nonnegative-diagonal-residual case and the other label-overlap
cases beyond this positive-direction assertion. No effective bound on the witness
norm, the localization radius or the time parameters is part of the
conclusion. The proof retains the nonstationary $g_t$, actual source
extension and clock throughout; its finite positive matrix does not
assert global positivity of $Q$ or compactness of $T_\Delta$ on the
full $L^2$ unit ball. No physical realization follows from this
mathematical direction.

## 追加锚（本行以下为增补区）

## 121. An optimal original passive pair without simultaneous 1/3 emission

**Definition 121.1 (the original family and the secondary objective).**
Fix arbitrary $a,\eta,t,\Delta>0$ and arbitrary
$p_{\rm N},q_{\rm N},r_{\rm N}>0$ with
$p_{\rm N}+q_{\rm N}+r_{\rm N}<1$.
Use exactly Definitions 117.1, 117.3, 117.4, 118.1 and 119.1, with their
suppliers in §§115–116. More explicitly, the carrier is the original
four-coordinate $G=H^1\times\mathbb R$ with product (115.1), source
$e=(0,0,0,0)$, raw Haar measure $d\mu=dx\,dy\,dz\,dw$ and the original
unit-source field $L\Gamma=\delta_e$. The source coefficients remain
$a,\eta$ and $g_c=16\sqrt{a\eta}$. The extension is exactly
$H=H_{\rm end}$ with $D(H)=\{u\in D(S^*):A(u)=\rho C(u)\}$,
$Hu=S^*u$, and the coefficient-positive normalized $h$ and
$\rho=A(h)/C(h)$ of (115.2). Retain $m=h^2\mu$, $m(G)=1$,
$U_hv=hv$, $K=U_h^{-1}HU_h$, the entire complex form (115.15),
including $\mathscr V=\mathscr V_0\dotplus\mathbb C1$ and
$D(H^{1/2})=\mathcal Q_c\dotplus\mathbb Ch$, and the actual operator
domain (115.17). The semigroup is $T_s=e^{-sK}$ in the original clock;
$Z$ is its actual conservative diffusion started at $e$ at time zero.
The lead-in $t$ uses that same evolution, with actual density $g_t$ of
Theorem 117.2, rather than an invariant initial distribution.

The native parameters and target retain precisely (117.10)–(117.11):

$$
\begin{gathered}
s_{\rm N}=p_{\rm N}+q_{\rm N},\quad
 a_{\rm N}=1-s_{\rm N},\quad b_{\rm N}=1-r_{\rm N},\quad
 c_{\rm N}=1-s_{\rm N}-r_{\rm N},\\
P_{\rm N}=\begin{pmatrix}
c_{\rm N}&p_{\rm N}&0&q_{\rm N}&r_{\rm N}\\
q_{\rm N}&a_{\rm N}&p_{\rm N}&0&0\\
0&q_{\rm N}&a_{\rm N}&p_{\rm N}&0\\
p_{\rm N}&0&q_{\rm N}&a_{\rm N}&0\\
r_{\rm N}&0&0&0&b_{\rm N}
\end{pmatrix},\qquad \pi=\tfrac15(1,1,1,1,1),\\
\chi(0)=0,\quad\chi(1)=1,\quad\chi(3)=3,\quad
\chi(2)=\chi(4)=B,\\
\Pi_{\rm N}(y,z)=\frac15
 \sum_{\substack{i:\chi(i)=y\\j:\chi(j)=z}}(P_{\rm N})_{ij}.
\end{gathered}
\tag{121.1}
$$

In particular both $p_{\rm N}=q_{\rm N}$ and
$r_{\rm N}=s_{\rm N}$ remain permitted. Let $\mathcal A=\{0,1,3,B\}$
and let $\mathcal F$ be the class of all Borel tuples
$f_y:G\to[0,1]$ with $\sum_{y\in\mathcal A}f_y(x)=1$ at every point.
The same tuple is read at $t$ and $t+\Delta$, using fresh read noises
independent conditional on the entire $Z$ path, leaving the source and
its successors unchanged and retaining all four outcomes, exactly as
in Definitions 117.3 and 118.1. There is no retained controller, shared
read noise, killing, postselection, reset or change of clock or extension.
For real bounded Borel inputs use precisely the ordered bilinear form
of Definition 120.1:

$$
\begin{gathered}
Q(u,w)=\int_Gg_t u\,T_\Delta w\,dm,\qquad
\nu_f(y,z)=\mathbb E_e[f_y(Z_t)f_z(Z_{t+\Delta})]=Q(f_y,f_z),\\
d(\nu)=\frac12\sum_{y,z\in\mathcal A}|\nu(y,z)-\Pi_{\rm N}(y,z)|,
\qquad d_f=d(\nu_f),\\
\mathcal M=\{\nu\in\mathcal L_{\rm stoch}:d(\nu)=D_{\rm stoch}\},
\qquad C(\nu)=\nu(1,3)+\nu(3,1).
\end{gathered}
\tag{121.2}
$$

Here $\mathcal L_{\rm stoch}$, $D_{\rm stoch}$ and $D_{\rm det}$ are
exactly (119.1). The functional $C$ measures two temporal pair entries;
it is distinct from simultaneous overlap of the two emission functions
at a single source point.

**Theorem 121.2 (existence of an overlap-free stochastic optimum).**
For every original parameter tuple of Definition 121.1, there exists
$f^\circ\in\mathcal F$ such that

$$
\begin{gathered}
d_{f^\circ}=D_{\rm stoch}=D_{\rm det}\ge\delta>0,\qquad
C(\nu_{f^\circ})=\min_{\nu\in\mathcal M}C(\nu),\\
m\bigl(\{x:f^\circ_1(x)>0\ \text{and}\ f^\circ_3(x)>0\}\bigr)=0.
\end{gathered}
\tag{121.3}
$$

Thus minimizing total variation first and $C$ second yields an optimal
Borel stochastic tuple with no positive-measure $1/3$ emission overlap.
The constant $\delta$ is the unchanged source-dependent lower bound of
Theorems 118.3 and 119.2.

**Proof.** Theorem 119.2 gives a nonempty compact
$\mathcal L_{\rm stoch}$ and attainment of $D_{\rm stoch}$.
Since $d$ is continuous on the finite-dimensional pair-law simplex,
$\mathcal M$ is nonempty and compact. The continuous linear functional
$C$ therefore has a minimum there. Choose a minimizing law $\nu$ and
an exact pointwise Borel simplex representative $f\in\mathcal F$ with
$\nu_f=\nu$, as supplied by Theorem 119.2. Its representative repair
preserves this pair law because both positive-time source marginals
$g_t m$ and $g_{t+\Delta}m$ are absolutely continuous with respect to
$m$. This neither changes the initial law $\delta_e$ nor prepares a
new state at either read. No convexity of $\mathcal M$ is needed.

Suppose the Borel set $E_0=\{f_1>0,\ f_3>0\}$ has positive $m$-measure.
Since

$$
E_0=\bigcup_{k\ge1}E_k,\qquad
E_k=\{f_1\ge1/k,\ f_3\ge1/k\},
$$

some $E_k$ has positive measure. Set $\kappa=1/k$ and apply Theorem 120.2
to this very $f$ and $E_k$. It supplies one bounded real Borel $v$ with
pointwise support in $E_k$, satisfying

$$
Q(v,f_z)=Q(f_z,v)=0\quad(z\in\mathcal A),\qquad q:=Q(v,v)>0.
\tag{121.4}
$$

Both $f_1$ and $f_3$ are nonzero nonnegative $L^2(m)$ functions.
The positivity improvement used in Theorem 117.2 gives
$T_\Delta f_1>0$ and $T_\Delta f_3>0$ almost everywhere, and
$g_t>0$ almost everywhere. Integrating over the positive-measure
supports of $f_1$ and $f_3$, respectively, proves
$\nu(1,3)=Q(f_1,f_3)>0$ and $\nu(3,1)=Q(f_3,f_1)>0$.
Choose a finite pointwise bound $B_v>0$ for $|v|$, and then
$\varepsilon>0$ small enough that

$$
\varepsilon B_v\le\kappa,\qquad
0<\tau:=\varepsilon^2q<\min\{\nu(1,3),\nu(3,1)\}.
\tag{121.5}
$$

Define $\widetilde f_1=f_1+\varepsilon v$,
$\widetilde f_3=f_3-\varepsilon v$ and leave $f_0,f_B$ unchanged.
On $E_k$, both altered coordinates are nonnegative by (121.5), and
their sum remains $f_1+f_3\le1$, so each is at most one. Off $E_k$
they are unchanged pointwise. The tuple is Borel and sums to one
everywhere; hence $\widetilde f\in\mathcal F$.

Bilinearity and all eight ordered equalities in (121.4) cancel every
linear term. The quadratic terms change only four entries:

$$
\begin{aligned}
\nu_{\widetilde f}(1,1)&=\nu(1,1)+\tau,&
\nu_{\widetilde f}(3,3)&=\nu(3,3)+\tau,\\
\nu_{\widetilde f}(1,3)&=\nu(1,3)-\tau,&
\nu_{\widetilde f}(3,1)&=\nu(3,1)-\tau.
\end{aligned}
\tag{121.6}
$$

The other twelve entries are unchanged. This expansion uses neither
symmetry of $Q$ nor global positivity of its quadratic form.
The exact target (121.1), equivalently (119.2), has
$\Pi_{\rm N}(1,3)=\Pi_{\rm N}(3,1)=0$.
By (121.5), each of these two absolute residuals decreases exactly by
$\tau$. For either diagonal residual
$R_{ii}=\nu(i,i)-\Pi_{\rm N}(i,i)$, $i\in\{1,3\}$, the elementary
absolute-value calculation is

$$
|r+\tau|-|r|=
\begin{cases}
\tau,&r\ge0,\\
-\tau,&r\le-\tau,\\
2r+\tau,&-\tau<r<0,
\end{cases}
\qquad |r+\tau|-|r|\le\tau.
\tag{121.7}
$$

Consequently, without any differentiation,

$$
\begin{aligned}
2(d_{\widetilde f}-D_{\rm stoch})
 &=\bigl(|R_{11}+\tau|-|R_{11}|\bigr)
   +\bigl(|R_{33}+\tau|-|R_{33}|\bigr)-2\tau\\
 &\le0.
\end{aligned}
\tag{121.8}
$$

Primary minimality forces $d_{\widetilde f}=D_{\rm stoch}$, so
$\nu_{\widetilde f}\in\mathcal M$. But (121.6) gives
$C(\nu_{\widetilde f})=C(\nu)-2\tau<C(\nu)$, contradicting secondary
minimality. In particular, when both diagonal residuals are nonnegative,
including either or both equal to zero, each diagonal change in
(121.7) is exactly $\tau$: the primary value stays fixed and the
secondary value strictly decreases. Thus these residual cases are
included in the same contradiction. It follows that $m(E_0)=0$;
taking $f^\circ=f$ and using (119.3) proves (121.3).
No step divides by $p_{\rm N}-q_{\rm N}$ or
$r_{\rm N}-s_{\rm N}$, so the permitted equalities remain included.
$\square$

**Definition 121.3 (attribution and mathematical scope).**
Theorem 121.2 is a repo-derived application and synthesis of the
source-specific compact attainment in Theorem 119.2 and constrained
positive direction in Theorem 120.2, using the actual entrance density
and positivity improvement of Theorem 117.2. These analytic suppliers
are used with their stated hypotheses and are not reproved here.
Minimizing a continuous secondary objective on a compact set of
primary optima and the scalar absolute-value calculation (121.7) are
standard intermediate ingredients, not new general theorems.
Theorem 119.2 retains its existing Banach–Alaoglu and local Rellich
suppliers and its cited Dvoretzky–Wald–Wolfowitz atomless splitting
and Borgs–Chayes–Lovász–Sós–Vesztergombi and Borgs–Chayes–Cohn–Zhao
fractional-partition antecedents. Those references provide the
intermediate correspondences specified there, not an assumed exact
quadratic purification of this nonstationary pair law. The new
source-specific inference is the secondary-minimum contradiction
(121.6)–(121.8); no worldwide novelty claim is made.

For the existential $1/3$ question, Theorem 121.2 resolves the
both-nonnegative-diagonal-residual possibility left open in Definition
120.17. It does not assert that every primary minimizer is overlap-free,
that other label overlaps vanish, or that the selected tuple is an
indicator partition. Equality of deterministic and stochastic infima
continues to be (119.3); deterministic attainment remains unresolved.
Simultaneous emission overlap of measure zero does not assert that
the temporal cross mass $C(\nu_{f^\circ})$ vanishes. No numerical
optimum, effective construction or sample bound is supplied.
The result is an ordinary mathematical consequence of the inherited
source theorems; it supplies no physical realization of the diffusion,
readout or native record law.

## 追加锚（本行以下为增补区）

## 122. Exact deterministic attainment for the original passive pair

**Theorem 122.1 (local infinite negative index and exact purification).**
Fix the original finite positive parameters $a,\eta,t,\Delta>0$ and every
native tuple of Definition 118.1, including the permitted equalities among
its positive entries. Retain exactly Definitions 117.1, 117.3, 117.4, 118.1
and 119.1, with their suppliers in §§115–116: the four-coordinate group
$G=H^1\times\mathbb R$, source $e$, raw Haar measure $\mu$, unit-source
field $\Gamma$, actual selector $A(u)=\rho C(u)$, coefficient-positive
normalized $h$, $m=h^2\mu$, the full complex form, $K=U_h^{-1}HU_h$,
the original-clock semigroup $T_s=e^{-sK}$, and the conservative diffusion
$Z$ started at $e$ at time zero. Let $g=g_t$ be its actual density at
time $t$. The retained extension and full complex form are

$$
\begin{gathered}
D(H^{1/2})=\mathcal Q_c\dotplus\mathbb Ch,\qquad
q_H[y+ch]=\overline q_c[y],\\
m=h^2\mu,\qquad U_hv=hv,\qquad K=U_h^{-1}HU_h,\qquad
T_s=e^{-sK},\\
\mathscr E[u,v]=\int_M\left(
a\sum_{i=1}^3\overline{X_i u}X_i v+
\eta\overline{\partial_wu}\partial_wv\right)dm.
\end{gathered}
\tag{122.1b}
$$

Let $g=g_t$ be the actual density at time $t$ and define, for bounded real
Borel functions,

$$
Q(u,v)=\int_G g(p)u(p)(T_\Delta v)(p)\,dm(p).
\tag{122.1}
$$

Let $\mathcal F$ be all pointwise Borel tuples
$f=(f_y)_{y\in\mathcal A}$ with $0\le f_y\le1$ and
$\sum_yf_y=1$ on $G$. The same tuple is read at $t$ and $t+\Delta$,
with fresh noises independent conditional on the entire path and unchanged
successors. Thus $\nu_f(y,z)=Q(f_y,f_z)$. The unchanged target is

$$
5\Pi_{\rm N}=
\begin{pmatrix}
c_{\rm N}&p_{\rm N}&q_{\rm N}&r_{\rm N}\\
q_{\rm N}&a_{\rm N}&0&p_{\rm N}\\
p_{\rm N}&0&a_{\rm N}&q_{\rm N}\\
r_{\rm N}&q_{\rm N}&p_{\rm N}&a_{\rm N}+b_{\rm N}
\end{pmatrix},
\quad
\begin{gathered}
c_{\rm N}=1-p_{\rm N}-q_{\rm N}-r_{\rm N},\\
a_{\rm N}=1-p_{\rm N}-q_{\rm N},\qquad b_{\rm N}=1-r_{\rm N},
\end{gathered}
\tag{122.1a}
$$

with $p_{\rm N},q_{\rm N},r_{\rm N}>0$ and
$p_{\rm N}+q_{\rm N}+r_{\rm N}<1$, including the permitted equalities.
For $d_f=\frac12\sum_{y,z}|\nu_f(y,z)-\Pi_{\rm N}(y,z)|$, the
deterministic class consists of indicator tuples of Borel partitions.

For every Borel $E\subset G$ with $m(E)>0$, the symmetrized form

$$
Q_E^{\rm sym}(u,v)=\frac{Q(u,v)+Q(v,u)}2,
\qquad u=v=0\quad\text{on }G\setminus E,
\tag{122.2}
$$

has infinite negative index: for every $N\ge1$ there are bounded real
Borel $v_1,\ldots,v_N$, vanishing pointwise outside $E$, for which
$\bigl(Q_E^{\rm sym}(v_i,v_j)\bigr)_{i,j=1}^N$ is negative definite.

Consequently, with $\mathcal A=\{0,1,3,B\}$, the attainable pair-law sets
of Definition 119.1 satisfy

$$
\mathcal L_{\rm det}=\mathcal L_{\rm stoch},
\qquad
D_{\rm det}=D_{\rm stoch},
\tag{122.3}
$$

and the minimum in Theorem 119.2 is attained by one Borel partition
$G=\bigsqcup_{y\in\mathcal A}A_y$, read at both original positive epochs,
with

$$
d_{\mathbf 1_A}=D_{\rm stoch}=D_{\rm det},
\qquad
\mathbf 1_A=(\mathbf 1_{A_0},\mathbf 1_{A_1},
\mathbf 1_{A_3},\mathbf 1_{A_B}).
\tag{122.4}
$$

**Proof.** Write the symmetric coordinates

$$
\xi=w-\frac{xy}{2},\qquad r^2=x^2+y^2,\qquad
\Omega=\{(x,y,z,w):r>0\}\subset M.
\tag{122.5}
$$

The complement of $\Omega$ is $m$-null. Proposition 85.4 of the linked
Continuation III source, in particular (85.12)–(85.14), gives the actual
central transform of the Green field. The heat-kernel formula of
Krötz–Thangavelu–Xu, *The heat kernel transform for the Heisenberg group*,
arXiv:math/0401243v2, §4.1, (4.1.2), with $n=1$, has the same symmetric
coordinate and Fourier normalization. Setting $\tau=\lambda s$ in that
formula and integrating the positive-real-part $s$-integral gives, for
$r>0$,

$$
\Gamma(x,y,z,\xi+xy/2)
 =\frac1{4\pi^2}\int_{\mathbb R}
 \frac{\tau}{\sinh\tau}
 \left[z^2+r^2\tau\coth\tau-4i\tau\xi\right]^{-3/2}d\tau .
\tag{122.6}
$$

Here
$\int_0^\infty s^{-5/2}e^{-D/(4s)}ds=4\sqrt\pi\,D^{-3/2}$ for
$\Re D>0$. Since
$\tau\coth\tau\ge\max(1,|\tau|)$ for real $\tau$, a sufficiently
small complex polydisc about every point of $\Omega$ has a constant $c>0$
for which

$$
\Re\!\left[z^2+(x^2+y^2)\tau\coth\tau-4i\tau\xi\right]
 \ge c\max(1,|\tau|)
\tag{122.7}
$$

uniformly in real $\tau$. The principal power in (122.6) is then
holomorphic and has an integrable majorant independent of the polydisc
parameter. Holomorphic parameter integration proves that the actual
$\Gamma$ is real analytic on $\Omega$.

On $\Omega$, the coefficient matrix of the actual local expression is

$$
\langle\mathsf A(p)\zeta,\zeta\rangle
 =a\bigl[\zeta_x^2+(\zeta_y+x\zeta_w)^2+\zeta_z^2\bigr]
   +\eta\zeta_w^2,
\tag{122.8}
$$

and is uniformly elliptic on compact subsets. The supplied $h$ is smooth
and satisfies the order-two local equation $Sh=0$. Applying
Kotake–Narasimhan, *Regularity theorems for fractional powers of a linear
elliptic operator*, Bull. Soc. Math. France 90 (1962), Theorem 1, p. 451,
to this order-two analytic differential expression makes $h$ analytic on
$\Omega$. Thus

$$
K=-h^{-2}\operatorname{div}(h^2\mathsf A\nabla)
\tag{122.9}
$$

has analytic coefficients there. For $u=T_sv$, spectral calculus gives

$$
\|K^jT_sv\|_{L^2(m)}
 \le \sup_{\lambda\ge0}\lambda^je^{-s\lambda}\,\|v\|_2
 \le \left(\frac{j}{es}\right)^j\|v\|_2.
\tag{122.10}
$$

On every $U\Subset\Omega$, local equivalence of $m$ and Lebesgue
measure gives a bound by $C_U^{j+1}(2j)!$. If $\mathcal K$ denotes the
order-two local differential expression in (122.9), the weak equation and
the interior estimates (120.6)–(120.7), iterated on nested compact subsets,
give the exact distributional correspondence
$K^jT_sv=\mathcal K^j(T_sv)$ on $U$, together with the displayed local
Sobolev bounds. Thus these spectral powers are the corresponding local
differential iterates. This is the required Kotake–Narasimhan hypothesis;
no global self-adjoint extension or spectral gap is used in this local step.
Therefore

$$
T_sv\text{ is real analytic on }\Omega\quad(s>0),
\tag{122.11}
$$

and in particular $g=T_{t/2}g_{t/2}$ is analytic there. The rotation
invariance of $\Gamma,h,K,T_s$ established in §120 also gives rotation
invariance of $g$.

Set $s=\Delta/2$ and let
$\mathcal H_s=\operatorname{Ran}T_s$ with
$\|T_sv\|_{\mathcal H_s}=\|v\|_{L^2(m)}$. The evaluation construction of
§120 identifies its reproducing kernel on $\Omega$ with
$p_\Delta$, and the strict finite-Gram positivity there makes this kernel
nonsingular. Suppose that the negative index of $Q_E^{\rm sym}$ were
finite, equal to $\kappa$. Replace $E$ by a positive-measure relatively
compact subset of $E\cap\Omega$, and then by its Lebesgue density points
$E^*$ in the coordinates (122.5). For distinct $p_i\in E^*$, the
normalized indicators

$$
\phi_{i,\varepsilon}
 =\frac{\mathbf1_{E\cap B(p_i,\varepsilon)}}
        {m(E\cap B(p_i,\varepsilon))}
\tag{122.12}
$$

have symmetric $Q$-Gram matrices converging to

$$
\bigl(s_g(p_i,p_j)\bigr)_{i,j},\qquad
s_g(p,q)=\frac{g(p)+g(q)}2p_\Delta(p,q).
\tag{122.13}
$$

This is the density-point continuity argument of (120.13)–(120.14), so every
finite point Gram matrix in (122.13) has at most $\kappa$ negative squares.

Define the real analytic Cayley transform

$$
b=\frac{g-1}{g+1}.
\tag{122.14}
$$

Since $g\ge0$, $b$ is bounded and $g+1>0$. The exact identity

$$
s_g(p,q)=\frac{(g(p)+1)(g(q)+1)}4
       \bigl(1-b(p)b(q)\bigr)p_\Delta(p,q)
\tag{122.15}
$$

shows that the finite Gram matrices of $s_g$ and of
$(1-b(p)b(q))p_\Delta(p,q)$ have the same inertia. Every function in
$\mathcal H_s$, and every member of
$\mathcal H_s\mathcal H_s+\mathcal H_s\mathcal H_s$, is real analytic on
the connected set $\Omega$ by (122.11). The zero set of a nonzero real
analytic function on a connected open set is null; see Mityagin, *The zero
set of a real analytic function*, arXiv:1512.07276v1, Proposition 0.
Hence $E^*$ is a uniqueness set for both classes.

We now apply Agler–Young, *Functions which are almost multipliers of Hilbert
function spaces*, arXiv:math/9605224v1, Theorem 2.1, p. 11, to the complex
RKHS obtained by complexifying $\mathcal H_s$ and restricting it to
$E^*$. The real Gram bound is the same Hermitian negative-square bound,
with $m=\kappa$ in that theorem. Its nonsingular-kernel and two uniqueness
set hypotheses are exactly those just established. It yields a closed
finite-codimensional $W\subset\mathcal H_s$ and a bounded map
$L:W\to\mathcal H_s$ satisfying $Lu=bu$ on $E^*$. Both sides are
analytic on $\Omega$, so uniqueness extends this equality to all of
$\Omega$.

Consider the actual multiplication domain

$$
D=\{u\in\mathcal H_s:bu\in\mathcal H_s\}.
\tag{122.16}
$$

It contains $W$, hence is closed and finite codimensional. Point
evaluations in the RKHS show that its multiplication map has closed graph,
so it is bounded. The pullbacks $R_\theta$ form a strongly continuous
unitary representation of the circle on $\mathcal H_s$, commute with
$K$, and preserve $b$; consequently $D$ and $D^\perp$ are rotation
invariant. The finite-dimensional circle representation on $D^\perp$
contains only finitely many integer angular characters. Choose an integer
$\ell$ absent from that finite list. The corresponding angular sector
$\mathcal H_{s,\ell}$ is nonzero, since it contains the heat image of a
nonzero smooth compact-core function of angular character $\ell$, and it is
contained in $D$. If $K_\ell$ is the
self-adjoint restriction of $K$ to the corresponding $L^2(m)$ sector,

$$
B_\ell=e^{sK_\ell}M_be^{-sK_\ell}
\tag{122.17}
$$

is bounded.

For $P_R=\mathbf1_{[0,R]}(K_\ell)$, define the bounded entire functions

$$
F_R(z)=P_Re^{zK_\ell}M_be^{-zK_\ell}P_R.
\tag{122.18}
$$

On $\Re z=s$, their norms are bounded by $\|B_\ell\|$. On
$\Re z=-s$, the same bound follows from
$B_\ell^*=e^{-sK_\ell}M_be^{sK_\ell}$, since $b$ is real. The
three-lines theorem and Cauchy's estimate at zero give

$$
\|F_R'(0)\|\le\frac{2\|B_\ell\|}{s},
\tag{122.19}
$$

uniformly in $R$. Passing to spectral limits yields a bounded commutator
form $[K_\ell,M_b]$; this passage is initially a form statement and does
not assume domain invariance.

Use cylindrical coordinates $(r,\theta,z,\xi)$. The principal symbol is

$$
 a\left[p_r^2+\left(\frac{p_\theta}{r}+\frac r2p_\xi\right)^2+p_z^2\right]
 +\eta p_\xi^2.
\tag{122.20}
$$

Because $b_\theta=0$, take genuine compact-core tests, supported in
$r>0$,

$$
 u_N=e^{i\ell\theta}\chi(r,z,\xi)e^{iN\zeta\cdot(r,z,\xi)},
\qquad \chi\in C_c^\infty(\{r>0\}),\quad \zeta\in\mathbb R^3.
\tag{122.21}
$$

These $u_N$ lie in the genuine punctured smooth core of every local power
of $K_\ell$, so the commutator form can be evaluated on them without
extending the singular expression through the source.

The exact divergence-form Leibniz identity from (122.9) is

$$
[K,M_b]u=(Kb)u-2\langle\mathsf A\nabla b,\nabla u\rangle.
\tag{122.22}
$$

The term proportional to $N$ in (122.22) is

$$
-2iN e^{i\ell\theta+iN\zeta\cdot(r,z,\xi)}\chi
\left[a b_r\zeta_r+a b_z\zeta_z
 +\left(\eta+\frac{ar^2}{4}\right)b_\xi\zeta_\xi\right].
\tag{122.23}
$$

For fixed $\ell,\chi,\zeta$, all remaining terms have uniformly bounded
$L^2(m)$-norm, while $\|u_N\|_2$ is independent of $N$. Boundedness
of the commutator form therefore forces $b_r=b_z=b_\xi=0$ on every compact
patch of $\Omega$. Rotation invariance gives $b_\theta=0$, so $b$, and
therefore $g$, is constant on connected $\Omega$.

The source-start density $g_t$ cannot be constant. Its mass is one, so a
constant would be $g_t=1$. For each $0<u<t$, the semigroup identity
$g_t=T_{t-u}g_u$, conservativity $T_{t-u}1=1$, and injectivity of
$T_{t-u}$ would then give $g_u=1$. For a nonzero
$\varphi\in C_c(\Omega)$, $\varphi\ge0$, continuity of the actual
diffusion from its source-start point gives

$$
\mathbb E_e[\varphi(Z_u)]\longrightarrow\varphi(e)=0
\quad(u\downarrow0),
\tag{122.24}
$$

whereas $g_u=1$ would make this expectation equal to
$\int\varphi\,dm>0$. This contradiction proves the local infinite-negative-
index assertion.

It remains to pass from that assertion to exact purification. Let
$f\in\mathcal F$ and suppose that, on a positive-measure set, two labels
$i\ne j$ are simultaneously nonzero. For some $\varepsilon_0>0$, the set

$$
E=\{f_i\ge\varepsilon_0,\ f_j\ge\varepsilon_0\}
\tag{122.25}
$$

has positive $m$-measure. By the first part, choose a nine-dimensional
negative-definite space of bounded real functions supported in $E$. The
linear map from that space to the eight ordered coordinates

$$
v\longmapsto
 \bigl(Q(v,f_z),Q(f_z,v)\bigr)_{z\in\mathcal A}
\tag{122.26}
$$

has a nonzero kernel vector $v_-$, and $Q(v_-,v_-)<0$. Theorem 120.2,
with the emission labels relabelled so that the selected pair is $1,3$,
supplies a bounded $v_+$ supported in the same $E$, satisfying the same
eight zero constraints and $Q(v_+,v_+)>0$. Hence
$v_++\lambda v_-$ has a nonzero real value of $\lambda$ for which

$$
Q(v,f_z)=Q(f_z,v)=0\quad(z\in\mathcal A),
\qquad Q(v,v)=0.
\tag{122.27}
$$

Choose $\varepsilon>0$ with
$\varepsilon\|v\|_\infty\le\varepsilon_0$, and put

$$
 f_y^\pm=f_y\pm\varepsilon
 (\mathbf1_{\{y=i\}}-\mathbf1_{\{y=j\}})v.
\tag{122.28}
$$

These are pointwise Borel simplex tuples: on $E$ the two changed
coordinates remain nonnegative and their sum is unchanged, and off $E$ the
tuple is unchanged. Bilinearity and (122.27) give

$$
\nu_{f^+}(y,z)=\nu_f(y,z)=\nu_{f^-}(y,z)
\quad(y,z\in\mathcal A).
\tag{122.29}
$$

Thus every positive-measure overlap gives two distinct tuples with the same
pair law and midpoint $f$.

Fix an attainable law $\nu$, and let its weak-star compact fiber in the
simplex be $\mathcal F_\nu$. Choose a countable separating family
$(\psi_n)_{n\ge1}$ in the real $L^1(m)$ unit ball and define

$$
J(f)=\sum_{n\ge1}2^{-n}\sum_{y\in\mathcal A}
       \left(\int_G\psi_n f_y\,dm\right)^2.
\tag{122.30}
$$

The series converges uniformly and $J$ is continuous. Because the family
separates $L^\infty(m)$ classes, $J$ is strictly convex on the simplex.
A maximizer exists on $\mathcal F_\nu$. If it had a positive-measure
overlap, (122.28)–(122.29) would write it as the midpoint of two distinct
points of the same fiber, contradicting strict convexity and maximality.
Therefore a maximizing tuple is an indicator tuple almost everywhere.
Choose Borel representatives and assign one fixed label on the combined
Borel null exceptional set. The two positive-time marginals have densities
$g_t$ and $g_{t+\Delta}$ with respect to $m$, so this repair preserves
the original two-time pair law. Hence every attainable stochastic law has a
Borel partition representative, proving the first equality in (122.3).
The second follows from the attained stochastic minimum in Theorem 119.2.

The argument is conditional precisely on the inherited source-side results
in §§115–116, Theorem 119.2 and Theorem 120.2. It uses the original
nonstationary source-start density, the original clock and the same Borel
readout at $t$ and $t+\Delta$. The two local clarifications are part of
the proof: Kotake–Narasimhan is applied to the order-two expression and the
weak-operator-to-differential-iterate induction (120.6)–(120.7), while
Agler–Young is applied only after complexifying the heat RKHS and restricting
to the density-point uniqueness set, with its finite negative-square parameter
set equal to $\kappa$. No stationarity, source reset, clock change, retained
controller, shared noise, killing, postselection, extra emission regularity,
quantitative or algorithmic construction, sample bound, native physical
realization, or whole-semigroup compactness premise follows.
$\square$

**Definition 122.2 (source-specific scope and supplied boundary).**
Theorem 122.1 is a repo-derived analytic application of the actual Green-field
formula in Proposition 85.4, the source-side suppliers of §§115–116, and the
attainment and positive-direction suppliers of Theorems 119.2 and 120.2.
The new inference supplies exactly the previously unresolved boundary between
(119.3), which gave only equality of stochastic and deterministic infima and
weak-star deterministic approximation, and deterministic attainment by one
Borel partition. It also supplies the local infinite-negative-index premise
needed to turn the positive quadratic direction of Theorem 120.2 into an
exact same-law perturbation. The cited analytic, heat-RKHS, density-point,
Agler–Young, rotation, commutator and compact-fiber ingredients are used
inside this source-specific proof; no standalone renamed literature theorem
or worldwide priority claim is asserted. The conclusion is only for the
original finite-positive-time family and the unchanged target and quantifiers
of Definition 119.1.

## 追加锚（本行以下为增补区）

## 123. The three-time coefficient image and its compact fibers

**Definition 123.1 (the original three-time coefficient).** Fix the original parameters $a,\eta,t,\Delta _1,\Delta _2>0$ and retain the source-start diffusion, clock, state space, and common Borel readout of §§115–122. Write

$$
L=\{0,1,3,B\},\qquad P=T_{\Delta _1},\qquad R=T_{\Delta _2},\qquad g=g_t.
$$

Retain $G=H^1\times\mathbb R$, $pp'=(x+x',y+y',z+z',w+w'+xy')$, the raw Haar measure $\mu=dx\,dy\,dz\,dw$, and the source $e$. The unit-source field $\Gamma$, actual selector $A(u)=\rho C(u)$ of (112.2)–(112.5), and coefficient-positive normalized zero vector $h$ are unchanged. Thus $m=h^2\mu$, $m(G)=1$, $U_hv=hv$, $K=U_h^{-1}HU_h\geq0$, and $T_s=e^{-sK}$ use the full conservative self-adjoint extension $H$ and the entire form of (115.15). The process starts at $e$ at time zero.

The measure $m$ is equivalent to Lebesgue measure off the null source and has no atoms, $T_s$ is conservative, Markov, and symmetric, and the source densities satisfy $g_s>0$ almost everywhere, $g_s\in L^2(m)$, $\int g_s\,dm=1$, and $g_{s+r}=T_rg_s$. The off-source transition kernel $p_s$ of (120.8)–(120.10) is nonnegative, symmetric and measurable; its values on the null source do not affect integration against $m$, and $\int p_s(x,y)m(dy)=1$ for almost every $x$.

For bounded real Borel functions define

$$
\mathcal C(u,v,w)=\int_G g\,u\,P(vRw)\,dm.
\tag{123.1}
$$

For a pointwise Borel simplex tuple $f=(f_y)_{y\in L}$, with $f_y\geq0$ and $\sum_yf_y=1$, the same readout is used at all three epochs and the fresh reads are conditionally independent. Therefore its complete three-time law is

$$
\nu_f^{(3)}(y,z,w)=\mathcal C(f_y,f_z,f_w)\qquad(y,z,w\in L).
\tag{123.2}
$$

The transition-density form is

$$
W(x_1,x_2,x_3)=g(x_1)p_{\Delta _1}(x_1,x_2)p_{\Delta _2}(x_2,x_3),
\tag{123.3}
$$

so that $d\mathbb P_{(Z_t,Z_{t+\Delta _1},Z_{t+\Delta _1+\Delta _2})}=W\,dm^3$. Here $W\geq0$, $W\in L^1(m^3)$, and $\int W\,dm^3=1$.

**Proposition 123.2 (continuity, compact fibers, and common-partition approximation).** Let $\mathcal S$ be the product of four copies of the weak-star compact order interval $[0,1]\subset L^\infty(m)$, cut out by the a.e. equation $\sum_yf_y=1$. Define

$$
\Phi _3:\mathcal S\longrightarrow\mathbb R^{64},\qquad
\Phi _3(f)=\bigl(\mathcal C(f_y,f_z,f_w)\bigr)_{y,z,w\in L}.
\tag{123.4}
$$

Then $\Phi _3$ is continuous, its image is compact, and every nonempty fiber is compact. If $\mathcal D$ denotes the indicator tuples of pointwise Borel partitions of $G$, then

$$
\Phi _3(\mathcal S)=\overline{\Phi _3(\mathcal D)}.
\tag{123.5}
$$

The closure is in all 64 coordinates, equivalently in total variation on $L^3$.

**Proof.** Since $m$ is a finite Borel measure on $\mathbb R^4$, $L^1(m)$ is separable, and the weak-star compactness of the order interval makes $\mathcal S$ compact and metrizable. Suppose $f_n\to f$ coordinatewise weak-star. For fixed $y,z,w$, set $b=Rf_w$. The exact difference is

$$
\begin{aligned}
&\mathcal C(f_{n,y},f_{n,z},f_{n,w})-\mathcal C(f_y,f_z,f_w)\\
={}&\int g f_{n,y}P\bigl(f_{n,z}R(f_{n,w}-f_w)\bigr)\,dm\\
&+\int g f_{n,y}P\bigl((f_{n,z}-f_z)b\bigr)\,dm\\
&+\int g(f_{n,y}-f_y)P(f_zb)\,dm.
\end{aligned}
\tag{123.6}
$$

Use precisely (119.6): weak-star convergence in $[0,1]$ implies strong $L^2(m)$ convergence after $T_s$, for every $s>0$. This is compactness on that order interval, not on the whole $L^2$ unit ball. The first term tends to zero by this bounded order-interval compactness $R(f_{n,w}-f_w)\to0$ in $L^2(m)$, the $L^2$ contraction of $P$, $0\leq f_{n,z}\leq1$, and Cauchy–Schwarz. For every $\psi\in L^1(m)$, $\psi b\in L^1(m)$, so $f_{n,z}b\to f_zb$ weak-star and the same compactness statement makes the second term tend to zero. The last term tends to zero against the fixed $L^1$ function $gP(f_zb)$. Thus every one of the 64 coordinates is continuous; no product of two unprocessed weak-star limits is taken.

Weak-star classes have Borel representatives. Combine the null sets on which their bounds or sum constraint fail and assign one fixed label there. The three positive-time laws are absolutely continuous with respect to $m$, so this common repair leaves (123.2) unchanged. Compactness of the image and its fibers follows.

For the reverse approximation, let $(\mathcal P_n)$ be increasing finite Borel partitions generating the Borel sigma algebra. In a cell $A\in\mathcal P_n$, split its $m$-mass into four Borel pieces of masses $\int_Af_y\,dm$. Such a split exists because $m\ll\mu$: the distribution $s\mapsto m(B\cap\{x\leq s\})$ is continuous for every Borel remainder $B$. The resulting partition $(E_{n,y})_y$ satisfies

$$
\int\psi(\mathbf1_{E_{n,y}}-f_y)\,dm=0
$$

for every $\mathcal P_n$-simple $\psi$. Density of these simple functions in $L^1(m)$ and the uniform bound by $1$ give $\mathbf1_{E_{n,y}}\to f_y$ weak-star. Continuity of $\Phi _3$ yields (123.5). In particular every continuous objective of the complete three-time law attains its stochastic optimum, and its deterministic infimum equals that optimum; (123.5) gives approximation, not deterministic attainment. $\square$

## 124. Obstructions to common factorization

**Proposition 124.1 (proper common factors are impossible for the full path density).** The heat operator $T_s$ is injective on $L^2(m)$ for every $s>0$. If the density $W$ in (123.3) has an $\mathcal A\otimes\mathcal A\otimes\mathcal A$-measurable version modulo $m^3$, for a sub-$\sigma$-algebra $\mathcal A$ of the completed Borel $\sigma$-algebra $\mathcal F$, then $\mathcal A=\mathcal F$ modulo $m$.

**Proof.** Spectral calculus gives

$$
\|T_su\|_2^2=\int_{[0,\infty)}e^{-2s\lambda}\,d\langle u,E_K(\lambda)u\rangle,
$$

so $T_su=0$ implies $u=0$. Integrating (123.3) in $x_3$ and then in $x_2$ gives

$$
D(x_1,x_2)=g(x_1)p_{\Delta _1}(x_1,x_2),
$$

with $g$ measurable for $\mathcal A$; division by $g>0$ almost everywhere then makes $p_{\Delta _1}$ measurable for $\mathcal A\otimes\mathcal A$, modulo null sets. If $\mathbb E_m[u\mid\mathcal A]=0$, boundedness and truncation of the kernel sections give $Pu=0$; $L^2$ approximation extends this to every such $u$. Injectivity of $P$ therefore makes conditional expectation the identity on $L^2(m)$, and every $L^2$ indicator is $\mathcal A$-measurable modulo null sets. Hence $\mathcal A=\mathcal F$ modulo $m$. $\square$

This rules out the route that simultaneously requires a proper common factor, conditional atomlessness over that factor, and measurability of the complete $W$ over its three coordinates. It does not exclude conditional constructions for smaller quantities.

**Proposition 124.2 (no finite separable path density).** There are no $N<\infty$ and integrable factors $a_j,b_j,c_j\in L^1(m)$ such that

$$
W(x_1,x_2,x_3)=\sum_{j=1}^Na_j(x_1)b_j(x_2)c_j(x_3)\quad\text{a.e.}
\tag{124.1}
$$

**Proof.** Integrate (124.1) in $x_3$, write $d_j=\int c_j\,dm$, and apply the resulting identity to a bounded $u$:

$$
g(x)Pu(x)=\sum_{j=1}^Nd_ja_j(x)\int b_j(y)u(y)\,dm(y).
$$

Since $g>0$ almost everywhere, the range of $P$ on bounded functions lies in a finite-dimensional subspace of $L^2(m)$. Bounded functions are dense in $L^2(m)$ and $P$ is bounded, so the entire range of $P$ would be finite-dimensional, contradicting injectivity on the infinite-dimensional space $L^2(m)$. $\square$

**Proposition 124.3 (finite conditional decompositions).** Let $\mathcal A_1,\mathcal A_2,\mathcal A_3\subset\mathcal F$ and suppose $\mathcal F$ is nowhere equivalent to $\mathcal A_2$ under $m$. The density $W$ cannot have a representation

$$
W=\sum_{j=1}^{N}A_j(x_1,x_2,x_3)\alpha_j(x_1)\beta_j(x_2)\gamma_j(x_3),
\tag{124.2}
$$

where every $A_j$ is $\mathcal A_1\otimes\mathcal A_2\otimes\mathcal A_3$-measurable, the single-coordinate factors are nonnegative and integrable, and every individual product term in (124.2) is absolutely integrable on $G^3$.

**Proof.** Put $b=1+\sum_j\beta_j$, $B=\int b\,dm$, and $d\mu _0=(b/B)\,dm$. This reference probability is equivalent to $m$, so the nowhere-equivalence hypothesis is preserved; it does not replace the process law. For every nonzero $\beta_j$, let $d\mu_j=\beta_jdm/\int\beta_j\,dm$; its density relative to $\mu _0$ is bounded by $B/\int\beta_j\,dm$. Zero factors are omitted. The conditional splitting lemma of He–Sun–Sun–Zeng, *Characterization of equilibrium existence and purification in general Bayesian games*, arXiv:2106.08563v1, Lemma 4(2), pp. 28–29, applied with $\mathcal A=\mathcal A_2$ and the constant fair distribution on the compact discrete action space $\{-1,1\}$ (with zero payoff), gives a measurable $v\in\{-1,1\}$ satisfying

$$
\int_D\beta_jv\,dm=0\qquad(D\in\mathcal A_2,\ j=1,\ldots,N).
\tag{124.3}
$$

For almost every fixed $(x_1,x_3)$, the section $A_j(x_1,\cdot,x_3)$ is $\mathcal A_2$-measurable. Equation (124.3), first for bounded simple sections and then by truncation, makes each term in (124.2) integrate to zero against $v(x_2)\,dm(dx_2)$; the asserted absolute integrability permits Fubini. Hence

$$
\int W(x_1,x_2,x_3)v(x_2)\,m(dx_2)m(dx_3)=0
$$

for almost every $x_1$. By (123.3) and conservation this is $g(x_1)Pv(x_1)$. Positivity of $g$ and injectivity of $P$ force $v=0$, contradicting $|v|=1$. The absolute-integrability hypothesis is used exactly in this Fubini step. $\square$

## 125. The common-readout coefficient boundary

**Definition 125.1 (a two-label perturbation).** Let $f$ be a pointwise Borel simplex tuple, let $i\neq j$ be labels, and let $\kappa>0$ satisfy

$$
E=\{f_i\geq\kappa,\ f_j\geq\kappa\},\qquad m(E)>0.
$$

Set $\sigma_i=1$, $\sigma_j=-1$, and $\sigma_y=0$ otherwise. For a bounded real Borel $v$ supported in $E$, put $f_y^s=f_y+s\sigma_yv$. The tuple remains a pointwise Borel simplex tuple whenever $|s|\|v\|_\infty\leq\kappa$.

**Proposition 125.2 (the exact 64-equation expansion).** For every $y,z,w\in L$,

$$
\nu_{f^s}^{(3)}(y,z,w)-\nu_f^{(3)}(y,z,w)
=s\ell_{yzw}(v)+s^2q_{yzw}(v)+s^3\sigma_y\sigma_z\sigma_w\mathcal C(v,v,v),
\tag{125.1}
$$

where

$$
\begin{aligned}
\ell_{yzw}(v)={}&\sigma_y\mathcal C(v,f_z,f_w)
+\sigma_z\mathcal C(f_y,v,f_w)
+\sigma_w\mathcal C(f_y,f_z,v),\\
q_{yzw}(v)={}&\sigma_y\sigma_z\mathcal C(v,v,f_w)
+\sigma_y\sigma_w\mathcal C(v,f_z,v)
+\sigma_z\sigma_w\mathcal C(f_y,v,v).
\end{aligned}
\tag{125.2}
$$

Thus preservation of the complete law means all 64 equations (125.1), one for each $(y,z,w)\in L^3$. The 48 slotwise linear conditions

$$
\mathcal C(v,f_z,f_w)=\mathcal C(f_y,v,f_w)=\mathcal C(f_y,f_z,v)=0
$$

are sufficient for all first-order coefficients to vanish. The twelve conditions

$$
A_w(v)=\mathcal C(v,v,f_w)=0,\qquad
B_z(v)=\mathcal C(v,f_z,v)=0,\qquad
D_y(v)=\mathcal C(f_y,v,v)=0
\tag{125.3}
$$

are sufficient for all second-order coefficients to vanish, and $\mathcal C(v,v,v)=0$ removes the cubic term. For a fixed nonzero $s$, the exact conditions for both signs in (125.1) are instead

$$
q_{yzw}(v)=0,\qquad
\ell_{yzw}(v)+s^2\sigma_y\sigma_z\sigma_w\mathcal C(v,v,v)=0
\quad(y,z,w\in L).
\tag{125.4}
$$

Consequently the slotwise system is sufficient, not necessary for every same-fiber perturbation.

The quadratic forms in (125.3) are

$$
\begin{aligned}
A_w(v)&=\int g v\,P(vRf_w)\,dm,\\
B_z(v)&=\int f_z\,P(gv)\,Rv\,dm,\\
D_y(v)&=\int P(gf_y)\,vRv\,dm.
\end{aligned}
\tag{125.5}
$$

All these integrals are finite by boundedness of $v$, $g\in L^2(m)$, and the Markov contractions. Summing over the free label gives

$$
\begin{aligned}
\sum_wA_w(v)&=\int g_t vT_{\Delta _1}v\,dm,\\
\sum_zB_z(v)&=\int g_t vT_{\Delta _1+\Delta _2}v\,dm,\\
\sum_yD_y(v)&=\int g_{t+\Delta _1}vT_{\Delta _2}v\,dm.
\end{aligned}
\tag{125.6}
$$

The three marginal sums in (125.6) do not determine the twelve individual forms. In particular, an index statement for one form does not supply simultaneous nullity of (125.3).

Let $U=\mathbb R^4$ and split $U=\mathbb R\sigma\oplus U_0$ with $\dim U_0=3$. The first-order coefficient tensor lies in

$$
(\mathbb R\sigma\otimes U\otimes U)+(U\otimes\mathbb R\sigma\otimes U)+(U\otimes U\otimes\mathbb R\sigma),
$$

of dimension $4^3-3^3=37$. The quadratic coefficient tensor lies in

$$
(\mathbb R\sigma\otimes\mathbb R\sigma\otimes U)+(\mathbb R\sigma\otimes U\otimes\mathbb R\sigma)+(U\otimes\mathbb R\sigma\otimes\mathbb R\sigma),
$$

of dimension $3\cdot3+1=10$, and the cubic tensor lies on $\mathbb R\sigma^{\otimes3}$. These counts compress the actual coefficient families; they do not discard any of the 64 equations.

**Lemma 125.3 (a conditional full-fiber criterion).** Let $V$ be a real vector space, let $d\geq1$, and let $q_1,\ldots,q_d$ be a linearly independent basis of a finite-dimensional family of quadratic forms. Suppose every nonzero pencil $\sum_j\lambda_jq_j$ has infinite negative index, meaning that it is negative definite on finite-dimensional subspaces of arbitrarily large dimension. After any finitely many homogeneous linear constraints on $V$, there is a two-dimensional subspace on which every $q_j$ vanishes identically. Every homogeneous cubic form consequently has a nonzero zero on that plane.

**Proof.** Intersecting a sufficiently large negative-definite subspace with finitely many linear kernels preserves infinite negative index. For $\lambda\in S^{d-1}$ choose a finite-dimensional subspace on which $q_\lambda=\sum_j\lambda_jq_j$ has at least $d+2$ negative dimensions. Negative definiteness on a fixed finite-dimensional subspace is open in $\lambda$, so a finite cover of $S^{d-1}$ and the span of the selected subspaces give a finite-dimensional $F$ on which every $q_\lambda$ has at least $d+2$ negative dimensions.

On the unit sphere of $F$, minimize $H(x)=\sum_jq_j(x)^2$. If the minimum at $x$ were positive, put $\lambda_j=q_j(x)$. The subspace satisfying $b_j(x,w)=0$ for all symmetric polar forms $b_j$ has codimension at most $d$; after the sphere constraint it still contains a nonzero $w$ with $q_\lambda(w)<0$. For

$$
x(s)=\frac{x+sw}{\sqrt{1+s^2\|w\|^2}},
$$

the first derivatives of all $q_j(x(s))$ vanish and

$$
\left.\frac{d^2}{ds^2}H(x(s))\right|_{s=0}
=4\bigl(q_\lambda(w)-H(x)\|w\|^2\bigr)<0,
$$

contradicting minimality. Thus there is a nonzero simultaneous zero $v_1$. Impose the additional equations $b_j(v_1,v)=0$ and one linear equation that is nonzero at $v_1$, and repeat the argument to obtain an independent simultaneous zero $v_2$. Polarization makes every $q_j$ vanish on $\operatorname{span}\{v_1,v_2\}$. A homogeneous cubic is odd on this plane, so it has a nonzero zero there. $\square$

For the actual perturbation, take $V_E$ to be the real $L^\infty(m)$ classes supported in $E$ and satisfying $\ell_{yzw}(v)=0$ for all labels. Since $m$ is nonatomic and $m(E)>0$, arbitrarily many disjoint positive-measure subsets of $E$ give independent indicators. Thus $L^\infty(E,m)$ is infinite-dimensional, and $V_E$ remains infinite-dimensional after these at most 37 linear constraints. The restricted span of the actual quadratic forms $q_{yzw}$ has dimension at most ten. If that dimension is positive and every nonzero pencil has infinite negative index on $V_E$, Lemma 125.3 supplies a common zero plane. If the restricted span is zero, take any two-dimensional subspace of $V_E$ directly; no pencil argument is needed. In either case the odd cubic $\mathcal C(v,v,v)$ has a nonzero zero on the plane. Choose bounded Borel representatives and repair their null exceptional sets inside $E$, obtaining $v$ nonzero as an $L^\infty(m)$ class, with all first- and second-order coefficients and the cubic zero. Taking $0<|s|\leq\kappa/\|v\|_\infty$ preserves the simplex, and (125.1) preserves all 64 coordinates for both signs. This is a sufficient criterion; the individual index statements for the three sums in (125.6) do not imply it.

If this criterion holds on some positive-measure overlap of every non-indicator tuple, then every compact fiber of $\Phi _3$ contains an indicator tuple. Indeed, maximize on a fiber the continuous strictly convex separator

$$
J(f)=\sum_{n\geq1}2^{-n}\sum_{y\in L}
\left(\int_G\psi_nf_y\,dm\right)^2,
\tag{125.7}
$$

where $(\psi_n)$ is a countable separating family in the real $L^1(m)$ unit ball. A maximizer with positive-measure overlap would be the midpoint of two distinct points of the same fiber by the criterion, contradicting strict convexity and maximality. It is therefore an indicator tuple almost everywhere; the common Borel null-set repair from Proposition 123.2 gives a pointwise Borel partition. This conditional implication is the full-fiber bridge, and its all-pencil hypothesis for the actual forms remains an additional premise.

## 126. Signed analytic coefficients and the equal-gap marginal consequence

**Proposition 126.1 (signed analytic rotation-invariant coefficient).** Let $s>0$ and let $\varphi\in L^1(m;\mathbb R)$ have a real analytic, rotation-invariant representative on

$$
\Omega=\{(x,y,z,w)\in G:x^2+y^2>0\}.
$$

If $\varphi$ is nonconstant on the connected set $\Omega$, then for every positive-measure Borel set $E$ the symmetric form

$$
Q_{\varphi,s}(u,v)=\frac12\int_G\varphi\{uT_sv+vT_su\}\,dm
\tag{126.1}
$$

on bounded real functions supported in $E$ has infinite negative index. Applying the assertion to $-\varphi$ gives infinite positive index as well.

**Proof.** Complexify the actual heat RKHS $\mathcal H_s=\operatorname{Ran}T_{s/2}$ with its pullback $L^2$ norm. Its kernel is $p_s$ and is nonsingular by the off-source kernel construction of §120. Every member of $\mathcal H_s$ and of $\mathcal H_s\mathcal H_s+\mathcal H_s\mathcal H_s$ is analytic on $\Omega$ by the heat-regularity argument used in §122.

Assume the negative index of (126.1) on $E$ is finite, say $\kappa$. If $E\cap\{\varphi<0\}$ has positive measure, the rotation-invariant density-point construction selects, for every $N$, points in one angular slice at which $\varphi=c<0$. The limiting Gram matrix is $c(p_s(p_i,p_j))$, strictly negative definite. Indicators of sufficiently small intersections of $E$ with balls around these points then give $N$ negative directions, a contradiction. Up to a null set we may therefore restrict to $E\cap\{\varphi\geq0\}$ and to a positive-measure relatively compact subset.

Suppose $\varphi(q)<0$ somewhere and put $c_0=-\varphi(q)>0$. On the density-point uniqueness set $E^*$ define

$$
b=\frac{\varphi-c_0}{\varphi+c_0},\qquad |b|\leq1.
$$

The Gram identity

$$
\frac{\varphi(p)+\varphi(q')}{2}p_s(p,q')
=\frac{(\varphi(p)+c_0)(\varphi(q')+c_0)}{4c_0}
(1-b(p)b(q'))p_s(p,q')
\tag{126.2}
$$

transfers the negative-square bound to $(1-b(p)\overline{b(q')})p_s(p,q')$. The Agler–Young theorem, *Functions which are almost multipliers of Hilbert function spaces*, arXiv:math/9605224v1, Theorem 2.1, p. 11, applies after complexification because $E^*$ is a uniqueness set for both analytic classes and $p_s$ is nonsingular. It supplies a closed finite-codimensional $W\subset\mathcal H_s$ and a bounded $L:W\to\mathcal H_s$ with $Lu=bu$ on $E^*$.

Analytic uniqueness extends

$$
(\varphi+c_0)Lu=(\varphi-c_0)u
\tag{126.3}
$$

to all of $\Omega$. At every point of the rotation orbit of $q$, $\varphi=-c_0$, so (126.3) gives $u=0$. That orbit contains arbitrarily many distinct points, while their evaluation functionals are linearly independent by nonsingularity of $p_s$. A finite-codimensional $W$ cannot be annihilated by arbitrarily many independent evaluations. Hence $\varphi\geq0$ on $\Omega$.

Now put $b=(\varphi-1)/(\varphi+1)$. The same theorem yields a finite-codimensional multiplication domain

$$
D=\{u\in\mathcal H_s:bu\in\mathcal H_s\}.
$$

The domain contains the closed finite-codimensional space supplied by the theorem, so it too is closed and finite-codimensional. Point evaluations give the closed graph of multiplication on $D$, hence boundedness. Rotation invariance preserves $D$ and $D^\perp$. Choose an angular character $\ell$ absent from the finite-dimensional representation on $D^\perp$. The corresponding sector lies in $D$, and

$$
B_\ell=e^{(s/2)K_\ell}M_be^{-(s/2)K_\ell}
$$

is bounded, since the pullback norm is $\|u\|_{\mathcal H_s}=\|e^{(s/2)K}u\|_2$. For $P_R=\mathbf1_{[0,R]}(K_\ell)$, the entire functions

$$
F_R(z)=P_Re^{zK_\ell}M_be^{-zK_\ell}P_R
$$

have uniform bound $\|B_\ell\|$ on the two boundary lines $\Re z=\pm s/2$: the positive boundary uses $B_\ell$, and the negative boundary uses its adjoint since $b$ is real. The three-lines theorem and Cauchy's estimate on a circle of radius $s/4$ give

$$
\|F_R'(0)\|\leq\frac{4\|B_\ell\|}{s}.
$$

Passing to spectral limits gives a bounded commutator form $[K_\ell,M_b]$. In cylindrical coordinates $(r,\theta,z,\xi)$, the principal symbol of the actual operator is

$$
a\left[p_r^2+\left(\frac{p_\theta}{r}+\frac r2p_\xi\right)^2+p_z^2\right]+\eta p_\xi^2.
\tag{126.4}
$$

Use compact-core tests supported in $r>0$,

$$
u_N=e^{i\ell\theta}\chi(r,z,\xi)e^{iN\zeta\cdot(r,z,\xi)},\qquad
\chi\in C_c^\infty(\{r>0\}),\quad\zeta\in\mathbb R^3.
$$

The divergence-form Leibniz identity gives, at order $N$,

$$
-2iN e^{i\ell\theta+iN\zeta\cdot(r,z,\xi)}\chi
\left[a b_r\zeta_r+a b_z\zeta_z
+\left(\eta+\frac{ar^2}{4}\right)b_\xi\zeta_\xi\right].
\tag{126.5}
$$

All remaining terms are uniformly bounded in $L^2(m)$ as $N\to\infty$. Boundedness of the commutator forces $b_r=b_z=b_\xi=0$ on every compact patch of $\Omega$; rotation invariance gives $b_\theta=0$. Thus $b$, and hence $\varphi$, is constant, contradicting the hypothesis. This proves infinite negative index. Replacing $\varphi$ by $-\varphi$ proves infinite positive index. $\square$

**Corollary 126.2 (simultaneous equal-gap adjacent marginals).** Let $\Delta _1=\Delta _2=d>0$. Then every nonzero pencil

$$
Q_{\alpha,\beta}(v)=\alpha\int g_t vT_dv\,dm
+\beta\int g_{t+d}vT_dv\,dm,\qquad(\alpha,\beta)\neq(0,0),
\tag{126.6}
$$

has infinite negative index on every positive-measure overlap. After any finitely many homogeneous linear constraints there is a two-dimensional subspace on which both forms in (126.6) vanish identically; this plane contains a nonzero zero of the actual cubic $\mathcal C(v,v,v)$.

**Proof.** Source regularity makes $\alpha g_t+\beta g_{t+d}$ analytic and rotation-invariant. It is nonconstant for every $(\alpha,\beta)\neq(0,0)$. Otherwise, using its mass, one would obtain

$$
(\alpha+\beta T_d)(g_t-1)=0.
\tag{126.7}
$$

The multiplier $\alpha+\beta e^{-d\lambda}$ has at most one positive zero. Since $\ker K=\mathbb C1$, spectral calculus would make $g_t-1$ either zero or an eigenvector for one positive eigenvalue. In the eigenvector case, for $0<u<t$,

$$
g_u=1+e^{\lambda_0(t-u)}(g_t-1).
$$

The displayed identity follows by injectivity of $T_{t-u}$, and has an $L^2(m)$ limit $r$ as $u\downarrow0$. In the first case the same injectivity gives $g_u=1$ for $0<u<t$, with limit $r=1$. In either case, for every $\psi\in C_c(G)$, finiteness of $m$ and $L^2$ convergence give

$$
\int_G\psi r\,dm
=\lim_{u\downarrow0}\int_G\psi g_u\,dm
=\lim_{u\downarrow0}\mathbb E_e[\psi(Z_u)]
=\psi(e).
$$

The last equality uses continuity of the actual source-start paths and bounded convergence. Compactly supported continuous tests on the original $G$ identify finite Borel measures, so $r\,m=\delta_e$. This contradicts $m(\{e\})=0$ and absolute continuity of $r\,m$; no stationarity or additional regularity is assumed. Proposition 126.1 applied to this coefficient proves the index assertion for every pencil. Lemma 125.3 with $d=2$ gives the common zero plane and the cubic zero. $\square$

The two forms in (126.6) are the first and third marginal sums in (125.6) when the gaps are equal. This conclusion supplies simultaneous cancellation for those two adjacent marginal conditions only. It does not impose the total-gap form, the remaining weighted forms in (125.3), or the other coordinates among the 64 equations; in particular it does not assert an unrestricted or exact three-time representative.

The finite linear vector-measure range theorem of Dvoretzky–Wald–Wolfowitz, *Relations among certain ranges of vector measures*, Pacific J. Math. 1 (1951), §3 Theorem 4 and Lemma 2, pp. 66–67, concerns linear integrals of a probability vector. The common-readout map (123.2) is trilinear, so that theorem alone does not supply the exact three-time conclusion. The conditional splitting input used in Proposition 124.3 is only the displayed Lemma 4(2) of He–Sun–Sun–Zeng, with its nowhere-equivalence, bounded-density, and absolute-integrability hypotheses. The multiplier step in Proposition 126.1 is only the finite-codimensional application of Agler–Young under the stated analytic uniqueness and nonsingular-kernel conditions.

## 追加锚（本行以下为增补区）

## 127. Localization of the original mixed pencil and a comparable-kernel interval

**Definition 127.1 (the original equal-gap pencil and its two domains).** Fix the original finite positive parameters $a,\eta,t,d>0$ and set $\Delta _1=\Delta _2=d$. Retain all the source, endpoint, native-parameter and readout hypotheses of §§115–126. In particular, $G=H^1\times\mathbb R$ has the original product and raw Haar measure $\mu$, $\Gamma$ is the same unit-source field, $H=H_{\rm end}$ has the actual selector $A(u)=\rho C(u)$, and $h$ is its coefficient-positive normalized zero vector. The measure, full form and original clock are

$$
\begin{gathered}
m=h^2\mu,\qquad U_hv=hv,\qquad K=U_h^{-1}HU_h,\qquad T_s=e^{-sK},\\
D(H^{1/2})=\mathcal Q_c\dotplus\mathbb Ch,\qquad
q_H[y+ch]=\overline q_c[y],\\
\mathscr E[u,v]=\int_{G\setminus\{e\}}
\left(a\sum_{j=1}^3\overline{X_ju}X_jv+
\eta\overline{\partial_wu}\partial_wv\right)dm.
\end{gathered}
\tag{127.1}
$$

The conservative diffusion still starts at $e$ at time zero. Write

$$
P=T_d,\qquad A_d=T_{d/2},\qquad g=g_t,\qquad
\varphi=\alpha g_t+\beta g_{t+d},\qquad
(\alpha,\beta,\gamma)\in\mathbb R^3.
$$

Here $g_s\in L^2(m)$, $g_s>0$ almost everywhere, $\int g_s\,dm=1$, and $g_{t+d}=Pg_t$, as in (117.2)–(117.3). For bounded real Borel classes put

$$
q_{\alpha,\beta,\gamma}(v)
=\int\varphi vPv\,dm+\gamma\int gvP^2v\,dm.
\tag{127.2}
$$

This is exactly the pencil with coefficients $\alpha,\gamma,\beta$ of the first, second and third marginal sums in (125.6). No change of source law, clock or extension is made in forming it. For a Borel $E$ with $m(E)>0$, distinguish the unrestricted space

$$
\mathcal V_E=\{v\in L^\infty(m;\mathbb R):v=0\text{ a.e. on }G\setminus E\}
$$

from the exact first-order constrained space

$$
\mathcal V_E^{\rm lin}=\ker\Lambda_E,\qquad
\Lambda_E:\mathcal V_E\longrightarrow\mathbb R^{L^3},\qquad
\Lambda_E(v)=(\ell_{yzw}(v))_{y,z,w\in L},\qquad
r_E=\operatorname{rank}\Lambda_E.
\tag{127.3}
$$

For (127.3), fix the pointwise Borel simplex tuple $f$, the distinct labels $i,j$, and the signs $\sigma$ of Definition 125.1; $\ell$ is exactly (125.2), with the common-readout trilinear form $\mathcal C$ of (123.1). When $E$ is an emission overlap, it is the same $E=\{f_i\ge\kappa,f_j\ge\kappa\}$, $\kappa>0$. The definition of $\mathcal V_E$ itself imposes no first-order equations. The negative index $n_-(q|_V)$ is the supremum of the dimensions of finite-dimensional real subspaces on which the symmetric polar form of $q$ is strictly negative definite; its values lie in $\mathbb N\cup\{\infty\}$.

**Proposition 127.2 (localization and exact first-order codimension).** For every real coefficient triple and every positive-measure Borel $E$,

$$
n_-(q_{\alpha,\beta,\gamma}|_{\mathcal V_E})
=n_-(q_{\alpha,\beta,\gamma}|_{\mathcal V_G}).
\tag{127.4}
$$

For the exact map (127.3), $r_E\le37$. If $n_-(q|_{\mathcal V_E^{\rm lin}})\le k<\infty$, then

$$
n_-(q|_{\mathcal V_G})\le k+r_E\le k+37.
\tag{127.5}
$$

In particular, infinite global negative index is equivalent to infinite negative index on $\mathcal V_E^{\rm lin}$ for every positive-measure $E$ and every fixed tuple and pair of labels as above.

**Proof.** Work first over the real Hilbert space $\mathcal H=L^2(m;\mathbb R)^4$. Define

$$
Z(v)=\bigl(A_dv,A_d(\varphi v),Pv,P(gv)\bigr),\qquad
J=\frac12
\begin{pmatrix}
0&I&0&0\\ I&0&0&0\\
0&0&0&\gamma I\\0&0&\gamma I&0
\end{pmatrix}.
\tag{127.6}
$$

All four coordinates exist because $m(G)=1$, $v$ is bounded, and $g,\varphi\in L^2(m)$. The semigroup identity and self-adjointness give

$$
q(v)=\langle JZ(v),Z(v)\rangle_{\mathcal H}.
\tag{127.7}
$$

For $z=(z_1,z_2,z_3,z_4)\in\mathcal H$,

$$
\langle z,Z(v)\rangle_{\mathcal H}
=\int vF_z\,dm,\qquad
F_z=A_dz_1+\varphi A_dz_2+Pz_3+gPz_4.
\tag{127.8}
$$

Cauchy–Schwarz shows $F_z\in L^1(m)$. The actual heat analyticity (122.11), the same analyticity of $g_s$, and closure of analytic functions under products give an analytic representative of $F_z$ on the connected full-measure open set

$$
\Omega=\{x^2+y^2>0\}.
$$

On each compact subset of $\Omega$, the measure $m=h^2\mu$ is equivalent to Lebesgue measure with positive smooth density. If $z\perp Z(\mathcal V_E)$, testing (127.8) against all bounded Borel functions supported in $E$ gives $F_z=0$ almost everywhere on $E$. Its zero set in $\Omega$ therefore has positive Lebesgue measure. Mityagin, *The zero set of a real analytic function*, [arXiv:1512.07276v1, Proposition 0](https://arxiv.org/abs/1512.07276v1), applied to this analytic representative on $\Omega$, implies $F_z=0$ throughout $\Omega$. As $m(G\setminus\Omega)=0$, (127.8) now vanishes for every $v\in\mathcal V_G$. Thus the two images have the same orthogonal complement, and

$$
\overline{Z(\mathcal V_E)}=\overline{Z(\mathcal V_G)}=:\mathcal H_0.
\tag{127.9}
$$

For completeness, the bounded symmetric form defined by $J$ has the same negative index on a dense linear subspace of $\mathcal H_0$ as on $\mathcal H_0$. Indeed, approximate a basis of any finite-dimensional strictly negative subspace by vectors in the dense subspace. The Gram matrices converge, and strict negative definiteness is open in the space of real symmetric matrices, so sufficiently close approximants remain independent and strictly negative. Moreover, passage through $Z$ preserves this index: $Z$ is injective on every strictly negative subspace of $\mathcal V_E$, by (127.7); conversely, lift a basis of any strictly negative subspace of $Z(\mathcal V_E)$ to $\mathcal V_E$. The lifted Gram matrix is the same. These observations applied to (127.9) prove (127.4). Analytic uniqueness and finite-dimensional stability are ingredients of this source-specific application.

To identify the actual codimension, let $U=\mathbb R^4=\mathbb R\sigma\oplus U_0$, $\dim U_0=3$. By the exact first line of (125.2), the image of $\Lambda_E$ lies in

$$
(\mathbb R\sigma\otimes U\otimes U)
+(U\otimes\mathbb R\sigma\otimes U)
+(U\otimes U\otimes\mathbb R\sigma).
$$

The complementary tensor summand is $U_0^{\otimes3}$, so this image-containing space has dimension $4^3-3^3=37$. Hence $r_E\le37$; equality is not required. This is the rank of the exact 64-coordinate first-order map, not the number of sufficient slotwise constraints. If $F\subset\mathcal V_E$ is an $N$-dimensional strictly negative subspace, ordinary rank–nullity gives

$$
\dim(F\cap\ker\Lambda_E)
=N-\operatorname{rank}(\Lambda_E|_F)\ge N-r_E.
$$

Thus a constrained bound $k$ excludes an unrestricted negative subspace of dimension $k+r_E+1$. Equation (127.4) gives (127.5). Conversely, an unrestricted infinite index survives this finite codimension, and a constrained infinite index implies an unrestricted one by inclusion. Bounded Borel representatives can be chosen to vanish pointwise outside $E$ by changing only null sets; all the integrals and exact equations are unchanged. $\square$

**Theorem 127.3 (a strict positive comparable-kernel coefficient interval).** Under Definition 127.1, suppose

$$
\beta=0,\qquad \alpha>0,\qquad \gamma\ne0,\qquad \gamma>-\alpha.
\tag{127.10}
$$

Then $q_{\alpha,0,\gamma}$ has infinite negative index on every $\mathcal V_E$ and on every exact space $\mathcal V_E^{\rm lin}$. In particular the assertion includes the opposite-sign interval $-\alpha<\gamma<0$.

**Proof.** Define

$$
\mathcal R=\alpha P+\gamma P^2=P(\alpha I+\gamma P),\qquad
c=\alpha+\min(\gamma,0)>0,\qquad
C=\alpha+\max(\gamma,0).
$$

The spectral theorem applied to the actual nonnegative self-adjoint $K$, with $P=e^{-dK}$, gives $0<P\le I$ in the sense that $P$ is positive and injective, and

$$
cP\le\mathcal R\le CP.
\tag{127.11}
$$

These are operator inequalities; no pointwise positivity of the kernel below is assumed. Let

$$
r(p,q)=\alpha p_d(p,q)+\gamma p_{2d}(p,q),\qquad p,q\in\Omega,
\tag{127.12}
$$

where both heat kernels are exactly those constructed in (120.8)–(120.10). To check the point-kernel comparison, take distinct $p_i\in\Omega$, complex scalars $z_i$, and $v=\sum_i z_i k_{d/2,p_i}$. Since $k_{d,p}=A_dk_{d/2,p}$, the evaluation-vector identities give

$$
\begin{aligned}
\sum_{i,j}\overline{z_i}z_jp_d(p_i,p_j)&=\|v\|_2^2,\\
\sum_{i,j}\overline{z_i}z_jr(p_i,p_j)
&=\langle v,(\alpha I+\gamma P)v\rangle_2.
\end{aligned}
$$

Consequently $c(p_d(p_i,p_j))\le(r(p_i,p_j))\le C(p_d(p_i,p_j))$. The strict finite-Gram positivity proved in §120 makes $r$ a nonsingular positive kernel, including when $\gamma<0$.

Let $\mathcal H_d=\operatorname{Ran}P^{1/2}$ with pullback norm $\|u\|_{\mathcal H_d}=\|P^{-1/2}u\|_2$, and let $\mathcal H_r$ be the RKHS of (127.12), regarded as functions on $\Omega$. Put $B=(\alpha I+\gamma P)^{1/2}$. The operator $B$ is bounded and invertible, commutes with $P$, and $\mathcal R^{1/2}=P^{1/2}B$. Its evaluation vectors are $Bk_{d/2,p}$, whose inner products give precisely (127.12). Thus, with unique analytic representatives on $\Omega$,

$$
\begin{gathered}
\mathcal H_r=\operatorname{Ran}\mathcal R^{1/2}
=\operatorname{Ran}P^{1/2}=\mathcal H_d,\\
C^{-1/2}\|u\|_{\mathcal H_d}
\le\|u\|_{\mathcal H_r}
\le c^{-1/2}\|u\|_{\mathcal H_d}.
\end{gathered}
\tag{127.13}
$$

The spectral comparison and range calculation here are standard functional calculus applied to this particular heat pencil. In particular, (122.11) makes every member of $\mathcal H_r$ analytic on $\Omega$. Every member of $\mathcal H_r\mathcal H_r+\mathcal H_r\mathcal H_r$ is analytic as well. Rotations commute with $P$ and $B$, by §120, so act as a strongly continuous unitary circle representation on $\mathcal H_r$.

For $\beta=0$, (127.2) becomes $q(v)=\langle gv,\mathcal Rv\rangle_2$. Its symmetric point kernel is

$$
S(p,q)=\frac{g(p)+g(q)}2r(p,q).
\tag{127.14}
$$

Suppose $n_-(q|_{\mathcal V_E})=k<\infty$. Choose a relatively compact positive-measure Borel subset $E_0\subset E\cap\Omega$, and let $E_0^*$ be its Lebesgue density points. At finitely many distinct points $p_i\in E_0^*$ use the bounded normalized indicators $\mathbf1_{E_0\cap B(p_i,\varepsilon)}/m(E_0\cap B(p_i,\varepsilon))$. Local continuity of $g,p_d,p_{2d}$ gives convergence of their polar Gram matrices to $(S(p_i,p_j))$, exactly by the double-integral calculation (120.13)–(120.14). Strict negativity on any fixed finite-dimensional subspace persists under matrix convergence, so every such point Gram matrix has at most $k$ negative eigenvalues.

The continuous analytic representative of $g$ is nonnegative on $\Omega$, since it is nonnegative almost everywhere and $m$ has full support there. Define $b=(g-1)/(g+1)$ on $\Omega$. It is real, bounded, analytic and rotation invariant. The identity

$$
S(p,q)=\frac{(g(p)+1)(g(q)+1)}4
\bigl(1-b(p)\overline{b(q)}\bigr)r(p,q)
\tag{127.15}
$$

is a congruence by an invertible positive diagonal matrix on every finite set. Thus $(1-b(p)\overline{b(q)})r(p,q)$ has at most $k$ negative squares on $E_0^*$. Mityagin's Proposition 0, with connected domain $\Omega$ and the locally equivalent measure $m$, shows that $E_0^*$ is a uniqueness set for both $\mathcal H_r$ and $\mathcal H_r\mathcal H_r+\mathcal H_r\mathcal H_r$; apply the zero-set statement to real and imaginary parts of differences.

Apply Agler–Young, *Functions which are almost multipliers of Hilbert function spaces*, [arXiv:math/9605224v1, Theorem 2.1](https://arxiv.org/html/math/9605224v1#S2.Thmtheorem1), to their Hilbert function space $H=\mathcal H_r$ on their set $\Omega=\Omega$, their uniqueness domain $D_\varphi=E_0^*$, and their function $\varphi=b|_{E_0^*}$. Their scalar $t$ in (2.1) is $1$, unrelated to the source time $t$, and their integer $m$ can be taken as $k$. The nonsingular-kernel and both uniqueness hypotheses have just been checked. The implication (2)$\Rightarrow$(1), with Definition 1.3 and the isometric identification of $H|_{E_0^*}$ with $H$, supplies a closed finite-codimensional $W\subset\mathcal H_r$ and a bounded map $L:W\to\mathcal H_r$ satisfying $Lu=bu$ on $E_0^*$. Analytic uniqueness then gives $Lu=bu$ throughout $\Omega$.

Use the maximal multiplication domain

$$
D_b=\{u\in\mathcal H_r:bu\in\mathcal H_r\}.
\tag{127.16}
$$

It contains $W$. If $\pi:\mathcal H_r\to\mathcal H_r/W$ is the quotient map, then $D_b=\pi^{-1}(\pi(D_b))$; the image is a linear subspace of a finite-dimensional space and hence closed. Therefore $D_b$ is closed and finite codimensional. If $u_n\to u$ in $D_b$ and $bu_n\to v$ in $\mathcal H_r$, continuity of point evaluation gives $v(p)=b(p)u(p)$ for every $p\in\Omega$. The graph is closed, so $M_b:D_b\to\mathcal H_r$ is bounded. Since rotations preserve $b$ and the norm, they preserve this maximal domain and its orthogonal complement. No rotation invariance of the originally supplied $W$ is needed.

The finite-dimensional circle representation on $D_b^\perp$ has only finitely many angular characters. Choose an integer $\ell$ absent from it. The entire $\ell$ sector of $\mathcal H_r$ lies in $D_b$ and is nonzero: it contains $P^{1/2}$ applied to any nonzero punctured smooth compact-core function of character $\ell$. Multiplication by $b$ preserves that character. By (127.13) it is bounded on the same sector of $\mathcal H_d$. With $K_\ell$ the self-adjoint restriction of the actual $K$ to its $L^2(m)$ angular sector, this means

$$
B_\ell=e^{(d/2)K_\ell}M_be^{-(d/2)K_\ell}
\quad\text{is bounded}.
\tag{127.17}
$$

The spectral-cutoff argument in (122.18)–(122.19), equivalently the argument following (126.3), now applies with heat parameter $s=d$. Explicitly, for $\Pi_R=\mathbf1_{[0,R]}(K_\ell)$ the entire compressed functions

$$
F_R(z)=\Pi_Re^{zK_\ell}M_be^{-zK_\ell}\Pi_R
$$

are bounded by $\|B_\ell\|$ on both lines $\Re z=\pm d/2$; the negative line uses the adjoint because $b$ is real. The three-lines theorem and Cauchy's estimate on a circle of radius $d/4$ give $\|F_R'(0)\|\le4\|B_\ell\|/d$, uniformly in $R$. Spectral limits yield a bounded commutator form $[K_\ell,M_b]$, initially without assuming that multiplication preserves the operator domain. This is exactly the inherited commutator mechanism of §§122 and 126 for the actual endpoint.

Its compact-core consequence can be evaluated using the same local expression (122.9). In the cylindrical coordinates of (126.4), take

$$
u_N=e^{i\ell\theta}\chi(r,z,\xi)e^{iN\zeta\cdot(r,z,\xi)},\qquad
\chi\in C_c^\infty((0,\infty)\times\mathbb R^2),\qquad
\zeta\in\mathbb R^3.
$$

These are genuine punctured smooth core vectors; $bu_N$ also has compact punctured support and is smooth. The divergence-form Leibniz calculation (122.22)–(122.23), or (126.5), gives the term of order $N$ as

$$
-2iN e^{i\ell\theta+iN\zeta\cdot(r,z,\xi)}\chi
\left[a b_r\zeta_r+a b_z\zeta_z+
\left(\eta+\frac{ar^2}{4}\right)b_\xi\zeta_\xi\right].
\tag{127.18}
$$

All other terms are bounded in $L^2(m)$ for fixed $\ell,\chi,\zeta$, and $\|u_N\|_2$ is independent of $N$. The bounded commutator form therefore forces the bracket to vanish on every compact patch for every $\zeta$. Since $a,\eta>0$, this gives $b_r=b_z=b_\xi=0$; rotation invariance gives $b_\theta=0$. Connectedness makes $b$, hence $g$, constant on $\Omega$.

Finally, the source-start contradiction (122.24) applies with no new initial-law assumption. A constant $g_t$ has mass one and equals $1$. For $0<u<t$, injectivity of $T_{t-u}$ and $g_t=T_{t-u}g_u$ give $g_u=1$. Choose $0\ne\psi\in C_c(\Omega)$, $\psi\ge0$. The original source-start continuous paths imply $\mathbb E_e\psi(Z_u)\to\psi(e)=0$ as $u\downarrow0$, whereas $g_u=1$ gives the positive constant $\int\psi\,dm$. This contradiction proves infinite negative index on $\mathcal V_E$. Proposition 127.2 imposes precisely the equations (127.3), proving the constrained assertion. $\square$

The reduction (127.4)–(127.5) holds for all real triples, but it does not determine their global indices. Theorem 127.3 uses the strict lower comparison $c>0$ and only the interval (127.10). It supplies no conclusion at $\gamma=-\alpha$, for stronger opposite-sign competition, or for general $\beta\ne0$ or unequal gaps beyond the results of §§122 and 126. The weighted form $\langle gv,(\alpha P+\gamma P^2)v\rangle$ is not ordered merely by the operator inequality $P^2\le P$; the multiplier argument is the additional step used here. The full mixed-time all-pencil assertion remains undetermined by these results. In particular, infinite index for this marginal pencil does not give the all-pencil hypothesis for the individual quadratic coefficients in (125.2) or (125.3). The complete three-time fiber assertion, all 64 equations, the cubic condition and the remaining native realization boundary retain exactly the additional obligations stated in §§123–126. The analytic regularity, source-start dynamics and spectral-cutoff commutator mechanism used above are those of the retained original family.

## 追加锚（本行以下为增补区）
