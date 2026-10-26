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
