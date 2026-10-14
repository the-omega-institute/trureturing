# Real renewal instruments and detector rank II: phase fibers and stationary identification

This volume continues the finite-memory instrument setting of [Real renewal instruments and detector rank](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK.md). It studies which stationary quantum properties are determined by a complete classical output law together with the characteristic polynomial of the averaged channel. All matrix algebras and memory dimensions are over the complex numbers.

## 23. A complete stationary law and the full channel spectrum do not determine purity

**Definition 23.1 (Finite-gap phase instruments and the two observed data).** Fix an integer $H\ge1$, put $d=H+1$, and let $K\subseteq\{1,\ldots,H\}$ contain $H$. Choose $p_k>0$ for $k\in K$ with $\sum_{k\in K}p_k=1$, and set $p_k=0$ for every nonnegative integer outside $K$, including $p_0=0$. For integers $a\ge0$ define

$$
t(a)=\sum_{k\ge a}p_k,\qquad
\mu=\sum_{k\ge0}(k+1)p_k=\sum_{a=0}^H t(a).
\tag{23.1}
$$

On the orthonormal basis $e_0,\ldots,e_H$ of $\mathbb C^d$, let

$$
Se_j=e_{j+1}\ (j<H),\qquad Se_H=0,\qquad
x_\theta=\sum_{k\in K}\sqrt{p_k}\,e^{i\theta_k}e_{H-k},\qquad
J_\theta=x_\theta e_H^*.
\tag{23.2}
$$

Here each $\theta_k\in\mathbb R/(2\pi\mathbb Z)$. Write $E_{ij}=e_ie_j^*$ and define complex-linear CP maps on the full matrix algebra $M_d(\mathbb C)$ by

$$
\mathcal C_0(A)=SAS^*,\qquad
\mathcal C_{1,\theta}(A)=J_\theta A J_\theta^*=A_{HH}x_\theta x_\theta^*,\qquad
\mathcal E_\theta=\mathcal C_0+\mathcal C_{1,\theta}.
\tag{23.3}
$$

For a density $\sigma$, chronological words $w=b_1\cdots b_n$ have probabilities

$$
\mathbb P_{\theta,\sigma}(w)
=\operatorname{Tr}\bigl(\mathcal C_{b_n,\theta}\cdots
\mathcal C_{b_1,\theta}(\sigma)\bigr),\qquad
\mathcal C_{0,\theta}=\mathcal C_0,\qquad
\mathbb P_{\theta,\sigma}(\varnothing)=1.
\tag{23.4}
$$

The complete stationary binary law means all these cylinder probabilities when $\sigma$ is invariant under $\mathcal E_\theta$. The second datum is
$\chi_{\mathcal E_\theta}(\lambda)=\det(\lambda I_{M_d}-\mathcal E_\theta)$, equivalently the entire eigenvalue multiset of this $d^2$-dimensional complex-linear map, with algebraic multiplicities. It contains neither eigenoperators nor Jordan block data. It is a channel spectrum, distinct from the eigenvalues of a Choi matrix or a stationary density, and is not a specification of the channel map or of full process tomography.

**Theorem 23.2 (One phase family with identical complete laws and characteristic polynomials).** For fixed $H,K,p$ in Definition 23.1, every phase choice gives a trace-preserving averaged channel with unique faithful mixed stationary density

$$
R_\theta=\sum_{j=0}^H S^j x_\theta x_\theta^*(S^*)^j,
\qquad \rho_\theta=\frac{R_\theta}{\mu}>0,
\qquad (\rho_\theta)_{ii}=\frac{t(H-i)}{\mu}.
\tag{23.5}
$$

Every word effect is diagonal and independent of $\theta$. More precisely, for any two phases $\theta,\eta$ and any densities $\sigma,\omega$ on this same carrier,

$$
\bigl[\mathbb P_{\theta,\sigma}(w)=\mathbb P_{\eta,\omega}(w)
\text{ for every finite }w\bigr]
\quad\Longleftrightarrow\quad
\sigma_{ii}=\omega_{ii}\text{ for every }i.
\tag{23.6}
$$

In stationarity the common law $\mathbb P_p$ is, for $m\ge1$ ticks and nonnegative integers $a,b,g_1,\ldots,g_{m-1}$,

$$
\mathbb P_p(0^a1\,0^{g_1}1\cdots0^{g_{m-1}}1\,0^b)
=\frac{t(a)t(b)}{\mu}\prod_{j=1}^{m-1}p_{g_j},
\tag{23.7}
$$

where the product is one for a single tick, and

$$
\mathbb P_p(0^N)=\frac1\mu\sum_{k\ge N}(k-N+1)p_k
\quad(N\ge0).
\tag{23.8}
$$

Thus (23.8) includes the empty word. Consecutive ticks have probability zero because $p_0=0$. The complete law determines the gap probabilities by

$$
p_k=\frac{\mathbb P_p(10^k1)}{\mathbb P_p(1)},\qquad
\mathbb P_p(1)=\mu^{-1}>0.
\tag{23.9}
$$

Nevertheless the full channel characteristic polynomial is independent of all phases:

$$
\chi_{\mathcal E_\theta}(\lambda)
=\lambda^{d^2-d}\left(\lambda^{H+1}-\sum_{k=1}^H p_k\lambda^{H-k}\right).
\tag{23.10}
$$

Proof. The normalization of $x_\theta$ gives

$$
S^*S=I-E_{HH},\qquad J_\theta^*J_\theta=E_{HH}.
\tag{23.11}
$$

Hence the two branches form an instrument and their sum is trace preserving. Suppress $\theta$ temporarily and put $\mathcal L(A)=SAS^*$. Since $S^d=0$, $\mathcal L^d=0$. Directly from the coordinates of $x$,

$$
\|S^j x\|^2=t(j),\qquad
\operatorname{Tr}R=\mu,\qquad
R_{HH}=\sum_{j=0}^H|x_{H-j}|^2=1,\qquad
R_{ii}=t(H-i).
\tag{23.12}
$$

Telescoping gives $\mathcal L(R)=R-xx^*$ and $\mathcal C_1(R)=xx^*$, so $R/\mu$ is invariant. Because $x_0=\sqrt{p_H}e^{i\theta_H}\ne0$, the columns $x,Sx,\ldots,S^Hx$ form a triangular matrix with nonzero diagonal. They span $\mathbb C^d$, so their Gram sum $R$ is positive definite. For any matrix $A$ satisfying $\mathcal E(A)=A$, the fixed-point equation and the finite inverse of $I-\mathcal L$ give

$$
(I-\mathcal L)A=A_{HH}xx^*,\qquad
A=A_{HH}\sum_{j=0}^H\mathcal L^j(xx^*)=A_{HH}R.
\tag{23.13}
$$

Trace one therefore forces $A=\rho_\theta$. This proves uniqueness on the full complex matrix algebra, not merely among diagonal states.

For diagonal $F=\operatorname{diag}(f_0,\ldots,f_H)$, the trace-dual maps are

$$
\begin{aligned}
\mathcal C_0^*(F)&=\operatorname{diag}(f_1,\ldots,f_H,0),\\
\mathcal C_{1,\theta}^*(F)&=
\left(\sum_{k\in K}p_k f_{H-k}\right)E_{HH}.
\end{aligned}
\tag{23.14}
$$

Starting from $I$, iteration of these formulas shows that the effect
$F_w=\mathcal C_{b_1,\theta}^*\cdots\mathcal C_{b_n,\theta}^*(I)$ is diagonal and phase independent. Conversely, the effects of the words $0^a1$, for $0\le a\le H$, are

$$
F_{0^a1}=(\mathcal C_0^*)^a(E_{HH})=E_{H-a,H-a}.
\tag{23.15}
$$

These effects recover every initial diagonal entry, proving both directions of (23.6), including comparisons between different phases.

For a first tick after $a$ zeros, (23.12) yields
$\mathcal C_1\mathcal L^a(\rho)=t(a)xx^*/\mu$; it is zero for $a>H$. For subsequent complete gaps,
$\mathcal C_1\mathcal L^g(xx^*)=p_gxx^*$, and a terminal zero run has trace $\operatorname{Tr}\mathcal L^b(xx^*)=t(b)$. Multiplication gives (23.7). Without a tick,

$$
\operatorname{Tr}\mathcal L^N(\rho)
=\frac1\mu\sum_{j=0}^H t(N+j)
=\frac1\mu\sum_{k\ge N}(k-N+1)p_k,
\tag{23.16}
$$

which proves (23.8) and then (23.9). Phase changes preserving output statistics have the established precedent of [Liu, Elliott, Binder, Di Franco and Gu, *Optimal stochastic modelling with unitary quantum dynamics*, arXiv:1810.09668, equation (6) and Theorem 1](https://arxiv.org/pdf/1810.09668); their equation (7) concerns phase-dependent stationary memory measures. The identities here additionally connect this finite-gap instrument's entire stationary law to the channel characteristic polynomial below.

Define the actual diagonal quotient $D:M_d(\mathbb C)\to\mathbb C^d$ by $D(A)=(A_{00},\ldots,A_{HH})^{\mathsf T}$. Put

$$
\mathcal N=\ker D,\qquad q_i=p_{H-i},\qquad
Pe_j=e_{j+1}\ (j<H),\qquad Pe_H=q.
\tag{23.17}
$$

Then $D\mathcal E_\theta=PD$ and $\dim_{\mathbb C}\mathcal N=d^2-d$. On $\mathcal N$ the tick branch vanishes, so
$T=\mathcal E_\theta|_{\mathcal N}$ is $T(A)=SAS^*$. For $i\ne j$, $T^H(E_{ij})=0$: at least one shifted index exceeds $H$. Thus $T^H=0$. This is a statement on $\mathcal N$; on the full algebra the no-tick map has exact order $H+1$, since $\mathcal L^H(E_{00})=E_{HH}\ne0$.

The diagonal matrices do not in general form an invariant subspace: $\mathcal E_\theta(E_{HH})=x_\theta x_\theta^*$ has off-diagonal entries whenever $|K|\ge2$. In the vector-space splitting
$A=(A-\operatorname{diag}D(A))+\operatorname{diag}D(A)$, the channel instead has the block form

$$
\mathcal E_\theta=
\begin{pmatrix}T&B_\theta\\0&P\end{pmatrix},\qquad
B_\theta(v)=v_H\bigl(x_\theta x_\theta^*-\operatorname{diag}q\bigr).
\tag{23.18}
$$

Use the block triangular determinant identity, as stated in [Mathlib, `Matrix.charpoly_fromBlocks_zero₂₁`, revision `db584cd6d46c92f209a44c0f1c829460d327499d`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean). It gives $\chi_{\mathcal E_\theta}=\chi_T\chi_P$. Nilpotence on the $(d^2-d)$-dimensional space gives $\chi_T(\lambda)=\lambda^{d^2-d}$. The shift columns and last column $q$ of $P$ give, by expansion of $\det(\lambda I-P)$,

$$
\chi_P(\lambda)=\lambda^d-\sum_{i=0}^H q_i\lambda^i
=\lambda^{H+1}-\sum_{k=1}^H p_k\lambda^{H-k}.
\tag{23.19}
$$

These intermediate determinant and nilpotence facts prove (23.10) even though $B_\theta$ depends on phase. $\square$

**Proposition 23.3 (Explicit four-dimensional stationary purity separation).** Take $H=3$, $K=\{1,2,3\}$ and $p_1=p_2=p_3=1/3$. Then $\mu=3$, every phase has stationary diagonal $(1,2,3,3)/9$, and

$$
\delta=\theta_1-2\theta_2+\theta_3,\qquad
\operatorname{Tr}(\rho_\theta^2)=\frac{37+8\cos\delta}{81}.
\tag{23.20}
$$

In particular, $\theta^+=(0,0,0)$ and $\theta^-=(\pi,0,0)$ give

$$
9\rho_+=
\begin{pmatrix}
1&1&1&0\\1&2&2&1\\1&2&3&2\\0&1&2&3
\end{pmatrix},\qquad
9\rho_-=
\begin{pmatrix}
1&1&-1&0\\1&2&0&-1\\-1&0&3&0\\0&-1&0&3
\end{pmatrix},
\tag{23.21}
$$

with purities $5/9$ and $29/81$, respectively. Their complete stationary binary laws coincide, and both averaged channels on $M_4(\mathbb C)$ have

$$
\chi_{\mathcal E_\pm}(\lambda)
=\lambda^{12}\left[\lambda^4-\frac{\lambda^2+\lambda+1}{3}\right].
\tag{23.22}
$$

The actual stationary-family purity range is exactly $[29/81,5/9]$. The larger set of all densities with the same diagonal, without requiring stationarity for any member of this instrument family, has purity range $[23/81,1]$.

Proof. Write $z_k=e^{i\theta_k}$, $a=z_3\overline z_2$, $b=z_3\overline z_1$ and $c=z_2\overline z_1$. Summing the four shifted outer products in (23.5) gives

$$
9\rho_\theta=
\begin{pmatrix}
1&a&b&0\\
\overline a&2&a+c&b\\
\overline b&\overline a+\overline c&3&a+c\\
0&\overline b&\overline a+\overline c&3
\end{pmatrix}.
\tag{23.23}
$$

Here $|a|=|b|=|c|=1$ and $|a+c|^2=2+2\cos\delta$. The squared diagonal sum is $23$ and the sum of squared moduli strictly above the diagonal is $7+4\cos\delta$. Hermiticity therefore gives $81\operatorname{Tr}\rho_\theta^2=23+2(7+4\cos\delta)$, proving (23.20). Substituting the two phase triples yields exactly (23.21); faithfulness and stationarity follow from (23.5). Theorem 23.2 supplies their equal complete laws and (23.22).

Varying $\delta$ attains every value in $[29/81,5/9]$. To distinguish this stationary family from the arbitrary fixed-diagonal fiber, put $w=(1,2,3,3)/9$. For any density $\sigma$ with diagonal $w$,
$\operatorname{Tr}\sigma^2=\sum_iw_i^2+\sum_{i\ne j}|\sigma_{ij}|^2\ge23/81$, while positivity and trace one give $\operatorname{Tr}\sigma^2\le1$. The lower endpoint is $\operatorname{diag}w$ and the upper is $vv^*$ with $v_i=\sqrt{w_i}$. The segment $(1-s)\operatorname{diag}w+s vv^*$, $0\le s\le1$, has purity $23/81+(1-23/81)s^2$, so it fills that larger interval. It does not enlarge the stationary range (23.20). $\square$

**Theorem 23.4 (Minimum homogeneous memory and failure of joint-data identification).** Every instrument in Proposition 23.3 has minimum complex memory dimension four among all exact finite homogeneous binary CP realizations of its stationary law. The competitor may have arbitrary Kraus counts and any mixed initial density, without a reset or invariant-initialization assumption. All persistent classical, quantum and controller registers influencing future outputs are included in its memory dimension; the comparison allows no uncounted external time-dependent controller.

Consequently the map

$$
\theta\longmapsto\bigl(\mathbb P_p,\chi_{\mathcal E_\theta}\bigr)
\tag{23.24}
$$

is constant on this family of minimum four-dimensional memories, whereas $\theta\mapsto\operatorname{Tr}\rho_\theta^2$ is not. No function of the complete stationary binary law and the entire averaged-channel eigenvalue multiset, even with the minimum memory dimension supplied, returns stationary purity for every member. The channels $\mathcal E_+$ and $\mathcal E_-$ are not conjugate by any memory unitary; their outcome-labeled CP instruments are therefore not unitarily equivalent, even allowing arbitrary scalar phases on the individual Kraus operators.

Proof. Let a competitor act on $M_D(\mathbb C)$, with no-tick map $\Phi$, tick map $\Psi$, trace-preserving sum $\Phi+\Psi$ and initial density $\sigma$. Equality of all stationary cylinders gives the actual tick probability $\operatorname{Tr}\Psi(\sigma)=1/3$. Its actual normalized posterior

$$
\tau_0=3\Psi(\sigma)
\tag{23.25}
$$

is a density. As in the actual-posterior extinction mechanism of [Theorem 21.8 in the preceding volume](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK.md), cylinders starting with a tick imply

$$
\operatorname{Tr}\Phi^k(\tau_0)
=\frac{\mathbb P_p(10^k)}{\mathbb P_p(1)}=t(k),\qquad
\operatorname{Tr}\Phi^3(\tau_0)=\frac13>0,\qquad
\Phi^4(\tau_0)=0.
\tag{23.26}
$$

The last equality uses positivity and zero trace, not an assumption that $\Phi$ vanishes on its unused ambient space.

Write $\Phi(A)=\sum_iK_iAK_i^*$, let $K_w$ range over all finite no-tick Kraus products including the empty product, and put

$$
U=\operatorname{span}\{K_w\operatorname{ran}\tau_0:w\text{ a finite Kraus word}\}.
\tag{23.27}
$$

Since

$$
0=\operatorname{Tr}\Phi^4(\tau_0)
=\sum_{|w|=4}\|K_w\tau_0^{1/2}\|_{\rm HS}^2,
\tag{23.28}
$$

every length-four product kills $\operatorname{ran}\tau_0$, and hence every longer product does too. Thus $U$ is invariant under every $K_i$, is spanned by words of length at most three, and every length-four product kills $U$: its action on a generator is a product of length at least four on $\operatorname{ran}\tau_0$. The restricted CP map on $M(U)$ therefore has nilpotency order exactly four; its third power is nonzero by (23.26).

Now apply [Bhat–Mallick, *Nilpotent Completely Positive Maps*, arXiv:1310.0591v1, Proposition 2.2 and Corollary 2.5](https://arxiv.org/pdf/1310.0591v1) on this invariant reachable space. Their Kraus-product criterion identifies nilpotence, and their bound on the order yields

$$
4\le\dim_{\mathbb C}U\le D.
\tag{23.29}
$$

Their convention $A\mapsto\sum_iL_i^*AL_i$ applies with $L_i=(K_i|_U)^*$. No purity of $\tau_0$, trace preservation of the restricted branch, or global reset is required. The explicit four-dimensional models attain the bound for every phase.

Equations (23.7)–(23.10) and (23.20) show that (23.24) is constant while purity takes two distinct values. A function of that constant pair would have to return both $5/9$ and $29/81$, which is impossible. The complete law already recovers every $p_k$ by (23.9); for the fixed minimal carrier here, adding (23.22) separates no phases.

For unitary conjugacy, suppose $\mathcal E_-\circ\operatorname{Ad}_V=\operatorname{Ad}_V\circ\mathcal E_+$, where $\operatorname{Ad}_V(A)=VAV^*$. Uniqueness of the stationary density gives $\rho_-=V\rho_+V^*$, contradicting their different purities. Outcome-labeled instrument equivalence means the same intertwining identity for each CP branch, so it would imply that channel identity after summation. Multiplying a Kraus operator by a scalar of modulus one does not change its CP map and cannot avoid this contradiction; exact matrix intertwining of chosen Kraus representatives is not imposed.

This nonidentification concerns the two data of Definition 23.1 in the exact homogeneous finite-memory class. It asserts no equality or difference of Jordan forms or mixing constants, and no insufficiency of stronger quantum intervention data. It supplies neither an approximation comparison nor a memory-advantage or physical-realization claim. $\square$

## 追加锚（本行以下为增补区）
