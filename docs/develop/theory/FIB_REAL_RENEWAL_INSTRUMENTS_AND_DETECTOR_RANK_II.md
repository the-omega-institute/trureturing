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

## 24. Three coherent outputs identify the shift/reset orbit after an observed tick

**Definition 24.1 (The fixed family and the permitted output access).** Specialize Definition 23.1 to $H=3$, $d=4$, $K=\{1,2,3\}$ and fixed known $p_1,p_2,p_3>0$ with sum one. Put

$$
c_k=\sqrt{p_k}e^{i\theta_k},\qquad
x=x_\theta=(c_3,c_2,c_1,0)^{\mathsf T},\qquad
q=p_2+p_3,\qquad \mu=2p_1+3p_2+4p_3,
\qquad \delta=\theta_1-2\theta_2+\theta_3.
\tag{24.1}
$$

The memory is $\mathbb C^4$, $Se_j=e_{j+1}$ for $j<3$, $Se_3=0$, $J_\theta=xe_3^*$, and the branches are $\mathcal C_0(A)=SAS^*$ and $\mathcal C_{1,\theta}(A)=J_\theta A J_\theta^*$. Their sum is $\mathcal E_\theta$. Inner products are conjugate-linear in the first entry. For chronological $w=b_1\cdots b_n$, set $K_0=S$, $K_1=J_\theta$ and $K_w=K_{b_n}\cdots K_{b_1}$.

An actual observed outcome $1$ is a heralded tick. After that tick, supply the additional ability to apply the same fixed isometry

$$
V_\theta\psi=S\psi\otimes|0\rangle+J_\theta\psi\otimes|1\rangle
\tag{24.2}
$$

successively, retaining its chronological output flags coherently and accessibly. The branch representatives are stable during these uses; no inaccessible environment retains which-branch records. There are no intermediate memory interventions and no terminal memory measurement. A permitted terminal POVM on the $n$ flags has every effect commuting with

$$
N_1=\sum_{r=1}^n |1\rangle\langle1|_r.
$$

Arbitrary measurements within each eigenspace of $N_1$ are allowed, but no external reference breaking this count symmetry is supplied. If $P_m^{(n)}$ projects onto words with $m$ ticks, the complete observable datum is the count-sector twirl

$$
T_{n,\theta}=\mathcal T_n(\Omega_{n,\theta}),\qquad
\mathcal T_n(A)=\sum_{m=0}^n P_m^{(n)} A P_m^{(n)},
\qquad
\Omega_{n,\theta}=\operatorname{Tr}_{\mathbb C^4}
\left|\sum_{w\in\{0,1\}^n}K_wx\otimes|w\rangle\right\rangle
\left\langle\sum_{w\in\{0,1\}^n}K_wx\otimes|w\rangle\right|.
\tag{24.3}
$$

Indeed all permitted effects have the same expectation on $\Omega$ and $\mathcal T_n(\Omega)$, and their unrestricted choices inside the blocks determine each block. Replacing $S,J$ by $e^{i\alpha_0}S,e^{i\alpha_1}J$ multiplies a length-$n$, count-$m$ amplitude by $e^{i[(n-m)\alpha_0+m\alpha_1]}$. Thus these independent constant branch phases cancel within every retained block; averaging them gives precisely $\mathcal T_n$. Stability across uses is essential: independently varying phases at each time are a different access model.

Memory-unitary equivalence of the averaged channels means that some unitary $U$ satisfies $\mathcal E_{\theta'}\circ\operatorname{Ad}_U=\operatorname{Ad}_U\circ\mathcal E_\theta$, where $\operatorname{Ad}_U(A)=UAU^*$. Outcome-labeled instrument equivalence requires the same equation separately for the two CP branches, with their labels fixed. These definitions concern CP maps and allow scalar phases on Kraus representatives.

**Theorem 24.2 (Operational identification, exact horizon and a mirror obstruction).** In the fixed positive family of Definition 24.1, define

$$
C_\theta=\langle010|\Omega_{3,\theta}|001\rangle.
$$

For any two phase triples $\theta,\theta'$, the following five conditions are equivalent:

1. $T_{3,\theta}=T_{3,\theta'}$ after an actual observed tick in each device.
2. $C_\theta=C_{\theta'}$ as complex numbers.
3. $e^{i\delta}=e^{i\delta'}$.
4. The averaged channels are memory-unitarily equivalent.
5. The outcome-labeled instruments are memory-unitarily equivalent.

The least complete post-tick horizon in the specified access class is exactly three. A fixed randomized choice between two count-preserving projective measurements, retaining the setting, gives a six-outcome distribution that separates these orbits. From any initial density, monitoring for an actual tick takes at most four device applications almost surely, counting the tick itself. Each trial then uses three coherent applications, so the whole separating trial uses at most seven applications.

This is injectivity of a finite-outcome distribution map on the family of orbits. It is not recovery of an unknown continuous phase with zero error from finitely many samples. Even finitely many copies of the complete $T_{3,\theta}$ do not perfectly discriminate distinct phases. Furthermore, the stationary-density eigenvalue multiset and all pairwise trace overlaps of the actual history posteriors together fail to identify the orbit: the phases $(\pi/2,0,0)$ and $(-\pi/2,0,0)$ give a counterexample. Classification is restricted to this supplied shift/reset family, not to all four-dimensional CP realizations of its classical law.

Proof. Theorem 23.2 supplies the unique stationary density, the complete classical law and the normalization $S^*S+J^*J=I$; the last identity makes (24.2) an isometry. Its nonidentification result is the antecedent here. The new observable comparison uses the additional access of Definition 24.1.

*Actual history posteriors and their oriented cycle.* For every input density $\sigma$,

$$
\mathcal C_{1,\theta}(\sigma)=\sigma_{33}xx^*.
$$

Whenever a tick actually occurs, its normalized posterior is therefore $\tau_0=xx^*$, independently of the input. Write $v_j=S^jx$. The stationary histories $10^j$, for $j=1,2,3$, have normalized posteriors

$$
\begin{aligned}
v_1&=(0,c_3,c_2,c_1)^{\mathsf T},&\|v_1\|^2&=1,\\
v_2&=(0,0,c_3,c_2)^{\mathsf T},&\|v_2\|^2&=q,\\
v_3&=(0,0,0,c_3)^{\mathsf T},&\|v_3\|^2&=p_3,\\
\tau_j&=v_jv_j^*/\|v_j\|^2.&&
\end{aligned}
\tag{24.4}
$$

Their cylinder probabilities are respectively $1/\mu,q/\mu,p_3/\mu$, all positive, by (23.7). For this ordered tuple, direct substitution gives

$$
\begin{aligned}
B_\theta:=\operatorname{Tr}(\tau_1\tau_2\tau_3)
&=\frac{\langle v_1,v_2\rangle\langle v_2,v_3\rangle
              \langle v_3,v_1\rangle}{q p_3}\\
&=\frac{(\overline c_2c_3+\overline c_1c_2)
                (\overline c_2c_3)(\overline c_3c_1)}{q p_3}\\
&=\frac{p_1p_2+c_1c_3\overline c_2^{\,2}}{q}
 =\frac{p_1p_2+p_2\sqrt{p_1p_3}e^{i\delta}}{q},\\
e^{i\delta}&=\frac{qB_\theta-p_1p_2}{p_2\sqrt{p_1p_3}}.
\end{aligned}
\tag{24.5}
$$

The inverse divides only by a strictly positive number; it remains valid when $B_\theta=0$. Reversing the cycle conjugates $B_\theta$. No argument of $B_\theta$ is used.

The trace-product invariant and its orientation are the known Bargmann construction: [Oszmaniec–Brod–Galvão, arXiv:2109.10006v1, equation (1), PDF p. 1, and Figure 1/Theorem 1, p. 2](https://arxiv.org/pdf/2109.10006v1). The corresponding common-source and zero-overlap qualifications are already in [Hidden Relations, C-9.7, C-10.1–C-10.2 and C-27.5.2](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md), [Local Choice Geometry, 7.1–7.2](FIB_ATOM_LOCAL_CHOICE_GEOMETRY.md), and [Second-Order Relation Completion, 68.1–68.2](AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md). Here their consumer is the actual tuple (24.4), rather than an independently posited tuple of states.

For the convention $W_{\rm cyc}|a,b,c\rangle=|b,c,a\rangle$, the standard cycle identity is

$$
\operatorname{Tr}\bigl[W_{\rm cyc}(\tau_1\otimes\tau_2\otimes\tau_3)\bigr]
=\operatorname{Tr}(\tau_1\tau_2\tau_3)=B_\theta.
\tag{24.6}
$$

The cited cycle test would require three independently prepared, stored $\mathbb C^4$ posteriors, a control qubit and controlled permutation access, together with their preparation controllers. After a herald, the acceptances for $j$ further observed zeros are $1,q,p_3$; positivity gives repeated preparation with success almost surely, but not a deterministic bound on the number of attempts for $j=2,3$. The four-use herald bound prepares only $\tau_0$. Equation (24.6) specifies a resource-dependent alternative; the direct output measurement below needs none of these three stored posteriors.

*The channel orbit in this family.* A phase change of $x$ alone is not the relevant channel gauge, because the same memory unitary must also conjugate $S$. Fixed positive probabilities on the three-dimensional support of $x$ have the familiar projective relative-phase coordinates; these are the probability-fiber constructions [InteriorProbabilityPhaseFiber](../../../D5/S3/Quantum/Fibers/InteriorProbabilityPhaseFiber.lean) and [ProjectiveInteriorProbabilityFiber](../../../D5/S3/Quantum/Fibers/ProjectiveInteriorProbabilityFiber.lean), with two relative phases. Their strict-interior domain is this three-coordinate support, not all four ambient coordinates. They do not impose the shift constraint; we impose it now.

The Kraus span $\operatorname{span}\{S,J_\theta\}$ has dimension two. More generally, within Definition 23.1 for $H\ge2$ and $c_H=\sqrt{p_H}e^{i\theta_H}\ne0$, its matrix pencil satisfies

$$
\det(uS+vJ_\theta)=(-1)^H u^H v c_H.
\tag{24.7}
$$

Indeed the first $H$ columns are $ue_1,\ldots,ue_H$, and only the $e_0$ component of the last column $vx_\theta$ contributes to the determinant. Consequently its only singular projective lines are $\mathbb C S$ of rank $H$ and $\mathbb C J_\theta$ of rank one. In the present family these ranks are three and one, so they cannot be interchanged by unitary conjugation. The rank distinction excludes $H=1$ from this argument.

Suppose averaged-channel equivalence holds. Use a fixed vectorization convention, and form the full-column-rank matrices

$$
F=[\operatorname{vec}S,\operatorname{vec}J_{\theta'}],\qquad
G=[\operatorname{vec}(USU^*),\operatorname{vec}(UJ_\theta U^*)].
$$

The exact channel identity gives equality of Choi matrices $FF^*=GG^*$. It first gives equality of their ranges, so $G=FM$ for an invertible two-by-two matrix $M$. If $L=(F^*F)^{-1}F^*$, multiplying $FF^*=FMM^*F^*$ on the left by $L$ and on the right by $L^*$ yields $MM^*=I$. The rank distinction in (24.7) then makes $M$ diagonal, hence diagonal unitary. Thus, for real $t,s$,

$$
USU^*=e^{it}S,\qquad UJ_\theta U^*=e^{is}J_{\theta'}.
\tag{24.8}
$$

This uses exact Choi equality, not merely equality of Kraus spans. Equivalently, the scalar magnitudes in (24.8) are forced by the preserved Hilbert–Schmidt norms $\sqrt H$ and $1$.

The first identity preserves $\ker S^*=\mathbb C e_0$. With $Ue_0=e^{i\gamma}e_0$, the relation $US=e^{it}SU$ gives successively

$$
Ue_j=e^{i\gamma}e^{ijt}e_j\quad(0\le j\le H).
$$

Conjugation of $J_\theta$ therefore multiplies its $c_k$ coefficient by $e^{-ikt}$. The second identity in (24.8) forces

$$
\theta'_k-\theta_k=a+bk\pmod{2\pi}\quad(k\in K),
\qquad a=-s,\quad b=-t.
\tag{24.9}
$$

Conversely, whenever (24.9) holds, $Ue_j=e^{-ijb}e_j$ gives $USU^*=e^{-ib}S$ and $UJ_\theta U^*=e^{-ia}J_{\theta'}$. These scalar branch phases cancel in the CP maps, proving outcome-labeled equivalence and therefore averaged-channel equivalence.

For $K=\{1,2,3\}$, affine differences imply $\delta'=\delta$ modulo $2\pi$. Conversely, if these second differences agree, put $d_k=\theta'_k-\theta_k$ in $\mathbb R/(2\pi\mathbb Z)$ and choose

$$
b=d_2-d_1,\qquad a=2d_1-d_2.
$$

Then $a+b=d_1$, $a+2b=d_2$, and $a+3b=2d_2-d_1=d_3$. This proves the equivalence of conditions 3–5 without treating a general tuple-invariant theorem as a channel-classification theorem.

*The directly accessible three-output density.* The partial trace in (24.3) has entries

$$
(\Omega_{n,\theta})_{w,w'}=\langle K_{w'}x,K_wx\rangle.
\tag{24.10}
$$

The only nonzero length-three amplitudes are

$$
K_{000}x=c_3e_3,\qquad K_{001}x=c_2x,\qquad
K_{010}x=c_1Sx.
$$

For example, chronology gives $K_{001}=JS^2$ and $K_{010}=SJS$. Their squared norms are $p_3,p_2,p_1$, and the two count-one words give

$$
\begin{aligned}
C_\theta
&=\langle c_2x,c_1Sx\rangle
 =\overline c_2c_1(\overline c_2c_3+\overline c_1c_2)\\
&=p_1p_2+p_2\sqrt{p_1p_3}e^{i\delta}=qB_\theta,\\
T_{3,\theta}
&=p_3|000\rangle\langle000|+p_2|001\rangle\langle001|
  +p_1|010\rangle\langle010|\\
&\quad+C_\theta|010\rangle\langle001|
       +\overline C_\theta|001\rangle\langle010|.
\end{aligned}
\tag{24.11}
$$

Both interfering words have two zeros and one tick. Their relative coherence therefore survives precisely the branch-phase symmetry in Definition 24.1. Since $p$ is fixed and $p_2\sqrt{p_1p_3}>0$, (24.11) and (24.5) establish the equivalence of conditions 1–3, completing all five equivalences.

Set

$$
A=|001\rangle\langle010|,\qquad
X=A+A^*,\qquad Y=(A-A^*)/i.
\tag{24.12}
$$

These are unnormalized Hermitian quadratures: the usual Hermitian real and imaginary parts of $A$ are $X/2,Y/2$. Both commute with $N_1$, have eigenvalues $+1,-1,0$, and satisfy

$$
\operatorname{Tr}(T_{3,\theta}X)=2\operatorname{Re}C_\theta,\qquad
\operatorname{Tr}(T_{3,\theta}Y)=2\operatorname{Im}C_\theta.
$$

For outcomes ordered $(+1,-1,0)$, their distributions are

$$
\begin{aligned}
\Pr(X)&=\left(\frac{p_1+p_2}{2}+\operatorname{Re}C_\theta,
              \frac{p_1+p_2}{2}-\operatorname{Re}C_\theta,p_3\right),\\
\Pr(Y)&=\left(\frac{p_1+p_2}{2}+\operatorname{Im}C_\theta,
              \frac{p_1+p_2}{2}-\operatorname{Im}C_\theta,p_3\right).
\end{aligned}
\tag{24.13}
$$

Choose $X$ or $Y$ independently with probability $1/2$ and retain the setting. The resulting six probabilities are one half of the respective entries in (24.13). They determine both components of $C_\theta$, and hence the orbit. Measurement vectors may be taken as $(|001\rangle\pm|010\rangle)/\sqrt2$ for $X$ and $(|001\rangle\pm i|010\rangle)/\sqrt2$ for $Y$; their orthogonal complements give the zero outcomes. The imaginary quadrature needs the allowed within-sector control, not an asymmetric reference between different count sectors.

*Why three is the minimum and finite samples remain statistical.* At one future use $Jx=0$, so $\Omega_{1,\theta}=|0\rangle\langle0|$. At two uses only $00,01$ survive, with memory amplitudes $S^2x$ and $c_1x$. Thus

$$
T_{1,\theta}=|0\rangle\langle0|,\qquad
T_{2,\theta}=q|00\rangle\langle00|+p_1|01\rangle\langle01|.
\tag{24.14}
$$

The complete permitted data at either horizon are phase independent, while the mirror pair below belongs to distinct orbits. Even repeated trials using only these data cannot separate that pair. Equation (24.13) attains separation at horizon three. This lower bound concerns the stated post-tick flag access only; arbitrary memory interventions, different starting preparations, joint access to stored memory states, or a symmetry-breaking reference are different tasks.

Here $\|x\|=\|Sx\|=1$ and $|\langle x,Sx\rangle|<1$: equality in Cauchy–Schwarz would imply $Sx=\lambda x$ for $|\lambda|=1$, contradicting $S^4=0$ and $x\ne0$. Consequently

$$
|C_\theta|=\sqrt{p_1p_2}\,|\langle x,Sx\rangle|
<\sqrt{p_1p_2}\le\frac{p_1+p_2}{2}.
\tag{24.15}
$$

All six probabilities in (24.13), after the factor $1/2$, are strictly positive for every phase. Also the count-one block of (24.11) has positive determinant $p_1p_2-|C_\theta|^2$, while $p_3>0$. Every $T_{3,\theta}$ is therefore strictly positive on the same support $\operatorname{span}\{|000\rangle,|001\rangle,|010\rangle\}$. Its finite tensor powers share the corresponding tensor-power support. A positive POVM effect having zero expectation under a positive definite density on this support vanishes there, and hence has zero expectation for every other member. Thus no finite collective measurement on these copies can perfectly discriminate two distinct phases. Distributional separation supplies neither exact probabilities for free nor finite-sample zero-error inference.

*The mirror counterexample inside the same model.* Let $\theta^+=(\pi/2,0,0)$ and $\theta^-=-\theta^+$. Since $S$ is real and $x_-=\overline{x_+}$, (23.5) and (24.4) give

$$
\rho_-=\overline{\rho_+},\qquad
\tau_j^-=\overline{\tau_j^+}\quad(0\le j\le3).
$$

Complex conjugation preserves the real eigenvalues and their multiplicities for a Hermitian density. The branch maps also commute with conjugation between the two models, so the normalized posteriors of every positive-probability stationary history are conjugate. For any two density matrices $A,B$, $\operatorname{Tr}(AB)=\operatorname{Tr}(A^{1/2}BA^{1/2})$ is real and nonnegative. Thus every pairwise posterior overlap is the same in the two models. Explicitly,

$$
\begin{aligned}
\operatorname{Tr}(\tau_1\tau_3)&=p_1,\\
\operatorname{Tr}(\tau_2\tau_3)&=p_2/q,\\
\operatorname{Tr}(\tau_1\tau_2)
&=\frac{p_2(p_1+p_3)+2p_2\sqrt{p_1p_3}\cos\delta}{q},\\
B_\pm&=\frac{p_1p_2\pm i p_2\sqrt{p_1p_3}}{q}.
\end{aligned}
\tag{24.16}
$$

The two values of $e^{i\delta}$ are $i$ and $-i$. The proved classification therefore separates their channel and labeled-instrument orbits despite equal full stationary spectra and pairwise SWAP data. Their $X$ distributions agree and their $Y$ distributions differ by (24.13).

The general mirror mechanism is already in the cited C-9.7 and Local Choice Geometry 7.2. A communication-task precedent is [Elliott, *Strict advantage of complex quantum theory in a communication task*, arXiv:2505.16523v2, §III.D equation (5), §III.E equation (6), and Appendices B–C](https://arxiv.org/pdf/2505.16523v2): its conjugate strategies have oppositely oriented nonreal Bargmann invariants. That communication advantage is not transferred here. By Theorem 23.2 the same classical renewal law has the real realization $\theta=(0,0,0)$ on the same four-dimensional carrier. Nonreal $B_\theta$ obstructs making this ordered posterior tuple simultaneously real by a common unitary, but gives no complex-over-real advantage for generating this classical law.

*Actual preparation and the charged resources.* Starting from any density $\sigma$, the event that the first tick occurs after $r$ zeros has probability

$$
\Pr_\sigma(0^r1)
=\operatorname{Tr}(JS^r\sigma(S^*)^rJ^*)
=\sigma_{3-r,3-r}\quad(0\le r\le3).
\tag{24.17}
$$

These four mutually exclusive probabilities sum to one. The all-zero word of length four has probability zero because $S^4=0$. Monitoring until the actual tick therefore prepares $xx^*$ in at most four applications almost surely, including the tick. Stop monitoring the future flags at that instant and perform the three coherent uses of (24.2). Reherald before every trial, including when the preceding terminal measurement has changed the memory state. The reset holds for every conditional input density, so each completed trial has the same distribution (24.13) under the stable-device assumptions. The bound $4+3=7$ is for this instrument; the classical-law comparison class in Theorem 23.4 does not inherit this reset bound.

A sufficient logical apparatus consists of the device memory $\mathbb C^4$, three stored output qubits (joint dimension eight), one reusable two-level herald detector, a six-state controller with states $\mathrm{wait},\mathrm{captured}_0,\mathrm{captured}_1,\mathrm{captured}_2,\mathrm{captured}_3,\mathrm{done}$, a two-state $X/Y$ setting register and a three-level outcome pointer for $+1,-1,0$. Each is counted separately; repetitions also require storage or processing of the retained setting/outcome data. A terminal projective pointer coupling can preserve every count sector: if $Q_+,Q_-,Q_0$ are the spectral projections of the chosen observable, the unitary $\sum_{z\in\{+,-,0\}}Q_z\otimes R_z$, with pointer unitaries taking its ready state to the three distinct outcomes, commutes with $N_1\otimes I$. The six-state controller supplies the wait, capture and termination logic; its states do not assert an optimal apparatus dimension. No optimized energy, elapsed-time or hardware cost follows, and the generator dimension in Theorem 23.4 is not an apparatus bound.

Finally, a classical CP-instrument interface alone need not provide (24.2) as an accessible coherent output. For example, the dilation

$$
\widetilde V\psi=S\psi\otimes|0\rangle\otimes|r_0\rangle
 +J\psi\otimes|1\rangle\otimes|r_1\rangle,
\qquad \langle r_0,r_1\rangle=0,
\tag{24.18}
$$

with a fresh inaccessible record at each use has exactly the same two CP branches on measurement of the flag. Tracing those records makes distinct chronological words orthogonal in the environment. It removes the $001/010$ coherence as well as the other off-diagonal word entries, while preserving the classical law. This supplies an explicit reason that the extra coherent-output access cannot be inferred from the instrument's classical interface.

For the distinction of tasks, [Riechers–Elliott, arXiv:2509.03004v1, Theorem 1 and Corollary 1, PDF p. 5](https://arxiv.org/pdf/2509.03004v1) characterize equality of classical output processes; they do not assert hidden memory-unitary uniqueness. The full stationary quantum-output equivalence results of [Guță–Kiukas, arXiv:1402.3535v1, Theorem 2, equation (7), PDF p. 8](https://arxiv.org/pdf/1402.3535v1), for primitive isometries, and [Girotti–Kiukas–Guță, arXiv:2603.20761v1, Theorem 6, PDF p. 32](https://arxiv.org/pdf/2603.20761v1), for irreducible chains, use a common Kraus phase and full stationary output states. They are bibliographic comparisons, not premises for this finite post-herald, count-twirled theorem. The family calculation (24.7)–(24.11), the restricted lower bound (24.14), and the preparation calculation (24.17) provide the identification and resource conclusions directly. $\square$

## 追加锚（本行以下为增补区）
